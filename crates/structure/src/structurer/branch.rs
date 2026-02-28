use petgraph::stable_graph::NodeIndex;
use petgraph::visit::EdgeRef;
use petgraph::Direction;
use rustc_hash::FxHashSet;

use lantern_hir::arena::ExprId;
use lantern_hir::cfg::{EdgeKind, Terminator};
use lantern_hir::expr::HirExpr;
use lantern_hir::func::HirFunc;
use lantern_hir::stmt::{ElseIfClause, HirStmt};
use lantern_hir::types::BinOp;

use super::cfg_helpers::{self, branch_successors, find_join_point, negate_condition};
use super::guard::{ends_with_exit, is_guard_clause};
use super::postdom::PostDomTree;
use super::structure_region;
use super::LoopCtx;

/// Follow unconditional jumps from `start` to find the effective target.
/// Returns `start` itself if it's not a pure Jump block, otherwise follows
/// the chain until a non-Jump block or a visited node is reached.
fn resolve_jump_target(func: &HirFunc, start: NodeIndex) -> NodeIndex {
    let mut node = start;
    let mut seen = FxHashSet::default();
    loop {
        if !seen.insert(node) {
            return node;
        }
        let block = &func.cfg[node];
        // Only follow pure Jump blocks with no statements
        if !block.stmts.is_empty() || !matches!(block.terminator, Terminator::Jump) {
            return node;
        }
        if let Some(succ) = cfg_helpers::single_successor(&func.cfg, node) {
            node = succ;
        } else {
            return node;
        }
    }
}

/// Find where a Jump-terminated block ultimately exits to, even if it has
/// statements.  Unlike `resolve_jump_target` (which only follows *empty*
/// blocks), this returns the single successor of a Jump block regardless of
/// whether it has statements.  Returns `None` if the block is not a Jump.
fn jump_exit_target(func: &HirFunc, node: NodeIndex) -> Option<NodeIndex> {
    let block = &func.cfg[node];
    if matches!(block.terminator, Terminator::Jump) {
        cfg_helpers::single_successor(&func.cfg, node)
    } else {
        None
    }
}

/// Check if a node is a Branch block (has a Branch terminator).
fn is_branch_block(func: &HirFunc, node: NodeIndex) -> bool {
    matches!(func.cfg[node].terminator, Terminator::Branch { .. })
}

/// Attempt to detect and structure an or-chain.
///
/// An or-chain is `if (A and B) or (C and D) or E then body end` compiled as a
/// chain of Branch blocks where each clause's "success" path reaches the same
/// body block and each clause's "fail" path skips to the next clause.
///
/// Returns `Some(next_node)` if an or-chain was detected, `None` otherwise.
fn try_or_chain(
    func: &mut HirFunc,
    node: NodeIndex,
    _condition: ExprId,
    _stop: Option<NodeIndex>,
    loop_ctx: Option<&LoopCtx>,
    visited: &mut FxHashSet<NodeIndex>,
    result: &mut Vec<HirStmt>,
    pdom: &PostDomTree,
) -> Option<Option<NodeIndex>> {
    // Find the shared body node by walking the first AND sub-chain.
    let body_node = find_or_chain_body(func, node)?;

    // Collect all OR clauses. Each clause is a Vec of (block, negate_condition?) pairs
    // forming an AND chain. The last block in each clause reaches body_node.
    //
    // clause_data: Vec of (Vec<(NodeIndex, bool)>, skip_target)
    //   - Vec<(block, body_on_else)> = AND links
    //   - skip_target = next OR clause entry (else-edge of first block)
    let mut clause_data: Vec<Vec<(NodeIndex, bool)>> = Vec::new();
    let mut current = node;
    let mut join_node = None;

    'walk: for _ in 0..20 {
        if !is_branch_block(func, current) {
            if current != body_node {
                join_node = Some(current);
            }
            break;
        }

        // Collect AND sub-chain from `current` that reaches body_node.
        let mut links: Vec<(NodeIndex, bool)> = Vec::new();
        let mut chain_node = current;
        let mut skip_target = None;

        for _ in 0..10 {
            if !is_branch_block(func, chain_node) {
                break;
            }
            let (then_n, else_n) = branch_successors(&func.cfg, chain_node);
            let (then_n, else_n) = match (then_n, else_n) {
                (Some(t), Some(e)) => (t, e),
                _ => break 'walk,
            };

            // Check if either edge goes directly to body_node.
            if then_n == body_node {
                // Body on then-edge. Condition as-is for body execution.
                links.push((chain_node, false));
                if skip_target.is_none() {
                    skip_target = Some(else_n);
                }
                // Record this AND chain as a clause.
                clause_data.push(links);
                current = skip_target.unwrap();
                continue 'walk;
            }
            if else_n == body_node {
                // Body on else-edge. Must negate condition.
                links.push((chain_node, true));
                if skip_target.is_none() {
                    skip_target = Some(then_n);
                }
                clause_data.push(links);
                current = skip_target.unwrap();
                continue 'walk;
            }

            // Neither edge goes to body directly. Check if one edge
            // is a Branch (AND chain continuation) and the other is
            // the skip target (next OR clause).
            let then_is_branch = is_branch_block(func, then_n);
            let else_is_branch = is_branch_block(func, else_n);

            if then_is_branch && !else_is_branch {
                // then = AND continuation, else = skip target
                links.push((chain_node, false));
                if skip_target.is_none() {
                    skip_target = Some(else_n);
                }
                chain_node = then_n;
            } else if !then_is_branch && else_is_branch {
                // else = AND continuation, then = skip target
                links.push((chain_node, true));
                if skip_target.is_none() {
                    skip_target = Some(then_n);
                }
                chain_node = else_n;
            } else if then_is_branch && else_is_branch {
                // Both are Branch. The then-edge is the AND continuation
                // (fallthrough), else is the skip. This is the standard
                // pattern: `if A then check_B else skip_to_next_OR`.
                links.push((chain_node, false));
                if skip_target.is_none() {
                    skip_target = Some(else_n);
                }
                chain_node = then_n;
            } else {
                // Neither edge is a Branch or body — this block is
                // the continuation AFTER the or-chain, not part of it.
                join_node = Some(current);
                break 'walk;
            }
        }

        // Didn't find body_node from this chain — current block is the
        // continuation after the or-chain.
        join_node = Some(current);
        break;
    }

    // Need at least 2 clauses for an or-chain.
    if clause_data.len() < 2 {
        return None;
    }

    // If ALL clauses reach the body through their else-edge (body_on_else=true
    // on the final link of every clause), this is actually an AND guard chain
    // (each block skips to the failure path when its condition is false).
    // Treating it as an or-chain would negate every condition, flipping
    // JumpIf↔JumpIfNot. Reject and let the normal structurer handle it.
    let all_body_on_else = clause_data
        .iter()
        .all(|links| links.last().is_some_and(|&(_, body_on_else)| body_on_else));
    if all_body_on_else {
        return None;
    }

    // Validate: body_node must only be reached by or-chain clause blocks.
    // If the body_node has predecessors from outside the or-chain (e.g. the
    // continuation path also reaches it), it's a shared exit — not an
    // exclusive or-chain body.  Consuming it would remove it from the
    // continuation path (a correctness bug: missing `return x`).
    {
        let clause_blocks: FxHashSet<NodeIndex> = clause_data
            .iter()
            .flat_map(|links| links.iter().map(|&(b, _)| b))
            .collect();
        for edge in func.cfg.edges_directed(body_node, Direction::Incoming) {
            if !clause_blocks.contains(&edge.source()) {
                return None;
            }
        }
    }

    // Determine the true join point via IPDOM of the or-chain root.
    // The walked join_node may actually be an else-body with real content
    // (e.g. an error logging path), not a convergence point.
    let ipdom_join = pdom.ipdom(node);

    // If we didn't find the join via chain walking, use IPDOM or body successor.
    if join_node.is_none() {
        join_node = ipdom_join
            .or_else(|| cfg_helpers::single_successor(&func.cfg, body_node));
    }

    // If the walked join_node has content and differs from the IPDOM join,
    // it's an else-body, not a join point. Use the IPDOM as the true join.
    let (else_node, true_join) = match (join_node, ipdom_join) {
        (Some(walked), Some(ipdom)) if walked != ipdom && has_block_content(func, walked) => {
            (Some(walked), Some(ipdom))
        }
        _ => (None, join_node),
    };

    // Build the combined condition from collected clause data.
    let mut or_parts: Vec<ExprId> = Vec::new();
    let mut all_blocks: Vec<NodeIndex> = Vec::new();

    for links in &clause_data {
        let mut and_parts: Vec<ExprId> = Vec::new();
        for (i, &(block, body_on_else)) in links.iter().enumerate() {
            all_blocks.push(block);
            let Terminator::Branch { condition, .. } = func.cfg[block].terminator else {
                return None;
            };

            let is_last = i + 1 == links.len();
            let cond = if is_last {
                // Last block: condition depends on which edge reaches body.
                if body_on_else {
                    negate_condition(func, condition)
                } else {
                    condition
                }
            } else {
                // Non-last block: condition must be true for AND chain
                // to continue (following then-edge for the standard pattern).
                // If body_on_else is true for a non-last block, it means
                // the chain follows the else-edge, so condition must be
                // false → negate.
                if body_on_else {
                    negate_condition(func, condition)
                } else {
                    condition
                }
            };
            and_parts.push(cond);
        }

        let clause_cond = if and_parts.len() == 1 {
            and_parts[0]
        } else {
            let mut combined = and_parts[0];
            for &part in &and_parts[1..] {
                combined = func.exprs.alloc(HirExpr::Binary {
                    op: BinOp::And,
                    left: combined,
                    right: part,
                });
            }
            combined
        };
        or_parts.push(clause_cond);
    }

    // Combine all OR clauses.
    let mut combined = or_parts[0];
    for &part in &or_parts[1..] {
        combined = func.exprs.alloc(HirExpr::Binary {
            op: BinOp::Or,
            left: combined,
            right: part,
        });
    }

    // Mark all intermediate clause blocks as visited.
    for &b in &all_blocks {
        visited.insert(b);
    }

    // Take statements from the intermediate blocks (value loads referenced
    // by the conditions). These need to be emitted before the if-statement.
    for &b in &all_blocks {
        let block_stmts = std::mem::take(&mut func.cfg[b].stmts);
        result.extend(block_stmts);
    }

    // Structure the body, stopping at the true join.
    let body_stmts = structure_region(func, body_node, true_join, loop_ctx, visited, pdom);

    // If the walked join was actually an else-body, structure it too.
    let else_stmts = if let Some(else_n) = else_node {
        Some(structure_region(func, else_n, true_join, loop_ctx, visited, pdom))
    } else {
        None
    };

    // Emit the combined if-statement.
    result.push(HirStmt::If {
        condition: combined,
        negated: true,
        then_body: body_stmts,
        elseif_clauses: Vec::new(),
        else_body: else_stmts,
    });

    Some(true_join)
}

/// Find the body node for an or-chain starting at `node`.
///
/// Walks the first AND sub-chain following then-edges through Branch blocks
/// until finding a non-Branch successor that has content (the body).
///
/// When both successors are Branch blocks, also checks if the else-edge target
/// is reachable from the then-edge's chain (convergence target for the OR).
fn find_or_chain_body(func: &HirFunc, start: NodeIndex) -> Option<NodeIndex> {
    let mut node = start;
    for _ in 0..10 {
        if !is_branch_block(func, node) {
            return None;
        }
        let (then_n, else_n) = branch_successors(&func.cfg, node);
        let (then_n, else_n) = match (then_n, else_n) {
            (Some(t), Some(e)) => (t, e),
            _ => return None,
        };

        let then_is_branch = is_branch_block(func, then_n);
        let else_is_branch = is_branch_block(func, else_n);

        if !then_is_branch && !else_is_branch {
            // Both non-Branch. Pick the one with content (body) vs empty (join).
            let then_has_content = has_block_content(func, then_n);
            let else_has_content = has_block_content(func, else_n);
            if then_has_content && !else_has_content {
                return Some(then_n);
            }
            if else_has_content && !then_has_content {
                return Some(else_n);
            }
            if then_has_content && else_has_content {
                // Both have content — pick lower PC (body before join).
                let then_pc = func.cfg[then_n].pc_range.0;
                let else_pc = func.cfg[else_n].pc_range.0;
                return Some(if then_pc < else_pc { then_n } else { else_n });
            }
            return None;
        }
        if !then_is_branch {
            return Some(then_n);
        }
        if !else_is_branch {
            return Some(else_n);
        }
        // Both Branch — check if one side is a convergence target reached
        // directly by the other side's chain. This handles `A or B` where
        // the body block itself starts with a Branch (if-then inside).
        let else_in_degree = count_incoming_from_branches(func, else_n);
        let then_in_degree = count_incoming_from_branches(func, then_n);
        if else_in_degree > then_in_degree && branch_chain_reaches(func, then_n, else_n, 5) {
            return Some(else_n);
        }
        if then_in_degree > else_in_degree && branch_chain_reaches(func, else_n, then_n, 5) {
            return Some(then_n);
        }
        // Neither side converges — follow then-edge (AND chain continuation).
        node = then_n;
    }
    None
}

/// Count how many incoming edges come from Branch blocks (potential or-chain members).
fn count_incoming_from_branches(func: &HirFunc, node: NodeIndex) -> usize {
    func.cfg
        .edges_directed(node, Direction::Incoming)
        .filter(|e| is_branch_block(func, e.source()))
        .count()
}

/// Check if a chain of Branch blocks starting at `start` has any edge that
/// targets `target` within `max_depth` hops.
fn branch_chain_reaches(
    func: &HirFunc,
    start: NodeIndex,
    target: NodeIndex,
    max_depth: usize,
) -> bool {
    let mut node = start;
    for _ in 0..max_depth {
        if !is_branch_block(func, node) {
            return false;
        }
        let (then_n, else_n) = branch_successors(&func.cfg, node);
        match (then_n, else_n) {
            (Some(t), Some(e)) => {
                if t == target || e == target {
                    return true;
                }
                // Follow the branch chain — pick the successor that's a Branch.
                let t_is_branch = is_branch_block(func, t);
                let e_is_branch = is_branch_block(func, e);
                if t_is_branch {
                    node = t;
                } else if e_is_branch {
                    node = e;
                } else {
                    return false;
                }
            }
            _ => return false,
        }
    }
    false
}

/// Check if a block has meaningful content (statements or non-trivial terminator).
fn has_block_content(func: &HirFunc, node: NodeIndex) -> bool {
    let block = &func.cfg[node];
    !block.stmts.is_empty()
        || !matches!(
            block.terminator,
            Terminator::Jump | Terminator::None
        )
}

/// Structure a branch (if/else) and return the next node to continue from.
pub(super) fn structure_branch(
    func: &mut HirFunc,
    _node: NodeIndex,
    condition: ExprId,
    negated: bool,
    stop: Option<NodeIndex>,
    loop_ctx: Option<&LoopCtx>,
    visited: &mut FxHashSet<NodeIndex>,
    result: &mut Vec<HirStmt>,
    pdom: &PostDomTree,
) -> Option<NodeIndex> {
    // Try to detect and structure an or-chain before normal branch processing.
    if let Some(next) = try_or_chain(func, _node, condition, stop, loop_ctx, visited, result, pdom) {
        return next;
    }

    let (then_node, else_node) = branch_successors(&func.cfg, _node);

    match (then_node, else_node) {
        (Some(then_n), Some(else_n)) => {
            // Check for break/continue as branch targets.
            // Resolve through intermediate Jump blocks so that compound
            // condition chains (A and B → continue) are detected even when
            // the branch doesn't directly target the loop header/exit.
            if let Some(lctx) = loop_ctx {
                let then_target = resolve_jump_target(func, then_n);
                let else_target = resolve_jump_target(func, else_n);

                // if cond then break end
                if Some(then_target) == lctx.exit && !visited.contains(&then_target) {
                    result.push(HirStmt::If {
                        condition,
                        negated,
                        then_body: vec![HirStmt::Break],
                        elseif_clauses: Vec::new(),
                        else_body: None,
                    });
                    return Some(else_n);
                }
                // if cond then continue end
                if then_target == lctx.header {
                    result.push(HirStmt::If {
                        condition,
                        negated,
                        then_body: vec![HirStmt::Continue],
                        elseif_clauses: Vec::new(),
                        else_body: None,
                    });
                    return Some(else_n);
                }

                // Then-branch has statements but exits the loop:
                //   if cond then <stmts>; break end
                // This handles blocks like `Logging.warning(...); Jump→exit`
                // where resolve_jump_target stops because the block isn't empty.
                if let Some(exit) = lctx.exit {
                    if Some(then_target) != lctx.exit {
                        if let Some(jt) = jump_exit_target(func, then_n) {
                            if jt == exit && !visited.contains(&exit) {
                                // Structure the then-branch stopping at the exit
                                // so we don't follow the Jump out of the loop.
                                let mut then_stmts =
                                    structure_region(func, then_n, Some(exit), loop_ctx, visited, pdom);
                                then_stmts.push(HirStmt::Break);
                                result.push(HirStmt::If {
                                    condition,
                                    negated,
                                    then_body: then_stmts,
                                    elseif_clauses: Vec::new(),
                                    else_body: None,
                                });
                                return Some(else_n);
                            }
                        }
                    }
                }

                // else branch breaks/continues: use `negated` flag from the
                // original opcode to decide between guard and wrapping forms.
                //   negated=true  (JumpIfNot*) → wrapping: `if cond then <body> end`
                //   negated=false (JumpIf*)    → guard: `if NOT(cond) then break/continue end; <body>`
                if Some(else_target) == lctx.exit && !visited.contains(&else_target) {
                    if negated {
                        // Wrapping form: `if cond then <body> end`
                        let then_stmts =
                            structure_region(func, then_n, stop, loop_ctx, visited, pdom);
                        result.push(HirStmt::If {
                            condition,
                            negated,
                            then_body: then_stmts,
                            elseif_clauses: Vec::new(),
                            else_body: None,
                        });
                    } else {
                        // Guard form: `if NOT(cond) then break end; <body>`
                        let guard_cond = negate_condition(func, condition);
                        result.push(HirStmt::If {
                            condition: guard_cond,
                            negated: true,
                            then_body: vec![HirStmt::Break],
                            elseif_clauses: Vec::new(),
                            else_body: None,
                        });
                        let then_stmts =
                            structure_region(func, then_n, stop, loop_ctx, visited, pdom);
                        result.extend(then_stmts);
                    }
                    return stop;
                }
                // Else-branch has statements but exits the loop.
                // Mirror of the then-branch case above.
                if let Some(exit) = lctx.exit {
                    if Some(else_target) != lctx.exit {
                        if let Some(jt) = jump_exit_target(func, else_n) {
                            if jt == exit && !visited.contains(&exit) {
                                let then_stmts =
                                    structure_region(func, then_n, stop, loop_ctx, visited, pdom);
                                let mut else_stmts =
                                    structure_region(func, else_n, Some(exit), loop_ctx, visited, pdom);
                                else_stmts.push(HirStmt::Break);
                                result.push(HirStmt::If {
                                    condition,
                                    negated,
                                    then_body: then_stmts,
                                    elseif_clauses: Vec::new(),
                                    else_body: Some(else_stmts),
                                });
                                return stop;
                            }
                        }
                    }
                }

                if else_target == lctx.header {
                    // Check for empty-else annotation before choosing form.
                    // When the then-body ends with Jump+0, the wrapping form
                    // is required to preserve the empty else in the output.
                    let has_empty_else =
                        has_empty_else_annotation(func, then_n, Some(else_target));
                    if negated || has_empty_else {
                        // Wrapping form: `if cond then <body> end`
                        let then_stmts =
                            structure_region(func, then_n, stop, loop_ctx, visited, pdom);
                        result.push(HirStmt::If {
                            condition,
                            negated,
                            then_body: then_stmts,
                            elseif_clauses: Vec::new(),
                            else_body: if has_empty_else { Some(vec![]) } else { None },
                        });
                    } else {
                        // Guard form: `if NOT(cond) then continue end; <body>`
                        let guard_cond = negate_condition(func, condition);
                        result.push(HirStmt::If {
                            condition: guard_cond,
                            negated: true,
                            then_body: vec![HirStmt::Continue],
                            elseif_clauses: Vec::new(),
                            else_body: None,
                        });
                        let then_stmts =
                            structure_region(func, then_n, stop, loop_ctx, visited, pdom);
                        result.extend(then_stmts);
                    }
                    return stop;
                }
            }

            // Find the join point via IPDOM — the immediate post-dominator
            // of the Branch node is where both branches must converge.
            // When IPDOM equals the outer stop, that's correct: the branch
            // fills the region up to stop and the caller continues from there.
            //
            // Fall back to the reachability-based heuristic when IPDOM
            // returns None (e.g. both branches terminate via Return —
            // there is no post-dominator, but a shared "sunk return"
            // block may still serve as the join point).
            let join = pdom
                .ipdom(_node)
                .or_else(|| find_join_point(func, then_n, else_n, stop, visited));

            // Fix for asymmetric returns: if join is None, check if one
            // branch always returns and the other continues.
            let (effective_join, then_returns, else_returns, join_from_cfg) = if join.is_some() {
                (join, false, false, true)
            } else {
                let tr = branch_always_returns(func, then_n, stop);
                let er = branch_always_returns(func, else_n, stop);
                let ej = if tr && !er {
                    Some(else_n)
                } else if er && !tr {
                    Some(then_n)
                } else {
                    None
                };
                (ej, tr, er, false)
            };

            // Guard clause shortcut: when one branch always returns and the
            // other continues, emit `if [not] cond then <return> end` directly.
            // This avoids the problem where shared return nodes have already
            // been visited, making structure_region return empty.
            if join.is_none() && then_returns && !else_returns {
                // then always returns → `if cond then <return> end; <continue from else>`
                let then_stmts = collect_return_stmts(func, then_n, stop, loop_ctx, visited, pdom);
                if !then_stmts.is_empty() {
                    result.push(HirStmt::If {
                        condition,
                        negated,
                        then_body: then_stmts,
                        elseif_clauses: Vec::new(),
                        else_body: None,
                    });
                    return Some(else_n);
                }
            }
            if join.is_none() && else_returns && !then_returns {
                // else always returns → structure then-body inline, emit
                // `if cond then <then_body> else <return> end` preserving
                // the original branch polarity (avoids JumpIf↔JumpIfNot swaps).
                let else_stmts = collect_return_stmts(func, else_n, stop, loop_ctx, visited, pdom);
                if !else_stmts.is_empty() {
                    let then_stmts =
                        structure_region(func, then_n, stop, loop_ctx, visited, pdom);
                    result.push(HirStmt::If {
                        condition,
                        negated,
                        then_body: then_stmts,
                        elseif_clauses: Vec::new(),
                        else_body: Some(else_stmts),
                    });
                    return effective_join.or(stop);
                }
            }

            let branch_stop = effective_join.or(stop);
            let mut then_stmts = structure_region(func, then_n, branch_stop, loop_ctx, visited, pdom);
            let mut else_stmts = structure_region(func, else_n, branch_stop, loop_ctx, visited, pdom);

            // When a branch targets a shared Return node that was already
            // visited by an earlier branch, structure_region returns empty.
            // Recover the return statement by cloning it from the terminator.
            //
            // Skip cloning when:
            // (a) The join came from find_join_point and the branch target IS the
            //     join point — the return will be emitted after the if/end.
            // (b) The branch target equals the outer stop node — the caller's
            //     loop will handle it (prevents duplicating a shared return
            //     inside a branch AND after the enclosing if).
            if then_stmts.is_empty() {
                let skip = (join_from_cfg && effective_join == Some(then_n))
                    || Some(then_n) == stop;
                if !skip {
                    if let Some(ret) = clone_return_from_node(func, then_n) {
                        then_stmts = vec![ret];
                    }
                }
            }
            if else_stmts.is_empty() {
                let skip = (join_from_cfg && effective_join == Some(else_n))
                    || Some(else_n) == stop;
                if !skip {
                    if let Some(ret) = clone_return_from_node(func, else_n) {
                        else_stmts = vec![ret];
                    }
                }
            }

            let (elseif_clauses, final_else) = extract_elseif_chain(else_stmts);

            if elseif_clauses.is_empty() && final_else.is_none() {
                // Check if the then-branch ends with a Jump(0) — the
                // compiler's artifact for an empty `else` body.  When
                // present, emit `else end` to match the original source.
                let has_empty_else = has_empty_else_annotation(func, then_n, effective_join);
                result.push(HirStmt::If {
                    condition,
                    negated,
                    then_body: then_stmts,
                    elseif_clauses: Vec::new(),
                    else_body: if has_empty_else { Some(vec![]) } else { None },
                });
            } else if elseif_clauses.is_empty() && final_else.is_some() {
                let final_else = final_else.unwrap();
                if then_stmts.is_empty() {
                    // Empty then-body → flip to `if not cond then <else> end`
                    let inv_cond = negate_condition(func, condition);
                    result.push(HirStmt::If {
                        condition: inv_cond,
                        negated: true,
                        then_body: final_else,
                        elseif_clauses: Vec::new(),
                        else_body: None,
                    });
                } else if is_guard_clause(&then_stmts) && !ends_with_exit(&final_else) {
                    // Guard clause pattern: then-body is a short early-out
                    // (return/break) and the else-body has continuation code.
                    // Emit as: if cond then <guard return> end; <body>
                    result.push(HirStmt::If {
                        condition,
                        negated,
                        then_body: then_stmts,
                        elseif_clauses: Vec::new(),
                        else_body: None,
                    });
                    result.extend(final_else);
                } else if is_guard_clause(&final_else) && !ends_with_exit(&then_stmts) {
                    // Inverse guard: else-body is the early-out, then-body continues.
                    // Emit as `if cond then <main body> end; <guard>`
                    result.push(HirStmt::If {
                        condition,
                        negated,
                        then_body: then_stmts,
                        elseif_clauses: Vec::new(),
                        else_body: None,
                    });
                    result.extend(final_else);
                } else {
                    result.push(HirStmt::If {
                        condition,
                        negated,
                        then_body: then_stmts,
                        elseif_clauses: Vec::new(),
                        else_body: Some(final_else),
                    });
                }
            } else {
                result.push(HirStmt::If {
                    condition,
                    negated,
                    then_body: then_stmts,
                    elseif_clauses,
                    else_body: final_else,
                });
            }

            effective_join
        }
        (Some(then_n), None) => {
            let then_stmts = structure_region(func, then_n, stop, loop_ctx, visited, pdom);
            result.push(HirStmt::If {
                condition,
                negated,
                then_body: then_stmts,
                elseif_clauses: Vec::new(),
                else_body: None,
            });
            None
        }
        _ => None,
    }
}

/// Check if a branch always ends in Return (no path reaches a continuation).
pub(super) fn branch_always_returns(
    func: &HirFunc,
    start: NodeIndex,
    stop: Option<NodeIndex>,
) -> bool {
    let mut stack = vec![start];
    let mut visited = FxHashSet::default();
    while let Some(node) = stack.pop() {
        if Some(node) == stop {
            // Reached the join point — this path does NOT return
            return false;
        }
        if !visited.insert(node) {
            continue;
        }
        match &func.cfg[node].terminator {
            lantern_hir::cfg::Terminator::Return(_) => {
                // This path returns — keep checking other paths
            }
            lantern_hir::cfg::Terminator::None => {
                // Dead end without return
                return false;
            }
            _ => {
                let mut pushed = false;
                for e in func.cfg.edges(node) {
                    if e.weight().kind != EdgeKind::LoopBack {
                        stack.push(e.target());
                        pushed = true;
                    }
                }
                if !pushed {
                    // All exits are back-edges — infinite loop, not a return
                    return false;
                }
            }
        }
    }
    !visited.is_empty()
}

/// If `node` is a terminal Return block (no statements, just a return
/// terminator), clone its return as a HirStmt.  This handles the case where
/// multiple branches share the same Return node — only the first visitor
/// gets to structure it, but later branches still need the return statement.
fn clone_return_from_node(func: &HirFunc, node: NodeIndex) -> Option<HirStmt> {
    let block = &func.cfg[node];
    if let Terminator::Return(values) = &block.terminator {
        // Only recover if the block has no other statements — a pure return.
        if block.stmts.is_empty() {
            return Some(HirStmt::Return(values.clone()));
        }
    }
    None
}

/// Collect return statements from a branch that always returns.
/// Walks through already-visited nodes following unconditional jumps
/// until a Return terminator is found.  This enables guard-clause
/// emission for shared return blocks that were consumed by earlier
/// structuring passes.
fn collect_return_stmts(
    func: &mut HirFunc,
    start: NodeIndex,
    stop: Option<NodeIndex>,
    loop_ctx: Option<&LoopCtx>,
    visited: &mut FxHashSet<NodeIndex>,
    pdom: &PostDomTree,
) -> Vec<HirStmt> {
    // First, try normal structuring — this works when the return node
    // hasn't been visited yet.
    let stmts = structure_region(func, start, stop, loop_ctx, visited, pdom);
    if !stmts.is_empty() {
        return stmts;
    }

    // If structuring returned empty, walk the chain to find the return.
    let mut node = start;
    let mut walked = FxHashSet::default();
    loop {
        if !walked.insert(node) {
            break;
        }
        let block = &func.cfg[node];
        match &block.terminator {
            Terminator::Return(values) => {
                return vec![HirStmt::Return(values.clone())];
            }
            Terminator::Jump => {
                // Follow unconditional jumps
                if let Some(succ) = cfg_helpers::single_successor(&func.cfg, node) {
                    node = succ;
                    continue;
                }
                break;
            }
            _ => break,
        }
    }
    Vec::new()
}

/// Check if the then-region of a branch ends with a `Jump +0` annotation,
/// indicating the original source had an empty `else` body.  Walks forward
/// from `start` following unconditional Jump edges until reaching `join`.
fn has_empty_else_annotation(
    func: &HirFunc,
    start: NodeIndex,
    join: Option<NodeIndex>,
) -> bool {
    let mut node = start;
    let mut depth = 0;
    loop {
        if depth > 20 {
            return false;
        }
        let block = &func.cfg[node];
        if block.has_empty_else_jump {
            // Verify this jump targets the join point (the else exit).
            if let Some(join_n) = join {
                for e in func.cfg.edges(node) {
                    if e.target() == join_n {
                        return true;
                    }
                }
            } else {
                // No join point known (e.g. last elseif clause whose body
                // jumps to the enclosing loop header/stop). The Jump +0
                // annotation alone is sufficient evidence.
                return true;
            }
        }
        // Follow unconditional jumps deeper into the then-region.
        if matches!(block.terminator, Terminator::Jump) {
            if let Some(succ) = cfg_helpers::single_successor(&func.cfg, node) {
                if Some(succ) == join {
                    return false; // Reached join without finding annotation
                }
                node = succ;
                depth += 1;
                continue;
            }
        }
        return false;
    }
}

/// Extract an elseif chain from else_stmts.
///
/// Returns `(elseif_clauses, final_else)` where `final_else` is `None` if
/// there is no else body, or `Some(stmts)` if there is (possibly empty for
/// an explicit empty `else end`).
pub(super) fn extract_elseif_chain(
    mut else_stmts: Vec<HirStmt>,
) -> (Vec<ElseIfClause>, Option<Vec<HirStmt>>) {
    if else_stmts.len() == 1 {
        if matches!(&else_stmts[0], HirStmt::If { .. }) {
            let stmt = else_stmts.remove(0);
            if let HirStmt::If {
                condition,
                negated: _,
                then_body,
                elseif_clauses,
                else_body,
            } = stmt
            {
                let mut clauses = vec![ElseIfClause {
                    condition,
                    body: then_body,
                }];
                clauses.extend(elseif_clauses);
                return (clauses, else_body);
            }
        }
    }
    if else_stmts.is_empty() {
        (Vec::new(), None)
    } else {
        (Vec::new(), Some(else_stmts))
    }
}
