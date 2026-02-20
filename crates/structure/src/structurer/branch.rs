use petgraph::stable_graph::NodeIndex;
use petgraph::visit::EdgeRef;
use rustc_hash::FxHashSet;

use lantern_hir::arena::ExprId;
use lantern_hir::cfg::{EdgeKind, Terminator};
use lantern_hir::func::HirFunc;
use lantern_hir::stmt::{ElseIfClause, HirStmt};

use super::LoopCtx;
use super::cfg_helpers::{self, branch_successors, find_join_point, negate_condition};
use super::guard::{ends_with_exit, is_guard_clause};
use super::structure_region;

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

/// Structure a branch (if/else) and return the next node to continue from.
pub(super) fn structure_branch(
    func: &mut HirFunc,
    _node: NodeIndex,
    condition: ExprId,
    stop: Option<NodeIndex>,
    loop_ctx: Option<&LoopCtx>,
    visited: &mut FxHashSet<NodeIndex>,
    result: &mut Vec<HirStmt>,
) -> Option<NodeIndex> {
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
                        then_body: vec![HirStmt::Continue],
                        elseif_clauses: Vec::new(),
                        else_body: None,
                    });
                    return Some(else_n);
                }
                // if not cond then break end (else branch breaks)
                if Some(else_target) == lctx.exit && !visited.contains(&else_target) {
                    let inv_cond = negate_condition(func, condition);
                    result.push(HirStmt::If {
                        condition: inv_cond,
                        then_body: vec![HirStmt::Break],
                        elseif_clauses: Vec::new(),
                        else_body: None,
                    });
                    return Some(then_n);
                }
                // if not cond then continue end (else branch continues)
                if else_target == lctx.header {
                    let inv_cond = negate_condition(func, condition);
                    result.push(HirStmt::If {
                        condition: inv_cond,
                        then_body: vec![HirStmt::Continue],
                        elseif_clauses: Vec::new(),
                        else_body: None,
                    });
                    return Some(then_n);
                }
            }

            // Find the join point (where both branches converge)
            let join = find_join_point(func, then_n, else_n, stop);

            // Fix for asymmetric returns: if join is None, check if one
            // branch always returns and the other continues.
            let (effective_join, then_returns, else_returns) = if join.is_some() {
                (join, false, false)
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
                (ej, tr, er)
            };

            // Guard clause shortcut: when one branch always returns and the
            // other continues, emit `if [not] cond then <return> end` directly.
            // This avoids the problem where shared return nodes have already
            // been visited, making structure_region return empty.
            if join.is_none() && then_returns && !else_returns {
                // then always returns → `if cond then <return> end; <continue from else>`
                let then_stmts = collect_return_stmts(func, then_n, stop, loop_ctx, visited);
                if !then_stmts.is_empty() {
                    result.push(HirStmt::If {
                        condition,
                        then_body: then_stmts,
                        elseif_clauses: Vec::new(),
                        else_body: None,
                    });
                    return Some(else_n);
                }
            }
            if join.is_none() && else_returns && !then_returns {
                // else always returns → `if not cond then <return> end; <continue from then>`
                let else_stmts = collect_return_stmts(func, else_n, stop, loop_ctx, visited);
                if !else_stmts.is_empty() {
                    let inv_cond = negate_condition(func, condition);
                    result.push(HirStmt::If {
                        condition: inv_cond,
                        then_body: else_stmts,
                        elseif_clauses: Vec::new(),
                        else_body: None,
                    });
                    return Some(then_n);
                }
            }

            let branch_stop = effective_join.or(stop);
            let mut then_stmts = structure_region(func, then_n, branch_stop, loop_ctx, visited);
            let mut else_stmts = structure_region(func, else_n, branch_stop, loop_ctx, visited);

            // When a branch targets a shared Return node that was already
            // visited by an earlier branch, structure_region returns empty.
            // Recover the return statement by cloning it from the terminator.
            if then_stmts.is_empty() {
                if let Some(ret) = clone_return_from_node(func, then_n) {
                    then_stmts = vec![ret];
                }
            }
            if else_stmts.is_empty() {
                if let Some(ret) = clone_return_from_node(func, else_n) {
                    else_stmts = vec![ret];
                }
            }

            let (elseif_clauses, final_else) = extract_elseif_chain(else_stmts);

            if elseif_clauses.is_empty() && final_else.is_empty() {
                result.push(HirStmt::If {
                    condition,
                    then_body: then_stmts,
                    elseif_clauses: Vec::new(),
                    else_body: None,
                });
            } else if elseif_clauses.is_empty() && !final_else.is_empty() {
                if then_stmts.is_empty() {
                    // Empty then-body → flip to `if not cond then <else> end`
                    let inv_cond = negate_condition(func, condition);
                    result.push(HirStmt::If {
                        condition: inv_cond,
                        then_body: final_else,
                        elseif_clauses: Vec::new(),
                        else_body: None,
                    });
                } else if is_guard_clause(&then_stmts) && !ends_with_exit(&final_else) {
                    // Guard clause pattern: then-body is a short early-out and
                    // the else-body continues. Flip to:
                    //   if not cond then <main body> end; <guard>
                    let inv_cond = negate_condition(func, condition);
                    result.push(HirStmt::If {
                        condition: inv_cond,
                        then_body: final_else,
                        elseif_clauses: Vec::new(),
                        else_body: None,
                    });
                    result.extend(then_stmts);
                } else if is_guard_clause(&final_else) && !ends_with_exit(&then_stmts) {
                    // Inverse guard: else-body is the early-out, then-body continues.
                    // Emit as `if cond then <main body> end; <guard>`
                    result.push(HirStmt::If {
                        condition,
                        then_body: then_stmts,
                        elseif_clauses: Vec::new(),
                        else_body: None,
                    });
                    result.extend(final_else);
                } else {
                    result.push(HirStmt::If {
                        condition,
                        then_body: then_stmts,
                        elseif_clauses: Vec::new(),
                        else_body: Some(final_else),
                    });
                }
            } else {
                result.push(HirStmt::If {
                    condition,
                    then_body: then_stmts,
                    elseif_clauses,
                    else_body: if final_else.is_empty() {
                        None
                    } else {
                        Some(final_else)
                    },
                });
            }

            effective_join
        }
        (Some(then_n), None) => {
            let then_stmts = structure_region(func, then_n, stop, loop_ctx, visited);
            result.push(HirStmt::If {
                condition,
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
) -> Vec<HirStmt> {
    // First, try normal structuring — this works when the return node
    // hasn't been visited yet.
    let stmts = structure_region(func, start, stop, loop_ctx, visited);
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

pub(super) fn extract_elseif_chain(
    mut else_stmts: Vec<HirStmt>,
) -> (Vec<ElseIfClause>, Vec<HirStmt>) {
    if else_stmts.len() == 1 {
        if matches!(&else_stmts[0], HirStmt::If { .. }) {
            let stmt = else_stmts.remove(0);
            if let HirStmt::If {
                condition,
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
                let final_else = else_body.unwrap_or_default();
                return (clauses, final_else);
            }
        }
    }
    (Vec::new(), else_stmts)
}
