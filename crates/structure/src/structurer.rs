use petgraph::stable_graph::NodeIndex;
use petgraph::visit::EdgeRef;
use rustc_hash::FxHashSet;

use lantern_hir::arena::ExprId;
use lantern_hir::cfg::{EdgeKind, Terminator};
use lantern_hir::expr::HirExpr;
use lantern_hir::func::HirFunc;
use lantern_hir::stmt::{ElseIfClause, HirStmt, LValue};
use lantern_hir::types::{BinOp, UnOp};
use lantern_hir::var::VarId;

/// Structure a function's CFG into nested HirStmt trees.
///
/// After this pass, `func.cfg[func.entry].stmts` contains the complete
/// structured output and `func.structured` is set to true. The emitter
/// walks only the entry block's stmts recursively.
pub fn structure_function(func: &mut HirFunc) {
    let entry = func.entry;
    let stmts = structure_region(func, entry, None, None, &mut FxHashSet::default());
    func.cfg[entry].stmts = stmts;
    func.cfg[entry].terminator = Terminator::None;
    func.structured = true;
}

/// Context for the enclosing loop, used to emit break/continue.
struct LoopCtx {
    header: NodeIndex,
    exit: Option<NodeIndex>,
}

/// Structure a region of the CFG starting from `start`, stopping before `stop`.
/// Returns the structured statement list.
///
/// `loop_ctx` provides the enclosing loop's header and exit for break/continue.
fn structure_region(
    func: &mut HirFunc,
    start: NodeIndex,
    stop: Option<NodeIndex>,
    loop_ctx: Option<&LoopCtx>,
    visited: &mut FxHashSet<NodeIndex>,
) -> Vec<HirStmt> {
    let mut result = Vec::new();
    let mut current = Some(start);

    while let Some(node) = current {
        if Some(node) == stop {
            break;
        }
        if !visited.insert(node) {
            break;
        }

        // Check if this is a while-loop header
        if let Some(loop_result) = try_structure_while(func, node, stop, loop_ctx, visited) {
            result.extend(loop_result.stmts);
            current = loop_result.next;
            continue;
        }

        // Take statements from this block
        let block_stmts = std::mem::take(&mut func.cfg[node].stmts);
        let terminator = func.cfg[node].terminator.clone();
        result.extend(block_stmts);

        match &terminator {
            Terminator::None => {
                current = None;
            }

            Terminator::Return(values) => {
                result.push(HirStmt::Return(values.clone()));
                current = None;
            }

            Terminator::Jump => {
                let succ = single_successor(&func.cfg, node);

                // Check for break/continue in loop context
                if let (Some(succ_node), Some(lctx)) = (succ, loop_ctx) {
                    // A jump to the stop node is just the natural end of the
                    // region — don't emit continue. For-loop bodies jump to
                    // the ForNumBack/ForGenBack block as normal iteration.
                    if Some(succ_node) != stop {
                        if succ_node == lctx.header {
                            result.push(HirStmt::Continue);
                            current = None;
                            continue;
                        }
                        if Some(succ_node) == lctx.exit {
                            result.push(HirStmt::Break);
                            current = None;
                            continue;
                        }
                    }
                }

                current = succ;
            }

            Terminator::Branch { condition } => {
                let condition = *condition;
                current = structure_branch(func, node, condition, stop, loop_ctx, visited, &mut result);
            }

            Terminator::ForNumPrep { base_reg, start, limit, step, ref loop_var_name } => {
                let start = *start;
                let limit = *limit;
                let step = *step;
                let base_reg = *base_reg;
                let loop_var_name = loop_var_name.clone();
                current = structure_for_num(func, node, base_reg, start, limit, step, loop_var_name, stop, loop_ctx, visited, &mut result);
            }

            Terminator::ForNumBack { .. } => {
                // Should not be reached during structuring — the ForNumPrep
                // handler structures the body up to and including this block.
                current = None;
            }

            Terminator::ForGenBack { base_reg, var_count, ref iterators, ref loop_var_names, .. } => {
                let base_reg = *base_reg;
                let var_count = *var_count;
                let iterators = iterators.clone();
                let loop_var_names = loop_var_names.clone();
                current = structure_for_gen(func, node, base_reg, var_count, iterators, loop_var_names, stop, loop_ctx, visited, &mut result);
            }
        }
    }

    result
}

/// Structure a branch (if/else) and return the next node to continue from.
fn structure_branch(
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
            // Check for break/continue as branch targets
            if let Some(lctx) = loop_ctx {
                // if cond then break end
                if Some(then_n) == lctx.exit && !visited.contains(&then_n) {
                    result.push(HirStmt::If {
                        condition,
                        then_body: vec![HirStmt::Break],
                        elseif_clauses: Vec::new(),
                        else_body: None,
                    });
                    return Some(else_n);
                }
                // if cond then continue end
                if then_n == lctx.header {
                    result.push(HirStmt::If {
                        condition,
                        then_body: vec![HirStmt::Continue],
                        elseif_clauses: Vec::new(),
                        else_body: None,
                    });
                    return Some(else_n);
                }
                // if not cond then break end (else branch breaks)
                if Some(else_n) == lctx.exit && !visited.contains(&else_n) {
                    let inv_cond = negate_condition(func, condition);
                    result.push(HirStmt::If {
                        condition: inv_cond,
                        then_body: vec![HirStmt::Break],
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
            let effective_join = join.or_else(|| {
                let then_returns = branch_always_returns(func, then_n, stop);
                let else_returns = branch_always_returns(func, else_n, stop);
                if then_returns && !else_returns {
                    Some(else_n)
                } else if else_returns && !then_returns {
                    Some(then_n)
                } else {
                    None
                }
            });

            let branch_stop = effective_join.or(stop);
            let then_stmts = structure_region(func, then_n, branch_stop, loop_ctx, visited);
            let else_stmts = structure_region(func, else_n, branch_stop, loop_ctx, visited);

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
                    let inv_cond = negate_condition(func, condition);
                    result.push(HirStmt::If {
                        condition: inv_cond,
                        then_body: final_else,
                        elseif_clauses: Vec::new(),
                        else_body: None,
                    });
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

/// Result of structuring a loop.
struct LoopResult {
    stmts: Vec<HirStmt>,
    next: Option<NodeIndex>,
}

/// Try to structure `node` as a while-loop header.
///
/// A while-loop is detected when a Branch node's body has a path back
/// to the header node (back-edge).
fn try_structure_while(
    func: &mut HirFunc,
    node: NodeIndex,
    _stop: Option<NodeIndex>,
    _outer_loop: Option<&LoopCtx>,
    visited: &mut FxHashSet<NodeIndex>,
) -> Option<LoopResult> {
    let condition = match &func.cfg[node].terminator {
        Terminator::Branch { condition } => *condition,
        _ => return None,
    };

    // Use branch_successors for deterministic then/else classification
    let (then_node, else_node) = branch_successors(&func.cfg, node);
    let (then_n, else_n) = match (then_node, else_node) {
        (Some(t), Some(e)) => (t, e),
        _ => return None,
    };

    // Check which branch has a back-edge to the header — that's the body.
    // The other branch is the exit.
    let (body_start, exit_node, loop_condition) =
        if has_back_edge_to(&func.cfg, then_n, node) {
            // Then-branch loops back: body=then, exit=else, condition as-is
            (then_n, else_n, condition)
        } else if has_back_edge_to(&func.cfg, else_n, node) {
            // Else-branch loops back: body=else, exit=then, negate condition
            let neg_cond = negate_condition(func, condition);
            (else_n, then_n, neg_cond)
        } else {
            return None;
        };

    // This is a while loop
    let header_stmts = std::mem::take(&mut func.cfg[node].stmts);

    let loop_ctx = LoopCtx {
        header: node,
        exit: Some(exit_node),
    };

    let body_stmts = structure_region(func, body_start, Some(node), Some(&loop_ctx), visited);

    let mut all_stmts = Vec::new();
    all_stmts.extend(header_stmts);
    all_stmts.push(HirStmt::While {
        condition: loop_condition,
        body: body_stmts,
    });

    Some(LoopResult {
        stmts: all_stmts,
        next: Some(exit_node),
    })
}

/// Check if any node reachable from `start` has a direct edge to `header`.
///
/// Skips LoopBack edges from ForNumBack/ForGenBack terminators — those
/// belong to for-loops and should not trigger while-loop detection.
fn has_back_edge_to(
    cfg: &lantern_hir::cfg::CfgGraph,
    start: NodeIndex,
    header: NodeIndex,
) -> bool {
    let mut visited = FxHashSet::default();
    let mut stack = vec![start];
    while let Some(node) = stack.pop() {
        if node == header || !visited.insert(node) {
            continue;
        }
        // Don't follow for-loop back-edges — they're not while-loop structure
        let is_for_back = matches!(
            cfg[node].terminator,
            Terminator::ForNumBack { .. } | Terminator::ForGenBack { .. }
        );
        for e in cfg.edges(node) {
            if is_for_back && e.weight().kind == EdgeKind::LoopBack {
                continue;
            }
            if e.target() == header {
                return true;
            }
            stack.push(e.target());
        }
    }
    false
}

/// Check if a branch always ends in Return (no path reaches a continuation).
fn branch_always_returns(
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
            Terminator::Return(_) => {
                // This path returns — keep checking other paths
            }
            Terminator::None => {
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

// ---- CFG helpers ----

fn single_successor(
    cfg: &lantern_hir::cfg::CfgGraph,
    node: NodeIndex,
) -> Option<NodeIndex> {
    cfg.edges(node).next().map(|e| e.target())
}

fn branch_successors(
    cfg: &lantern_hir::cfg::CfgGraph,
    node: NodeIndex,
) -> (Option<NodeIndex>, Option<NodeIndex>) {
    let mut then_node = None;
    let mut else_node = None;
    for e in cfg.edges(node) {
        match e.weight().kind {
            EdgeKind::Then | EdgeKind::LoopBack => then_node = Some(e.target()),
            EdgeKind::Else | EdgeKind::LoopExit => else_node = Some(e.target()),
            EdgeKind::Unconditional => {
                if then_node.is_none() {
                    then_node = Some(e.target());
                } else {
                    else_node = Some(e.target());
                }
            }
        }
    }
    (then_node, else_node)
}

fn find_join_point(
    func: &HirFunc,
    then_node: NodeIndex,
    else_node: NodeIndex,
    outer_stop: Option<NodeIndex>,
) -> Option<NodeIndex> {
    let then_reachable = collect_reachable(&func.cfg, then_node, outer_stop);
    let else_reachable = collect_reachable(&func.cfg, else_node, outer_stop);

    let mut common: Vec<NodeIndex> = then_reachable
        .intersection(&else_reachable)
        .copied()
        .collect();

    if then_reachable.contains(&else_node) {
        common.push(else_node);
    }
    if else_reachable.contains(&then_node) {
        common.push(then_node);
    }

    if common.is_empty() {
        return None;
    }

    common.sort_by_key(|n| func.cfg[*n].pc_range.0);
    common.dedup();
    Some(common[0])
}

fn collect_reachable(
    cfg: &lantern_hir::cfg::CfgGraph,
    start: NodeIndex,
    stop: Option<NodeIndex>,
) -> FxHashSet<NodeIndex> {
    let mut visited = FxHashSet::default();
    let mut stack = vec![start];
    while let Some(node) = stack.pop() {
        if Some(node) == stop || !visited.insert(node) {
            continue;
        }
        for e in cfg.edges(node) {
            if e.weight().kind != EdgeKind::LoopBack {
                stack.push(e.target());
            }
        }
    }
    visited
}

fn extract_elseif_chain(
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

/// Structure a numeric for-loop from a ForNumPrep terminator.
///
/// CFG shape:
///   [ForNumPrep] --LoopBack--> [body...] --> [ForNumBack] --LoopBack--> body
///                --LoopExit--> [exit]        [ForNumBack] --LoopExit--> exit
///
/// The structurer produces HirStmt::NumericFor and returns the exit node.
fn structure_for_num(
    func: &mut HirFunc,
    node: NodeIndex,
    _base_reg: u8,
    start: ExprId,
    limit: ExprId,
    step: Option<ExprId>,
    loop_var_name: Option<String>,
    stop: Option<NodeIndex>,
    _outer_loop: Option<&LoopCtx>,
    visited: &mut FxHashSet<NodeIndex>,
    result: &mut Vec<HirStmt>,
) -> Option<NodeIndex> {
    // Find body start (LoopBack) and exit (LoopExit) from the prep block
    let mut body_start = None;
    let mut exit_node = None;
    for e in func.cfg.edges(node) {
        match e.weight().kind {
            EdgeKind::LoopBack => body_start = Some(e.target()),
            EdgeKind::LoopExit => exit_node = Some(e.target()),
            _ => {}
        }
    }

    let body_start = match body_start {
        Some(n) => n,
        None => return exit_node.or(stop),
    };

    // Find the ForNumBack block — it's the block with a ForNumBack terminator
    // reachable from the body. We structure the body stopping at the back-edge block.
    let back_block = find_for_back_block(func, body_start, node);

    // Create loop variable VarId from the name resolved during lifting.
    let mut var_info = lantern_hir::var::VarInfo::new();
    var_info.name = loop_var_name;
    var_info.is_loop_var = true;
    let var = func.vars.alloc(var_info);

    // Set up loop context for break/continue inside the body
    let loop_ctx = LoopCtx {
        header: back_block.unwrap_or(node),
        exit: exit_node,
    };

    // Structure the body, stopping before the ForNumBack block
    let body_stmts = structure_region(func, body_start, back_block, Some(&loop_ctx), visited);

    // Mark the back-edge block as visited so it's not re-processed
    if let Some(back) = back_block {
        visited.insert(back);
    }

    result.push(HirStmt::NumericFor {
        var,
        start,
        limit,
        step,
        body: body_stmts,
    });

    exit_node
}

/// Structure a generic for-loop from a ForGenBack terminator.
///
/// CFG shape:
///   [FORGPREP/Jump] --unconditional--> [ForGenBack]
///   [ForGenBack] --LoopBack--> [body...] --back to ForGenBack
///   [ForGenBack] --LoopExit--> [exit]
///
/// The structurer produces HirStmt::GenericFor and returns the exit node.
fn structure_for_gen(
    func: &mut HirFunc,
    node: NodeIndex,
    _base_reg: u8,
    var_count: u8,
    iterators: Vec<ExprId>,
    loop_var_names: Vec<Option<String>>,
    _stop: Option<NodeIndex>,
    _outer_loop: Option<&LoopCtx>,
    visited: &mut FxHashSet<NodeIndex>,
    result: &mut Vec<HirStmt>,
) -> Option<NodeIndex> {
    // Find body start (LoopBack) and exit (LoopExit) from the ForGenBack block
    let mut body_start = None;
    let mut exit_node = None;
    for e in func.cfg.edges(node) {
        match e.weight().kind {
            EdgeKind::LoopBack => body_start = Some(e.target()),
            EdgeKind::LoopExit => exit_node = Some(e.target()),
            _ => {}
        }
    }

    let body_start = match body_start {
        Some(n) => n,
        None => return exit_node,
    };

    // Create loop variable VarIds from names resolved during lifting.
    let vars: Vec<lantern_hir::var::VarId> = (0..var_count)
        .map(|i| {
            let mut var_info = lantern_hir::var::VarInfo::new();
            var_info.name = loop_var_names.get(i as usize).cloned().flatten();
            var_info.is_loop_var = true;
            func.vars.alloc(var_info)
        })
        .collect();

    // Set up loop context — the header is this ForGenBack node
    let loop_ctx = LoopCtx {
        header: node,
        exit: exit_node,
    };

    // Try to inline iterator temp assignments from the prep block.
    // Before the for-loop, the prep block emits something like:
    //   local _v10, _v21, _v2 = pairs(_G)
    // and the iterators are [Var(_v10), Var(_v21), Var(_v2)].
    // We fold that into: for k, v in pairs(_G) do
    let iterators = try_inline_for_gen_iterators(func, &iterators, result);

    // Structure the body, stopping before the ForGenBack node itself (back-edge)
    let body_stmts = structure_region(func, body_start, Some(node), Some(&loop_ctx), visited);

    result.push(HirStmt::GenericFor {
        vars,
        iterators,
        body: body_stmts,
    });

    exit_node
}

/// Try to inline iterator temp assignments into generic for-loop headers.
///
/// Looks at the last statement(s) in `result` to see if they define the
/// variables referenced by the iterator expressions. If so, replaces the
/// iterator list with the actual call expressions and removes the temp
/// assignments.
///
/// Handles two patterns:
/// 1. MultiAssign: `_v10, _v21, _v2 = pairs(t)` with iterators [Var(_v10), Var(_v21), Var(_v2)]
///    → iterators become [pairs(t)]
/// 2. Sequence of Assigns: `_v10 = f`, `_v21 = s`, `_v2 = c` with matching iterators
///    → iterators become [f, s, c] (though this is less common)
fn try_inline_for_gen_iterators(
    func: &HirFunc,
    iterators: &[ExprId],
    result: &mut Vec<HirStmt>,
) -> Vec<ExprId> {
    if result.is_empty() || iterators.is_empty() {
        return iterators.to_vec();
    }

    // Extract VarIds from iterator expressions (all must be Var references)
    let iter_vars: Vec<VarId> = iterators
        .iter()
        .filter_map(|&expr_id| {
            if let HirExpr::Var(var_id) = func.exprs.get(expr_id) {
                Some(*var_id)
            } else {
                None
            }
        })
        .collect();

    if iter_vars.len() != iterators.len() {
        // Not all iterators are simple Var references — can't inline
        return iterators.to_vec();
    }

    // Pattern 1: Last statement is MultiAssign with matching targets
    if let Some(HirStmt::MultiAssign { targets, values }) = result.last() {
        let target_vars: Vec<Option<VarId>> = targets
            .iter()
            .map(|t| {
                if let LValue::Local(v) = t {
                    Some(*v)
                } else {
                    None
                }
            })
            .collect();

        if target_vars.len() == iter_vars.len()
            && target_vars
                .iter()
                .zip(iter_vars.iter())
                .all(|(tv, iv)| *tv == Some(*iv))
        {
            // All targets match — check that the temps are unnamed (compiler-generated)
            let all_unnamed = iter_vars
                .iter()
                .all(|v| func.vars.get(*v).name.is_none());
            if all_unnamed {
                let new_iterators = values.clone();
                result.pop(); // Remove the MultiAssign
                return new_iterators;
            }
        }
    }

    // Pattern 2: Last N statements are individual Assigns matching the iterator vars
    if result.len() >= iter_vars.len() {
        let start = result.len() - iter_vars.len();
        let mut matched = true;
        let mut new_iterators = Vec::new();

        for (i, &var_id) in iter_vars.iter().enumerate() {
            if let HirStmt::Assign {
                target: LValue::Local(tv),
                value,
            } = &result[start + i]
            {
                if *tv == var_id && func.vars.get(var_id).name.is_none() {
                    new_iterators.push(*value);
                } else {
                    matched = false;
                    break;
                }
            } else {
                matched = false;
                break;
            }
        }

        if matched {
            result.truncate(start); // Remove the Assign statements
            return new_iterators;
        }
    }

    iterators.to_vec()
}

/// Find the ForNumBack block reachable from `body_start`, avoiding `header`.
/// This is the block whose terminator is ForNumBack.
fn find_for_back_block(
    func: &HirFunc,
    body_start: NodeIndex,
    header: NodeIndex,
) -> Option<NodeIndex> {
    let mut visited = FxHashSet::default();
    let mut stack = vec![body_start];
    while let Some(node) = stack.pop() {
        if node == header || !visited.insert(node) {
            continue;
        }
        if matches!(func.cfg[node].terminator, Terminator::ForNumBack { .. }) {
            return Some(node);
        }
        for e in func.cfg.edges(node) {
            stack.push(e.target());
        }
    }
    None
}

fn negate_condition(func: &mut HirFunc, condition: ExprId) -> ExprId {
    if let HirExpr::Unary { op: UnOp::Not, operand } = func.exprs.get(condition) {
        return *operand;
    }
    // Invert comparisons directly instead of wrapping in not()
    if let HirExpr::Binary { op, left, right } = func.exprs.get(condition).clone() {
        let inv_op = match op {
            BinOp::CompareEq => Some(BinOp::CompareNe),
            BinOp::CompareNe => Some(BinOp::CompareEq),
            BinOp::CompareLt => Some(BinOp::CompareGe),
            BinOp::CompareLe => Some(BinOp::CompareGt),
            BinOp::CompareGt => Some(BinOp::CompareLe),
            BinOp::CompareGe => Some(BinOp::CompareLt),
            _ => None,
        };
        if let Some(inv_op) = inv_op {
            return func.exprs.alloc(HirExpr::Binary { op: inv_op, left, right });
        }
    }
    func.exprs.alloc(HirExpr::Unary {
        op: UnOp::Not,
        operand: condition,
    })
}
