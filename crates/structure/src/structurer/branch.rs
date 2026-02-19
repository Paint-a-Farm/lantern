use petgraph::stable_graph::NodeIndex;
use petgraph::visit::EdgeRef;
use rustc_hash::FxHashSet;

use lantern_hir::arena::ExprId;
use lantern_hir::cfg::EdgeKind;
use lantern_hir::func::HirFunc;
use lantern_hir::stmt::{ElseIfClause, HirStmt};

use super::LoopCtx;
use super::cfg_helpers::{branch_successors, find_join_point, negate_condition};
use super::guard::{ends_with_exit, is_guard_clause};
use super::structure_region;

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
