use petgraph::stable_graph::NodeIndex;
use petgraph::visit::EdgeRef;
use rustc_hash::FxHashSet;

use lantern_hir::arena::ExprId;
use lantern_hir::cfg::{EdgeKind, Terminator};
use lantern_hir::expr::HirExpr;
use lantern_hir::func::HirFunc;
use lantern_hir::stmt::{HirStmt, LValue};
use lantern_hir::types::LuaValue;
use lantern_hir::var::VarId;

use super::cfg_helpers::{branch_successors, negate_condition};
use super::postdom::PostDomTree;
use super::structure_region;
use super::LoopCtx;
use super::LoopResult;

/// Try to structure `node` as a while-loop header.
///
/// A while-loop is detected when a Branch node's body has a path back
/// to the header node (back-edge), WITHOUT passing through the `stop`
/// node (which represents the outer loop header, if any).
pub(super) fn try_structure_while(
    func: &mut HirFunc,
    node: NodeIndex,
    stop: Option<NodeIndex>,
    _outer_loop: Option<&LoopCtx>,
    visited: &mut FxHashSet<NodeIndex>,
    pdom: &PostDomTree,
) -> Option<LoopResult> {
    let condition = match &func.cfg[node].terminator {
        Terminator::Branch { condition, .. } => *condition,
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
    //
    // We pass `stop` to prevent the DFS from traversing through the outer
    // loop header. Without this, an if-statement inside a loop body would
    // be misidentified as a nested while loop because its branches reach
    // the outer header and loop back to this node.
    //
    // Also treat the enclosing loop's exit as a barrier. Inside a for-loop
    // body, a branch that exits the for-loop (jump to exit node → outer
    // loop → back to this node) is a break, not a while-loop back-edge.
    let extra_barrier = _outer_loop.and_then(|lctx| lctx.exit);
    let (body_start, exit_node, loop_condition) =
        if has_back_edge_to(&func.cfg, then_n, node, stop, extra_barrier) {
            // Then-branch loops back: body=then, exit=else, condition as-is
            (then_n, else_n, condition)
        } else if has_back_edge_to(&func.cfg, else_n, node, stop, extra_barrier) {
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

    let body_stmts = structure_region(func, body_start, Some(node), Some(&loop_ctx), visited, pdom);

    let mut all_stmts = Vec::new();

    if header_stmts.is_empty() {
        // Simple while-loop: no header computations, just `while cond do ... end`
        all_stmts.push(HirStmt::While {
            condition: loop_condition,
            body: body_stmts,
        });
    } else {
        // The header block has statements that compute the loop condition
        // (e.g. `key = string.format(...)`). These re-execute every iteration
        // via the back-edge, so they belong INSIDE the loop body.
        //
        // Emit: `while true do <header_stmts>; if not <cond> then break end; <body> end`
        let true_expr = func
            .exprs
            .alloc(HirExpr::Literal(LuaValue::Boolean(true)));
        let neg_cond = negate_condition(func, loop_condition);

        let mut loop_body = Vec::new();
        loop_body.extend(header_stmts);
        loop_body.push(HirStmt::If {
            condition: neg_cond,
            negated: true,
            then_body: vec![HirStmt::Break],
            elseif_clauses: Vec::new(),
            else_body: None,
        });
        loop_body.extend(body_stmts);

        all_stmts.push(HirStmt::While {
            condition: true_expr,
            body: loop_body,
        });
    }

    Some(LoopResult {
        stmts: all_stmts,
        next: Some(exit_node),
    })
}

/// Check if any node reachable from `start` has a direct edge to `header`,
/// without passing through `barrier` (the outer loop header, if any).
///
/// The barrier prevents false positives: an if-statement inside a while-loop
/// body has branches that eventually reach the outer loop header, which loops
/// back to the if-statement's node. Without the barrier, this transitive path
/// would make the if-statement look like a nested while loop.
///
/// Also skips LoopBack edges from ForNumBack/ForGenBack terminators — those
/// belong to for-loops and should not trigger while-loop detection.
pub(super) fn has_back_edge_to(
    cfg: &lantern_hir::cfg::CfgGraph,
    start: NodeIndex,
    header: NodeIndex,
    barrier: Option<NodeIndex>,
    extra_barrier: Option<NodeIndex>,
) -> bool {
    let mut visited = FxHashSet::default();
    let mut stack = vec![start];
    while let Some(node) = stack.pop() {
        if node == header || Some(node) == barrier || Some(node) == extra_barrier || !visited.insert(node) {
            continue;
        }
        // Don't follow for-loop back-edges — they're not while-loop structure.
        // This includes both ForNumBack/ForGenBack LoopBack edges (iteration)
        // and ForNumPrep/ForGenPrep LoopBack edges (entry into the loop body).
        let is_for_back = matches!(
            cfg[node].terminator,
            Terminator::ForNumBack { .. }
                | Terminator::ForGenBack { .. }
                | Terminator::ForNumPrep { .. }
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

/// Structure a numeric for-loop from a ForNumPrep terminator.
///
/// CFG shape:
///   [ForNumPrep] --LoopBack--> [body...] --> [ForNumBack] --LoopBack--> body
///                --LoopExit--> [exit]        [ForNumBack] --LoopExit--> exit
///
/// The structurer produces HirStmt::NumericFor and returns the exit node.
pub(super) fn structure_for_num(
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
    pdom: &PostDomTree,
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
    let body_stmts = structure_region(func, body_start, back_block, Some(&loop_ctx), visited, pdom);

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
pub(super) fn structure_for_gen(
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
    pdom: &PostDomTree,
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
    let vars: Vec<VarId> = (0..var_count)
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
    let body_stmts = structure_region(func, body_start, Some(node), Some(&loop_ctx), visited, pdom);

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
            let all_unnamed = iter_vars.iter().all(|v| func.vars.get(*v).name.is_none());
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
