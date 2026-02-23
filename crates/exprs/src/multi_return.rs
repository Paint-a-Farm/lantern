use lantern_hir::arena::ExprId;
use lantern_hir::expr::HirExpr;
use lantern_hir::func::HirFunc;
use lantern_hir::stmt::{HirStmt, LValue};

/// Collapse consecutive Select assignments from the same call into MultiAssign.
///
/// Recognizes the pattern:
///   var_A = Call { ... }          (or MethodCall)
///   var_B = Select { source: call_expr, index: 1 }
///   var_C = Select { source: call_expr, index: 2 }
///
/// Transforms into:
///   MultiAssign { targets: [A, B, C], values: [call_expr] }
///
/// The call expression's result_count is updated to match the number of targets.
///
/// Also handles VarArg multi-capture:
///   var_A = VarArg
///   var_B = Select { source: vararg_expr, index: 1 }
pub fn collapse_multi_returns(func: &mut HirFunc) {
    let nodes: Vec<_> = func.cfg.node_indices().collect();

    for node_idx in nodes {
        let stmts = &func.cfg[node_idx].stmts;
        if stmts.is_empty() {
            continue;
        }

        // Find groups to collapse, working backwards to not invalidate indices
        let groups = find_multi_return_groups(stmts, func);

        if groups.is_empty() {
            continue;
        }

        // Apply groups in reverse order (by start index) to preserve earlier indices
        let mut new_stmts = func.cfg[node_idx].stmts.clone();
        let mut groups = groups;
        groups.sort_by(|a, b| b.start_idx.cmp(&a.start_idx));

        for group in &groups {
            // Build the MultiAssign
            let targets: Vec<LValue> = group.targets.clone();
            let values = vec![group.call_expr];

            // Update the call's result_count to match
            update_result_count(&mut func.exprs, group.call_expr, targets.len() as u8);

            let multi = HirStmt::MultiAssign { targets, values };

            // Replace the range [start..start+count) with the single MultiAssign
            new_stmts.splice(
                group.start_idx..group.start_idx + group.count,
                std::iter::once(multi),
            );
        }

        func.cfg[node_idx].stmts = new_stmts;
    }
}

struct MultiReturnGroup {
    start_idx: usize,
    count: usize,
    call_expr: ExprId,
    targets: Vec<LValue>,
}

fn find_multi_return_groups(stmts: &[HirStmt], func: &HirFunc) -> Vec<MultiReturnGroup> {
    let mut groups = Vec::new();
    let mut i = 0;

    while i < stmts.len() {
        // Look for a Call/MethodCall/VarArg assignment
        if let Some((target, call_expr)) = get_call_assign(&stmts[i]) {
            if is_multi_return_source(func, call_expr) {
                let mut targets = vec![target];
                let mut j = i + 1;

                // Collect consecutive Select assignments referencing this call
                while j < stmts.len() {
                    if let Some((sel_target, sel_source, sel_index)) =
                        get_select_assign(&stmts[j], func)
                    {
                        if sel_source == call_expr {
                            debug_assert_eq!(
                                sel_index as usize,
                                targets.len(),
                                "Select index out of order"
                            );
                            targets.push(sel_target);
                            j += 1;
                            continue;
                        }
                    }
                    break;
                }

                if targets.len() > 1 {
                    groups.push(MultiReturnGroup {
                        start_idx: i,
                        count: targets.len(),
                        call_expr,
                        targets,
                    });
                    i = j;
                    continue;
                }
            }
        }
        i += 1;
    }

    groups
}

/// Check if a statement is `Assign { target, value }` where value is a Call/MethodCall/VarArg.
fn get_call_assign(stmt: &HirStmt) -> Option<(LValue, ExprId)> {
    if let HirStmt::Assign { target, value } = stmt {
        Some((target.clone(), *value))
    } else {
        None
    }
}

/// Check if an expression is a multi-return source (Call, MethodCall, VarArg).
fn is_multi_return_source(func: &HirFunc, expr_id: ExprId) -> bool {
    matches!(
        func.exprs.get(expr_id),
        HirExpr::Call { .. } | HirExpr::MethodCall { .. } | HirExpr::VarArg
    )
}

/// Check if a statement is `Assign { target, Select { source, index } }`.
/// Returns (target, source_expr, index).
fn get_select_assign(stmt: &HirStmt, func: &HirFunc) -> Option<(LValue, ExprId, u8)> {
    if let HirStmt::Assign { target, value } = stmt {
        if let HirExpr::Select { source, index } = func.exprs.get(*value) {
            return Some((target.clone(), *source, *index));
        }
    }
    None
}

/// Update the result_count of a Call or MethodCall expression.
fn update_result_count(exprs: &mut lantern_hir::arena::ExprArena, expr_id: ExprId, count: u8) {
    match exprs.get_mut(expr_id) {
        HirExpr::Call { result_count, .. } => *result_count = count,
        HirExpr::MethodCall { result_count, .. } => *result_count = count,
        _ => {}
    }
}
