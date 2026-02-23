use lantern_hir::arena::ExprId;
use lantern_hir::expr::HirExpr;
use lantern_hir::func::HirFunc;
use lantern_hir::stmt::{HirStmt, LValue};
use lantern_hir::var::VarId;

use crate::inline::expr_has_side_effects;

/// Inline temporary variables that are defined and used within the same
/// statement list (branch body).
///
/// Unlike `eliminate_temporaries` which requires globally single-use variables,
/// this pass operates per-statement-list, allowing inlining of temps that are
/// reused across branches of an if/else (same VarId, different def sites).
///
/// Uses targeted `arena.replace()` on specific ExprId slots rather than
/// global `substitute_vars_batch`, so the same VarId can be inlined
/// independently in different branches.
pub fn inline_branch_locals(func: &mut HirFunc) {
    for _ in 0..100 {
        let count = branch_inline_pass(func);
        if count == 0 {
            break;
        }
    }
}

/// Single pass over all CFG blocks. Returns number of inlined variables.
fn branch_inline_pass(func: &mut HirFunc) -> usize {
    let mut total = 0;
    let nodes: Vec<_> = func.cfg.node_indices().collect();
    for node_idx in nodes {
        let stmts = std::mem::take(&mut func.cfg[node_idx].stmts);
        let (new_stmts, count) = process_stmt_list(func, stmts, false);
        func.cfg[node_idx].stmts = new_stmts;
        total += count;
    }
    total
}

/// Process a single statement list: find and inline branch-local temps.
/// Returns (new_stmts, inline_count).
///
/// `in_conditional_body` is true when this list is inside an If/While/For body —
/// we must not empty it completely.
fn process_stmt_list(
    func: &mut HirFunc,
    mut stmts: Vec<HirStmt>,
    in_conditional_body: bool,
) -> (Vec<HirStmt>, usize) {
    let mut total = 0;

    // First, recurse into nested bodies (bottom-up)
    for stmt in stmts.iter_mut() {
        match stmt {
            HirStmt::If {
                then_body,
                elseif_clauses,
                else_body,
                ..
            } => {
                let (new_then, c1) = process_stmt_list(func, std::mem::take(then_body), true);
                *then_body = new_then;
                total += c1;
                for clause in elseif_clauses.iter_mut() {
                    let (new_body, c) =
                        process_stmt_list(func, std::mem::take(&mut clause.body), true);
                    clause.body = new_body;
                    total += c;
                }
                if let Some(body) = else_body {
                    let (new_body, c) = process_stmt_list(func, std::mem::take(body), true);
                    *body = new_body;
                    total += c;
                }
            }
            HirStmt::While { body, .. }
            | HirStmt::Repeat { body, .. }
            | HirStmt::NumericFor { body, .. }
            | HirStmt::GenericFor { body, .. } => {
                let (new_body, c) = process_stmt_list(func, std::mem::take(body), true);
                *body = new_body;
                total += c;
            }
            _ => {}
        }
    }

    // Now process this level: find branch-local inline candidates
    let mut to_remove = Vec::new();
    let mut i = 0;
    while i < stmts.len() {
        if let HirStmt::Assign {
            target: LValue::Local(var_id),
            value: rhs_expr,
        } = &stmts[i]
        {
            let var_id = *var_id;
            let rhs_expr = *rhs_expr;
            let info = func.vars.get(var_id);

            // Only inline unnamed temporaries
            if !info.is_temporary() {
                i += 1;
                continue;
            }

            // Skip Table and Closure RHS — handled by other passes
            if matches!(
                func.exprs.get(rhs_expr),
                HirExpr::Table { .. } | HirExpr::Closure { .. }
            ) {
                i += 1;
                continue;
            }

            // Check for uses BEFORE this def in the same list (loop body safety)
            let uses_before = count_var_uses_in_stmts(&stmts[..i], var_id, &func.exprs);
            if uses_before > 0 {
                i += 1;
                continue;
            }

            // Scan forward for the first statement that uses this var
            let rhs_has_effects = expr_has_side_effects(func, rhs_expr);
            let mut found_use: Option<(usize, ExprId)> = None;
            let mut blocked = false;

            for j in (i + 1)..stmts.len() {
                // Check if stmt j uses var_id
                let uses_in_j = find_var_uses_in_stmt(&stmts[j], var_id, &func.exprs);
                if !uses_in_j.is_empty() {
                    if uses_in_j.len() == 1 {
                        found_use = Some((j, uses_in_j[0]));
                    }
                    // Stop scanning — this is the first mention
                    break;
                }

                // Check interference: stmt j reassigns this var
                if stmt_defines_var(&stmts[j], var_id) {
                    blocked = true;
                    break;
                }

                // Side-effect ordering: if RHS has effects and intervening stmt
                // also has effects, don't reorder
                if rhs_has_effects && stmt_has_side_effects(&stmts[j], func) {
                    blocked = true;
                    break;
                }
            }

            if blocked {
                i += 1;
                continue;
            }

            if let Some((j, use_expr_id)) = found_use {
                // Verify no more uses after j in this list
                let remaining_uses = count_var_uses_in_stmts(&stmts[j + 1..], var_id, &func.exprs);
                if remaining_uses == 0 {
                    // Inline: replace the specific use ExprId with the RHS
                    let replacement = func.exprs.get(rhs_expr).clone();
                    func.exprs.replace(use_expr_id, replacement);
                    to_remove.push(i);
                }
            }
        }
        i += 1;
    }

    // Protect against emptying conditional bodies
    if in_conditional_body && to_remove.len() == stmts.len() && !to_remove.is_empty() {
        to_remove.pop();
    }

    let count = to_remove.len();
    total += count;

    // Remove dead definition statements
    if !to_remove.is_empty() {
        let remove_set: rustc_hash::FxHashSet<usize> = to_remove.into_iter().collect();
        stmts = stmts
            .into_iter()
            .enumerate()
            .filter(|(idx, _)| !remove_set.contains(idx))
            .map(|(_, s)| s)
            .collect();
    }

    (stmts, total)
}

/// Find all ExprId slots in an expression tree that hold `Var(target)`.
fn find_var_uses_in_expr(
    exprs: &lantern_hir::arena::ExprArena,
    root: ExprId,
    target: VarId,
    out: &mut Vec<ExprId>,
) {
    match exprs.get(root) {
        HirExpr::Var(v) => {
            if *v == target {
                out.push(root);
            }
        }
        HirExpr::FieldAccess { table, .. } => {
            find_var_uses_in_expr(exprs, *table, target, out);
        }
        HirExpr::IndexAccess { table, key } => {
            find_var_uses_in_expr(exprs, *table, target, out);
            find_var_uses_in_expr(exprs, *key, target, out);
        }
        HirExpr::Binary { left, right, .. } => {
            find_var_uses_in_expr(exprs, *left, target, out);
            find_var_uses_in_expr(exprs, *right, target, out);
        }
        HirExpr::Unary { operand, .. } => {
            find_var_uses_in_expr(exprs, *operand, target, out);
        }
        HirExpr::Call { func, args, .. } => {
            find_var_uses_in_expr(exprs, *func, target, out);
            for a in args {
                find_var_uses_in_expr(exprs, *a, target, out);
            }
        }
        HirExpr::MethodCall { object, args, .. } => {
            find_var_uses_in_expr(exprs, *object, target, out);
            for a in args {
                find_var_uses_in_expr(exprs, *a, target, out);
            }
        }
        HirExpr::Table { array, hash, .. } => {
            for a in array {
                find_var_uses_in_expr(exprs, *a, target, out);
            }
            for (k, v) in hash {
                find_var_uses_in_expr(exprs, *k, target, out);
                find_var_uses_in_expr(exprs, *v, target, out);
            }
        }
        HirExpr::Concat(parts) => {
            for p in parts {
                find_var_uses_in_expr(exprs, *p, target, out);
            }
        }
        HirExpr::IfExpr {
            condition,
            then_expr,
            else_expr,
        } => {
            find_var_uses_in_expr(exprs, *condition, target, out);
            find_var_uses_in_expr(exprs, *then_expr, target, out);
            find_var_uses_in_expr(exprs, *else_expr, target, out);
        }
        HirExpr::Select { source, .. } => {
            find_var_uses_in_expr(exprs, *source, target, out);
        }
        HirExpr::Literal(_)
        | HirExpr::Global(_)
        | HirExpr::Upvalue(_)
        | HirExpr::VarArg
        | HirExpr::Reg(_)
        | HirExpr::Closure { .. } => {}
    }
}

/// Find all ExprId slots referencing a var in a statement's expressions (uses only).
/// Does NOT count the LHS of `Assign { Local(var_id), .. }` as a use.
/// Does count var refs in LValue::Field/Index table/key expressions.
fn find_var_uses_in_stmt(
    stmt: &HirStmt,
    target: VarId,
    exprs: &lantern_hir::arena::ExprArena,
) -> Vec<ExprId> {
    let mut out = Vec::new();
    match stmt {
        HirStmt::Assign {
            target: lval,
            value,
        } => {
            // Count uses in the RHS expression
            find_var_uses_in_expr(exprs, *value, target, &mut out);
            // Count uses in LValue table/key (reads)
            find_var_uses_in_lvalue(lval, target, exprs, &mut out);
        }
        HirStmt::MultiAssign { targets, values } => {
            for v in values {
                find_var_uses_in_expr(exprs, *v, target, &mut out);
            }
            for t in targets {
                find_var_uses_in_lvalue(t, target, exprs, &mut out);
            }
        }
        HirStmt::LocalDecl { init, .. } => {
            if let Some(expr) = init {
                find_var_uses_in_expr(exprs, *expr, target, &mut out);
            }
        }
        HirStmt::MultiLocalDecl { values, .. } => {
            for v in values {
                find_var_uses_in_expr(exprs, *v, target, &mut out);
            }
        }
        HirStmt::CompoundAssign {
            target: lval,
            value,
            ..
        } => {
            find_var_uses_in_expr(exprs, *value, target, &mut out);
            find_var_uses_in_lvalue(lval, target, exprs, &mut out);
        }
        HirStmt::ExprStmt(expr) => {
            find_var_uses_in_expr(exprs, *expr, target, &mut out);
        }
        HirStmt::Return(values) => {
            for v in values {
                find_var_uses_in_expr(exprs, *v, target, &mut out);
            }
        }
        HirStmt::If {
            condition,
            then_body,
            elseif_clauses,
            else_body,
        } => {
            find_var_uses_in_expr(exprs, *condition, target, &mut out);
            // Also search nested bodies — use might be inside a nested if
            for s in then_body {
                out.extend(find_var_uses_in_stmt(s, target, exprs));
            }
            for clause in elseif_clauses {
                find_var_uses_in_expr(exprs, clause.condition, target, &mut out);
                for s in &clause.body {
                    out.extend(find_var_uses_in_stmt(s, target, exprs));
                }
            }
            if let Some(body) = else_body {
                for s in body {
                    out.extend(find_var_uses_in_stmt(s, target, exprs));
                }
            }
        }
        HirStmt::While { condition, body } => {
            find_var_uses_in_expr(exprs, *condition, target, &mut out);
            for s in body {
                out.extend(find_var_uses_in_stmt(s, target, exprs));
            }
        }
        HirStmt::Repeat { body, condition } => {
            for s in body {
                out.extend(find_var_uses_in_stmt(s, target, exprs));
            }
            find_var_uses_in_expr(exprs, *condition, target, &mut out);
        }
        HirStmt::NumericFor {
            start,
            limit,
            step,
            body,
            ..
        } => {
            find_var_uses_in_expr(exprs, *start, target, &mut out);
            find_var_uses_in_expr(exprs, *limit, target, &mut out);
            if let Some(s) = step {
                find_var_uses_in_expr(exprs, *s, target, &mut out);
            }
            for s in body {
                out.extend(find_var_uses_in_stmt(s, target, exprs));
            }
        }
        HirStmt::GenericFor {
            iterators, body, ..
        } => {
            for iter in iterators {
                find_var_uses_in_expr(exprs, *iter, target, &mut out);
            }
            for s in body {
                out.extend(find_var_uses_in_stmt(s, target, exprs));
            }
        }
        HirStmt::FunctionDef { func_expr, .. } | HirStmt::LocalFunctionDef { func_expr, .. } => {
            find_var_uses_in_expr(exprs, *func_expr, target, &mut out);
        }
        HirStmt::Break
        | HirStmt::Continue
        | HirStmt::CloseUpvals { .. }
        | HirStmt::RegAssign { .. } => {}
    }
    out
}

/// Find var uses in LValue table/key expressions (these are reads).
fn find_var_uses_in_lvalue(
    lval: &LValue,
    target: VarId,
    exprs: &lantern_hir::arena::ExprArena,
    out: &mut Vec<ExprId>,
) {
    match lval {
        LValue::Field { table, .. } => {
            find_var_uses_in_expr(exprs, *table, target, out);
        }
        LValue::Index { table, key } => {
            find_var_uses_in_expr(exprs, *table, target, out);
            find_var_uses_in_expr(exprs, *key, target, out);
        }
        LValue::Local(_) | LValue::Global(_) | LValue::Upvalue(_) => {}
    }
}

/// Count total uses of a var across a slice of statements.
fn count_var_uses_in_stmts(
    stmts: &[HirStmt],
    target: VarId,
    exprs: &lantern_hir::arena::ExprArena,
) -> usize {
    let mut count = 0;
    for stmt in stmts {
        count += find_var_uses_in_stmt(stmt, target, exprs).len();
    }
    count
}

/// Check if a statement assigns to (defines) a given variable.
fn stmt_defines_var(stmt: &HirStmt, var_id: VarId) -> bool {
    match stmt {
        HirStmt::Assign {
            target: LValue::Local(v),
            ..
        } => *v == var_id,
        HirStmt::MultiAssign { targets, .. } => targets
            .iter()
            .any(|t| matches!(t, LValue::Local(v) if *v == var_id)),
        HirStmt::LocalDecl { var, .. } => *var == var_id,
        HirStmt::MultiLocalDecl { vars, .. } => vars.contains(&var_id),
        _ => false,
    }
}

/// Check if a statement has observable side effects.
fn stmt_has_side_effects(stmt: &HirStmt, func: &HirFunc) -> bool {
    match stmt {
        HirStmt::Assign { value, .. } => expr_has_side_effects(func, *value),
        HirStmt::MultiAssign { values, .. } => {
            values.iter().any(|v| expr_has_side_effects(func, *v))
        }
        HirStmt::LocalDecl { init, .. } => init.map_or(false, |e| expr_has_side_effects(func, e)),
        HirStmt::MultiLocalDecl { values, .. } => {
            values.iter().any(|v| expr_has_side_effects(func, *v))
        }
        HirStmt::ExprStmt(e) => expr_has_side_effects(func, *e),
        HirStmt::CompoundAssign { value, .. } => expr_has_side_effects(func, *value),
        // Control flow and returns always have effects
        HirStmt::Return(_)
        | HirStmt::Break
        | HirStmt::Continue
        | HirStmt::If { .. }
        | HirStmt::While { .. }
        | HirStmt::Repeat { .. }
        | HirStmt::NumericFor { .. }
        | HirStmt::GenericFor { .. }
        | HirStmt::FunctionDef { .. }
        | HirStmt::LocalFunctionDef { .. } => true,
        HirStmt::CloseUpvals { .. } | HirStmt::RegAssign { .. } => false,
    }
}
