use rustc_hash::{FxHashMap, FxHashSet};

use lantern_hir::arena::ExprId;
use lantern_hir::expr::HirExpr;
use lantern_hir::func::HirFunc;
use lantern_hir::stmt::{HirStmt, LValue};
use lantern_hir::var::VarId;

/// Eliminate temporary variables by inlining their expressions.
///
/// A temporary is a variable with:
/// - No debug name (unnamed compiler-generated)
/// - Exactly one definition site
/// - Exactly one use site (or zero uses — dead store)
///
/// For single-use temporaries, we replace every `Var(temp)` reference in the
/// expression arena with the temp's RHS expression, then remove the dead
/// assignment statement. This is O(1) per inline thanks to the arena.
///
/// Works on both flat CFG blocks and structured (nested) statements.
///
/// Iterates until no more temporaries can be eliminated.
pub fn eliminate_temporaries(func: &mut HirFunc) {
    loop {
        let inlined = inline_pass(func);
        if inlined == 0 {
            break;
        }
    }
}

/// Single pass: find and inline all eligible temporaries.
/// Returns the number of inlined variables.
fn inline_pass(func: &mut HirFunc) -> usize {
    // Step 1: Count uses of each VarId across all expressions and statements.
    let use_counts = count_uses(func);

    // Step 2: Find inline candidates by walking all stmts (including nested).
    let mut single_use: FxHashMap<VarId, ExprId> = FxHashMap::default();
    let mut dead_stores: FxHashSet<VarId> = FxHashSet::default();
    let mut dead_calls: FxHashSet<VarId> = FxHashSet::default();
    let mut dead_call_extracts: FxHashSet<VarId> = FxHashSet::default();

    for node_idx in func.cfg.node_indices() {
        let block = &func.cfg[node_idx];
        find_candidates_in_stmts(
            &block.stmts,
            func,
            &use_counts,
            &mut single_use,
            &mut dead_stores,
            &mut dead_calls,
            &mut dead_call_extracts,
        );
    }

    let total = single_use.len() + dead_stores.len() + dead_calls.len() + dead_call_extracts.len();
    if total == 0 {
        return 0;
    }

    // Step 3: Apply arena substitutions for single-use inlines (batch)
    func.exprs.substitute_vars_batch(&single_use);

    // Step 4: Walk all stmts and remove/transform candidates.
    let all_nodes: Vec<_> = func.cfg.node_indices().collect();
    for node_idx in all_nodes {
        let stmts = std::mem::take(&mut func.cfg[node_idx].stmts);
        func.cfg[node_idx].stmts = apply_removals(
            stmts,
            func,
            &single_use,
            &dead_stores,
            &dead_calls,
            &dead_call_extracts,
        );
    }

    total
}

/// Recursively find inline candidates in a statement list.
fn find_candidates_in_stmts(
    stmts: &[HirStmt],
    func: &HirFunc,
    use_counts: &FxHashMap<VarId, usize>,
    single_use: &mut FxHashMap<VarId, ExprId>,
    dead_stores: &mut FxHashSet<VarId>,
    dead_calls: &mut FxHashSet<VarId>,
    dead_call_extracts: &mut FxHashSet<VarId>,
) {
    for stmt in stmts {
        // Check this statement for a candidate
        if let HirStmt::Assign {
            target: LValue::Local(var_id),
            value,
        } = stmt
        {
            let info = func.vars.get(*var_id);
            let has_name = info.name.is_some();
            let is_closure = matches!(func.exprs.get(*value), HirExpr::Closure { .. });
            let uses = use_counts.get(var_id).copied().unwrap_or(0);

            // Named variables are generally kept (not inlined), except:
            // - Closures with exactly 1 use can be inlined at the call site
            if !(has_name && !(is_closure && uses == 1)) {
                if uses == 0 {
                    if !expr_has_side_effects(func, *value) {
                        dead_stores.insert(*var_id);
                    } else if is_statement_expr(func, *value) {
                        dead_calls.insert(*var_id);
                    } else {
                        dead_call_extracts.insert(*var_id);
                    }
                } else if uses == 1 {
                    if !(matches!(func.exprs.get(*value), HirExpr::Table { .. })
                        && is_var_used_as_table_target(func, *var_id))
                    {
                        single_use.insert(*var_id, *value);
                    }
                }
            }
        }

        // Recurse into nested bodies
        match stmt {
            HirStmt::If { then_body, elseif_clauses, else_body, .. } => {
                find_candidates_in_stmts(then_body, func, use_counts, single_use, dead_stores, dead_calls, dead_call_extracts);
                for clause in elseif_clauses {
                    find_candidates_in_stmts(&clause.body, func, use_counts, single_use, dead_stores, dead_calls, dead_call_extracts);
                }
                if let Some(body) = else_body {
                    find_candidates_in_stmts(body, func, use_counts, single_use, dead_stores, dead_calls, dead_call_extracts);
                }
            }
            HirStmt::While { body, .. } | HirStmt::Repeat { body, .. }
            | HirStmt::NumericFor { body, .. } | HirStmt::GenericFor { body, .. } => {
                find_candidates_in_stmts(body, func, use_counts, single_use, dead_stores, dead_calls, dead_call_extracts);
            }
            _ => {}
        }
    }
}

/// Recursively walk stmts and remove/transform inlined candidates.
fn apply_removals(
    stmts: Vec<HirStmt>,
    func: &HirFunc,
    single_use: &FxHashMap<VarId, ExprId>,
    dead_stores: &FxHashSet<VarId>,
    dead_calls: &FxHashSet<VarId>,
    dead_call_extracts: &FxHashSet<VarId>,
) -> Vec<HirStmt> {
    let mut result = Vec::with_capacity(stmts.len());

    for stmt in stmts {
        // Check if this Assign should be removed/transformed
        if let HirStmt::Assign {
            target: LValue::Local(var_id),
            value,
        } = &stmt
        {
            if single_use.contains_key(var_id) || dead_stores.contains(var_id) {
                continue; // Remove
            }
            if dead_calls.contains(var_id) {
                result.push(HirStmt::ExprStmt(*value));
                continue;
            }
            if dead_call_extracts.contains(var_id) {
                let mut calls = Vec::new();
                collect_side_effect_calls(func, *value, &mut calls);
                if calls.is_empty() {
                    continue; // Remove
                }
                for call_expr in calls {
                    result.push(HirStmt::ExprStmt(call_expr));
                }
                continue;
            }
        }

        // Recurse into nested bodies
        let stmt = match stmt {
            HirStmt::If { condition, then_body, elseif_clauses, else_body } => {
                let then_body = apply_removals(then_body, func, single_use, dead_stores, dead_calls, dead_call_extracts);
                let elseif_clauses = elseif_clauses.into_iter().map(|c| {
                    lantern_hir::stmt::ElseIfClause {
                        condition: c.condition,
                        body: apply_removals(c.body, func, single_use, dead_stores, dead_calls, dead_call_extracts),
                    }
                }).collect();
                let else_body = else_body.map(|b| apply_removals(b, func, single_use, dead_stores, dead_calls, dead_call_extracts));
                HirStmt::If { condition, then_body, elseif_clauses, else_body }
            }
            HirStmt::While { condition, body } => {
                let body = apply_removals(body, func, single_use, dead_stores, dead_calls, dead_call_extracts);
                HirStmt::While { condition, body }
            }
            HirStmt::Repeat { condition, body } => {
                let body = apply_removals(body, func, single_use, dead_stores, dead_calls, dead_call_extracts);
                HirStmt::Repeat { condition, body }
            }
            HirStmt::NumericFor { var, start, limit, step, body } => {
                let body = apply_removals(body, func, single_use, dead_stores, dead_calls, dead_call_extracts);
                HirStmt::NumericFor { var, start, limit, step, body }
            }
            HirStmt::GenericFor { vars, iterators, body } => {
                let body = apply_removals(body, func, single_use, dead_stores, dead_calls, dead_call_extracts);
                HirStmt::GenericFor { vars, iterators, body }
            }
            other => other,
        };
        result.push(stmt);
    }

    result
}

/// Count how many times each VarId is used as a value (read).
/// Counts references in:
/// - All expressions in the arena (Var nodes)
/// - Statement targets that read vars (compound assign, etc.)
fn count_uses(func: &HirFunc) -> FxHashMap<VarId, usize> {
    let mut counts: FxHashMap<VarId, usize> = FxHashMap::default();

    // Count uses in expressions
    for i in 0..func.exprs.len() {
        let expr_id = ExprId(i as u32);
        if let HirExpr::Var(var_id) = func.exprs.get(expr_id) {
            *counts.entry(*var_id).or_insert(0) += 1;
        }
    }

    // Count uses in statement LValues that read (Field/Index tables can be vars)
    for node_idx in func.cfg.node_indices() {
        for stmt in &func.cfg[node_idx].stmts {
            count_uses_in_stmt(stmt, func, &mut counts);
        }
    }

    counts
}

fn count_uses_in_stmt(
    stmt: &HirStmt,
    func: &HirFunc,
    counts: &mut FxHashMap<VarId, usize>,
) {
    match stmt {
        HirStmt::If { then_body, elseif_clauses, else_body, .. } => {
            for s in then_body {
                count_uses_in_stmt(s, func, counts);
            }
            for clause in elseif_clauses {
                for s in &clause.body {
                    count_uses_in_stmt(s, func, counts);
                }
            }
            if let Some(body) = else_body {
                for s in body {
                    count_uses_in_stmt(s, func, counts);
                }
            }
        }
        HirStmt::While { body, .. } | HirStmt::Repeat { body, .. } => {
            for s in body {
                count_uses_in_stmt(s, func, counts);
            }
        }
        HirStmt::NumericFor { body, .. } | HirStmt::GenericFor { body, .. } => {
            for s in body {
                count_uses_in_stmt(s, func, counts);
            }
        }
        _ => {}
    }
}

/// Check if an expression has observable side effects (calls, etc.).
fn expr_has_side_effects(func: &HirFunc, expr_id: ExprId) -> bool {
    match func.exprs.get(expr_id) {
        HirExpr::Call { .. } | HirExpr::MethodCall { .. } => true,
        HirExpr::Binary { left, right, .. } => {
            expr_has_side_effects(func, *left) || expr_has_side_effects(func, *right)
        }
        HirExpr::Unary { operand, .. } => expr_has_side_effects(func, *operand),
        HirExpr::Concat(operands) => operands.iter().any(|o| expr_has_side_effects(func, *o)),
        HirExpr::Table { array, hash } => {
            array.iter().any(|a| expr_has_side_effects(func, *a))
                || hash
                    .iter()
                    .any(|(k, v)| expr_has_side_effects(func, *k) || expr_has_side_effects(func, *v))
        }
        HirExpr::FieldAccess { table, .. } => expr_has_side_effects(func, *table),
        HirExpr::IndexAccess { table, key } => {
            expr_has_side_effects(func, *table) || expr_has_side_effects(func, *key)
        }
        HirExpr::IfExpr { condition, then_expr, else_expr } => {
            expr_has_side_effects(func, *condition)
                || expr_has_side_effects(func, *then_expr)
                || expr_has_side_effects(func, *else_expr)
        }
        HirExpr::Select { source, .. } => expr_has_side_effects(func, *source),
        _ => false,
    }
}

/// Check if a variable is used as the table target of a FieldAccess/IndexAccess
/// (expression side) or Field/Index (LValue side).
fn is_var_used_as_table_target(func: &HirFunc, var_id: VarId) -> bool {
    // Check expression arena: FieldAccess/IndexAccess table positions
    for i in 0..func.exprs.len() {
        let expr_id = ExprId(i as u32);
        match func.exprs.get(expr_id) {
            HirExpr::FieldAccess { table, .. } | HirExpr::IndexAccess { table, .. } => {
                if matches!(func.exprs.get(*table), HirExpr::Var(v) if *v == var_id) {
                    return true;
                }
            }
            _ => {}
        }
    }
    // Check LValues in statements: Field/Index table positions
    for node_idx in func.cfg.node_indices() {
        for stmt in &func.cfg[node_idx].stmts {
            if lvalue_uses_var_as_table(stmt, func, var_id) {
                return true;
            }
        }
    }
    false
}

fn lvalue_uses_var_as_table(stmt: &HirStmt, func: &HirFunc, var_id: VarId) -> bool {
    match stmt {
        HirStmt::Assign { target, .. } | HirStmt::CompoundAssign { target, .. } => {
            lvalue_has_var_table(target, func, var_id)
        }
        HirStmt::MultiAssign { targets, .. } => {
            targets.iter().any(|t| lvalue_has_var_table(t, func, var_id))
        }
        HirStmt::If { then_body, elseif_clauses, else_body, .. } => {
            then_body.iter().any(|s| lvalue_uses_var_as_table(s, func, var_id))
                || elseif_clauses.iter().any(|c| c.body.iter().any(|s| lvalue_uses_var_as_table(s, func, var_id)))
                || else_body.as_ref().is_some_and(|b| b.iter().any(|s| lvalue_uses_var_as_table(s, func, var_id)))
        }
        HirStmt::While { body, .. } | HirStmt::Repeat { body, .. }
        | HirStmt::NumericFor { body, .. } | HirStmt::GenericFor { body, .. } => {
            body.iter().any(|s| lvalue_uses_var_as_table(s, func, var_id))
        }
        _ => false,
    }
}

fn lvalue_has_var_table(lv: &LValue, func: &HirFunc, var_id: VarId) -> bool {
    match lv {
        LValue::Field { table, .. } | LValue::Index { table, .. } => {
            matches!(func.exprs.get(*table), HirExpr::Var(v) if *v == var_id)
        }
        _ => false,
    }
}

/// Check if an expression is valid as a standalone Lua statement.
fn is_statement_expr(func: &HirFunc, expr_id: ExprId) -> bool {
    matches!(
        func.exprs.get(expr_id),
        HirExpr::Call { .. } | HirExpr::MethodCall { .. }
    )
}

/// Recursively collect all Call/MethodCall sub-expressions from an expression tree.
fn collect_side_effect_calls(func: &HirFunc, expr_id: ExprId, out: &mut Vec<ExprId>) {
    match func.exprs.get(expr_id) {
        HirExpr::Call { .. } | HirExpr::MethodCall { .. } => {
            out.push(expr_id);
        }
        HirExpr::Table { array, hash } => {
            let array = array.clone();
            let hash = hash.clone();
            for item in &array {
                collect_side_effect_calls(func, *item, out);
            }
            for (k, v) in &hash {
                collect_side_effect_calls(func, *k, out);
                collect_side_effect_calls(func, *v, out);
            }
        }
        HirExpr::Binary { left, right, .. } => {
            let (left, right) = (*left, *right);
            collect_side_effect_calls(func, left, out);
            collect_side_effect_calls(func, right, out);
        }
        HirExpr::Unary { operand, .. } => {
            let operand = *operand;
            collect_side_effect_calls(func, operand, out);
        }
        HirExpr::Concat(operands) => {
            let operands = operands.clone();
            for op in &operands {
                collect_side_effect_calls(func, *op, out);
            }
        }
        HirExpr::IfExpr { condition, then_expr, else_expr } => {
            let (c, t, e) = (*condition, *then_expr, *else_expr);
            collect_side_effect_calls(func, c, out);
            collect_side_effect_calls(func, t, out);
            collect_side_effect_calls(func, e, out);
        }
        HirExpr::Select { source, .. } => {
            let source = *source;
            collect_side_effect_calls(func, source, out);
        }
        HirExpr::FieldAccess { table, .. } => {
            let table = *table;
            collect_side_effect_calls(func, table, out);
        }
        HirExpr::IndexAccess { table, key } => {
            let (table, key) = (*table, *key);
            collect_side_effect_calls(func, table, out);
            collect_side_effect_calls(func, key, out);
        }
        _ => {}
    }
}
