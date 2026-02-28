use rustc_hash::FxHashMap;

use lantern_hir::arena::ExprId;
use lantern_hir::expr::HirExpr;
use lantern_hir::func::HirFunc;
use lantern_hir::stmt::{HirStmt, LValue};
use lantern_hir::var::{VarId, VarInfo};

/// Split multi-def unnamed temporaries into separate single-def variables.
///
/// When the Luau compiler reuses a register for sequential temporaries (e.g.
/// `R6 = data; call(R6); R6 = data; call(R6)`), the var solver may assign
/// the same VarId to all defs/uses of that register. This creates multi-def
/// variables that the inline pass cannot handle.
///
/// This pass walks each statement list (including nested bodies) and for each
/// unnamed variable that is defined more than once, creates fresh VarIds for
/// the 2nd, 3rd, ... definitions and rewrites the uses between consecutive
/// defs to reference the new VarId.
pub fn split_multi_def_temps(func: &mut HirFunc) {
    let nodes: Vec<_> = func.cfg.node_indices().collect();
    for node_idx in nodes {
        let stmts = std::mem::take(&mut func.cfg[node_idx].stmts);
        func.cfg[node_idx].stmts = split_stmts(stmts, func);
    }
}

fn split_stmts(stmts: Vec<HirStmt>, func: &mut HirFunc) -> Vec<HirStmt> {
    // Phase 1: Find unnamed variables with multiple defs in this statement list.
    let mut def_count: FxHashMap<VarId, usize> = FxHashMap::default();
    for stmt in &stmts {
        if let Some(var_id) = get_def_var(stmt) {
            let info = func.vars.get(var_id);
            if info.name.is_none() && !info.is_param && !info.is_loop_var {
                *def_count.entry(var_id).or_insert(0) += 1;
            }
        }
    }

    // Keep only vars with 2+ defs
    let multi_defs: FxHashMap<VarId, usize> = def_count
        .into_iter()
        .filter(|(_, count)| *count >= 2)
        .collect();

    if multi_defs.is_empty() {
        // Still recurse into nested bodies
        return stmts
            .into_iter()
            .map(|s| recurse_into_bodies(s, func))
            .collect();
    }

    // Phase 2: Walk statements and split multi-def variables.
    //
    // For each multi-def var, on the 2nd+ definition:
    // 1. Create a new VarId
    // 2. Rewrite the def statement to use the new VarId
    // 3. Track the rename: old VarId → new VarId
    //
    // Between defs, rewrite all Var(old) references in expressions to Var(new).
    // When we see a new def of the same original var, start a new rename.
    //
    // We track per-original-var which replacement VarId is "current".
    let mut current_replacement: FxHashMap<VarId, VarId> = FxHashMap::default();
    // Count of defs seen so far per original var.
    let mut seen_defs: FxHashMap<VarId, usize> = FxHashMap::default();
    // Batch of expression rewrites to apply: old ExprId containing Var(orig) → Var(replacement)
    // We process statement-by-statement, applying rewrites between defs.

    let mut result = Vec::with_capacity(stmts.len());

    for stmt in stmts {
        let def_var = get_def_var(&stmt);

        // Check if this statement defines a multi-def var
        if let Some(var_id) = def_var {
            if multi_defs.contains_key(&var_id) {
                let count = seen_defs.entry(var_id).or_insert(0);
                *count += 1;

                if *count >= 2 {
                    // 2nd+ definition: create a new VarId
                    let new_var = func.vars.alloc(VarInfo::new());
                    current_replacement.insert(var_id, new_var);

                    // Rewrite the def to use the new VarId
                    let stmt = rewrite_def(stmt, var_id, new_var);
                    let stmt = recurse_into_bodies(stmt, func);
                    result.push(stmt);
                    continue;
                }
                // First def: no rewrite needed, but clear any stale replacement
                current_replacement.remove(&var_id);
            }
        }

        // Apply current rewrites to uses in this statement's expressions
        let stmt = if !current_replacement.is_empty() {
            rewrite_uses_in_stmt(stmt, &current_replacement, &mut func.exprs)
        } else {
            stmt
        };

        let stmt = recurse_into_bodies(stmt, func);
        result.push(stmt);
    }

    result
}

/// Get the VarId being defined by an Assign{Local} or LocalDecl statement.
fn get_def_var(stmt: &HirStmt) -> Option<VarId> {
    match stmt {
        HirStmt::Assign {
            target: LValue::Local(var_id),
            ..
        } => Some(*var_id),
        HirStmt::LocalDecl {
            var,
            init: Some(_),
            ..
        } => Some(*var),
        _ => None,
    }
}

/// Rewrite a def statement to use a new VarId.
fn rewrite_def(stmt: HirStmt, old_var: VarId, new_var: VarId) -> HirStmt {
    match stmt {
        HirStmt::Assign {
            target: LValue::Local(var_id),
            value,
        } if var_id == old_var => HirStmt::Assign {
            target: LValue::Local(new_var),
            value,
        },
        HirStmt::LocalDecl {
            var,
            init: Some(value),
        } if var == old_var => HirStmt::Assign {
            target: LValue::Local(new_var),
            value,
        },
        other => other,
    }
}

/// Rewrite Var references in a statement's expressions.
///
/// For each expression referenced by this statement, if it's a Var(old_var)
/// and old_var has a current replacement, replace the expression with Var(new_var).
fn rewrite_uses_in_stmt(
    stmt: HirStmt,
    replacements: &FxHashMap<VarId, VarId>,
    exprs: &mut lantern_hir::arena::ExprArena,
) -> HirStmt {
    // Collect all ExprIds from this statement
    let mut expr_ids = Vec::new();
    collect_stmt_use_expr_ids(&stmt, &mut expr_ids);

    // For each expression, recursively check for Var nodes to rewrite
    let mut visited = rustc_hash::FxHashSet::default();
    for expr_id in expr_ids {
        rewrite_var_refs(expr_id, replacements, exprs, &mut visited);
    }

    stmt
}

/// Recursively rewrite Var references in an expression tree.
fn rewrite_var_refs(
    expr_id: ExprId,
    replacements: &FxHashMap<VarId, VarId>,
    exprs: &mut lantern_hir::arena::ExprArena,
    visited: &mut rustc_hash::FxHashSet<ExprId>,
) {
    if !visited.insert(expr_id) {
        return;
    }

    // First check if this is a Var that needs rewriting
    if let HirExpr::Var(var_id) = exprs.get(expr_id) {
        if let Some(&new_var) = replacements.get(var_id) {
            exprs.replace(expr_id, HirExpr::Var(new_var));
            return;
        }
    }

    // Recurse into children
    match exprs.get(expr_id).clone() {
        HirExpr::FieldAccess { table, .. } => {
            rewrite_var_refs(table, replacements, exprs, visited);
        }
        HirExpr::IndexAccess { table, key } => {
            rewrite_var_refs(table, replacements, exprs, visited);
            rewrite_var_refs(key, replacements, exprs, visited);
        }
        HirExpr::Binary { left, right, .. } => {
            rewrite_var_refs(left, replacements, exprs, visited);
            rewrite_var_refs(right, replacements, exprs, visited);
        }
        HirExpr::Unary { operand, .. } => {
            rewrite_var_refs(operand, replacements, exprs, visited);
        }
        HirExpr::Call { func: f, args, .. } => {
            rewrite_var_refs(f, replacements, exprs, visited);
            for a in &args {
                rewrite_var_refs(*a, replacements, exprs, visited);
            }
        }
        HirExpr::MethodCall { object, args, .. } => {
            rewrite_var_refs(object, replacements, exprs, visited);
            for a in &args {
                rewrite_var_refs(*a, replacements, exprs, visited);
            }
        }
        HirExpr::Table { array, hash, .. } => {
            for a in &array {
                rewrite_var_refs(*a, replacements, exprs, visited);
            }
            for (k, v) in &hash {
                rewrite_var_refs(*k, replacements, exprs, visited);
                rewrite_var_refs(*v, replacements, exprs, visited);
            }
        }
        HirExpr::Concat(operands) => {
            for o in &operands {
                rewrite_var_refs(*o, replacements, exprs, visited);
            }
        }
        HirExpr::IfExpr {
            condition,
            then_expr,
            else_expr,
        } => {
            rewrite_var_refs(condition, replacements, exprs, visited);
            rewrite_var_refs(then_expr, replacements, exprs, visited);
            rewrite_var_refs(else_expr, replacements, exprs, visited);
        }
        HirExpr::Select { source, .. } => {
            rewrite_var_refs(source, replacements, exprs, visited);
        }
        _ => {}
    }
}

/// Collect ExprIds that represent USES (reads) in a statement.
/// Does NOT include the value being defined (for Assign/LocalDecl, only the RHS uses).
fn collect_stmt_use_expr_ids(stmt: &HirStmt, out: &mut Vec<ExprId>) {
    match stmt {
        HirStmt::Assign { target, value } => {
            // The target LValue may have sub-expressions (Field table, Index key)
            match target {
                LValue::Field { table, .. } => out.push(*table),
                LValue::Index { table, key } => {
                    out.push(*table);
                    out.push(*key);
                }
                _ => {}
            }
            out.push(*value);
        }
        HirStmt::LocalDecl { init, .. } => {
            if let Some(init) = init {
                out.push(*init);
            }
        }
        HirStmt::MultiLocalDecl { values, .. } => {
            out.extend(values.iter().copied());
        }
        HirStmt::MultiAssign { targets, values } => {
            for t in targets {
                match t {
                    LValue::Field { table, .. } => out.push(*table),
                    LValue::Index { table, key } => {
                        out.push(*table);
                        out.push(*key);
                    }
                    _ => {}
                }
            }
            out.extend(values.iter().copied());
        }
        HirStmt::CompoundAssign { target, value, .. } => {
            match target {
                LValue::Field { table, .. } => out.push(*table),
                LValue::Index { table, key } => {
                    out.push(*table);
                    out.push(*key);
                }
                _ => {}
            }
            out.push(*value);
        }
        HirStmt::ExprStmt(e) => out.push(*e),
        HirStmt::Return(values) => out.extend(values.iter().copied()),
        HirStmt::FunctionDef { name, func_expr } => {
            match name {
                LValue::Field { table, .. } => out.push(*table),
                LValue::Index { table, key } => {
                    out.push(*table);
                    out.push(*key);
                }
                _ => {}
            }
            out.push(*func_expr);
        }
        HirStmt::LocalFunctionDef { func_expr, .. } => out.push(*func_expr),
        HirStmt::RegAssign { value, .. } => out.push(*value),
        // Structured bodies: only collect condition/iterator expressions,
        // not body statements (those are handled by recursion in split_stmts).
        HirStmt::If { condition, .. } => out.push(*condition),
        HirStmt::While { condition, .. } => out.push(*condition),
        HirStmt::Repeat { condition, .. } => out.push(*condition),
        HirStmt::NumericFor {
            start, limit, step, ..
        } => {
            out.push(*start);
            out.push(*limit);
            if let Some(s) = step {
                out.push(*s);
            }
        }
        HirStmt::GenericFor { iterators, .. } => {
            out.extend(iterators.iter().copied());
        }
        HirStmt::Break | HirStmt::Continue | HirStmt::CloseUpvals { .. } => {}
    }
}

/// Recurse into nested bodies of structured statements.
fn recurse_into_bodies(stmt: HirStmt, func: &mut HirFunc) -> HirStmt {
    match stmt {
        HirStmt::If {
            condition,
            then_body,
            elseif_clauses,
            else_body,
            negated,
        } => {
            let then_body = split_stmts(then_body, func);
            let elseif_clauses = elseif_clauses
                .into_iter()
                .map(|c| lantern_hir::stmt::ElseIfClause {
                    condition: c.condition,
                    body: split_stmts(c.body, func),
                })
                .collect();
            let else_body = else_body.map(|b| split_stmts(b, func));
            HirStmt::If {
                condition,
                then_body,
                elseif_clauses,
                else_body,
                negated,
            }
        }
        HirStmt::While { condition, body } => {
            let body = split_stmts(body, func);
            HirStmt::While { condition, body }
        }
        HirStmt::Repeat { condition, body } => {
            let body = split_stmts(body, func);
            HirStmt::Repeat { condition, body }
        }
        HirStmt::NumericFor {
            var,
            start,
            limit,
            step,
            body,
        } => {
            let body = split_stmts(body, func);
            HirStmt::NumericFor {
                var,
                start,
                limit,
                step,
                body,
            }
        }
        HirStmt::GenericFor {
            vars,
            iterators,
            body,
        } => {
            let body = split_stmts(body, func);
            HirStmt::GenericFor {
                vars,
                iterators,
                body,
            }
        }
        other => other,
    }
}
