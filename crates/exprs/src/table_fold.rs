use lantern_hir::arena::ExprId;
use lantern_hir::expr::HirExpr;
use lantern_hir::func::HirFunc;
use lantern_hir::stmt::{HirStmt, LValue};
use lantern_hir::types::LuaValue;
use lantern_hir::var::VarId;

/// Fold consecutive table field assignments into the table constructor.
///
/// Recognizes the pattern:
///   local _v = {}          (or { existing entries })
///   _v[k1] = val1
///   _v[k2] = val2
///   ...
///   use(_v)                (single remaining use)
///
/// Transforms into a single table constructor with all entries folded in.
/// After folding, the variable is no longer used as a table target, so
/// `eliminate_temporaries` can inline it at the use site.
///
/// Also handles field assignments: `_v.field = val`.
pub fn fold_table_constructors(func: &mut HirFunc) {
    let nodes: Vec<_> = func.cfg.node_indices().collect();
    for node_idx in nodes {
        fold_in_stmts(&mut func.cfg[node_idx].stmts, &mut func.exprs);
    }
}

fn fold_in_stmts(stmts: &mut Vec<HirStmt>, exprs: &mut lantern_hir::arena::ExprArena) {
    // First recurse into nested bodies
    for stmt in stmts.iter_mut() {
        match stmt {
            HirStmt::If {
                then_body,
                elseif_clauses,
                else_body,
                ..
            } => {
                fold_in_stmts(then_body, exprs);
                for clause in elseif_clauses {
                    fold_in_stmts(&mut clause.body, exprs);
                }
                if let Some(body) = else_body {
                    fold_in_stmts(body, exprs);
                }
            }
            HirStmt::While { body, .. }
            | HirStmt::Repeat { body, .. }
            | HirStmt::NumericFor { body, .. }
            | HirStmt::GenericFor { body, .. } => {
                fold_in_stmts(body, exprs);
            }
            _ => {}
        }
    }

    // Now scan this level for table fold candidates
    let mut i = 0;
    while i < stmts.len() {
        if let Some((var_id, table_expr_id)) = get_table_def(&stmts[i], exprs) {
            // Count consecutive field/index assignments to this var
            let mut j = i + 1;
            let mut field_writes: Vec<TableWrite> = Vec::new();

            while j < stmts.len() {
                if let Some(tw) = get_table_write(&stmts[j], var_id, exprs) {
                    // Stop if the key or value references the table variable itself.
                    // Folding `t[k] = t[1]` into the constructor would change semantics
                    // because `t` doesn't exist yet during constructor evaluation.
                    if table_write_references_var(&tw, var_id, exprs) {
                        break;
                    }
                    field_writes.push(tw);
                    j += 1;
                } else {
                    break;
                }
            }

            if !field_writes.is_empty() {
                // Collect stale table-reference ExprIds from the about-to-be-removed
                // statements. After fold, these Var(v) expressions would still sit in
                // the arena and fool is_var_used_as_table_target into thinking the var
                // is still used as a table target, blocking inline.
                let stale_table_refs: Vec<ExprId> = stmts[i + 1..j]
                    .iter()
                    .filter_map(|s| match s {
                        HirStmt::Assign {
                            target: LValue::Index { table, .. },
                            ..
                        }
                        | HirStmt::Assign {
                            target: LValue::Field { table, .. },
                            ..
                        } => Some(*table),
                        _ => None,
                    })
                    .collect();

                // Fold the writes into the table expression
                apply_table_fold(exprs, table_expr_id, &field_writes);

                // Null out stale Var(v) references so they don't block inlining
                for stale_ref in stale_table_refs {
                    exprs.replace(stale_ref, HirExpr::Literal(LuaValue::Nil));
                }

                // Remove the folded statements (indices i+1..j)
                stmts.drain(i + 1..j);
            }
        }
        i += 1;
    }
}

/// An individual field/index write to fold into the table.
enum TableWrite {
    /// `t[key] = value` where key is a numeric literal
    NumericIndex { key: i64, value: ExprId },
    /// `t[key] = value` where key is a non-numeric expression
    ExprIndex { key: ExprId, value: ExprId },
    /// `t.field = value`
    Field { field: String, value: ExprId },
}

/// Check if a statement defines a table: `local v = {}` or `v = {}`
fn get_table_def(stmt: &HirStmt, exprs: &lantern_hir::arena::ExprArena) -> Option<(VarId, ExprId)> {
    let (var_id, value) = match stmt {
        HirStmt::Assign {
            target: LValue::Local(var_id),
            value,
        } => (*var_id, *value),
        HirStmt::LocalDecl {
            var,
            init: Some(value),
        } => (*var, *value),
        _ => return None,
    };
    // Only match if the value is actually a Table expression
    if matches!(exprs.get(value), HirExpr::Table { .. }) {
        Some((var_id, value))
    } else {
        None
    }
}

/// Check if a statement writes a field/index to the given variable.
fn get_table_write(
    stmt: &HirStmt,
    var_id: VarId,
    exprs: &lantern_hir::arena::ExprArena,
) -> Option<TableWrite> {
    if let HirStmt::Assign { target, value } = stmt {
        match target {
            LValue::Index { table, key } => {
                if matches!(exprs.get(*table), HirExpr::Var(v) if *v == var_id) {
                    // Check if key is a numeric literal
                    if let HirExpr::Literal(LuaValue::Number(n)) = exprs.get(*key) {
                        let n = *n;
                        if n.fract() == 0.0 && n >= 1.0 {
                            return Some(TableWrite::NumericIndex {
                                key: n as i64,
                                value: *value,
                            });
                        }
                    }
                    return Some(TableWrite::ExprIndex {
                        key: *key,
                        value: *value,
                    });
                }
            }
            LValue::Field { table, field } => {
                if matches!(exprs.get(*table), HirExpr::Var(v) if *v == var_id) {
                    return Some(TableWrite::Field {
                        field: field.clone(),
                        value: *value,
                    });
                }
            }
            _ => {}
        }
    }
    None
}

/// Fold the collected writes into the Table expression.
fn apply_table_fold(
    exprs: &mut lantern_hir::arena::ExprArena,
    table_expr_id: ExprId,
    writes: &[TableWrite],
) {
    // Only fold if the target expression is actually a Table
    let (mut array, mut hash) = match exprs.get(table_expr_id).clone() {
        HirExpr::Table { array, hash } => (array, hash),
        _ => return,
    };

    // Track the next expected array index (1-based, after existing array entries)
    let mut next_array_idx = (array.len() as i64) + 1;

    for write in writes {
        match write {
            TableWrite::NumericIndex { key, value } => {
                if *key == next_array_idx {
                    // Sequential: append to array portion
                    array.push(*value);
                    next_array_idx += 1;
                } else {
                    // Non-sequential: goes to hash with explicit key
                    let key_expr = exprs.alloc(HirExpr::Literal(LuaValue::Number(*key as f64)));
                    hash.push((key_expr, *value));
                }
            }
            TableWrite::ExprIndex { key, value } => {
                hash.push((*key, *value));
            }
            TableWrite::Field { field, value } => {
                let key_expr = exprs.alloc(HirExpr::Literal(LuaValue::String(
                    field.as_bytes().to_vec(),
                )));
                hash.push((key_expr, *value));
            }
        }
    }

    // Replace the table expression with the folded version
    exprs.replace(table_expr_id, HirExpr::Table { array, hash });
}

/// Check if a table write's key or value expressions reference the given variable.
fn table_write_references_var(
    tw: &TableWrite,
    var_id: VarId,
    exprs: &lantern_hir::arena::ExprArena,
) -> bool {
    match tw {
        TableWrite::NumericIndex { value, .. } => expr_references_var(exprs, *value, var_id),
        TableWrite::ExprIndex { key, value } => {
            expr_references_var(exprs, *key, var_id) || expr_references_var(exprs, *value, var_id)
        }
        TableWrite::Field { value, .. } => expr_references_var(exprs, *value, var_id),
    }
}

/// Check if an expression transitively references a given variable.
fn expr_references_var(
    exprs: &lantern_hir::arena::ExprArena,
    expr_id: ExprId,
    var_id: VarId,
) -> bool {
    match exprs.get(expr_id) {
        HirExpr::Var(v) => *v == var_id,
        HirExpr::FieldAccess { table, .. } => expr_references_var(exprs, *table, var_id),
        HirExpr::IndexAccess { table, key } => {
            expr_references_var(exprs, *table, var_id) || expr_references_var(exprs, *key, var_id)
        }
        HirExpr::Binary { left, right, .. } => {
            expr_references_var(exprs, *left, var_id) || expr_references_var(exprs, *right, var_id)
        }
        HirExpr::Unary { operand, .. } => expr_references_var(exprs, *operand, var_id),
        HirExpr::Call { func, args, .. } => {
            expr_references_var(exprs, *func, var_id)
                || args.iter().any(|a| expr_references_var(exprs, *a, var_id))
        }
        HirExpr::MethodCall { object, args, .. } => {
            expr_references_var(exprs, *object, var_id)
                || args.iter().any(|a| expr_references_var(exprs, *a, var_id))
        }
        HirExpr::Table { array, hash } => {
            array.iter().any(|a| expr_references_var(exprs, *a, var_id))
                || hash.iter().any(|(k, v)| {
                    expr_references_var(exprs, *k, var_id) || expr_references_var(exprs, *v, var_id)
                })
        }
        HirExpr::Concat(operands) => operands
            .iter()
            .any(|o| expr_references_var(exprs, *o, var_id)),
        HirExpr::IfExpr {
            condition,
            then_expr,
            else_expr,
        } => {
            expr_references_var(exprs, *condition, var_id)
                || expr_references_var(exprs, *then_expr, var_id)
                || expr_references_var(exprs, *else_expr, var_id)
        }
        HirExpr::Select { source, .. } => expr_references_var(exprs, *source, var_id),
        HirExpr::Closure { captures, .. } => captures.iter().any(|c| match &c.source {
            lantern_hir::expr::CaptureSource::Var(v) => *v == var_id,
            _ => false,
        }),
        _ => false,
    }
}
