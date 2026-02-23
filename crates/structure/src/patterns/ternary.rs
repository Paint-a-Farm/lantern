//! Post-structuring ternary fold-back pass.
//!
//! Recognizes `if cond then x = a else x = b end` and
//! `local x = b; if cond then x = a end` patterns, folding them back
//! into `x = cond and a or b` ternary expressions.
//!
//! Supplements the pre-lifting ternary detectors by catching patterns
//! they miss (e.g. when the Luau compiler didn't use and/or bytecode).

use lantern_hir::arena::ExprId;
use lantern_hir::expr::HirExpr;
use lantern_hir::func::HirFunc;
use lantern_hir::stmt::{HirStmt, LValue};
use lantern_hir::types::BinOp;
use lantern_hir::var::VarId;


/// Fold ternary patterns in a statement list.
///
/// Detects two patterns:
///
/// **Pattern 1**: `x = b; if cond then x = a end`
///   → `x = cond and a or b`
///
/// **Pattern 2**: `if cond then x = a else x = b end`
///   → `x = cond and a or b`
///
/// Only folds when the true-value is guaranteed truthy (not `nil` or `false`)
/// to preserve Lua `and`/`or` semantics.
pub fn fold_ternary_patterns(func: &mut HirFunc, stmts: Vec<HirStmt>) -> Vec<HirStmt> {
    let mut result = Vec::with_capacity(stmts.len());
    let mut i = 0;

    while i < stmts.len() {
        // Pattern 1: assignment + if-then (no else)
        if i + 1 < stmts.len() {
            if let Some(folded) = try_fold_assign_then_if(func, &stmts[i], &stmts[i + 1]) {
                result.push(folded);
                i += 2;
                continue;
            }
        }

        // Pattern 2: if-then-else with single assignment in each branch
        if let Some(folded) = try_fold_if_else(func, &stmts[i]) {
            result.push(folded);
            i += 1;
            continue;
        }

        result.push(stmts[i].clone());
        i += 1;
    }

    result
}

/// Pattern 1: `x = false_val; if cond then x = true_val end`
/// Also handles: `local x = false_val; if cond then x = true_val end`
fn try_fold_assign_then_if(
    func: &mut HirFunc,
    first: &HirStmt,
    second: &HirStmt,
) -> Option<HirStmt> {
    // Extract var_id and false_val from the first statement
    let (var_id, false_val, is_local_decl) = match first {
        HirStmt::Assign {
            target: LValue::Local(vid),
            value,
        } => (*vid, *value, false),
        HirStmt::LocalDecl {
            var,
            init: Some(value),
        } => (*var, *value, true),
        _ => return None,
    };

    // Extract condition and true_val from the if-then
    let (condition, true_val) = match second {
        HirStmt::If {
            condition,
            then_body,
            elseif_clauses,
            else_body,
        } => {
            // Must be a simple if-then (no elseif, no else)
            if !elseif_clauses.is_empty() || else_body.is_some() {
                return None;
            }
            // Then body must be a single assignment to the same variable
            if then_body.len() != 1 {
                return None;
            }
            match &then_body[0] {
                HirStmt::Assign {
                    target: LValue::Local(vid),
                    value,
                } if *vid == var_id => (*condition, *value),
                _ => return None,
            }
        }
        _ => return None,
    };

    // Safety check: true_val must be truthy (not nil or false literal)
    // to preserve `cond and a or b` semantics
    if !is_truthy_expr(&func.exprs, true_val) {
        return None;
    }

    // Safety check: condition and true_val must not reference the target variable
    // (self-referential patterns like `x = cond(x) and a or b` or `x = cond and f(x) or b` are wrong)
    if expr_contains_var(&func.exprs, condition, var_id)
        || expr_contains_var(&func.exprs, true_val, var_id)
    {
        return None;
    }

    // Build: cond and true_val or false_val
    let and_expr = func.exprs.alloc(HirExpr::Binary {
        op: BinOp::And,
        left: condition,
        right: true_val,
    });
    let or_expr = func.exprs.alloc(HirExpr::Binary {
        op: BinOp::Or,
        left: and_expr,
        right: false_val,
    });

    if is_local_decl {
        Some(HirStmt::LocalDecl {
            var: var_id,
            init: Some(or_expr),
        })
    } else {
        Some(HirStmt::Assign {
            target: LValue::Local(var_id),
            value: or_expr,
        })
    }
}

/// Pattern 2: `if cond then x = a else x = b end`
fn try_fold_if_else(func: &mut HirFunc, stmt: &HirStmt) -> Option<HirStmt> {
    let (condition, then_body, else_body) = match stmt {
        HirStmt::If {
            condition,
            then_body,
            elseif_clauses,
            else_body: Some(else_body),
        } => {
            if !elseif_clauses.is_empty() {
                return None;
            }
            (*condition, then_body, else_body)
        }
        _ => return None,
    };

    // Both branches must be a single assignment to the same local
    if then_body.len() != 1 || else_body.len() != 1 {
        return None;
    }

    let (var_id, true_val) = match &then_body[0] {
        HirStmt::Assign {
            target: LValue::Local(vid),
            value,
        } => (*vid, *value),
        _ => return None,
    };

    let false_val = match &else_body[0] {
        HirStmt::Assign {
            target: LValue::Local(vid),
            value,
        } if *vid == var_id => *value,
        _ => return None,
    };

    // Safety check: true_val must be truthy
    if !is_truthy_expr(&func.exprs, true_val) {
        return None;
    }

    // Safety check: condition and branches must not reference the target variable
    if expr_contains_var(&func.exprs, condition, var_id)
        || expr_contains_var(&func.exprs, true_val, var_id)
        || expr_contains_var(&func.exprs, false_val, var_id)
    {
        return None;
    }

    // Build: cond and true_val or false_val
    let and_expr = func.exprs.alloc(HirExpr::Binary {
        op: BinOp::And,
        left: condition,
        right: true_val,
    });
    let or_expr = func.exprs.alloc(HirExpr::Binary {
        op: BinOp::Or,
        left: and_expr,
        right: false_val,
    });

    Some(HirStmt::Assign {
        target: LValue::Local(var_id),
        value: or_expr,
    })
}

/// Check if an expression is guaranteed truthy (not nil or false).
///
/// Conservative: returns true only when we can prove the value is
/// never nil/false. Unknown expressions return false (don't fold).
fn is_truthy_expr(exprs: &lantern_hir::arena::ExprArena, expr_id: ExprId) -> bool {
    match exprs.get(expr_id) {
        // Literals
        HirExpr::Literal(val) => {
            use lantern_hir::types::LuaValue;
            !matches!(val, LuaValue::Nil | LuaValue::Boolean(false))
        }
        // Numbers, strings, vectors are always truthy
        // Tables are always truthy
        HirExpr::Table { .. } => true,
        // Closures are always truthy
        HirExpr::Closure { .. } => true,
        // Arithmetic/string ops always produce numbers/strings (truthy)
        HirExpr::Binary { op, .. } => matches!(
            op,
            BinOp::Add
                | BinOp::Sub
                | BinOp::Mul
                | BinOp::Div
                | BinOp::FloorDiv
                | BinOp::Mod
                | BinOp::Pow
                | BinOp::Concat
        ),
        HirExpr::Unary { op, .. } => {
            use lantern_hir::types::UnOp;
            matches!(op, UnOp::Minus | UnOp::Len)
        }
        // `not x` returns a boolean, which could be false — NOT truthy
        // Variable reads, function calls, field accesses — unknown truthiness
        _ => false,
    }
}

/// Check if an expression tree contains a reference to a specific variable.
/// Used to reject self-referential ternaries like `x = cond and f(x) or default`.
fn expr_contains_var(exprs: &lantern_hir::arena::ExprArena, expr_id: ExprId, target: VarId) -> bool {
    match exprs.get(expr_id) {
        HirExpr::Var(v) => *v == target,
        HirExpr::Binary { left, right, .. } => {
            expr_contains_var(exprs, *left, target) || expr_contains_var(exprs, *right, target)
        }
        HirExpr::Unary { operand, .. } => expr_contains_var(exprs, *operand, target),
        HirExpr::FieldAccess { table, .. } => expr_contains_var(exprs, *table, target),
        HirExpr::IndexAccess { table, key } => {
            expr_contains_var(exprs, *table, target) || expr_contains_var(exprs, *key, target)
        }
        HirExpr::Call { func, args, .. } => {
            expr_contains_var(exprs, *func, target)
                || args.iter().any(|a| expr_contains_var(exprs, *a, target))
        }
        HirExpr::MethodCall { object, args, .. } => {
            expr_contains_var(exprs, *object, target)
                || args.iter().any(|a| expr_contains_var(exprs, *a, target))
        }
        HirExpr::IfExpr { condition, then_expr, else_expr } => {
            expr_contains_var(exprs, *condition, target)
                || expr_contains_var(exprs, *then_expr, target)
                || expr_contains_var(exprs, *else_expr, target)
        }
        HirExpr::Concat(parts) => parts.iter().any(|p| expr_contains_var(exprs, *p, target)),
        HirExpr::Select { source, .. } => expr_contains_var(exprs, *source, target),
        HirExpr::Table { array, hash } => {
            array.iter().any(|a| expr_contains_var(exprs, *a, target))
                || hash.iter().any(|(k, v)| {
                    expr_contains_var(exprs, *k, target) || expr_contains_var(exprs, *v, target)
                })
        }
        // Literals, globals, upvalues, varargs, closures, regs — no local var refs
        _ => false,
    }
}
