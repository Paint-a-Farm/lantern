//! Phi-node early return transformation.
//!
//! Converts phi-node patterns produced by the vars solver (Phase 4c) into
//! early-return form:
//!
//! ```text
//! local _v = default        if not cond then
//! if cond then          -->     return default
//!     _v = branch_val       end
//! end                       return branch_val
//! return _v
//! ```

use lantern_hir::arena::ExprId;
use lantern_hir::expr::{CaptureSource, HirExpr};
use lantern_hir::func::HirFunc;
use lantern_hir::stmt::{HirStmt, LValue};
use lantern_hir::var::VarId;

use super::conditions::negate_condition;

/// Transform phi-node patterns into early returns.
///
/// Scans for 3-stmt (`LocalDecl{init}; If{assign}; Return`) or 4-stmt
/// (`LocalDecl{no init}; Assign; If{assign}; Return`) windows that assign
/// a temporary variable in two branches and return it, and rewrites them
/// into guard-style early returns.
pub(super) fn fold_phinode_returns(func: &mut HirFunc, stmts: Vec<HirStmt>) -> Vec<HirStmt> {
    if stmts.len() < 3 {
        return stmts;
    }

    let mut result = Vec::with_capacity(stmts.len());
    let mut i = 0;

    while i < stmts.len() {
        // Try 4-statement variant first (more specific)
        if i + 4 <= stmts.len() {
            if let Some((guard, tail_ret)) = try_match_4stmt(func, &stmts, i) {
                result.push(guard);
                result.push(tail_ret);
                i += 4;
                continue;
            }
        }

        // Try 3-statement variant
        if i + 3 <= stmts.len() {
            if let Some((guard, tail_ret)) = try_match_3stmt(func, &stmts, i) {
                result.push(guard);
                result.push(tail_ret);
                i += 3;
                continue;
            }
        }

        result.push(stmts[i].clone());
        i += 1;
    }

    result
}

/// 3-stmt: `LocalDecl { var: V, init: Some(default) }; If { assign V }; Return(V)`
fn try_match_3stmt(
    func: &mut HirFunc,
    stmts: &[HirStmt],
    i: usize,
) -> Option<(HirStmt, HirStmt)> {
    let (var_id, default_expr) = match &stmts[i] {
        HirStmt::LocalDecl {
            var,
            init: Some(val),
        } => (*var, *val),
        _ => return None,
    };

    if !func.vars.get(var_id).is_temporary() {
        return None;
    }

    let (condition, branch_expr) = match_if_assign(var_id, &stmts[i + 1])?;
    match_return_var(func, var_id, &stmts[i + 2])?;

    if var_used_outside_window(func, stmts, i, 3, var_id) {
        return None;
    }

    let neg_cond = negate_condition(func, condition);
    Some(build_early_return(neg_cond, default_expr, branch_expr))
}

/// 4-stmt: `LocalDecl { var: V, init: None }; Assign(V, default); If { assign V }; Return(V)`
fn try_match_4stmt(
    func: &mut HirFunc,
    stmts: &[HirStmt],
    i: usize,
) -> Option<(HirStmt, HirStmt)> {
    let var_id = match &stmts[i] {
        HirStmt::LocalDecl { var, init: None } => *var,
        _ => return None,
    };

    if !func.vars.get(var_id).is_temporary() {
        return None;
    }

    let default_expr = match &stmts[i + 1] {
        HirStmt::Assign {
            target: LValue::Local(v),
            value,
        } if *v == var_id => *value,
        _ => return None,
    };

    let (condition, branch_expr) = match_if_assign(var_id, &stmts[i + 2])?;
    match_return_var(func, var_id, &stmts[i + 3])?;

    if var_used_outside_window(func, stmts, i, 4, var_id) {
        return None;
    }

    let neg_cond = negate_condition(func, condition);
    Some(build_early_return(neg_cond, default_expr, branch_expr))
}

fn build_early_return(
    neg_condition: ExprId,
    default_expr: ExprId,
    branch_expr: ExprId,
) -> (HirStmt, HirStmt) {
    let guard = HirStmt::If {
        condition: neg_condition,
        negated: true,
        then_body: vec![HirStmt::Return(vec![default_expr])],
        elseif_clauses: Vec::new(),
        else_body: None,
    };
    let tail = HirStmt::Return(vec![branch_expr]);
    (guard, tail)
}

/// Match `If { condition, then_body: [Assign(Local(V), val)], no elseif/else }`
fn match_if_assign(var_id: VarId, stmt: &HirStmt) -> Option<(ExprId, ExprId)> {
    if let HirStmt::If {
        condition,
        then_body,
        elseif_clauses,
        else_body,
        ..
    } = stmt
    {
        if !elseif_clauses.is_empty() || else_body.is_some() {
            return None;
        }
        if then_body.len() != 1 {
            return None;
        }
        if let HirStmt::Assign {
            target: LValue::Local(v),
            value,
        } = &then_body[0]
        {
            if *v == var_id {
                return Some((*condition, *value));
            }
        }
    }
    None
}

/// Match `Return([expr])` where expr is `Var(V)`.
fn match_return_var(func: &HirFunc, var_id: VarId, stmt: &HirStmt) -> Option<()> {
    if let HirStmt::Return(vals) = stmt {
        if vals.len() == 1 {
            if let HirExpr::Var(v) = func.exprs.get(vals[0]) {
                if *v == var_id {
                    return Some(());
                }
            }
        }
    }
    None
}

/// Check if `var_id` is referenced anywhere in `stmts` outside `[start..start+len)`.
fn var_used_outside_window(
    func: &HirFunc,
    stmts: &[HirStmt],
    start: usize,
    len: usize,
    var_id: VarId,
) -> bool {
    for (idx, stmt) in stmts.iter().enumerate() {
        if idx >= start && idx < start + len {
            continue;
        }
        if stmt_refs_var(func, stmt, var_id) {
            return true;
        }
    }
    false
}

// --- Recursive variable reference checking ---

fn stmt_refs_var(func: &HirFunc, stmt: &HirStmt, target: VarId) -> bool {
    match stmt {
        HirStmt::LocalDecl { var, init } => {
            *var == target || init.map_or(false, |e| expr_refs_var(func, e, target))
        }
        HirStmt::MultiLocalDecl { vars, values } => {
            vars.contains(&target)
                || values.iter().any(|e| expr_refs_var(func, *e, target))
        }
        HirStmt::Assign { target: lval, value } => {
            lval_refs_var(func, lval, target) || expr_refs_var(func, *value, target)
        }
        HirStmt::MultiAssign { targets, values } => {
            targets.iter().any(|l| lval_refs_var(func, l, target))
                || values.iter().any(|e| expr_refs_var(func, *e, target))
        }
        HirStmt::CompoundAssign {
            target: lval,
            value,
            ..
        } => lval_refs_var(func, lval, target) || expr_refs_var(func, *value, target),
        HirStmt::ExprStmt(e) => expr_refs_var(func, *e, target),
        HirStmt::Return(vals) => vals.iter().any(|e| expr_refs_var(func, *e, target)),
        HirStmt::If {
            condition,
            then_body,
            elseif_clauses,
            else_body,
            ..
        } => {
            expr_refs_var(func, *condition, target)
                || then_body.iter().any(|s| stmt_refs_var(func, s, target))
                || elseif_clauses.iter().any(|c| {
                    expr_refs_var(func, c.condition, target)
                        || c.body.iter().any(|s| stmt_refs_var(func, s, target))
                })
                || else_body
                    .as_ref()
                    .map_or(false, |b| b.iter().any(|s| stmt_refs_var(func, s, target)))
        }
        HirStmt::While { condition, body } | HirStmt::Repeat { body, condition } => {
            expr_refs_var(func, *condition, target)
                || body.iter().any(|s| stmt_refs_var(func, s, target))
        }
        HirStmt::NumericFor {
            var,
            start,
            limit,
            step,
            body,
        } => {
            *var == target
                || expr_refs_var(func, *start, target)
                || expr_refs_var(func, *limit, target)
                || step.map_or(false, |e| expr_refs_var(func, e, target))
                || body.iter().any(|s| stmt_refs_var(func, s, target))
        }
        HirStmt::GenericFor {
            vars,
            iterators,
            body,
        } => {
            vars.contains(&target)
                || iterators.iter().any(|e| expr_refs_var(func, *e, target))
                || body.iter().any(|s| stmt_refs_var(func, s, target))
        }
        HirStmt::FunctionDef { name, func_expr } => {
            lval_refs_var(func, name, target) || expr_refs_var(func, *func_expr, target)
        }
        HirStmt::LocalFunctionDef { var, func_expr } => {
            *var == target || expr_refs_var(func, *func_expr, target)
        }
        HirStmt::Break | HirStmt::Continue | HirStmt::CloseUpvals { .. } | HirStmt::RegAssign { .. } => false,
    }
}

fn lval_refs_var(func: &HirFunc, lval: &LValue, target: VarId) -> bool {
    match lval {
        LValue::Local(v) => *v == target,
        LValue::Field { table, .. } => expr_refs_var(func, *table, target),
        LValue::Index { table, key } => {
            expr_refs_var(func, *table, target) || expr_refs_var(func, *key, target)
        }
        LValue::Global(_) | LValue::Upvalue(_) => false,
    }
}

fn expr_refs_var(func: &HirFunc, expr_id: ExprId, target: VarId) -> bool {
    match func.exprs.get(expr_id) {
        HirExpr::Var(v) => *v == target,
        HirExpr::Binary { left, right, .. } => {
            expr_refs_var(func, *left, target) || expr_refs_var(func, *right, target)
        }
        HirExpr::Unary { operand, .. } => expr_refs_var(func, *operand, target),
        HirExpr::Call { func: f, args, .. } => {
            expr_refs_var(func, *f, target)
                || args.iter().any(|a| expr_refs_var(func, *a, target))
        }
        HirExpr::MethodCall { object, args, .. } => {
            expr_refs_var(func, *object, target)
                || args.iter().any(|a| expr_refs_var(func, *a, target))
        }
        HirExpr::FieldAccess { table, .. } => expr_refs_var(func, *table, target),
        HirExpr::IndexAccess { table, key } => {
            expr_refs_var(func, *table, target) || expr_refs_var(func, *key, target)
        }
        HirExpr::Table { array, hash, .. } => {
            array.iter().any(|e| expr_refs_var(func, *e, target))
                || hash
                    .iter()
                    .any(|(k, v)| expr_refs_var(func, *k, target) || expr_refs_var(func, *v, target))
        }
        HirExpr::Concat(parts) => parts.iter().any(|e| expr_refs_var(func, *e, target)),
        HirExpr::IfExpr {
            condition,
            then_expr,
            else_expr,
        } => {
            expr_refs_var(func, *condition, target)
                || expr_refs_var(func, *then_expr, target)
                || expr_refs_var(func, *else_expr, target)
        }
        HirExpr::Select { source, .. } => expr_refs_var(func, *source, target),
        HirExpr::Closure { captures, .. } => captures.iter().any(|c| match &c.source {
            CaptureSource::Var(v) => *v == target,
            _ => false,
        }),
        HirExpr::Literal(_)
        | HirExpr::Global(_)
        | HirExpr::Upvalue(_)
        | HirExpr::VarArg
        | HirExpr::Reg(_) => false,
    }
}
