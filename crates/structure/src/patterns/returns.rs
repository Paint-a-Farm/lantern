//! Return-value normalization patterns.
//!
//! Three passes that clean up compiler-generated temp variables around return
//! statements and multi-return calls:
//!
//! - **`inline_return_temps`** — `local v = expr; return v` -> `return expr`
//! - **`collapse_multi_return_temps`** — `local _v1, _v2 = call(); x = _v1; y = _v2`
//!   -> `x, y = call(...)`
//! - **`strip_redundant_returns`** — removes bare returns at the end of
//!   if-branches when a bare return immediately follows the if-statement.

use lantern_hir::expr::HirExpr;
use lantern_hir::func::HirFunc;
use lantern_hir::stmt::{HirStmt, LValue};

// ---------------------------------------------------------------------------
// Inline return temps
// ---------------------------------------------------------------------------

/// Inline `local v = expr; return v` -> `return expr`.
///
/// Handles three patterns:
///
/// 1. **Sequence**: `local a = e1; local b = e2; return a, b` -> `return e1, e2`
/// 2. **MultiAssign**: `local a, b = call(); return a, b` -> `return call()`
/// 3. **Single**: `local v = expr; return v` -> `return expr` (covered by case 1)
pub(super) fn inline_return_temps(func: &HirFunc, mut stmts: Vec<HirStmt>) -> Vec<HirStmt> {
    if stmts.len() < 2 {
        return stmts;
    }

    let last_idx = stmts.len() - 1;

    if let HirStmt::Return(ret_vals) = &stmts[last_idx] {
        if ret_vals.is_empty() {
            return stmts;
        }

        let n = ret_vals.len();

        // Case 1: sequence of N Assigns before the Return, one per return value
        if stmts.len() >= n + 1 {
            let start = last_idx - n;
            let mut all_match = true;
            let mut values = Vec::with_capacity(n);

            for i in 0..n {
                if let HirStmt::Assign {
                    target: LValue::Local(def_var),
                    value,
                } = &stmts[start + i]
                {
                    if let HirExpr::Var(ret_var) = func.exprs.get(ret_vals[i]) {
                        // Only inline unnamed temps — named variables like
                        // `instance` must keep the assignment to preserve
                        // the Move instruction in the roundtrip.
                        if ret_var == def_var
                            && func.vars.get(*def_var).name.is_none()
                        {
                            values.push(*value);
                            continue;
                        }
                    }
                }
                all_match = false;
                break;
            }

            if all_match {
                for _ in 0..n {
                    stmts.remove(start);
                }
                stmts[start] = HirStmt::Return(values);
                return stmts;
            }
        }

        // Case 2: MultiAssign pattern — `local a, b = call(); return a, b` -> `return call()`
        let prev_idx = last_idx - 1;
        if let HirStmt::MultiAssign { targets, values } = &stmts[prev_idx] {
            if targets.len() == n && values.len() == 1 {
                let all_match = targets.iter().zip(ret_vals.iter()).all(|(t, rv)| {
                    if let (LValue::Local(tv), HirExpr::Var(rv)) = (t, func.exprs.get(*rv)) {
                        tv == rv
                    } else {
                        false
                    }
                });
                if all_match {
                    let values = values.clone();
                    stmts.remove(prev_idx);
                    stmts[prev_idx] = HirStmt::Return(values);
                    return stmts;
                }
            }
        }
    }

    stmts
}

// ---------------------------------------------------------------------------
// Collapse multi-return temps
// ---------------------------------------------------------------------------

/// Collapse multi-return temps into direct assignment.
///
/// Pattern:
/// ```text
/// local _v1, _v2, _v3 = call(...)   -- MultiAssign with unnamed temps
/// x = _v1                           -- assignments may be in any order
/// z = _v3                           -- and target any LValue (field, global, etc.)
/// y = _v2
/// ```
///
/// Transforms into:
/// ```text
/// x, y, z = call(...)
/// ```
///
/// Only applies when ALL temp variables are unnamed and each is used exactly
/// once in the immediately following assign statements.  The assignments may
/// appear in any order — we map each temp back to its position.
pub(super) fn collapse_multi_return_temps(func: &HirFunc, mut stmts: Vec<HirStmt>) -> Vec<HirStmt> {
    let mut i = 0;
    while i < stmts.len() {
        if let HirStmt::MultiAssign { targets, values } = &stmts[i] {
            let n = targets.len();

            // All targets must be unnamed temp variables — collect their VarIds
            let temp_vars: Vec<_> = targets
                .iter()
                .filter_map(|t| {
                    if let LValue::Local(var_id) = t {
                        if func.vars.get(*var_id).name.is_none() {
                            return Some(*var_id);
                        }
                    }
                    None
                })
                .collect();

            if temp_vars.len() == n && i + n < stmts.len() {
                // Next N statements must each be `Assign { target: X, value: Var(temp) }`
                // where temp is one of the MultiAssign temps.  Order may differ.
                let mut real_targets: Vec<Option<LValue>> = vec![None; n];
                let mut all_match = true;

                for j in 0..n {
                    if let HirStmt::Assign {
                        target: real_target,
                        value,
                    } = &stmts[i + 1 + j]
                    {
                        if let HirExpr::Var(used_var) = func.exprs.get(*value) {
                            if let Some(pos) = temp_vars.iter().position(|v| v == used_var) {
                                if real_targets[pos].is_none() {
                                    real_targets[pos] = Some(real_target.clone());
                                    continue;
                                }
                            }
                        }
                    }
                    all_match = false;
                    break;
                }

                if all_match && real_targets.iter().all(|t| t.is_some()) {
                    let values = values.clone();
                    let targets: Vec<LValue> =
                        real_targets.into_iter().map(|t| t.unwrap()).collect();
                    for _ in 0..n {
                        stmts.remove(i + 1);
                    }
                    stmts[i] = HirStmt::MultiAssign { targets, values };
                    i += 1;
                    continue;
                }
            }
        }
        i += 1;
    }
    stmts
}

// ---------------------------------------------------------------------------
// Strip redundant returns
// ---------------------------------------------------------------------------

/// Remove bare `return` statements that are redundant because a bare return
/// follows immediately after, or because the function ends implicitly.
///
/// **Pattern 1** — bare return before sibling return:
/// ```text
/// if cond then           if cond then
///     stuff()                stuff()
///     return      -->    end
/// end                    return
/// return
/// ```
///
/// **Pattern 2** — sole bare return in else at end of statement list:
/// ```text
/// if cond then           if cond then
///     stuff()      -->       stuff()
/// else                   end
///     return
/// end
/// ```
pub(super) fn strip_redundant_returns(stmts: &mut Vec<HirStmt>) {
    // Pattern 2: when the last statement is an if whose else body is just
    // a bare return (sole statement), drop the else body.
    if let Some(HirStmt::If {
        else_body,
        then_body,
        elseif_clauses,
        ..
    }) = stmts.last_mut()
    {
        if let Some(else_stmts) = else_body {
            if else_stmts.len() == 1
                && matches!(&else_stmts[0], HirStmt::Return(v) if v.is_empty())
                && !branch_has_value_return(then_body)
                && !elseif_clauses.iter().any(|c| branch_has_value_return(&c.body))
            {
                *else_body = None;
            }
        }
    }

    // Pattern 1: strip bare returns from if-branches before a sibling return.
    let len = stmts.len();
    if len < 2 {
        return;
    }

    // Check if the last statement is a bare return — if so, strip bare returns
    // from the ends of if-branches in the preceding statement.
    if matches!(stmts.last(), Some(HirStmt::Return(v)) if v.is_empty()) {
        if let Some(HirStmt::If {
            then_body,
            elseif_clauses,
            else_body,
            ..
        }) = stmts.get_mut(len - 2)
        {
            strip_trailing_bare_return(then_body);
            for clause in elseif_clauses.iter_mut() {
                strip_trailing_bare_return(&mut clause.body);
            }
            if let Some(else_body) = else_body {
                strip_trailing_bare_return(else_body);
            }
        }
    }
}

/// Strip a trailing bare `return` from a branch body.
/// Also recurses into nested if-statements at the end of the body.
fn strip_trailing_bare_return(stmts: &mut Vec<HirStmt>) {
    if matches!(stmts.last(), Some(HirStmt::Return(v)) if v.is_empty()) {
        stmts.pop();
        return;
    }
    // Recurse into nested if at end of body
    if let Some(HirStmt::If {
        then_body,
        elseif_clauses,
        else_body,
        ..
    }) = stmts.last_mut()
    {
        strip_trailing_bare_return(then_body);
        for clause in elseif_clauses.iter_mut() {
            strip_trailing_bare_return(&mut clause.body);
        }
        if let Some(else_body) = else_body {
            strip_trailing_bare_return(else_body);
        }
    }
}

/// Check if a branch body ends with `return <values>` (non-empty return).
fn branch_has_value_return(stmts: &[HirStmt]) -> bool {
    match stmts.last() {
        Some(HirStmt::Return(v)) => !v.is_empty(),
        Some(HirStmt::If {
            then_body,
            elseif_clauses,
            else_body,
            ..
        }) => {
            branch_has_value_return(then_body)
                || elseif_clauses.iter().any(|c| branch_has_value_return(&c.body))
                || else_body.as_ref().is_some_and(|b| branch_has_value_return(b))
        }
        _ => false,
    }
}

