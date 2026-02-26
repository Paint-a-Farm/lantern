//! Return-value normalization patterns.
//!
//! Two passes that clean up compiler-generated temp variables around return
//! statements and multi-return calls:
//!
//! - **`inline_return_temps`** — `local v = expr; return v` -> `return expr`
//! - **`collapse_multi_return_temps`** — `local _v1, _v2 = call(); x = _v1; y = _v2`
//!   -> `x, y = call(...)`

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
/// x = _v1                           -- (or local x = _v1)
/// y = _v2
/// z = _v3
/// ```
///
/// Transforms into:
/// ```text
/// x, y, z = call(...)
/// ```
///
/// Only applies when ALL temp variables are unnamed and each is used exactly
/// once in the immediately following assign statements.
pub(super) fn collapse_multi_return_temps(func: &HirFunc, mut stmts: Vec<HirStmt>) -> Vec<HirStmt> {
    let mut i = 0;
    while i < stmts.len() {
        if let HirStmt::MultiAssign { targets, values } = &stmts[i] {
            let n = targets.len();

            // All targets must be unnamed temp variables
            let all_unnamed = targets.iter().all(|t| {
                if let LValue::Local(var_id) = t {
                    func.vars.get(*var_id).name.is_none()
                } else {
                    false
                }
            });

            if all_unnamed && i + n < stmts.len() {
                // Next N statements must be `Assign { target: real_var, value: Var(temp) }`
                // where each temp matches the corresponding MultiAssign target
                let mut real_targets = Vec::with_capacity(n);
                let mut all_match = true;

                for j in 0..n {
                    if let HirStmt::Assign {
                        target: real_target,
                        value,
                    } = &stmts[i + 1 + j]
                    {
                        if let LValue::Local(temp_var) = &targets[j] {
                            if let HirExpr::Var(used_var) = func.exprs.get(*value) {
                                if used_var == temp_var {
                                    real_targets.push(real_target.clone());
                                    continue;
                                }
                            }
                        }
                    }
                    all_match = false;
                    break;
                }

                if all_match {
                    let values = values.clone();
                    for _ in 0..n {
                        stmts.remove(i + 1);
                    }
                    stmts[i] = HirStmt::MultiAssign {
                        targets: real_targets,
                        values,
                    };
                    i += 1;
                    continue;
                }
            }
        }
        i += 1;
    }
    stmts
}
