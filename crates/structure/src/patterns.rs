//! Post-structuring pattern transformations.
//!
//! These passes walk the structured HirStmt tree and apply pattern-based
//! rewrites to improve output quality:
//!
//! - **Elseif normalization**: Converts inverted `if A then <chain> else <handler>`
//!   into proper `if not A then <handler> elseif ...` chains.
//! - **Compound conditions**: Merges `if A then if B then` into `if A and B then`.
//! - **Boolean value recovery**: Converts `r = true; if cond then else r = false end`
//!   into `r = cond`.

use lantern_hir::expr::HirExpr;
use lantern_hir::func::HirFunc;
use lantern_hir::stmt::{ElseIfClause, HirStmt, LValue};
use lantern_hir::types::BinOp;

/// Apply all post-structuring patterns to the function.
pub fn apply_patterns(func: &mut HirFunc) {
    let entry = func.entry;
    let stmts = std::mem::take(&mut func.cfg[entry].stmts);
    let stmts = transform_stmts(func, stmts);
    func.cfg[entry].stmts = stmts;
}

/// Recursively transform a statement list, applying all patterns.
fn transform_stmts(func: &mut HirFunc, stmts: Vec<HirStmt>) -> Vec<HirStmt> {
    let mut result = Vec::with_capacity(stmts.len());
    for stmt in stmts {
        let stmt = transform_stmt(func, stmt);
        result.push(stmt);
    }
    // Merge consecutive early-exit guards (if cond then continue/break end)
    result = merge_consecutive_guards(func, result);
    // Flip single early-exit guards into wrapping if-then blocks
    result = flip_guard_to_wrapper(func, result);
    // Inline `local v = expr; return v` → `return expr`
    result = inline_return_temps(func, result);
    // Collapse `local _v1, _v2 = call(); x = _v1; y = _v2` → `x, y = call()`
    result = collapse_multi_return_temps(func, result);
    result
}

/// Transform a single statement, recursing into nested bodies.
fn transform_stmt(func: &mut HirFunc, stmt: HirStmt) -> HirStmt {
    match stmt {
        HirStmt::If {
            condition,
            then_body,
            elseif_clauses,
            else_body,
        } => {
            // First, recurse into all bodies
            let then_body = transform_stmts(func, then_body);
            let elseif_clauses = elseif_clauses
                .into_iter()
                .map(|c| ElseIfClause {
                    condition: c.condition,
                    body: transform_stmts(func, c.body),
                })
                .collect();
            let else_body = else_body.map(|b| transform_stmts(func, b));

            let mut if_stmt = HirStmt::If {
                condition,
                then_body,
                elseif_clauses,
                else_body,
            };

            // Apply patterns (order matters — normalize first, then merge, then flip guards)
            if_stmt = normalize_inverted_elseif(func, if_stmt);
            if_stmt = merge_compound_conditions(func, if_stmt);
            if_stmt = flip_elseif_guard(func, if_stmt);

            if_stmt
        }
        HirStmt::While { condition, body } => HirStmt::While {
            condition,
            body: transform_stmts(func, body),
        },
        HirStmt::Repeat { body, condition } => HirStmt::Repeat {
            body: transform_stmts(func, body),
            condition,
        },
        HirStmt::NumericFor {
            var,
            start,
            limit,
            step,
            body,
        } => HirStmt::NumericFor {
            var,
            start,
            limit,
            step,
            body: transform_stmts(func, body),
        },
        HirStmt::GenericFor {
            vars,
            iterators,
            body,
        } => HirStmt::GenericFor {
            vars,
            iterators,
            body: transform_stmts(func, body),
        },
        other => other,
    }
}

/// Normalize inverted elseif chains.
///
/// The Luau compiler generates elseif chains as:
/// ```text
/// if A ~= X then
///     if A ~= Y then
///         <fallthrough>
///     else
///         <handler_Y>
///     end
/// else
///     <handler_X>
/// end
/// ```
///
/// This normalizes them to:
/// ```text
/// if A == X then
///     <handler_X>
/// elseif A == Y then
///     <handler_Y>
/// else
///     <fallthrough>
/// end
/// ```
///
/// Detection: `then_body` is a single If with no elseif_clauses and `else_body`
/// is non-empty. The then_body's inner If has the same inverted structure.
fn normalize_inverted_elseif(func: &mut HirFunc, stmt: HirStmt) -> HirStmt {
    normalize_inverted_elseif_inner(func, stmt, false)
}

fn normalize_inverted_elseif_inner(func: &mut HirFunc, stmt: HirStmt, in_chain: bool) -> HirStmt {
    let HirStmt::If {
        condition,
        then_body,
        elseif_clauses,
        else_body,
    } = stmt
    else {
        return stmt;
    };

    // Requires: no existing elseif clauses, and an else_body exists
    if !elseif_clauses.is_empty() || else_body.is_none() {
        return HirStmt::If {
            condition,
            then_body,
            elseif_clauses,
            else_body,
        };
    }

    // Check if then_body is a single If (chain continues)
    let is_chain = then_body.len() == 1 && matches!(&then_body[0], HirStmt::If { .. });
    let else_body = else_body.unwrap();

    if !is_chain {
        if in_chain {
            // Leaf of an inverted chain: invert condition, swap bodies
            let inv_condition = negate_condition(func, condition);
            return HirStmt::If {
                condition: inv_condition,
                then_body: else_body,
                elseif_clauses: Vec::new(),
                else_body: Some(then_body),
            };
        }
        // Not in a chain context — leave as-is
        return HirStmt::If {
            condition,
            then_body,
            elseif_clauses: Vec::new(),
            else_body: Some(else_body),
        };
    }

    // Invert the outer condition: the else_body becomes the then_body
    let inv_condition = negate_condition(func, condition);

    // The inner If becomes the elseif chain
    let inner_if = then_body.into_iter().next().unwrap();
    let HirStmt::If {
        condition: inner_cond,
        then_body: inner_then,
        elseif_clauses: inner_elseif,
        else_body: inner_else,
    } = inner_if
    else {
        unreachable!();
    };

    // Build the elseif chain from the inner If
    let mut clauses = Vec::new();

    // The inner If's condition + then becomes an elseif
    // But the inner If might itself be inverted — so we need to
    // recursively normalize it first.
    let normalized_inner = normalize_inverted_elseif_inner(
        func,
        HirStmt::If {
            condition: inner_cond,
            then_body: inner_then,
            elseif_clauses: inner_elseif,
            else_body: inner_else,
        },
        true, // we're inside a chain
    );

    // Now extract the chain from the normalized inner
    if let HirStmt::If {
        condition: norm_cond,
        then_body: norm_then,
        elseif_clauses: norm_elseif,
        else_body: norm_else,
    } = normalized_inner
    {
        clauses.push(ElseIfClause {
            condition: norm_cond,
            body: norm_then,
        });
        clauses.extend(norm_elseif);

        HirStmt::If {
            condition: inv_condition,
            then_body: else_body,
            elseif_clauses: clauses,
            else_body: norm_else,
        }
    } else {
        unreachable!();
    }
}

/// Merge compound conditions (and-chains).
///
/// Pattern: `if A then if B then <body> end end` -> `if A and B then <body> end`
///
/// Also handles: `if A then (empty) else <rest>` -> `if not A then <rest>`
/// followed by potential further merging.
fn merge_compound_conditions(func: &mut HirFunc, stmt: HirStmt) -> HirStmt {
    let HirStmt::If {
        condition,
        then_body,
        elseif_clauses,
        else_body,
    } = stmt
    else {
        return stmt;
    };

    // Pattern 1: if A then (empty) elseif B then ... end
    // -> if (not A) and B then ... end
    // This handles: if g_addTestCommands then elseif not getIsSet("cheats") then
    if then_body.is_empty() && !elseif_clauses.is_empty() && else_body.is_none() {
        // The outer condition is vacuous — the first elseif is the real condition
        // combined with `not outer_condition`
        let not_cond = negate_condition(func, condition);
        let first_clause = &elseif_clauses[0];
        let and_cond = func.exprs.alloc(HirExpr::Binary {
            op: BinOp::And,
            left: not_cond,
            right: first_clause.condition,
        });

        let new_then = elseif_clauses[0].body.clone();
        let new_elseif: Vec<ElseIfClause> = elseif_clauses[1..].to_vec();

        return merge_compound_conditions(
            func,
            HirStmt::If {
                condition: and_cond,
                then_body: new_then,
                elseif_clauses: new_elseif,
                else_body: None,
            },
        );
    }

    // Pattern 2: if A then <single if B (no else)> end (no else)
    // -> if A and B then <body> end
    let is_and_chain = then_body.len() == 1
        && elseif_clauses.is_empty()
        && else_body.is_none()
        && matches!(
            &then_body[0],
            HirStmt::If {
                elseif_clauses,
                else_body,
                ..
            } if elseif_clauses.is_empty() && else_body.is_none()
        );

    if is_and_chain {
        let mut then_body = then_body;
        let inner = then_body.remove(0);
        if let HirStmt::If {
            condition: inner_cond,
            then_body: inner_then,
            ..
        } = inner
        {
            let and_cond = func.exprs.alloc(HirExpr::Binary {
                op: BinOp::And,
                left: condition,
                right: inner_cond,
            });
            return merge_compound_conditions(
                func,
                HirStmt::If {
                    condition: and_cond,
                    then_body: inner_then,
                    elseif_clauses: Vec::new(),
                    else_body: None,
                },
            );
        }
        unreachable!();
    }

    HirStmt::If {
        condition,
        then_body,
        elseif_clauses,
        else_body,
    }
}

/// Flip the last elseif clause when it's a guard (short + ends with return/break)
/// and the else body has real code. This converts:
/// ```text
/// if A then ...
/// elseif B then return       -->   if A then ...
/// else <code> end                  elseif not B then <code> end
/// ```
fn flip_elseif_guard(func: &mut HirFunc, stmt: HirStmt) -> HirStmt {
    let HirStmt::If {
        condition,
        then_body,
        mut elseif_clauses,
        else_body,
    } = stmt
    else {
        return stmt;
    };

    let Some(ref else_body_stmts) = else_body else {
        return HirStmt::If { condition, then_body, elseif_clauses, else_body };
    };

    // Check if the last elseif (or the then-body if no elseifs) is a guard
    if let Some(last_clause) = elseif_clauses.last_mut() {
        if is_short_guard(&last_clause.body) && !ends_with_exit(else_body_stmts) {
            let guard_stmts = std::mem::replace(&mut last_clause.body, else_body.unwrap());
            last_clause.condition = negate_condition(func, last_clause.condition);
            // The guard stmts (e.g. just `return`) become trailing statements
            // after the if — but since we're inside an if statement, we need to
            // check if there are more elseif clauses that would make this invalid.
            // Actually, the guard was the LAST clause, so we can just drop the else
            // and the guard will be implicit at end of function.
            // But to be safe, if the guard has actual content beyond return, keep it.
            if guard_stmts.len() == 1 && matches!(guard_stmts[0], HirStmt::Return(ref v) if v.is_empty()) {
                // Just a bare return — drop it, the function will return implicitly
                return HirStmt::If { condition, then_body, elseif_clauses, else_body: None };
            }
            // Guard has content (e.g., `error(); return`) — keep as else
            return HirStmt::If { condition, then_body, elseif_clauses, else_body: Some(guard_stmts) };
        }
    } else if is_short_guard(&then_body) && !ends_with_exit(else_body_stmts) {
        // No elseif clauses — just then-body is a guard with else having real code.
        // This is already handled by the structurer, but handle it here too for safety.
        return HirStmt::If { condition, then_body, elseif_clauses, else_body };
    }

    HirStmt::If { condition, then_body, elseif_clauses, else_body }
}

/// Check if a statement list is a short guard clause (≤3 statements ending with return/break).
fn is_short_guard(stmts: &[HirStmt]) -> bool {
    if stmts.is_empty() || stmts.len() > 3 {
        return false;
    }
    matches!(stmts.last(), Some(HirStmt::Return { .. } | HirStmt::Break))
}

/// Check if a statement list ends with an exit (return or break).
fn ends_with_exit(stmts: &[HirStmt]) -> bool {
    matches!(stmts.last(), Some(HirStmt::Return { .. } | HirStmt::Break))
}

fn negate_condition(func: &mut HirFunc, condition: lantern_hir::arena::ExprId) -> lantern_hir::arena::ExprId {
    func.exprs.negate_condition(condition)
}

/// Negate a condition, applying De Morgan's law to `or` chains.
/// `c1 or c2 or c3` → `(not c1) and (not c2) and (not c3)`
/// For non-or expressions, falls back to simple negation.
fn negate_or_chain(func: &mut HirFunc, condition: lantern_hir::arena::ExprId) -> lantern_hir::arena::ExprId {
    // Flatten the or-chain
    let mut terms = Vec::new();
    flatten_or_chain(func, condition, &mut terms);

    if terms.len() <= 1 {
        return negate_condition(func, condition);
    }

    // Negate each term and combine with `and`
    let mut result = negate_condition(func, terms[0]);
    for &term in &terms[1..] {
        let neg = negate_condition(func, term);
        result = func.exprs.alloc(HirExpr::Binary {
            op: BinOp::And,
            left: result,
            right: neg,
        });
    }
    result
}

/// Flatten a left-associative `or` chain into individual terms.
fn flatten_or_chain(func: &HirFunc, expr: lantern_hir::arena::ExprId, out: &mut Vec<lantern_hir::arena::ExprId>) {
    if let HirExpr::Binary { op: BinOp::Or, left, right } = func.exprs.get(expr) {
        flatten_or_chain(func, *left, out);
        out.push(*right);
    } else {
        out.push(expr);
    }
}

/// Check if a statement is `if cond then continue end` or `if cond then break end`
/// with no elseif/else branches.
fn is_early_exit_guard(stmt: &HirStmt) -> Option<(&lantern_hir::arena::ExprId, bool)> {
    if let HirStmt::If {
        condition,
        then_body,
        elseif_clauses,
        else_body,
    } = stmt
    {
        if elseif_clauses.is_empty()
            && else_body.is_none()
            && then_body.len() == 1
        {
            let is_continue = matches!(&then_body[0], HirStmt::Continue);
            let is_break = matches!(&then_body[0], HirStmt::Break);
            if is_continue || is_break {
                return Some((condition, is_continue));
            }
        }
    }
    None
}

/// Merge consecutive early-exit guards with the same exit type.
///
/// ```text
/// if cond1 then continue end     -->   if cond1 or cond2 then continue end
/// if cond2 then continue end
/// ```
fn merge_consecutive_guards(func: &mut HirFunc, stmts: Vec<HirStmt>) -> Vec<HirStmt> {
    if stmts.len() < 2 {
        return stmts;
    }

    let mut result: Vec<HirStmt> = Vec::with_capacity(stmts.len());
    let mut i = 0;

    while i < stmts.len() {
        if let Some((&first_cond, first_is_continue)) = is_early_exit_guard(&stmts[i]) {
            // Collect consecutive guards with the same exit type
            let mut merged_cond = first_cond;
            let mut j = i + 1;
            while j < stmts.len() {
                if let Some((&next_cond, next_is_continue)) = is_early_exit_guard(&stmts[j]) {
                    if next_is_continue == first_is_continue {
                        merged_cond = func.exprs.alloc(HirExpr::Binary {
                            op: BinOp::Or,
                            left: merged_cond,
                            right: next_cond,
                        });
                        j += 1;
                        continue;
                    }
                }
                break;
            }

            if j > i + 1 {
                // We merged multiple guards
                let exit_stmt = if first_is_continue {
                    HirStmt::Continue
                } else {
                    HirStmt::Break
                };
                result.push(HirStmt::If {
                    condition: merged_cond,
                    then_body: vec![exit_stmt],
                    elseif_clauses: Vec::new(),
                    else_body: None,
                });
                i = j;
            } else {
                result.push(stmts[i].clone());
                i += 1;
            }
        } else {
            result.push(stmts[i].clone());
            i += 1;
        }
    }

    result
}

/// Flip a single early-exit guard at the start of a list into a wrapping if block.
///
/// ```text
/// if cond then continue end     -->   if not cond then
/// stmt1                                   stmt1
/// stmt2                                   stmt2
///                                     end
/// ```
///
/// Only applies when the guard is the first statement and there are
/// following statements to wrap.
fn flip_guard_to_wrapper(func: &mut HirFunc, stmts: Vec<HirStmt>) -> Vec<HirStmt> {
    if stmts.len() < 2 {
        return stmts;
    }

    // Only flip `continue` guards (break has different semantics — it exits the loop)
    if let Some((&cond, true)) = is_early_exit_guard(&stmts[0]) {
        // Apply De Morgan's law when negating an `or` chain:
        // not (c1 or c2 or c3) → (not c1) and (not c2) and (not c3)
        let inv_cond = negate_or_chain(func, cond);
        let rest: Vec<HirStmt> = stmts[1..].to_vec();

        vec![HirStmt::If {
            condition: inv_cond,
            then_body: rest,
            elseif_clauses: Vec::new(),
            else_body: None,
        }]
    } else {
        stmts
    }
}

/// Inline `local v = expr; return v` → `return expr`.
///
/// Handles three patterns:
/// 1. Single: `local v = expr; return v` → `return expr`
/// 2. MultiAssign: `local a, b = call(); return a, b` → `return call()`
/// 3. Sequence: `local a = e1; local b = e2; return a, b` → `return e1, e2`
fn inline_return_temps(func: &HirFunc, mut stmts: Vec<HirStmt>) -> Vec<HirStmt> {
    if stmts.len() < 2 {
        return stmts;
    }

    let last_idx = stmts.len() - 1;

    if let HirStmt::Return(ret_vals) = &stmts[last_idx] {
        if ret_vals.is_empty() {
            return stmts;
        }

        let n = ret_vals.len();

        // Check for sequence of N Assigns before the Return, one per return value
        if stmts.len() >= n + 1 {
            let start = last_idx - n;
            let mut all_match = true;
            let mut values = Vec::with_capacity(n);

            for i in 0..n {
                if let HirStmt::Assign { target: LValue::Local(def_var), value } = &stmts[start + i] {
                    if let HirExpr::Var(ret_var) = func.exprs.get(ret_vals[i]) {
                        if ret_var == def_var {
                            values.push(*value);
                            continue;
                        }
                    }
                }
                all_match = false;
                break;
            }

            if all_match {
                // Remove the N assign statements and rewrite the return
                for _ in 0..n {
                    stmts.remove(start);
                }
                stmts[start] = HirStmt::Return(values);
                return stmts;
            }
        }

        // MultiAssign pattern: `local a, b = call(); return a, b` → `return call()`
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
/// x, y, z = call(...)               -- (or local x, y, z = call(...))
/// ```
///
/// Only applies when ALL temp variables are unnamed and each is used exactly
/// once in the immediately following assign statements.
fn collapse_multi_return_temps(func: &HirFunc, mut stmts: Vec<HirStmt>) -> Vec<HirStmt> {
    let mut i = 0;
    while i < stmts.len() {
        if let HirStmt::MultiAssign { targets, values } = &stmts[i] {
            let n = targets.len();

            // Check: all targets are unnamed temp variables
            let all_unnamed = targets.iter().all(|t| {
                if let LValue::Local(var_id) = t {
                    func.vars.get(*var_id).name.is_none()
                } else {
                    false
                }
            });

            if all_unnamed && i + n < stmts.len() {
                // Check: next N statements are Assign { target: real_var, value: Var(temp) }
                // where temp matches the corresponding MultiAssign target
                let mut real_targets = Vec::with_capacity(n);
                let mut all_match = true;

                for j in 0..n {
                    if let HirStmt::Assign { target: real_target, value } = &stmts[i + 1 + j] {
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
                    // Replace: MultiAssign + N assigns → single MultiAssign with real targets
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

