//! Guard clause patterns.
//!
//! Handles three related transformations:
//!
//! 1. **`flip_elseif_guard`** — when the last elseif clause is a short guard and
//!    the else body has real code, flip the guard's condition and drop the else.
//!
//! 2. **`merge_consecutive_guards`** — collapses adjacent
//!    `if cond then continue end` / `if cond then break end` guards into a single
//!    `if cond1 or cond2 then continue/break end`.
//!
//! 3. **`flip_guard_to_wrapper`** — converts a leading `if cond then continue end`
//!    guard into a wrapping `if not cond then <rest> end` block.

use lantern_hir::arena::ExprId;
use lantern_hir::expr::HirExpr;
use lantern_hir::func::HirFunc;
use lantern_hir::stmt::{ElseIfClause, HirStmt};
use lantern_hir::types::{BinOp, LuaValue};

use super::conditions::negate_or_chain;

// ---------------------------------------------------------------------------
// Guard chain decomposition
// ---------------------------------------------------------------------------

/// Decompose an if-elseif chain where ALL branches are short guards into
/// separate guard statements followed by the else body.
///
/// ```text
/// if A then return               -->   if A then return end
/// elseif B then return                 if B then return end
/// else <code> end                      <code>
/// ```
///
/// Only applies when then_body AND all elseif clauses are short guards
/// (≤3 stmts ending with return/break) and the else body has real code.
/// Returns `Some(stmts)` if decomposed, `None` if not applicable.
pub(super) fn decompose_guard_chain(stmt: &HirStmt) -> Option<Vec<HirStmt>> {
    let HirStmt::If {
        condition,
        then_body,
        elseif_clauses,
        else_body,
        ..
    } = stmt
    else {
        return None;
    };

    // Must have at least one elseif clause (otherwise flip_guard_to_wrapper handles it)
    if elseif_clauses.is_empty() {
        return None;
    }

    // Must have an else body with real code
    let Some(else_body_stmts) = else_body else {
        return None;
    };
    if ends_with_exit(else_body_stmts) {
        return None;
    }

    // then_body must be a short guard
    if !is_short_guard(then_body) {
        return None;
    }

    // ALL elseif clauses must be short guards
    if !elseif_clauses.iter().all(|c| is_short_guard(&c.body)) {
        return None;
    }

    // Decompose: each guard becomes a separate `if cond then <guard> end`
    let mut result = Vec::with_capacity(elseif_clauses.len() + 1 + else_body_stmts.len());

    // First guard from then_body
    result.push(HirStmt::If {
        condition: *condition,
        negated: true,
        then_body: then_body.clone(),
        elseif_clauses: Vec::new(),
        else_body: None,
    });

    // Each elseif becomes a separate guard
    for clause in elseif_clauses {
        result.push(HirStmt::If {
            condition: clause.condition,
            negated: true,
            then_body: clause.body.clone(),
            elseif_clauses: Vec::new(),
            else_body: None,
        });
    }

    // Append else body stmts directly
    result.extend(else_body_stmts.iter().cloned());

    Some(result)
}

// ---------------------------------------------------------------------------
// Hoist guards from else body into elseif clauses
// ---------------------------------------------------------------------------

/// When then_body is a short guard and the else_body starts with guard-like
/// if-statements, promote them to elseif clauses.
///
/// ```text
/// if A then return X                -->   if A then return X
/// else                                    elseif B then return Y
///     if B then return Y                  else <tail> end
///     end
///     <tail>
/// end
/// ```
///
/// Only applies when there are no existing elseif clauses, the then_body is a
/// short guard, and the else_body starts with simple if-then-end guards
/// (no elseif/else on the inner ifs).
pub(super) fn hoist_else_guards(_func: &mut HirFunc, stmt: HirStmt) -> HirStmt {
    let HirStmt::If {
        condition,
        negated,
        then_body,
        elseif_clauses,
        else_body,
    } = stmt
    else {
        return stmt;
    };

    // Requires: no existing elseif clauses, then_body is a short guard, else_body exists
    if !elseif_clauses.is_empty() || !is_short_guard(&then_body) {
        return HirStmt::If {
            condition,
            negated,
            then_body,
            elseif_clauses,
            else_body,
        };
    }

    let Some(else_stmts) = else_body else {
        return HirStmt::If {
            condition,
            negated,
            then_body,
            elseif_clauses,
            else_body: None,
        };
    };

    // Collect leading guard ifs from the else body
    let mut new_elseif = Vec::new();
    let mut rest_start = 0;

    for (i, stmt) in else_stmts.iter().enumerate() {
        if let HirStmt::If {
            condition: inner_cond,
            then_body: ref inner_then,
            elseif_clauses: ref inner_elseif,
            else_body: ref inner_else,
            ..
        } = *stmt
        {
            if inner_elseif.is_empty() && inner_else.is_none() && is_short_guard(inner_then) {
                new_elseif.push(ElseIfClause {
                    condition: inner_cond,
                    body: inner_then.clone(),
                });
                rest_start = i + 1;
                continue;
            }
        }
        break;
    }

    // Need at least one hoisted guard to be worthwhile
    if new_elseif.is_empty() {
        return HirStmt::If {
            condition,
            negated,
            then_body,
            elseif_clauses,
            else_body: Some(else_stmts),
        };
    }

    let tail: Vec<HirStmt> = else_stmts[rest_start..].to_vec();
    let new_else = if tail.is_empty() { None } else { Some(tail) };

    HirStmt::If {
        condition,
        negated,
        then_body,
        elseif_clauses: new_elseif,
        else_body: new_else,
    }
}

// ---------------------------------------------------------------------------
// Elseif guard flip
// ---------------------------------------------------------------------------

/// Flip the last elseif clause when it is a short guard (ends with return/break)
/// and the else body has real code.
///
/// ```text
/// if A then ...
/// elseif B then return           -->   if A then ...
/// else <code> end                      elseif not B then <code> end
/// ```
pub(super) fn flip_elseif_guard(func: &mut HirFunc, stmt: HirStmt) -> HirStmt {
    let HirStmt::If {
        condition,
        negated,
        then_body,
        mut elseif_clauses,
        else_body,
    } = stmt
    else {
        return stmt;
    };

    let Some(ref else_body_stmts) = else_body else {
        return HirStmt::If {
            condition,
            negated,
            then_body,
            elseif_clauses,
            else_body,
        };
    };

    if let Some(last_clause) = elseif_clauses.last_mut() {
        // Flip when:
        // (a) guard body is short + else body is NOT an exit (normal case), OR
        // (b) guard body is a trivial return (return / return nil) even if else also exits
        let can_flip = is_short_guard(&last_clause.body)
            && (!ends_with_exit(else_body_stmts) || is_trivial_return(func, &last_clause.body));
        if can_flip {
            let guard_stmts = std::mem::replace(&mut last_clause.body, else_body.unwrap());
            last_clause.condition = negate_or_chain(func, last_clause.condition);

            // Bare `return` — drop it; the function will return implicitly
            if guard_stmts.len() == 1
                && matches!(guard_stmts[0], HirStmt::Return(ref v) if v.is_empty())
            {
                return HirStmt::If {
                    condition,
                    negated: true,
                    then_body,
                    elseif_clauses,
                    else_body: None,
                };
            }
            // Guard has content (e.g. `return nil`, `error(); return`) — keep as else
            return HirStmt::If {
                condition,
                negated,
                then_body,
                elseif_clauses,
                else_body: Some(guard_stmts),
            };
        }
    } else if is_short_guard(&then_body) && !ends_with_exit(else_body_stmts) {
        // No elseif clauses — then-body is a guard with else having real code.
        // Already handled by the structurer; keep as-is for safety.
        return HirStmt::If {
            condition,
            negated,
            then_body,
            elseif_clauses,
            else_body,
        };
    }

    HirStmt::If {
        condition,
        negated,
        then_body,
        elseif_clauses,
        else_body,
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Check if a statement list is a short guard clause (≤3 statements ending with
/// `return` or `break`).
pub(super) fn is_short_guard(stmts: &[HirStmt]) -> bool {
    if stmts.is_empty() || stmts.len() > 3 {
        return false;
    }
    matches!(stmts.last(), Some(HirStmt::Return { .. } | HirStmt::Break))
}

/// Check if a statement list ends with an exit (`return` or `break`).
pub(super) fn ends_with_exit(stmts: &[HirStmt]) -> bool {
    matches!(stmts.last(), Some(HirStmt::Return { .. } | HirStmt::Break))
}

/// Check if a statement list is a trivial return — just `return` or `return nil`.
/// These are implicit at the end of a function and can be dropped after guard flipping.
fn is_trivial_return(func: &HirFunc, stmts: &[HirStmt]) -> bool {
    if stmts.len() != 1 {
        return false;
    }
    match &stmts[0] {
        HirStmt::Return(v) if v.is_empty() => true,
        HirStmt::Return(v) if v.len() == 1 => {
            matches!(func.exprs.get(v[0]), HirExpr::Literal(LuaValue::Nil))
        }
        _ => false,
    }
}

/// Check if a statement list is "linear" — no control flow branching.
/// A linear tail produces only one implicit RETURN path, so wrapping it in
/// an if-block doesn't change the RETURN count.
fn is_linear_tail(stmts: &[HirStmt]) -> bool {
    stmts.iter().all(|s| {
        !matches!(
            s,
            HirStmt::If { .. }
                | HirStmt::While { .. }
                | HirStmt::Repeat { .. }
                | HirStmt::NumericFor { .. }
                | HirStmt::GenericFor { .. }
        )
    })
}

/// Check if a statement is `if cond then continue end` or `if cond then break end`
/// with no elseif/else branches.
///
/// Returns `Some((condition, is_continue))` or `None`.
pub(super) fn is_early_exit_guard(stmt: &HirStmt) -> Option<(&ExprId, bool)> {
    if let HirStmt::If {
        condition,
        then_body,
        elseif_clauses,
        else_body,
        ..
    } = stmt
    {
        if elseif_clauses.is_empty() && else_body.is_none() && then_body.len() == 1 {
            let is_continue = matches!(&then_body[0], HirStmt::Continue);
            let is_break = matches!(&then_body[0], HirStmt::Break);
            if is_continue || is_break {
                return Some((condition, is_continue));
            }
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Consecutive guard merging
// ---------------------------------------------------------------------------

/// Merge consecutive early-exit guards with the same exit type.
///
/// ```text
/// if cond1 then continue end     -->   if cond1 or cond2 then continue end
/// if cond2 then continue end
/// ```
pub(super) fn merge_consecutive_guards(func: &mut HirFunc, stmts: Vec<HirStmt>) -> Vec<HirStmt> {
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
                let exit_stmt = if first_is_continue {
                    HirStmt::Continue
                } else {
                    HirStmt::Break
                };
                result.push(HirStmt::If {
                    condition: merged_cond,
                    negated: true,
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

// ---------------------------------------------------------------------------
// Guard-to-wrapper flip
// ---------------------------------------------------------------------------

/// Flip an early-exit guard into a wrapping if block.
///
/// ```text
/// <leading stmts>                  <leading stmts>
/// if cond then continue end  -->   if not cond then
/// stmt1                                stmt1
/// stmt2                                stmt2
///                                  end
/// ```
///
/// Flips `continue` guards and bare `return` guards (no return value).
/// `break` guards are not flipped — they exit the loop rather than skip one
/// iteration, so wrapping would change semantics.
///
/// The guard does not need to be the first statement — leading non-guard
/// statements are preserved before the wrapping if block.
pub(super) fn flip_guard_to_wrapper(_func: &mut HirFunc, stmts: Vec<HirStmt>) -> Vec<HirStmt> {
    // Previously flipped `if cond then continue end; body` → `if not cond then body end`.
    // Disabled: these forms produce different opcodes (JumpIfLt vs JumpIfNotLe),
    // so flipping breaks roundtrip fidelity. Guard+continue is preserved as-is.
    stmts
}

// ---------------------------------------------------------------------------
// Tail absorption into else
// ---------------------------------------------------------------------------

/// When an if-then-end with bare `return` (no values) is followed by a short
/// tail at the end of a statement list, flip the guard into a wrapping if.
///
/// ```text
/// if cond then return end          if not cond then
/// shortTail()                -->       shortTail()
///                                  end
/// ```
///
/// A bare `return` at the end of a function is identical to falling through
/// (both compile to the same implicit RETURN). Flipping the guard removes
/// the explicit RETURN, matching the original `if not cond then code end` style
/// that the compiler generates with just 1 implicit RETURN.
///
/// Only applies to bare `return` (no values) — `return X` guards stay as-is
/// because the explicit return value needs the RETURN instruction.
pub(super) fn absorb_tail_into_else(func: &mut HirFunc, stmts: Vec<HirStmt>) -> Vec<HirStmt> {
    if stmts.len() < 2 {
        return stmts;
    }

    // Find `if cond then return end` (bare return, no elseif/else) followed by
    // a short non-exit tail. Walk backwards to find the best candidate.
    let mut if_idx = None;
    for i in (0..stmts.len() - 1).rev() {
        if let HirStmt::If {
            then_body,
            elseif_clauses,
            else_body,
            ..
        } = &stmts[i]
        {
            if elseif_clauses.is_empty()
                && else_body.is_none()
                && then_body.len() == 1
                && matches!(&then_body[0], HirStmt::Return(v) if v.is_empty())
            {
                let tail = &stmts[i + 1..];
                if !tail.is_empty() && !ends_with_exit(tail) && is_linear_tail(tail) {
                    if_idx = Some(i);
                    break;
                }
            }
        }
    }

    let Some(i) = if_idx else {
        return stmts;
    };

    // Extract the condition and negate it
    let condition = if let HirStmt::If { condition, .. } = &stmts[i] {
        *condition
    } else {
        unreachable!()
    };
    let inv_cond = negate_or_chain(func, condition);

    let mut result = stmts;
    let tail: Vec<HirStmt> = result.split_off(i + 1);

    // Replace the guard with a wrapping if-not-cond
    *result.last_mut().unwrap() = HirStmt::If {
        condition: inv_cond,
        negated: true,
        then_body: tail,
        elseif_clauses: Vec::new(),
        else_body: None,
    };

    result
}
