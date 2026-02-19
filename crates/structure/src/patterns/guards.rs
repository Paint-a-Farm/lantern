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
use lantern_hir::stmt::HirStmt;
use lantern_hir::types::BinOp;

use super::conditions::{negate_condition, negate_or_chain};

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

    if let Some(last_clause) = elseif_clauses.last_mut() {
        if is_short_guard(&last_clause.body) && !ends_with_exit(else_body_stmts) {
            let guard_stmts = std::mem::replace(&mut last_clause.body, else_body.unwrap());
            last_clause.condition = negate_condition(func, last_clause.condition);

            // Bare `return` — drop it; the function will return implicitly
            if guard_stmts.len() == 1
                && matches!(guard_stmts[0], HirStmt::Return(ref v) if v.is_empty())
            {
                return HirStmt::If { condition, then_body, elseif_clauses, else_body: None };
            }
            // Guard has content (e.g. `error(); return`) — keep as else
            return HirStmt::If {
                condition,
                then_body,
                elseif_clauses,
                else_body: Some(guard_stmts),
            };
        }
    } else if is_short_guard(&then_body) && !ends_with_exit(else_body_stmts) {
        // No elseif clauses — then-body is a guard with else having real code.
        // Already handled by the structurer; keep as-is for safety.
        return HirStmt::If { condition, then_body, elseif_clauses, else_body };
    }

    HirStmt::If { condition, then_body, elseif_clauses, else_body }
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
                let exit_stmt = if first_is_continue { HirStmt::Continue } else { HirStmt::Break };
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

// ---------------------------------------------------------------------------
// Guard-to-wrapper flip
// ---------------------------------------------------------------------------

/// Flip a single early-exit `continue` guard at the start of a list into a
/// wrapping if block.
///
/// ```text
/// if cond then continue end     -->   if not cond then
/// stmt1                                   stmt1
/// stmt2                                   stmt2
///                                     end
/// ```
///
/// Only applies when the guard is the first statement and there are following
/// statements to wrap. Only flips `continue` guards — `break` has different
/// semantics (exits the loop).
pub(super) fn flip_guard_to_wrapper(func: &mut HirFunc, stmts: Vec<HirStmt>) -> Vec<HirStmt> {
    if stmts.len() < 2 {
        return stmts;
    }

    // Only flip `continue` guards
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
