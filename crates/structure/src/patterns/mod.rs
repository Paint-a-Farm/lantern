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

mod compound;
mod conditions;
mod elseif;
mod guards;
mod phinode;
mod returns;
mod ternary;

use lantern_hir::func::HirFunc;
use lantern_hir::stmt::{ElseIfClause, HirStmt};

use compound::merge_compound_conditions;
use elseif::normalize_inverted_elseif;
use guards::{absorb_tail_into_else, decompose_guard_chain, flip_elseif_guard, flip_guard_to_wrapper, hoist_else_guards, merge_consecutive_guards};
use phinode::fold_phinode_returns;
use returns::{collapse_multi_return_temps, inline_return_temps, strip_redundant_returns};
use ternary::fold_ternary_patterns;

/// Apply all post-structuring patterns to the function.
pub fn apply_patterns(func: &mut HirFunc) {
    let entry = func.entry;
    let stmts = std::mem::take(&mut func.cfg[entry].stmts);
    let stmts = transform_stmts(func, stmts, true);
    func.cfg[entry].stmts = stmts;
}

/// Recursively transform a statement list, applying all patterns.
///
/// `is_top_level` is true only for the function's entry block — not for
/// nested bodies inside loops, ifs, etc.  This gates transforms that are
/// only valid at the outermost scope (e.g. bare-return guard flipping).
fn transform_stmts(func: &mut HirFunc, stmts: Vec<HirStmt>, is_top_level: bool) -> Vec<HirStmt> {
    let mut result = Vec::with_capacity(stmts.len());
    for stmt in stmts {
        let transformed = transform_stmt(func, stmt);
        for stmt in transformed {
            // Remove empty if-then-end statements (no body, no elseif, no else).
            // These are artifacts from the structurer or inliner — the original source
            // never had empty ifs (the compiler doesn't generate them).
            if matches!(&stmt, HirStmt::If {
                then_body, elseif_clauses, else_body, ..
            } if then_body.is_empty() && elseif_clauses.is_empty() && else_body.is_none())
            {
                continue;
            }
            result.push(stmt);
        }
    }
    // Fold ternary patterns: `x = b; if cond then x = a end` → `x = cond and a or b`
    result = fold_ternary_patterns(func, result);
    // Fold phi-node patterns into early returns:
    // `local _v = default; if cond then _v = val end; return _v`
    // → `if not cond then return default end; return val`
    result = fold_phinode_returns(func, result);
    // Collapse multi-return temps BEFORE guard flips, because flip_guard_to_wrapper
    // absorbs tail statements into if bodies — those wouldn't be visited again.
    result = collapse_multi_return_temps(func, result);
    // Merge consecutive early-exit guards (if cond then continue/break end)
    result = merge_consecutive_guards(func, result);
    // Flip single early-exit guards into wrapping if-then blocks
    result = flip_guard_to_wrapper(func, result);
    // Flip bare-return guards into wrapping if-not blocks — ONLY at top level.
    // A bare `return` at function-end is identical to falling through, but inside
    // nested blocks it's a real control flow exit that must be preserved.
    if is_top_level {
        result = absorb_tail_into_else(func, result);
    }
    // Strip redundant bare returns: when an if-branch ends with bare `return`
    // and the next statement is also bare `return`, the inner one is redundant.
    // Also strips sole-bare-return else bodies at end of statement list.
    strip_redundant_returns(&mut result);
    // Inline `local v = expr; return v` → `return expr`
    result = inline_return_temps(func, result);
    result
}

/// Transform a single statement, recursing into nested bodies.
/// Returns a Vec because some patterns decompose one stmt into multiple.
fn transform_stmt(func: &mut HirFunc, stmt: HirStmt) -> Vec<HirStmt> {
    match stmt {
        HirStmt::If {
            condition,
            negated,
            then_body,
            elseif_clauses,
            else_body,
        } => {
            // First, recurse into all bodies (nested = not top level)
            let then_body = transform_stmts(func, then_body, false);
            let elseif_clauses = elseif_clauses
                .into_iter()
                .map(|c| ElseIfClause {
                    condition: c.condition,
                    body: transform_stmts(func, c.body, false),
                })
                .collect();
            let else_body = else_body.map(|b| transform_stmts(func, b, false));

            let mut if_stmt = HirStmt::If {
                condition,
                negated,
                then_body,
                elseif_clauses,
                else_body,
            };

            // Apply patterns (order matters — normalize first, then merge, then flip guards)
            if_stmt = normalize_inverted_elseif(func, if_stmt);
            if_stmt = merge_compound_conditions(func, if_stmt);

            // Decompose guard chains BEFORE flipping: `if A then return elseif B then
            // return else <code> end` → separate `if A then return end; if B then
            // return end; <code>`. This must happen before flip_elseif_guard which
            // would merge the guard into the else body.
            if let Some(expanded) = decompose_guard_chain(&if_stmt) {
                return expanded;
            }

            // Hoist guard ifs from else body into elseif clauses:
            // `if A then return else { if B then return end; <tail> } end`
            // → `if A then return elseif B then return else <tail> end`
            if_stmt = hoist_else_guards(func, if_stmt);

            if_stmt = flip_elseif_guard(func, if_stmt);

            // Strip trailing empty elseif clauses (artifact of structuring).
            if let HirStmt::If {
                condition,
                negated,
                then_body,
                mut elseif_clauses,
                else_body,
            } = if_stmt
            {
                while elseif_clauses.last().is_some_and(|c| c.body.is_empty()) {
                    elseif_clauses.pop();
                }
                if_stmt = HirStmt::If {
                    condition,
                    negated,
                    then_body,
                    elseif_clauses,
                    else_body,
                };
            }

            vec![if_stmt]
        }
        HirStmt::While { condition, body } => vec![HirStmt::While {
            condition,
            body: transform_stmts(func, body, false),
        }],
        HirStmt::Repeat { body, condition } => vec![HirStmt::Repeat {
            body: transform_stmts(func, body, false),
            condition,
        }],
        HirStmt::NumericFor {
            var,
            start,
            limit,
            step,
            body,
        } => vec![HirStmt::NumericFor {
            var,
            start,
            limit,
            step,
            body: transform_stmts(func, body, false),
        }],
        HirStmt::GenericFor {
            vars,
            iterators,
            body,
        } => vec![HirStmt::GenericFor {
            vars,
            iterators,
            body: transform_stmts(func, body, false),
        }],
        other => vec![other],
    }
}
