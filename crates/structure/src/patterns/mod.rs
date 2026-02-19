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
mod returns;

use lantern_hir::func::HirFunc;
use lantern_hir::stmt::{ElseIfClause, HirStmt};

use compound::merge_compound_conditions;
use elseif::normalize_inverted_elseif;
use guards::{flip_elseif_guard, flip_guard_to_wrapper, merge_consecutive_guards};
use returns::{collapse_multi_return_temps, inline_return_temps};

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
        HirStmt::NumericFor { var, start, limit, step, body } => HirStmt::NumericFor {
            var,
            start,
            limit,
            step,
            body: transform_stmts(func, body),
        },
        HirStmt::GenericFor { vars, iterators, body } => HirStmt::GenericFor {
            vars,
            iterators,
            body: transform_stmts(func, body),
        },
        other => other,
    }
}
