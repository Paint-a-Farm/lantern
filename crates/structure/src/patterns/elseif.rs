//! Inverted elseif chain normalization.
//!
//! The Luau compiler generates elseif chains as:
//! ```text
//! if A ~= X then
//!     if A ~= Y then
//!         <fallthrough>
//!     else
//!         <handler_Y>
//!     end
//! else
//!     <handler_X>
//! end
//! ```
//!
//! This pass normalizes them to:
//! ```text
//! if A == X then
//!     <handler_X>
//! elseif A == Y then
//!     <handler_Y>
//! else
//!     <fallthrough>
//! end
//! ```

use lantern_hir::func::HirFunc;
use lantern_hir::stmt::{ElseIfClause, HirStmt};

use super::conditions::negate_condition;

/// Normalize inverted elseif chains.
///
/// Detection: `then_body` is a single If with no `elseif_clauses` and an
/// `else_body` exists. The inner If has the same inverted structure.
pub(super) fn normalize_inverted_elseif(func: &mut HirFunc, stmt: HirStmt) -> HirStmt {
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

    // Build the elseif chain from the inner If.
    // The inner If might itself be inverted — recursively normalize first.
    let mut clauses = Vec::new();
    let normalized_inner = normalize_inverted_elseif_inner(
        func,
        HirStmt::If {
            condition: inner_cond,
            then_body: inner_then,
            elseif_clauses: inner_elseif,
            else_body: inner_else,
        },
        true,
    );

    // Extract the chain from the normalized inner
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
