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

use lantern_hir::arena::ExprId;
use lantern_hir::expr::HirExpr;
use lantern_hir::func::HirFunc;
use lantern_hir::stmt::{ElseIfClause, HirStmt};
use lantern_hir::types::{BinOp, UnOp};

use super::conditions::negate_condition;

/// Check if negating a condition would be "clean" — either removing an existing
/// `not` wrapper or inverting a comparison operator — without adding a `not()`
/// wrapper that would change the emitted bytecode.
fn is_cleanly_negatable(func: &HirFunc, condition: ExprId) -> bool {
    match func.exprs.get(condition) {
        HirExpr::Unary {
            op: UnOp::Not, ..
        } => true,
        HirExpr::Binary { op, .. } => matches!(
            op,
            BinOp::CompareEq
                | BinOp::CompareNe
                | BinOp::CompareLt
                | BinOp::CompareLe
                | BinOp::CompareGt
                | BinOp::CompareGe
        ),
        _ => false,
    }
}

/// Check if a condition can be safely inverted given its bytecode polarity.
/// negated=false → guard form: condition already has not()/inverted comparison → safe
/// negated=true → wrapping form: only safe if cleanly negatable
fn can_invert_condition(func: &HirFunc, condition: ExprId, negated: bool) -> bool {
    !negated || is_cleanly_negatable(func, condition)
}

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
        negated,
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
            negated,
            then_body,
            elseif_clauses,
            else_body,
        };
    }

    // Check if then_body is a single If *with an else_body* (chain continues).
    // An inverted elseif chain has `if A then if B then ... else handler end else handler end`.
    // If the inner If has no else_body, it's a genuine `if A then <nested check> else <alt> end`,
    // not an inverted chain — leave it alone to preserve branch polarity.
    let is_chain = then_body.len() == 1
        && matches!(&then_body[0], HirStmt::If { else_body: Some(_), elseif_clauses, .. } if elseif_clauses.is_empty());
    let else_body = else_body.unwrap();

    if !is_chain {
        if in_chain {
            // Leaf of an inverted chain. Try to invert if safe, otherwise
            // keep the condition and bodies as-is from the structurer.
            //
            // When kept as-is, the condition and bodies are in the correct
            // positions because the structurer already accounts for branch
            // polarity. The un-inverted condition compiles to the same opcode
            // (JumpIfNot for both `if cond then` and `elseif cond then`).
            if can_invert_condition(func, condition, negated) {
                let inv_condition = negate_condition(func, condition);
                return HirStmt::If {
                    condition: inv_condition,
                    negated: true, // wrapping form after inversion
                    then_body: else_body,
                    elseif_clauses: Vec::new(),
                    else_body: Some(then_body),
                };
            }
            // Keep as-is — bodies stay in structurer order
            return HirStmt::If {
                condition,
                negated,
                then_body,
                elseif_clauses: Vec::new(),
                else_body: Some(else_body),
            };
        }
        // Not in a chain context — leave as-is
        return HirStmt::If {
            condition,
            negated,
            then_body,
            elseif_clauses: Vec::new(),
            else_body: Some(else_body),
        };
    }

    // We're at a chain node (not a leaf). The condition will be inverted.
    // Guard: only proceed if the condition can be cleanly inverted.
    if !can_invert_condition(func, condition, negated) {
        return HirStmt::If {
            condition,
            negated,
            then_body,
            elseif_clauses: Vec::new(),
            else_body: Some(else_body),
        };
    }

    let inv_condition = negate_condition(func, condition);

    // The inner If becomes the elseif chain
    let inner_if = then_body.into_iter().next().unwrap();
    let HirStmt::If {
        condition: inner_cond,
        negated: inner_negated,
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
            negated: inner_negated,
            then_body: inner_then,
            elseif_clauses: inner_elseif,
            else_body: inner_else,
        },
        true,
    );

    // Extract the chain from the normalized inner
    if let HirStmt::If {
        condition: norm_cond,
        negated: _,
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
            negated: true, // inverted outer condition → wrapping form
            then_body: else_body,
            elseif_clauses: clauses,
            else_body: norm_else,
        }
    } else {
        unreachable!();
    }
}
