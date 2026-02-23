//! Condition negation helpers shared across pattern passes.

use lantern_hir::arena::ExprId;
use lantern_hir::expr::HirExpr;
use lantern_hir::func::HirFunc;
use lantern_hir::types::BinOp;

/// Negate a condition using the arena's built-in negation.
pub(super) fn negate_condition(func: &mut HirFunc, condition: ExprId) -> ExprId {
    func.exprs.negate_condition(condition)
}

/// Negate a condition, applying De Morgan's law to `or` chains.
///
/// `c1 or c2 or c3` -> `(not c1) and (not c2) and (not c3)`
///
/// For non-or expressions, falls back to simple negation.
pub(super) fn negate_or_chain(func: &mut HirFunc, condition: ExprId) -> ExprId {
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
pub(super) fn flatten_or_chain(func: &HirFunc, expr: ExprId, out: &mut Vec<ExprId>) {
    if let HirExpr::Binary {
        op: BinOp::Or,
        left,
        right,
    } = func.exprs.get(expr)
    {
        flatten_or_chain(func, *left, out);
        out.push(*right);
    } else {
        out.push(expr);
    }
}
