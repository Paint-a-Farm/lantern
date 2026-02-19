//! Compound condition merging.
//!
//! Merges nested single-branch `if` statements into `and`-chained conditions:
//! `if A then if B then <body> end end` -> `if A and B then <body> end`
//!
//! Also handles the vacuous-then pattern:
//! `if A then (empty) elseif B then ...` -> `if (not A) and B then ...`

use lantern_hir::expr::HirExpr;
use lantern_hir::func::HirFunc;
use lantern_hir::stmt::{ElseIfClause, HirStmt};
use lantern_hir::types::BinOp;

use super::conditions::negate_condition;

/// Merge compound conditions (and-chains).
///
/// Pattern 1 — vacuous then:
/// `if A then (empty) elseif B then ... end` -> `if (not A) and B then ... end`
///
/// Pattern 2 — nested if:
/// `if A then <single if B (no else)> end (no else)` -> `if A and B then <body> end`
pub(super) fn merge_compound_conditions(func: &mut HirFunc, stmt: HirStmt) -> HirStmt {
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
    if then_body.is_empty() && !elseif_clauses.is_empty() && else_body.is_none() {
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
