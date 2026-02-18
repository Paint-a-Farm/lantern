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
use lantern_hir::stmt::{ElseIfClause, HirStmt};
use lantern_hir::types::{BinOp, UnOp};

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

            // Apply patterns (order matters — normalize first, then merge)
            if_stmt = normalize_inverted_elseif(func, if_stmt);
            if_stmt = merge_compound_conditions(func, if_stmt);

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

fn negate_condition(func: &mut HirFunc, condition: lantern_hir::arena::ExprId) -> lantern_hir::arena::ExprId {
    // If already `not X`, just return X (double negation elimination)
    if let HirExpr::Unary {
        op: UnOp::Not,
        operand,
    } = func.exprs.get(condition)
    {
        return *operand;
    }

    // For comparisons, invert the operator
    if let HirExpr::Binary { op, left, right } = func.exprs.get(condition).clone() {
        let inv_op = match op {
            BinOp::CompareEq => Some(BinOp::CompareNe),
            BinOp::CompareNe => Some(BinOp::CompareEq),
            BinOp::CompareLt => Some(BinOp::CompareGe),
            BinOp::CompareLe => Some(BinOp::CompareGt),
            BinOp::CompareGt => Some(BinOp::CompareLe),
            BinOp::CompareGe => Some(BinOp::CompareLt),
            _ => None,
        };
        if let Some(inv_op) = inv_op {
            return func.exprs.alloc(HirExpr::Binary {
                op: inv_op,
                left,
                right,
            });
        }
    }

    func.exprs.alloc(HirExpr::Unary {
        op: UnOp::Not,
        operand: condition,
    })
}

