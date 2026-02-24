use lantern_hir::stmt::HirStmt;

/// Check if a statement list is a "guard clause" — a short block (≤3 statements)
/// that ends with return or break. These are typically early-out checks like:
///   if not valid then error("..."); return end
pub(super) fn is_guard_clause(stmts: &[HirStmt]) -> bool {
    if stmts.is_empty() || stmts.len() > 3 {
        return false;
    }
    matches!(stmts.last(), Some(HirStmt::Return { .. } | HirStmt::Break))
}

/// Check if a statement list ends with an exit (return or break).
/// Used to distinguish symmetric if-else (both branches exit) from
/// guard clauses (one branch exits, the other continues).
pub(super) fn ends_with_exit(stmts: &[HirStmt]) -> bool {
    matches!(stmts.last(), Some(HirStmt::Return { .. } | HirStmt::Break))
}

/// Recursively strip trailing bare `return` statements that are redundant.
/// A bare `return` at the end of a function body is implicit in Lua.
/// This also strips them from the last if/else/elseif branches when the
/// if statement is itself the last statement in the function.
///
/// Only strips a bare return when the branch has other statements — a branch
/// whose sole purpose is `return` (early exit guard) must keep it.
///
/// When any sibling branch ends with `return <value>`, bare returns in other
/// branches are kept — removing them changes bytecode because the compiler
/// must add a Jump + implicit trailing Return instead.
pub(super) fn strip_trailing_returns(stmts: &mut Vec<HirStmt>) {
    // Strip a trailing bare return from the statement list itself
    if matches!(stmts.last(), Some(HirStmt::Return(v)) if v.is_empty()) {
        stmts.pop();
    }

    // If the last statement is an if, recurse into all its branches
    if let Some(HirStmt::If {
        then_body,
        elseif_clauses,
        else_body,
        ..
    }) = stmts.last_mut()
    {
        // Check if any branch ends with a non-bare return (return <value>).
        // If so, don't strip bare returns from other branches — the compiler
        // generates different bytecode (Jump + trailing Return vs inline Return).
        let has_valued_return = has_non_bare_return(then_body)
            || elseif_clauses.iter().any(|c| has_non_bare_return(&c.body))
            || else_body.as_ref().is_some_and(|b| has_non_bare_return(b));

        if !has_valued_return {
            strip_trailing_return_if_not_sole(then_body);
            for clause in elseif_clauses.iter_mut() {
                strip_trailing_return_if_not_sole(&mut clause.body);
            }
            if let Some(else_body) = else_body {
                strip_trailing_return_if_not_sole(else_body);
            }
        }
    }
}

/// Check if a statement list ends with `return <values>` (non-empty return).
fn has_non_bare_return(stmts: &[HirStmt]) -> bool {
    match stmts.last() {
        Some(HirStmt::Return(v)) => !v.is_empty(),
        Some(HirStmt::If {
            then_body,
            elseif_clauses,
            else_body,
            ..
        }) => {
            has_non_bare_return(then_body)
                || elseif_clauses.iter().any(|c| has_non_bare_return(&c.body))
                || else_body.as_ref().is_some_and(|b| has_non_bare_return(b))
        }
        _ => false,
    }
}

/// Strip a trailing bare return from a branch body, but only if it's not the
/// sole statement. A branch with only `return` is an early-exit guard and
/// must keep the return to be meaningful.
fn strip_trailing_return_if_not_sole(stmts: &mut Vec<HirStmt>) {
    if stmts.len() > 1 {
        if matches!(stmts.last(), Some(HirStmt::Return(v)) if v.is_empty()) {
            stmts.pop();
        }
    }
    // Recurse into nested if as last statement
    if let Some(HirStmt::If {
        then_body,
        elseif_clauses,
        else_body,
        ..
    }) = stmts.last_mut()
    {
        strip_trailing_return_if_not_sole(then_body);
        for clause in elseif_clauses.iter_mut() {
            strip_trailing_return_if_not_sole(&mut clause.body);
        }
        if let Some(else_body) = else_body {
            strip_trailing_return_if_not_sole(else_body);
        }
    }
}
