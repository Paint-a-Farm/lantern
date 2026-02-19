use std::fmt::Write;

use lantern_hir::stmt::{ElseIfClause, HirStmt, LValue};
use lantern_hir::var::VarId;

use rustc_hash::FxHashSet;

use super::LuaEmitter;

impl<'a> LuaEmitter<'a> {
    /// Pre-declare local variables that are first assigned inside one branch
    /// of an if-statement but referenced in another branch or after the if.
    ///
    /// Without this, `local p0x = p0.x` inside an if-branch would scope p0x
    /// to that branch, making it a global reference in the else-branch.
    pub(super) fn hoist_branch_locals(
        &mut self,
        then_body: &[HirStmt],
        elseif_clauses: &[ElseIfClause],
        else_body: Option<&[HirStmt]>,
    ) {
        // Collect undeclared locals assigned in each branch
        let then_assigns = self.collect_undeclared_assigns(then_body);
        let mut other_assigns = FxHashSet::default();
        let mut other_refs = FxHashSet::default();
        if let Some(else_stmts) = else_body {
            other_assigns.extend(self.collect_undeclared_assigns(else_stmts));
            other_refs.extend(collect_var_refs(else_stmts));
        }
        for clause in elseif_clauses {
            other_assigns.extend(self.collect_undeclared_assigns(&clause.body));
            other_refs.extend(collect_var_refs(&clause.body));
        }

        // A variable needs hoisting if:
        // - It's first assigned in the then-branch AND referenced in else/elseif, or
        // - It's first assigned in else/elseif AND referenced in then-branch
        let then_refs = collect_var_refs(then_body);

        let mut to_hoist = Vec::new();
        for &var_id in &then_assigns {
            if other_assigns.contains(&var_id) || other_refs.contains(&var_id) {
                to_hoist.push(var_id);
            }
        }
        for &var_id in &other_assigns {
            if then_refs.contains(&var_id) && !to_hoist.contains(&var_id) {
                to_hoist.push(var_id);
            }
        }

        // Sort for deterministic output
        to_hoist.sort_by_key(|v| v.0);

        for var_id in to_hoist {
            let name = self.var_name(var_id);
            self.write_indent();
            let _ = writeln!(self.output, "local {} = nil", name);
            self.declared.insert(var_id);
        }
    }

    /// Collect VarIds that are assigned as `LValue::Local(var_id)` in statements
    /// where var_id hasn't been declared yet.
    pub(super) fn collect_undeclared_assigns(&self, stmts: &[HirStmt]) -> FxHashSet<VarId> {
        let mut result = FxHashSet::default();
        for stmt in stmts {
            collect_undeclared_assigns_stmt(stmt, &self.declared, &mut result);
        }
        result
    }
}

/// Collect VarIds assigned as LValue::Local in statements, recursively.
/// Only includes vars not in `declared`.
pub(super) fn collect_undeclared_assigns_stmt(
    stmt: &HirStmt,
    declared: &FxHashSet<VarId>,
    result: &mut FxHashSet<VarId>,
) {
    match stmt {
        HirStmt::Assign { target: LValue::Local(var_id), .. } => {
            if !declared.contains(var_id) {
                result.insert(*var_id);
            }
        }
        HirStmt::MultiAssign { targets, .. } => {
            for t in targets {
                if let LValue::Local(var_id) = t {
                    if !declared.contains(var_id) {
                        result.insert(*var_id);
                    }
                }
            }
        }
        HirStmt::If { then_body, elseif_clauses, else_body, .. } => {
            for s in then_body {
                collect_undeclared_assigns_stmt(s, declared, result);
            }
            for clause in elseif_clauses {
                for s in &clause.body {
                    collect_undeclared_assigns_stmt(s, declared, result);
                }
            }
            if let Some(else_stmts) = else_body {
                for s in else_stmts {
                    collect_undeclared_assigns_stmt(s, declared, result);
                }
            }
        }
        HirStmt::While { body, .. } | HirStmt::Repeat { body, .. } => {
            for s in body {
                collect_undeclared_assigns_stmt(s, declared, result);
            }
        }
        HirStmt::NumericFor { body, .. } | HirStmt::GenericFor { body, .. } => {
            for s in body {
                collect_undeclared_assigns_stmt(s, declared, result);
            }
        }
        _ => {}
    }
}

/// Collect all VarIds referenced (read or assigned) in statements.
pub(super) fn collect_var_refs(stmts: &[HirStmt]) -> FxHashSet<VarId> {
    let mut result = FxHashSet::default();
    for stmt in stmts {
        collect_var_refs_stmt(stmt, &mut result);
    }
    result
}

fn collect_var_refs_stmt(stmt: &HirStmt, result: &mut FxHashSet<VarId>) {
    match stmt {
        HirStmt::Assign { target, .. } => {
            if let LValue::Local(var_id) = target {
                result.insert(*var_id);
            }
        }
        HirStmt::MultiAssign { targets, .. } => {
            for t in targets {
                if let LValue::Local(var_id) = t {
                    result.insert(*var_id);
                }
            }
        }
        HirStmt::If { then_body, elseif_clauses, else_body, .. } => {
            for s in then_body {
                collect_var_refs_stmt(s, result);
            }
            for clause in elseif_clauses {
                for s in &clause.body {
                    collect_var_refs_stmt(s, result);
                }
            }
            if let Some(else_stmts) = else_body {
                for s in else_stmts {
                    collect_var_refs_stmt(s, result);
                }
            }
        }
        HirStmt::While { body, .. } | HirStmt::Repeat { body, .. } => {
            for s in body {
                collect_var_refs_stmt(s, result);
            }
        }
        HirStmt::NumericFor { body, .. } | HirStmt::GenericFor { body, .. } => {
            for s in body {
                collect_var_refs_stmt(s, result);
            }
        }
        _ => {}
    }
}
