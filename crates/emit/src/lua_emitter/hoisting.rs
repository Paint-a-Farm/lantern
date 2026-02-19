use std::fmt::Write;

use lantern_hir::arena::ExprId;
use lantern_hir::expr::HirExpr;
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
        following_stmts: &[HirStmt],
    ) {
        // Collect undeclared locals assigned in each branch
        let then_assigns = self.collect_undeclared_assigns(then_body);
        let mut other_assigns = FxHashSet::default();
        let mut other_refs = FxHashSet::default();
        if let Some(else_stmts) = else_body {
            other_assigns.extend(self.collect_undeclared_assigns(else_stmts));
            other_refs.extend(collect_var_refs(else_stmts, &self.func.exprs));
        }
        for clause in elseif_clauses {
            other_assigns.extend(self.collect_undeclared_assigns(&clause.body));
            other_refs.extend(collect_var_refs(&clause.body, &self.func.exprs));
        }

        // Also collect references from statements that follow the if block
        let following_refs = collect_var_refs(following_stmts, &self.func.exprs);

        // A variable needs hoisting if:
        // - It's first assigned in the then-branch AND referenced in else/elseif, or
        // - It's first assigned in else/elseif AND referenced in then-branch, or
        // - It's first assigned in ANY branch AND referenced in following statements
        let then_refs = collect_var_refs(then_body, &self.func.exprs);

        // Collect all undeclared assigns across all branches
        let mut all_branch_assigns = then_assigns.clone();
        all_branch_assigns.extend(&other_assigns);

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
        // Hoist any variable first-assigned in any branch that's referenced after the if
        for &var_id in &all_branch_assigns {
            if following_refs.contains(&var_id) && !to_hoist.contains(&var_id) {
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

/// Collect all VarIds referenced (read or assigned) in statements,
/// including reads from expressions via the expression arena.
pub(super) fn collect_var_refs(
    stmts: &[HirStmt],
    exprs: &lantern_hir::arena::ExprArena,
) -> FxHashSet<VarId> {
    let mut result = FxHashSet::default();
    for stmt in stmts {
        collect_var_refs_stmt(stmt, exprs, &mut result);
    }
    result
}

fn collect_var_refs_stmt(
    stmt: &HirStmt,
    exprs: &lantern_hir::arena::ExprArena,
    result: &mut FxHashSet<VarId>,
) {
    match stmt {
        HirStmt::Assign { target, value } => {
            if let LValue::Local(var_id) = target {
                result.insert(*var_id);
            }
            collect_expr_var_refs(*value, exprs, result);
        }
        HirStmt::MultiAssign { targets, values } => {
            for t in targets {
                if let LValue::Local(var_id) = t {
                    result.insert(*var_id);
                }
            }
            for v in values {
                collect_expr_var_refs(*v, exprs, result);
            }
        }
        HirStmt::LocalDecl { var, init } => {
            result.insert(*var);
            if let Some(expr) = init {
                collect_expr_var_refs(*expr, exprs, result);
            }
        }
        HirStmt::MultiLocalDecl { vars, values } => {
            for v in vars {
                result.insert(*v);
            }
            for v in values {
                collect_expr_var_refs(*v, exprs, result);
            }
        }
        HirStmt::CompoundAssign { target, value, .. } => {
            if let LValue::Local(var_id) = target {
                result.insert(*var_id);
            }
            collect_expr_var_refs(*value, exprs, result);
        }
        HirStmt::ExprStmt(expr) => {
            collect_expr_var_refs(*expr, exprs, result);
        }
        HirStmt::Return(values) => {
            for v in values {
                collect_expr_var_refs(*v, exprs, result);
            }
        }
        HirStmt::If { condition, then_body, elseif_clauses, else_body } => {
            collect_expr_var_refs(*condition, exprs, result);
            for s in then_body {
                collect_var_refs_stmt(s, exprs, result);
            }
            for clause in elseif_clauses {
                collect_expr_var_refs(clause.condition, exprs, result);
                for s in &clause.body {
                    collect_var_refs_stmt(s, exprs, result);
                }
            }
            if let Some(else_stmts) = else_body {
                for s in else_stmts {
                    collect_var_refs_stmt(s, exprs, result);
                }
            }
        }
        HirStmt::While { condition, body } => {
            collect_expr_var_refs(*condition, exprs, result);
            for s in body {
                collect_var_refs_stmt(s, exprs, result);
            }
        }
        HirStmt::Repeat { body, condition } => {
            for s in body {
                collect_var_refs_stmt(s, exprs, result);
            }
            collect_expr_var_refs(*condition, exprs, result);
        }
        HirStmt::NumericFor { var, start, limit, step, body } => {
            result.insert(*var);
            collect_expr_var_refs(*start, exprs, result);
            collect_expr_var_refs(*limit, exprs, result);
            if let Some(s) = step {
                collect_expr_var_refs(*s, exprs, result);
            }
            for s in body {
                collect_var_refs_stmt(s, exprs, result);
            }
        }
        HirStmt::GenericFor { vars, iterators, body } => {
            for v in vars {
                result.insert(*v);
            }
            for iter in iterators {
                collect_expr_var_refs(*iter, exprs, result);
            }
            for s in body {
                collect_var_refs_stmt(s, exprs, result);
            }
        }
        HirStmt::FunctionDef { func_expr, .. } => {
            collect_expr_var_refs(*func_expr, exprs, result);
        }
        HirStmt::LocalFunctionDef { var, func_expr } => {
            result.insert(*var);
            collect_expr_var_refs(*func_expr, exprs, result);
        }
        _ => {}
    }
}

/// Recursively collect all VarId references from an expression tree.
fn collect_expr_var_refs(
    expr_id: ExprId,
    exprs: &lantern_hir::arena::ExprArena,
    result: &mut FxHashSet<VarId>,
) {
    match exprs.get(expr_id) {
        HirExpr::Var(var_id) => {
            result.insert(*var_id);
        }
        HirExpr::FieldAccess { table, .. } => {
            collect_expr_var_refs(*table, exprs, result);
        }
        HirExpr::IndexAccess { table, key } => {
            collect_expr_var_refs(*table, exprs, result);
            collect_expr_var_refs(*key, exprs, result);
        }
        HirExpr::Binary { left, right, .. } => {
            collect_expr_var_refs(*left, exprs, result);
            collect_expr_var_refs(*right, exprs, result);
        }
        HirExpr::Unary { operand, .. } => {
            collect_expr_var_refs(*operand, exprs, result);
        }
        HirExpr::Call { func, args, .. } => {
            collect_expr_var_refs(*func, exprs, result);
            for a in args {
                collect_expr_var_refs(*a, exprs, result);
            }
        }
        HirExpr::MethodCall { object, args, .. } => {
            collect_expr_var_refs(*object, exprs, result);
            for a in args {
                collect_expr_var_refs(*a, exprs, result);
            }
        }
        HirExpr::Table { array, hash } => {
            for a in array {
                collect_expr_var_refs(*a, exprs, result);
            }
            for (k, v) in hash {
                collect_expr_var_refs(*k, exprs, result);
                collect_expr_var_refs(*v, exprs, result);
            }
        }
        HirExpr::Concat(parts) => {
            for p in parts {
                collect_expr_var_refs(*p, exprs, result);
            }
        }
        HirExpr::IfExpr { condition, then_expr, else_expr } => {
            collect_expr_var_refs(*condition, exprs, result);
            collect_expr_var_refs(*then_expr, exprs, result);
            collect_expr_var_refs(*else_expr, exprs, result);
        }
        HirExpr::Select { source, .. } => {
            collect_expr_var_refs(*source, exprs, result);
        }
        HirExpr::Closure { .. } | HirExpr::Literal(_) | HirExpr::Global(_)
        | HirExpr::Upvalue(_) | HirExpr::VarArg | HirExpr::Reg(_) => {}
    }
}
