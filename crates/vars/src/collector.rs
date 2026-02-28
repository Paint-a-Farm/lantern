use lantern_hir::arena::ExprId;
use lantern_hir::cfg::Terminator;
use lantern_hir::expr::HirExpr;
use lantern_hir::func::HirFunc;
use lantern_hir::stmt::HirStmt;
use lantern_hir::var::RegRef;

/// A register access (def or use) collected from the HIR.
#[derive(Debug, Clone)]
pub struct RegAccess {
    pub reg: RegRef,
    pub is_def: bool,
    /// True if this access comes from an instruction that has an AUX word
    /// (occupying 2 PC slots). Used to correctly match scope boundaries.
    pub has_aux: bool,
    /// True if this def assigns a table constructor (Table expression).
    /// Used to enable the delayed-scope matching for table constructors.
    pub is_table_def: bool,
    /// True if this def assigns a closure (NewClosure/DupClosure).
    /// Closures are followed by CAPTURE instructions, so the scope starts
    /// several PCs after the def — further than the normal pc+1/pc+2 pattern.
    pub is_closure_def: bool,
}

/// Collect all register accesses from a function's HIR.
///
/// Walks all blocks' statements and terminators, finding every RegRef
/// in expressions and statements. RegAssign targets are defs, Reg
/// expressions are uses.
pub fn collect_accesses(func: &HirFunc) -> Vec<RegAccess> {
    let mut accesses = Vec::new();

    for node_idx in func.cfg.node_indices() {
        let block = &func.cfg[node_idx];

        for stmt in &block.stmts {
            collect_from_stmt(func, stmt, &mut accesses);
        }

        collect_from_terminator(func, &block.terminator, &mut accesses);
    }

    accesses
}

fn collect_from_stmt(func: &HirFunc, stmt: &HirStmt, out: &mut Vec<RegAccess>) {
    match stmt {
        HirStmt::RegAssign { target, value } => {
            // target is a def — propagate has_aux from the RegRef
            let is_table_def = matches!(func.exprs.get(*value), HirExpr::Table { .. });
            let is_closure_def = matches!(func.exprs.get(*value), HirExpr::Closure { .. });
            out.push(RegAccess {
                reg: *target,
                is_def: true,
                has_aux: target.has_aux,
                is_table_def,
                is_closure_def,
            });
            // value may contain uses
            collect_from_expr(func, *value, out);
        }

        HirStmt::Assign { target, value } => {
            collect_from_lvalue(func, target, out);
            collect_from_expr(func, *value, out);
        }

        HirStmt::MultiAssign { targets, values } => {
            for t in targets {
                collect_from_lvalue(func, t, out);
            }
            for v in values {
                collect_from_expr(func, *v, out);
            }
        }

        HirStmt::ExprStmt(expr) => {
            collect_from_expr(func, *expr, out);
        }

        HirStmt::CompoundAssign { target, value, .. } => {
            collect_from_lvalue(func, target, out);
            collect_from_expr(func, *value, out);
        }

        HirStmt::If {
            condition,
            then_body,
            elseif_clauses,
            else_body,
            ..
        } => {
            collect_from_expr(func, *condition, out);
            for s in then_body {
                collect_from_stmt(func, s, out);
            }
            for clause in elseif_clauses {
                collect_from_expr(func, clause.condition, out);
                for s in &clause.body {
                    collect_from_stmt(func, s, out);
                }
            }
            if let Some(body) = else_body {
                for s in body {
                    collect_from_stmt(func, s, out);
                }
            }
        }

        HirStmt::While { condition, body } => {
            collect_from_expr(func, *condition, out);
            for s in body {
                collect_from_stmt(func, s, out);
            }
        }

        HirStmt::Repeat { body, condition } => {
            for s in body {
                collect_from_stmt(func, s, out);
            }
            collect_from_expr(func, *condition, out);
        }

        HirStmt::NumericFor {
            start,
            limit,
            step,
            body,
            ..
        } => {
            collect_from_expr(func, *start, out);
            collect_from_expr(func, *limit, out);
            if let Some(s) = step {
                collect_from_expr(func, *s, out);
            }
            for s in body {
                collect_from_stmt(func, s, out);
            }
        }

        HirStmt::GenericFor {
            iterators, body, ..
        } => {
            for iter in iterators {
                collect_from_expr(func, *iter, out);
            }
            for s in body {
                collect_from_stmt(func, s, out);
            }
        }

        HirStmt::Return(values) => {
            for v in values {
                collect_from_expr(func, *v, out);
            }
        }

        HirStmt::LocalDecl { init, .. } => {
            if let Some(expr) = init {
                collect_from_expr(func, *expr, out);
            }
        }

        HirStmt::MultiLocalDecl { values, .. } => {
            for v in values {
                collect_from_expr(func, *v, out);
            }
        }

        HirStmt::FunctionDef { func_expr, .. } | HirStmt::LocalFunctionDef { func_expr, .. } => {
            collect_from_expr(func, *func_expr, out);
        }

        HirStmt::Break | HirStmt::Continue | HirStmt::CloseUpvals { .. } => {}
    }
}

fn collect_from_terminator(func: &HirFunc, term: &Terminator, out: &mut Vec<RegAccess>) {
    match term {
        Terminator::Branch { condition, .. } => {
            collect_from_expr(func, *condition, out);
        }
        Terminator::Return(values) => {
            for v in values {
                collect_from_expr(func, *v, out);
            }
        }
        Terminator::ForNumPrep {
            start, limit, step, ..
        } => {
            collect_from_expr(func, *start, out);
            collect_from_expr(func, *limit, out);
            if let Some(s) = step {
                collect_from_expr(func, *s, out);
            }
        }
        Terminator::ForNumBack { .. } => {}
        Terminator::ForGenBack { iterators, .. } => {
            for iter in iterators {
                collect_from_expr(func, *iter, out);
            }
        }
        Terminator::None | Terminator::Jump => {}
    }
}

fn collect_from_expr(func: &HirFunc, expr_id: ExprId, out: &mut Vec<RegAccess>) {
    match func.exprs.get(expr_id) {
        HirExpr::Reg(reg) => {
            out.push(RegAccess {
                reg: *reg,
                is_def: false,
                has_aux: reg.has_aux,
                is_table_def: false,
                is_closure_def: false,
            });
        }
        HirExpr::FieldAccess { table, .. } => {
            collect_from_expr(func, *table, out);
        }
        HirExpr::IndexAccess { table, key } => {
            collect_from_expr(func, *table, out);
            collect_from_expr(func, *key, out);
        }
        HirExpr::Binary { left, right, .. } => {
            collect_from_expr(func, *left, out);
            collect_from_expr(func, *right, out);
        }
        HirExpr::Unary { operand, .. } => {
            collect_from_expr(func, *operand, out);
        }
        HirExpr::Call { func: f, args, .. } => {
            collect_from_expr(func, *f, out);
            for a in args {
                collect_from_expr(func, *a, out);
            }
        }
        HirExpr::MethodCall { object, args, .. } => {
            collect_from_expr(func, *object, out);
            for a in args {
                collect_from_expr(func, *a, out);
            }
        }
        HirExpr::Table { array, hash, .. } => {
            for a in array {
                collect_from_expr(func, *a, out);
            }
            for (k, v) in hash {
                collect_from_expr(func, *k, out);
                collect_from_expr(func, *v, out);
            }
        }
        HirExpr::Concat(operands) => {
            for o in operands {
                collect_from_expr(func, *o, out);
            }
        }
        HirExpr::IfExpr {
            condition,
            then_expr,
            else_expr,
        } => {
            collect_from_expr(func, *condition, out);
            collect_from_expr(func, *then_expr, out);
            collect_from_expr(func, *else_expr, out);
        }
        HirExpr::Select { source, .. } => {
            collect_from_expr(func, *source, out);
        }
        HirExpr::Closure { captures, .. } => {
            for cap in captures {
                if let lantern_hir::expr::CaptureSource::Register(reg) = &cap.source {
                    out.push(RegAccess {
                        reg: *reg,
                        is_def: false,
                        has_aux: reg.has_aux,
                        is_table_def: false,
                        is_closure_def: false,
                    });
                }
            }
        }
        // No register refs in these
        HirExpr::Var(_)
        | HirExpr::Literal(_)
        | HirExpr::Global(_)
        | HirExpr::Upvalue(_)
        | HirExpr::VarArg => {}
    }
}

fn collect_from_lvalue(func: &HirFunc, lv: &lantern_hir::stmt::LValue, out: &mut Vec<RegAccess>) {
    match lv {
        lantern_hir::stmt::LValue::Field { table, .. } => {
            collect_from_expr(func, *table, out);
        }
        lantern_hir::stmt::LValue::Index { table, key } => {
            collect_from_expr(func, *table, out);
            collect_from_expr(func, *key, out);
        }
        _ => {}
    }
}
