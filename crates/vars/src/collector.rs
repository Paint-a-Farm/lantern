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
    /// The PC range of the basic block containing this access.
    /// Used to distinguish sequential register reuse (same block) from
    /// parallel branch writes (different blocks).
    pub block_pc_range: (usize, usize),
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
        let block_pc = block.pc_range;

        for stmt in &block.stmts {
            collect_from_stmt(func, stmt, block_pc, &mut accesses);
        }

        collect_from_terminator(func, &block.terminator, block_pc, &mut accesses);
    }

    accesses
}

fn collect_from_stmt(func: &HirFunc, stmt: &HirStmt, block_pc: (usize, usize), out: &mut Vec<RegAccess>) {
    match stmt {
        HirStmt::RegAssign { target, value } => {
            // target is a def — propagate has_aux from the RegRef
            let is_table_def = matches!(func.exprs.get(*value), HirExpr::Table { .. });
            out.push(RegAccess {
                reg: *target,
                is_def: true,
                has_aux: target.has_aux,
                is_table_def,
                block_pc_range: block_pc,
            });
            // value may contain uses
            collect_from_expr(func, *value, block_pc, out);
        }

        HirStmt::Assign { target, value } => {
            collect_from_lvalue(func, target, block_pc, out);
            collect_from_expr(func, *value, block_pc, out);
        }

        HirStmt::MultiAssign { targets, values } => {
            for t in targets {
                collect_from_lvalue(func, t, block_pc, out);
            }
            for v in values {
                collect_from_expr(func, *v, block_pc, out);
            }
        }

        HirStmt::ExprStmt(expr) => {
            collect_from_expr(func, *expr, block_pc, out);
        }

        HirStmt::CompoundAssign { target, value, .. } => {
            collect_from_lvalue(func, target, block_pc, out);
            collect_from_expr(func, *value, block_pc, out);
        }

        HirStmt::If {
            condition,
            then_body,
            elseif_clauses,
            else_body,
        } => {
            collect_from_expr(func, *condition, block_pc, out);
            for s in then_body {
                collect_from_stmt(func, s, block_pc, out);
            }
            for clause in elseif_clauses {
                collect_from_expr(func, clause.condition, block_pc, out);
                for s in &clause.body {
                    collect_from_stmt(func, s, block_pc, out);
                }
            }
            if let Some(body) = else_body {
                for s in body {
                    collect_from_stmt(func, s, block_pc, out);
                }
            }
        }

        HirStmt::While { condition, body } => {
            collect_from_expr(func, *condition, block_pc, out);
            for s in body {
                collect_from_stmt(func, s, block_pc, out);
            }
        }

        HirStmt::Repeat { body, condition } => {
            for s in body {
                collect_from_stmt(func, s, block_pc, out);
            }
            collect_from_expr(func, *condition, block_pc, out);
        }

        HirStmt::NumericFor {
            start,
            limit,
            step,
            body,
            ..
        } => {
            collect_from_expr(func, *start, block_pc, out);
            collect_from_expr(func, *limit, block_pc, out);
            if let Some(s) = step {
                collect_from_expr(func, *s, block_pc, out);
            }
            for s in body {
                collect_from_stmt(func, s, block_pc, out);
            }
        }

        HirStmt::GenericFor {
            iterators, body, ..
        } => {
            for iter in iterators {
                collect_from_expr(func, *iter, block_pc, out);
            }
            for s in body {
                collect_from_stmt(func, s, block_pc, out);
            }
        }

        HirStmt::Return(values) => {
            for v in values {
                collect_from_expr(func, *v, block_pc, out);
            }
        }

        HirStmt::LocalDecl { init, .. } => {
            if let Some(expr) = init {
                collect_from_expr(func, *expr, block_pc, out);
            }
        }

        HirStmt::MultiLocalDecl { values, .. } => {
            for v in values {
                collect_from_expr(func, *v, block_pc, out);
            }
        }

        HirStmt::FunctionDef { func_expr, .. }
        | HirStmt::LocalFunctionDef { func_expr, .. } => {
            collect_from_expr(func, *func_expr, block_pc, out);
        }

        HirStmt::Break | HirStmt::Continue | HirStmt::CloseUpvals { .. } => {}
    }
}

fn collect_from_terminator(func: &HirFunc, term: &Terminator, block_pc: (usize, usize), out: &mut Vec<RegAccess>) {
    match term {
        Terminator::Branch { condition } => {
            collect_from_expr(func, *condition, block_pc, out);
        }
        Terminator::Return(values) => {
            for v in values {
                collect_from_expr(func, *v, block_pc, out);
            }
        }
        Terminator::ForNumPrep { start, limit, step, .. } => {
            // The for-loop expressions are uses of registers loaded before FORNPREP.
            // Loop variable names are resolved during lifting and stored in the
            // terminator — no register def needed here for naming.
            collect_from_expr(func, *start, block_pc, out);
            collect_from_expr(func, *limit, block_pc, out);
            if let Some(s) = step {
                collect_from_expr(func, *s, block_pc, out);
            }
        }
        Terminator::ForNumBack { .. } => {}
        Terminator::ForGenBack { iterators, .. } => {
            for iter in iterators {
                collect_from_expr(func, *iter, block_pc, out);
            }
        }
        Terminator::None | Terminator::Jump => {}
    }
}

fn collect_from_expr(func: &HirFunc, expr_id: ExprId, block_pc: (usize, usize), out: &mut Vec<RegAccess>) {
    match func.exprs.get(expr_id) {
        HirExpr::Reg(reg) => {
            out.push(RegAccess {
                reg: *reg,
                is_def: false,
                has_aux: reg.has_aux,
                is_table_def: false,
                block_pc_range: block_pc,
            });
        }
        HirExpr::FieldAccess { table, .. } => {
            collect_from_expr(func, *table, block_pc, out);
        }
        HirExpr::IndexAccess { table, key } => {
            collect_from_expr(func, *table, block_pc, out);
            collect_from_expr(func, *key, block_pc, out);
        }
        HirExpr::Binary { left, right, .. } => {
            collect_from_expr(func, *left, block_pc, out);
            collect_from_expr(func, *right, block_pc, out);
        }
        HirExpr::Unary { operand, .. } => {
            collect_from_expr(func, *operand, block_pc, out);
        }
        HirExpr::Call { func: f, args, .. } => {
            collect_from_expr(func, *f, block_pc, out);
            for a in args {
                collect_from_expr(func, *a, block_pc, out);
            }
        }
        HirExpr::MethodCall { object, args, .. } => {
            collect_from_expr(func, *object, block_pc, out);
            for a in args {
                collect_from_expr(func, *a, block_pc, out);
            }
        }
        HirExpr::Table { array, hash } => {
            for a in array {
                collect_from_expr(func, *a, block_pc, out);
            }
            for (k, v) in hash {
                collect_from_expr(func, *k, block_pc, out);
                collect_from_expr(func, *v, block_pc, out);
            }
        }
        HirExpr::Concat(operands) => {
            for o in operands {
                collect_from_expr(func, *o, block_pc, out);
            }
        }
        HirExpr::IfExpr {
            condition,
            then_expr,
            else_expr,
        } => {
            collect_from_expr(func, *condition, block_pc, out);
            collect_from_expr(func, *then_expr, block_pc, out);
            collect_from_expr(func, *else_expr, block_pc, out);
        }
        HirExpr::Select { source, .. } => {
            collect_from_expr(func, *source, block_pc, out);
        }
        HirExpr::Closure { captures, .. } => {
            for cap in captures {
                if let lantern_hir::expr::CaptureSource::Register(reg) = &cap.source {
                    out.push(RegAccess {
                        reg: *reg,
                        is_def: false,
                        has_aux: reg.has_aux,
                        is_table_def: false,
                        block_pc_range: block_pc,
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

fn collect_from_lvalue(func: &HirFunc, lv: &lantern_hir::stmt::LValue, block_pc: (usize, usize), out: &mut Vec<RegAccess>) {
    match lv {
        lantern_hir::stmt::LValue::Field { table, .. } => {
            collect_from_expr(func, *table, block_pc, out);
        }
        lantern_hir::stmt::LValue::Index { table, key } => {
            collect_from_expr(func, *table, block_pc, out);
            collect_from_expr(func, *key, block_pc, out);
        }
        _ => {}
    }
}
