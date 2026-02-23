use std::fmt::Write;

use petgraph::stable_graph::NodeIndex;
use petgraph::visit::EdgeRef;

use lantern_hir::arena::ExprId;
use lantern_hir::cfg::{EdgeKind, Terminator};
use lantern_hir::expr::HirExpr;
use lantern_hir::stmt::{ElseIfClause, HirStmt, LValue};
use lantern_hir::types::{BinOp, LuaValue};

use super::precedence::binop_str;
use super::LuaEmitter;

impl<'a> LuaEmitter<'a> {
    pub(super) fn emit_stmts(&mut self, stmts: &[HirStmt]) {
        for stmt in stmts {
            self.emit_stmt(stmt);
        }
    }

    pub(super) fn emit_unstructured(&mut self) {
        // Collect blocks sorted by PC start
        let mut blocks: Vec<_> = self
            .func
            .cfg
            .node_indices()
            .map(|idx| (idx, self.func.cfg[idx].pc_range))
            .collect();
        blocks.sort_by_key(|(_, (start, _))| *start);

        for (node_idx, (start_pc, _end_pc)) in &blocks {
            // Block label
            self.write_indent();
            let _ = writeln!(
                self.output,
                "-- block_{} (pc {})",
                node_idx.index(),
                start_pc
            );

            let block = &self.func.cfg[*node_idx];

            // Emit statements
            for stmt in &block.stmts {
                self.emit_stmt(stmt);
            }

            // Emit terminator
            self.emit_terminator(&block.terminator, *node_idx);
        }
    }

    pub(super) fn emit_stmt(&mut self, stmt: &HirStmt) {
        match stmt {
            HirStmt::LocalDecl { var, init } => {
                self.declared.insert(*var);
                self.write_indent();
                let name = self.var_name(*var);
                match init {
                    Some(expr) => {
                        let _ = write!(self.output, "local {} = ", name);
                        self.emit_expr(*expr);
                        self.output.push('\n');
                    }
                    None => {
                        let _ = writeln!(self.output, "local {}", name);
                    }
                }
            }

            HirStmt::MultiLocalDecl { vars, values } => {
                self.write_indent();
                self.output.push_str("local ");
                for (i, var) in vars.iter().enumerate() {
                    if i > 0 {
                        self.output.push_str(", ");
                    }
                    self.declared.insert(*var);
                    self.output.push_str(&self.var_name(*var));
                }
                if !values.is_empty() {
                    self.output.push_str(" = ");
                    for (i, val) in values.iter().enumerate() {
                        if i > 0 {
                            self.output.push_str(", ");
                        }
                        self.emit_expr(*val);
                    }
                }
                self.output.push('\n');
            }

            HirStmt::Assign { target, value } => {
                // Check if this is a function definition pattern:
                // X.Y = function(self, ...) → function X:Y(...)
                // X.Y = function(...)       → function X.Y(...)
                if self.try_emit_func_def(target, *value) {
                    return;
                }

                self.write_indent();
                // Assign { Local } means "assign to a local variable".
                // If we haven't yet emitted a `local` for this var (it wasn't
                // declared by a LocalDecl node earlier in scope), emit it now.
                if let LValue::Local(var_id) = target {
                    if self.declared.insert(*var_id) {
                        self.output.push_str("local ");
                    }
                }
                self.emit_lvalue(target);
                self.output.push_str(" = ");
                self.emit_expr(*value);
                self.output.push('\n');
            }

            HirStmt::MultiAssign { targets, values } => {
                self.write_indent();
                for (i, t) in targets.iter().enumerate() {
                    if i > 0 {
                        self.output.push_str(", ");
                    }
                    self.emit_lvalue(t);
                }
                self.output.push_str(" = ");
                for (i, v) in values.iter().enumerate() {
                    if i > 0 {
                        self.output.push_str(", ");
                    }
                    self.emit_expr(*v);
                }
                self.output.push('\n');
            }

            HirStmt::CompoundAssign { op, target, value } => {
                self.write_indent();
                self.emit_lvalue(target);
                let _ = write!(self.output, " {}= ", binop_str(*op));
                self.emit_expr(*value);
                self.output.push('\n');
            }

            HirStmt::ExprStmt(expr) => {
                self.emit_expr_stmt(*expr);
            }

            HirStmt::Return(values) => {
                self.write_indent();
                self.output.push_str("return");
                for (i, v) in values.iter().enumerate() {
                    if i == 0 {
                        self.output.push(' ');
                    } else {
                        self.output.push_str(", ");
                    }
                    self.emit_expr(*v);
                }
                self.output.push('\n');
            }

            HirStmt::If {
                condition,
                then_body,
                elseif_clauses,
                else_body,
            } => {
                self.write_indent();
                self.output.push_str("if ");
                self.emit_expr(*condition);
                self.output.push_str(" then\n");
                self.indent += 1;
                self.emit_stmts(then_body);
                self.indent -= 1;
                for clause in elseif_clauses {
                    self.emit_elseif(clause);
                }
                if let Some(else_stmts) = else_body {
                    self.write_indent();
                    self.output.push_str("else\n");
                    self.indent += 1;
                    self.emit_stmts(else_stmts);
                    self.indent -= 1;
                }
                self.write_indent();
                self.output.push_str("end\n");
            }

            HirStmt::While { condition, body } => {
                self.write_indent();
                self.output.push_str("while ");
                self.emit_expr(*condition);
                self.output.push_str(" do\n");
                self.indent += 1;
                self.emit_stmts(body);
                self.indent -= 1;
                self.write_indent();
                self.output.push_str("end\n");
            }

            HirStmt::Repeat { body, condition } => {
                self.write_indent();
                self.output.push_str("repeat\n");
                self.indent += 1;
                self.emit_stmts(body);
                self.indent -= 1;
                self.write_indent();
                self.output.push_str("until ");
                self.emit_expr(*condition);
                self.output.push('\n');
            }

            HirStmt::NumericFor {
                var,
                start,
                limit,
                step,
                body,
            } => {
                self.write_indent();
                let name = self.var_name(*var);
                let _ = write!(self.output, "for {} = ", name);
                self.emit_expr(*start);
                self.output.push_str(", ");
                self.emit_expr(*limit);
                if let Some(step_expr) = step {
                    // Omit step when it's the default value of 1
                    let is_default_step = matches!(
                        self.func.exprs.get(*step_expr),
                        HirExpr::Literal(LuaValue::Number(n)) if *n == 1.0
                    );
                    if !is_default_step {
                        self.output.push_str(", ");
                        self.emit_expr(*step_expr);
                    }
                }
                self.output.push_str(" do\n");
                self.indent += 1;
                self.emit_stmts(body);
                self.indent -= 1;
                self.write_indent();
                self.output.push_str("end\n");
            }

            HirStmt::GenericFor {
                vars,
                iterators,
                body,
            } => {
                self.write_indent();
                self.output.push_str("for ");
                for (i, v) in vars.iter().enumerate() {
                    if i > 0 {
                        self.output.push_str(", ");
                    }
                    self.output.push_str(&self.var_name(*v));
                }
                self.output.push_str(" in ");
                for (i, iter) in iterators.iter().enumerate() {
                    if i > 0 {
                        self.output.push_str(", ");
                    }
                    self.emit_expr(*iter);
                }
                self.output.push_str(" do\n");
                self.indent += 1;
                self.emit_stmts(body);
                self.indent -= 1;
                self.write_indent();
                self.output.push_str("end\n");
            }

            HirStmt::Break => {
                self.write_indent();
                self.output.push_str("break\n");
            }

            HirStmt::Continue => {
                self.write_indent();
                self.output.push_str("continue\n");
            }

            HirStmt::FunctionDef { name, func_expr } => {
                self.write_indent();
                self.output.push_str("function ");
                self.emit_lvalue(name);
                // The closure will emit (...) body end
                self.emit_closure_body(*func_expr);
                self.output.push('\n');
            }

            HirStmt::LocalFunctionDef { var, func_expr } => {
                self.write_indent();
                let name = self.var_name(*var);
                let _ = write!(self.output, "local function {}", name);
                self.emit_closure_body(*func_expr);
                self.output.push('\n');
            }

            HirStmt::CloseUpvals { .. } => {
                // Internal — skip in output
            }

            HirStmt::RegAssign { target, value } => {
                self.write_indent();
                let _ = write!(self.output, "r{}_{} = ", target.register, target.pc);
                self.emit_expr(*value);
                self.output.push('\n');
            }
        }
    }

    /// Try to emit `target = closure` as a function definition.
    ///
    /// Detects patterns like:
    ///   `X.Y = function(self, ...)` -> `function X:Y(...)`
    ///   `X.Y = function(...)` -> `function X.Y(...)`
    ///
    /// Returns true if the statement was handled as a function definition.
    pub(super) fn try_emit_func_def(&mut self, target: &LValue, value: ExprId) -> bool {
        let ctx = match self.file_ctx {
            Some(ctx) => ctx,
            None => return false,
        };

        // Check if value is a Closure expression
        let (proto_id, _captures) = match self.func.exprs.get(value) {
            HirExpr::Closure { proto_id, captures } => (*proto_id, captures.clone()),
            _ => return false,
        };

        // Resolve proto_id to bytecode function index, then to HirFunc
        let child_protos = match ctx.child_protos.get(self.func.proto_index) {
            Some(cp) => cp,
            None => return false,
        };
        let bc_func_idx = match child_protos.get(proto_id) {
            Some(&idx) => idx,
            None => return false,
        };
        let child_func = match ctx.funcs.get(bc_func_idx) {
            Some(f) => f,
            None => return false,
        };

        // Build the qualified name and prefix from the assignment target
        let (qualified_name, prefix) = match target {
            LValue::Field { table, field } => {
                // Check if child's first param is "self"
                let has_self = child_func.params.first().map_or(false, |p| {
                    child_func.vars.get(*p).name.as_deref() == Some("self")
                });
                let separator = if has_self { ":" } else { "." };
                let table_str = match self.expr_to_string(*table) {
                    Some(s) => s,
                    None => return false, // Can't form valid qualified name
                };
                // Lua syntax forbids bracket indexing in function definition paths:
                // `function a.b[3].c() end` is invalid, must use assignment form instead.
                if table_str.contains('[') {
                    return false;
                }
                (format!("{}{}{}", table_str, separator, field), "")
            }
            LValue::Global(name) => (name.clone(), ""),
            LValue::Local(var_id) => {
                let name = self.var_name(*var_id);
                let prefix = if self.declared.contains(var_id) {
                    ""
                } else {
                    "local "
                };
                (name, prefix)
            }
            _ => return false,
        };

        // Emit as function definition
        self.write_indent();
        self.output.push_str(prefix);
        let mut child_emitter = LuaEmitter::new(child_func, self.file_ctx);
        child_emitter.indent = self.indent;
        child_emitter.emit_signature(Some(&qualified_name));
        child_emitter.indent += 1;
        child_emitter.emit_body();
        child_emitter.indent -= 1;
        child_emitter.write_indent();
        child_emitter.output.push_str("end\n");
        self.output.push_str(&child_emitter.output);

        true
    }

    pub(super) fn emit_elseif(&mut self, clause: &ElseIfClause) {
        self.write_indent();
        self.output.push_str("elseif ");
        self.emit_expr(clause.condition);
        self.output.push_str(" then\n");
        self.indent += 1;
        self.emit_stmts(&clause.body);
        self.indent -= 1;
    }

    /// Emit an expression used as a statement.
    ///
    /// Converts `and`/`or` expressions into `if` statements since Luau only
    /// allows function calls as expression statements.
    ///
    /// Patterns:
    ///   `a and b`         → `if a then <b> end`
    ///   `a or b`          → `if not a then <b> end`
    ///   `a and b or c`    → `if a then <b> else <c> end`
    ///   `Call(Closure, ..)` → `(function() ... end)(args)` (IIFE needs parens)
    fn emit_expr_stmt(&mut self, expr: ExprId) {
        match self.func.exprs.get(expr) {
            HirExpr::Binary {
                op: BinOp::Or,
                left,
                right,
            } => {
                let (left, right) = (*left, *right);
                // Check for ternary: `(a and b) or c`
                //
                // When used as a statement, only `c` has side effects — `a` and `b`
                // are just conditions. The Luau compiler generates this from:
                //   `if not a or not b then c() end`
                // So we emit: `if not (a and b) then c end`
                //
                // Only decompose as if/then/else when BOTH branches are calls
                // (i.e., both have side effects worth executing).
                if let HirExpr::Binary {
                    op: BinOp::And,
                    left: cond,
                    right: then_expr,
                } = self.func.exprs.get(left)
                {
                    let (cond, then_expr) = (*cond, *then_expr);
                    let then_is_call = self.expr_is_call_like(then_expr);
                    let else_is_call = self.expr_is_call_like(right);

                    if then_is_call && else_is_call {
                        // Both branches are calls: `if a then call1() else call2() end`
                        self.write_indent();
                        self.output.push_str("if ");
                        self.emit_expr(cond);
                        self.output.push_str(" then\n");
                        self.indent += 1;
                        self.emit_expr_stmt(then_expr);
                        self.indent -= 1;
                        self.write_indent();
                        self.output.push_str("else\n");
                        self.indent += 1;
                        self.emit_expr_stmt(right);
                        self.indent -= 1;
                        self.write_indent();
                        self.output.push_str("end\n");
                    } else if then_is_call {
                        // Only then-branch is a call: `if a then call() end`
                        // `b` was the condition for `c`, drop the else
                        self.write_indent();
                        self.output.push_str("if ");
                        self.emit_expr(cond);
                        self.output.push_str(" then\n");
                        self.indent += 1;
                        self.emit_expr_stmt(then_expr);
                        self.indent -= 1;
                        self.write_indent();
                        self.output.push_str("end\n");
                    } else {
                        // then-branch is not a call (it's a condition check):
                        // `(a and b) or c` → `if not (a and b) then c end`
                        self.write_indent();
                        self.output.push_str("if not (");
                        self.emit_expr(cond);
                        self.output.push_str(" and ");
                        self.emit_expr(then_expr);
                        self.output.push_str(") then\n");
                        self.indent += 1;
                        self.emit_expr_stmt(right);
                        self.indent -= 1;
                        self.write_indent();
                        self.output.push_str("end\n");
                    }
                } else {
                    // `a or b` → `if not a then b end`
                    self.write_indent();
                    self.output.push_str("if not ");
                    self.emit_expr_parens(left, super::precedence::Precedence::UNARY);
                    self.output.push_str(" then\n");
                    self.indent += 1;
                    self.emit_expr_stmt(right);
                    self.indent -= 1;
                    self.write_indent();
                    self.output.push_str("end\n");
                }
            }
            HirExpr::Binary {
                op: BinOp::And,
                left,
                right,
            } => {
                let (left, right) = (*left, *right);
                self.write_indent();
                self.output.push_str("if ");
                self.emit_expr(left);
                self.output.push_str(" then\n");
                self.indent += 1;
                self.emit_expr_stmt(right);
                self.indent -= 1;
                self.write_indent();
                self.output.push_str("end\n");
            }
            _ => {
                // Regular expression statement (function call, etc.)
                // Non-call expressions here indicate an upstream issue (lost assignment
                // target from ternary decomposition), but we emit them as-is to
                // preserve semantic information.
                self.write_indent();
                self.emit_expr(expr);
                self.output.push('\n');
            }
        }
    }

    /// Check if an expression is a call (or contains one through And/Or chains).
    fn expr_is_call_like(&self, expr: ExprId) -> bool {
        match self.func.exprs.get(expr) {
            HirExpr::Call { .. } | HirExpr::MethodCall { .. } => true,
            HirExpr::Binary {
                op: BinOp::And,
                right,
                ..
            }
            | HirExpr::Binary {
                op: BinOp::Or,
                right,
                ..
            } => self.expr_is_call_like(*right),
            _ => false,
        }
    }

    pub(super) fn emit_lvalue(&mut self, lv: &LValue) {
        match lv {
            LValue::Local(var_id) => {
                self.output.push_str(&self.var_name(*var_id));
            }
            LValue::Global(name) => {
                self.output.push_str(name);
            }
            LValue::Field { table, field } => {
                self.emit_expr_parens(*table, super::precedence::Precedence::POSTFIX);
                self.output.push('.');
                self.output.push_str(field);
            }
            LValue::Index { table, key } => {
                self.emit_expr_parens(*table, super::precedence::Precedence::POSTFIX);
                self.output.push('[');
                self.emit_expr(*key);
                self.output.push(']');
            }
            LValue::Upvalue(slot) => {
                if let Some(Some(name)) = self.func.upvalue_names.get(*slot as usize) {
                    self.output.push_str(name);
                } else {
                    let _ = write!(self.output, "upval_{}", slot);
                }
            }
        }
    }

    pub(super) fn emit_terminator(&mut self, terminator: &Terminator, node_idx: NodeIndex) {
        match terminator {
            Terminator::None => {}

            Terminator::Jump => {
                let target = self.func.cfg.edges(node_idx).next().map(|e| e.target());
                if let Some(t) = target {
                    self.write_indent();
                    let _ = writeln!(self.output, "goto block_{}", t.index());
                }
            }

            Terminator::Branch { condition } => {
                // Find then/else edges
                let mut then_target = None;
                let mut else_target = None;
                for e in self.func.cfg.edges(node_idx) {
                    match e.weight().kind {
                        EdgeKind::Then | EdgeKind::LoopBack => then_target = Some(e.target()),
                        EdgeKind::Else | EdgeKind::LoopExit => else_target = Some(e.target()),
                        EdgeKind::Unconditional => {
                            if then_target.is_none() {
                                then_target = Some(e.target());
                            } else {
                                else_target = Some(e.target());
                            }
                        }
                    }
                }

                self.write_indent();
                self.output.push_str("if ");
                self.emit_expr(*condition);
                self.output.push_str(" then goto ");
                if let Some(t) = then_target {
                    let _ = write!(self.output, "block_{}", t.index());
                }
                self.output.push_str(" else goto ");
                if let Some(e) = else_target {
                    let _ = write!(self.output, "block_{}", e.index());
                }
                self.output.push('\n');
            }

            Terminator::Return(values) => {
                self.write_indent();
                self.output.push_str("return");
                for (i, v) in values.iter().enumerate() {
                    if i == 0 {
                        self.output.push(' ');
                    } else {
                        self.output.push_str(", ");
                    }
                    self.emit_expr(*v);
                }
                self.output.push('\n');
            }

            Terminator::ForNumPrep { .. }
            | Terminator::ForNumBack { .. }
            | Terminator::ForGenBack { .. } => {
                // For-loop terminators are handled by the structurer.
                // If we reach here, the function wasn't structured.
                self.write_indent();
                self.output.push_str("-- for loop (unstructured)\n");
            }
        }
    }
}
