use std::fmt::Write;

use petgraph::stable_graph::NodeIndex;
use petgraph::visit::EdgeRef;

use lantern_hir::arena::ExprId;
use lantern_hir::cfg::{EdgeKind, Terminator};
use lantern_hir::expr::HirExpr;
use lantern_hir::func::HirFunc;
use lantern_hir::stmt::{ElseIfClause, HirStmt, LValue};
use lantern_hir::types::{BinOp, LuaValue, UnOp};
use lantern_hir::var::VarId;

use rustc_hash::FxHashSet;

use crate::type_info;

/// Context for whole-file emission.
/// Maps child proto indices to their lifted HirFuncs.
pub struct FileContext<'a> {
    /// All HirFuncs in the chunk, indexed by bytecode function index.
    pub funcs: &'a [HirFunc],
    /// For each bytecode function, its child_protos table.
    /// child_protos[func_index][local_proto_id] = global bytecode func index.
    pub child_protos: &'a [Vec<usize>],
}

/// Emit a single function to Lua source text including signature.
pub fn emit_function(func: &HirFunc) -> String {
    let mut emitter = LuaEmitter::new(func, None);
    emitter.emit_with_signature();
    emitter.output
}

/// Emit a whole file: the main function's body as top-level statements,
/// with closures emitted inline and `X.Y = function(self, ...)` converted
/// to `function X:Y(...)`.
pub fn emit_file(funcs: &[HirFunc], child_protos: &[Vec<usize>], main_index: usize) -> String {
    let ctx = FileContext {
        funcs,
        child_protos,
    };

    let main_func = &funcs[main_index];
    let mut emitter = LuaEmitter::new(main_func, Some(&ctx));

    // The main function's body IS the top-level code.
    // Emit it without a function wrapper.
    if main_func.structured {
        let entry = main_func.entry;
        for stmt in &main_func.cfg[entry].stmts {
            emitter.emit_stmt(stmt);
        }
    }

    emitter.output
}

pub struct LuaEmitter<'a> {
    func: &'a HirFunc,
    pub output: String,
    indent: usize,
    /// Track which local variables have been declared (emitted with `local`).
    /// Pre-populated with parameters and for-loop variables.
    declared: FxHashSet<VarId>,
    /// File context for resolving closures to child HirFuncs.
    file_ctx: Option<&'a FileContext<'a>>,
}

impl<'a> LuaEmitter<'a> {
    pub fn new(func: &'a HirFunc, file_ctx: Option<&'a FileContext<'a>>) -> Self {
        // Pre-declare parameters and loop variables
        let mut declared = FxHashSet::default();
        for (var_id, info) in func.vars.iter() {
            if info.is_param || info.is_loop_var {
                declared.insert(var_id);
            }
        }

        Self {
            func,
            output: String::new(),
            indent: 0,
            declared,
            file_ctx,
        }
    }

    /// Emit the full function definition including signature and `end`.
    pub fn emit_with_signature(&mut self) {
        self.emit_signature(None);
        self.indent += 1;
        self.emit_body();
        self.indent -= 1;
        self.output.push_str("end\n");
    }

    /// Emit just the function body (no signature/end wrapper).
    pub fn emit_body(&mut self) {
        if self.func.structured {
            let entry = self.func.entry;
            let stmts = &self.func.cfg[entry].stmts;
            for (i, stmt) in stmts.iter().enumerate() {
                // Skip trailing bare return (implicit in Lua)
                if i == stmts.len() - 1 {
                    if let HirStmt::Return(values) = stmt {
                        if values.is_empty() {
                            continue;
                        }
                    }
                }
                self.emit_stmt(stmt);
            }
        } else {
            self.emit_unstructured();
        }
    }

    /// Emit the function signature.
    ///
    /// If `qualified_name` is provided, it overrides the function's debug name
    /// (used for `function ClassName:methodName(...)` emission).
    fn emit_signature(&mut self, qualified_name: Option<&str>) {
        let type_info = type_info::decode_param_types(&self.func.type_info);

        // Check if first param is "self" — if so, this is a method
        let has_self = self.func.params.first().map_or(false, |p| {
            self.func.vars.get(*p).name.as_deref() == Some("self")
        });

        self.output.push_str("function");

        // Function name
        let name = qualified_name.map(|s| s.to_string()).or_else(|| self.func.name.clone());
        if let Some(name) = &name {
            self.output.push(' ');
            self.output.push_str(name);
        }

        self.output.push('(');

        // Parameters: skip "self" for method notation (it's implicit with `:`)
        let param_start = if has_self { 1 } else { 0 };
        let params = &self.func.params[param_start..];

        for (i, var_id) in params.iter().enumerate() {
            if i > 0 {
                self.output.push_str(", ");
            }

            let name = self.var_name(*var_id);
            self.output.push_str(&name);

            // Type annotation from type_info (offset by param_start since we may skip self)
            if let Some(ref ti) = type_info {
                let type_index = param_start + i;
                if let Some(type_str) = ti.param_types.get(type_index) {
                    if !type_str.is_empty() {
                        let _ = write!(self.output, ": {}", type_str);
                    }
                }
            }
        }

        if self.func.is_vararg {
            if !params.is_empty() {
                self.output.push_str(", ");
            }
            self.output.push_str("...");
        }

        self.output.push_str(")\n");
    }

    fn emit_unstructured(&mut self) {
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
            let _ = writeln!(self.output, "-- block_{} (pc {})", node_idx.index(), start_pc);

            let block = &self.func.cfg[*node_idx];

            // Emit statements
            for stmt in &block.stmts {
                self.emit_stmt(stmt);
            }

            // Emit terminator
            self.emit_terminator(&block.terminator, *node_idx);
        }
    }

    fn emit_stmt(&mut self, stmt: &HirStmt) {
        match stmt {
            HirStmt::LocalDecl { var, init } => {
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
                // If all targets are undeclared locals, emit as `local a, b = ...`
                let all_new_locals = targets.iter().all(|t| {
                    matches!(t, LValue::Local(v) if !self.declared.contains(v))
                });
                if all_new_locals {
                    self.output.push_str("local ");
                    for t in targets {
                        if let LValue::Local(v) = t {
                            self.declared.insert(*v);
                        }
                    }
                }
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
                self.write_indent();
                self.emit_expr(*expr);
                self.output.push('\n');
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
                // Hoist local declarations for variables that are first-assigned
                // inside one branch but used in another branch or after the if.
                self.hoist_branch_locals(then_body, elseif_clauses, else_body.as_deref());

                self.write_indent();
                self.output.push_str("if ");
                self.emit_expr(*condition);
                self.output.push_str(" then\n");
                self.indent += 1;
                for s in then_body {
                    self.emit_stmt(s);
                }
                self.indent -= 1;
                for clause in elseif_clauses {
                    self.emit_elseif(clause);
                }
                if let Some(else_stmts) = else_body {
                    self.write_indent();
                    self.output.push_str("else\n");
                    self.indent += 1;
                    for s in else_stmts {
                        self.emit_stmt(s);
                    }
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
                for s in body {
                    self.emit_stmt(s);
                }
                self.indent -= 1;
                self.write_indent();
                self.output.push_str("end\n");
            }

            HirStmt::Repeat { body, condition } => {
                self.write_indent();
                self.output.push_str("repeat\n");
                self.indent += 1;
                for s in body {
                    self.emit_stmt(s);
                }
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
                for s in body {
                    self.emit_stmt(s);
                }
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
                for s in body {
                    self.emit_stmt(s);
                }
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
    ///   `X.Y = function(self, ...)` → `function X:Y(...)`
    ///   `X.Y = function(...)` → `function X.Y(...)`
    ///
    /// Returns true if the statement was handled as a function definition.
    fn try_emit_func_def(&mut self, target: &LValue, value: ExprId) -> bool {
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
                (format!("{}{}{}", table_str, separator, field), "")
            }
            LValue::Global(name) => {
                (name.clone(), "")
            }
            LValue::Local(var_id) => {
                let name = self.var_name(*var_id);
                let is_new = self.declared.insert(*var_id);
                let prefix = if is_new { "local " } else { "" };
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

    fn emit_elseif(&mut self, clause: &ElseIfClause) {
        self.write_indent();
        self.output.push_str("elseif ");
        self.emit_expr(clause.condition);
        self.output.push_str(" then\n");
        self.indent += 1;
        for s in &clause.body {
            self.emit_stmt(s);
        }
        self.indent -= 1;
    }

    /// Pre-declare local variables that are first assigned inside one branch
    /// of an if-statement but referenced in another branch or after the if.
    ///
    /// Without this, `local p0x = p0.x` inside an if-branch would scope p0x
    /// to that branch, making it a global reference in the else-branch.
    fn hoist_branch_locals(
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
    fn collect_undeclared_assigns(&self, stmts: &[HirStmt]) -> FxHashSet<VarId> {
        let mut result = FxHashSet::default();
        for stmt in stmts {
            collect_undeclared_assigns_stmt(stmt, &self.declared, &mut result);
        }
        result
    }

    fn emit_terminator(
        &mut self,
        terminator: &Terminator,
        node_idx: NodeIndex,
    ) {
        match terminator {
            Terminator::None => {}

            Terminator::Jump => {
                let target = self
                    .func
                    .cfg
                    .edges(node_idx)
                    .next()
                    .map(|e| e.target());
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

    fn emit_expr(&mut self, expr_id: ExprId) {
        let expr = self.func.exprs.get(expr_id).clone();
        match &expr {
            HirExpr::Var(var_id) => {
                self.output.push_str(&self.var_name(*var_id));
            }

            HirExpr::Reg(reg_ref) => {
                let _ = write!(self.output, "r{}_{}", reg_ref.register, reg_ref.pc);
            }

            HirExpr::Literal(val) => {
                self.emit_literal(val);
            }

            HirExpr::Global(name) => {
                self.output.push_str(name);
            }

            HirExpr::Upvalue(slot) => {
                if let Some(Some(name)) = self.func.upvalue_names.get(*slot as usize) {
                    self.output.push_str(name);
                } else {
                    let _ = write!(self.output, "upval_{}", slot);
                }
            }

            HirExpr::VarArg => {
                self.output.push_str("...");
            }

            HirExpr::FieldAccess { table, field } => {
                // Literals need parens: ("str").field, not "str".field
                let needs_parens = matches!(self.func.exprs.get(*table), HirExpr::Literal(_));
                if needs_parens {
                    self.output.push('(');
                    self.emit_expr(*table);
                    self.output.push(')');
                } else {
                    self.emit_expr_parens(*table, Precedence::POSTFIX);
                }
                self.output.push('.');
                self.output.push_str(field);
            }

            HirExpr::IndexAccess { table, key } => {
                self.emit_expr_parens(*table, Precedence::POSTFIX);
                self.output.push('[');
                self.emit_expr(*key);
                self.output.push(']');
            }

            HirExpr::Binary { op, left, right } => {
                let prec = binop_precedence(*op);
                self.emit_expr_parens(*left, prec);
                let _ = write!(self.output, " {} ", binop_str(*op));
                // Right-associative for .. and ^, left-associative otherwise
                let right_prec = if matches!(op, BinOp::Concat | BinOp::Pow) {
                    Precedence(prec.0 - 1)
                } else {
                    Precedence(prec.0 + 1)
                };
                self.emit_expr_parens(*right, right_prec);
            }

            HirExpr::Unary { op, operand } => {
                match op {
                    UnOp::Not => self.output.push_str("not "),
                    UnOp::Minus => self.output.push('-'),
                    UnOp::Len => self.output.push('#'),
                }
                self.emit_expr_parens(*operand, Precedence::UNARY);
            }

            HirExpr::Call {
                func,
                args,
                ..
            } => {
                self.emit_expr_parens(*func, Precedence::POSTFIX);
                self.output.push('(');
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        self.output.push_str(", ");
                    }
                    self.emit_expr(*arg);
                }
                self.output.push(')');
            }

            HirExpr::MethodCall {
                object,
                method,
                args,
                ..
            } => {
                // Literals need explicit parens as method receivers: ("str"):method()
                let needs_parens = matches!(self.func.exprs.get(*object), HirExpr::Literal(_));
                if needs_parens {
                    self.output.push('(');
                    self.emit_expr(*object);
                    self.output.push(')');
                } else {
                    self.emit_expr_parens(*object, Precedence::POSTFIX);
                }
                self.output.push(':');
                self.output.push_str(method);
                self.output.push('(');
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        self.output.push_str(", ");
                    }
                    self.emit_expr(*arg);
                }
                self.output.push(')');
            }

            HirExpr::Closure { proto_id, .. } => {
                // Try to resolve and emit inline if we have file context
                if let Some(ctx) = self.file_ctx {
                    if let Some(child_protos) = ctx.child_protos.get(self.func.proto_index) {
                        if let Some(&bc_idx) = child_protos.get(*proto_id) {
                            if let Some(child_func) = ctx.funcs.get(bc_idx) {
                                // Anonymous closure: function(...) body end
                                let mut child_emitter = LuaEmitter::new(child_func, self.file_ctx);
                                child_emitter.indent = self.indent;
                                self.output.push_str("function");
                                child_emitter.emit_params_only();
                                self.output.push_str(&child_emitter.output);
                                child_emitter.output.clear();
                                child_emitter.indent += 1;
                                child_emitter.emit_body();
                                child_emitter.indent -= 1;
                                child_emitter.write_indent();
                                child_emitter.output.push_str("end");
                                self.output.push_str(&child_emitter.output);
                                return;
                            }
                        }
                    }
                }

                // Fallback: placeholder
                let _ = write!(self.output, "function --[[proto#{}]]() end", proto_id);
            }

            HirExpr::Table { array, hash } => {
                if array.is_empty() && hash.is_empty() {
                    self.output.push_str("{}");
                    return;
                }
                self.output.push_str("{ ");
                let mut first = true;
                for item in array {
                    if !first {
                        self.output.push_str(", ");
                    }
                    self.emit_expr(*item);
                    first = false;
                }
                for (key, val) in hash {
                    if !first {
                        self.output.push_str(", ");
                    }
                    self.output.push('[');
                    self.emit_expr(*key);
                    self.output.push_str("] = ");
                    self.emit_expr(*val);
                    first = false;
                }
                self.output.push_str(" }");
            }

            HirExpr::Concat(operands) => {
                for (i, op) in operands.iter().enumerate() {
                    if i > 0 {
                        self.output.push_str(" .. ");
                    }
                    self.emit_expr_parens(*op, Precedence::CONCAT);
                }
            }

            HirExpr::IfExpr {
                condition,
                then_expr,
                else_expr,
            } => {
                self.output.push_str("if ");
                self.emit_expr(*condition);
                self.output.push_str(" then ");
                self.emit_expr(*then_expr);
                self.output.push_str(" else ");
                self.emit_expr(*else_expr);
            }

            HirExpr::Select { source, index } => {
                // Select should be collapsed into MultiAssign before emission.
                // If it survives, emit as a comment annotation.
                let _ = write!(self.output, "--[[result #{}]] ", index);
                self.emit_expr(*source);
            }
        }
    }

    fn emit_literal(&mut self, val: &LuaValue) {
        match val {
            LuaValue::Nil => self.output.push_str("nil"),
            LuaValue::Boolean(true) => self.output.push_str("true"),
            LuaValue::Boolean(false) => self.output.push_str("false"),
            LuaValue::Number(n) => {
                if n.is_infinite() {
                    if n.is_sign_positive() {
                        self.output.push_str("math.huge");
                    } else {
                        self.output.push_str("-math.huge");
                    }
                } else if n.is_nan() {
                    self.output.push_str("(0/0)");
                } else if n.fract() == 0.0 && n.abs() < 1e15 {
                    // Format integers without decimal point
                    let _ = write!(self.output, "{}", *n as i64);
                } else {
                    let _ = write!(self.output, "{}", n);
                }
            }
            LuaValue::String(bytes) => {
                self.emit_string(bytes);
            }
            LuaValue::Vector(x, y, z) => {
                let _ = write!(self.output, "Vector3.new({}, {}, {})", x, y, z);
            }
        }
    }

    fn emit_string(&mut self, bytes: &[u8]) {
        self.output.push('"');
        for &b in bytes {
            match b {
                b'\\' => self.output.push_str("\\\\"),
                b'"' => self.output.push_str("\\\""),
                b'\n' => self.output.push_str("\\n"),
                b'\r' => self.output.push_str("\\r"),
                b'\t' => self.output.push_str("\\t"),
                b'\0' => self.output.push_str("\\0"),
                0x20..=0x7e => self.output.push(b as char),
                _ => {
                    let _ = write!(self.output, "\\{}", b);
                }
            }
        }
        self.output.push('"');
    }

    fn emit_lvalue(&mut self, lv: &LValue) {
        match lv {
            LValue::Local(var_id) => {
                self.output.push_str(&self.var_name(*var_id));
            }
            LValue::Global(name) => {
                self.output.push_str(name);
            }
            LValue::Field { table, field } => {
                self.emit_expr_parens(*table, Precedence::POSTFIX);
                self.output.push('.');
                self.output.push_str(field);
            }
            LValue::Index { table, key } => {
                self.emit_expr_parens(*table, Precedence::POSTFIX);
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

    fn emit_closure_body(&mut self, expr_id: ExprId) {
        // Try to resolve the closure to a child function
        if let HirExpr::Closure { proto_id, .. } = self.func.exprs.get(expr_id) {
            if let Some(ctx) = self.file_ctx {
                if let Some(child_protos) = ctx.child_protos.get(self.func.proto_index) {
                    if let Some(&bc_idx) = child_protos.get(*proto_id) {
                        if let Some(child_func) = ctx.funcs.get(bc_idx) {
                            // Emit params and body
                            let mut child_emitter = LuaEmitter::new(child_func, self.file_ctx);
                            child_emitter.indent = self.indent;
                            // Emit just the params portion
                            child_emitter.emit_params_only();
                            self.output.push_str(&child_emitter.output);
                            child_emitter.output.clear();
                            child_emitter.indent += 1;
                            child_emitter.emit_body();
                            child_emitter.indent -= 1;
                            child_emitter.write_indent();
                            child_emitter.output.push_str("end");
                            self.output.push_str(&child_emitter.output);
                            return;
                        }
                    }
                }
            }
        }
        // Fallback
        self.output.push_str("() end");
    }

    /// Emit just the parameter list: `(params...)\n`
    fn emit_params_only(&mut self) {
        let has_self = self.func.params.first().map_or(false, |p| {
            self.func.vars.get(*p).name.as_deref() == Some("self")
        });
        let param_start = if has_self { 1 } else { 0 };
        let params = &self.func.params[param_start..];

        self.output.push('(');
        for (i, var_id) in params.iter().enumerate() {
            if i > 0 {
                self.output.push_str(", ");
            }
            self.output.push_str(&self.var_name(*var_id));
        }
        if self.func.is_vararg {
            if !params.is_empty() {
                self.output.push_str(", ");
            }
            self.output.push_str("...");
        }
        self.output.push_str(")\n");
    }

    /// Convert an expression to a string (for building qualified names).
    fn expr_to_string(&self, expr_id: ExprId) -> Option<String> {
        let expr = self.func.exprs.get(expr_id);
        match expr {
            HirExpr::Global(name) => Some(name.clone()),
            HirExpr::Var(var_id) => Some(self.var_name(*var_id)),
            HirExpr::FieldAccess { table, field } => {
                Some(format!("{}.{}", self.expr_to_string(*table)?, field))
            }
            HirExpr::IndexAccess { table, key } => {
                Some(format!("{}[{}]", self.expr_to_string(*table)?, self.expr_to_string(*key)?))
            }
            HirExpr::Upvalue(slot) => {
                if let Some(Some(name)) = self.func.upvalue_names.get(*slot as usize) {
                    Some(name.clone())
                } else {
                    Some(format!("upval_{}", slot))
                }
            }
            HirExpr::Literal(lit) => {
                match lit {
                    LuaValue::String(s) => Some(format!("\"{}\"", String::from_utf8_lossy(s))),
                    LuaValue::Number(n) => {
                        if n.is_infinite() {
                            Some(if n.is_sign_positive() { "math.huge".to_string() } else { "-math.huge".to_string() })
                        } else if n.is_nan() {
                            Some("(0/0)".to_string())
                        } else {
                            Some(format!("{}", n))
                        }
                    }
                    LuaValue::Boolean(b) => Some(format!("{}", b)),
                    LuaValue::Nil => Some("nil".to_string()),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Emit an expression, wrapping in parentheses if its precedence is lower.
    fn emit_expr_parens(&mut self, expr_id: ExprId, min_prec: Precedence) {
        let expr = self.func.exprs.get(expr_id);
        let my_prec = expr_precedence(expr);

        if my_prec.0 < min_prec.0 {
            self.output.push('(');
            self.emit_expr(expr_id);
            self.output.push(')');
        } else {
            self.emit_expr(expr_id);
        }
    }

    fn var_name(&self, var_id: VarId) -> String {
        self.func.vars.get(var_id).display_name(var_id)
    }

    fn write_indent(&mut self) {
        for _ in 0..self.indent {
            self.output.push_str("    ");
        }
    }
}

/// Operator precedence levels (higher = binds tighter).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Precedence(u8);

impl Precedence {
    const OR: Self = Precedence(1);
    const AND: Self = Precedence(2);
    const COMPARE: Self = Precedence(3);
    const CONCAT: Self = Precedence(4);
    const ADD: Self = Precedence(5);
    const MUL: Self = Precedence(6);
    const UNARY: Self = Precedence(7);
    const POW: Self = Precedence(8);

    const POSTFIX: Self = Precedence(10);
}

fn binop_precedence(op: BinOp) -> Precedence {
    match op {
        BinOp::Or => Precedence::OR,
        BinOp::And => Precedence::AND,
        BinOp::CompareEq
        | BinOp::CompareNe
        | BinOp::CompareLt
        | BinOp::CompareLe
        | BinOp::CompareGt
        | BinOp::CompareGe => Precedence::COMPARE,
        BinOp::Concat => Precedence::CONCAT,
        BinOp::Add | BinOp::Sub => Precedence::ADD,
        BinOp::Mul | BinOp::Div | BinOp::FloorDiv | BinOp::Mod => Precedence::MUL,
        BinOp::Pow => Precedence::POW,
    }
}

fn expr_precedence(expr: &HirExpr) -> Precedence {
    match expr {
        HirExpr::Binary { op, .. } => binop_precedence(*op),
        HirExpr::Unary { .. } => Precedence::UNARY,
        HirExpr::Concat(_) => Precedence::CONCAT,
        _ => Precedence(20), // atoms — never need parens
    }
}

fn binop_str(op: BinOp) -> &'static str {
    match op {
        BinOp::Add => "+",
        BinOp::Sub => "-",
        BinOp::Mul => "*",
        BinOp::Div => "/",
        BinOp::FloorDiv => "//",
        BinOp::Mod => "%",
        BinOp::Pow => "^",
        BinOp::Concat => "..",
        BinOp::CompareEq => "==",
        BinOp::CompareNe => "~=",
        BinOp::CompareLt => "<",
        BinOp::CompareLe => "<=",
        BinOp::CompareGt => ">",
        BinOp::CompareGe => ">=",
        BinOp::And => "and",
        BinOp::Or => "or",
    }
}

/// Collect VarIds assigned as LValue::Local in statements, recursively.
/// Only includes vars not in `declared`.
fn collect_undeclared_assigns_stmt(
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
fn collect_var_refs(stmts: &[HirStmt]) -> FxHashSet<VarId> {
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
