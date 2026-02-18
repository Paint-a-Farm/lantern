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

/// Emit a function to Lua source text.
///
/// Currently works on unstructured HIR: walks blocks in PC order,
/// emitting block labels and goto-style control flow. As the
/// structure/patterns crates recover higher-level constructs,
/// this will emit proper if/while/for/etc.
pub fn emit_function(func: &HirFunc) -> String {
    let mut emitter = LuaEmitter::new(func);
    emitter.emit();
    emitter.output
}

pub struct LuaEmitter<'a> {
    func: &'a HirFunc,
    pub output: String,
    indent: usize,
}

impl<'a> LuaEmitter<'a> {
    pub fn new(func: &'a HirFunc) -> Self {
        Self {
            func,
            output: String::new(),
            indent: 0,
        }
    }

    pub fn emit(&mut self) {
        if self.func.structured {
            // Structured mode: walk only the entry block's nested statement tree
            let entry = self.func.entry;
            for stmt in &self.func.cfg[entry].stmts {
                self.emit_stmt(stmt);
            }
        } else {
            self.emit_unstructured();
        }
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
                self.write_indent();
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
                    self.output.push_str(", ");
                    self.emit_expr(*step_expr);
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
                self.emit_expr_parens(*table, Precedence::POSTFIX);
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
                self.emit_expr_parens(*object, Precedence::POSTFIX);
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
                // In unstructured mode we don't have the child's HIR,
                // so just emit a placeholder referencing the proto.
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
                self.output.push_str("select(");
                self.emit_expr(*source);
                let _ = write!(self.output, ", {})", index);
            }
        }
    }

    fn emit_literal(&mut self, val: &LuaValue) {
        match val {
            LuaValue::Nil => self.output.push_str("nil"),
            LuaValue::Boolean(true) => self.output.push_str("true"),
            LuaValue::Boolean(false) => self.output.push_str("false"),
            LuaValue::Number(n) => {
                // Format integers without decimal point
                if n.fract() == 0.0 && n.abs() < 1e15 {
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

    fn emit_closure_body(&mut self, _expr_id: ExprId) {
        // In unstructured mode, closures reference child protos by index.
        // Full closure emission comes later when we lift child functions.
        self.output.push_str("() end");
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
