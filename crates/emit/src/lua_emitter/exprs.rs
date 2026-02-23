use std::fmt::Write;

use lantern_hir::arena::ExprId;
use lantern_hir::expr::HirExpr;
use lantern_hir::types::{BinOp, LuaValue, UnOp};

use super::precedence::{binop_precedence, binop_str, expr_precedence, Precedence};
use super::LuaEmitter;

impl<'a> LuaEmitter<'a> {
    pub(super) fn emit_expr(&mut self, expr_id: ExprId) {
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

            HirExpr::Call { func, args, .. } => {
                // Closures need explicit parens for IIFE: (function() ... end)(args)
                let needs_parens = matches!(self.func.exprs.get(*func), HirExpr::Closure { .. });
                if needs_parens {
                    self.output.push('(');
                }
                self.emit_expr_parens(*func, Precedence::POSTFIX);
                if needs_parens {
                    self.output.push(')');
                }
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

    pub(super) fn emit_literal(&mut self, val: &LuaValue) {
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

    pub(super) fn emit_string(&mut self, bytes: &[u8]) {
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

    pub(super) fn emit_closure_body(&mut self, expr_id: ExprId) {
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
    pub(super) fn emit_params_only(&mut self) {
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
    pub(super) fn expr_to_string(&self, expr_id: ExprId) -> Option<String> {
        let expr = self.func.exprs.get(expr_id);
        match expr {
            HirExpr::Global(name) => Some(name.clone()),
            HirExpr::Var(var_id) => Some(self.var_name(*var_id)),
            HirExpr::FieldAccess { table, field } => {
                Some(format!("{}.{}", self.expr_to_string(*table)?, field))
            }
            HirExpr::IndexAccess { table, key } => Some(format!(
                "{}[{}]",
                self.expr_to_string(*table)?,
                self.expr_to_string(*key)?
            )),
            HirExpr::Upvalue(slot) => {
                if let Some(Some(name)) = self.func.upvalue_names.get(*slot as usize) {
                    Some(name.clone())
                } else {
                    Some(format!("upval_{}", slot))
                }
            }
            HirExpr::Literal(lit) => match lit {
                LuaValue::String(s) => Some(format!("\"{}\"", String::from_utf8_lossy(s))),
                LuaValue::Number(n) => {
                    if n.is_infinite() {
                        Some(if n.is_sign_positive() {
                            "math.huge".to_string()
                        } else {
                            "-math.huge".to_string()
                        })
                    } else if n.is_nan() {
                        Some("(0/0)".to_string())
                    } else {
                        Some(format!("{}", n))
                    }
                }
                LuaValue::Boolean(b) => Some(format!("{}", b)),
                LuaValue::Nil => Some("nil".to_string()),
                _ => None,
            },
            _ => None,
        }
    }

    /// Emit an expression, wrapping in parentheses if its precedence is lower.
    pub(super) fn emit_expr_parens(&mut self, expr_id: ExprId, min_prec: Precedence) {
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
}
