use lantern_bytecode::constant::Constant;
use lantern_bytecode::instruction::Instruction;

use lantern_hir::arena::ExprId;
use lantern_hir::expr::HirExpr;
use lantern_hir::stmt::HirStmt;
use lantern_hir::types::{BinOp, LuaValue, UnOp};

impl<'a> super::Lifter<'a> {
    pub(super) fn lift_constant(&mut self, index: usize, pc: usize) -> ExprId {
        let value = self.constant_to_value(index);
        self.alloc_expr(HirExpr::Literal(value), pc)
    }

    pub(super) fn constant_to_value(&self, index: usize) -> LuaValue {
        match &self.func.constants[index] {
            Constant::Nil => LuaValue::Nil,
            Constant::Boolean(b) => LuaValue::Boolean(*b),
            Constant::Number(n) => LuaValue::Number(*n),
            Constant::String(idx) => {
                let bytes = self.chunk.string_table[*idx - 1].clone();
                LuaValue::String(bytes)
            }
            Constant::Vector(x, y, z, _) => LuaValue::Vector(*x, *y, *z),
            _ => LuaValue::Nil, // Import, Table, Closure handled elsewhere
        }
    }

    /// Resolve AUX word to a string name.
    /// For GETGLOBAL/SETGLOBAL/GETTABLEKS/SETTABLEKS/NAMECALL, AUX is a
    /// constant table index pointing to a String constant.
    pub(super) fn string_from_aux(&self, aux: u32) -> String {
        let const_idx = aux as usize;
        if const_idx < self.func.constants.len() {
            if let Constant::String(str_idx) = &self.func.constants[const_idx] {
                if *str_idx > 0 && *str_idx <= self.chunk.string_table.len() {
                    return String::from_utf8_lossy(&self.chunk.string_table[*str_idx - 1])
                        .to_string();
                }
            }
        }
        format!("__unknown_{}", aux)
    }

    pub(super) fn lift_import(&mut self, aux: u32, pc: usize) -> ExprId {
        // GETIMPORT AUX encodes up to 3 name indices:
        // top 2 bits = count (1-3), then 3x 10-bit indices
        let count = (aux >> 30) as usize;
        let k0 = ((aux >> 20) & 0x3FF) as usize;

        let name0 = match &self.func.constants[k0] {
            Constant::String(idx) => {
                String::from_utf8_lossy(&self.chunk.string_table[*idx - 1]).to_string()
            }
            _ => format!("__import_{}", k0),
        };

        let mut expr = self.alloc_expr(HirExpr::Global(name0), pc);

        if count >= 2 {
            let k1 = ((aux >> 10) & 0x3FF) as usize;
            let field1 = match &self.func.constants[k1] {
                Constant::String(idx) => {
                    String::from_utf8_lossy(&self.chunk.string_table[*idx - 1]).to_string()
                }
                _ => format!("__field_{}", k1),
            };
            expr = self.alloc_expr(
                HirExpr::FieldAccess {
                    table: expr,
                    field: field1,
                },
                pc,
            );
        }

        if count >= 3 {
            let k2 = (aux & 0x3FF) as usize;
            let field2 = match &self.func.constants[k2] {
                Constant::String(idx) => {
                    String::from_utf8_lossy(&self.chunk.string_table[*idx - 1]).to_string()
                }
                _ => format!("__field_{}", k2),
            };
            expr = self.alloc_expr(
                HirExpr::FieldAccess {
                    table: expr,
                    field: field2,
                },
                pc,
            );
        }

        expr
    }

    pub(super) fn lift_binary(
        &mut self,
        op: BinOp,
        insn: &Instruction,
        pc: usize,
        rhs_const: bool,
    ) -> usize {
        let reg = self.reg_ref(insn.a, pc);
        let left = self.alloc_expr(HirExpr::Reg(self.reg_ref(insn.b, pc)), pc);
        let right = if rhs_const {
            self.lift_constant(insn.c as usize, pc)
        } else {
            self.alloc_expr(HirExpr::Reg(self.reg_ref(insn.c, pc)), pc)
        };
        let expr = self.alloc_expr(HirExpr::Binary { op, left, right }, pc);
        self.emit_assign_reg(reg, expr);
        1
    }

    pub(super) fn lift_binary_rk(&mut self, op: BinOp, insn: &Instruction, pc: usize) -> usize {
        // Reverse: A = K[B] op C
        let reg = self.reg_ref(insn.a, pc);
        let left = self.lift_constant(insn.b as usize, pc);
        let right = self.alloc_expr(HirExpr::Reg(self.reg_ref(insn.c, pc)), pc);
        let expr = self.alloc_expr(HirExpr::Binary { op, left, right }, pc);
        self.emit_assign_reg(reg, expr);
        1
    }

    pub(super) fn lift_unary(&mut self, op: UnOp, insn: &Instruction, pc: usize) -> usize {
        let reg = self.reg_ref(insn.a, pc);
        let operand = self.alloc_expr(HirExpr::Reg(self.reg_ref(insn.b, pc)), pc);
        let expr = self.alloc_expr(HirExpr::Unary { op, operand }, pc);
        self.emit_assign_reg(reg, expr);
        1
    }

    /// Fold array elements from SETLIST into the Table expression for `table_reg`.
    ///
    /// Searches backwards through the current block's statements to find the
    /// RegAssign for `table_reg` that contains a `HirExpr::Table`, then appends
    /// the elements to its `array` field.
    pub(super) fn fold_array_into_table(&mut self, table_reg: u8, elements: Vec<ExprId>) {
        // Find the Table expression ID assigned to this register
        let stmts = &self.hir.cfg[self.current_block].stmts;
        let mut table_expr_id = None;
        for stmt in stmts.iter().rev() {
            if let HirStmt::RegAssign { target, value } = stmt {
                if target.register == table_reg {
                    // Check this is actually a Table expression
                    if matches!(self.hir.exprs.get(*value), HirExpr::Table { .. }) {
                        table_expr_id = Some(*value);
                    }
                    break;
                }
            }
        }

        if let Some(expr_id) = table_expr_id {
            // Mutate the Table expression in the arena to include elements
            if let HirExpr::Table { array, .. } = self.hir.exprs.get_mut(expr_id) {
                array.extend(elements);
            }
        }
    }

    /// Try to fold a SETTABLEKS assignment into a table constructor.
    ///
    /// If register `table_reg` was last assigned a `HirExpr::Table` (from
    /// NEWTABLE or DUPTABLE), this adds the key-value pair to the table's
    /// `hash` field and returns true. Otherwise returns false.
    pub(super) fn try_fold_hash_into_table(
        &mut self,
        table_reg: u8,
        field: &str,
        value: ExprId,
        pc: usize,
    ) -> bool {
        // Find the Table expression ID assigned to this register, and track
        // which registers were assigned between the table def and now.
        let stmts = &self.hir.cfg[self.current_block].stmts;
        let mut table_expr_id = None;
        let mut table_stmt_idx = 0;
        for (idx, stmt) in stmts.iter().enumerate().rev() {
            if let HirStmt::RegAssign { target, value: v } = stmt {
                if target.register == table_reg {
                    if let HirExpr::Table { has_named_keys, .. } = self.hir.exprs.get(*v) {
                        // Only fold into DupTable tables (has_named_keys=true).
                        // NewTable tables should be left for the post-varrecovery
                        // table_fold pass which produces proper Var references.
                        if *has_named_keys {
                            table_expr_id = Some(*v);
                            table_stmt_idx = idx;
                        }
                    }
                    break;
                }
            }
        }

        if let Some(expr_id) = table_expr_id {
            // Check if the value register was assigned AFTER the table def.
            // If so, the value depends on something computed after the table
            // constructor, so folding would create a use-before-def.
            let value_reg = match self.hir.exprs.get(value) {
                HirExpr::Reg(rr) => Some(rr.register),
                _ => None,
            };
            if let Some(vreg) = value_reg {
                for stmt in &stmts[table_stmt_idx + 1..] {
                    if let HirStmt::RegAssign { target, value: v } = stmt {
                        if target.register == vreg {
                            // The value register was assigned after the table.
                            // Allow folding if the value is a simple literal/constant
                            // (e.g. LoadB true) since it doesn't depend on ordering.
                            if !matches!(self.hir.exprs.get(*v), HirExpr::Literal(_)) {
                                return false;
                            }
                            break;
                        }
                    }
                }
            }

            let key = self.alloc_expr(
                HirExpr::Literal(LuaValue::String(field.as_bytes().to_vec())),
                pc,
            );
            if let HirExpr::Table { hash, .. } = self.hir.exprs.get_mut(expr_id) {
                hash.push((key, value));
                return true;
            }
        }
        false
    }
}
