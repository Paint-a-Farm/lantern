use lantern_bytecode::constant::Constant;
use lantern_bytecode::instruction::Instruction;
use lantern_bytecode::opcode::OpCode;

use lantern_hir::arena::ExprId;
use lantern_hir::cfg::{EdgeKind, HirEdge};
use lantern_hir::expr::{Capture, CaptureSource, HirExpr};
use lantern_hir::stmt::{HirStmt, LValue};
use lantern_hir::types::{BinOp, CaptureKind, LuaValue, UnOp};
use lantern_hir::var::RegRef;

impl<'a> super::Lifter<'a> {
    /// Lift a single instruction. Returns the number of PCs consumed
    /// (usually 1, but 2 for instructions with AUX).
    pub(super) fn lift_instruction(&mut self, insn: &Instruction, pc: usize) -> usize {
        match insn.op {
            OpCode::Nop | OpCode::Break | OpCode::Coverage | OpCode::NativeCall => 1,

            OpCode::PrepVarArgs => 1,

            OpCode::LoadNil => {
                let reg = self.reg_ref(insn.a, pc);
                let expr = self.alloc_expr(HirExpr::Literal(LuaValue::Nil), pc);
                self.emit_assign_reg(reg, expr);
                1
            }

            OpCode::LoadB => {
                let reg = self.reg_ref(insn.a, pc);
                let val = insn.b != 0;
                let expr = self.alloc_expr(HirExpr::Literal(LuaValue::Boolean(val)), pc);
                self.emit_assign_reg(reg, expr);

                if insn.c != 0 {
                    // LOADB with jump
                    let target = (pc + 1).wrapping_add(insn.c as usize);
                    self.add_jump_edge(target);
                    2 // skip next instruction
                } else {
                    1
                }
            }

            OpCode::LoadN => {
                let reg = self.reg_ref(insn.a, pc);
                let expr = self.alloc_expr(HirExpr::Literal(LuaValue::Number(insn.d as f64)), pc);
                self.emit_assign_reg(reg, expr);
                1
            }

            OpCode::LoadK => {
                let reg = self.reg_ref(insn.a, pc);
                let expr = self.lift_constant(insn.d as usize, pc);
                self.emit_assign_reg(reg, expr);
                1
            }

            OpCode::LoadKX => {
                let reg = self.reg_ref(insn.a, pc);
                let expr = self.lift_constant(insn.aux as usize, pc);
                self.emit_assign_reg(reg, expr);
                2 // AUX word
            }

            OpCode::Move => {
                let dst = self.reg_ref(insn.a, pc);
                let src = self.alloc_expr(HirExpr::Reg(self.reg_ref(insn.b, pc)), pc);
                self.emit_assign_reg(dst, src);
                1
            }

            // Global access
            OpCode::GetGlobal => {
                let reg = self.reg_ref(insn.a, pc);
                let name = self.string_from_aux(insn.aux);
                let expr = self.alloc_expr(HirExpr::Global(name), pc);
                self.emit_assign_reg(reg, expr);
                2 // AUX
            }

            OpCode::SetGlobal => {
                let name = self.string_from_aux(insn.aux);
                let value = self.alloc_expr(HirExpr::Reg(self.reg_ref(insn.a, pc)), pc);
                self.emit_stmt(HirStmt::Assign {
                    target: LValue::Global(name),
                    value,
                });
                2 // AUX
            }

            // Upvalue access
            OpCode::GetUpval => {
                let reg = self.reg_ref(insn.a, pc);
                let expr = self.alloc_expr(HirExpr::Upvalue(insn.b), pc);
                self.emit_assign_reg(reg, expr);
                1
            }

            OpCode::SetUpval => {
                let value = self.alloc_expr(HirExpr::Reg(self.reg_ref(insn.a, pc)), pc);
                self.emit_stmt(HirStmt::Assign {
                    target: LValue::Upvalue(insn.b),
                    value,
                });
                1
            }

            OpCode::CloseUpvals => {
                self.emit_stmt(HirStmt::CloseUpvals {
                    from_register: insn.a,
                });
                1
            }

            // Import (e.g. math.floor, table.insert)
            OpCode::GetImport => {
                let reg = self.reg_ref(insn.a, pc);
                let expr = self.lift_import(insn.aux, pc);
                self.emit_assign_reg(reg, expr);
                2 // AUX
            }

            // Table operations
            OpCode::GetTable => {
                let reg = self.reg_ref(insn.a, pc);
                let table = self.alloc_expr(HirExpr::Reg(self.reg_ref(insn.b, pc)), pc);
                let key = self.alloc_expr(HirExpr::Reg(self.reg_ref(insn.c, pc)), pc);
                let expr = self.alloc_expr(HirExpr::IndexAccess { table, key }, pc);
                self.emit_assign_reg(reg, expr);
                1
            }

            OpCode::SetTable => {
                let table_expr = self.alloc_expr(HirExpr::Reg(self.reg_ref(insn.b, pc)), pc);
                let key_expr = self.alloc_expr(HirExpr::Reg(self.reg_ref(insn.c, pc)), pc);
                let value = self.alloc_expr(HirExpr::Reg(self.reg_ref(insn.a, pc)), pc);
                self.emit_stmt(HirStmt::Assign {
                    target: LValue::Index {
                        table: table_expr,
                        key: key_expr,
                    },
                    value,
                });
                1
            }

            OpCode::GetTableKS => {
                let reg = self.reg_ref(insn.a, pc);
                let table = self.alloc_expr(HirExpr::Reg(self.reg_ref(insn.b, pc)), pc);
                let field = self.string_from_aux(insn.aux);
                let expr = self.alloc_expr(HirExpr::FieldAccess { table, field }, pc);
                self.emit_assign_reg(reg, expr);
                2 // AUX
            }

            OpCode::SetTableKS => {
                let field = self.string_from_aux(insn.aux);
                let value = self.alloc_expr(HirExpr::Reg(self.reg_ref(insn.a, pc)), pc);
                // Try to fold into a table constructor (DUPTABLE/NEWTABLE pattern).
                // We don't pop the value RegAssign here — it references the register
                // directly. The value may come from an earlier multi-return Select,
                // and popping would disrupt the Select chain for multi_return collapsing.
                if !self.try_fold_hash_into_table(insn.b, &field, value, pc) {
                    // Not a table constructor — emit normal field assignment
                    let table_expr = self.alloc_expr(HirExpr::Reg(self.reg_ref(insn.b, pc)), pc);
                    self.emit_stmt(HirStmt::Assign {
                        target: LValue::Field {
                            table: table_expr,
                            field,
                        },
                        value,
                    });
                }
                2 // AUX
            }

            OpCode::GetTableN => {
                let reg = self.reg_ref(insn.a, pc);
                let table = self.alloc_expr(HirExpr::Reg(self.reg_ref(insn.b, pc)), pc);
                // C is index-1, actual index is C+1
                let key = self.alloc_expr(
                    HirExpr::Literal(LuaValue::Number((insn.c as f64) + 1.0)),
                    pc,
                );
                let expr = self.alloc_expr(HirExpr::IndexAccess { table, key }, pc);
                self.emit_assign_reg(reg, expr);
                1
            }

            OpCode::SetTableN => {
                let table_expr = self.alloc_expr(HirExpr::Reg(self.reg_ref(insn.b, pc)), pc);
                let key_expr = self.alloc_expr(
                    HirExpr::Literal(LuaValue::Number((insn.c as f64) + 1.0)),
                    pc,
                );
                let value = self.alloc_expr(HirExpr::Reg(self.reg_ref(insn.a, pc)), pc);
                self.emit_stmt(HirStmt::Assign {
                    target: LValue::Index {
                        table: table_expr,
                        key: key_expr,
                    },
                    value,
                });
                1
            }

            // Arithmetic: A = B op C
            OpCode::Add => self.lift_binary(BinOp::Add, insn, pc, false),
            OpCode::Sub => self.lift_binary(BinOp::Sub, insn, pc, false),
            OpCode::Mul => self.lift_binary(BinOp::Mul, insn, pc, false),
            OpCode::Div => self.lift_binary(BinOp::Div, insn, pc, false),
            OpCode::Mod => self.lift_binary(BinOp::Mod, insn, pc, false),
            OpCode::Pow => self.lift_binary(BinOp::Pow, insn, pc, false),
            OpCode::IDiv => self.lift_binary(BinOp::FloorDiv, insn, pc, false),

            // Arithmetic with constant: A = B op K[C]
            OpCode::AddK => self.lift_binary(BinOp::Add, insn, pc, true),
            OpCode::SubK => self.lift_binary(BinOp::Sub, insn, pc, true),
            OpCode::MulK => self.lift_binary(BinOp::Mul, insn, pc, true),
            OpCode::DivK => self.lift_binary(BinOp::Div, insn, pc, true),
            OpCode::ModK => self.lift_binary(BinOp::Mod, insn, pc, true),
            OpCode::PowK => self.lift_binary(BinOp::Pow, insn, pc, true),
            OpCode::IDivK => self.lift_binary(BinOp::FloorDiv, insn, pc, true),

            // Reverse constant arithmetic: A = K[B] op C
            OpCode::SubRK => self.lift_binary_rk(BinOp::Sub, insn, pc),
            OpCode::DivRK => self.lift_binary_rk(BinOp::Div, insn, pc),

            // And/Or: A = B and/or C (or K[C])
            OpCode::And => self.lift_binary(BinOp::And, insn, pc, false),
            OpCode::Or => self.lift_binary(BinOp::Or, insn, pc, false),
            OpCode::AndK => self.lift_binary(BinOp::And, insn, pc, true),
            OpCode::OrK => self.lift_binary(BinOp::Or, insn, pc, true),

            // Unary: A = op B
            OpCode::Not => self.lift_unary(UnOp::Not, insn, pc),
            OpCode::Minus => self.lift_unary(UnOp::Minus, insn, pc),
            OpCode::Length => self.lift_unary(UnOp::Len, insn, pc),

            // Concat: A = B..B+1..…..C
            OpCode::Concat => {
                let reg = self.reg_ref(insn.a, pc);
                let operands: Vec<ExprId> = (insn.b..=insn.c)
                    .map(|r| self.alloc_expr(HirExpr::Reg(self.reg_ref(r, pc)), pc))
                    .collect();
                let expr = self.alloc_expr(HirExpr::Concat(operands), pc);
                self.emit_assign_reg(reg, expr);
                1
            }

            // Table constructor
            OpCode::NewTable => {
                let reg = self.reg_ref(insn.a, pc);
                let expr = self.alloc_expr(
                    HirExpr::Table {
                        array: Vec::new(),
                        hash: Vec::new(),
                        has_named_keys: false,
                    },
                    pc,
                );
                self.emit_assign_reg(reg, expr);
                2 // AUX (array size)
            }

            OpCode::DupTable => {
                let reg = self.reg_ref(insn.a, pc);
                // DUPTABLE creates a table from a template constant with
                // pre-allocated hash keys.  Mark has_named_keys so the emitter
                // uses bare identifier syntax (`key = val`) which compiles back
                // to DUPTABLE.
                let expr = self.alloc_expr(
                    HirExpr::Table {
                        array: Vec::new(),
                        hash: Vec::new(),
                        has_named_keys: true,
                    },
                    pc,
                );
                self.emit_assign_reg(reg, expr);
                1
            }

            OpCode::SetList => {
                // SETLIST A B C AUX: table[AUX..] = R(B)..R(B+C-2)
                // C is count+1 (0=MULTRET). Fold elements into the Table expression.
                let table_reg = insn.a;
                let source_reg = insn.b;
                let count_plus_1 = insn.c;

                let elements: Vec<ExprId> = if count_plus_1 == 0 {
                    // MULTRET: collect fixed regs + MULTRET expression
                    self.collect_multret_args(source_reg, pc)
                } else {
                    let count = (count_plus_1 - 1) as u8;
                    (0..count)
                        .map(|i| {
                            // Pop the RegAssign for this element register to capture
                            // the actual value expression, removing the dead temp.
                            self.pop_last_reg_assign(source_reg + i).unwrap_or_else(|| {
                                self.alloc_expr(HirExpr::Reg(self.reg_ref(source_reg + i, pc)), pc)
                            })
                        })
                        .collect()
                };

                // Find the Table expression for this register and fold elements in
                self.fold_array_into_table(table_reg, elements);
                2 // AUX
            }

            // NAMECALL: prepare method call (A = B[K], A+1 = B)
            OpCode::NameCall => {
                let method = self.string_from_aux(insn.aux);
                let obj = self.alloc_expr(HirExpr::Reg(self.reg_ref(insn.b, pc)), pc);

                // NAMECALL must be followed by CALL
                let next_pc = pc + 2; // skip AUX
                let call_insn = &self.func.instructions[next_pc];
                debug_assert!(call_insn.op == OpCode::Call);

                let nresults = if call_insn.c == 0 { 0 } else { call_insn.c - 1 };

                // Arguments start at A+2 (A = func, A+1 = self)
                // B counts include the implicit self, so explicit args = B-2
                let args = if call_insn.b == 0 {
                    // MULTRET args: fixed regs from A+2 to top_reg-1, then top expr
                    self.collect_multret_args(call_insn.a + 2, next_pc)
                } else {
                    let nargs = call_insn.b.saturating_sub(2); // B includes func+self
                    (0..nargs)
                        .map(|i| {
                            self.alloc_expr(
                                HirExpr::Reg(self.reg_ref(call_insn.a + 2 + i, next_pc)),
                                next_pc,
                            )
                        })
                        .collect()
                };

                let call_expr = self.alloc_expr(
                    HirExpr::MethodCall {
                        object: obj,
                        method,
                        args,
                        result_count: nresults as u8,
                    },
                    pc,
                );

                let result_reg = self.reg_ref(call_insn.a, next_pc);
                self.emit_assign_reg(result_reg, call_expr);

                // Multi-return: assign Select for each additional result register
                if nresults > 1 {
                    for i in 1..nresults {
                        let select_expr = self.alloc_expr(
                            HirExpr::Select {
                                source: call_expr,
                                index: i as u8,
                            },
                            next_pc,
                        );
                        let reg = self.reg_ref(call_insn.a + i as u8, next_pc);
                        self.emit_assign_reg(reg, select_expr);
                    }
                }

                // If C=0, this call produces MULTRET results
                if call_insn.c == 0 {
                    self.top = Some((call_expr, call_insn.a));
                }

                3 // NAMECALL + AUX + CALL
            }

            // Function calls
            OpCode::Call => {
                let func_expr = self.alloc_expr(HirExpr::Reg(self.reg_ref(insn.a, pc)), pc);
                let nresults = if insn.c == 0 { 0 } else { insn.c - 1 };

                let args = if insn.b == 0 {
                    // MULTRET args: fixed regs from A+1 to top_reg-1, then top expr
                    self.collect_multret_args(insn.a + 1, pc)
                } else {
                    let nargs = insn.b - 1;
                    (0..nargs)
                        .map(|i| {
                            self.alloc_expr(HirExpr::Reg(self.reg_ref(insn.a + 1 + i, pc)), pc)
                        })
                        .collect()
                };

                let builtin_id = std::mem::take(&mut self.pending_fastcall);
                let call_expr = self.alloc_expr(
                    HirExpr::Call {
                        func: func_expr,
                        args,
                        result_count: nresults as u8,
                        builtin_id,
                    },
                    pc,
                );

                let result_reg = self.reg_ref(insn.a, pc);
                self.emit_assign_reg(result_reg, call_expr);

                // Multi-return: assign Select for each additional result register
                if nresults > 1 {
                    for i in 1..nresults {
                        let select_expr = self.alloc_expr(
                            HirExpr::Select {
                                source: call_expr,
                                index: i as u8,
                            },
                            pc,
                        );
                        let reg = self.reg_ref(insn.a + i as u8, pc);
                        self.emit_assign_reg(reg, select_expr);
                    }
                }

                // If C=0, this call produces MULTRET results
                if insn.c == 0 {
                    self.top = Some((call_expr, insn.a));
                }
                1
            }

            // Return
            OpCode::Return => {
                let values = if insn.b == 0 {
                    // MULTRET return: fixed regs A..top_reg-1, then top expr
                    self.collect_multret_args(insn.a, pc)
                } else {
                    let nvals = insn.b - 1;
                    (0..nvals)
                        .map(|i| self.alloc_expr(HirExpr::Reg(self.reg_ref(insn.a + i, pc)), pc))
                        .collect()
                };

                self.hir.cfg[self.current_block].terminator =
                    lantern_hir::cfg::Terminator::Return(values);
                1
            }

            // Jumps
            OpCode::Jump | OpCode::JumpBack | OpCode::JumpX => {
                let offset = if insn.op == OpCode::JumpX {
                    insn.e
                } else {
                    insn.d as i32
                };
                let target = ((pc + 1) as i64 + offset as i64) as usize;
                self.add_jump_edge(target);
                self.hir.cfg[self.current_block].terminator = lantern_hir::cfg::Terminator::Jump;
                if insn.op == OpCode::JumpX {
                    1
                } else {
                    1
                }
            }

            // Conditional branches
            //
            // Convention: fallthrough = then-edge, target = else-edge.
            // The Luau compiler deterministically chooses opcode polarity:
            //   `if cond then`     → JumpIfNot (skip then-body when falsy)
            //   `if not cond then` → JumpIf    (skip then-body when truthy)
            // So we can recover the original condition polarity from the opcode.
            // The condition is the INVERSE of the jump test.
            OpCode::JumpIf => {
                // JumpIf = jump when truthy → original source had `if not cond then`
                let inner = self.alloc_expr(HirExpr::Reg(self.reg_ref(insn.a, pc)), pc);
                let cond = self.alloc_expr(
                    HirExpr::Unary {
                        op: UnOp::Not,
                        operand: inner,
                    },
                    pc,
                );
                let target = ((pc + 1) as i64 + insn.d as i64) as usize;
                self.emit_branch(cond, pc + 1, target, false);
                1
            }

            OpCode::JumpIfNot => {
                // JumpIfNot = jump when falsy → original source had `if cond then`
                let cond = self.alloc_expr(HirExpr::Reg(self.reg_ref(insn.a, pc)), pc);
                let target = ((pc + 1) as i64 + insn.d as i64) as usize;
                self.emit_branch(cond, pc + 1, target, true);
                1
            }

            // Comparison jumps (with AUX)
            //
            // Same convention: fallthrough = then-edge, target = else-edge.
            // The compiler uses the "Not" variant to skip past the then-body:
            //   `if a == b then` → JumpIfNotEq (skip when not equal)
            //   `if a ~= b then` → JumpIfEq   (skip when equal)
            // The condition is the inverse of the jump test.
            OpCode::JumpIfEq
            | OpCode::JumpIfLe
            | OpCode::JumpIfLt
            | OpCode::JumpIfNotEq
            | OpCode::JumpIfNotLe
            | OpCode::JumpIfNotLt => {
                let left = self.alloc_expr(HirExpr::Reg(self.reg_ref(insn.a, pc)), pc);
                let right = self.alloc_expr(
                    HirExpr::Reg(RegRef {
                        register: insn.aux as u8,
                        pc,
                        has_aux: false,
                    }),
                    pc,
                );

                // Invert: the condition is what makes you NOT jump (= stay in then-body)
                let op = match insn.op {
                    OpCode::JumpIfNotEq => BinOp::CompareEq, // source: if a == b
                    OpCode::JumpIfNotLe => BinOp::CompareLe, // source: if a <= b
                    OpCode::JumpIfNotLt => BinOp::CompareLt, // source: if a < b
                    OpCode::JumpIfEq => BinOp::CompareNe,    // source: if a ~= b
                    OpCode::JumpIfLe => BinOp::CompareGt,    // source: if a > b
                    OpCode::JumpIfLt => BinOp::CompareGe,    // source: if a >= b
                    _ => unreachable!(),
                };

                let negated = matches!(insn.op, OpCode::JumpIfNotEq | OpCode::JumpIfNotLe | OpCode::JumpIfNotLt);
                let cond = self.alloc_expr(HirExpr::Binary { op, left, right }, pc);
                let target = ((pc + 1) as i64 + insn.d as i64) as usize;
                self.emit_branch(cond, pc + 2, target, negated);
                2 // AUX
            }

            // Constant comparison jumps (JumpXEqK*)
            //
            // Same convention: fallthrough = then, target = else.
            // not_flag=0: jump when == (source had `if ~= then`), condition = ~=
            // not_flag=1: jump when ~= (source had `if == then`), condition = ==
            // Wait — this is opposite. not_flag inverts the comparison:
            //   not_flag=0: jump if equal     → source had `if x ~= K then`
            //   not_flag=1: jump if not-equal → source had `if x == K then`
            OpCode::JumpXEqKNil | OpCode::JumpXEqKB | OpCode::JumpXEqKN | OpCode::JumpXEqKS => {
                let left = self.alloc_expr(HirExpr::Reg(self.reg_ref(insn.a, pc)), pc);
                let not_flag = (insn.aux >> 31) != 0;

                let right_val = match insn.op {
                    OpCode::JumpXEqKNil => LuaValue::Nil,
                    OpCode::JumpXEqKB => LuaValue::Boolean((insn.aux & 1) != 0),
                    OpCode::JumpXEqKN => {
                        let ki = (insn.aux & 0xFFFFFF) as usize;
                        self.constant_to_value(ki)
                    }
                    OpCode::JumpXEqKS => {
                        let ki = (insn.aux & 0xFFFFFF) as usize;
                        self.constant_to_value(ki)
                    }
                    _ => unreachable!(),
                };

                let right = self.alloc_expr(HirExpr::Literal(right_val), pc);
                // Invert: condition is what keeps us in fallthrough (then-body)
                // not_flag=0 → jump when equal → condition is ~= (stay when not equal)
                // not_flag=1 → jump when not-equal → condition is == (stay when equal)
                let op = if not_flag {
                    BinOp::CompareEq
                } else {
                    BinOp::CompareNe
                };

                let cond = self.alloc_expr(HirExpr::Binary { op, left, right }, pc);
                let target = ((pc + 1) as i64 + insn.d as i64) as usize;
                // not_flag=1 means JumpIfNotEq → negated (wrapping pattern)
                // not_flag=0 means JumpIfEq → non-negated (guard pattern)
                self.emit_branch(cond, pc + 2, target, not_flag);
                2 // AUX
            }

            // Numeric for-loop
            OpCode::ForNPrep => {
                // Register layout: A+0=limit, A+1=step, A+2=index(=user variable)
                let base = insn.a;
                let limit = self.alloc_expr(HirExpr::Reg(self.reg_ref(base, pc)), pc);
                let step = self.alloc_expr(HirExpr::Reg(self.reg_ref(base + 1, pc)), pc);
                let start = self.alloc_expr(HirExpr::Reg(self.reg_ref(base + 2, pc)), pc);

                // Look up loop variable name from debug info — the user-visible
                // variable is at A+2 and its scope starts at the body (pc+1).
                let loop_var_name = self
                    .func
                    .debug
                    .scopes
                    .lookup(base + 2, pc + 1)
                    .map(|s| s.to_string());

                // TODO: elide step when it's trivially 1 (store None)
                let body_pc = pc + 1;
                let exit_pc = ((pc + 1) as i64 + insn.d as i64) as usize;

                self.hir.cfg[self.current_block].terminator =
                    lantern_hir::cfg::Terminator::ForNumPrep {
                        base_reg: base,
                        start,
                        limit,
                        step: Some(step),
                        loop_var_name,
                    };

                // Body edge (LoopBack) and exit edge (LoopExit)
                if let Some(&body_node) = self.block_map.get(&body_pc) {
                    self.hir.cfg.add_edge(
                        self.current_block,
                        body_node,
                        HirEdge {
                            kind: EdgeKind::LoopBack,
                            args: Vec::new(),
                        },
                    );
                }
                if let Some(&exit_node) = self.block_map.get(&exit_pc) {
                    self.hir.cfg.add_edge(
                        self.current_block,
                        exit_node,
                        HirEdge {
                            kind: EdgeKind::LoopExit,
                            args: Vec::new(),
                        },
                    );
                }
                1
            }

            OpCode::ForNLoop => {
                let body_pc = ((pc + 1) as i64 + insn.d as i64) as usize;
                let exit_pc = pc + 1;

                self.hir.cfg[self.current_block].terminator =
                    lantern_hir::cfg::Terminator::ForNumBack { base_reg: insn.a };

                if let Some(&body_node) = self.block_map.get(&body_pc) {
                    self.hir.cfg.add_edge(
                        self.current_block,
                        body_node,
                        HirEdge {
                            kind: EdgeKind::LoopBack,
                            args: Vec::new(),
                        },
                    );
                }
                if let Some(&exit_node) = self.block_map.get(&exit_pc) {
                    self.hir.cfg.add_edge(
                        self.current_block,
                        exit_node,
                        HirEdge {
                            kind: EdgeKind::LoopExit,
                            args: Vec::new(),
                        },
                    );
                }
                1
            }

            // Generic for-loop
            OpCode::ForGPrep | OpCode::ForGPrepINext | OpCode::ForGPrepNext => {
                // FORGPREP sets up iteration state then jumps to FORGLOOP.
                // The iterator expressions are already in registers A+0/A+1/A+2
                // from preceding instructions. We just record them and jump.
                let base = insn.a;
                let iterators = vec![
                    self.alloc_expr(HirExpr::Reg(self.reg_ref(base, pc)), pc),
                    self.alloc_expr(HirExpr::Reg(self.reg_ref(base + 1, pc)), pc),
                    self.alloc_expr(HirExpr::Reg(self.reg_ref(base + 2, pc)), pc),
                ];

                let variant = match insn.op {
                    OpCode::ForGPrepINext => lantern_hir::cfg::ForGenVariant::IPairs,
                    OpCode::ForGPrepNext => lantern_hir::cfg::ForGenVariant::Pairs,
                    _ => lantern_hir::cfg::ForGenVariant::Generic,
                };

                // Store iterators and variant in the block for the structurer to pick up
                self.hir.cfg[self.current_block].for_gen_iterators = Some(iterators);
                self.hir.cfg[self.current_block].for_gen_variant = Some(variant);

                let target = ((pc + 1) as i64 + insn.d as i64) as usize;
                self.add_jump_edge(target);
                self.hir.cfg[self.current_block].terminator = lantern_hir::cfg::Terminator::Jump;
                1
            }

            OpCode::ForGLoop => {
                let base = insn.a;
                let var_count = (insn.aux & 0xFF) as u8;
                let body_pc = ((pc + 1) as i64 + insn.d as i64) as usize;
                let exit_pc = pc + 2; // skip AUX word

                // Look for iterator info and variant from the FORGPREP block that jumps to us.
                let iterators = self.find_forgen_iterators();
                let variant = self.find_forgen_variant();

                // Look up loop variable names from debug info — variables are at
                // A+3..A+2+var_count and their scope starts at the body.
                let loop_var_names: Vec<Option<String>> = (0..var_count)
                    .map(|i| {
                        self.func
                            .debug
                            .scopes
                            .lookup(base + 3 + i, body_pc)
                            .map(|s| s.to_string())
                    })
                    .collect();

                self.hir.cfg[self.current_block].terminator =
                    lantern_hir::cfg::Terminator::ForGenBack {
                        base_reg: base,
                        var_count,
                        iterators,
                        loop_var_names,
                        variant,
                    };

                if let Some(&body_node) = self.block_map.get(&body_pc) {
                    self.hir.cfg.add_edge(
                        self.current_block,
                        body_node,
                        HirEdge {
                            kind: EdgeKind::LoopBack,
                            args: Vec::new(),
                        },
                    );
                }
                if let Some(&exit_node) = self.block_map.get(&exit_pc) {
                    self.hir.cfg.add_edge(
                        self.current_block,
                        exit_node,
                        HirEdge {
                            kind: EdgeKind::LoopExit,
                            args: Vec::new(),
                        },
                    );
                }
                2 // AUX
            }

            // Closures
            OpCode::NewClosure | OpCode::DupClosure => {
                let reg = self.reg_ref(insn.a, pc);
                // NEWCLOSURE: insn.d is the child_protos index directly
                // DUPCLOSURE: insn.d is a constant index → Closure(global_func_idx)
                //   We reverse-lookup through child_protos to get the local proto index
                let proto_id = if insn.op == OpCode::DupClosure {
                    match &self.func.constants[insn.d as usize] {
                        Constant::Closure(global_idx) => self
                            .func
                            .child_protos
                            .iter()
                            .position(|&cp| cp == *global_idx)
                            .unwrap_or(*global_idx),
                        _ => insn.d as usize,
                    }
                } else {
                    insn.d as usize
                };

                // CAPTURE instructions follow immediately
                let mut captures = Vec::new();
                let mut capture_pc = pc + 1;
                while capture_pc < self.func.instructions.len() {
                    let cap_insn = &self.func.instructions[capture_pc];
                    if cap_insn.op != OpCode::Capture {
                        break;
                    }
                    let kind = match cap_insn.a {
                        0 => CaptureKind::Val,
                        1 => CaptureKind::Ref,
                        2 => CaptureKind::Upval,
                        _ => CaptureKind::Val,
                    };
                    let source = match kind {
                        CaptureKind::Val | CaptureKind::Ref => {
                            CaptureSource::Register(self.reg_ref(cap_insn.b, capture_pc))
                        }
                        CaptureKind::Upval => CaptureSource::Upvalue(cap_insn.b),
                    };
                    captures.push(Capture { kind, source });
                    capture_pc += 1;
                }

                let expr = self.alloc_expr(HirExpr::Closure { proto_id, captures }, pc);
                self.emit_assign_reg(reg, expr);
                // Return total PCs consumed: 1 for NEWCLOSURE + N for CAPTUREs
                capture_pc - pc
            }

            OpCode::Capture => {
                // Should be consumed by NewClosure/DupClosure handler
                1
            }

            // Varargs
            OpCode::GetVarArgs => {
                let reg = self.reg_ref(insn.a, pc);
                let expr = self.alloc_expr(HirExpr::VarArg, pc);
                self.emit_assign_reg(reg, expr);

                let nresults = if insn.b == 0 { 0 } else { insn.b - 1 };
                // Multi-capture: assign Select for each additional vararg register
                if nresults > 1 {
                    for i in 1..nresults {
                        let select_expr = self.alloc_expr(
                            HirExpr::Select {
                                source: expr,
                                index: i as u8,
                            },
                            pc,
                        );
                        let r = self.reg_ref(insn.a + i as u8, pc);
                        self.emit_assign_reg(r, select_expr);
                    }
                }

                // B=0 means capture all varargs (MULTRET producer)
                if insn.b == 0 {
                    self.top = Some((expr, insn.a));
                }
                1
            }

            // FASTCALL variants — optimization hints followed by a real CALL.
            // Record the builtin ID so the next CALL carries it.
            OpCode::FastCall => {
                self.pending_fastcall = insn.a;
                1
            }
            OpCode::FastCall1 => {
                self.pending_fastcall = insn.a;
                1
            }
            OpCode::FastCall2 => {
                self.pending_fastcall = insn.a;
                2 // has AUX
            }
            OpCode::FastCall2K => {
                self.pending_fastcall = insn.a;
                2 // has AUX
            }
            OpCode::FastCall3 => {
                self.pending_fastcall = insn.a;
                2 // has AUX
            }
        }
    }
}
