use petgraph::stable_graph::NodeIndex;
use petgraph::Direction;
use rustc_hash::FxHashMap;

use lantern_bytecode::chunk::Chunk;
use lantern_bytecode::constant::Constant;
use lantern_bytecode::function::Function;
use lantern_bytecode::instruction::Instruction;
use lantern_bytecode::opcode::OpCode;

use lantern_hir::arena::ExprId;
use lantern_hir::cfg::{EdgeKind, HirBlock, HirEdge};
use lantern_hir::expr::{Capture, CaptureSource, HirExpr};
use lantern_hir::func::HirFunc;
use lantern_hir::stmt::{HirStmt, LValue};
use lantern_hir::types::{BinOp, CaptureKind, LuaValue, UnOp};
use lantern_hir::var::RegRef;

use crate::block_discovery;

/// Lift a bytecode function into HIR.
///
/// Produces an unstructured CFG with raw register references (RegRef).
/// The constraint solver in the `vars` crate resolves these to VarIds.
pub fn lift_function(chunk: &Chunk, func_index: usize) -> HirFunc {
    let func = &chunk.functions[func_index];
    let mut lifter = Lifter::new(chunk, func, func_index);
    lifter.lift();
    lifter.hir
}

struct Lifter<'a> {
    chunk: &'a Chunk,
    func: &'a Function,
    hir: HirFunc,
    /// Map from block-start PC to CFG node index.
    block_map: FxHashMap<usize, NodeIndex>,
    /// Current block being built.
    current_block: NodeIndex,
    /// MULTRET tracking: when a CALL with C=0 or GETVARARGS with B=0
    /// produces a variable number of results, we record the expression
    /// and the base register. The next MULTRET consumer (CALL B=0,
    /// RETURN B=0, SETLIST C=0) uses this to collect the arguments.
    top: Option<(ExprId, u8)>,
    /// Pending FASTCALL builtin ID: set by FASTCALL* instructions,
    /// consumed by the next CALL instruction. 0 = no pending fastcall.
    pending_fastcall: u8,
    /// Boolean value computation regions detected in the instruction stream.
    /// These regions contain conditional jumps that compute boolean values
    /// rather than creating real control flow branches.
    bool_regions: Vec<crate::bool_regions::BoolRegion>,
    /// Truthiness-based or/and chains (JUMPIF/JUMPIFNOT) detected in the
    /// instruction stream.
    truthy_chains: Vec<crate::bool_regions::TruthyChain>,
}

impl<'a> Lifter<'a> {
    fn new(chunk: &'a Chunk, func: &'a Function, func_index: usize) -> Self {
        let mut hir = HirFunc::new(func_index);
        hir.is_vararg = func.is_vararg;
        hir.num_upvalues = func.num_upvalues;
        hir.name = chunk.get_string(func.debug.func_name_index);
        hir.line_info = func.debug.line_info.clone();
        hir.type_info = func.type_info.clone();

        // Set up upvalue names from debug info
        hir.upvalue_names = func
            .debug
            .upvalue_name_indices
            .iter()
            .map(|&idx| chunk.get_string(idx))
            .collect();

        let entry = hir.entry;
        let mut block_map = FxHashMap::default();
        block_map.insert(0, entry);

        Self {
            chunk,
            func,
            hir,
            block_map,
            current_block: entry,
            top: None,
            pending_fastcall: 0,
            bool_regions: Vec::new(),
            truthy_chains: Vec::new(),
        }
    }

    fn lift(&mut self) {
        let instructions = &self.func.instructions;
        if instructions.is_empty() {
            return;
        }

        // Detect boolean value computation regions before block discovery.
        // These regions contain conditional jumps that compute boolean values
        // (e.g. `x = a == b or a == c`), NOT real control flow branches.
        // Suppressing them prevents false block boundaries.
        let mut suppressed = crate::bool_regions::detect_bool_regions(instructions);
        self.bool_regions = crate::bool_regions::find_bool_regions(instructions);

        // Detect truthiness-based or/and chains (JUMPIF/JUMPIFNOT)
        let (truthy_chains, truthy_suppressed) =
            crate::bool_regions::detect_truthy_chains(instructions);
        self.truthy_chains = truthy_chains;
        suppressed.extend(truthy_suppressed);

        // Discover block boundaries
        let starts = block_discovery::discover_block_starts(instructions, &suppressed);
        let ranges = block_discovery::block_ranges(&starts, instructions.len());

        // Create all blocks in the CFG
        for &start_pc in &starts {
            self.block_map.entry(start_pc).or_insert_with(|| {
                self.hir.cfg.add_node(HirBlock::new())
            });
        }

        // Lift each block
        for (start_pc, end_pc) in ranges {
            let node = self.block_map[&start_pc];
            self.current_block = node;
            self.hir.cfg[node].pc_range = (start_pc, end_pc);
            self.lift_block(start_pc, end_pc);
        }
    }

    fn lift_block(&mut self, start_pc: usize, end_pc: usize) {
        self.top = None; // Reset MULTRET state at block boundary
        let mut pc = start_pc;
        while pc < end_pc {
            // Check if this PC starts a boolean value computation region.
            // If so, lift the entire region as a single expression.
            if let Some(advance) = self.try_lift_bool_region(pc) {
                pc += advance;
                continue;
            }
            // Check if this PC starts a truthiness-based or/and chain.
            if let Some(advance) = self.try_lift_truthy_chain(pc) {
                pc += advance;
                continue;
            }
            let insn = &self.func.instructions[pc];
            let advance = self.lift_instruction(insn, pc);
            pc += advance;
        }

        // If block doesn't end with a terminator, add fallthrough edge
        let block = &self.hir.cfg[self.current_block];
        if matches!(block.terminator, lantern_hir::cfg::Terminator::None) {
            if let Some(&next_node) = self.block_map.get(&end_pc) {
                self.hir.cfg.add_edge(
                    self.current_block,
                    next_node,
                    HirEdge::unconditional(),
                );
                self.hir.cfg[self.current_block].terminator =
                    lantern_hir::cfg::Terminator::Jump;
            }
        }
    }

    /// Lift a single instruction. Returns the number of PCs consumed
    /// (usually 1, but 2 for instructions with AUX).
    fn lift_instruction(&mut self, insn: &Instruction, pc: usize) -> usize {
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
                let expr = self.alloc_expr(
                    HirExpr::Literal(LuaValue::Number(insn.d as f64)),
                    pc,
                );
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
                let table_expr = self.alloc_expr(HirExpr::Reg(self.reg_ref(insn.b, pc)), pc);
                let field = self.string_from_aux(insn.aux);
                let value = self.alloc_expr(HirExpr::Reg(self.reg_ref(insn.a, pc)), pc);
                self.emit_stmt(HirStmt::Assign {
                    target: LValue::Field {
                        table: table_expr,
                        field,
                    },
                    value,
                });
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
                    .map(|r| {
                        self.alloc_expr(HirExpr::Reg(self.reg_ref(r, pc)), pc)
                    })
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
                    },
                    pc,
                );
                self.emit_assign_reg(reg, expr);
                2 // AUX (array size)
            }

            OpCode::DupTable => {
                let reg = self.reg_ref(insn.a, pc);
                // DUPTABLE creates a table from a template constant.
                // For now, emit an empty table — the template is a hash layout hint.
                let expr = self.alloc_expr(
                    HirExpr::Table {
                        array: Vec::new(),
                        hash: Vec::new(),
                    },
                    pc,
                );
                self.emit_assign_reg(reg, expr);
                1
            }

            OpCode::SetList => {
                // SETLIST A B C AUX: table[AUX+1..AUX+C] = R(B)..R(B+C-1)
                // We don't restructure this into the table constructor yet —
                // that's done in the patterns crate.
                // Consume MULTRET top if C=0 to prevent stale state.
                if insn.c == 0 {
                    self.top.take();
                }
                // TODO: record SETLIST for pattern matching
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
                            self.alloc_expr(
                                HirExpr::Reg(self.reg_ref(insn.a + 1 + i, pc)),
                                pc,
                            )
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
                        .map(|i| {
                            self.alloc_expr(
                                HirExpr::Reg(self.reg_ref(insn.a + i, pc)),
                                pc,
                            )
                        })
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
                self.hir.cfg[self.current_block].terminator =
                    lantern_hir::cfg::Terminator::Jump;
                if insn.op == OpCode::JumpX { 1 } else { 1 }
            }

            // Conditional branches
            OpCode::JumpIf => {
                let cond = self.alloc_expr(HirExpr::Reg(self.reg_ref(insn.a, pc)), pc);
                let target = ((pc + 1) as i64 + insn.d as i64) as usize;
                self.emit_branch(cond, target, pc + 1);
                1
            }

            OpCode::JumpIfNot => {
                // JumpIfNot: jump if falsy. We negate: branch true = fallthrough, false = target
                let inner = self.alloc_expr(HirExpr::Reg(self.reg_ref(insn.a, pc)), pc);
                let cond = self.alloc_expr(HirExpr::Unary { op: UnOp::Not, operand: inner }, pc);
                let target = ((pc + 1) as i64 + insn.d as i64) as usize;
                self.emit_branch(cond, target, pc + 1);
                1
            }

            // Comparison jumps (with AUX)
            OpCode::JumpIfEq
            | OpCode::JumpIfLe
            | OpCode::JumpIfLt
            | OpCode::JumpIfNotEq
            | OpCode::JumpIfNotLe
            | OpCode::JumpIfNotLt => {
                let left = self.alloc_expr(HirExpr::Reg(self.reg_ref(insn.a, pc)), pc);
                let right = self.alloc_expr(
                    HirExpr::Reg(RegRef { register: insn.aux as u8, pc }),
                    pc,
                );

                let op = match insn.op {
                    OpCode::JumpIfEq => BinOp::CompareEq,
                    OpCode::JumpIfLe => BinOp::CompareLe,
                    OpCode::JumpIfLt => BinOp::CompareLt,
                    OpCode::JumpIfNotEq => BinOp::CompareNe,
                    OpCode::JumpIfNotLe => BinOp::CompareGt, // not(a<=b) = a>b
                    OpCode::JumpIfNotLt => BinOp::CompareGe, // not(a<b) = a>=b
                    _ => unreachable!(),
                };

                let cond = self.alloc_expr(HirExpr::Binary { op, left, right }, pc);
                let target = ((pc + 1) as i64 + insn.d as i64) as usize;
                self.emit_branch(cond, target, pc + 2);
                2 // AUX
            }

            // Constant comparison jumps
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
                let base_op = BinOp::CompareEq;
                let op = if not_flag { BinOp::CompareNe } else { base_op };

                let cond = self.alloc_expr(HirExpr::Binary { op, left, right }, pc);
                let target = ((pc + 1) as i64 + insn.d as i64) as usize;
                self.emit_branch(cond, target, pc + 2);
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
                let loop_var_name = self.func.debug.scopes
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
                        HirEdge { kind: EdgeKind::LoopBack, args: Vec::new() },
                    );
                }
                if let Some(&exit_node) = self.block_map.get(&exit_pc) {
                    self.hir.cfg.add_edge(
                        self.current_block,
                        exit_node,
                        HirEdge { kind: EdgeKind::LoopExit, args: Vec::new() },
                    );
                }
                1
            }

            OpCode::ForNLoop => {
                let body_pc = ((pc + 1) as i64 + insn.d as i64) as usize;
                let exit_pc = pc + 1;

                self.hir.cfg[self.current_block].terminator =
                    lantern_hir::cfg::Terminator::ForNumBack {
                        base_reg: insn.a,
                    };

                if let Some(&body_node) = self.block_map.get(&body_pc) {
                    self.hir.cfg.add_edge(
                        self.current_block,
                        body_node,
                        HirEdge { kind: EdgeKind::LoopBack, args: Vec::new() },
                    );
                }
                if let Some(&exit_node) = self.block_map.get(&exit_pc) {
                    self.hir.cfg.add_edge(
                        self.current_block,
                        exit_node,
                        HirEdge { kind: EdgeKind::LoopExit, args: Vec::new() },
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
                self.hir.cfg[self.current_block].terminator =
                    lantern_hir::cfg::Terminator::Jump;
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
                        self.func.debug.scopes
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
                        HirEdge { kind: EdgeKind::LoopBack, args: Vec::new() },
                    );
                }
                if let Some(&exit_node) = self.block_map.get(&exit_pc) {
                    self.hir.cfg.add_edge(
                        self.current_block,
                        exit_node,
                        HirEdge { kind: EdgeKind::LoopExit, args: Vec::new() },
                    );
                }
                2 // AUX
            }

            // Closures
            OpCode::NewClosure | OpCode::DupClosure => {
                let reg = self.reg_ref(insn.a, pc);
                let proto_id = insn.d as usize;

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

                let expr = self.alloc_expr(
                    HirExpr::Closure { proto_id, captures },
                    pc,
                );
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

    // ---- Helpers ----

    fn reg_ref(&self, register: u8, pc: usize) -> RegRef {
        RegRef { register, pc }
    }

    fn alloc_expr(&mut self, expr: HirExpr, pc: usize) -> ExprId {
        let id = self.hir.exprs.alloc(expr);
        self.hir.set_origin_expr(id, pc);
        id
    }

    fn emit_stmt(&mut self, stmt: HirStmt) {
        self.hir.cfg[self.current_block].stmts.push(stmt);
    }

    /// Collect arguments for a MULTRET consumer.
    ///
    /// When B=0 in CALL/RETURN, the arguments extend from `from_reg` up to
    /// the register where the previous MULTRET producer placed its results,
    /// with the MULTRET expression itself as the final argument.
    fn collect_multret_args(&mut self, from_reg: u8, pc: usize) -> Vec<ExprId> {
        let mut args = Vec::new();
        if let Some((top_expr, top_reg)) = self.top.take() {
            // Collect fixed registers between from_reg and top_reg
            for r in from_reg..top_reg {
                args.push(self.alloc_expr(HirExpr::Reg(self.reg_ref(r, pc)), pc));
            }
            // The MULTRET expression is the last argument
            args.push(top_expr);
        }
        args
    }

    fn emit_assign_reg(&mut self, reg: RegRef, value: ExprId) {
        self.emit_stmt(HirStmt::RegAssign {
            target: reg,
            value,
        });
    }

    /// Find iterator expressions from a predecessor FORGPREP block.
    /// FORGPREP stores its iterators in the block, then jumps to FORGLOOP.
    /// Assumes exactly one FORGPREP predecessor per FORGLOOP (Luau compiler invariant).
    fn find_forgen_iterators(&self) -> Vec<ExprId> {
        for pred in self.hir.cfg.neighbors_directed(self.current_block, Direction::Incoming) {
            if let Some(iters) = &self.hir.cfg[pred].for_gen_iterators {
                return iters.clone();
            }
        }
        Vec::new()
    }

    fn find_forgen_variant(&self) -> lantern_hir::cfg::ForGenVariant {
        for pred in self.hir.cfg.neighbors_directed(self.current_block, Direction::Incoming) {
            if let Some(variant) = self.hir.cfg[pred].for_gen_variant {
                return variant;
            }
        }
        lantern_hir::cfg::ForGenVariant::Generic
    }

    fn lift_constant(&mut self, index: usize, pc: usize) -> ExprId {
        let value = self.constant_to_value(index);
        self.alloc_expr(HirExpr::Literal(value), pc)
    }

    fn constant_to_value(&self, index: usize) -> LuaValue {
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
    fn string_from_aux(&self, aux: u32) -> String {
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

    fn lift_import(&mut self, aux: u32, pc: usize) -> ExprId {
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
            expr = self.alloc_expr(HirExpr::FieldAccess { table: expr, field: field1 }, pc);
        }

        if count >= 3 {
            let k2 = (aux & 0x3FF) as usize;
            let field2 = match &self.func.constants[k2] {
                Constant::String(idx) => {
                    String::from_utf8_lossy(&self.chunk.string_table[*idx - 1]).to_string()
                }
                _ => format!("__field_{}", k2),
            };
            expr = self.alloc_expr(HirExpr::FieldAccess { table: expr, field: field2 }, pc);
        }

        expr
    }

    fn lift_binary(&mut self, op: BinOp, insn: &Instruction, pc: usize, rhs_const: bool) -> usize {
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

    fn lift_binary_rk(&mut self, op: BinOp, insn: &Instruction, pc: usize) -> usize {
        // Reverse: A = K[B] op C
        let reg = self.reg_ref(insn.a, pc);
        let left = self.lift_constant(insn.b as usize, pc);
        let right = self.alloc_expr(HirExpr::Reg(self.reg_ref(insn.c, pc)), pc);
        let expr = self.alloc_expr(HirExpr::Binary { op, left, right }, pc);
        self.emit_assign_reg(reg, expr);
        1
    }

    fn lift_unary(&mut self, op: UnOp, insn: &Instruction, pc: usize) -> usize {
        let reg = self.reg_ref(insn.a, pc);
        let operand = self.alloc_expr(HirExpr::Reg(self.reg_ref(insn.b, pc)), pc);
        let expr = self.alloc_expr(HirExpr::Unary { op, operand }, pc);
        self.emit_assign_reg(reg, expr);
        1
    }

    fn add_jump_edge(&mut self, target_pc: usize) {
        if let Some(&target_node) = self.block_map.get(&target_pc) {
            self.hir.cfg.add_edge(
                self.current_block,
                target_node,
                HirEdge::unconditional(),
            );
        }
    }

    fn emit_branch(&mut self, condition: ExprId, then_pc: usize, else_pc: usize) {
        self.hir.cfg[self.current_block].terminator =
            lantern_hir::cfg::Terminator::Branch { condition };

        if let Some(&then_node) = self.block_map.get(&then_pc) {
            self.hir.cfg.add_edge(
                self.current_block,
                then_node,
                HirEdge::then_edge(),
            );
        }
        if let Some(&else_node) = self.block_map.get(&else_pc) {
            self.hir.cfg.add_edge(
                self.current_block,
                else_node,
                HirEdge::else_edge(),
            );
        }
    }

    /// Try to lift a boolean value computation region starting at `pc`.
    ///
    /// If `pc` is the start of a detected boolean region, lifts the entire
    /// region as a compound boolean expression and returns the number of
    /// PCs consumed. Otherwise returns None.
    fn try_lift_bool_region(&mut self, pc: usize) -> Option<usize> {
        // Find a region that starts at this PC
        let region_idx = self.bool_regions.iter().position(|r| r.start_pc == pc)?;

        // Copy fields to avoid borrowing self.bool_regions while we mutate self.
        let false_pc = self.bool_regions[region_idx].false_pc;
        let end_pc = self.bool_regions[region_idx].end_pc;
        let result_reg = self.bool_regions[region_idx].result_reg;
        let is_or_chain = self.bool_regions[region_idx].is_or_chain;

        let instructions = &self.func.instructions;

        // Collect all conditional jump conditions within the region.
        // Each jump contributes an operand to the compound boolean expression.
        //
        // We process instructions sequentially. Non-jump instructions (LOADB pre-inits,
        // GETIMPORT operand loads, etc.) are lifted normally for their side effects
        // (they load values into registers that the comparisons reference).
        // Conditional jumps are NOT lifted as branches — instead we extract their
        // comparison conditions.
        let mut conditions: Vec<ExprId> = Vec::new();
        let mut scan_pc = pc;

        while scan_pc < false_pc {
            let insn = &instructions[scan_pc];

            // Check if this is a conditional jump inside the boolean region
            if let Some(cond_expr) = self.lift_bool_condition(insn, scan_pc) {
                conditions.push(cond_expr);
                // Advance past AUX word if needed
                scan_pc += if crate::bool_regions::has_aux_word(insn.op) { 2 } else { 1 };
                continue;
            }

            // Not a conditional jump — lift the instruction normally.
            // This handles LOADB (pre-inits), GETIMPORT, MOVE, etc.
            // We skip LOADB pre-inits for the result register since we're
            // replacing the entire computation.
            if insn.op == OpCode::LoadB && insn.a == result_reg && insn.c == 0 {
                // Skip pre-init LOADB for the result register — it's part
                // of the boolean pattern, not a real assignment.
                scan_pc += 1;
                continue;
            }

            let advance = self.lift_instruction(insn, scan_pc);
            scan_pc += advance;
        }

        // Determine the combining operator.
        // OR-chain: pre-init=true, conditions OR'd
        // AND-chain: pre-init=false, conditions AND'd
        // Single comparison or unknown: no combining needed
        let chain_op = match is_or_chain {
            Some(true) => BinOp::Or,
            Some(false) => BinOp::And,
            None => BinOp::Or, // default for single comparison (doesn't matter, only 1 condition)
        };

        // Build the compound expression.
        let result_expr = if conditions.is_empty() {
            // Degenerate: no conditions found. Emit a literal.
            self.alloc_expr(HirExpr::Literal(LuaValue::Boolean(true)), false_pc)
        } else if conditions.len() == 1 {
            conditions[0]
        } else {
            // Build left-to-right chain: ((a op b) op c)
            let mut combined = conditions[0];
            for &cond in &conditions[1..] {
                combined = self.alloc_expr(
                    HirExpr::Binary {
                        op: chain_op,
                        left: combined,
                        right: cond,
                    },
                    false_pc,
                );
            }
            combined
        };

        // Emit the assignment: result_reg = <compound boolean expression>
        let reg = self.reg_ref(result_reg, false_pc);
        self.emit_assign_reg(reg, result_expr);

        // Return PCs consumed: from start through the LOADB true at true_pc
        Some(end_pc - pc)
    }

    /// Try to lift a truthiness-based or/and chain starting at `pc`.
    ///
    /// Pattern for `a or b or c`:
    ///   GETIMPORT R2, a; JUMPIF R2, +N  (short-circuit if truthy)
    ///   GETIMPORT R2, b; JUMPIF R2, +K  (short-circuit if truthy)
    ///   GETIMPORT R2, c                 (last value, falls through)
    ///   <join point>: use R2
    ///
    /// Each segment between jumps loads a value into the chain register.
    /// We lift those loads normally, then capture the value as an operand
    /// in the compound expression.
    fn try_lift_truthy_chain(&mut self, pc: usize) -> Option<usize> {
        // Find a chain whose first jump is at this PC.
        // The chain's jump_pcs[0] is the first JUMPIF/JUMPIFNOT.
        // But the value load BEFORE the first jump may start earlier.
        // For our detection, the chain `start_pc` is the first jump PC
        // (since find_truthy_chain_start currently returns the jump itself).
        let chain_idx = self.truthy_chains.iter().position(|c| {
            c.start_pc == pc
        })?;

        // Copy fields to avoid borrow issues
        let end_pc = self.truthy_chains[chain_idx].end_pc;
        let result_reg = self.truthy_chains[chain_idx].result_reg;
        let is_or = self.truthy_chains[chain_idx].is_or;
        let jump_pcs = self.truthy_chains[chain_idx].jump_pcs.clone();

        let chain_op = if is_or { BinOp::Or } else { BinOp::And };

        // Process each segment. A segment is the instructions between
        // (previous_jump+1) and the current jump (exclusive).
        // For the first segment, instructions before the first jump
        // should already have been lifted by the normal block lifting
        // (they precede the chain start_pc). BUT: the value load for the
        // first JUMPIF operand may have been lifted as a RegAssign already
        // in the current block. We need to capture that.

        let mut operands: Vec<ExprId> = Vec::new();
        let instructions = &self.func.instructions;

        // The first operand: the value in the chain register was loaded
        // by instructions already lifted before this PC. We reference the
        // register state as it stands.
        // Actually — the first JUMPIF is at jump_pcs[0] = pc (the start).
        // The value load for R2 happened before pc. Those instructions were
        // already lifted as normal statements. We need to pop the last
        // RegAssign to R2 from the current block.
        let first_operand = self.pop_last_reg_assign(result_reg);
        operands.push(first_operand.unwrap_or_else(|| {
            // Fallback: reference the register directly
            self.alloc_expr(HirExpr::Reg(self.reg_ref(result_reg, pc)), pc)
        }));

        // Now process segments between consecutive jumps
        for i in 0..jump_pcs.len() {
            let jump_pc = jump_pcs[i];
            // Advance past the jump itself
            let segment_start = jump_pc + 1;
            let segment_end = if i + 1 < jump_pcs.len() {
                jump_pcs[i + 1]
            } else {
                // After the last jump, lift up to end_pc (the join point)
                end_pc
            };

            // Lift instructions in this segment
            let mut seg_pc = segment_start;
            while seg_pc < segment_end {
                let insn = &instructions[seg_pc];

                // Skip JUMPIF/JUMPIFNOT — already handled as chain jumps
                if matches!(insn.op, OpCode::JumpIf | OpCode::JumpIfNot) && insn.a == result_reg {
                    seg_pc += 1;
                    continue;
                }

                let advance = self.lift_instruction(insn, seg_pc);
                seg_pc += advance;
            }

            // The segment should have loaded a value into result_reg.
            // Pop the last RegAssign as the next operand.
            if let Some(operand) = self.pop_last_reg_assign(result_reg) {
                operands.push(operand);
            }
        }

        // Build compound expression
        if operands.is_empty() {
            return None; // shouldn't happen
        }

        let result_expr = if operands.len() == 1 {
            operands[0]
        } else {
            let mut combined = operands[0];
            for &op in &operands[1..] {
                combined = self.alloc_expr(
                    HirExpr::Binary {
                        op: chain_op,
                        left: combined,
                        right: op,
                    },
                    pc,
                );
            }
            combined
        };

        // Emit the assignment
        let reg = self.reg_ref(result_reg, pc);
        self.emit_assign_reg(reg, result_expr);

        Some(end_pc - pc)
    }

    /// Pop the last RegAssign to `register` from the current block's statements.
    /// Returns the assigned value expression, or None if no such statement found.
    fn pop_last_reg_assign(&mut self, register: u8) -> Option<ExprId> {
        let stmts = &mut self.hir.cfg[self.current_block].stmts;
        // Search from the end for the most recent RegAssign to this register
        for i in (0..stmts.len()).rev() {
            if let HirStmt::RegAssign { target, value } = &stmts[i] {
                if target.register == register {
                    let expr = *value;
                    stmts.remove(i);
                    return Some(expr);
                }
            }
            // Don't search too far back — only the most recent few statements
            if stmts.len() - i > 3 {
                break;
            }
        }
        None
    }

    /// Extract a comparison expression from a conditional jump instruction
    /// inside a boolean region. Returns the condition as a HirExpr if this
    /// is a recognized conditional jump, None otherwise.
    fn lift_bool_condition(&mut self, insn: &Instruction, pc: usize) -> Option<ExprId> {
        match insn.op {
            OpCode::JumpIfEq
            | OpCode::JumpIfLe
            | OpCode::JumpIfLt
            | OpCode::JumpIfNotEq
            | OpCode::JumpIfNotLe
            | OpCode::JumpIfNotLt => {
                let left = self.alloc_expr(HirExpr::Reg(self.reg_ref(insn.a, pc)), pc);
                let right = self.alloc_expr(
                    HirExpr::Reg(RegRef { register: insn.aux as u8, pc }),
                    pc,
                );

                // Extract the POSITIVE comparison condition.
                //
                // OR-chain uses positive jumps (JUMPIFEQ/LE/LT) → extract as-is
                // AND-chain uses negated jumps (JUMPIFNOTEQ/NOTLE/NOTLT) → negate back
                //
                // In both cases we want the positive comparison that the source
                // code expresses as an operand.
                let op = match insn.op {
                    OpCode::JumpIfEq => BinOp::CompareEq,
                    OpCode::JumpIfLe => BinOp::CompareLe,
                    OpCode::JumpIfLt => BinOp::CompareLt,
                    OpCode::JumpIfNotEq => BinOp::CompareEq,  // not(!=) = ==
                    OpCode::JumpIfNotLe => BinOp::CompareLe,  // not(not(<=)) = <=
                    OpCode::JumpIfNotLt => BinOp::CompareLt,  // not(not(<)) = <
                    _ => unreachable!(),
                };

                Some(self.alloc_expr(HirExpr::Binary { op, left, right }, pc))
            }

            OpCode::JumpIf | OpCode::JumpIfNot => {
                let operand = self.alloc_expr(HirExpr::Reg(self.reg_ref(insn.a, pc)), pc);
                if insn.op == OpCode::JumpIfNot {
                    let negated = self.alloc_expr(
                        HirExpr::Unary { op: UnOp::Not, operand },
                        pc,
                    );
                    Some(negated)
                } else {
                    Some(operand)
                }
            }

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
                // For bool regions, use the positive comparison
                let op = if not_flag { BinOp::CompareNe } else { BinOp::CompareEq };
                Some(self.alloc_expr(HirExpr::Binary { op, left, right }, pc))
            }

            _ => None,
        }
    }

}
