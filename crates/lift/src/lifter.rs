use petgraph::stable_graph::NodeIndex;
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
}

impl<'a> Lifter<'a> {
    fn new(chunk: &'a Chunk, func: &'a Function, func_index: usize) -> Self {
        let mut hir = HirFunc::new(func_index);
        hir.is_vararg = func.is_vararg;
        hir.num_upvalues = func.num_upvalues;
        hir.name = chunk.get_string(func.debug.func_name_index);

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
        }
    }

    fn lift(&mut self) {
        let instructions = &self.func.instructions;
        if instructions.is_empty() {
            return;
        }

        // Discover block boundaries
        let starts = block_discovery::discover_block_starts(instructions);
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
        let mut pc = start_pc;
        while pc < end_pc {
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
                // For now just record it as a statement.
                let _table_reg = insn.a;
                let _source_start = insn.b;
                let _count = insn.c; // 0 = MULTRET
                let _start_index = insn.aux;
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

                let nargs = if call_insn.b == 0 { 0 } else { call_insn.b - 1 };
                let nresults = call_insn.c;

                // Arguments start at A+2 (A = func, A+1 = self)
                let args: Vec<ExprId> = (0..nargs.saturating_sub(1))
                    .map(|i| {
                        self.alloc_expr(
                            HirExpr::Reg(self.reg_ref(call_insn.a + 2 + i, next_pc)),
                            next_pc,
                        )
                    })
                    .collect();

                let call_expr = self.alloc_expr(
                    HirExpr::MethodCall {
                        object: obj,
                        method,
                        args,
                        result_count: nresults,
                    },
                    pc,
                );

                let result_reg = self.reg_ref(call_insn.a, next_pc);
                if nresults == 1 || nresults == 0 {
                    // Single result or used as statement
                    self.emit_assign_reg(result_reg, call_expr);
                } else {
                    self.emit_assign_reg(result_reg, call_expr);
                }

                3 // NAMECALL + AUX + CALL
            }

            // Function calls
            OpCode::Call => {
                let func_expr = self.alloc_expr(HirExpr::Reg(self.reg_ref(insn.a, pc)), pc);
                let nargs = if insn.b == 0 { 0 } else { insn.b - 1 };
                let nresults = insn.c;

                let args: Vec<ExprId> = (0..nargs)
                    .map(|i| {
                        self.alloc_expr(
                            HirExpr::Reg(self.reg_ref(insn.a + 1 + i, pc)),
                            pc,
                        )
                    })
                    .collect();

                let call_expr = self.alloc_expr(
                    HirExpr::Call {
                        func: func_expr,
                        args,
                        result_count: nresults,
                    },
                    pc,
                );

                let result_reg = self.reg_ref(insn.a, pc);
                self.emit_assign_reg(result_reg, call_expr);
                1
            }

            // Return
            OpCode::Return => {
                let nvals = if insn.b == 0 {
                    // MULTRET — for now treat as 0 returns
                    // TODO: handle MULTRET properly
                    0
                } else {
                    insn.b - 1
                };

                let values: Vec<ExprId> = (0..nvals)
                    .map(|i| {
                        self.alloc_expr(
                            HirExpr::Reg(self.reg_ref(insn.a + i, pc)),
                            pc,
                        )
                    })
                    .collect();

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

            // For loops
            OpCode::ForNPrep => {
                // Numeric for prep: registers are [limit, step, index, variable]
                // Jump to FORNLOOP if loop should execute, or skip
                let target = ((pc + 1) as i64 + insn.d as i64) as usize;
                // For now, just emit the jump edges. The patterns crate will
                // recognize the FORNPREP/FORNLOOP pair.
                self.add_conditional_edges(pc + 1, target);
                1
            }

            OpCode::ForNLoop => {
                let target = ((pc + 1) as i64 + insn.d as i64) as usize;
                self.add_conditional_edges(target, pc + 1);
                1
            }

            OpCode::ForGPrep | OpCode::ForGPrepINext | OpCode::ForGPrepNext => {
                let target = ((pc + 1) as i64 + insn.d as i64) as usize;
                self.add_jump_edge(target);
                self.hir.cfg[self.current_block].terminator =
                    lantern_hir::cfg::Terminator::Jump;
                1
            }

            OpCode::ForGLoop => {
                let target = ((pc + 1) as i64 + insn.d as i64) as usize;
                // Back-edge to loop body, exit to after loop
                // AUX has var count in low 8 bits
                self.add_conditional_edges(target, pc + 1);
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
                1
            }

            // FASTCALL variants — these are optimization hints followed by a real CALL.
            // We skip them and let the CALL handle the actual semantics.
            OpCode::FastCall => {
                // FASTCALL A C: skip C instructions to get to the CALL
                // The CALL following handles everything
                1
            }
            OpCode::FastCall1 => 1,
            OpCode::FastCall2 => 2, // has AUX
            OpCode::FastCall2K => 2, // has AUX
            OpCode::FastCall3 => 2, // has AUX

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

    fn emit_assign_reg(&mut self, _reg: RegRef, value: ExprId) {
        // Before variable recovery, we emit assignments to register references.
        // The vars crate will convert these to proper VarId assignments.
        // For now, encode as raw assignment.
        // We use a special internal representation: store as ExprStmt wrapping the assignment.
        // The actual assignment target will be resolved later.
        self.emit_stmt(HirStmt::ExprStmt(value));
        // TODO: track that `value` is assigned to `reg` for constraint generation
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

    fn string_from_aux(&self, aux: u32) -> String {
        let idx = aux as usize;
        if idx > 0 && idx <= self.chunk.string_table.len() {
            String::from_utf8_lossy(&self.chunk.string_table[idx - 1]).to_string()
        } else {
            format!("__unknown_{}", idx)
        }
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

    fn add_conditional_edges(&mut self, then_pc: usize, else_pc: usize) {
        // Placeholder condition — will be resolved by pattern matching
        let cond = self.alloc_expr(HirExpr::Literal(LuaValue::Boolean(true)), 0);
        self.hir.cfg[self.current_block].terminator =
            lantern_hir::cfg::Terminator::Branch { condition: cond };

        if let Some(&then_node) = self.block_map.get(&then_pc) {
            self.hir.cfg.add_edge(
                self.current_block,
                then_node,
                HirEdge { kind: EdgeKind::LoopBack, args: Vec::new() },
            );
        }
        if let Some(&else_node) = self.block_map.get(&else_pc) {
            self.hir.cfg.add_edge(
                self.current_block,
                else_node,
                HirEdge { kind: EdgeKind::LoopExit, args: Vec::new() },
            );
        }
    }
}
