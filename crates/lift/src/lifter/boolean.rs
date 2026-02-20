use lantern_bytecode::instruction::Instruction;
use lantern_bytecode::opcode::OpCode;

use lantern_hir::arena::ExprId;
use lantern_hir::expr::HirExpr;
use lantern_hir::types::{BinOp, LuaValue, UnOp};
use lantern_hir::var::RegRef;

impl<'a> super::Lifter<'a> {
    /// Try to lift a boolean value computation region starting at `pc`.
    ///
    /// If `pc` is the start of a detected boolean region, lifts the entire
    /// region as a compound boolean expression and returns the number of
    /// PCs consumed. Otherwise returns None.
    pub(super) fn try_lift_bool_region(&mut self, pc: usize) -> Option<usize> {
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
                // For JumpXEqK* in AND chains, bail-out jumps (target==end_pc)
                // need the condition negated. Unlike JumpIfEq/JumpIfNotEq which
                // encode direction in the opcode, JumpXEqK* uses the same form
                // for both chain types — we disambiguate via jump target.
                let cond_expr = if matches!(insn.op,
                    OpCode::JumpXEqKNil | OpCode::JumpXEqKB |
                    OpCode::JumpXEqKN | OpCode::JumpXEqKS)
                {
                    let target = ((scan_pc + 1) as i64 + insn.d as i64) as usize;
                    if target == end_pc && is_or_chain == Some(false) {
                        // AND chain bail-out: source condition is the negation
                        // of the jump test. Flip Eq↔Ne.
                        self.negate_comparison(cond_expr, scan_pc)
                    } else {
                        cond_expr
                    }
                } else {
                    cond_expr
                };
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
        // Use end_pc - 1 (the true LoadB) as the def PC, so that pc+1 = end_pc
        // matches the scope start for the variable being assigned. Using false_pc
        // would be 2 PCs before the scope start, missing the +1 lookup.
        let def_pc = end_pc - 1;
        let reg = self.reg_ref(result_reg, def_pc);
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
    pub(super) fn try_lift_truthy_chain(&mut self, pc: usize) -> Option<usize> {
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

    /// Try to lift a compound `a and b or c` ternary starting at `pc`.
    ///
    /// Pattern:
    /// ```text
    /// JumpIfNot Ra, +N       → fallback_pc  (if a falsy, skip to c)
    /// [compute b into Rb]
    /// JumpIf Rb, +M          → join_pc      (if b truthy, skip c)
    /// [compute c into Rb]    ← fallback_pc
    /// <join>                 ← join_pc: use Rb
    /// ```
    ///
    /// Produces: `Rb = a and b or c`
    pub(super) fn try_lift_and_or_ternary(&mut self, pc: usize) -> Option<usize> {
        let ternary_idx = self.and_or_ternaries.iter().position(|t| t.and_jump_pc == pc)?;

        let and_jump_pc = self.and_or_ternaries[ternary_idx].and_jump_pc;
        let or_jump_pc = self.and_or_ternaries[ternary_idx].or_jump_pc;
        let fallback_pc = self.and_or_ternaries[ternary_idx].fallback_pc;
        let join_pc = self.and_or_ternaries[ternary_idx].join_pc;
        let and_reg = self.and_or_ternaries[ternary_idx].and_reg;
        let result_reg = self.and_or_ternaries[ternary_idx].result_reg;
        let is_comparison = self.and_or_ternaries[ternary_idx].is_comparison;

        // The "a" operand: for comparison jumps, extract the condition from
        // the jump instruction itself. For truthiness jumps, pop the last
        // RegAssign to and_reg.
        let a_operand = if is_comparison {
            let insn = &self.func.instructions[pc];
            self.lift_bool_condition(insn, pc).unwrap_or_else(|| {
                self.alloc_expr(HirExpr::Reg(self.reg_ref(and_reg, pc)), pc)
            })
        } else {
            self.pop_last_reg_assign(and_reg).unwrap_or_else(|| {
                self.alloc_expr(HirExpr::Reg(self.reg_ref(and_reg, pc)), pc)
            })
        };

        // Lift the "b" part: instructions between and_jump+1 (skipping AUX) and or_jump
        let b_start = if is_comparison { and_jump_pc + 2 } else { and_jump_pc + 1 };
        let mut seg_pc = b_start;
        while seg_pc < or_jump_pc {
            let insn = &self.func.instructions[seg_pc];
            let advance = self.lift_instruction(insn, seg_pc);
            seg_pc += advance;
        }
        // The "b" operand: the value in result_reg loaded by the b-segment
        let b_operand = self.pop_last_reg_assign(result_reg).unwrap_or_else(|| {
            self.alloc_expr(HirExpr::Reg(self.reg_ref(result_reg, or_jump_pc)), or_jump_pc)
        });

        // Lift the "c" part: instructions between fallback_pc and join_pc
        seg_pc = fallback_pc;
        while seg_pc < join_pc {
            let insn = &self.func.instructions[seg_pc];
            let advance = self.lift_instruction(insn, seg_pc);
            seg_pc += advance;
        }
        // The "c" operand: the value in result_reg loaded by the c-segment
        let c_operand = self.pop_last_reg_assign(result_reg).unwrap_or_else(|| {
            self.alloc_expr(HirExpr::Reg(self.reg_ref(result_reg, fallback_pc)), fallback_pc)
        });

        // Build: a and b or c → Binary(Or, Binary(And, a, b), c)
        let and_expr = self.alloc_expr(
            HirExpr::Binary {
                op: BinOp::And,
                left: a_operand,
                right: b_operand,
            },
            pc,
        );
        let result_expr = self.alloc_expr(
            HirExpr::Binary {
                op: BinOp::Or,
                left: and_expr,
                right: c_operand,
            },
            pc,
        );

        // Emit: result_reg = a and b or c
        let reg = self.reg_ref(result_reg, pc);
        self.emit_assign_reg(reg, result_expr);

        Some(join_pc - pc)
    }

    /// Try to lift a simple conditional value ternary starting at `pc`.
    ///
    /// Pattern:
    /// ```text
    /// JumpIfNot Ra, +N         → false_val_pc
    /// [load true value into Rb]
    /// Jump +M                  → join_pc
    /// [load false value into Rb]  ← false_val_pc
    /// <join>                      ← join_pc
    /// ```
    ///
    /// Produces: `Rb = Ra and true_val or false_val`
    pub(super) fn try_lift_value_ternary(&mut self, pc: usize) -> Option<usize> {
        let idx = self.value_ternaries.iter().position(|t| t.jump_pc == pc)?;

        let jump_pc = self.value_ternaries[idx].jump_pc;
        let skip_jump_pc = self.value_ternaries[idx].skip_jump_pc;
        let false_val_pc = self.value_ternaries[idx].false_val_pc;
        let join_pc = self.value_ternaries[idx].join_pc;
        let cond_reg = self.value_ternaries[idx].cond_reg;
        let result_reg = self.value_ternaries[idx].result_reg;
        let is_comparison = self.value_ternaries[idx].is_comparison;

        // The condition operand: for comparison jumps, extract from the jump
        // instruction itself. For truthiness jumps, pop the last RegAssign.
        let cond_operand = if is_comparison {
            let insn = &self.func.instructions[pc];
            self.lift_bool_condition(insn, pc).unwrap_or_else(|| {
                self.alloc_expr(HirExpr::Reg(self.reg_ref(cond_reg, pc)), pc)
            })
        } else {
            self.pop_last_reg_assign(cond_reg).unwrap_or_else(|| {
                self.alloc_expr(HirExpr::Reg(self.reg_ref(cond_reg, pc)), pc)
            })
        };

        // Lift the true-value instructions (skip AUX word for comparison jumps)
        let true_start = if is_comparison { jump_pc + 2 } else { jump_pc + 1 };
        let mut seg_pc = true_start;
        while seg_pc < skip_jump_pc {
            let insn = &self.func.instructions[seg_pc];
            let advance = self.lift_instruction(insn, seg_pc);
            seg_pc += advance;
        }
        let true_operand = self.pop_last_reg_assign(result_reg).unwrap_or_else(|| {
            self.alloc_expr(HirExpr::Reg(self.reg_ref(result_reg, skip_jump_pc)), skip_jump_pc)
        });

        // Lift the false-value instructions (between false_val_pc and join_pc)
        seg_pc = false_val_pc;
        while seg_pc < join_pc {
            let insn = &self.func.instructions[seg_pc];
            let advance = self.lift_instruction(insn, seg_pc);
            seg_pc += advance;
        }
        let false_operand = self.pop_last_reg_assign(result_reg).unwrap_or_else(|| {
            self.alloc_expr(HirExpr::Reg(self.reg_ref(result_reg, false_val_pc)), false_val_pc)
        });

        // Build: cond and true_val or false_val
        let and_expr = self.alloc_expr(
            HirExpr::Binary {
                op: BinOp::And,
                left: cond_operand,
                right: true_operand,
            },
            pc,
        );
        let result_expr = self.alloc_expr(
            HirExpr::Binary {
                op: BinOp::Or,
                left: and_expr,
                right: false_operand,
            },
            pc,
        );

        // Emit: result_reg = cond and true_val or false_val
        let reg = self.reg_ref(result_reg, pc);
        self.emit_assign_reg(reg, result_expr);

        Some(join_pc - pc)
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
                    HirExpr::Reg(RegRef { register: insn.aux as u8, pc, has_aux: false }),
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

    /// Negate a comparison expression (flip Eq↔Ne, Lt↔Ge, Le↔Gt).
    /// Used when a JumpXEqK* bail-out jump in an AND chain needs inversion.
    fn negate_comparison(&mut self, expr_id: ExprId, _pc: usize) -> ExprId {
        self.hir.exprs.negate_condition(expr_id)
    }
}
