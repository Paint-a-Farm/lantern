//! Detection of compound `a and b or c` ternary expressions.
//!
//! Pattern:
//! ```text
//! [compute a into Ra]
//! JumpIfNot Ra, +N       → fallback_pc  (if a falsy, skip to c)
//! [compute b into Rb]
//! JumpIf Rb, +M          → join_pc      (if b truthy, skip c)
//! [compute c into Rb]    ← fallback_pc
//! <join>                 ← join_pc: use Rb
//! ```
//!
//! This represents `Rb = a and b or c`. The result register is Rb.

use lantern_bytecode::instruction::Instruction;
use lantern_bytecode::opcode::OpCode;
use rustc_hash::FxHashSet;

use super::utils::{has_aux_word, tail_has_side_effects, tail_loads_register};

/// A compound `a and b or c` ternary expression.
#[derive(Debug)]
pub struct AndOrTernary {
    /// PC of the JumpIfNot instruction (the "and" test).
    pub and_jump_pc: usize,
    /// PC of the JumpIf instruction (the "or" skip).
    pub or_jump_pc: usize,
    /// Start of the fallback value (the "c" part).
    pub fallback_pc: usize,
    /// PC after the entire ternary (the join point).
    pub join_pc: usize,
    /// The register tested by the "and" part (Ra).
    pub and_reg: u8,
    /// The register holding the result (Rb).
    pub result_reg: u8,
}

/// Detect compound `a and b or c` ternaries.
///
/// Returns the found ternaries and a set of PCs that should be suppressed
/// from block boundary creation.
pub fn detect_and_or_ternaries(
    instructions: &[Instruction],
) -> (Vec<AndOrTernary>, FxHashSet<usize>) {
    let ternaries = find_and_or_ternaries(instructions);
    let mut suppressed = FxHashSet::default();

    for t in &ternaries {
        suppressed.insert(t.and_jump_pc);
        suppressed.insert(t.or_jump_pc);
        // Also suppress the NOP after JumpIfNot if it has an AUX word.
        if has_aux_word(instructions[t.and_jump_pc].op) {
            suppressed.insert(t.and_jump_pc + 1);
        }
    }

    (ternaries, suppressed)
}

fn find_and_or_ternaries(instructions: &[Instruction]) -> Vec<AndOrTernary> {
    let mut ternaries = Vec::new();
    let mut pc = 0;

    while pc < instructions.len() {
        let insn = &instructions[pc];

        // Look for JumpIfNot Ra (the "and" part).
        if insn.op == OpCode::JumpIfNot {
            let and_reg = insn.a;
            let fallback_pc = ((pc + 1) as i64 + insn.d as i64) as usize;

            // Scan forward for a JumpIf Rb that jumps past the fallback.
            // The JumpIf must be BEFORE fallback_pc.
            let mut scan = pc + 1;
            while scan < fallback_pc && scan < instructions.len() {
                let scan_insn = &instructions[scan];
                if scan_insn.op == OpCode::JumpIf {
                    let or_reg = scan_insn.a;
                    let join_pc = ((scan + 1) as i64 + scan_insn.d as i64) as usize;

                    // The join point must be past the fallback (skip the "c" value),
                    // and the fallback must simply load a value into the same register.
                    if join_pc > fallback_pc
                        && tail_loads_register(instructions, fallback_pc, join_pc, or_reg)
                        && !tail_has_side_effects(instructions, fallback_pc, join_pc)
                        && scan + 1 <= fallback_pc
                    {
                        ternaries.push(AndOrTernary {
                            and_jump_pc: pc,
                            or_jump_pc: scan,
                            fallback_pc,
                            join_pc,
                            and_reg,
                            result_reg: or_reg,
                        });
                        pc = join_pc;
                        break;
                    }
                }
                scan += 1;
            }
        }

        pc += 1;
    }

    ternaries
}
