//! Detection of `a and b or c` ternary expressions, including compound conditions.
//!
//! Simple pattern:
//! ```text
//! [compute a into Ra]
//! JumpIfNot Ra, +N       → fallback_pc  (if a falsy, skip to c)
//! [compute b into Rb]
//! JumpIf Rb, +M          → join_pc      (if b truthy, skip c)
//! [compute c into Rb]    ← fallback_pc
//! <join>                 ← join_pc: use Rb
//! ```
//!
//! Compound-condition pattern (`(a1 and a2) and b or c`):
//! ```text
//! [compute a1]
//! JumpIfNot a1, +N       → fallback_pc  (all conditions target same fallback)
//! [compute a2]
//! JumpIfNot a2, +M       → fallback_pc
//! [compute b into Rb]
//! JumpIf Rb, +K          → join_pc
//! [compute c into Rb]    ← fallback_pc
//! <join>                 ← join_pc: use Rb
//! ```
//!
//! Also handles comparison-based conditions (JumpIfNotEq/Le/Lt, JumpIfEq/Le/Lt,
//! JumpXEqK*) in any position of the compound chain.

use lantern_bytecode::instruction::Instruction;
use lantern_bytecode::opcode::OpCode;
use rustc_hash::FxHashSet;

use super::utils::{has_aux_word, is_negated_conditional_jump, tail_has_side_effects, tail_loads_register};

/// A compound `a and b or c` ternary expression.
#[derive(Debug)]
pub struct AndOrTernary {
    /// PC of the first conditional jump (the leading "and" condition).
    pub and_jump_pc: usize,
    /// PCs of additional conditional jumps targeting the same fallback.
    /// Empty for simple (single-condition) ternaries.
    pub compound_jump_pcs: Vec<usize>,
    /// PC of the JumpIf instruction (the "or" skip).
    pub or_jump_pc: usize,
    /// Start of the fallback value (the "c" part).
    pub fallback_pc: usize,
    /// PC after the entire ternary (the join point).
    pub join_pc: usize,
    /// The register tested by the first "and" part (Ra). Only meaningful for
    /// JumpIfNot; for comparison jumps the condition involves two registers.
    pub and_reg: u8,
    /// The register holding the result (Rb).
    pub result_reg: u8,
    /// True if the first leading jump is a comparison (not JumpIfNot).
    pub is_comparison: bool,
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
        // Suppress AUX word after the leading jump if present.
        if has_aux_word(instructions[t.and_jump_pc].op) {
            suppressed.insert(t.and_jump_pc + 1);
        }
        // Suppress all compound condition jumps and their AUX words.
        for &cpc in &t.compound_jump_pcs {
            suppressed.insert(cpc);
            if has_aux_word(instructions[cpc].op) {
                suppressed.insert(cpc + 1);
            }
        }
    }

    (ternaries, suppressed)
}

fn find_and_or_ternaries(instructions: &[Instruction]) -> Vec<AndOrTernary> {
    let mut ternaries = Vec::new();
    let mut pc = 0;

    while pc < instructions.len() {
        let insn = &instructions[pc];

        // Look for any conditional jump that could start an and-or ternary.
        if is_negated_conditional_jump(insn) {
            let is_comparison = insn.op != OpCode::JumpIfNot;
            let and_reg = insn.a;
            let fallback_pc = ((pc + 1) as i64 + insn.d as i64) as usize;

            // Collect additional conditional jumps targeting the same fallback_pc.
            // These form compound conditions: (a1 and a2 and ...) and b or c.
            let scan_start = if has_aux_word(insn.op) { pc + 2 } else { pc + 1 };
            let mut compound_jump_pcs = Vec::new();
            let mut scan = scan_start;

            while scan < fallback_pc && scan < instructions.len() {
                let scan_insn = &instructions[scan];

                // Check for another conditional jump targeting the same fallback.
                if is_negated_conditional_jump(scan_insn) {
                    let target = ((scan + 1) as i64 + scan_insn.d as i64) as usize;
                    if target == fallback_pc {
                        compound_jump_pcs.push(scan);
                        scan += if has_aux_word(scan_insn.op) { 2 } else { 1 };
                        continue;
                    }
                    // A conditional jump with a different target means nested control
                    // flow (e.g. `if cond then <body with inner if> end`), not a flat
                    // ternary expression. Stop scanning.
                    break;
                }

                // Check for the JumpIf (the "or" part).
                if scan_insn.op == OpCode::JumpIf {
                    let or_reg = scan_insn.a;
                    let join_pc = ((scan + 1) as i64 + scan_insn.d as i64) as usize;

                    // The true branch (between the leading condition and the JumpIf)
                    // must be a simple value load — no side effects allowed.
                    let true_start = if let Some(&last_cpc) = compound_jump_pcs.last() {
                        last_cpc + if has_aux_word(instructions[last_cpc].op) { 2 } else { 1 }
                    } else {
                        scan_start
                    };

                    // The join point must be past the fallback (skip the "c" value),
                    // and both branches must simply load a value into the result register.
                    if join_pc > fallback_pc
                        && !tail_has_side_effects(instructions, true_start, scan)
                        && tail_loads_register(instructions, fallback_pc, join_pc, or_reg)
                        && !tail_has_side_effects(instructions, fallback_pc, join_pc)
                        && scan + 1 <= fallback_pc
                    {
                        ternaries.push(AndOrTernary {
                            and_jump_pc: pc,
                            compound_jump_pcs,
                            or_jump_pc: scan,
                            fallback_pc,
                            join_pc,
                            and_reg,
                            result_reg: or_reg,
                            is_comparison,
                        });
                        pc = join_pc;
                        break;
                    }
                    // JumpIf that doesn't match — stop scanning.
                    break;
                }

                scan += 1;
            }
        }

        pc += 1;
    }

    ternaries
}
