//! Detection of simple conditional value ternaries.
//!
//! Pattern:
//! ```text
//! JumpIfNot Ra, +N         → false_val_pc  (if a falsy, skip to false value)
//! [load true value into Rb] (1+ instructions)
//! Jump +M                  → join_pc       (skip past false value)
//! [load false value into Rb] ← false_val_pc (1+ instructions)
//! <join point>             ← join_pc: use Rb
//! ```
//!
//! This represents `a and true_val or false_val`. The condition register is Ra,
//! the result register is Rb.
//!
//! Also handles comparison-based ternaries where the leading jump is
//! `JumpIfNotEq/Le/Lt` instead of `JumpIfNot`. These produce the same structure
//! but with a comparison condition instead of a truthiness test.
//!
//! Note: This differs from `BoolRegion` (which uses LoadB false/true pairs)
//! and from `AndOrTernary` (which uses JumpIfNot + JumpIf for `a and b or c`
//! where the truthiness of b matters). This pattern is a simple conditional
//! assignment where the true/false values are arbitrary (LoadK, GetImport, etc.)

use lantern_bytecode::instruction::Instruction;
use lantern_bytecode::opcode::OpCode;
use rustc_hash::FxHashSet;

use super::utils::{has_aux_word, is_negated_conditional_jump, tail_has_side_effects, tail_loads_register, writes_register};

/// A simple conditional value assignment (ternary expression).
#[derive(Debug)]
pub struct ValueTernary {
    /// PC of the JumpIfNot (or JumpIfNotEq/Le/Lt) instruction.
    pub jump_pc: usize,
    /// PC of the unconditional Jump instruction (end of true branch).
    pub skip_jump_pc: usize,
    /// First PC of the false value (target of the leading jump).
    pub false_val_pc: usize,
    /// PC after the entire ternary (target of the Jump).
    pub join_pc: usize,
    /// The register tested by the condition (Ra). Only meaningful for
    /// JumpIfNot; for comparison jumps the condition involves two registers.
    pub cond_reg: u8,
    /// The register holding the result (Rb).
    pub result_reg: u8,
    /// True if the leading jump is a comparison (JumpIfNotEq/Le/Lt) rather
    /// than a truthiness test (JumpIfNot). The lifter uses this to extract
    /// the comparison expression from the jump instruction itself.
    pub is_comparison: bool,
}

/// Detect simple conditional value ternaries and return suppressed PCs.
///
/// Returns the found ternaries and a set of PCs that should be suppressed
/// from block boundary creation.
pub fn detect_value_ternaries(
    instructions: &[Instruction],
) -> (Vec<ValueTernary>, FxHashSet<usize>) {
    let ternaries = find_value_ternaries(instructions);
    let mut suppressed = FxHashSet::default();

    for t in &ternaries {
        // Suppress the leading jump and the unconditional Jump.
        suppressed.insert(t.jump_pc);
        suppressed.insert(t.skip_jump_pc);
    }

    (ternaries, suppressed)
}

/// Find all simple conditional value ternaries.
///
/// Scans for any negated conditional jump followed by a value load, then Jump,
/// then another value load into the same register.
fn find_value_ternaries(instructions: &[Instruction]) -> Vec<ValueTernary> {
    let mut ternaries = Vec::new();

    for pc in 0..instructions.len() {
        let insn = &instructions[pc];

        // Look for any negated conditional jump: JumpIfNot, JumpIfNotEq/Le/Lt, JumpXEqK*.
        if !is_negated_conditional_jump(insn) {
            continue;
        }

        let is_comparison = insn.op != OpCode::JumpIfNot;
        let cond_reg = insn.a;
        let false_val_pc = ((pc + 1) as i64 + insn.d as i64) as usize;

        // The true value starts after the jump (and its AUX word if any).
        let true_start = if has_aux_word(insn.op) { pc + 2 } else { pc + 1 };

        // The Jump must be at false_val_pc - 1 (immediately before the false value).
        if false_val_pc < 2 || false_val_pc > instructions.len() {
            continue;
        }
        let skip_jump_pc = false_val_pc - 1;
        if skip_jump_pc <= pc {
            continue;
        }

        let skip_insn = &instructions[skip_jump_pc];
        if skip_insn.op != OpCode::Jump {
            continue;
        }

        let join_pc = ((skip_jump_pc + 1) as i64 + skip_insn.d as i64) as usize;

        // There must be at least one instruction for the true value.
        if true_start >= skip_jump_pc {
            continue;
        }

        // There must be at least one instruction for the false value.
        if false_val_pc >= join_pc || join_pc > instructions.len() {
            continue;
        }

        // Both branches must load into the same result register.
        // Find the register written by the last instruction of the true branch.
        let true_last_insn = &instructions[skip_jump_pc - 1];
        if !writes_register(true_last_insn, true_last_insn.a) {
            continue;
        }
        let result_reg = true_last_insn.a;

        // Verify the false branch also writes to result_reg.
        if !tail_loads_register(instructions, false_val_pc, join_pc, result_reg) {
            continue;
        }

        // Verify no side effects in either branch.
        if tail_has_side_effects(instructions, true_start, skip_jump_pc)
            || tail_has_side_effects(instructions, false_val_pc, join_pc)
        {
            continue;
        }

        ternaries.push(ValueTernary {
            jump_pc: pc,
            skip_jump_pc,
            false_val_pc,
            join_pc,
            cond_reg,
            result_reg,
            is_comparison,
        });
    }

    ternaries
}
