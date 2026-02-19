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
//! Note: This differs from `BoolRegion` (which uses LoadB false/true pairs)
//! and from `AndOrTernary` (which uses JumpIfNot + JumpIf for `a and b or c`
//! where the truthiness of b matters). This pattern is a simple conditional
//! assignment where the true/false values are arbitrary (LoadK, GetImport, etc.)

use lantern_bytecode::instruction::Instruction;
use lantern_bytecode::opcode::OpCode;
use rustc_hash::FxHashSet;

use super::utils::{tail_has_side_effects, tail_loads_register, writes_register};

/// A simple conditional value assignment (ternary expression).
#[derive(Debug)]
pub struct ValueTernary {
    /// PC of the JumpIfNot instruction.
    pub jump_pc: usize,
    /// PC of the unconditional Jump instruction (end of true branch).
    pub skip_jump_pc: usize,
    /// First PC of the false value (target of JumpIfNot).
    pub false_val_pc: usize,
    /// PC after the entire ternary (target of the Jump).
    pub join_pc: usize,
    /// The register tested by the condition (Ra).
    pub cond_reg: u8,
    /// The register holding the result (Rb).
    pub result_reg: u8,
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
        // Suppress the JumpIfNot and the unconditional Jump to prevent block boundaries.
        suppressed.insert(t.jump_pc);
        suppressed.insert(t.skip_jump_pc);
    }

    (ternaries, suppressed)
}

/// Find all simple conditional value ternaries.
///
/// Scans for JumpIfNot followed by a value load, then Jump, then another
/// value load into the same register.
fn find_value_ternaries(instructions: &[Instruction]) -> Vec<ValueTernary> {
    let mut ternaries = Vec::new();

    for pc in 0..instructions.len() {
        let insn = &instructions[pc];

        // Look for JumpIfNot Ra, +N.
        if insn.op != OpCode::JumpIfNot {
            continue;
        }

        let cond_reg = insn.a;
        let false_val_pc = ((pc + 1) as i64 + insn.d as i64) as usize;

        // The true value is between pc+1 and the Jump instruction.
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
        let true_start = pc + 1;
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
        });
    }

    ternaries
}
