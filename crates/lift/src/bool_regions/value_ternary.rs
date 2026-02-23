//! Detection of conditional value ternaries, including compound conditions.
//!
//! Simple pattern:
//! ```text
//! JumpIfNot Ra, +N         → false_val_pc  (if a falsy, skip to false value)
//! [load true value into Rb] (1+ instructions)
//! Jump +M                  → join_pc       (skip past false value)
//! [load false value into Rb] ← false_val_pc (1+ instructions)
//! <join point>             ← join_pc: use Rb
//! ```
//!
//! Compound-condition pattern (`(a1 and a2) and true_val or false_val`):
//! ```text
//! JumpIfNot* a1, +N        → false_val_pc  (all conditions target same false_val)
//! JumpIfNot* a2, +M        → false_val_pc
//! [load true value into Rb]
//! Jump +K                  → join_pc
//! [load false value into Rb] ← false_val_pc
//! <join point>             ← join_pc: use Rb
//! ```
//!
//! This represents `a and true_val or false_val`. The condition register is Ra,
//! the result register is Rb.
//!
//! Also handles comparison-based ternaries where the leading jump is
//! `JumpIfNotEq/Le/Lt`, `JumpIfEq/Le/Lt`, or `JumpXEqK*` instead of `JumpIfNot`.
//!
//! Note: This differs from `BoolRegion` (which uses LoadB false/true pairs)
//! and from `AndOrTernary` (which uses JumpIfNot + JumpIf for `a and b or c`
//! where the truthiness of b matters). This pattern is a simple conditional
//! assignment where the true/false values are arbitrary (LoadK, GetImport, etc.)

use lantern_bytecode::instruction::Instruction;
use lantern_bytecode::opcode::OpCode;
use rustc_hash::FxHashSet;

use super::utils::{
    has_aux_word, is_negated_conditional_jump, tail_has_side_effects, tail_loads_register,
    writes_multiple_registers, writes_register,
};

/// A conditional value assignment (ternary expression), possibly with compound conditions.
#[derive(Debug)]
pub struct ValueTernary {
    /// PC of the first conditional jump.
    pub jump_pc: usize,
    /// PCs of additional conditional jumps targeting the same false_val_pc.
    /// Empty for simple (single-condition) ternaries.
    pub compound_jump_pcs: Vec<usize>,
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
    /// True if the first leading jump is a comparison (not JumpIfNot).
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
        // Suppress AUX word after the leading jump if present.
        if has_aux_word(instructions[t.jump_pc].op) {
            suppressed.insert(t.jump_pc + 1);
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

/// Find all conditional value ternaries, including compound conditions.
///
/// Scans for any conditional jump, collects additional conditional jumps
/// targeting the same false_val_pc, then verifies a value load + Jump +
/// value load structure.
fn find_value_ternaries(instructions: &[Instruction]) -> Vec<ValueTernary> {
    let mut ternaries = Vec::new();
    let mut pc = 0;

    while pc < instructions.len() {
        let insn = &instructions[pc];

        // Look for any conditional jump that could start a value ternary.
        if !is_negated_conditional_jump(insn) {
            pc += 1;
            continue;
        }

        let is_comparison = insn.op != OpCode::JumpIfNot;
        let cond_reg = insn.a;
        let false_val_pc = ((pc + 1) as i64 + insn.d as i64) as usize;

        // Collect additional conditional jumps targeting the same false_val_pc.
        let scan_start = if has_aux_word(insn.op) {
            pc + 2
        } else {
            pc + 1
        };
        let mut compound_jump_pcs = Vec::new();
        let mut scan = scan_start;

        while scan < false_val_pc && scan < instructions.len() {
            let scan_insn = &instructions[scan];
            if is_negated_conditional_jump(scan_insn) {
                let target = ((scan + 1) as i64 + scan_insn.d as i64) as usize;
                if target == false_val_pc {
                    compound_jump_pcs.push(scan);
                    scan += if has_aux_word(scan_insn.op) { 2 } else { 1 };
                    continue;
                }
            }
            // Not a matching compound jump — stop collecting, continue scanning
            // for the Jump (unconditional skip).
            break;
        }

        // The true value starts after the last condition jump.
        let last_cond_pc = compound_jump_pcs.last().copied().unwrap_or(pc);
        let last_cond_insn = &instructions[last_cond_pc];
        let true_start = last_cond_pc
            + if has_aux_word(last_cond_insn.op) {
                2
            } else {
                1
            };

        // The Jump must be at false_val_pc - 1 (immediately before the false value).
        if false_val_pc < 2 || false_val_pc > instructions.len() {
            pc += 1;
            continue;
        }
        let skip_jump_pc = false_val_pc - 1;
        if skip_jump_pc <= pc {
            pc += 1;
            continue;
        }

        let skip_insn = &instructions[skip_jump_pc];
        if skip_insn.op != OpCode::Jump {
            pc += 1;
            continue;
        }

        let join_pc = ((skip_jump_pc + 1) as i64 + skip_insn.d as i64) as usize;

        // There must be at least one instruction for the true value.
        if true_start >= skip_jump_pc {
            pc += 1;
            continue;
        }

        // There must be at least one instruction for the false value.
        if false_val_pc >= join_pc || join_pc > instructions.len() {
            pc += 1;
            continue;
        }

        // Both branches must load into the same result register.
        // Skip past Nop/AUX words to find the actual value-producing instruction.
        let mut true_last_pc = skip_jump_pc - 1;
        while true_last_pc > true_start && instructions[true_last_pc].op == OpCode::Nop {
            true_last_pc -= 1;
        }
        let true_last_insn = &instructions[true_last_pc];
        if !writes_register(true_last_insn, true_last_insn.a) {
            pc += 1;
            continue;
        }
        let result_reg = true_last_insn.a;

        // Verify the false branch also writes to result_reg.
        if !tail_loads_register(instructions, false_val_pc, join_pc, result_reg) {
            pc += 1;
            continue;
        }

        // A true value ternary writes to exactly ONE register per branch.
        // If either branch writes to multiple distinct registers, this is
        // a real if/else with multi-assignment, not a conditional expression.
        if writes_multiple_registers(instructions, true_start, skip_jump_pc, result_reg)
            || writes_multiple_registers(instructions, false_val_pc, join_pc, result_reg)
        {
            pc += 1;
            continue;
        }

        // Verify no side effects in either branch.
        if tail_has_side_effects(instructions, true_start, skip_jump_pc)
            || tail_has_side_effects(instructions, false_val_pc, join_pc)
        {
            pc += 1;
            continue;
        }

        ternaries.push(ValueTernary {
            jump_pc: pc,
            compound_jump_pcs,
            skip_jump_pc,
            false_val_pc,
            join_pc,
            cond_reg,
            result_reg,
            is_comparison,
        });

        // Skip past the ternary to avoid overlapping detections.
        pc = join_pc;
    }

    ternaries
}
