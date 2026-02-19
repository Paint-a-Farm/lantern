//! Detection of boolean value computation regions.
//!
//! The Luau compiler generates specific bytecode patterns when a boolean
//! expression is used as a value (assigned to a variable, passed to a
//! function, etc.). The telltale signature is a `LOADB Rx, false, +1` /
//! `LOADB Rx, true` pair (the epilogue). We scan for this pair, then trace
//! backwards to find all conditional jumps that participate.

use lantern_bytecode::instruction::Instruction;
use lantern_bytecode::opcode::OpCode;
use rustc_hash::FxHashSet;

use super::utils::{conditional_jump_target, has_aux_word};

/// A boolean value computation region in the instruction stream.
///
/// All conditional jumps within `[start_pc, end_pc)` that target the
/// `true_pc` or `end_pc` are part of this boolean computation and
/// should NOT create block boundaries.
#[derive(Debug)]
pub struct BoolRegion {
    /// First instruction of the region (typically LOADB or first comparison).
    pub start_pc: usize,
    /// PC of `LOADB Rx, false, +1`.
    pub false_pc: usize,
    /// PC of `LOADB Rx, true`.
    pub true_pc: usize,
    /// PC after the region (first instruction not part of the boolean computation).
    pub end_pc: usize,
    /// The target register holding the boolean result.
    pub result_reg: u8,
    /// Whether this is an OR-chain (true) or AND-chain (false).
    /// Determined by the pre-init LOADB value: true = OR, false = AND.
    /// None if no pre-init was found (simple single comparison).
    pub is_or_chain: Option<bool>,
}

/// Detect all boolean value computation regions in the instruction stream.
///
/// Returns a set of PCs for conditional jumps that are *internal* to
/// boolean value computations. Block discovery should NOT create block
/// boundaries at these PCs.
pub fn detect_bool_regions(instructions: &[Instruction]) -> FxHashSet<usize> {
    let mut internal_jumps = FxHashSet::default();

    let regions = find_bool_regions(instructions);
    for region in &regions {
        // Find all conditional jumps within the region that target
        // the true_pc, end_pc, or any PC within the region.
        // These are all part of the boolean expression, not real branches.
        for pc in region.start_pc..region.false_pc {
            let insn = &instructions[pc];
            if let Some(target) = conditional_jump_target(insn, pc) {
                // Jump targets the true LOADB, or past the epilogue (end_pc),
                // or the false LOADB — all part of the boolean computation.
                if target == region.true_pc
                    || target == region.end_pc
                    || target == region.false_pc
                {
                    internal_jumps.insert(pc);
                    // Also suppress block boundaries for AUX-word jumps.
                    if has_aux_word(insn.op) {
                        internal_jumps.insert(pc + 1);
                    }
                }
            }
        }
        // The LOADB false,+1 at false_pc also creates a jump (C != 0),
        // suppress that too.
        internal_jumps.insert(region.false_pc);
        // The true_pc LOADB is also part of the region.
        internal_jumps.insert(region.true_pc);
    }

    internal_jumps
}

/// Find all boolean value computation regions.
pub fn find_bool_regions(instructions: &[Instruction]) -> Vec<BoolRegion> {
    let mut regions = Vec::new();

    for pc in 0..instructions.len().saturating_sub(1) {
        let insn = &instructions[pc];
        let next = &instructions[pc + 1];

        // Look for LOADB Rx, false, +1 followed by LOADB Rx, true.
        if insn.op == OpCode::LoadB
            && insn.b == 0        // false
            && insn.c != 0        // has skip (+1)
            && next.op == OpCode::LoadB
            && next.a == insn.a   // same register
            && next.b != 0        // true
            && next.c == 0        // no skip
        {
            let result_reg = insn.a;
            let false_pc = pc;
            let true_pc = pc + 1;
            let end_pc = pc + 2; // first instruction after the pair

            // Trace backwards to find the start of the region.
            let start_pc =
                find_region_start(instructions, false_pc, true_pc, end_pc, result_reg);

            // Determine OR vs AND by looking at the pre-init LOADB value.
            // OR chain: pre-init is `true` (LOADB Rx, 1)
            // AND chain: pre-init is `false` (LOADB Rx, 0)
            let is_or_chain = if start_pc < false_pc {
                let start_insn = &instructions[start_pc];
                if start_insn.op == OpCode::LoadB
                    && start_insn.a == result_reg
                    && start_insn.c == 0
                {
                    Some(start_insn.b != 0)
                } else {
                    None
                }
            } else {
                None // Single comparison, no pre-init.
            };

            regions.push(BoolRegion {
                start_pc,
                false_pc,
                true_pc,
                end_pc,
                result_reg,
                is_or_chain,
            });
        }
    }

    regions
}

/// Find the start of a boolean value region by tracing backwards from the
/// epilogue (`LOADB false,+1` / `LOADB true` pair).
///
/// We look for conditional jumps that target `true_pc` or `end_pc`, and
/// trace back to find the earliest instruction in the chain.
fn find_region_start(
    instructions: &[Instruction],
    false_pc: usize,
    true_pc: usize,
    end_pc: usize,
    result_reg: u8,
) -> usize {
    let mut earliest = false_pc;

    for scan_pc in (0..false_pc).rev() {
        let insn = &instructions[scan_pc];

        if let Some(target) = conditional_jump_target(insn, scan_pc) {
            if target == true_pc || target == end_pc || target == false_pc {
                earliest = scan_pc;

                // Check if there's a LOADB pre-init before this comparison.
                if let Some(loadb_pc) =
                    find_preceding_loadb(instructions, scan_pc, result_reg)
                {
                    earliest = loadb_pc;
                }
            }
        }
    }

    earliest
}

/// Look backwards from `before_pc` for a LOADB of `reg` that is likely
/// the pre-initialization of a comparison in the boolean chain.
///
/// Returns the PC of the LOADB if found within a short window.
fn find_preceding_loadb(
    instructions: &[Instruction],
    before_pc: usize,
    reg: u8,
) -> Option<usize> {
    // compileConditionValue emits:
    //   LOADB target, 0or1  (the pre-init)
    //   <operand loads: GETIMPORT, MOVE, etc>
    //   comparison jump
    // The LOADB is typically 1-4 instructions before the comparison jump.
    // We look back up to 6 instructions to be safe (covers GETIMPORT pairs with AUX).
    use super::utils::is_chain_barrier;

    let window = 6.min(before_pc);
    for delta in 1..=window {
        let scan = before_pc - delta;
        let insn = &instructions[scan];
        if insn.op == OpCode::LoadB && insn.a == reg && insn.c == 0 {
            return Some(scan);
        }
        if is_chain_barrier(insn) {
            break;
        }
    }
    None
}
