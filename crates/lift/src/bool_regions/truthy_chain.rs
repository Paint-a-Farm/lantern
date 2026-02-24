//! Detection of truthiness-based or/and chains.
//!
//! Pattern for `a or b or c`:
//! ```text
//! load R2, a; JUMPIF R2, +N       -- if truthy, skip to join
//! load R2, b; JUMPIF R2, +K       -- if truthy, skip to join
//! load R2, c                      -- last value, falls through
//! <join point>: use R2
//! ```
//!
//! And-chains use JUMPIFNOT instead of JUMPIF.
//!
//! Mixed chains may include JumpXEqKNil alongside JumpIf/JumpIfNot when the
//! compiler generates nil-checks as part of a compound expression:
//! `a ~= nil and a.b ~= nil and f(a.b)` compiles to JumpXEqKNil + JumpIfNot
//! instructions all targeting the same join point on the same register.
//!
//! **Important**: A standalone JumpXEqKNil (single link) is NOT treated as a
//! chain because it is indistinguishable from `if x ~= nil then <body> end`
//! using only tail-register analysis. JumpXEqKNil links are only accepted when
//! they appear in a multi-link chain (2+ jumps targeting the same join point).

use lantern_bytecode::instruction::Instruction;
use lantern_bytecode::opcode::OpCode;
use rustc_hash::FxHashSet;

use super::utils::{
    conditional_jump_target, has_aux_word, tail_loads_register, writes_multiple_registers,
};

/// A truthiness-based or/and chain in the instruction stream.
#[derive(Debug)]
pub struct TruthyChain {
    /// First PC of the chain (the first value load or JUMPIF/JUMPIFNOT).
    pub start_pc: usize,
    /// PC after the last value load (the join point).
    pub end_pc: usize,
    /// The register holding the chain result.
    pub result_reg: u8,
    /// Whether this is an OR-chain (JUMPIF) or AND-chain (JUMPIFNOT).
    pub is_or: bool,
    /// PCs of the JUMPIF/JUMPIFNOT instructions in the chain.
    pub jump_pcs: Vec<usize>,
}

/// Detect truthiness-based or/and chains and return suppressed PCs.
///
/// Returns the found chains and a set of PCs that should be suppressed
/// from block boundary creation.
pub fn detect_truthy_chains(instructions: &[Instruction]) -> (Vec<TruthyChain>, FxHashSet<usize>) {
    let chains = find_truthy_chains(instructions);
    let mut suppressed = FxHashSet::default();

    for chain in &chains {
        for &jump_pc in &chain.jump_pcs {
            suppressed.insert(jump_pc);
        }
    }

    (chains, suppressed)
}

/// Classify a conditional jump as or-chain or and-chain compatible, returning
/// `(is_or, register, target_pc)`. Returns `None` for non-compatible instructions.
///
/// Compatible instructions:
/// - `JumpIf Rn` → or-chain (skip to join when truthy)
/// - `JumpIfNot Rn` → and-chain (skip to join when falsy)
/// - `JumpXEqKNil Rn` with AUX bit 31 = 0 → and-chain (skip when nil)
/// - `JumpXEqKNil Rn` with AUX bit 31 = 1 → or-chain (skip when non-nil)
fn classify_chain_jump(insn: &Instruction, pc: usize) -> Option<(bool, u8, usize)> {
    match insn.op {
        OpCode::JumpIf => {
            let target = ((pc + 1) as i64 + insn.d as i64) as usize;
            Some((true, insn.a, target))
        }
        OpCode::JumpIfNot => {
            let target = ((pc + 1) as i64 + insn.d as i64) as usize;
            Some((false, insn.a, target))
        }
        OpCode::JumpXEqKNil => {
            let target = ((pc + 1) as i64 + insn.d as i64) as usize;
            let not_flag = (insn.aux >> 31) != 0;
            // AUX bit 31 = 0: "jump if == nil" → and-chain (skip when nil/falsy)
            // AUX bit 31 = 1: "jump if ~= nil" → or-chain (skip when truthy)
            Some((not_flag, insn.a, target))
        }
        _ => None,
    }
}

/// Check if an instruction is a JumpXEqKNil.
fn is_jump_x_eq_k_nil(op: OpCode) -> bool {
    op == OpCode::JumpXEqKNil
}

/// Find all truthiness-based or/and chains.
///
/// A chain is a sequence of compatible conditional jumps on the SAME register,
/// all targeting the SAME join point. JumpIf, JumpIfNot, and JumpXEqKNil can
/// be mixed within a chain as long as they have the same or/and sense.
///
/// **Constraint**: Chains that consist entirely of JumpXEqKNil instructions
/// are rejected — at least one link must be JumpIf or JumpIfNot. This prevents
/// false positives from guard conditions (`if x ~= nil then <body> end`) which
/// generate identical bytecode to `x ~= nil and <value>` for single links.
fn find_truthy_chains(instructions: &[Instruction]) -> Vec<TruthyChain> {
    let mut chains = Vec::new();
    let mut pc = 0;

    while pc < instructions.len() {
        let insn = &instructions[pc];

        if let Some((is_or, reg, join_pc)) = classify_chain_jump(insn, pc) {
            // Try to extend: look for more compatible jumps on the same register
            // targeting the same join point.
            let mut jump_pcs = vec![pc];
            let mut scan = pc + 1;
            // Skip AUX word for instructions that have one.
            if has_aux_word(insn.op) {
                scan += 1;
            }

            while scan < instructions.len() && scan < join_pc {
                let scan_insn = &instructions[scan];

                // Check for another compatible jump of the same sense, same reg, same target.
                if let Some((scan_is_or, scan_reg, scan_target)) =
                    classify_chain_jump(scan_insn, scan)
                {
                    if scan_is_or == is_or && scan_reg == reg && scan_target == join_pc {
                        jump_pcs.push(scan);
                        scan += 1;
                        // Skip AUX word.
                        if has_aux_word(scan_insn.op) {
                            scan += 1;
                        }
                        continue;
                    }
                }

                // Skip non-jump instructions (value loads between jumps).
                if conditional_jump_target(scan_insn, scan).is_none() {
                    scan += 1;
                    continue;
                }

                // Hit a different jump — stop extending.
                break;
            }

            // Safety check: if ALL links are JumpXEqKNil, reject the chain.
            // A standalone JumpXEqKNil (or a sequence of them without JumpIf/JumpIfNot)
            // is indistinguishable from guard conditions. We only accept JumpXEqKNil
            // when it's mixed with JumpIf/JumpIfNot in a multi-link chain.
            let has_classic_link = jump_pcs
                .iter()
                .any(|&p| !is_jump_x_eq_k_nil(instructions[p].op));

            if !has_classic_link {
                // All links are JumpXEqKNil — skip. Fall through to pc += 1.
                pc += 1;
                continue;
            }

            // Validate each segment between consecutive jumps: the instructions
            // between jump[i] and jump[i+1] must reload the chain register and
            // contain no barriers. This distinguishes `a and b and c` (every
            // intermediate segment is a clean value reload) from guard conditions
            // where the body has side effects or complex code.
            //
            // Also validate the final tail (last_jump → join_pc).
            let mut all_segments_valid = true;
            for i in 0..jump_pcs.len() {
                let seg_start = if has_aux_word(instructions[jump_pcs[i]].op) {
                    jump_pcs[i] + 2
                } else {
                    jump_pcs[i] + 1
                };
                let seg_end = if i + 1 < jump_pcs.len() {
                    jump_pcs[i + 1]
                } else {
                    join_pc
                };
                if !tail_loads_register(instructions, seg_start, seg_end, reg) {
                    all_segments_valid = false;
                    break;
                }
                // Reject segments that write to registers beyond the chain
                // register — these are if-bodies, not value expressions.
                if writes_multiple_registers(instructions, seg_start, seg_end, reg) {
                    all_segments_valid = false;
                    break;
                }
            }

            if !jump_pcs.is_empty() && all_segments_valid {
                let first_jump = jump_pcs[0];
                let start_pc = find_truthy_chain_start(first_jump);

                chains.push(TruthyChain {
                    start_pc,
                    end_pc: join_pc,
                    result_reg: reg,
                    is_or,
                    jump_pcs: jump_pcs.clone(),
                });

                pc = join_pc;
                continue;
            }
        }

        pc += 1;
    }

    chains
}

/// Find the start of a truthy chain by looking backwards from the first
/// JUMPIF/JUMPIFNOT for the value load into the chain register.
fn find_truthy_chain_start(first_jump_pc: usize) -> usize {
    // The value load is typically 1-3 instructions before the jump
    // (GETGLOBAL has AUX, GETIMPORT has AUX, etc.).
    // For now, use the instruction at the first jump as the start.
    // The lifter handles instructions before the first jump normally.
    if first_jump_pc > 0 {
        first_jump_pc
    } else {
        0
    }
}
