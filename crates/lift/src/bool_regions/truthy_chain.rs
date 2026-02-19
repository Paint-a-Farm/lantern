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

use lantern_bytecode::instruction::Instruction;
use lantern_bytecode::opcode::OpCode;
use rustc_hash::FxHashSet;

use super::utils::{conditional_jump_target, tail_loads_register};

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
pub fn detect_truthy_chains(
    instructions: &[Instruction],
) -> (Vec<TruthyChain>, FxHashSet<usize>) {
    let chains = find_truthy_chains(instructions);
    let mut suppressed = FxHashSet::default();

    for chain in &chains {
        for &jump_pc in &chain.jump_pcs {
            suppressed.insert(jump_pc);
        }
    }

    (chains, suppressed)
}

/// Find all truthiness-based or/and chains.
///
/// A chain is a sequence of JUMPIF or JUMPIFNOT instructions on the SAME
/// register, all targeting the SAME join point (the PC after the last value).
fn find_truthy_chains(instructions: &[Instruction]) -> Vec<TruthyChain> {
    let mut chains = Vec::new();
    let mut pc = 0;

    while pc < instructions.len() {
        let insn = &instructions[pc];

        if matches!(insn.op, OpCode::JumpIf | OpCode::JumpIfNot) {
            let is_or = insn.op == OpCode::JumpIf;
            let reg = insn.a;
            let join_pc = ((pc + 1) as i64 + insn.d as i64) as usize;

            // Try to extend: look for more JUMPIF/JUMPIFNOT of the same register
            // targeting the same join point.
            let mut jump_pcs = vec![pc];
            let mut scan = pc + 1;

            while scan < instructions.len() && scan < join_pc {
                let scan_insn = &instructions[scan];

                // Check for another jump of the same kind, same reg, same target.
                if scan_insn.op == insn.op && scan_insn.a == reg {
                    let scan_target = ((scan + 1) as i64 + scan_insn.d as i64) as usize;
                    if scan_target == join_pc {
                        jump_pcs.push(scan);
                        scan += 1;
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

            // Validate: instructions between the last jump and join_pc must
            // reload the chain register. This distinguishes `a or b` (value
            // chain) from `if a then <body> end` (control flow).
            let last_jump = *jump_pcs.last().unwrap();
            let tail_reloads_reg =
                tail_loads_register(instructions, last_jump + 1, join_pc, reg);

            if !jump_pcs.is_empty() && tail_reloads_reg {
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
