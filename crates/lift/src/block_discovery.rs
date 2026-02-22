use lantern_bytecode::instruction::Instruction;
use lantern_bytecode::opcode::OpCode;
use rustc_hash::FxHashSet;

/// Discover basic block boundaries from a function's instruction stream.
///
/// A new block starts at:
/// - PC 0 (function entry)
/// - The target of any jump
/// - The instruction after any jump/branch (fallthrough)
/// - RETURN instructions end a block
///
/// `suppressed_pcs` contains PCs of instructions (e.g. conditional jumps
/// inside boolean value computations) that should NOT create block boundaries.
///
/// `suppressed_targets` contains PCs that should NEVER become block starts,
/// even if they are jump targets. Used for PCs inside value ternaries where
/// an external jump targets a PC that the ternary lifter handles internally.
///
/// Returns a sorted set of block-start PCs.
pub fn discover_block_starts(
    instructions: &[Instruction],
    suppressed_pcs: &FxHashSet<usize>,
    suppressed_targets: &FxHashSet<usize>,
) -> Vec<usize> {
    let mut starts = FxHashSet::default();
    starts.insert(0);

    for (pc, insn) in instructions.iter().enumerate() {
        // Skip instructions that are inside boolean value regions
        if suppressed_pcs.contains(&pc) {
            continue;
        }

        match insn.op {
            // LOADB with C != 0 is a conditional jump
            OpCode::LoadB => {
                if insn.c != 0 {
                    let target = (pc + 1).wrapping_add(insn.c as usize);
                    starts.insert(target);
                }
            }

            // Unconditional jumps
            OpCode::Jump | OpCode::JumpBack | OpCode::JumpX => {
                let offset = if insn.op == OpCode::JumpX {
                    insn.e
                } else {
                    insn.d as i32
                };
                let target = ((pc + 1) as i64 + offset as i64) as usize;
                starts.insert(pc + 1); // fallthrough
                starts.insert(target);
            }

            // Conditional jumps (no AUX)
            OpCode::JumpIf | OpCode::JumpIfNot => {
                let target = ((pc + 1) as i64 + insn.d as i64) as usize;
                starts.insert(pc + 1); // fallthrough
                starts.insert(target);
            }

            // Conditional jumps with AUX word
            OpCode::JumpIfEq
            | OpCode::JumpIfLe
            | OpCode::JumpIfLt
            | OpCode::JumpIfNotEq
            | OpCode::JumpIfNotLe
            | OpCode::JumpIfNotLt
            | OpCode::JumpXEqKNil
            | OpCode::JumpXEqKB
            | OpCode::JumpXEqKN
            | OpCode::JumpXEqKS => {
                let target = ((pc + 1) as i64 + insn.d as i64) as usize;
                // +2 because of AUX word
                starts.insert(pc + 2);
                starts.insert(target);
            }

            // Numeric for prep: sets up loop, jumps over body if empty
            OpCode::ForNPrep => {
                let target = ((pc + 1) as i64 + insn.d as i64) as usize;
                starts.insert(pc + 1); // loop body start
                starts.insert(target); // after loop
            }

            // Numeric for loop: back-edge
            OpCode::ForNLoop => {
                let target = ((pc + 1) as i64 + insn.d as i64) as usize;
                starts.insert(pc); // loop header (the FORNLOOP itself)
                starts.insert(pc + 1); // after loop
                starts.insert(target); // loop body start
            }

            // Generic for prep
            OpCode::ForGPrep | OpCode::ForGPrepINext | OpCode::ForGPrepNext => {
                let target = ((pc + 1) as i64 + insn.d as i64) as usize;
                starts.insert(pc + 1); // loop body start
                starts.insert(target); // FORGLOOP location
            }

            // Generic for loop: back-edge (has AUX)
            OpCode::ForGLoop => {
                let target = ((pc + 1) as i64 + insn.d as i64) as usize;
                starts.insert(pc + 2); // after loop exit (skip AUX word)
                starts.insert(target); // loop body start
            }

            // RETURN ends a block, next instruction starts new block
            OpCode::Return => {
                if pc + 1 < instructions.len() {
                    starts.insert(pc + 1);
                }
            }

            _ => {}
        }
    }

    // Remove any starts beyond instruction range or in suppressed targets
    let len = instructions.len();
    let mut sorted: Vec<usize> = starts
        .into_iter()
        .filter(|&pc| pc < len && !suppressed_targets.contains(&pc))
        .collect();
    sorted.sort_unstable();
    sorted
}

/// Compute block ranges from sorted start PCs and total instruction count.
/// Returns (start_pc, end_pc_exclusive) pairs.
pub fn block_ranges(starts: &[usize], instruction_count: usize) -> Vec<(usize, usize)> {
    starts
        .windows(2)
        .map(|w| (w[0], w[1]))
        .chain(std::iter::once((
            *starts.last().unwrap_or(&0),
            instruction_count,
        )))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_block_discovery() {
        // Simple linear function: LOADN, LOADN, ADD, RETURN
        let insns = vec![
            Instruction { op: OpCode::LoadN, a: 0, b: 0, c: 0, d: 1, e: 0, aux: 0 },
            Instruction { op: OpCode::LoadN, a: 1, b: 0, c: 0, d: 2, e: 0, aux: 0 },
            Instruction { op: OpCode::Add, a: 2, b: 0, c: 1, d: 0, e: 0, aux: 0 },
            Instruction { op: OpCode::Return, a: 2, b: 2, c: 0, d: 0, e: 0, aux: 0 },
        ];
        let starts = discover_block_starts(&insns, &FxHashSet::default(), &FxHashSet::default());
        // Only one block: PC 0
        assert_eq!(starts, vec![0]);
    }

    #[test]
    fn test_jump_creates_blocks() {
        // LOADN, JUMPIF, LOADN, RETURN, LOADN, RETURN
        let insns = vec![
            Instruction { op: OpCode::LoadN, a: 0, b: 0, c: 0, d: 1, e: 0, aux: 0 },
            // JUMPIF A=0, D=2 -> jump to PC 4
            Instruction { op: OpCode::JumpIf, a: 0, b: 0, c: 0, d: 2, e: 0, aux: 0 },
            Instruction { op: OpCode::LoadN, a: 1, b: 0, c: 0, d: 10, e: 0, aux: 0 },
            Instruction { op: OpCode::Return, a: 1, b: 2, c: 0, d: 0, e: 0, aux: 0 },
            Instruction { op: OpCode::LoadN, a: 1, b: 0, c: 0, d: 20, e: 0, aux: 0 },
            Instruction { op: OpCode::Return, a: 1, b: 2, c: 0, d: 0, e: 0, aux: 0 },
        ];
        let starts = discover_block_starts(&insns, &FxHashSet::default(), &FxHashSet::default());
        // Blocks: 0, 2 (fallthrough after JUMPIF), 4 (jump target)
        assert_eq!(starts, vec![0, 2, 4]);
    }
}
