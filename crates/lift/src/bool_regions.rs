//! Boolean value region detection.
//!
//! The Luau compiler generates specific bytecode patterns when a boolean
//! expression is used as a value (assigned to a variable, passed to a
//! function, etc.). Instead of computing a boolean through control flow
//! branches, these patterns should be recognized at lift time and compiled
//! into `HirExpr::Binary { And/Or }` chains.
//!
//! ## Pattern: Simple comparison as value
//!
//! `local x = a == b` compiles to:
//! ```text
//! JUMPIFEQ R1, R2, +2     -- comparison jump
//! LOADB R0, false, +1     -- false path: set 0, skip
//! LOADB R0, true          -- true path: set 1
//! ```
//!
//! ## Pattern: Or-chain as value
//!
//! `local x = a == X or a == Y` compiles to:
//! ```text
//! LOADB R0, true          -- pre-init for left comparison
//! JUMPIFEQ R1, R3, +N     -- left true → skip to end (short-circuit)
//! JUMPIFEQ R1, R4, +2     -- right comparison jump
//! LOADB R0, false, +1     -- false path
//! LOADB R0, true          -- true path (right comparison target)
//! <next instruction>       -- short-circuit target
//! ```
//!
//! ## Detection
//!
//! The telltale signature is the `LOADB Rx, false, +1` / `LOADB Rx, true`
//! pair at the end of the region. We scan for this pair, then trace backwards
//! to find all conditional jumps that participate. The conditional jumps
//! within the region should NOT create separate basic blocks — the entire
//! region is a single expression computation.

use lantern_bytecode::instruction::Instruction;
use lantern_bytecode::opcode::OpCode;
use rustc_hash::FxHashSet;

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
                    // Also suppress block boundaries for AUX-word jumps
                    if has_aux_word(insn.op) {
                        internal_jumps.insert(pc + 1);
                    }
                }
            }
        }
        // The LOADB false,+1 at false_pc also creates a jump (C!=0),
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

        // Look for LOADB Rx, false, +1 followed by LOADB Rx, true
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
            let end_pc = pc + 2;  // first instruction after the pair

            // Trace backwards to find the start of the region.
            // Look for the earliest instruction that is part of this
            // boolean computation. The region starts at the first
            // LOADB or comparison instruction that feeds into this chain.
            let start_pc = find_region_start(instructions, false_pc, true_pc, end_pc, result_reg);

            // Determine OR vs AND by looking at the pre-init LOADB value.
            // OR chain: pre-init is `true` (LOADB Rx, 1)
            // AND chain: pre-init is `false` (LOADB Rx, 0)
            let is_or_chain = if start_pc < false_pc {
                let start_insn = &instructions[start_pc];
                if start_insn.op == OpCode::LoadB && start_insn.a == result_reg && start_insn.c == 0 {
                    Some(start_insn.b != 0)
                } else {
                    None
                }
            } else {
                None // Single comparison, no pre-init
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
/// epilogue (LOADB false,+1 / LOADB true pair).
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

    // Scan backwards from false_pc looking for jumps that target true_pc or end_pc.
    // Each such jump may be preceded by a LOADB (pre-init) or GETIMPORT (load operand).
    for scan_pc in (0..false_pc).rev() {
        let insn = &instructions[scan_pc];

        // Check if this is a conditional jump targeting our boolean region
        if let Some(target) = conditional_jump_target(insn, scan_pc) {
            if target == true_pc || target == end_pc || target == false_pc {
                // This jump is part of the chain. The region extends at least to here.
                earliest = scan_pc;

                // Check if there's a LOADB pre-init before this comparison.
                // The pattern is: LOADB Rx, true/false → <operand loads> → comparison jump
                // Look for a LOADB of the result register before this jump.
                // But we need to be careful not to look too far back.
                // A LOADB immediately before the comparison operands is part of the region.
                if let Some(loadb_pc) = find_preceding_loadb(instructions, scan_pc, result_reg) {
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
    //   JUMP comparison
    // The LOADB is typically 1-4 instructions before the comparison jump.
    // We look back up to 6 instructions to be safe (covers GETIMPORT pairs with AUX).
    let window = 6.min(before_pc);
    for delta in 1..=window {
        let scan = before_pc - delta;
        let insn = &instructions[scan];
        if insn.op == OpCode::LoadB && insn.a == reg && insn.c == 0 {
            // Found a LOADB Rx with no skip — this is a pre-init
            return Some(scan);
        }
        // Stop if we hit something that definitely isn't part of the chain
        // (like a RETURN, CALL, or a LOADB for a different register with skip)
        if is_chain_barrier(insn) {
            break;
        }
    }
    None
}

/// Check if an instruction is a barrier that can't be inside a boolean chain.
fn is_chain_barrier(insn: &Instruction) -> bool {
    matches!(
        insn.op,
        OpCode::Return
            | OpCode::Call
            | OpCode::SetGlobal
            | OpCode::SetUpval
            | OpCode::SetTable
            | OpCode::SetTableKS
            | OpCode::SetTableN
            | OpCode::SetList
            | OpCode::Jump
            | OpCode::JumpBack
            | OpCode::ForNPrep
            | OpCode::ForNLoop
            | OpCode::ForGPrep
            | OpCode::ForGPrepINext
            | OpCode::ForGPrepNext
            | OpCode::ForGLoop
    )
}

/// Get the jump target of a conditional jump instruction, if it is one.
fn conditional_jump_target(insn: &Instruction, pc: usize) -> Option<usize> {
    match insn.op {
        OpCode::JumpIf | OpCode::JumpIfNot => {
            Some(((pc + 1) as i64 + insn.d as i64) as usize)
        }
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
            Some(((pc + 1) as i64 + insn.d as i64) as usize)
        }
        _ => None,
    }
}

/// A truthiness-based or/and chain in the instruction stream.
///
/// Pattern for `a or b or c`:
/// ```text
/// load R2, a; JUMPIF R2, +N       -- if truthy, skip to join
/// load R2, b; JUMPIF R2, +K       -- if truthy, skip to join
/// load R2, c                      -- last value, falls through
/// <join point>: use R2
/// ```
///
/// And-chains use JUMPIFNOT instead of JUMPIF.
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

/// Find all truthiness-based or/and chains.
///
/// A chain is a sequence of JUMPIF or JUMPIFNOT instructions on the SAME
/// register, all targeting the SAME join point (the PC after the last value).
fn find_truthy_chains(instructions: &[Instruction]) -> Vec<TruthyChain> {
    let mut chains = Vec::new();
    let mut pc = 0;

    while pc < instructions.len() {
        let insn = &instructions[pc];

        // Look for JUMPIF/JUMPIFNOT
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

                // Check for another JUMPIF/JUMPIFNOT of same reg targeting same join
                if scan_insn.op == insn.op && scan_insn.a == reg {
                    let scan_target = ((scan + 1) as i64 + scan_insn.d as i64) as usize;
                    if scan_target == join_pc {
                        jump_pcs.push(scan);
                        scan += 1;
                        continue;
                    }
                }

                // Skip non-jump instructions (value loads between jumps)
                if conditional_jump_target(scan_insn, scan).is_none() {
                    scan += 1;
                    continue;
                }

                // Hit a different jump — stop extending
                break;
            }

            // Validate: instructions between the last jump and join_pc must
            // reload the chain register. This distinguishes `a or b` (value chain)
            // from `if a then <body> end` (control flow).
            let last_jump = *jump_pcs.last().unwrap();
            let tail_reloads_reg = tail_loads_register(instructions, last_jump + 1, join_pc, reg);

            if !jump_pcs.is_empty() && tail_reloads_reg {
                let first_jump = jump_pcs[0];
                let start_pc = find_truthy_chain_start(instructions, first_jump, reg);

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

/// Check if the instructions between `from` and `to` (exclusive) contain
/// a load into `register` and no other control flow or side effects.
///
/// This validates that the tail of a truthy chain is a simple value reload,
/// distinguishing `a or b` from `if a then <body> end`.
fn tail_loads_register(instructions: &[Instruction], from: usize, to: usize, register: u8) -> bool {
    let mut found_load = false;
    for pc in from..to {
        if pc >= instructions.len() {
            return false;
        }
        let insn = &instructions[pc];

        // Check if this instruction writes to the target register
        if writes_register(insn, register) {
            found_load = true;
        }

        // Reject if we see control flow or side-effect instructions
        // that wouldn't appear in a value computation
        if is_chain_barrier(insn) || conditional_jump_target(insn, pc).is_some() {
            return false;
        }
    }
    found_load
}

/// Check if an instruction writes to a specific register.
fn writes_register(insn: &Instruction, register: u8) -> bool {
    // Most instructions write to A register
    if insn.a != register {
        return false;
    }
    matches!(
        insn.op,
        OpCode::GetImport
            | OpCode::GetGlobal
            | OpCode::Move
            | OpCode::LoadK
            | OpCode::LoadKX
            | OpCode::LoadN
            | OpCode::LoadB
            | OpCode::LoadNil
            | OpCode::GetUpval
            | OpCode::GetTable
            | OpCode::GetTableKS
            | OpCode::GetTableN
            | OpCode::Add
            | OpCode::Sub
            | OpCode::Mul
            | OpCode::Div
            | OpCode::Mod
            | OpCode::Pow
            | OpCode::IDiv
            | OpCode::And
            | OpCode::Or
            | OpCode::Not
            | OpCode::Minus
            | OpCode::Length
            | OpCode::Concat
            | OpCode::Call
    )
}

/// Find the start of a truthy chain by looking backwards from the first
/// JUMPIF/JUMPIFNOT for the value load into the chain register.
fn find_truthy_chain_start(
    _instructions: &[Instruction],
    first_jump_pc: usize,
    _reg: u8,
) -> usize {
    // The value load is typically 1-3 instructions before the jump
    // (GETGLOBAL has AUX, GETIMPORT has AUX, etc.)
    // For now, use the instruction immediately before as the start.
    // The lifter will handle instructions before the first jump normally.
    if first_jump_pc > 0 {
        first_jump_pc
    } else {
        0
    }
}

/// Check if an opcode has an AUX word.
pub fn has_aux_word(op: OpCode) -> bool {
    matches!(
        op,
        OpCode::JumpIfEq
            | OpCode::JumpIfLe
            | OpCode::JumpIfLt
            | OpCode::JumpIfNotEq
            | OpCode::JumpIfNotLe
            | OpCode::JumpIfNotLt
            | OpCode::JumpXEqKNil
            | OpCode::JumpXEqKB
            | OpCode::JumpXEqKN
            | OpCode::JumpXEqKS
    )
}
