//! Shared low-level utilities for boolean region detection.
//!
//! These helpers are used by all pattern-detection submodules.

use lantern_bytecode::instruction::Instruction;
use lantern_bytecode::opcode::OpCode;

/// Check if an opcode has an AUX word following the instruction.
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

/// Get the jump target PC of a conditional jump instruction, if it is one.
pub fn conditional_jump_target(insn: &Instruction, pc: usize) -> Option<usize> {
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

/// Check if an instruction is a barrier that cannot appear inside a boolean chain.
///
/// Call is NOT a barrier — `a or func()` is valid Lua. The call is the value
/// producer in the chain tail. Side-effect-only instructions (SetTable, Return,
/// etc.) remain barriers because they indicate control flow, not value expressions.
///
/// SetList is NOT a barrier — it populates a table created by NewTable as part
/// of a table literal value (e.g. `a or {1, 2, 3}`). The NewTable writes the
/// chain register and SetList fills it.
pub fn is_chain_barrier(insn: &Instruction) -> bool {
    matches!(
        insn.op,
        OpCode::Return
            | OpCode::SetGlobal
            | OpCode::SetUpval
            | OpCode::SetTable
            | OpCode::SetTableKS
            | OpCode::SetTableN
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

/// Check if an instruction is a conditional jump that can serve as the leading
/// jump of a ternary expression (`cond and b or c` / `cond and b or c`).
///
/// In a ternary, the leading jump skips to the false/fallback value when the
/// source-level condition is false. Both "negated" opcodes (JumpIfNot, JumpIfNotEq)
/// and "positive" opcodes (JumpIfEq, JumpXEqK* with either polarity) can fill
/// this role — they just encode different source conditions.
///
/// The lifter resolves the actual condition from the opcode + AUX flags.
pub fn is_negated_conditional_jump(insn: &Instruction) -> bool {
    matches!(
        insn.op,
        OpCode::JumpIfNot
            | OpCode::JumpIfNotEq
            | OpCode::JumpIfNotLe
            | OpCode::JumpIfNotLt
            | OpCode::JumpIfEq
            | OpCode::JumpIfLe
            | OpCode::JumpIfLt
            | OpCode::JumpXEqKNil
            | OpCode::JumpXEqKB
            | OpCode::JumpXEqKN
            | OpCode::JumpXEqKS
    )
}

/// Check if an instruction writes to a specific register.
pub fn writes_register(insn: &Instruction, register: u8) -> bool {
    // Most instructions write to the A register.
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
            | OpCode::NameCall
            | OpCode::Add
            | OpCode::Sub
            | OpCode::Mul
            | OpCode::Div
            | OpCode::Mod
            | OpCode::Pow
            | OpCode::IDiv
            | OpCode::AddK
            | OpCode::SubK
            | OpCode::MulK
            | OpCode::DivK
            | OpCode::ModK
            | OpCode::PowK
            | OpCode::IDivK
            | OpCode::SubRK
            | OpCode::DivRK
            | OpCode::And
            | OpCode::Or
            | OpCode::AndK
            | OpCode::OrK
            | OpCode::Not
            | OpCode::Minus
            | OpCode::Length
            | OpCode::Concat
            | OpCode::Call
            | OpCode::NewTable
            | OpCode::DupTable
            | OpCode::NewClosure
            | OpCode::DupClosure
            | OpCode::GetVarArgs
    )
}

/// Check if the instructions in `[from, to)` contain a load into `register`
/// and no control flow or side effects.
///
/// This validates that a range is a simple value reload, distinguishing
/// `a or b` from `if a then <body> end`.
pub fn tail_loads_register(
    instructions: &[Instruction],
    from: usize,
    to: usize,
    register: u8,
) -> bool {
    let mut found_load = false;
    for pc in from..to {
        if pc >= instructions.len() {
            return false;
        }
        let insn = &instructions[pc];

        if writes_register(insn, register) {
            found_load = true;
        }

        // Reject control flow or side-effect instructions.
        if is_chain_barrier(insn) || conditional_jump_target(insn, pc).is_some() {
            return false;
        }

        // A Call with C=1 (0 return values) is a side-effect-only call, not a
        // value producer. In a real `a and func()` chain the call must return a
        // value (C >= 2). A void call in the tail means this is an if-body, not
        // a chain segment.
        if insn.op == OpCode::Call && insn.c == 1 {
            return false;
        }
    }
    found_load
}

/// Check if instructions in `[from, to)` have side effects beyond simple loads.
pub fn tail_has_side_effects(instructions: &[Instruction], from: usize, to: usize) -> bool {
    for pc in from..to {
        if pc >= instructions.len() {
            return true;
        }
        let insn = &instructions[pc];
        if is_chain_barrier(insn) || conditional_jump_target(insn, pc).is_some() {
            return true;
        }
    }
    false
}
