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
pub fn is_chain_barrier(insn: &Instruction) -> bool {
    matches!(
        insn.op,
        OpCode::Return
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

/// Check if an instruction is a negated conditional jump (the "if not cond" family).
///
/// These are used as the leading jump in value ternaries and and-or ternaries:
/// `JumpIfNot` tests truthiness, `JumpIfNotEq/Le/Lt` test comparisons,
/// `JumpXEqK*` with NOT flag clear tests equality (jump if equal → negated).
/// All produce the same structural pattern: jump over true-value to false-value.
pub fn is_negated_conditional_jump(insn: &Instruction) -> bool {
    match insn.op {
        OpCode::JumpIfNot | OpCode::JumpIfNotEq | OpCode::JumpIfNotLe | OpCode::JumpIfNotLt => {
            true
        }
        // JumpXEqK* with NOT flag clear: "jump if reg == value"
        // This is the negated sense for `and` chains (source was `reg ~= value and ...`)
        OpCode::JumpXEqKNil | OpCode::JumpXEqKB | OpCode::JumpXEqKN | OpCode::JumpXEqKS => {
            (insn.aux >> 31) == 0
        }
        _ => false,
    }
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
