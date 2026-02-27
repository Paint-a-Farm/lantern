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
        OpCode::JumpIf | OpCode::JumpIfNot => Some(((pc + 1) as i64 + insn.d as i64) as usize),
        OpCode::JumpIfEq
        | OpCode::JumpIfLe
        | OpCode::JumpIfLt
        | OpCode::JumpIfNotEq
        | OpCode::JumpIfNotLe
        | OpCode::JumpIfNotLt
        | OpCode::JumpXEqKNil
        | OpCode::JumpXEqKB
        | OpCode::JumpXEqKN
        | OpCode::JumpXEqKS => Some(((pc + 1) as i64 + insn.d as i64) as usize),
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

/// Check if instructions in `[from, to)` write to any register other than
/// `expected_reg`. Used to distinguish value ternaries (single result register)
/// from multi-assignment if/else branches.
///
/// Writes inside table constructor regions (NewTable/DupTable → SetList) are
/// excluded because they are temporary element loads, not independent register
/// writes.
pub fn writes_multiple_registers(
    instructions: &[Instruction],
    from: usize,
    to: usize,
    expected_reg: u8,
) -> bool {
    let mut in_table_ctor = false;
    for pc in from..to {
        if pc >= instructions.len() {
            break;
        }
        let insn = &instructions[pc];
        // Skip Nop (AUX words)
        if insn.op == OpCode::Nop {
            continue;
        }
        // Track table constructor regions: NewTable/DupTable writing to expected_reg
        // starts a region; SetList on expected_reg ends it. Writes inside the region
        // are element temporaries and should be ignored.
        if matches!(insn.op, OpCode::NewTable | OpCode::DupTable) && insn.a == expected_reg {
            in_table_ctor = true;
            continue;
        }
        if insn.op == OpCode::SetList && insn.a == expected_reg {
            in_table_ctor = false;
            continue;
        }
        if in_table_ctor {
            continue;
        }
        // If this instruction writes to A and A != expected_reg, it's multi-reg
        if writes_register(insn, insn.a) && insn.a != expected_reg {
            return true;
        }
    }
    false
}

/// Find the end PC of a table constructor starting at `start_pc`.
///
/// For `NewTable`, the constructor ends at the `SetList` on the same register.
/// For `DupTable`, the constructor ends after the last `SetTableKS`/`SetTableN`/
/// `SetTable` that writes to the table register (B field).
///
/// Returns `start_pc + 1` if no population instructions are found (empty table).
fn find_table_ctor_end(
    instructions: &[Instruction],
    start_pc: usize,
    limit: usize,
    register: u8,
) -> usize {
    let is_dup = instructions[start_pc].op == OpCode::DupTable;
    let mut end = start_pc + 1;
    for p in (start_pc + 1)..limit {
        if p >= instructions.len() {
            break;
        }
        let pi = &instructions[p];
        if pi.op == OpCode::Nop {
            continue;
        }
        if !is_dup {
            // NewTable: ends at SetList on the register.
            if pi.op == OpCode::SetList && pi.a == register {
                return p + 1;
            }
        } else {
            // DupTable: track SetTableKS/SetTableN/SetTable writing to the table.
            if matches!(pi.op, OpCode::SetTableKS | OpCode::SetTableN | OpCode::SetTable)
                && pi.b == register
            {
                // Include the AUX word after SetTableKS/SetTableN.
                end = if has_aux_word(pi.op) { p + 2 } else { p + 1 };
                continue;
            }
        }
        // For both: loads into registers above the table register are element values.
        if writes_register(pi, pi.a) && pi.a > register {
            continue;
        }
        // Any other instruction means we've left the constructor.
        if end > start_pc + 1 {
            return end;
        }
        break;
    }
    end
}

/// Check if the instructions in `[from, to)` contain a load into `register`
/// and no control flow or side effects.
///
/// This validates that a range is a simple value reload, distinguishing
/// `a or b` from `if a then <body> end`.
///
/// Instructions inside table constructor regions (NewTable/DupTable → SetList)
/// targeting the chain register are allowed, since they are part of a table
/// literal value expression (e.g. `a or {1, 2, 3}`).
pub fn tail_loads_register(
    instructions: &[Instruction],
    from: usize,
    to: usize,
    register: u8,
) -> bool {
    let mut found_load = false;
    let mut in_table_ctor = false;
    let mut in_table_ctor_end = 0usize;
    for pc in from..to {
        if pc >= instructions.len() {
            return false;
        }
        let insn = &instructions[pc];

        // Track table constructor regions on the chain register.
        // NewTable/DupTable followed by population instructions (SetList for
        // array elements, SetTableKS/N for named keys) form a table literal.
        // We find the end of the constructor and skip the entire region.
        //
        // Without a population check, `local data = {}` (empty table) would
        // enter table-ctor mode and skip all subsequent instructions —
        // including barriers — causing false positives (e.g. Weather:draw).
        if matches!(insn.op, OpCode::NewTable | OpCode::DupTable) && insn.a == register {
            let ctor_end = find_table_ctor_end(instructions, pc, to, register);
            if ctor_end > pc + 1 {
                // Valid table constructor with population — skip the region.
                found_load = true;
                // Jump `pc` forward: the for-loop will increment past the ctor.
                // We use in_table_ctor with a known end PC via a dedicated skip.
                // (Simply advance the iterator by setting in_table_ctor_end.)
                in_table_ctor = true;
                in_table_ctor_end = ctor_end;
                continue;
            }
            // No population (empty table like `{}`) — treat as plain write.
            found_load = true;
        }
        if in_table_ctor {
            if pc < in_table_ctor_end {
                continue;
            }
            in_table_ctor = false;
        }
        if in_table_ctor {
            continue;
        }

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
///
/// Instructions inside table constructor regions (NewTable/DupTable → SetList)
/// are allowed — they are part of a value expression.
pub fn tail_has_side_effects(instructions: &[Instruction], from: usize, to: usize) -> bool {
    let mut in_table_ctor = false;
    for pc in from..to {
        if pc >= instructions.len() {
            return true;
        }
        let insn = &instructions[pc];

        // Track table constructor regions. We need to know the register, but
        // tail_has_side_effects doesn't receive one. Instead, track ANY
        // NewTable/DupTable → SetList pair on the same register.
        if matches!(insn.op, OpCode::NewTable | OpCode::DupTable) {
            in_table_ctor = true;
            continue;
        }
        if insn.op == OpCode::SetList {
            in_table_ctor = false;
            continue;
        }
        if in_table_ctor {
            continue;
        }

        if is_chain_barrier(insn) || conditional_jump_target(insn, pc).is_some() {
            return true;
        }

        // A Call with C=1 (0 return values) is a side-effect-only call (e.g.
        // error logging).  It must not appear inside a value expression — its
        // presence means this range is an imperative body, not a value load.
        if insn.op == OpCode::Call && insn.c == 1 {
            return true;
        }
    }
    false
}
