/// Luau bytecode opcodes (version 6).
///
/// Each variant documents the instruction format and operand usage.
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpCode {
    /// NOP: noop
    Nop = 0,
    /// BREAK: debugger break
    Break = 1,
    /// LOADNIL: A = nil
    LoadNil = 2,
    /// LOADB: A = (bool)B; if C, pc += C
    LoadB = 3,
    /// LOADN: A = D (signed 16-bit number)
    LoadN = 4,
    /// LOADK: A = constants[D]
    LoadK = 5,
    /// MOVE: A = B
    Move = 6,
    /// GETGLOBAL: A = globals[constants[AUX]]
    GetGlobal = 7,
    /// SETGLOBAL: globals[constants[AUX]] = A
    SetGlobal = 8,
    /// GETUPVAL: A = upvalues[B]
    GetUpval = 9,
    /// SETUPVAL: upvalues[B] = A
    SetUpval = 10,
    /// CLOSEUPVALS: close upvalues >= A
    CloseUpvals = 11,
    /// GETIMPORT: A = import(constants[D]); AUX encodes import path
    GetImport = 12,
    /// GETTABLE: A = B[C]
    GetTable = 13,
    /// SETTABLE: B[C] = A
    SetTable = 14,
    /// GETTABLEKS: A = B[constants[AUX]]
    GetTableKS = 15,
    /// SETTABLEKS: B[constants[AUX]] = A
    SetTableKS = 16,
    /// GETTABLEN: A = B[C+1]
    GetTableN = 17,
    /// SETTABLEN: B[C+1] = A
    SetTableN = 18,
    /// NEWCLOSURE: A = closure(protos[D])
    NewClosure = 19,
    /// NAMECALL: A = B[constants[AUX]]; A+1 = B (method call prep)
    NameCall = 20,
    /// CALL: A, ..A+C-2 = A(A+1, ..A+B-1)
    Call = 21,
    /// RETURN: return A, ..A+B-2
    Return = 22,
    /// JUMP: pc += D
    Jump = 23,
    /// JUMPBACK: pc += D (with interrupt check)
    JumpBack = 24,
    /// JUMPIF: if A then pc += D
    JumpIf = 25,
    /// JUMPIFNOT: if not A then pc += D
    JumpIfNot = 26,
    /// JUMPIFEQ: if A == AUX then pc += D
    JumpIfEq = 27,
    /// JUMPIFLE: if A <= AUX then pc += D
    JumpIfLe = 28,
    /// JUMPIFLT: if A < AUX then pc += D
    JumpIfLt = 29,
    /// JUMPIFNOTEQ: if A ~= AUX then pc += D
    JumpIfNotEq = 30,
    /// JUMPIFNOTLE: if not (A <= AUX) then pc += D
    JumpIfNotLe = 31,
    /// JUMPIFNOTLT: if not (A < AUX) then pc += D
    JumpIfNotLt = 32,
    /// ADD: A = B + C
    Add = 33,
    /// SUB: A = B - C
    Sub = 34,
    /// MUL: A = B * C
    Mul = 35,
    /// DIV: A = B / C
    Div = 36,
    /// MOD: A = B % C
    Mod = 37,
    /// POW: A = B ^ C
    Pow = 38,
    /// ADDK: A = B + constants[C]
    AddK = 39,
    /// SUBK: A = B - constants[C]
    SubK = 40,
    /// MULK: A = B * constants[C]
    MulK = 41,
    /// DIVK: A = B / constants[C]
    DivK = 42,
    /// MODK: A = B % constants[C]
    ModK = 43,
    /// POWK: A = B ^ constants[C]
    PowK = 44,
    /// AND: A = B and C
    And = 45,
    /// OR: A = B or C
    Or = 46,
    /// ANDK: A = B and constants[C]
    AndK = 47,
    /// ORK: A = B or constants[C]
    OrK = 48,
    /// CONCAT: A = B .. B+1 .. ... .. C
    Concat = 49,
    /// NOT: A = not B
    Not = 50,
    /// MINUS: A = -B
    Minus = 51,
    /// LENGTH: A = #B
    Length = 52,
    /// NEWTABLE: A = {} (B=log2 hash size, AUX=array size)
    NewTable = 53,
    /// DUPTABLE: A = table template from constants[D]
    DupTable = 54,
    /// SETLIST: A[AUX..] = A+1, ..A+B (C=count or 0=MULTRET)
    SetList = 55,
    /// FORNPREP: prepare numeric for, skip if done; A=base, D=jump
    ForNPrep = 56,
    /// FORNLOOP: iterate numeric for; A=base, D=jump back
    ForNLoop = 57,
    /// FORGLOOP: iterate generic for; A=base, D=jump back, AUX=varcount
    ForGLoop = 58,
    /// FORGPREP_INEXT: prepare ipairs-style generic for
    ForGPrepINext = 59,
    /// FASTCALL3: fast call with 3 register args
    FastCall3 = 60,
    /// FORGPREP_NEXT: prepare pairs-style generic for
    ForGPrepNext = 61,
    /// NATIVECALL: (pseudo-instruction, runtime only)
    NativeCall = 62,
    /// GETVARARGS: A, ..A+B-2 = ...
    GetVarArgs = 63,
    /// DUPCLOSURE: A = closure from constants[D] (shared proto)
    DupClosure = 64,
    /// PREPVARARGS: prepare vararg stack; A = fixed arg count
    PrepVarArgs = 65,
    /// LOADKX: A = constants[AUX]
    LoadKX = 66,
    /// JUMPX: pc += E (24-bit signed, with interrupt)
    JumpX = 67,
    /// FASTCALL: fast call builtin; A=builtin_id, C=jump offset
    FastCall = 68,
    /// COVERAGE: hit counter (E format)
    Coverage = 69,
    /// CAPTURE: capture upvalue for preceding NEWCLOSURE
    Capture = 70,
    /// SUBRK: A = constants[C] - B
    SubRK = 71,
    /// DIVRK: A = constants[C] / B
    DivRK = 72,
    /// FASTCALL1: fast call with 1 register arg
    FastCall1 = 73,
    /// FASTCALL2: fast call with 2 register args
    FastCall2 = 74,
    /// FASTCALL2K: fast call with 1 reg + 1 constant arg
    FastCall2K = 75,
    /// FORGPREP: prepare generic for loop, jump to backedge
    ForGPrep = 76,
    /// JUMPXEQKNIL: if A == nil (±NOT flag) then pc += D
    JumpXEqKNil = 77,
    /// JUMPXEQKB: if A == (bool)(AUX low bit) (±NOT flag) then pc += D
    JumpXEqKB = 78,
    /// JUMPXEQKN: if A == constants[AUX & 0xFFFFFF] (±NOT flag) then pc += D
    JumpXEqKN = 79,
    /// JUMPXEQKS: if A == constants[AUX & 0xFFFFFF] (±NOT flag) then pc += D
    JumpXEqKS = 80,
    /// IDIV: A = B // C (floor division)
    IDiv = 81,
    /// IDIVK: A = B // constants[C]
    IDivK = 82,
}

impl OpCode {
    /// Try to convert a raw opcode byte to an OpCode.
    pub fn from_byte(byte: u8) -> Option<Self> {
        if byte <= 82 {
            // SAFETY: all values 0..=82 are valid OpCode discriminants
            Some(unsafe { std::mem::transmute(byte) })
        } else {
            None
        }
    }

    /// Whether this opcode is followed by an AUX word.
    pub fn has_aux(self) -> bool {
        matches!(
            self,
            OpCode::GetGlobal
                | OpCode::SetGlobal
                | OpCode::GetImport
                | OpCode::GetTableKS
                | OpCode::SetTableKS
                | OpCode::NameCall
                | OpCode::JumpIfEq
                | OpCode::JumpIfLe
                | OpCode::JumpIfLt
                | OpCode::JumpIfNotEq
                | OpCode::JumpIfNotLe
                | OpCode::JumpIfNotLt
                | OpCode::NewTable
                | OpCode::SetList
                | OpCode::ForGLoop
                | OpCode::LoadKX
                | OpCode::FastCall2
                | OpCode::FastCall2K
                | OpCode::FastCall3
                | OpCode::JumpXEqKNil
                | OpCode::JumpXEqKB
                | OpCode::JumpXEqKN
                | OpCode::JumpXEqKS
        )
    }
}
