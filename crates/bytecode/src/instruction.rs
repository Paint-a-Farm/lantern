use crate::opcode::OpCode;

/// A decoded Luau bytecode instruction.
///
/// Instructions come in three formats:
/// - **ABC**: opcode(8) + A(8) + B(8) + C(8), optionally followed by AUX(32)
/// - **AD**: opcode(8) + A(8) + D(16 signed), optionally followed by AUX(32)
/// - **E**: opcode(8) + E(24 signed)
#[derive(Debug, Clone, Copy)]
pub struct Instruction {
    pub op: OpCode,
    pub a: u8,
    pub b: u8,
    pub c: u8,
    pub d: i16,
    pub e: i32,
    pub aux: u32,
}

impl Instruction {
    /// Decode a single 32-bit instruction word with the given encode key.
    pub fn decode(word: u32, encode_key: u8) -> Option<Self> {
        let raw_op = (word & 0xFF) as u8;
        let op_byte = raw_op.wrapping_mul(encode_key);
        let op = OpCode::from_byte(op_byte)?;

        let a = ((word >> 8) & 0xFF) as u8;
        let b = ((word >> 16) & 0xFF) as u8;
        let c = ((word >> 24) & 0xFF) as u8;
        let d = ((word >> 16) & 0xFFFF) as i16;
        let e = (word as i32) >> 8;

        Some(Self {
            op,
            a,
            b,
            c,
            d,
            e,
            aux: 0,
        })
    }

    /// Set the AUX word for this instruction.
    pub fn with_aux(mut self, aux: u32) -> Self {
        self.aux = aux;
        self
    }

    /// Decode an instruction stream from raw u32 words.
    ///
    /// Instructions that require AUX words consume two words. A NOP placeholder
    /// is inserted for the AUX word's slot to keep PC indices aligned.
    pub fn decode_all(words: &[u32], encode_key: u8) -> Vec<Self> {
        let mut instructions = Vec::with_capacity(words.len());
        let mut pc = 0;

        while pc < words.len() {
            let insn = Self::decode(words[pc], encode_key)
                .unwrap_or_else(|| panic!("invalid opcode at PC {}", pc));

            if insn.op.has_aux() && pc + 1 < words.len() {
                let aux = words[pc + 1];
                instructions.push(insn.with_aux(aux));
                // Insert NOP placeholder for AUX word
                instructions.push(Self {
                    op: OpCode::Nop,
                    a: 0,
                    b: 0,
                    c: 0,
                    d: 0,
                    e: 0,
                    aux: 0,
                });
                pc += 2;
            } else {
                instructions.push(insn);
                pc += 1;
            }
        }

        instructions
    }
}
