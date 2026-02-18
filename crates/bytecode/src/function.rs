use nom::number::complete::{le_u32, le_u8};
use nom::IResult;

use crate::constant::Constant;
use crate::instruction::Instruction;
use crate::scope_tree::{LocalScope, ScopeTree};
use crate::{leb128_usize, parse_list, parse_list_len};

/// Debug information for a bytecode function.
#[derive(Debug, Clone)]
pub struct DebugInfo {
    /// Function name (index into string table, 0 = anonymous).
    pub func_name_index: usize,
    /// Variable scopes indexed by register and PC range.
    pub scopes: ScopeTree,
    /// Upvalue name indices (1-based into string table, 0 = unnamed).
    pub upvalue_name_indices: Vec<usize>,
    /// Line number for the function definition.
    pub line_defined: usize,
    /// Per-instruction line deltas (if available).
    pub line_info: Option<LineInfo>,
}

/// Line number information for mapping PCs to source lines.
#[derive(Debug, Clone)]
pub struct LineInfo {
    pub line_gap_log2: u8,
    pub line_deltas: Vec<u8>,
    pub abs_line_info: Vec<u32>,
    pub base_line: usize,
}

impl LineInfo {
    /// Get the source line number for a given PC.
    pub fn line_for_pc(&self, pc: usize, line_defined: usize) -> usize {
        // Compute line from deltas up to PC
        let mut line = line_defined;
        for i in 0..pc.min(self.line_deltas.len()) {
            line = line.wrapping_add(self.line_deltas[i] as usize);
        }
        line
    }
}

/// A parsed bytecode function prototype.
#[derive(Debug, Clone)]
pub struct Function {
    pub max_stack_size: u8,
    pub num_params: u8,
    pub num_upvalues: u8,
    pub is_vararg: bool,
    pub flags: u8,
    /// Type info bytes (version 6).
    pub type_info: Vec<u8>,
    /// Decoded instructions with AUX words inlined.
    pub instructions: Vec<Instruction>,
    /// Constant pool for this function.
    pub constants: Vec<Constant>,
    /// Child proto indices.
    pub child_protos: Vec<usize>,
    /// Debug information (names, scopes, lines).
    pub debug: DebugInfo,
}

impl Function {
    pub(crate) fn parse<'a>(
        input: &'a [u8],
        encode_key: u8,
        string_table: &[Vec<u8>],
    ) -> IResult<&'a [u8], Self> {
        let (input, max_stack_size) = le_u8(input)?;
        let (input, num_params) = le_u8(input)?;
        let (input, num_upvalues) = le_u8(input)?;
        let (input, is_vararg) = le_u8(input)?;

        // Version 6: flags + type info
        let (input, flags) = le_u8(input)?;
        let (input, type_info) = parse_list(input, le_u8)?;

        // Instructions (as raw u32 words)
        let (input, raw_words) = parse_list(input, le_u32)?;
        let instructions = Instruction::decode_all(&raw_words, encode_key);

        // Constants
        let (input, constants) = parse_list(input, Constant::parse)?;

        // Child proto indices
        let (input, child_protos) = parse_list(input, leb128_usize)?;

        // Line info
        let (input, line_defined) = leb128_usize(input)?;
        let (input, func_name_index) = leb128_usize(input)?;

        let (input, has_line_info) = le_u8(input)?;
        let (input, line_info) = if has_line_info != 0 {
            let (input, line_gap_log2) = le_u8(input)?;
            let (input, line_deltas) = parse_list_len(input, le_u8, raw_words.len())?;
            let abs_count = ((raw_words.len().saturating_sub(1)) >> line_gap_log2) + 1;
            let (input, abs_line_info) = parse_list_len(input, le_u32, abs_count)?;
            (
                input,
                Some(LineInfo {
                    line_gap_log2,
                    line_deltas,
                    abs_line_info,
                    base_line: line_defined,
                }),
            )
        } else {
            (input, None)
        };

        // Debug info: local variable scopes
        let (input, has_debug) = le_u8(input)?;
        let (input, scopes, upvalue_name_indices) = if has_debug != 0 {
            let (input, num_locals) = leb128_usize(input)?;
            let mut local_scopes = Vec::with_capacity(num_locals);
            let mut input = input;
            for _ in 0..num_locals {
                let (rest, name_index) = leb128_usize(input)?;
                let (rest, scope_start) = leb128_usize(rest)?;
                let (rest, scope_end) = leb128_usize(rest)?;
                let (rest, register) = le_u8(rest)?;
                input = rest;

                // Resolve name from string table (1-based index)
                let name = if name_index > 0 && name_index <= string_table.len() {
                    String::from_utf8_lossy(&string_table[name_index - 1]).to_string()
                } else {
                    continue; // skip unnamed debug entries
                };

                local_scopes.push(LocalScope {
                    register,
                    name,
                    pc_range: scope_start..scope_end,
                });
            }

            let (input, num_upval_names) = leb128_usize(input)?;
            let mut upvalue_names = Vec::with_capacity(num_upval_names);
            let mut input = input;
            for _ in 0..num_upval_names {
                let (rest, idx) = leb128_usize(input)?;
                upvalue_names.push(idx);
                input = rest;
            }

            (input, ScopeTree::new(local_scopes), upvalue_names)
        } else {
            (input, ScopeTree::default(), Vec::new())
        };

        Ok((
            input,
            Function {
                max_stack_size,
                num_params,
                num_upvalues,
                is_vararg: is_vararg != 0,
                flags,
                type_info,
                instructions,
                constants,
                child_protos,
                debug: DebugInfo {
                    func_name_index,
                    scopes,
                    upvalue_name_indices,
                    line_defined,
                    line_info,
                },
            },
        ))
    }

    /// Get the string constant at index `idx` (1-based into string table).
    /// Must be called with the chunk's string table.
    pub fn get_string<'a>(&self, idx: usize, string_table: &'a [Vec<u8>]) -> Option<&'a [u8]> {
        if idx > 0 && idx <= string_table.len() {
            Some(&string_table[idx - 1])
        } else {
            None
        }
    }
}
