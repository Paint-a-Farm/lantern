use nom::number::complete::le_u8;
use nom::IResult;

use crate::function::Function;
use crate::{leb128_usize, parse_list, parse_string};

/// A parsed Luau bytecode chunk (version 6).
///
/// Contains the string table shared by all functions, the function prototypes,
/// and the index of the main (entry) function.
#[derive(Debug)]
pub struct Chunk {
    pub string_table: Vec<Vec<u8>>,
    pub functions: Vec<Function>,
    pub main: usize,
}

impl Chunk {
    pub(crate) fn parse(input: &[u8], encode_key: u8) -> IResult<&[u8], Self> {
        // Version 6 always has types_version byte
        let (input, types_version) = le_u8(input)?;
        if types_version > 3 {
            panic!("unsupported types version: {}", types_version);
        }

        // String table (shared across all functions)
        let (input, string_table) = parse_list(input, parse_string)?;

        // Skip userdataRemapping if types_version == 3
        let input = if types_version == 3 {
            let mut input = input;
            loop {
                let (rest, val) = leb128_usize(input)?;
                input = rest;
                if val == 0 {
                    break;
                }
            }
            input
        } else {
            input
        };

        // Function prototypes
        let (input, functions) = {
            let (input, count) = leb128_usize(input)?;
            let mut funcs = Vec::with_capacity(count);
            let mut input = input;
            for _ in 0..count {
                let (rest, func) = Function::parse(input, encode_key, &string_table)?;
                funcs.push(func);
                input = rest;
            }
            (input, funcs)
        };

        // Main function index
        let (input, main) = leb128_usize(input)?;

        Ok((
            input,
            Chunk {
                string_table,
                functions,
                main,
            },
        ))
    }

    /// Resolve a string table index (1-based) to a UTF-8 string.
    pub fn get_string(&self, index: usize) -> Option<String> {
        if index > 0 && index <= self.string_table.len() {
            Some(String::from_utf8_lossy(&self.string_table[index - 1]).to_string())
        } else {
            None
        }
    }

    /// Get the main function prototype.
    pub fn main_function(&self) -> &Function {
        &self.functions[self.main]
    }
}
