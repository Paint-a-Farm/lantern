use nom::number::complete::{le_f32, le_f64, le_u32, le_u8};
use nom::IResult;

use crate::{leb128_usize, parse_list};

/// A constant value in the function's constant table.
#[derive(Debug, Clone)]
pub enum Constant {
    Nil,
    Boolean(bool),
    Number(f64),
    /// Index into the chunk's string table (1-based).
    String(usize),
    /// Encoded import path (3x10-bit indices + 2-bit length in high bits).
    Import(u32),
    /// Table template: list of constant indices for hash keys.
    Table(Vec<usize>),
    /// Child proto index for closure.
    Closure(usize),
    /// 4D vector (x, y, z, w).
    Vector(f32, f32, f32, f32),
}

const TAG_NIL: u8 = 0;
const TAG_BOOLEAN: u8 = 1;
const TAG_NUMBER: u8 = 2;
const TAG_STRING: u8 = 3;
const TAG_IMPORT: u8 = 4;
const TAG_TABLE: u8 = 5;
const TAG_CLOSURE: u8 = 6;
const TAG_VECTOR: u8 = 7;

impl Constant {
    pub fn parse(input: &[u8]) -> IResult<&[u8], Self> {
        let (input, tag) = le_u8(input)?;
        match tag {
            TAG_NIL => Ok((input, Constant::Nil)),
            TAG_BOOLEAN => {
                let (input, val) = le_u8(input)?;
                Ok((input, Constant::Boolean(val != 0)))
            }
            TAG_NUMBER => {
                let (input, val) = le_f64(input)?;
                Ok((input, Constant::Number(val)))
            }
            TAG_STRING => {
                let (input, idx) = leb128_usize(input)?;
                Ok((input, Constant::String(idx)))
            }
            TAG_IMPORT => {
                let (input, val) = le_u32(input)?;
                Ok((input, Constant::Import(val)))
            }
            TAG_TABLE => {
                let (input, keys) = parse_list(input, leb128_usize)?;
                Ok((input, Constant::Table(keys)))
            }
            TAG_CLOSURE => {
                let (input, id) = leb128_usize(input)?;
                Ok((input, Constant::Closure(id)))
            }
            TAG_VECTOR => {
                let (input, x) = le_f32(input)?;
                let (input, y) = le_f32(input)?;
                let (input, z) = le_f32(input)?;
                let (input, w) = le_f32(input)?;
                Ok((input, Constant::Vector(x, y, z, w)))
            }
            _ => panic!("unknown constant tag: {}", tag),
        }
    }

    /// Decode an import path from a 32-bit encoded value.
    /// Returns (path_length, id0, id1, id2) where ids are 10-bit constant indices.
    pub fn decode_import(encoded: u32) -> (u8, u32, u32, u32) {
        let count = (encoded >> 30) as u8;
        let id0 = (encoded >> 20) & 0x3FF;
        let id1 = (encoded >> 10) & 0x3FF;
        let id2 = encoded & 0x3FF;
        (count, id0, id1, id2)
    }
}
