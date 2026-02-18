pub mod opcode;
pub mod instruction;
pub mod constant;
pub mod function;
pub mod chunk;
pub mod scope_tree;

use nom::number::complete::le_u8;
use nom::IResult;

/// Parse a LEB128-encoded unsigned integer.
pub(crate) fn leb128_usize(input: &[u8]) -> IResult<&[u8], usize> {
    let mut result: usize = 0;
    let mut shift = 0;
    let mut i = input;
    loop {
        let (rest, byte) = le_u8(i)?;
        result |= ((byte & 0x7F) as usize) << shift;
        i = rest;
        if byte & 0x80 == 0 {
            return Ok((i, result));
        }
        shift += 7;
    }
}

/// Parse a length-prefixed list using LEB128 length.
pub(crate) fn parse_list<'a, T>(
    input: &'a [u8],
    parser: impl Fn(&'a [u8]) -> IResult<&'a [u8], T>,
) -> IResult<&'a [u8], Vec<T>> {
    let (input, length) = leb128_usize(input)?;
    let mut items = Vec::with_capacity(length);
    let mut input = input;
    for _ in 0..length {
        let (rest, item) = parser(input)?;
        items.push(item);
        input = rest;
    }
    Ok((input, items))
}

/// Parse a fixed-length list.
pub(crate) fn parse_list_len<'a, T>(
    input: &'a [u8],
    parser: impl Fn(&'a [u8]) -> IResult<&'a [u8], T>,
    length: usize,
) -> IResult<&'a [u8], Vec<T>> {
    let mut items = Vec::with_capacity(length);
    let mut input = input;
    for _ in 0..length {
        let (rest, item) = parser(input)?;
        items.push(item);
        input = rest;
    }
    Ok((input, items))
}

/// Parse a length-prefixed string.
pub(crate) fn parse_string(input: &[u8]) -> IResult<&[u8], Vec<u8>> {
    let (input, length) = leb128_usize(input)?;
    let (rest, bytes) = nom::bytes::complete::take(length)(input)?;
    Ok((rest, bytes.to_owned()))
}

/// Deserialize Luau bytecode (version 6 only).
///
/// `encode_key` is the XOR multiplication key (1 for FS25, 203 for Roblox).
pub fn deserialize(bytecode: &[u8], encode_key: u8) -> Result<chunk::Chunk, String> {
    let (input, version) =
        le_u8::<_, nom::error::Error<&[u8]>>(bytecode).map_err(|e| e.to_string())?;
    if version == 0 {
        let error_msg = String::from_utf8_lossy(&bytecode[1..]).to_string();
        return Err(format!("bytecode compilation error: {}", error_msg));
    }
    if version != 6 {
        return Err(format!(
            "unsupported bytecode version: {} (lantern targets version 6 only)",
            version
        ));
    }
    match chunk::Chunk::parse(input, encode_key) {
        Ok((_, chunk)) => Ok(chunk),
        Err(err) => Err(err.to_string()),
    }
}
