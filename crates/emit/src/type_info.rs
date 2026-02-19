/// Decode Luau type_info bytes into parameter type annotations.
///
/// Type info encoding (version 6 bytecode):
///   VarInt func_sig_len
///   VarInt upval_count
///   VarInt local_count
///   func_sig bytes: [LBC_TYPE_FUNCTION, num_params, param_type_0, param_type_1, ...]
///   upval type bytes...
///   local entries: (type: u8, reg: u8, startpc: VarInt, endpc_delta: VarInt)

const LBC_TYPE_FUNCTION: u8 = 5;
const LBC_TYPE_OPTIONAL_BIT: u8 = 1 << 7;

/// Decoded parameter types from type_info.
pub struct FuncTypeInfo {
    /// Type annotation string for each parameter, in order.
    /// Empty string means no annotation / `any`.
    pub param_types: Vec<String>,
}

/// Decode type_info bytes into parameter type strings.
/// Returns None if type_info is empty or malformed.
pub fn decode_param_types(type_info: &[u8]) -> Option<FuncTypeInfo> {
    if type_info.is_empty() {
        return None;
    }

    let mut pos = 0;

    // Read three VarInts: func_sig_len, upval_count, local_count
    let func_sig_len = read_varint(type_info, &mut pos)?;
    let _upval_count = read_varint(type_info, &mut pos)?;
    let _local_count = read_varint(type_info, &mut pos)?;

    if func_sig_len < 2 {
        return None;
    }

    // func_sig bytes start at `pos`
    let sig_start = pos;
    if sig_start + func_sig_len as usize > type_info.len() {
        return None;
    }

    let sig = &type_info[sig_start..sig_start + func_sig_len as usize];

    // sig[0] should be LBC_TYPE_FUNCTION
    if sig[0] != LBC_TYPE_FUNCTION {
        return None;
    }

    let num_params = sig[1] as usize;
    let mut param_types = Vec::with_capacity(num_params);

    for i in 0..num_params {
        let type_byte = if 2 + i < sig.len() {
            sig[2 + i]
        } else {
            0 // missing = any
        };
        param_types.push(type_byte_to_string(type_byte));
    }

    Some(FuncTypeInfo { param_types })
}

fn type_byte_to_string(b: u8) -> String {
    let optional = b & LBC_TYPE_OPTIONAL_BIT != 0;
    let base = b & !LBC_TYPE_OPTIONAL_BIT;

    let name = match base {
        0 => "nil",
        1 => "boolean",
        2 => "number",
        3 => "string",
        4 => "table",
        5 => "function", // unlikely for param
        6 => "thread",
        7 => "userdata",
        8 => "vector",
        9 => "buffer",
        15 => "", // any — no annotation
        64..=95 => "userdata", // tagged userdata range
        _ => "",
    };

    if name.is_empty() {
        return String::new();
    }

    if optional {
        format!("{}?", name)
    } else {
        name.to_string()
    }
}

/// Read a LEB128-style VarInt from the byte slice.
fn read_varint(data: &[u8], pos: &mut usize) -> Option<u32> {
    let mut result: u32 = 0;
    let mut shift = 0;
    loop {
        if *pos >= data.len() {
            return None;
        }
        let byte = data[*pos];
        *pos += 1;
        result |= ((byte & 0x7F) as u32) << shift;
        if byte & 0x80 == 0 {
            break;
        }
        shift += 7;
        if shift > 28 {
            return None; // overflow protection
        }
    }
    Some(result)
}
