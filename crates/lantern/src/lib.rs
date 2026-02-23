//! Lantern — a Luau bytecode decompiler.
//!
//! This crate provides the public API for decompiling Luau bytecode
//! into readable Lua source code.

/// Decompile Luau bytecode into Lua source.
///
/// `bytecode` is the raw file contents (including the version byte and
/// any XOR encryption). `encode_key` is the cipher key used during
/// compilation (1 for FS25, 203 for Roblox).
///
/// Returns formatted Lua source code as a string.
pub fn decompile_bytecode(bytecode: &[u8], encode_key: u8) -> String {
    let chunk = match lantern_bytecode::deserialize(bytecode, encode_key) {
        Ok(c) => c,
        Err(e) => return format!("-- lantern parse error: {}\n", e),
    };

    // Lift and process all functions.
    let mut hir_funcs: Vec<Option<lantern_hir::func::HirFunc>> =
        (0..chunk.functions.len()).map(|_| None).collect();

    for func_idx in 0..chunk.functions.len() {
        let mut hir = lantern_lift::lift_function(&chunk, func_idx);

        let bc_func = &chunk.functions[func_idx];

        lantern_vars::recover_variables(&mut hir, &bc_func.debug.scopes, bc_func.num_params);

        // Expression simplification (before structuring).
        lantern_exprs::collapse_multi_returns(&mut hir);
        lantern_exprs::eliminate_temporaries(&mut hir);
        lantern_exprs::fold_table_constructors(&mut hir);
        lantern_exprs::eliminate_temporaries(&mut hir);

        // CFG structuring.
        lantern_structure::structure_function(&mut hir);

        // Post-structuring patterns and second optimization pass.
        lantern_structure::apply_patterns(&mut hir);
        lantern_exprs::eliminate_temporaries(&mut hir);
        lantern_exprs::fold_table_constructors(&mut hir);
        lantern_exprs::eliminate_temporaries(&mut hir);
        lantern_exprs::inline_branch_locals(&mut hir);

        hir_funcs[func_idx] = Some(hir);
    }

    // Emit as a complete Lua file.
    let child_protos: Vec<Vec<usize>> = chunk
        .functions
        .iter()
        .map(|f| f.child_protos.clone())
        .collect();

    let funcs: Vec<lantern_hir::func::HirFunc> = hir_funcs
        .into_iter()
        .map(|f| f.expect("all functions should be lifted"))
        .collect();

    let lua_source = lantern_emit::emit_file(&funcs, &child_protos, chunk.main);

    format_luau(&lua_source)
}

fn format_luau(code: &str) -> String {
    let mut config = stylua_lib::Config::new();
    config.syntax = stylua_lib::LuaVersion::Luau;
    config.indent_type = stylua_lib::IndentType::Tabs;
    config.indent_width = 4;
    config.column_width = 999;
    match stylua_lib::format_code(code, config, None, stylua_lib::OutputVerification::None) {
        Ok(formatted) => formatted,
        Err(_) => code.to_string(),
    }
}
