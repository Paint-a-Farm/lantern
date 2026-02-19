use std::fs;
use std::path::{Path, PathBuf};

use lantern_hir::timing::{self, FileTimings, FuncTimings, PipelineReport, PHASE_EMIT, PHASE_EXPRS, PHASE_LIFT, PHASE_PATTERNS, PHASE_STRUCTURE, PHASE_VARS};

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.is_empty() {
        eprintln!("usage: lantern [--emit N | --file] <file.l64> [file2.l64 ...]");
        std::process::exit(1);
    }

    // Parse flags
    let mut emit_func: Option<usize> = None;
    let mut file_mode = false;
    let mut raw_mode = false;
    let mut no_format = false;
    let mut dump_bc = false;
    let mut output_dir: Option<String> = None;
    let mut paths = Vec::new();
    let mut i = 0;
    while i < args.len() {
        if args[i] == "--emit" {
            i += 1;
            emit_func = Some(args[i].parse().expect("--emit expects a function index"));
        } else if args[i] == "--file" {
            file_mode = true;
        } else if args[i] == "--raw" {
            raw_mode = true;
        } else if args[i] == "--no-format" {
            no_format = true;
        } else if args[i] == "--dump" {
            dump_bc = true;
        } else if args[i] == "--output-dir" {
            i += 1;
            output_dir = Some(args[i].clone());
            file_mode = true; // --output-dir implies --file
        } else {
            paths.push(args[i].clone());
        }
        i += 1;
    }

    // Expand directories into .l64 files recursively
    let mut expanded_paths = Vec::new();
    for path in &paths {
        let p = Path::new(path);
        if p.is_dir() {
            collect_l64_files(p, &mut expanded_paths);
        } else {
            expanded_paths.push(path.clone());
        }
    }
    expanded_paths.sort();
    let paths = expanded_paths;

    // Determine base directory for relative path computation when using --output-dir
    let base_dir: Option<PathBuf> = output_dir.as_ref().map(|_| {
        // Use the first input path's parent as the base for relative paths
        let first = Path::new(&paths[0]);
        if first.is_dir() {
            first.to_path_buf()
        } else {
            first.parent().unwrap_or(Path::new(".")).to_path_buf()
        }
    });

    let verbose = paths.len() == 1 && output_dir.is_none();
    let mut report = PipelineReport::new();
    let total_files = paths.len();

    for (file_idx, path) in paths.iter().enumerate() {
        if output_dir.is_some() && total_files > 1 {
            eprint!("\r[{}/{}] {}                    ", file_idx + 1, total_files, path);
        }

        let data = match fs::read(path) {
            Ok(d) => d,
            Err(e) => {
                eprintln!("Error reading {}: {}", path, e);
                continue;
            }
        };

        let (chunk, parse_duration) = timing::timed(|| lantern_bytecode::deserialize(&data, 1));
        let chunk = match chunk {
            Ok(c) => c,
            Err(e) => {
                eprintln!("Parse error {}: {}", path, e);
                continue;
            }
        };

            // Dump bytecode if requested
        if dump_bc {
            for (fi, f) in chunk.functions.iter().enumerate() {
                if let Some(target) = emit_func {
                    if fi != target { continue; }
                }
                let func_name = chunk.get_string(f.debug.func_name_index).unwrap_or_else(|| format!("fn#{}", fi));
                println!("=== fn #{}: {} ({} instructions) ===", fi, func_name, f.instructions.len());
                for (pc, insn) in f.instructions.iter().enumerate() {
                    let const_str = match insn.op {
                        lantern_bytecode::opcode::OpCode::GetTableKS
                        | lantern_bytecode::opcode::OpCode::SetTableKS
                        | lantern_bytecode::opcode::OpCode::NameCall => {
                            if pc + 1 < f.instructions.len() {
                                let aux = f.instructions[pc + 1].aux;
                                chunk.get_string(aux as usize).map(|s| format!(" ; \"{}\"", s))
                            } else { None }
                        }
                        lantern_bytecode::opcode::OpCode::LoadK => {
                            if let Some(c) = f.constants.get(insn.d as usize) {
                                Some(format!(" ; {:?}", c))
                            } else { None }
                        }
                        lantern_bytecode::opcode::OpCode::GetImport => {
                            let id = insn.d as u32;
                            let count = (id >> 30) as u8;
                            let mut parts = Vec::new();
                            let bits = id & 0x3FFFFFFF;
                            for j in 0..count {
                                let idx = ((bits >> (20 - 10 * j)) & 0x3FF) as usize;
                                if let Some(s) = chunk.get_string(idx) {
                                    parts.push(s);
                                }
                            }
                            if !parts.is_empty() {
                                Some(format!(" ; {}", parts.join(".")))
                            } else { None }
                        }
                        _ => None,
                    };
                    let aux_str = if insn.op.has_aux() {
                        format!(" aux=0x{:08X}", insn.aux)
                    } else { String::new() };
                    println!("  {:4}  {:?}\tA={} B={} C={} D={} E={}{}{}",
                        pc, insn.op, insn.a, insn.b, insn.c, insn.d, insn.e,
                        aux_str, const_str.unwrap_or_default());
                }
                println!();
            }
            continue;
        }

        let mut file_timings = FileTimings::new(path.as_str());
        file_timings.parse_time = parse_duration;

        // Lift all functions
        let mut hir_funcs: Vec<Option<lantern_hir::func::HirFunc>> =
            (0..chunk.functions.len()).map(|_| None).collect();

        for func_idx in 0..chunk.functions.len() {
            let func_name = chunk
                .get_string(chunk.functions[func_idx].debug.func_name_index)
                .unwrap_or_else(|| format!("fn#{}", func_idx));

            let mut func_timings = FuncTimings::new(&func_name);

            let (mut hir, lift_duration) =
                timing::timed(|| lantern_lift::lift_function(&chunk, func_idx));
            func_timings.record(PHASE_LIFT, lift_duration);

            // Variable recovery: resolve registers → named variables
            if !raw_mode {
                let debug_cfg = std::env::var("DEBUG_CFG").is_ok() && emit_func == Some(func_idx);

                let bc_func = &chunk.functions[func_idx];

                let ((), vars_duration) = timing::timed(|| {
                    lantern_vars::recover_variables(
                        &mut hir,
                        &bc_func.debug.scopes,
                        bc_func.num_params,
                    );
                });
                func_timings.record(PHASE_VARS, vars_duration);

                if debug_cfg {
                    eprintln!("=== AFTER VARS (fn #{}) ===", func_idx);
                    dump_cfg_blocks(&hir);
                }

                // Expression simplification: collapse multi-return, then inline temps
                // (before structuring — the structurer inspects body sizes for guard detection)
                let ((), exprs_duration) = timing::timed(|| {
                    lantern_exprs::collapse_multi_returns(&mut hir);
                    lantern_exprs::eliminate_temporaries(&mut hir);
                    lantern_exprs::fold_table_constructors(&mut hir);
                    lantern_exprs::eliminate_temporaries(&mut hir);
                });
                func_timings.record(PHASE_EXPRS, exprs_duration);

                if debug_cfg {
                    eprintln!("=== AFTER EXPRS (fn #{}) ===", func_idx);
                    dump_cfg_blocks(&hir);
                }

                // CFG structuring: collapse flat blocks into nested control flow
                let ((), structure_duration) = timing::timed(|| {
                    lantern_structure::structure_function(&mut hir);
                });
                func_timings.record(PHASE_STRUCTURE, structure_duration);

                if debug_cfg {
                    eprintln!("=== AFTER STRUCTURE (fn #{}) ===", func_idx);
                    dump_cfg_blocks(&hir);
                }

                // Post-structuring patterns: normalize elseif chains, merge conditions
                let ((), patterns_duration) = timing::timed(|| {
                    lantern_structure::apply_patterns(&mut hir);
                    // Second inline pass: catch temps inside structured bodies
                    lantern_exprs::eliminate_temporaries(&mut hir);
                    lantern_exprs::fold_table_constructors(&mut hir);
                    lantern_exprs::eliminate_temporaries(&mut hir);
                });
                func_timings.record(PHASE_PATTERNS, patterns_duration);
            }

            if verbose && !file_mode {
                let stmt_count: usize =
                    hir.cfg.node_weights().map(|b| b.stmts.len()).sum();
                println!(
                    "  fn #{}: {} — {} blocks, {} edges, {} exprs, {} stmts ({:.2?})",
                    func_idx,
                    func_name,
                    hir.cfg.node_count(),
                    hir.cfg.edge_count(),
                    hir.exprs.len(),
                    stmt_count,
                    lift_duration,
                );
            }

            // Emit Lua source for the selected function
            if emit_func == Some(func_idx) {
                let (lua_source, emit_duration) =
                    timing::timed(|| lantern_emit::emit_function(&hir));
                func_timings.record(PHASE_EMIT, emit_duration);

                println!("\n-- fn #{} --", func_idx);
                print!("{}", lua_source);
                println!("-- emit: {:.2?} --", emit_duration);
            }

            file_timings.functions.push(func_timings);
            hir_funcs[func_idx] = Some(hir);
        }

        // Full-file emission mode
        if file_mode {
            // Build child_protos mapping from bytecode
            let child_protos: Vec<Vec<usize>> = chunk
                .functions
                .iter()
                .map(|f| f.child_protos.clone())
                .collect();

            // Unwrap all HirFuncs (they were all lifted above)
            let funcs: Vec<lantern_hir::func::HirFunc> = hir_funcs
                .into_iter()
                .map(|f| f.expect("all functions should be lifted"))
                .collect();

            let (lua_source, emit_duration) = timing::timed(|| {
                lantern_emit::emit_file(&funcs, &child_protos, chunk.main)
            });

            let (output, format_duration) = if no_format {
                (lua_source, std::time::Duration::ZERO)
            } else {
                timing::timed(|| format_luau(&lua_source, path))
            };

            if let Some(ref out_dir) = output_dir {
                // Write to output directory, preserving relative path structure
                let src_path = Path::new(path);
                let rel = if let Some(ref base) = base_dir {
                    src_path.strip_prefix(base).unwrap_or(src_path.file_name().map(Path::new).unwrap_or(src_path))
                } else {
                    src_path
                };
                let mut out_path = PathBuf::from(out_dir);
                out_path.push(rel);
                out_path.set_extension("lua");
                if let Some(parent) = out_path.parent() {
                    fs::create_dir_all(parent).ok();
                }
                match fs::write(&out_path, &output) {
                    Ok(_) => {}
                    Err(e) => eprintln!("Error writing {}: {}", out_path.display(), e),
                }
            } else {
                print!("{}", output);
            }
            if verbose {
                eprintln!("-- file emit: {:.2?}, format: {:.2?} --", emit_duration, format_duration);
            }
        } else if verbose && emit_func.is_none() {
            println!(
                "Parsed: {} ({:.2?})",
                path, parse_duration,
            );
        }

        report.add(file_timings);
    }

    if output_dir.is_some() && total_files > 1 {
        eprintln!(); // newline after progress counter
    }

    report.print_summary();

    if report.total_functions() > 10 {
        report.print_slowest(15);
    }
}

fn format_luau(code: &str, path: &str) -> String {
    let mut config = stylua_lib::Config::new();
    config.syntax = stylua_lib::LuaVersion::Luau;
    config.indent_type = stylua_lib::IndentType::Tabs;
    config.indent_width = 4;
    config.column_width = 999;
    match stylua_lib::format_code(code, config, None, stylua_lib::OutputVerification::None) {
        Ok(formatted) => formatted,
        Err(e) => {
            eprintln!("stylua format error in {}: {}", path, e);
            code.to_string()
        }
    }
}

fn dump_cfg_blocks(hir: &lantern_hir::func::HirFunc) {
    for node in hir.cfg.node_indices() {
        let block = &hir.cfg[node];
        eprintln!("  block {:?} (pc {:?}): {} stmts, terminator={:?}",
            node, block.pc_range, block.stmts.len(), block.terminator);
        for (i, stmt) in block.stmts.iter().enumerate() {
            eprintln!("    stmt[{}]: {:?}", i, stmt);
        }
    }
}

fn collect_l64_files(dir: &Path, out: &mut Vec<String>) {
    let entries = match fs::read_dir(dir) {
        Ok(e) => e,
        Err(_) => return,
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_l64_files(&path, out);
        } else if path.extension().is_some_and(|e| e == "l64") {
            out.push(path.to_string_lossy().into_owned());
        }
    }
}
