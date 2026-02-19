use std::fs;
use std::path::Path;

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

    let verbose = paths.len() == 1;
    let mut report = PipelineReport::new();

    for path in &paths {
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

        // Temporary: dump debug scopes when DEBUG_SCOPES=1
        if std::env::var("DEBUG_SCOPES").is_ok() {
            for (fi, f) in chunk.functions.iter().enumerate() {
                if emit_func != Some(fi) { continue; }
                let func_name = chunk.get_string(f.debug.func_name_index).unwrap_or_else(|| format!("fn#{}", fi));
                eprintln!("=== Debug scopes for {} (fn #{}) — {} entries ===", func_name, fi, f.debug.scopes.all_scopes().len());
                for scope in f.debug.scopes.all_scopes() {
                    eprintln!("  r{} = '{}' pc {}..{}", scope.register, scope.name, scope.pc_range.start, scope.pc_range.end);
                }
            }
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
                let bc_func = &chunk.functions[func_idx];
                let ((), vars_duration) = timing::timed(|| {
                    lantern_vars::recover_variables(
                        &mut hir,
                        &bc_func.debug.scopes,
                        bc_func.num_params,
                    );
                });
                func_timings.record(PHASE_VARS, vars_duration);

                // Expression simplification: collapse multi-return, then inline temps
                let ((), exprs_duration) = timing::timed(|| {
                    lantern_exprs::collapse_multi_returns(&mut hir);
                    lantern_exprs::eliminate_temporaries(&mut hir);
                });
                func_timings.record(PHASE_EXPRS, exprs_duration);

                // CFG structuring: collapse flat blocks into nested control flow
                let ((), structure_duration) = timing::timed(|| {
                    lantern_structure::structure_function(&mut hir);
                });
                func_timings.record(PHASE_STRUCTURE, structure_duration);

                // Post-structuring patterns: normalize elseif chains, merge conditions
                let ((), patterns_duration) = timing::timed(|| {
                    lantern_structure::apply_patterns(&mut hir);
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

            print!("{}", lua_source);
            if verbose {
                eprintln!("-- file emit: {:.2?} --", emit_duration);
            }
        } else if verbose && emit_func.is_none() {
            println!(
                "Parsed: {} ({:.2?})",
                path, parse_duration,
            );
        }

        report.add(file_timings);
    }

    report.print_summary();

    if report.total_functions() > 10 {
        report.print_slowest(15);
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
