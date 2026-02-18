use std::fs;

use lantern_hir::timing::{self, FileTimings, FuncTimings, PipelineReport, PHASE_EMIT, PHASE_EXPRS, PHASE_LIFT, PHASE_PATTERNS, PHASE_STRUCTURE, PHASE_VARS};

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.is_empty() {
        eprintln!("usage: lantern [--emit N] <file.l64> [file2.l64 ...]");
        std::process::exit(1);
    }

    // Parse flags
    let mut emit_func: Option<usize> = None;
    let mut raw_mode = false;
    let mut paths = Vec::new();
    let mut i = 0;
    while i < args.len() {
        if args[i] == "--emit" {
            i += 1;
            emit_func = Some(args[i].parse().expect("--emit expects a function index"));
        } else if args[i] == "--raw" {
            raw_mode = true;
        } else {
            paths.push(args[i].clone());
        }
        i += 1;
    }

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

        let mut file_timings = FileTimings::new(path.as_str());
        file_timings.parse_time = parse_duration;

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

                // Temporary elimination: inline single-use unnamed variables
                let ((), exprs_duration) = timing::timed(|| {
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

            if verbose {
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

                println!("\n-- {} (fn #{}) --", func_name, func_idx);
                println!("{}", lua_source);
                println!("-- emit: {:.2?} --", emit_duration);
            }

            file_timings.functions.push(func_timings);
        }

        if verbose && emit_func.is_none() {
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
