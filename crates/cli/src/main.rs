use std::fs;

use lantern_hir::timing::{self, FileTimings, FuncTimings, PipelineReport, PHASE_LIFT};

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.is_empty() {
        eprintln!("usage: lantern <file.l64> [file2.l64 ...]");
        std::process::exit(1);
    }

    let verbose = args.len() == 1;
    let mut report = PipelineReport::new();

    for path in &args {
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

        for i in 0..chunk.functions.len() {
            let func_name = chunk
                .get_string(chunk.functions[i].debug.func_name_index)
                .unwrap_or_else(|| format!("fn#{}", i));

            let mut func_timings = FuncTimings::new(&func_name);

            let (hir, lift_duration) = timing::timed(|| lantern_lift::lift_function(&chunk, i));
            func_timings.record(PHASE_LIFT, lift_duration);

            if verbose {
                let stmt_count: usize = hir
                    .cfg
                    .node_weights()
                    .map(|b| b.stmts.len())
                    .sum();
                println!(
                    "  fn #{}: {} — {} blocks, {} edges, {} exprs, {} stmts ({:.2?})",
                    i,
                    func_name,
                    hir.cfg.node_count(),
                    hir.cfg.edge_count(),
                    hir.exprs.len(),
                    stmt_count,
                    lift_duration,
                );
            }

            file_timings.functions.push(func_timings);
        }

        if verbose {
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
