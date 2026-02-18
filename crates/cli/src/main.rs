use std::fs;
use std::time::Instant;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.is_empty() {
        eprintln!("usage: lantern <file.l64> [file2.l64 ...]");
        std::process::exit(1);
    }

    let total_start = Instant::now();
    let mut total_functions = 0usize;
    let mut total_blocks = 0usize;
    let mut total_exprs = 0usize;
    let mut file_count = 0usize;

    for path in &args {
        let data = match fs::read(path) {
            Ok(d) => d,
            Err(e) => {
                eprintln!("Error reading {}: {}", path, e);
                continue;
            }
        };

        let parse_start = Instant::now();
        let chunk = match lantern_bytecode::deserialize(&data, 1) {
            Ok(c) => c,
            Err(e) => {
                eprintln!("Parse error {}: {}", path, e);
                continue;
            }
        };
        let parse_elapsed = parse_start.elapsed();

        let lift_start = Instant::now();
        let mut func_count = 0;
        let mut blocks = 0;
        let mut exprs = 0;

        for i in 0..chunk.functions.len() {
            let hir = lantern_lift::lift_function(&chunk, i);
            blocks += hir.cfg.node_count();
            exprs += hir.exprs.len();
            func_count += 1;
        }
        let lift_elapsed = lift_start.elapsed();

        if args.len() == 1 {
            // Detailed per-function output for single file
            println!("Parsed: {} ({:.2?})", path, parse_elapsed);
            println!("  strings: {}", chunk.string_table.len());
            println!("  functions: {}", chunk.functions.len());

            for (i, func) in chunk.functions.iter().enumerate() {
                let name = chunk.get_string(func.debug.func_name_index);
                let hir = lantern_lift::lift_function(&chunk, i);
                let stmt_count: usize = hir.cfg.node_weights()
                    .map(|b| b.stmts.len())
                    .sum();

                println!(
                    "  fn #{}: {} — {} blocks, {} edges, {} exprs, {} stmts",
                    i,
                    name.as_deref().unwrap_or("<anonymous>"),
                    hir.cfg.node_count(),
                    hir.cfg.edge_count(),
                    hir.exprs.len(),
                    stmt_count,
                );
            }
            println!("  lift: {:.2?}", lift_elapsed);
        } else {
            // Summary for batch mode
            let short_name = path.rsplit('/').next().unwrap_or(path);
            println!(
                "{}: {} funcs, {} blocks, {} exprs (parse {:.2?}, lift {:.2?})",
                short_name, func_count, blocks, exprs, parse_elapsed, lift_elapsed,
            );
        }

        total_functions += func_count;
        total_blocks += blocks;
        total_exprs += exprs;
        file_count += 1;
    }

    if file_count > 1 {
        let total_elapsed = total_start.elapsed();
        println!("\n--- Totals ---");
        println!(
            "{} files, {} functions, {} blocks, {} exprs in {:.2?}",
            file_count, total_functions, total_blocks, total_exprs, total_elapsed,
        );
    }
}
