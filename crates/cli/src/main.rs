use std::fs;

fn main() {
    let path = std::env::args().nth(1).expect("usage: lantern <file.l64>");
    let data = fs::read(&path).expect("failed to read file");

    // FS25 uses encode_key = 1
    match lantern_bytecode::deserialize(&data, 1) {
        Ok(chunk) => {
            println!("Parsed: {}", path);
            println!("  strings: {}", chunk.string_table.len());
            println!("  functions: {}", chunk.functions.len());
            println!("  main: #{}", chunk.main);

            let main_fn = chunk.main_function();
            let name = chunk.get_string(main_fn.debug.func_name_index);
            println!(
                "  main function: {} ({} params, {} upvalues, {} instructions, {} constants)",
                name.as_deref().unwrap_or("<anonymous>"),
                main_fn.num_params,
                main_fn.num_upvalues,
                main_fn.instructions.len(),
                main_fn.constants.len(),
            );

            // Print all function names
            for (i, func) in chunk.functions.iter().enumerate() {
                let name = chunk.get_string(func.debug.func_name_index);
                let scopes = func.debug.scopes.all_scopes();
                println!(
                    "  fn #{}: {} (params={}, stack={}, insns={}, scopes={})",
                    i,
                    name.as_deref().unwrap_or("<anonymous>"),
                    func.num_params,
                    func.max_stack_size,
                    func.instructions.len(),
                    scopes.len(),
                );
            }
        }
        Err(e) => {
            eprintln!("Error: {}", e);
            std::process::exit(1);
        }
    }
}
