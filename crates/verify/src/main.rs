use anyhow::Result;
use clap::{Parser, Subcommand};

use lantern_verify::generator::{self, GrammarCasesArgs};
use lantern_verify::roundtrip::{self, RoundtripArgs};

#[derive(Debug, Parser)]
#[command(
    name = "lantern-verify",
    about = "Verification helpers for lantern decompiler output"
)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Debug, Subcommand)]
enum Command {
    /// Decompile one or more .l64 files and verify generated Lua via luau-analyze.
    Roundtrip(RoundtripArgs),
    /// Generate and validate grammar-backed Luau test cases.
    GrammarCases(GrammarCasesArgs),
}

fn real_main() -> Result<()> {
    let cli = Cli::parse();
    match cli.command {
        Command::Roundtrip(args) => roundtrip::run(args),
        Command::GrammarCases(args) => generator::run_grammar_cases(args),
    }
}

fn main() -> Result<()> {
    // Spawn with a larger stack to handle deeply recursive IR traversals
    // (matching the CLI binary's 32 MB stack).
    let builder = std::thread::Builder::new().stack_size(32 * 1024 * 1024);
    builder
        .spawn(|| real_main())
        .expect("failed to spawn main thread")
        .join()
        .expect("main thread panicked")
}
