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

fn main() -> Result<()> {
    let cli = Cli::parse();
    match cli.command {
        Command::Roundtrip(args) => roundtrip::run(args),
        Command::GrammarCases(args) => generator::run_grammar_cases(args),
    }
}
