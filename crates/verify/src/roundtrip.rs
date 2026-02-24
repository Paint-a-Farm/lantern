use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{SystemTime, UNIX_EPOCH};

use anyhow::{bail, Context, Result};
use clap::{Args, ValueEnum};

use crate::analyze;
use crate::normalize::{self, CompareMode};

#[derive(Debug, Clone, Copy, ValueEnum)]
pub enum CompareModeArg {
    Loose,
    Strict,
}

#[derive(Debug, Args)]
pub struct RoundtripArgs {
    /// Input .l64 file(s) or directories (recursively scanned).
    #[arg(required = true)]
    pub inputs: Vec<PathBuf>,

    /// Bytecode decode key for source .l64 files.
    #[arg(long, default_value_t = 1)]
    pub encode_key: u8,

    /// Output directory for generated .lua files.
    /// If omitted, a temp directory is used.
    #[arg(long)]
    pub out_dir: Option<PathBuf>,

    /// Keep output files when using a temporary output directory.
    #[arg(long)]
    pub keep_output: bool,

    /// Skip recompile+bytecode comparison phase.
    #[arg(long)]
    pub skip_roundtrip_compile: bool,

    /// Fail if luau-analyze reports any diagnostic (not just syntax errors).
    #[arg(long)]
    pub fail_on_analyze_diagnostics: bool,

    /// Structural comparison strictness for bytecode roundtrip.
    #[arg(long, value_enum, default_value_t = CompareModeArg::Loose)]
    pub compare_mode: CompareModeArg,

    /// Print the list of source files that pass roundtrip (one per line).
    #[arg(long)]
    pub list_passing: bool,

    /// Print all failures (not just the first 10).
    #[arg(long)]
    pub list_failing: bool,
}

#[derive(Debug)]
struct GeneratedCase {
    source_path: PathBuf,
    output_path: PathBuf,
}

#[derive(Debug, Default)]
struct CompileRoundtripReport {
    checked: usize,
    failures: Vec<String>,
    passed: Vec<PathBuf>,
}

pub fn run(args: RoundtripArgs) -> Result<()> {
    ensure_command_available("luau-analyze")?;
    if !args.skip_roundtrip_compile {
        ensure_command_available("luau-compile")?;
    }

    let mut input_files = collect_input_files(&args.inputs)?;
    input_files.sort();
    if input_files.is_empty() {
        bail!("no .l64/.luau files found in input paths");
    }

    let (output_dir, is_temp) = prepare_output_dir(args.out_dir.as_deref())?;
    println!(
        "lantern-verify: writing decompiled files to {}",
        output_dir.display()
    );

    // Compile any .luau inputs to .l64 bytecode first.
    let l64_files = prepare_l64_inputs(&input_files, &output_dir)?;

    let generated = decompile_inputs(&l64_files, &output_dir, args.encode_key)?;
    let generated_paths: Vec<PathBuf> = generated.iter().map(|c| c.output_path.clone()).collect();

    let analyze_report = analyze::run_luau_analyze(&generated_paths)?;
    let analyze_total = analyze_report.total_diagnostics();
    println!(
        "luau-analyze: {} diagnostics ({} syntax errors)",
        analyze_total, analyze_report.syntax_errors
    );
    for line in analyze_report.samples.iter().take(10) {
        println!("  {}", line);
    }

    let mut hard_failures: Vec<String> = Vec::new();
    if analyze_report.syntax_errors > 0 {
        hard_failures.push(format!(
            "luau-analyze reported {} syntax errors",
            analyze_report.syntax_errors
        ));
    }
    if args.fail_on_analyze_diagnostics && analyze_total > 0 {
        hard_failures.push(format!(
            "luau-analyze reported {} diagnostics and --fail-on-analyze-diagnostics is set",
            analyze_total
        ));
    }

    let compile_report = if args.skip_roundtrip_compile {
        None
    } else {
        Some(run_compile_roundtrip(
            &generated,
            args.encode_key,
            to_compare_mode(args.compare_mode),
        ))
    };

    if let Some(report) = &compile_report {
        println!(
            "compile roundtrip: {} checked, {} passed, {} mismatches",
            report.checked,
            report.passed.len(),
            report.failures.len()
        );
        let limit = if args.list_failing { report.failures.len() } else { 10 };
        for line in report.failures.iter().take(limit) {
            println!("  {}", line);
        }
        if args.list_passing {
            for path in &report.passed {
                println!("PASS: {}", path.display());
            }
        }
        if !report.failures.is_empty() {
            hard_failures.push(format!(
                "compile roundtrip reported {} mismatches",
                report.failures.len()
            ));
        }
    }

    if hard_failures.is_empty() {
        println!("verification passed: {} files checked", input_files.len());
        if is_temp && !args.keep_output {
            fs::remove_dir_all(&output_dir).with_context(|| {
                format!("failed to delete temp output {}", output_dir.display())
            })?;
        }
        return Ok(());
    }

    if is_temp {
        println!(
            "verification failed; generated output kept at {}",
            output_dir.display()
        );
    }
    bail!(hard_failures.join("; "))
}

fn to_compare_mode(mode: CompareModeArg) -> CompareMode {
    match mode {
        CompareModeArg::Loose => CompareMode::Loose,
        CompareModeArg::Strict => CompareMode::Strict,
    }
}

fn run_compile_roundtrip(
    cases: &[GeneratedCase],
    source_encode_key: u8,
    compare_mode: CompareMode,
) -> CompileRoundtripReport {
    let mut report = CompileRoundtripReport::default();

    for case in cases {
        report.checked += 1;
        match verify_case_roundtrip(case, source_encode_key, compare_mode) {
            Ok(()) => {
                report.passed.push(case.source_path.clone());
            }
            Err(err) => {
                report
                    .failures
                    .push(format!("{} -> {}", case.source_path.display(), err));
            }
        }
    }

    report
}

fn verify_case_roundtrip(
    case: &GeneratedCase,
    source_encode_key: u8,
    compare_mode: CompareMode,
) -> Result<()> {
    let source_bytes = fs::read(&case.source_path)
        .with_context(|| format!("failed to read source {}", case.source_path.display()))?;
    let source_chunk =
        lantern_bytecode::deserialize(&source_bytes, source_encode_key).map_err(|e| {
            anyhow::anyhow!(
                "failed to parse source bytecode {}: {}",
                case.source_path.display(),
                e
            )
        })?;

    let compiled_output = compile_luau_binary(&case.output_path)?;
    let recompiled_chunk = deserialize_compiled_chunk(&compiled_output)?;

    normalize::chunks_equivalent(&source_chunk, &recompiled_chunk, compare_mode).map_err(
        |why| {
            anyhow::anyhow!(
                "structural mismatch for {}: {}",
                case.output_path.display(),
                why
            )
        },
    )?;

    Ok(())
}

fn compile_luau_binary(lua_path: &Path) -> Result<Vec<u8>> {
    let output = Command::new("luau-compile")
        .arg("--binary")
        .arg("-O2")
        .arg("-g2")
        .arg(lua_path)
        .output()
        .with_context(|| format!("failed to run luau-compile for {}", lua_path.display()))?;

    if !output.status.success() {
        bail!(
            "luau-compile failed for {}: {}",
            lua_path.display(),
            String::from_utf8_lossy(&output.stderr).trim()
        );
    }
    if output.stdout.is_empty() {
        bail!(
            "luau-compile produced empty output for {}",
            lua_path.display()
        );
    }

    Ok(output.stdout)
}

fn deserialize_compiled_chunk(compiled: &[u8]) -> Result<lantern_bytecode::chunk::Chunk> {
    // luau-compile outputs unencoded bytecode. Key 1 is the identity under
    // wrapping_mul, so it's the correct key for unencoded data.
    lantern_bytecode::deserialize(compiled, 1)
        .map_err(|e| anyhow::anyhow!("failed to parse recompiled bytecode: {}", e))
}

fn decompile_inputs(
    inputs: &[PathBuf],
    out_dir: &Path,
    encode_key: u8,
) -> Result<Vec<GeneratedCase>> {
    let mut cases = Vec::with_capacity(inputs.len());
    for (idx, path) in inputs.iter().enumerate() {
        let bytes = fs::read(path).with_context(|| format!("failed to read {}", path.display()))?;
        let lua = lantern::decompile_bytecode(&bytes, encode_key);
        if lua.starts_with("-- lantern parse error:") {
            bail!(
                "decompiler parse error for {}: {}",
                path.display(),
                lua.trim()
            );
        }

        let output_name = format!("{:05}_{}.lua", idx, sanitize_path_component(path));
        let output_path = out_dir.join(output_name);
        fs::write(&output_path, lua).with_context(|| {
            format!("failed to write generated output {}", output_path.display())
        })?;

        cases.push(GeneratedCase {
            source_path: path.clone(),
            output_path,
        });
    }
    Ok(cases)
}

fn sanitize_path_component(path: &Path) -> String {
    let raw = path
        .file_stem()
        .or_else(|| path.file_name())
        .and_then(|s| s.to_str())
        .unwrap_or("file");
    raw.chars()
        .map(|ch| {
            if ch.is_ascii_alphanumeric() || ch == '_' || ch == '-' {
                ch
            } else {
                '_'
            }
        })
        .collect()
}

fn prepare_output_dir(out_dir: Option<&Path>) -> Result<(PathBuf, bool)> {
    if let Some(out) = out_dir {
        fs::create_dir_all(out)
            .with_context(|| format!("failed to create output directory {}", out.display()))?;
        return Ok((out.to_path_buf(), false));
    }

    let stamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_millis())
        .unwrap_or(0);
    let dir = std::env::temp_dir().join(format!("lantern-verify-{}-{}", std::process::id(), stamp));
    fs::create_dir_all(&dir)
        .with_context(|| format!("failed to create temp output directory {}", dir.display()))?;
    Ok((dir, true))
}

fn ensure_command_available(name: &str) -> Result<()> {
    let status = Command::new(name)
        .arg("--help")
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status();
    match status {
        Ok(_) => Ok(()),
        Err(err) if err.kind() == std::io::ErrorKind::NotFound => {
            bail!("{name} is not installed or not in PATH")
        }
        Err(err) => bail!("failed to check {name}: {err}"),
    }
}

fn collect_input_files(inputs: &[PathBuf]) -> Result<Vec<PathBuf>> {
    let mut files = Vec::new();
    for input in inputs {
        if input.is_dir() {
            collect_from_dir(input, &mut files)?;
        } else if input
            .extension()
            .is_some_and(|ext| ext == "l64" || ext == "luau")
        {
            files.push(input.clone());
        } else {
            bail!(
                "input is neither a directory nor a .l64/.luau file: {}",
                input.display()
            );
        }
    }
    Ok(files)
}

fn collect_from_dir(dir: &Path, out: &mut Vec<PathBuf>) -> Result<()> {
    let entries =
        fs::read_dir(dir).with_context(|| format!("failed to list directory {}", dir.display()))?;

    for entry in entries {
        let entry = entry.with_context(|| format!("failed to read entry in {}", dir.display()))?;
        let path = entry.path();
        if path.is_dir() {
            collect_from_dir(&path, out)?;
        } else if path
            .extension()
            .is_some_and(|ext| ext == "l64" || ext == "luau")
        {
            out.push(path);
        }
    }
    Ok(())
}

/// Compile any `.luau` inputs to `.l64` bytecode via luau-compile, returning
/// the final list of `.l64` paths (originals kept as-is, `.luau` replaced
/// with compiled temp files).
fn prepare_l64_inputs(inputs: &[PathBuf], tmp_dir: &Path) -> Result<Vec<PathBuf>> {
    let mut out = Vec::with_capacity(inputs.len());
    for path in inputs {
        if path.extension().is_some_and(|ext| ext == "luau") {
            let bytecode = compile_luau_binary(path)?;
            let stem = path.file_stem().and_then(|s| s.to_str()).unwrap_or("case");
            let l64_path = tmp_dir.join(format!("{}.l64", stem));
            fs::write(&l64_path, bytecode).with_context(|| {
                format!("failed to write compiled bytecode for {}", path.display())
            })?;
            out.push(l64_path);
        } else {
            out.push(path.clone());
        }
    }
    Ok(out)
}
