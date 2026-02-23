use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{bail, Context, Result};

#[derive(Debug, Default)]
pub struct AnalyzeReport {
    pub syntax_errors: usize,
    pub other_diagnostics: usize,
    pub samples: Vec<String>,
}

impl AnalyzeReport {
    pub fn total_diagnostics(&self) -> usize {
        self.syntax_errors + self.other_diagnostics
    }
}

pub fn run_luau_analyze(paths: &[PathBuf]) -> Result<AnalyzeReport> {
    let mut report = AnalyzeReport::default();

    // Keep command lines at a reasonable size.
    for chunk in paths.chunks(200) {
        let mut cmd = Command::new("luau-analyze");
        cmd.arg("--formatter=plain");
        for path in chunk {
            cmd.arg(path);
        }

        let output = cmd.output().context("failed to execute luau-analyze")?;
        if !output.status.success() {
            bail!(
                "luau-analyze failed with status {}",
                output.status.code().unwrap_or(-1)
            );
        }

        parse_output(&mut report, &output.stdout, &output.stderr);
    }

    Ok(report)
}

pub fn classify_issue(path: &Path, report: &AnalyzeReport) -> Option<&'static str> {
    if report.syntax_errors > 0 {
        return Some("syntax");
    }
    if report.total_diagnostics() > 0 {
        // Preserve future extension point for per-file policy.
        let _ = path;
        return Some("diagnostic");
    }
    None
}

fn parse_output(report: &mut AnalyzeReport, stdout: &[u8], stderr: &[u8]) {
    let mut text = String::new();
    text.push_str(&String::from_utf8_lossy(stdout));
    if !stderr.is_empty() {
        if !text.ends_with('\n') {
            text.push('\n');
        }
        text.push_str(&String::from_utf8_lossy(stderr));
    }

    for line in text.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        if !looks_like_diagnostic(line) {
            continue;
        }
        if report.samples.len() < 30 {
            report.samples.push(line.to_string());
        }
        if line.contains("SyntaxError:") {
            report.syntax_errors += 1;
        } else {
            report.other_diagnostics += 1;
        }
    }
}

fn looks_like_diagnostic(line: &str) -> bool {
    line.contains(": (W") && line.contains(')')
}
