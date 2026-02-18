use std::time::{Duration, Instant};
use rustc_hash::FxHashMap;

/// Phase names used throughout the pipeline.
pub const PHASE_PARSE: &str = "parse";
pub const PHASE_LIFT: &str = "lift";
pub const PHASE_VARS: &str = "vars";
pub const PHASE_PATTERNS: &str = "patterns";
pub const PHASE_STRUCTURE: &str = "structure";
pub const PHASE_EXPRS: &str = "exprs";
pub const PHASE_EMIT: &str = "emit";

/// Tracks per-phase timing for a single function decompilation.
#[derive(Debug, Clone)]
pub struct FuncTimings {
    pub func_name: String,
    pub phases: Vec<(String, Duration)>,
}

impl FuncTimings {
    pub fn new(func_name: impl Into<String>) -> Self {
        Self {
            func_name: func_name.into(),
            phases: Vec::new(),
        }
    }

    pub fn record(&mut self, phase: &str, duration: Duration) {
        self.phases.push((phase.to_string(), duration));
    }

    pub fn total(&self) -> Duration {
        self.phases.iter().map(|(_, d)| *d).sum()
    }
}

/// Aggregated timing report across all functions in a file.
#[derive(Debug, Clone)]
pub struct FileTimings {
    pub file_name: String,
    pub parse_time: Duration,
    pub functions: Vec<FuncTimings>,
}

impl FileTimings {
    pub fn new(file_name: impl Into<String>) -> Self {
        Self {
            file_name: file_name.into(),
            parse_time: Duration::ZERO,
            functions: Vec::new(),
        }
    }

    pub fn total_lift(&self) -> Duration {
        self.functions.iter()
            .flat_map(|f| f.phases.iter())
            .filter(|(p, _)| p == PHASE_LIFT)
            .map(|(_, d)| *d)
            .sum()
    }

    pub fn total_all_phases(&self) -> Duration {
        self.parse_time + self.functions.iter().map(|f| f.total()).sum::<Duration>()
    }
}

/// Aggregated report across all files.
pub struct PipelineReport {
    pub files: Vec<FileTimings>,
}

impl PipelineReport {
    pub fn new() -> Self {
        Self { files: Vec::new() }
    }

    pub fn add(&mut self, file: FileTimings) {
        self.files.push(file);
    }

    pub fn total_functions(&self) -> usize {
        self.files.iter().map(|f| f.functions.len()).sum()
    }

    pub fn phase_totals(&self) -> FxHashMap<String, Duration> {
        let mut totals = FxHashMap::default();
        // Parse phase
        let parse_total: Duration = self.files.iter().map(|f| f.parse_time).sum();
        totals.insert(PHASE_PARSE.to_string(), parse_total);

        // Per-function phases
        for file in &self.files {
            for func in &file.functions {
                for (phase, duration) in &func.phases {
                    *totals.entry(phase.clone()).or_insert(Duration::ZERO) += *duration;
                }
            }
        }
        totals
    }

    pub fn grand_total(&self) -> Duration {
        self.files.iter().map(|f| f.total_all_phases()).sum()
    }

    /// Print a summary table.
    pub fn print_summary(&self) {
        let totals = self.phase_totals();
        let grand = self.grand_total();
        let func_count = self.total_functions();
        let file_count = self.files.len();

        println!("\n--- Performance Summary ---");
        println!("{} files, {} functions in {:.2?}", file_count, func_count, grand);
        println!();

        // Print phases in pipeline order
        let phase_order = [
            PHASE_PARSE, PHASE_LIFT, PHASE_VARS, PHASE_PATTERNS,
            PHASE_STRUCTURE, PHASE_EXPRS, PHASE_EMIT,
        ];
        for &phase in &phase_order {
            if let Some(&dur) = totals.get(phase) {
                let pct = if grand.as_nanos() > 0 {
                    dur.as_nanos() as f64 / grand.as_nanos() as f64 * 100.0
                } else {
                    0.0
                };
                println!("  {:12} {:>10.2?}  ({:.1}%)", phase, dur, pct);
            }
        }

        if func_count > 0 {
            let avg = grand / func_count as u32;
            println!("\n  avg/function: {:.2?}", avg);
        }
    }

    /// Print the N slowest functions.
    pub fn print_slowest(&self, n: usize) {
        let mut all_funcs: Vec<(&str, &FuncTimings)> = self.files.iter()
            .flat_map(|f| f.functions.iter().map(move |func| (f.file_name.as_str(), func)))
            .collect();

        all_funcs.sort_by(|a, b| b.1.total().cmp(&a.1.total()));

        println!("\n--- Slowest {} Functions ---", n);
        for (file, func) in all_funcs.into_iter().take(n) {
            let short_file = file.rsplit('/').next().unwrap_or(file);
            print!("  {:.2?}  {}::{}", func.total(), short_file, func.func_name);
            // Show phase breakdown
            let parts: Vec<String> = func.phases.iter()
                .map(|(p, d)| format!("{}={:.2?}", p, d))
                .collect();
            println!("  [{}]", parts.join(", "));
        }
    }
}

/// Convenience: time a closure and return (result, duration).
pub fn timed<F, T>(f: F) -> (T, Duration)
where
    F: FnOnce() -> T,
{
    let start = Instant::now();
    let result = f();
    (result, start.elapsed())
}
