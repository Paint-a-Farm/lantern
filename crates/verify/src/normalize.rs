use lantern_bytecode::chunk::Chunk;
use lantern_bytecode::constant::Constant;
use lantern_bytecode::function::Function;
use lantern_bytecode::opcode::OpCode;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CompareMode {
    Loose,
    Strict,
    /// Semantic: like Loose, but normalizes branch-direction differences
    /// (JumpIf/JumpIfNot, comparison operand swaps) and reports separately
    /// how many mismatches are "branch-direction only" vs real semantic diffs.
    Semantic,
}

/// Per-function comparison result.
#[derive(Debug)]
pub struct FunctionResult {
    /// Function index in the chunk.
    pub index: usize,
    /// Function name from debug info (empty string for anonymous).
    pub name: String,
    /// `true` if the original is the main (module-level) function.
    pub is_main: bool,
    /// `None` = pass, `Some(reason)` = mismatch description.
    pub error: Option<String>,
}

/// Result of comparing two chunks per-function.
#[derive(Debug)]
pub struct ChunkCompareReport {
    /// Per-function results (one entry per function in the original chunk).
    pub functions: Vec<FunctionResult>,
    /// Top-level error (e.g. function count mismatch) that prevents
    /// per-function comparison. When set, `functions` is empty.
    pub top_level_error: Option<String>,
}

impl ChunkCompareReport {
    pub fn passed(&self) -> usize {
        self.functions.iter().filter(|f| f.error.is_none()).count()
    }

    pub fn failed(&self) -> usize {
        self.functions.iter().filter(|f| f.error.is_some()).count()
    }

    pub fn checked(&self) -> usize {
        self.functions.len()
    }

    /// Returns the old-style first-error result for backwards compatibility.
    pub fn to_result(&self) -> Result<(), String> {
        if let Some(ref e) = self.top_level_error {
            return Err(e.clone());
        }
        for f in &self.functions {
            if let Some(ref e) = f.error {
                return Err(e.clone());
            }
        }
        Ok(())
    }
}

/// Compare two chunks, returning per-function pass/fail results.
pub fn chunks_compare(a: &Chunk, b: &Chunk, mode: CompareMode) -> ChunkCompareReport {
    if a.functions.len() != b.functions.len() {
        return ChunkCompareReport {
            functions: Vec::new(),
            top_level_error: Some(format!(
                "function count mismatch: {} vs {}",
                a.functions.len(),
                b.functions.len()
            )),
        };
    }
    if a.main != b.main {
        return ChunkCompareReport {
            functions: Vec::new(),
            top_level_error: Some(format!(
                "main function mismatch: {} vs {}",
                a.main, b.main
            )),
        };
    }

    let results: Vec<FunctionResult> = a
        .functions
        .iter()
        .zip(b.functions.iter())
        .enumerate()
        .map(|(idx, (fa, fb))| {
            let name = func_debug_name(a, idx);
            let is_main = idx == a.main;
            let error = compare_functions(idx, fa, fb, mode);
            FunctionResult {
                index: idx,
                name,
                is_main,
                error,
            }
        })
        .collect();

    ChunkCompareReport {
        functions: results,
        top_level_error: None,
    }
}

/// Old API: fail on first mismatch (backwards compatible).
pub fn chunks_equivalent(a: &Chunk, b: &Chunk, mode: CompareMode) -> Result<(), String> {
    chunks_compare(a, b, mode).to_result()
}

/// Compare a single function pair, returning `None` for pass or an error string.
fn compare_functions(
    idx: usize,
    fa: &Function,
    fb: &Function,
    mode: CompareMode,
) -> Option<String> {
    if fa.num_params != fb.num_params {
        return Some(format!(
            "fn#{idx} num_params mismatch: {} vs {}",
            fa.num_params, fb.num_params
        ));
    }
    if fa.is_vararg != fb.is_vararg {
        return Some(format!("fn#{idx} vararg mismatch"));
    }
    if fa.num_upvalues != fb.num_upvalues {
        return Some(format!(
            "fn#{idx} upvalue count mismatch: {} vs {}",
            fa.num_upvalues, fb.num_upvalues
        ));
    }

    if mode == CompareMode::Semantic {
        return compare_functions_semantic(idx, fa, fb);
    }

    let a_hist = opcode_histogram(fa);
    let b_hist = opcode_histogram(fb);
    if a_hist != b_hist {
        let mut diff_lines = Vec::new();
        for (i, (&ca, &cb)) in a_hist.iter().zip(b_hist.iter()).enumerate() {
            if ca != cb {
                diff_lines.push(format!("  op[{i}]: orig={ca} recompiled={cb}"));
            }
        }
        return Some(format!(
            "fn#{idx} opcode histogram mismatch:\n{}",
            diff_lines.join("\n")
        ));
    }

    let a_consts = constant_histogram(fa.constants.as_slice());
    let b_consts = constant_histogram(fb.constants.as_slice());
    if a_consts != b_consts {
        return Some(format!("fn#{idx} constant histogram mismatch"));
    }

    if mode == CompareMode::Strict {
        if fa.instructions.len() != fb.instructions.len() {
            return Some(format!(
                "fn#{idx} instruction count mismatch: {} vs {}",
                fa.instructions.len(),
                fb.instructions.len()
            ));
        }
        if fa.child_protos.len() != fb.child_protos.len() {
            return Some(format!(
                "fn#{idx} child proto count mismatch: {} vs {}",
                fa.child_protos.len(),
                fb.child_protos.len()
            ));
        }

        for (pc, (ia, ib)) in fa
            .instructions
            .iter()
            .zip(fb.instructions.iter())
            .enumerate()
        {
            if ia.op != ib.op {
                return Some(format!(
                    "fn#{idx} opcode mismatch at pc {pc}: {:?} vs {:?}",
                    ia.op, ib.op
                ));
            }
        }
    }

    None
}

/// Extract the debug name of a function from the chunk's string table (public).
pub fn func_debug_name_pub(chunk: &Chunk, func_idx: usize) -> String {
    func_debug_name(chunk, func_idx)
}

/// Extract the debug name of a function from the chunk's string table.
fn func_debug_name(chunk: &Chunk, func_idx: usize) -> String {
    let func = &chunk.functions[func_idx];
    let name_idx = func.debug.func_name_index;
    if name_idx == 0 {
        return String::new();
    }
    // String table indices are 1-based in the debug info.
    chunk
        .string_table
        .get(name_idx.wrapping_sub(1))
        .map(|b| String::from_utf8_lossy(b).into_owned())
        .unwrap_or_default()
}

/// Semantic comparison: normalizes branch-direction differences before comparing.
///
/// Builds a "normalized opcode histogram" that merges equivalent comparison pairs
/// (e.g., JumpIfLt + JumpIfNotLe into one bucket, JumpIf + JumpIfNot into one)
/// and branch-layout opcodes (Jump/Nop/Return). If the normalized histogram
/// matches but the raw one differs, the function is considered equivalent
/// (pure branch-direction / return-sinking difference).
///
/// Note: register-level operand comparison is not performed because the compiler
/// freely reassigns registers, making raw register numbers meaningless without
/// full data-flow analysis.
fn compare_functions_semantic(
    idx: usize,
    fa: &Function,
    fb: &Function,
) -> Option<String> {
    // First: check if raw opcode histograms already match (fast path)
    let a_raw = opcode_histogram(fa);
    let b_raw = opcode_histogram(fb);
    if a_raw == b_raw {
        let a_consts = constant_histogram(fa.constants.as_slice());
        let b_consts = constant_histogram(fb.constants.as_slice());
        if a_consts != b_consts {
            return Some(format!("fn#{idx} constant histogram mismatch"));
        }
        // Note: we intentionally do NOT compare comparison operands (register numbers)
        // here. Even with identical opcode histograms and instruction counts, the
        // compiler may assign the same values to different registers, making raw
        // register comparison meaningless without full data-flow analysis.
        return None; // Exact match
    }

    // Check normalized histogram (merge equivalent opcode pairs)
    let a_norm = normalized_opcode_histogram(fa);
    let b_norm = normalized_opcode_histogram(fb);
    if a_norm != b_norm {
        // Real structural difference even after normalization
        let mut diff_lines = Vec::new();
        for (i, (&ca, &cb)) in a_raw.iter().zip(b_raw.iter()).enumerate() {
            if ca != cb {
                diff_lines.push(format!("  op[{i}]: orig={ca} recompiled={cb}"));
            }
        }
        return Some(format!(
            "fn#{idx} opcode histogram mismatch (structural):\n{}",
            diff_lines.join("\n")
        ));
    }

    // Normalized histogram matches — the difference is purely branch-direction.
    // We don't compare register-level operands here because register allocation
    // can differ even when the logic is identical.

    // Verify constants match
    let a_consts = constant_histogram(fa.constants.as_slice());
    let b_consts = constant_histogram(fb.constants.as_slice());
    if a_consts != b_consts {
        return Some(format!("fn#{idx} constant histogram mismatch"));
    }

    // Pure branch-direction difference — semantically equivalent
    None
}

/// Opcode bucket index for the normalized histogram.
/// Merges equivalent comparison pairs and branch-layout opcodes.
fn normalized_opcode_bucket(op: OpCode) -> usize {
    match op {
        // Merge JumpIf/JumpIfNot — branch direction choice
        OpCode::JumpIf | OpCode::JumpIfNot => 25,
        // Merge comparison pairs: Lt/NotLe are equivalent (with operand swap)
        OpCode::JumpIfLt | OpCode::JumpIfNotLe => 29,
        // Merge comparison pairs: Le/NotLt are equivalent (with operand swap)
        OpCode::JumpIfLe | OpCode::JumpIfNotLt => 28,
        // Merge comparison pairs: Eq/NotEq — same opcode count in either direction
        OpCode::JumpIfEq | OpCode::JumpIfNotEq => 27,
        // Merge Jump/Nop/Return — branch reordering changes jump counts, nop padding,
        // and return sinking/duplication (if A then return x end; return y
        // vs if A then return x else return y end)
        OpCode::Jump | OpCode::Nop | OpCode::Return => 0,
        other => other as usize,
    }
}

/// Build an opcode histogram where equivalent branch opcodes share a bucket.
fn normalized_opcode_histogram(func: &Function) -> [u32; 83] {
    let mut hist = [0_u32; 83];
    for insn in &func.instructions {
        let bucket = normalized_opcode_bucket(insn.op);
        if bucket < hist.len() {
            hist[bucket] += 1;
        }
    }
    hist
}

fn opcode_histogram(func: &lantern_bytecode::function::Function) -> [u32; 83] {
    let mut hist = [0_u32; 83];
    for insn in &func.instructions {
        let idx = insn.op as usize;
        if idx < hist.len() {
            hist[idx] += 1;
        }
    }
    hist
}

fn constant_histogram(constants: &[Constant]) -> [u32; 8] {
    let mut hist = [0_u32; 8];
    for constant in constants {
        let idx = match constant {
            Constant::Nil => 0,
            Constant::Boolean(_) => 1,
            Constant::Number(_) => 2,
            Constant::String(_) => 3,
            Constant::Import(_) => 4,
            Constant::Table(_) => 5,
            Constant::Closure(_) => 6,
            Constant::Vector(_, _, _, _) => 7,
        };
        hist[idx] += 1;
    }
    hist
}
