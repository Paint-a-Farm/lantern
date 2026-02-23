use std::fs;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result};

/// Collect `.luau` regression snippets from a directory tree.
pub fn collect_regression_snippets(root: &Path) -> Result<Vec<PathBuf>> {
    let mut out = Vec::new();
    collect_luau_files(root, &mut out)?;
    out.sort();
    Ok(out)
}

fn collect_luau_files(root: &Path, out: &mut Vec<PathBuf>) -> Result<()> {
    let entries =
        fs::read_dir(root).with_context(|| format!("failed to list {}", root.display()))?;
    for entry in entries {
        let entry = entry.with_context(|| format!("failed to read entry in {}", root.display()))?;
        let path = entry.path();
        if path.is_dir() {
            collect_luau_files(&path, out)?;
        } else if path.extension().is_some_and(|ext| ext == "luau") {
            out.push(path);
        }
    }
    Ok(())
}
