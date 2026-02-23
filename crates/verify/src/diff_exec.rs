use std::path::Path;

use anyhow::{bail, Result};

/// Placeholder for behavior-differential execution.
///
/// The initial verify crate focuses on static validity + structural roundtrip.
/// This function exists so callers can wire behavior checks later without API
/// churn in the crate.
pub fn compare_behavior(_original: &Path, _recompiled: &Path) -> Result<()> {
    bail!("behavior differential execution is not implemented yet")
}
