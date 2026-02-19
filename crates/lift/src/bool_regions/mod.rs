//! Boolean value region detection.
//!
//! The Luau compiler generates specific bytecode patterns when a boolean
//! expression is used as a value (assigned to a variable, passed to a
//! function, etc.). Instead of computing a boolean through control flow
//! branches, these patterns should be recognized at lift time and compiled
//! into `HirExpr::Binary { And/Or }` chains.
//!
//! ## Pattern: Simple comparison as value
//!
//! `local x = a == b` compiles to:
//! ```text
//! JUMPIFEQ R1, R2, +2     -- comparison jump
//! LOADB R0, false, +1     -- false path: set 0, skip
//! LOADB R0, true          -- true path: set 1
//! ```
//!
//! ## Pattern: Or-chain as value
//!
//! `local x = a == X or a == Y` compiles to:
//! ```text
//! LOADB R0, true          -- pre-init for left comparison
//! JUMPIFEQ R1, R3, +N     -- left true → skip to end (short-circuit)
//! JUMPIFEQ R1, R4, +2     -- right comparison jump
//! LOADB R0, false, +1     -- false path
//! LOADB R0, true          -- true path (right comparison target)
//! <next instruction>       -- short-circuit target
//! ```
//!
//! ## Detection
//!
//! The telltale signature is the `LOADB Rx, false, +1` / `LOADB Rx, true`
//! pair at the end of the region. We scan for this pair, then trace backwards
//! to find all conditional jumps that participate. The conditional jumps
//! within the region should NOT create separate basic blocks — the entire
//! region is a single expression computation.

mod and_or_ternary;
mod bool_region;
mod truthy_chain;
mod utils;
mod value_ternary;

// Public types.
pub use and_or_ternary::AndOrTernary;
pub use bool_region::BoolRegion;
pub use truthy_chain::TruthyChain;
pub use value_ternary::ValueTernary;

// Public detection functions.
pub use and_or_ternary::detect_and_or_ternaries;
pub use bool_region::{detect_bool_regions, find_bool_regions};
pub use truthy_chain::detect_truthy_chains;
pub use utils::has_aux_word;
pub use value_ternary::detect_value_ternaries;
