use rustc_hash::FxHashMap;

use crate::expr::HirExpr;
use crate::var::VarId;

/// Opaque expression identifier. Index into ExprArena.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ExprId(pub u32);

/// Flat arena storing all expressions in a function.
///
/// Expressions reference each other by ExprId, not by nesting.
/// This enables O(1) substitution: to replace a variable with an
/// expression, just overwrite the slot.
#[derive(Debug, Clone)]
pub struct ExprArena {
    exprs: Vec<HirExpr>,
}

impl ExprArena {
    pub fn new() -> Self {
        Self { exprs: Vec::new() }
    }

    /// Allocate a new expression, returns its id.
    pub fn alloc(&mut self, expr: HirExpr) -> ExprId {
        let id = ExprId(self.exprs.len() as u32);
        self.exprs.push(expr);
        id
    }

    /// Get an expression by id.
    pub fn get(&self, id: ExprId) -> &HirExpr {
        &self.exprs[id.0 as usize]
    }

    /// Get a mutable expression by id.
    pub fn get_mut(&mut self, id: ExprId) -> &mut HirExpr {
        &mut self.exprs[id.0 as usize]
    }

    /// Replace an expression in-place. O(1).
    pub fn replace(&mut self, id: ExprId, expr: HirExpr) {
        self.exprs[id.0 as usize] = expr;
    }

    /// Replace all references to a variable with a copy of the given expression.
    /// Used for temporary elimination.
    pub fn substitute_var(&mut self, var: VarId, replacement: ExprId) {
        for i in 0..self.exprs.len() {
            if let HirExpr::Var(v) = &self.exprs[i] {
                if *v == var {
                    // Clone the replacement expression into this slot
                    self.exprs[i] = self.exprs[replacement.0 as usize].clone();
                }
            }
        }
    }

    /// Batch substitute: replace multiple variables in a single pass.
    /// Much faster than calling substitute_var() N times (O(n) vs O(n*k)).
    pub fn substitute_vars_batch(&mut self, subs: &FxHashMap<VarId, ExprId>) {
        if subs.is_empty() {
            return;
        }
        for i in 0..self.exprs.len() {
            if let HirExpr::Var(v) = &self.exprs[i] {
                if let Some(&replacement) = subs.get(v) {
                    self.exprs[i] = self.exprs[replacement.0 as usize].clone();
                }
            }
        }
    }

    /// Number of expressions allocated.
    pub fn len(&self) -> usize {
        self.exprs.len()
    }

    pub fn is_empty(&self) -> bool {
        self.exprs.is_empty()
    }

    /// Negate a condition expression, producing the logical inverse.
    ///
    /// Applies simplifications:
    /// - `not (not x)` → `x` (double negation elimination)
    /// - `a == b` → `a ~= b` (comparison inversion)
    /// - `a < b` → `a >= b`, etc.
    /// - Otherwise wraps in `not(expr)`
    pub fn negate_condition(&mut self, condition: ExprId) -> ExprId {
        use crate::expr::HirExpr;
        use crate::types::{BinOp, UnOp};

        // Double negation: not(not x) → x
        if let HirExpr::Unary {
            op: UnOp::Not,
            operand,
        } = self.get(condition)
        {
            return *operand;
        }

        // Comparison inversion
        if let HirExpr::Binary { op, left, right } = self.get(condition).clone() {
            let inv_op = match op {
                BinOp::CompareEq => Some(BinOp::CompareNe),
                BinOp::CompareNe => Some(BinOp::CompareEq),
                BinOp::CompareLt => Some(BinOp::CompareGe),
                BinOp::CompareLe => Some(BinOp::CompareGt),
                BinOp::CompareGt => Some(BinOp::CompareLe),
                BinOp::CompareGe => Some(BinOp::CompareLt),
                _ => None,
            };
            if let Some(inv_op) = inv_op {
                return self.alloc(HirExpr::Binary {
                    op: inv_op,
                    left,
                    right,
                });
            }
        }

        // Fallback: wrap in not()
        self.alloc(HirExpr::Unary {
            op: UnOp::Not,
            operand: condition,
        })
    }
}
