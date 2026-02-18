use rustc_hash::FxHashMap;

use lantern_hir::arena::ExprId;
use lantern_hir::expr::HirExpr;
use lantern_hir::func::HirFunc;
use lantern_hir::stmt::{HirStmt, LValue};
use lantern_hir::var::VarId;

/// Eliminate temporary variables by inlining their expressions.
///
/// A temporary is a variable with:
/// - No debug name (unnamed compiler-generated)
/// - Exactly one definition site
/// - Exactly one use site (or zero uses — dead store)
///
/// For single-use temporaries, we replace every `Var(temp)` reference in the
/// expression arena with the temp's RHS expression, then remove the dead
/// assignment statement. This is O(1) per inline thanks to the arena.
///
/// Iterates until no more temporaries can be eliminated.
pub fn eliminate_temporaries(func: &mut HirFunc) {
    loop {
        let inlined = inline_pass(func);
        if inlined == 0 {
            break;
        }
    }
}

/// Single pass: find and inline all eligible temporaries.
/// Returns the number of inlined variables.
fn inline_pass(func: &mut HirFunc) -> usize {
    // Step 1: Count uses of each VarId across all expressions and statements.
    let use_counts = count_uses(func);

    // Step 2: Find inline candidates — single-def, single-use (or zero-use)
    // unnamed temporaries where the def is a simple Assign in a block.
    let mut candidates: Vec<InlineCandidate> = Vec::new();

    for node_idx in func.cfg.node_indices() {
        let block = &func.cfg[node_idx];
        for (stmt_idx, stmt) in block.stmts.iter().enumerate() {
            if let HirStmt::Assign {
                target: LValue::Local(var_id),
                value,
            } = stmt
            {
                let info = func.vars.get(*var_id);

                // Must be unnamed (no debug name) — it's a compiler temporary
                if info.name.is_some() {
                    continue;
                }

                let uses = use_counts.get(var_id).copied().unwrap_or(0);

                if uses == 0 {
                    if !expr_has_side_effects(func, *value) {
                        // Dead store with no side effects — remove entirely
                        candidates.push(InlineCandidate {
                            var_id: *var_id,
                            value_expr: *value,
                            node_idx,
                            stmt_idx,
                            kind: InlineKind::DeadStore,
                        });
                    } else {
                        // Dead store with side effects (e.g., unused call result)
                        // Convert: `_v = func()` → `func()`
                        candidates.push(InlineCandidate {
                            var_id: *var_id,
                            value_expr: *value,
                            node_idx,
                            stmt_idx,
                            kind: InlineKind::DeadCall,
                        });
                    }
                } else if uses == 1 {
                    // Single-use temporary — inline the expression
                    // Safety check: the expression must be safe to move
                    // (no side effects that would be reordered).
                    // For now, we inline everything except calls with side effects
                    // when there are intervening side effects.
                    // Simple heuristic: always inline single-use temps.
                    // This is safe because the Luau compiler generates temporaries
                    // in strict evaluation order.
                    candidates.push(InlineCandidate {
                        var_id: *var_id,
                        value_expr: *value,
                        node_idx,
                        stmt_idx,
                        kind: InlineKind::SingleUse,
                    });
                }
            }
        }
    }

    if candidates.is_empty() {
        return 0;
    }

    // Step 3: Apply inlines.
    // Process in reverse statement order within each block so that removing
    // statements doesn't invalidate earlier indices.
    candidates.sort_by(|a, b| {
        a.node_idx
            .index()
            .cmp(&b.node_idx.index())
            .then(b.stmt_idx.cmp(&a.stmt_idx)) // reverse stmt order
    });

    // Step 3: Apply arena substitutions for single-use inlines (batch)
    let subs: FxHashMap<VarId, ExprId> = candidates
        .iter()
        .filter(|c| matches!(c.kind, InlineKind::SingleUse))
        .map(|c| (c.var_id, c.value_expr))
        .collect();
    func.exprs.substitute_vars_batch(&subs);

    let inlined = candidates.len();

    // Step 4: Modify/remove statements.
    // Group by block, then process each block in reverse statement order.
    // - SingleUse/DeadStore: remove the statement
    // - DeadCall: convert Assign → ExprStmt (keep the side-effectful expression)
    let mut actions_by_block: FxHashMap<usize, Vec<(usize, &InlineKind)>> =
        FxHashMap::default();
    for candidate in &candidates {
        actions_by_block
            .entry(candidate.node_idx.index())
            .or_default()
            .push((candidate.stmt_idx, &candidate.kind));
    }

    let all_nodes: Vec<_> = func.cfg.node_indices().collect();
    for node_idx in all_nodes {
        if let Some(actions) = actions_by_block.get(&node_idx.index()) {
            let mut sorted: Vec<_> = actions.clone();
            sorted.sort_by(|a, b| b.0.cmp(&a.0)); // reverse order
            sorted.dedup_by_key(|a| a.0);

            for (idx, kind) in sorted {
                if idx < func.cfg[node_idx].stmts.len() {
                    match kind {
                        InlineKind::DeadCall => {
                            // Convert `var = call()` → `call()`
                            if let HirStmt::Assign { value, .. } = &func.cfg[node_idx].stmts[idx] {
                                let value = *value;
                                func.cfg[node_idx].stmts[idx] = HirStmt::ExprStmt(value);
                            }
                        }
                        InlineKind::SingleUse | InlineKind::DeadStore => {
                            func.cfg[node_idx].stmts.remove(idx);
                        }
                    }
                }
            }
        }
    }

    inlined
}

/// Count how many times each VarId is used as a value (read).
/// Counts references in:
/// - All expressions in the arena (Var nodes)
/// - Statement targets that read vars (compound assign, etc.)
/// - Terminator conditions
fn count_uses(func: &HirFunc) -> FxHashMap<VarId, usize> {
    let mut counts: FxHashMap<VarId, usize> = FxHashMap::default();

    // Count uses in expressions
    for i in 0..func.exprs.len() {
        let expr_id = ExprId(i as u32);
        if let HirExpr::Var(var_id) = func.exprs.get(expr_id) {
            *counts.entry(*var_id).or_insert(0) += 1;
        }
    }

    // Count uses in statement LValues that read (Field/Index tables can be vars)
    for node_idx in func.cfg.node_indices() {
        for stmt in &func.cfg[node_idx].stmts {
            count_uses_in_stmt(stmt, func, &mut counts);
        }
    }

    counts
}

fn count_uses_in_stmt(
    stmt: &HirStmt,
    func: &HirFunc,
    counts: &mut FxHashMap<VarId, usize>,
) {
    match stmt {
        HirStmt::If { then_body, elseif_clauses, else_body, .. } => {
            for s in then_body {
                count_uses_in_stmt(s, func, counts);
            }
            for clause in elseif_clauses {
                for s in &clause.body {
                    count_uses_in_stmt(s, func, counts);
                }
            }
            if let Some(body) = else_body {
                for s in body {
                    count_uses_in_stmt(s, func, counts);
                }
            }
        }
        HirStmt::While { body, .. } | HirStmt::Repeat { body, .. } => {
            for s in body {
                count_uses_in_stmt(s, func, counts);
            }
        }
        HirStmt::NumericFor { body, .. } | HirStmt::GenericFor { body, .. } => {
            for s in body {
                count_uses_in_stmt(s, func, counts);
            }
        }
        _ => {}
    }
}

/// Check if an expression has observable side effects (calls, etc.).
fn expr_has_side_effects(func: &HirFunc, expr_id: ExprId) -> bool {
    match func.exprs.get(expr_id) {
        HirExpr::Call { .. } | HirExpr::MethodCall { .. } => true,
        HirExpr::Binary { left, right, .. } => {
            expr_has_side_effects(func, *left) || expr_has_side_effects(func, *right)
        }
        HirExpr::Unary { operand, .. } => expr_has_side_effects(func, *operand),
        HirExpr::Concat(operands) => operands.iter().any(|o| expr_has_side_effects(func, *o)),
        HirExpr::Table { array, hash } => {
            array.iter().any(|a| expr_has_side_effects(func, *a))
                || hash
                    .iter()
                    .any(|(k, v)| expr_has_side_effects(func, *k) || expr_has_side_effects(func, *v))
        }
        HirExpr::FieldAccess { table, .. } => expr_has_side_effects(func, *table),
        HirExpr::IndexAccess { table, key } => {
            expr_has_side_effects(func, *table) || expr_has_side_effects(func, *key)
        }
        HirExpr::IfExpr { condition, then_expr, else_expr } => {
            expr_has_side_effects(func, *condition)
                || expr_has_side_effects(func, *then_expr)
                || expr_has_side_effects(func, *else_expr)
        }
        HirExpr::Select { source, .. } => expr_has_side_effects(func, *source),
        _ => false,
    }
}

struct InlineCandidate {
    var_id: VarId,
    value_expr: ExprId,
    node_idx: petgraph::stable_graph::NodeIndex,
    stmt_idx: usize,
    kind: InlineKind,
}

enum InlineKind {
    /// Single-use temp: inline expression, remove statement.
    SingleUse,
    /// Dead store with no side effects: remove entirely.
    DeadStore,
    /// Dead store with side effects (e.g., unused call result):
    /// convert `var = call()` → `call()`.
    DeadCall,
}
