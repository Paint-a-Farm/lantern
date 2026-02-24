use petgraph::stable_graph::NodeIndex;
use rustc_hash::FxHashSet;

use lantern_hir::cfg::Terminator;
use lantern_hir::func::HirFunc;
use lantern_hir::stmt::HirStmt;

mod branch;
mod cfg_helpers;
mod guard;
mod loops;

use branch::structure_branch;
use cfg_helpers::single_successor;
use guard::strip_trailing_returns;
use loops::{structure_for_gen, structure_for_num, try_structure_while};

/// Structure a function's CFG into nested HirStmt trees.
///
/// After this pass, `func.cfg[func.entry].stmts` contains the complete
/// structured output and `func.structured` is set to true. The emitter
/// walks only the entry block's stmts recursively.
pub fn structure_function(func: &mut HirFunc) {
    let entry = func.entry;
    let mut stmts = structure_region(func, entry, None, None, &mut FxHashSet::default());
    strip_trailing_returns(&mut stmts);
    func.cfg[entry].stmts = stmts;
    func.cfg[entry].terminator = Terminator::None;
    func.structured = true;
}

/// Context for the enclosing loop, used to emit break/continue.
pub(crate) struct LoopCtx {
    pub(crate) header: NodeIndex,
    pub(crate) exit: Option<NodeIndex>,
}

/// Result of structuring a loop.
pub(crate) struct LoopResult {
    pub(crate) stmts: Vec<HirStmt>,
    pub(crate) next: Option<NodeIndex>,
}

/// Structure a region of the CFG starting from `start`, stopping before `stop`.
/// Returns the structured statement list.
///
/// `loop_ctx` provides the enclosing loop's header and exit for break/continue.
pub(crate) fn structure_region(
    func: &mut HirFunc,
    start: NodeIndex,
    stop: Option<NodeIndex>,
    loop_ctx: Option<&LoopCtx>,
    visited: &mut FxHashSet<NodeIndex>,
) -> Vec<HirStmt> {
    let mut result = Vec::new();
    let mut current = Some(start);

    while let Some(node) = current {
        if Some(node) == stop {
            break;
        }
        if !visited.insert(node) {
            break;
        }

        // Check if this is a while-loop header
        if let Some(loop_result) = try_structure_while(func, node, stop, loop_ctx, visited) {
            result.extend(loop_result.stmts);
            current = loop_result.next;
            continue;
        }

        // Take statements from this block
        let block_stmts = std::mem::take(&mut func.cfg[node].stmts);
        let terminator = func.cfg[node].terminator.clone();
        result.extend(block_stmts);

        match &terminator {
            Terminator::None => {
                current = None;
            }

            Terminator::Return(values) => {
                result.push(HirStmt::Return(values.clone()));
                current = None;
            }

            Terminator::Jump => {
                let succ = single_successor(&func.cfg, node);

                // Check for break/continue in loop context
                if let (Some(succ_node), Some(lctx)) = (succ, loop_ctx) {
                    // A jump to the stop node is just the natural end of the
                    // region — don't emit continue. For-loop bodies jump to
                    // the ForNumBack/ForGenBack block as normal iteration.
                    if Some(succ_node) != stop {
                        if succ_node == lctx.header {
                            result.push(HirStmt::Continue);
                            current = None;
                            continue;
                        }
                        if Some(succ_node) == lctx.exit {
                            result.push(HirStmt::Break);
                            current = None;
                            continue;
                        }
                    }
                }

                current = succ;
            }

            Terminator::Branch { condition, negated } => {
                let condition = *condition;
                let negated = *negated;
                current =
                    structure_branch(func, node, condition, negated, stop, loop_ctx, visited, &mut result);
            }

            Terminator::ForNumPrep {
                base_reg,
                start,
                limit,
                step,
                ref loop_var_name,
            } => {
                let start = *start;
                let limit = *limit;
                let step = *step;
                let base_reg = *base_reg;
                let loop_var_name = loop_var_name.clone();
                current = structure_for_num(
                    func,
                    node,
                    base_reg,
                    start,
                    limit,
                    step,
                    loop_var_name,
                    stop,
                    loop_ctx,
                    visited,
                    &mut result,
                );
            }

            Terminator::ForNumBack { .. } => {
                // Should not be reached during structuring — the ForNumPrep
                // handler structures the body up to and including this block.
                current = None;
            }

            Terminator::ForGenBack {
                base_reg,
                var_count,
                ref iterators,
                ref loop_var_names,
                ..
            } => {
                let base_reg = *base_reg;
                let var_count = *var_count;
                let iterators = iterators.clone();
                let loop_var_names = loop_var_names.clone();
                current = structure_for_gen(
                    func,
                    node,
                    base_reg,
                    var_count,
                    iterators,
                    loop_var_names,
                    stop,
                    loop_ctx,
                    visited,
                    &mut result,
                );
            }
        }
    }

    result
}
