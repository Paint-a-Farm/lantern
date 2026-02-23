use petgraph::stable_graph::NodeIndex;
use petgraph::visit::EdgeRef;
use rustc_hash::FxHashSet;

use lantern_hir::arena::ExprId;
use lantern_hir::cfg::{CfgGraph, EdgeKind, Terminator};
use lantern_hir::func::HirFunc;

pub(super) fn single_successor(cfg: &CfgGraph, node: NodeIndex) -> Option<NodeIndex> {
    cfg.edges(node).next().map(|e| e.target())
}

pub(super) fn branch_successors(
    cfg: &CfgGraph,
    node: NodeIndex,
) -> (Option<NodeIndex>, Option<NodeIndex>) {
    let mut then_node = None;
    let mut else_node = None;
    for e in cfg.edges(node) {
        match e.weight().kind {
            EdgeKind::Then | EdgeKind::LoopBack => then_node = Some(e.target()),
            EdgeKind::Else | EdgeKind::LoopExit => else_node = Some(e.target()),
            EdgeKind::Unconditional => {
                if then_node.is_none() {
                    then_node = Some(e.target());
                } else {
                    else_node = Some(e.target());
                }
            }
        }
    }
    (then_node, else_node)
}

pub(super) fn find_join_point(
    func: &HirFunc,
    then_node: NodeIndex,
    else_node: NodeIndex,
    outer_stop: Option<NodeIndex>,
    visited: &FxHashSet<NodeIndex>,
) -> Option<NodeIndex> {
    let then_reachable = collect_reachable(&func.cfg, then_node, outer_stop);
    let else_reachable = collect_reachable(&func.cfg, else_node, outer_stop);

    // A pure terminal block (e.g. bare Return with no statements and no
    // outgoing edges) is a destination, not a convergence point.  Treating
    // it as a join causes the structurer to produce empty if-then-end with
    // the body spilling after the `end`.
    //
    // However, a terminal block WITH statements IS a valid join — both
    // branches converge there and there is code to execute after the merge.
    // Example: `if p == nil then ... else ... end; <computation>; return`
    // Here the return block has statements and must be the join point.
    let mut common: Vec<NodeIndex> = then_reachable
        .intersection(&else_reachable)
        .copied()
        .filter(|n| is_valid_join_candidate(&func.cfg, *n))
        .collect();

    if then_reachable.contains(&else_node) && is_valid_join_candidate(&func.cfg, else_node) {
        common.push(else_node);
    }
    if else_reachable.contains(&then_node) && is_valid_join_candidate(&func.cfg, then_node) {
        common.push(then_node);
    }

    // Return-sinking: if no valid join candidate was found, check for a
    // "sunk return" — a bare Return block that one branch flows into via Jump
    // while the other IS that block. The Luau compiler sinks `return x` into
    // the continuation point after if-then, creating this pattern:
    //   Block 0: Branch → then=1, else=2
    //   Block 1: assign; Jump → 2
    //   Block 2: Return (bare, no stmts)
    // Block 2 should be the join point (return after if-end), not an
    // independent branch target.
    if common.is_empty() {
        // Check: else_node is a bare Return reachable from then_node.
        // Only consider blocks not yet visited by the structurer — visited
        // blocks may appear "bare" because their stmts were already consumed.
        if then_reachable.contains(&else_node)
            && !visited.contains(&else_node)
            && is_sunk_return(&func.cfg, else_node)
        {
            common.push(else_node);
        }
        // Check: then_node is a bare Return reachable from else_node
        if else_reachable.contains(&then_node)
            && !visited.contains(&then_node)
            && is_sunk_return(&func.cfg, then_node)
        {
            common.push(then_node);
        }
    }

    if common.is_empty() {
        return None;
    }

    common.sort_by_key(|n| func.cfg[*n].pc_range.0);
    common.dedup();
    Some(common[0])
}

pub(super) fn collect_reachable(
    cfg: &CfgGraph,
    start: NodeIndex,
    stop: Option<NodeIndex>,
) -> FxHashSet<NodeIndex> {
    let mut visited = FxHashSet::default();
    let mut stack = vec![start];
    while let Some(node) = stack.pop() {
        if Some(node) == stop || !visited.insert(node) {
            continue;
        }
        for e in cfg.edges(node) {
            if e.weight().kind != EdgeKind::LoopBack {
                stack.push(e.target());
            }
        }
    }
    visited
}

/// Check if a node has at least one non-LoopBack outgoing edge.
fn has_forward_successors(cfg: &CfgGraph, node: NodeIndex) -> bool {
    cfg.edges(node)
        .any(|e| e.weight().kind != EdgeKind::LoopBack)
}

/// Check if a node is a valid candidate for a join point.
///
/// A node with forward successors is always valid (branches converge and
/// execution continues). A terminal node (no forward successors) is valid
/// only if it has statements — meaning there is real code to execute at
/// the merge point before the terminal action (return, etc.).
///
/// A bare terminal (no statements, just a Return) is NOT a valid join
/// because both branches independently terminate there and there is
/// nothing to place after `end`.
fn is_valid_join_candidate(cfg: &CfgGraph, node: NodeIndex) -> bool {
    if has_forward_successors(cfg, node) {
        return true;
    }
    // Terminal node: valid join only if it has statements to execute
    !cfg[node].stmts.is_empty()
}

/// Check if a node is a "sunk return" — a bare Return block with no
/// statements and no forward successors. This is the pattern created by
/// the Luau compiler when it sinks `return x` to the end of an if-then block.
fn is_sunk_return(cfg: &CfgGraph, node: NodeIndex) -> bool {
    let block = &cfg[node];
    block.stmts.is_empty()
        && matches!(block.terminator, Terminator::Return(_))
        && !has_forward_successors(cfg, node)
}

pub(super) fn negate_condition(func: &mut HirFunc, condition: ExprId) -> ExprId {
    func.exprs.negate_condition(condition)
}
