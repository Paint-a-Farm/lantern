use petgraph::stable_graph::NodeIndex;
use petgraph::visit::EdgeRef;
use rustc_hash::FxHashSet;

use lantern_hir::arena::ExprId;
use lantern_hir::cfg::{CfgGraph, EdgeKind};
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

pub(super) fn negate_condition(func: &mut HirFunc, condition: ExprId) -> ExprId {
    func.exprs.negate_condition(condition)
}
