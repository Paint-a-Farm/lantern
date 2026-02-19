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

    let mut common: Vec<NodeIndex> = then_reachable
        .intersection(&else_reachable)
        .copied()
        .collect();

    if then_reachable.contains(&else_node) {
        common.push(else_node);
    }
    if else_reachable.contains(&then_node) {
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

pub(super) fn negate_condition(func: &mut HirFunc, condition: ExprId) -> ExprId {
    func.exprs.negate_condition(condition)
}
