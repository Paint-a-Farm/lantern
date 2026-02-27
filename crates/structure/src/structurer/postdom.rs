//! Post-dominator tree computation for the CFG.
//!
//! A node X **post-dominates** node Y if every path from Y to the exit
//! must pass through X.  The **immediate post-dominator** (IPDOM) of Y
//! is the closest such X.
//!
//! For structured control-flow recovery, the join point of an if/else is
//! exactly the IPDOM of the Branch node.  Using post-dominators gives a
//! principled, heuristic-free answer — no reachability intersections, no
//! PC-ordering tie-breakers.
//!
//! Algorithm: Cooper, Harvey & Kennedy's iterative dominance computation
//! applied to the reverse CFG (treating exit nodes as entries).  This is
//! O(n²) worst-case but converges quickly for structured control flow.

use petgraph::stable_graph::NodeIndex;
use petgraph::visit::EdgeRef;
use petgraph::Direction;
use rustc_hash::FxHashMap;

use lantern_hir::cfg::{CfgGraph, EdgeKind, Terminator};

/// Post-dominator tree stored as a map from node → immediate post-dominator.
///
/// Nodes with no IPDOM (e.g. exit nodes, unreachable nodes) have no entry.
pub struct PostDomTree {
    ipdom: FxHashMap<NodeIndex, NodeIndex>,
}

impl PostDomTree {
    /// Look up the immediate post-dominator of `node`.
    pub fn ipdom(&self, node: NodeIndex) -> Option<NodeIndex> {
        self.ipdom.get(&node).copied()
    }
}

/// Compute the post-dominator tree for a CFG.
///
/// Exit nodes are identified as those with a `Return` terminator or no
/// forward successors.  A virtual exit node (index 0 in the RPO array)
/// unifies all exit nodes so the CHK intersect always terminates.
pub fn compute_postdom_tree(cfg: &CfgGraph, _entry: NodeIndex) -> PostDomTree {
    let nodes: Vec<NodeIndex> = cfg.node_indices().collect();
    if nodes.is_empty() {
        return PostDomTree {
            ipdom: FxHashMap::default(),
        };
    }

    // Exit nodes: Return terminators or no forward outgoing edges.
    let exit_nodes: Vec<NodeIndex> = nodes
        .iter()
        .copied()
        .filter(|&n| {
            matches!(cfg[n].terminator, Terminator::Return(_))
                || !cfg
                    .edges(n)
                    .any(|e| e.weight().kind != EdgeKind::LoopBack)
        })
        .collect();

    if exit_nodes.is_empty() {
        return PostDomTree {
            ipdom: FxHashMap::default(),
        };
    }

    // Compute reverse postorder of the REVERSE CFG starting from exit nodes.
    let rpo_nodes = reverse_postorder_on_reverse_cfg(cfg, &exit_nodes);

    // Build the RPO array with a virtual exit at index 0.
    // Real nodes occupy indices 1..=rpo_nodes.len().
    // The virtual exit is the root of the post-dominator tree.
    let virtual_exit: usize = 0;
    let total = rpo_nodes.len() + 1; // +1 for virtual exit

    // Map NodeIndex → RPO index (1-based for real nodes)
    let mut rpo_idx: FxHashMap<NodeIndex, usize> = FxHashMap::default();
    for (i, &n) in rpo_nodes.iter().enumerate() {
        rpo_idx.insert(n, i + 1); // offset by 1 for virtual exit at 0
    }

    // IPDOM array. UNDEFINED = usize::MAX.
    const UNDEFINED: usize = usize::MAX;
    let mut dom: Vec<usize> = vec![UNDEFINED; total];

    // Virtual exit dominates itself (root).
    dom[virtual_exit] = virtual_exit;

    // All real exit nodes are immediately post-dominated by the virtual exit.
    for &ex in &exit_nodes {
        if let Some(&idx) = rpo_idx.get(&ex) {
            dom[idx] = virtual_exit;
        }
    }

    // Iterate until convergence.
    let mut changed = true;
    while changed {
        changed = false;
        // Process real nodes only (indices 1..total), in RPO order.
        for rpo_i in 1..total {
            let node = rpo_nodes[rpo_i - 1];

            // Skip exit nodes (their IPDOM is fixed to virtual exit)
            if exit_nodes.contains(&node) {
                continue;
            }

            // For post-domination, the "predecessors" in the reverse CFG are
            // the forward successors of `node` in the original CFG.
            let mut new_idom = UNDEFINED;
            for edge in cfg.edges(node) {
                if edge.weight().kind == EdgeKind::LoopBack {
                    continue;
                }
                let succ = edge.target();
                let succ_rpo = match rpo_idx.get(&succ) {
                    Some(&i) => i,
                    None => continue, // unreachable from exits
                };
                if dom[succ_rpo] == UNDEFINED {
                    continue;
                }
                if new_idom == UNDEFINED {
                    new_idom = succ_rpo;
                } else {
                    new_idom = intersect(&dom, new_idom, succ_rpo);
                }
            }

            if new_idom != UNDEFINED && dom[rpo_i] != new_idom {
                dom[rpo_i] = new_idom;
                changed = true;
            }
        }
    }

    // Convert RPO indices back to NodeIndex.
    // Skip entries that resolve to the virtual exit (no real IPDOM)
    // and self-references.
    let mut result: FxHashMap<NodeIndex, NodeIndex> = FxHashMap::default();
    for (rpo_i, &d) in dom.iter().enumerate() {
        if rpo_i == 0 || rpo_i >= total {
            continue; // skip virtual exit
        }
        if d != UNDEFINED && d != rpo_i && d != virtual_exit {
            result.insert(rpo_nodes[rpo_i - 1], rpo_nodes[d - 1]);
        }
    }

    PostDomTree { ipdom: result }
}

/// Cooper-Harvey-Kennedy intersect: walk up the dominator tree from two
/// nodes until they meet.  The virtual exit at index 0 is the ultimate
/// root, guaranteeing termination.
fn intersect(dom: &[usize], mut a: usize, mut b: usize) -> usize {
    while a != b {
        while a > b {
            a = dom[a];
        }
        while b > a {
            b = dom[b];
        }
    }
    a
}

/// Compute reverse-postorder of the reversed CFG.
/// DFS from exit nodes following incoming edges (skipping LoopBack).
fn reverse_postorder_on_reverse_cfg(
    cfg: &CfgGraph,
    exits: &[NodeIndex],
) -> Vec<NodeIndex> {
    use rustc_hash::FxHashSet;

    let mut visited = FxHashSet::default();
    let mut postorder = Vec::new();

    for &exit in exits {
        dfs_reverse(cfg, exit, &mut visited, &mut postorder);
    }

    postorder.reverse();
    postorder
}

fn dfs_reverse(
    cfg: &CfgGraph,
    node: NodeIndex,
    visited: &mut rustc_hash::FxHashSet<NodeIndex>,
    postorder: &mut Vec<NodeIndex>,
) {
    if !visited.insert(node) {
        return;
    }
    for edge in cfg.edges_directed(node, Direction::Incoming) {
        if edge.weight().kind == EdgeKind::LoopBack {
            continue;
        }
        dfs_reverse(cfg, edge.source(), visited, postorder);
    }
    postorder.push(node);
}
