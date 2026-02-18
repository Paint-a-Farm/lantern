use petgraph::stable_graph::NodeIndex;
use rustc_hash::FxHashMap;

use crate::arena::ExprArena;
use crate::cfg::CfgGraph;
use crate::var::{VarId, VarTable};

/// A function in the HIR — the central data structure.
///
/// Contains the CFG, expression arena, variable table, and
/// metadata for mapping back to bytecode origins.
#[derive(Debug)]
pub struct HirFunc {
    /// Control flow graph. Nodes are basic blocks, edges are branches.
    pub cfg: CfgGraph,

    /// Entry block of the CFG.
    pub entry: NodeIndex,

    /// All expressions in this function, stored flat.
    pub exprs: ExprArena,

    /// All variables in this function with metadata.
    pub vars: VarTable,

    /// Function parameters (ordered).
    pub params: Vec<VarId>,

    /// Whether this function accepts varargs.
    pub is_vararg: bool,

    /// Number of upvalues.
    pub num_upvalues: u8,

    /// Bytecode function index in the chunk.
    pub proto_index: usize,

    /// Map from HIR elements to their bytecode PC origin.
    /// Keys are ExprId or StmtRef encoded as u32.
    pub origins: FxHashMap<u32, usize>,

    /// Upvalue names (from debug info, if available).
    pub upvalue_names: Vec<Option<String>>,

    /// Function name (from debug info, if available).
    pub name: Option<String>,

    /// Whether the CFG has been structured into nested HirStmt trees.
    /// When true, the emitter should only walk `cfg[entry].stmts` recursively
    /// instead of iterating all blocks.
    pub structured: bool,

    /// Line info from bytecode debug data, preserved for downstream emission.
    pub line_info: Option<lantern_bytecode::function::LineInfo>,
}

impl HirFunc {
    pub fn new(proto_index: usize) -> Self {
        let mut cfg = CfgGraph::new();
        let entry = cfg.add_node(crate::cfg::HirBlock::new());

        Self {
            cfg,
            entry,
            exprs: ExprArena::new(),
            vars: VarTable::new(),
            params: Vec::new(),
            is_vararg: false,
            num_upvalues: 0,
            proto_index,
            origins: FxHashMap::default(),
            upvalue_names: Vec::new(),
            name: None,
            structured: false,
            line_info: None,
        }
    }

    /// Record the bytecode PC origin for an expression.
    pub fn set_origin_expr(&mut self, expr_id: crate::arena::ExprId, pc: usize) {
        self.origins.insert(expr_id.0, pc);
    }

    /// Get the bytecode PC origin for an expression.
    pub fn get_origin_expr(&self, expr_id: crate::arena::ExprId) -> Option<usize> {
        self.origins.get(&expr_id.0).copied()
    }
}
