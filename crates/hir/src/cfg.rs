use petgraph::stable_graph::{NodeIndex, StableDiGraph};
use petgraph::visit::EdgeRef;

use crate::arena::ExprId;
use crate::stmt::HirStmt;
use crate::var::VarId;

/// A basic block in the control flow graph.
#[derive(Debug, Clone)]
pub struct HirBlock {
    /// Statements in this block (executed sequentially).
    pub stmts: Vec<HirStmt>,
    /// Block terminator (how control leaves this block).
    pub terminator: Terminator,
    /// Bytecode PC range for this block [start, end).
    pub pc_range: (usize, usize),
    /// Generic for-loop setup: iterator expressions from a FORGPREP block.
    /// The structurer consumes these when building GenericFor statements.
    pub for_gen_iterators: Option<Vec<ExprId>>,
    /// FORGPREP variant (which opcode was used). Propagated to FORGLOOP's terminator.
    pub for_gen_variant: Option<ForGenVariant>,
    /// True when this block ends with `Jump +0` (offset 0) — the compiler's
    /// artifact for an empty `else` body.  The structurer uses this to emit
    /// `else end` even though the else body is empty.
    pub has_empty_else_jump: bool,
}

impl HirBlock {
    pub fn new() -> Self {
        Self {
            stmts: Vec::new(),
            terminator: Terminator::None,
            pc_range: (0, 0),
            for_gen_iterators: None,
            for_gen_variant: None,
            has_empty_else_jump: false,
        }
    }
}

/// How control flow leaves a basic block.
#[derive(Debug, Clone)]
pub enum Terminator {
    /// Block has no terminator yet (under construction).
    None,
    /// Unconditional jump.
    Jump,
    /// Conditional branch: if `condition` then `then` edge, else `else` edge.
    ///
    /// `negated` records whether the original bytecode used a negated jump
    /// (JumpIfNot, JumpIfNotLt, JumpIfNotLe, JumpIfNotEq). When true the
    /// original source had `if cond then <body> end` (wrapping); when false
    /// the source had `if NOT(cond) then break/continue end; <body>` (guard).
    Branch { condition: ExprId, negated: bool },
    /// Return from function.
    Return(Vec<ExprId>),
    /// Numeric for-loop setup (FORNPREP).
    /// The block's stmts contain the limit/step/init assignments.
    /// Edges: LoopBack → body start, LoopExit → after loop.
    ForNumPrep {
        /// Base register (A). Layout: A+0=limit, A+1=step, A+2=index(=var).
        base_reg: u8,
        /// Expressions for start, limit, step that were loaded before FORNPREP.
        start: ExprId,
        limit: ExprId,
        step: Option<ExprId>,
        /// Loop variable name from debug info (resolved during lifting).
        loop_var_name: Option<String>,
    },
    /// Numeric for-loop back-edge (FORNLOOP).
    /// Edges: LoopBack → body start, LoopExit → exit.
    ForNumBack { base_reg: u8 },
    /// Generic for-loop back-edge (FORGLOOP).
    /// The FORGPREP block jumps unconditionally to this block.
    /// Edges: LoopBack → body start, LoopExit → exit.
    ForGenBack {
        /// Base register (A). Layout: A+0=generator, A+1=state, A+2=index, A+3..=vars.
        base_reg: u8,
        /// Number of user-visible loop variables.
        var_count: u8,
        /// Iterator expressions (the values loaded before FORGPREP).
        iterators: Vec<ExprId>,
        /// Loop variable names from debug info (resolved during lifting).
        loop_var_names: Vec<Option<String>>,
        /// Which FORGPREP variant was used (generic, ipairs, pairs/next).
        variant: ForGenVariant,
    },
}

/// Which FORGPREP variant was used for a generic for-loop.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ForGenVariant {
    /// FORGPREP — generic iterator (user-defined generator function).
    Generic,
    /// FORGPREP_INEXT — optimized for ipairs() iteration.
    IPairs,
    /// FORGPREP_NEXT — optimized for pairs()/next() iteration.
    Pairs,
}

/// Edge metadata in the CFG.
#[derive(Debug, Clone)]
pub struct HirEdge {
    pub kind: EdgeKind,
    /// Phi-like arguments: values flowing into the successor block's parameters.
    pub args: Vec<(VarId, ExprId)>,
}

/// What kind of control flow edge this is.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EdgeKind {
    /// Unconditional or fallthrough.
    Unconditional,
    /// Taken when condition is true.
    Then,
    /// Taken when condition is false.
    Else,
    /// Loop back-edge.
    LoopBack,
    /// Loop exit edge.
    LoopExit,
}

impl HirEdge {
    pub fn unconditional() -> Self {
        Self {
            kind: EdgeKind::Unconditional,
            args: Vec::new(),
        }
    }

    pub fn then_edge() -> Self {
        Self {
            kind: EdgeKind::Then,
            args: Vec::new(),
        }
    }

    pub fn else_edge() -> Self {
        Self {
            kind: EdgeKind::Else,
            args: Vec::new(),
        }
    }
}

/// The control flow graph type used throughout lantern.
pub type CfgGraph = StableDiGraph<HirBlock, HirEdge>;

/// Helper to find the "then" successor of a conditional branch.
pub fn then_successor(graph: &CfgGraph, node: NodeIndex) -> Option<NodeIndex> {
    graph
        .edges(node)
        .find(|e| e.weight().kind == EdgeKind::Then)
        .map(|e| e.target())
}

/// Helper to find the "else" successor of a conditional branch.
pub fn else_successor(graph: &CfgGraph, node: NodeIndex) -> Option<NodeIndex> {
    graph
        .edges(node)
        .find(|e| e.weight().kind == EdgeKind::Else)
        .map(|e| e.target())
}
