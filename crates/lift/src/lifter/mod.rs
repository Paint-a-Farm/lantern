mod boolean;
mod expressions;
mod opcodes;

use petgraph::stable_graph::NodeIndex;
use petgraph::Direction;
use rustc_hash::{FxHashMap, FxHashSet};

use lantern_bytecode::chunk::Chunk;
use lantern_bytecode::function::Function;

use lantern_hir::arena::ExprId;
use lantern_hir::cfg::{HirBlock, HirEdge};
use lantern_hir::expr::HirExpr;
use lantern_hir::func::HirFunc;
use lantern_hir::stmt::HirStmt;
use lantern_hir::var::RegRef;

use crate::block_discovery;

/// Lift a bytecode function into HIR.
///
/// Produces an unstructured CFG with raw register references (RegRef).
/// The constraint solver in the `vars` crate resolves these to VarIds.
pub fn lift_function(chunk: &Chunk, func_index: usize) -> HirFunc {
    let func = &chunk.functions[func_index];
    let mut lifter = Lifter::new(chunk, func, func_index);
    lifter.lift();
    lifter.hir
}

pub(crate) struct Lifter<'a> {
    pub(crate) chunk: &'a Chunk,
    pub(crate) func: &'a Function,
    pub(crate) hir: HirFunc,
    /// Map from block-start PC to CFG node index.
    pub(crate) block_map: FxHashMap<usize, NodeIndex>,
    /// Current block being built.
    pub(crate) current_block: NodeIndex,
    /// MULTRET tracking: when a CALL with C=0 or GETVARARGS with B=0
    /// produces a variable number of results, we record the expression
    /// and the base register. The next MULTRET consumer (CALL B=0,
    /// RETURN B=0, SETLIST C=0) uses this to collect the arguments.
    pub(crate) top: Option<(ExprId, u8)>,
    /// Pending FASTCALL builtin ID: set by FASTCALL* instructions,
    /// consumed by the next CALL instruction. 0 = no pending fastcall.
    pub(crate) pending_fastcall: u8,
    /// Boolean value computation regions detected in the instruction stream.
    /// These regions contain conditional jumps that compute boolean values
    /// rather than creating real control flow branches.
    pub(crate) bool_regions: Vec<crate::bool_regions::BoolRegion>,
    /// Truthiness-based or/and chains (JUMPIF/JUMPIFNOT) detected in the
    /// instruction stream.
    pub(crate) truthy_chains: Vec<crate::bool_regions::TruthyChain>,
    /// Compound `a and b or c` ternary expressions.
    pub(crate) and_or_ternaries: Vec<crate::bool_regions::AndOrTernary>,
    /// Simple conditional value ternaries (JumpIfNot + value + Jump + value).
    pub(crate) value_ternaries: Vec<crate::bool_regions::ValueTernary>,
}

impl<'a> Lifter<'a> {
    fn new(chunk: &'a Chunk, func: &'a Function, func_index: usize) -> Self {
        let mut hir = HirFunc::new(func_index);
        hir.is_vararg = func.is_vararg;
        hir.num_upvalues = func.num_upvalues;
        hir.name = chunk.get_string(func.debug.func_name_index);
        hir.line_info = func.debug.line_info.clone();
        hir.type_info = func.type_info.clone();

        // Set up upvalue names from debug info
        hir.upvalue_names = func
            .debug
            .upvalue_name_indices
            .iter()
            .map(|&idx| chunk.get_string(idx))
            .collect();

        let entry = hir.entry;
        let mut block_map = FxHashMap::default();
        block_map.insert(0, entry);

        Self {
            chunk,
            func,
            hir,
            block_map,
            current_block: entry,
            top: None,
            pending_fastcall: 0,
            bool_regions: Vec::new(),
            truthy_chains: Vec::new(),
            and_or_ternaries: Vec::new(),
            value_ternaries: Vec::new(),
        }
    }

    fn lift(&mut self) {
        let instructions = &self.func.instructions;
        if instructions.is_empty() {
            return;
        }

        // Detect boolean value computation regions before block discovery.
        // These regions contain conditional jumps that compute boolean values
        // (e.g. `x = a == b or a == c`), NOT real control flow branches.
        // Suppressing them prevents false block boundaries.
        let mut suppressed = crate::bool_regions::detect_bool_regions(instructions);
        self.bool_regions = crate::bool_regions::find_bool_regions(instructions);

        // Detect compound `a and b or c` ternaries FIRST (higher priority)
        let (and_or_ternaries, and_or_suppressed) =
            crate::bool_regions::detect_and_or_ternaries(instructions);
        self.and_or_ternaries = and_or_ternaries;
        suppressed.extend(and_or_suppressed);

        // Detect truthiness-based or/and chains (JUMPIF/JUMPIFNOT)
        // Skip chains that overlap with already-detected and/or ternaries
        let (truthy_chains, _truthy_suppressed) =
            crate::bool_regions::detect_truthy_chains(instructions);
        // Filter out chains whose jumps are already suppressed by ternaries
        self.truthy_chains = truthy_chains
            .into_iter()
            .filter(|chain| !chain.jump_pcs.iter().any(|pc| suppressed.contains(pc)))
            .collect();
        for chain in &self.truthy_chains {
            for &jump_pc in &chain.jump_pcs {
                suppressed.insert(jump_pc);
            }
        }

        // Detect simple conditional value ternaries (JumpIfNot + value + Jump + value)
        // Skip ternaries whose jumps are already suppressed
        let (value_ternaries, _value_suppressed) =
            crate::bool_regions::detect_value_ternaries(instructions);
        self.value_ternaries = value_ternaries
            .into_iter()
            .filter(|t| {
                !suppressed.contains(&t.jump_pc)
                    && !suppressed.contains(&t.skip_jump_pc)
                    && t.compound_jump_pcs
                        .iter()
                        .all(|&cpc| !suppressed.contains(&cpc))
            })
            .collect();
        let mut suppressed_targets = FxHashSet::default();
        for t in &self.value_ternaries {
            suppressed.insert(t.jump_pc);
            suppressed.insert(t.skip_jump_pc);
            if crate::bool_regions::has_aux_word(instructions[t.jump_pc].op) {
                suppressed.insert(t.jump_pc + 1);
            }
            for &cpc in &t.compound_jump_pcs {
                suppressed.insert(cpc);
                if crate::bool_regions::has_aux_word(instructions[cpc].op) {
                    suppressed.insert(cpc + 1);
                }
            }
            // Suppress ALL PCs within the value ternary range as block-start
            // targets. External jumps may target false_val_pc, but the ternary
            // lifter handles those PCs internally. Without this, the false
            // branch would land in a separate block and the ternary result
            // would be invisible to subsequent or-chains.
            for pc in (t.jump_pc + 1)..t.join_pc {
                suppressed_targets.insert(pc);
            }
        }

        // Discover block boundaries
        let starts =
            block_discovery::discover_block_starts(instructions, &suppressed, &suppressed_targets);
        let ranges = block_discovery::block_ranges(&starts, instructions.len());

        // Create all blocks in the CFG
        for &start_pc in &starts {
            self.block_map
                .entry(start_pc)
                .or_insert_with(|| self.hir.cfg.add_node(HirBlock::new()));
        }

        // Lift each block
        for (start_pc, end_pc) in ranges {
            let node = self.block_map[&start_pc];
            self.current_block = node;
            self.hir.cfg[node].pc_range = (start_pc, end_pc);
            self.lift_block(start_pc, end_pc);
        }
    }

    fn lift_block(&mut self, start_pc: usize, end_pc: usize) {
        self.top = None; // Reset MULTRET state at block boundary
        let mut pc = start_pc;
        while pc < end_pc {
            // Check if this PC starts a boolean value computation region.
            // If so, lift the entire region as a single expression.
            // Reject patterns that would overshoot the block boundary — they
            // were detected on the raw instruction stream and may span across
            // block-creating opcodes (e.g. FORGPREP/FORGLOOP).
            if let Some(advance) = self.try_lift_bool_region(pc) {
                if pc + advance <= end_pc {
                    pc += advance;
                    continue;
                }
            }
            // Check if this PC starts an `a and b or c` ternary.
            if let Some(advance) = self.try_lift_and_or_ternary(pc) {
                if pc + advance <= end_pc {
                    pc += advance;
                    continue;
                }
            }
            // Check if this PC starts a truthiness-based or/and chain.
            if let Some(advance) = self.try_lift_truthy_chain(pc) {
                if pc + advance <= end_pc {
                    pc += advance;
                    continue;
                }
            }
            // Check if this PC starts a simple conditional value ternary.
            if let Some(advance) = self.try_lift_value_ternary(pc) {
                if pc + advance <= end_pc {
                    pc += advance;
                    continue;
                }
            }
            let insn = &self.func.instructions[pc];
            let advance = self.lift_instruction(insn, pc);
            pc += advance;
        }

        // If block doesn't end with a terminator, add fallthrough edge
        let block = &self.hir.cfg[self.current_block];
        if matches!(block.terminator, lantern_hir::cfg::Terminator::None) {
            if let Some(&next_node) = self.block_map.get(&end_pc) {
                self.hir
                    .cfg
                    .add_edge(self.current_block, next_node, HirEdge::unconditional());
                self.hir.cfg[self.current_block].terminator = lantern_hir::cfg::Terminator::Jump;
            }
        }
    }

    // ---- Helpers ----

    pub(super) fn reg_ref(&self, register: u8, pc: usize) -> RegRef {
        RegRef {
            register,
            pc,
            has_aux: self
                .func
                .instructions
                .get(pc)
                .map_or(false, |i| i.op.has_aux()),
        }
    }

    pub(super) fn alloc_expr(&mut self, expr: HirExpr, pc: usize) -> ExprId {
        let id = self.hir.exprs.alloc(expr);
        self.hir.set_origin_expr(id, pc);
        id
    }

    pub(super) fn emit_stmt(&mut self, stmt: HirStmt) {
        self.hir.cfg[self.current_block].stmts.push(stmt);
    }

    /// Collect arguments for a MULTRET consumer.
    ///
    /// When B=0 in CALL/RETURN, the arguments extend from `from_reg` up to
    /// the register where the previous MULTRET producer placed its results,
    /// with the MULTRET expression itself as the final argument.
    pub(super) fn collect_multret_args(&mut self, from_reg: u8, pc: usize) -> Vec<ExprId> {
        let mut args = Vec::new();
        if let Some((_top_expr, top_reg)) = self.top.take() {
            // Collect fixed registers between from_reg and top_reg (inclusive).
            // We include top_reg itself as a Reg reference instead of using
            // the raw ExprId so that variable recovery properly tracks def→use
            // chains. Using top_expr directly would create a second reference
            // to the same call expression, causing duplicate statements.
            for r in from_reg..=top_reg {
                args.push(self.alloc_expr(HirExpr::Reg(self.reg_ref(r, pc)), pc));
            }
        }
        args
    }

    pub(super) fn emit_assign_reg(&mut self, reg: RegRef, value: ExprId) {
        self.emit_stmt(HirStmt::RegAssign { target: reg, value });
    }

    /// Find iterator expressions from a predecessor FORGPREP block.
    /// FORGPREP stores its iterators in the block, then jumps to FORGLOOP.
    /// Assumes exactly one FORGPREP predecessor per FORGLOOP (Luau compiler invariant).
    fn find_forgen_iterators(&self) -> Vec<ExprId> {
        for pred in self
            .hir
            .cfg
            .neighbors_directed(self.current_block, Direction::Incoming)
        {
            if let Some(iters) = &self.hir.cfg[pred].for_gen_iterators {
                return iters.clone();
            }
        }
        Vec::new()
    }

    fn find_forgen_variant(&self) -> lantern_hir::cfg::ForGenVariant {
        for pred in self
            .hir
            .cfg
            .neighbors_directed(self.current_block, Direction::Incoming)
        {
            if let Some(variant) = self.hir.cfg[pred].for_gen_variant {
                return variant;
            }
        }
        lantern_hir::cfg::ForGenVariant::Generic
    }

    pub(super) fn add_jump_edge(&mut self, target_pc: usize) {
        if let Some(&target_node) = self.block_map.get(&target_pc) {
            self.hir
                .cfg
                .add_edge(self.current_block, target_node, HirEdge::unconditional());
        }
    }

    pub(super) fn emit_branch(&mut self, condition: ExprId, then_pc: usize, else_pc: usize, negated: bool) {
        self.hir.cfg[self.current_block].terminator =
            lantern_hir::cfg::Terminator::Branch { condition, negated };

        if let Some(&then_node) = self.block_map.get(&then_pc) {
            self.hir
                .cfg
                .add_edge(self.current_block, then_node, HirEdge::then_edge());
        }
        if let Some(&else_node) = self.block_map.get(&else_pc) {
            self.hir
                .cfg
                .add_edge(self.current_block, else_node, HirEdge::else_edge());
        }
    }

    /// Pop the last RegAssign to `register` from the current block's statements.
    /// Returns the assigned value expression, or None if no such statement found.
    pub(super) fn pop_last_reg_assign(&mut self, register: u8) -> Option<ExprId> {
        let stmts = &mut self.hir.cfg[self.current_block].stmts;
        // Search from the end for the most recent RegAssign to this register
        for i in (0..stmts.len()).rev() {
            if let HirStmt::RegAssign { target, value } = &stmts[i] {
                if target.register == register {
                    let expr = *value;
                    stmts.remove(i);
                    return Some(expr);
                }
            }
            // Don't search too far back — only the most recent few statements
            if stmts.len() - i > 3 {
                break;
            }
        }
        None
    }
}
