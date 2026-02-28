use petgraph::algo::dominators::simple_fast;
use petgraph::stable_graph::NodeIndex;
use petgraph::Direction;
use rustc_hash::{FxHashMap, FxHashSet};

use lantern_bytecode::scope_tree::ScopeTree;
use lantern_hir::arena::ExprId;
use lantern_hir::expr::{CaptureSource, HirExpr};
use lantern_hir::func::HirFunc;
use lantern_hir::stmt::{HirStmt, LValue};
use lantern_hir::var::{RegRef, VarId, VarInfo};

use crate::collector::{self, RegAccess};

/// Recover variables from raw register references.
///
/// Uses debug scopes as hard constraints:
/// - Same register + overlapping scope → MustAlias (same variable)
/// - Same register + non-overlapping scopes → MustNotAlias (different variable)
///
/// After solving, rewrites all RegRef → VarId and RegAssign → Assign/LocalDecl.
pub fn recover_variables(func: &mut HirFunc, scopes: &ScopeTree, num_params: u8) {
    let accesses = collector::collect_accesses(func);

    // Always create parameter variables, even if there are no register accesses
    // (e.g., an empty function body like `function Foo:delete() end` still needs
    // its "self" parameter registered for correct colon-syntax detection).
    if accesses.is_empty() {
        for i in 0..num_params {
            let name = lookup_param_name(scopes, i);
            let mut info = VarInfo::new();
            info.name = name;
            info.is_param = true;
            let var_id = func.vars.alloc(info);
            func.params.push(var_id);
        }
        return;
    }

    // We maintain separate maps for defs and uses because a single instruction
    // can both read and write the same register at the same PC (e.g., CALL reads
    // r0 as the function reference, then writes r0 as the result). These must
    // resolve to different variables.
    let mut def_var: FxHashMap<RegRef, VarId> = FxHashMap::default();
    let mut use_var: FxHashMap<RegRef, VarId> = FxHashMap::default();

    // Phase 1: Group accesses by register
    let mut by_register: FxHashMap<u8, Vec<&RegAccess>> = FxHashMap::default();
    for access in &accesses {
        by_register
            .entry(access.reg.register)
            .or_default()
            .push(access);
    }

    // Phase 2: Create parameter variables first (r0..r{num_params-1})
    //
    // For non-vararg functions, parameter scopes start at PC 0.
    // For vararg functions (PREPVARARGS at PC 0), parameter scopes start at PC 1.
    // We find the parameter name from the earliest scope for each register.
    for i in 0..num_params {
        let name = lookup_param_name(scopes, i);
        let mut info = VarInfo::new();
        info.name = name;
        info.is_param = true;
        let var_id = func.vars.alloc(info);
        func.params.push(var_id);
        // Bind all accesses to this param register that fall within its scope
        let param_name = lookup_param_name(scopes, i);
        if let Some(reg_accesses) = by_register.get(&i) {
            for access in reg_accesses {
                let scope_name = scopes.lookup(i, access.reg.pc);
                if scope_name.is_some() && scope_name == param_name.as_deref() {
                    if access.is_def {
                        def_var.insert(access.reg, var_id);
                    } else {
                        use_var.insert(access.reg, var_id);
                    }
                }
            }
        }
    }

    // Phase 3: Match accesses that fall STRICTLY within a scope range.
    // No pc+1 guessing — only exact containment.
    //
    // For USES: always bind if inside a scope.
    // For DEFS: only bind if the value is "live" — i.e., there's no later
    // def of the same register before a use. This prevents binding discarded
    // call results that happen to reuse a named variable's register.
    for (&register, reg_accesses) in &by_register {
        let mut scope_vars: FxHashMap<(u8, String, usize), VarId> = FxHashMap::default();

        for access in reg_accesses {
            let map = if access.is_def { &def_var } else { &use_var };
            if map.contains_key(&access.reg) {
                continue; // Already bound (e.g., parameter)
            }

            // Strict containment: the access PC must be inside a scope range
            let scope = find_scope(scopes, register, access.reg.pc);

            if let Some(scope) = scope {
                // Key by (register, name, scope_start) — each scope entry maps to
                // a separate VarId. The compiler creates one scope entry per `local`
                // declaration; two entries with the same (register, name) but different
                // scope_starts are genuinely different variables (e.g. re-declarations
                // in sequential code like WoodHarvester's two `local x, y, z`).
                let key = (register, scope.0.to_string(), scope.1);
                let scope_range = scope.1..scope.2;
                let var_id = *scope_vars.entry(key).or_insert_with(|| {
                    let mut info = VarInfo::new();
                    info.name = Some(scope.0.to_string());
                    info.scope_pcs.push(scope_range.clone());
                    func.vars.alloc(info)
                });

                // Ensure scope range is recorded (may already be there from creation)
                let info = func.vars.get_mut(var_id);
                if !info
                    .scope_pcs
                    .iter()
                    .any(|r| r.start == scope_range.start && r.end == scope_range.end)
                {
                    info.scope_pcs.push(scope_range);
                }
                if access.is_def {
                    if !info.def_pcs.contains(&access.reg.pc) {
                        info.def_pcs.push(access.reg.pc);
                    }
                    def_var.insert(access.reg, var_id);
                } else {
                    if !info.use_pcs.contains(&access.reg.pc) {
                        info.use_pcs.push(access.reg.pc);
                    }
                    use_var.insert(access.reg, var_id);
                }
            } else {
                // No scope info — create a temporary per-def
                if access.is_def {
                    let mut info = VarInfo::new();
                    info.def_pcs.push(access.reg.pc);
                    let var_id = func.vars.alloc(info);
                    def_var.insert(access.reg, var_id);
                }
                // Uses without scope: deferred to Phase 4
            }
        }
    }

    // Phase 3a: Bind defining instructions to their scopes using the known
    // Luau compiler invariant: scope starts 1 PC after the def (or 2 for AUX).
    //
    // For each scope, look for a def at exactly (scope_start - 1) or
    // (scope_start - 2 for AUX). This is deterministic: no scanning, no
    // heuristics, just the known offset.
    //
    // Also handles table constructors (DupTable/NewTable) where the scope
    // opens after field initialization instructions.
    bind_scope_initializers(
        func,
        scopes,
        &accesses,
        &by_register,
        &mut def_var,
        &use_var,
    );

    // Phase 3b: CFG-based pre-scope binding.
    //
    // When the Luau compiler writes a register in multiple branches before
    // opening its scope at the join point, the defs fall outside the scope.
    // Example: `if cond then R4=1 else R4=0 end` with scope starting at
    // the join point.
    //
    // Use the CFG to find such patterns: for each scope with unbound defs,
    // check if predecessor blocks contain unresolved defs of the same register
    // that flow directly into the scope start.
    bind_prescope_defs_via_cfg(func, scopes, &accesses, &mut def_var, &use_var);

    // Phase 4: Resolve unscopped uses by finding their reaching def.
    // For each unresolved use of register R at PC p, find the latest
    // def of R at PC < p that can actually reach the use through the CFG.
    //
    // A def in one branch of an if/else CANNOT reach a use in the sibling
    // branch — only defs in dominating blocks (ancestors in the CFG) are valid.
    let mut unresolved_uses: Vec<RegRef> = Vec::new();
    for access in &accesses {
        if !access.is_def && !use_var.contains_key(&access.reg) {
            unresolved_uses.push(access.reg);
        }
    }

    // Build reaching-def map: register → sorted list of (pc, var_id)
    let mut reaching_defs: FxHashMap<u8, Vec<(usize, VarId)>> = FxHashMap::default();
    for access in &accesses {
        if access.is_def {
            if let Some(&var_id) = def_var.get(&access.reg) {
                reaching_defs
                    .entry(access.reg.register)
                    .or_default()
                    .push((access.reg.pc, var_id));
            }
        }
    }
    for defs in reaching_defs.values_mut() {
        defs.sort_by_key(|(pc, _)| *pc);
    }

    // Build dominator tree to filter reaching-defs.
    // A def in block D can only reach a use in block U if D dominates U
    // (i.e., D is on every path from the entry to U). This prevents defs
    // in sibling branches from incorrectly "reaching" across branches.
    //
    // Example: LOADB R3, false in block 0; Call into R3 in block 1 (then-branch);
    // Return R3 in block 2 (else-branch). Block 1 does NOT dominate block 2,
    // so the Call def is filtered out; the LOADB def in block 0 is used.
    let entry = func.cfg.node_indices().next();
    let doms = entry.map(|e| simple_fast(&func.cfg, e));

    for use_ref in &unresolved_uses {
        if let Some(defs) = reaching_defs.get(&use_ref.register) {
            let use_block = find_node_containing_pc(func, use_ref.pc);

            // Find the latest def strictly before this use whose block
            // dominates the use block.
            let var_id = defs
                .iter()
                .rev()
                .find(|(def_pc, _)| {
                    if *def_pc >= use_ref.pc {
                        return false;
                    }
                    let def_block = find_node_containing_pc(func, *def_pc);
                    match (def_block, use_block, &doms) {
                        (Some(d), Some(u), Some(dom_tree)) => {
                            if d == u {
                                true // Same block — always dominates
                            } else {
                                // Check if d dominates u by walking up the dominator tree
                                let mut current = Some(u);
                                while let Some(node) = current {
                                    if node == d {
                                        return true;
                                    }
                                    current = dom_tree.immediate_dominator(node);
                                }
                                false
                            }
                        }
                        _ => false, // Fail-fast: reject if dominator info unavailable
                    }
                })
                .map(|(_, vid)| *vid);
            if let Some(vid) = var_id {
                use_var.insert(*use_ref, vid);
            }
        }
    }

    // Phase 4b: Unify branch defs with dominator defs.
    //
    // Pattern: `R2 = false; if cond then R2 = <expr> end; return R2`
    // After Phase 4, the Return resolves R2 to Block 0's VarId (the LOADB def),
    // while Block 1's def gets a separate orphaned VarId that's never used.
    // This prevents the ternary folder from recognizing the pattern.
    //
    // Fix: for each register with multiple unscopped defs, if one def is in
    // a dominator block (already used by Phase 4 resolution) and another is
    // in a non-dominator branch block, unify the branch def with the dominator
    // def's VarId. This makes the assignment visible as a conditional update
    // to the same variable.
    if let Some(ref dom_tree) = doms {
        // Collect all unscopped defs grouped by register
        let mut unscopped_defs_by_reg: FxHashMap<u8, Vec<(RegRef, VarId)>> = FxHashMap::default();
        for access in &accesses {
            if access.is_def {
                if let Some(&vid) = def_var.get(&access.reg) {
                    let info = func.vars.get(vid);
                    if info.name.is_none() {
                        unscopped_defs_by_reg
                            .entry(access.reg.register)
                            .or_default()
                            .push((access.reg, vid));
                    }
                }
            }
        }

        // For each register with multiple unscopped defs, look for the pattern
        for (_register, defs) in &unscopped_defs_by_reg {
            if defs.len() < 2 {
                continue;
            }

            // Find which VarIds are actually used (have at least one use_var entry)
            let used_vids: FxHashSet<VarId> = use_var.values().copied().collect();

            // Find the "dominator def" — the one that's actually referenced by uses
            let dom_defs: Vec<_> = defs.iter().filter(|(_, vid)| used_vids.contains(vid)).collect();
            let orphan_defs: Vec<_> = defs.iter().filter(|(_, vid)| !used_vids.contains(vid)).collect();

            if dom_defs.len() != 1 || orphan_defs.is_empty() {
                continue;
            }

            let (dom_ref, dom_vid) = dom_defs[0];
            let dom_block = find_node_containing_pc(func, dom_ref.pc);

            for (orphan_ref, orphan_vid) in &orphan_defs {
                if *orphan_vid == *dom_vid {
                    continue;
                }
                let orphan_block = find_node_containing_pc(func, orphan_ref.pc);

                // The orphan must be in a DIFFERENT block from the dom def.
                // Same-block defs are sequential register reuses, not branch alternatives.
                // The orphan block must also be strictly dominated by the dom block
                // (not equal to it).
                let is_branch_def = match (dom_block, orphan_block) {
                    (Some(d), Some(o)) if d != o => {
                        let mut current = Some(o);
                        let mut found = false;
                        while let Some(node) = current {
                            if node == d {
                                found = true;
                                break;
                            }
                            current = dom_tree.immediate_dominator(node);
                        }
                        found
                    }
                    _ => false,
                };

                if is_branch_def {
                    // Rebind the orphan def to the dominator's VarId
                    def_var.insert(*orphan_ref, *dom_vid);
                }
            }
        }
    }

    // Phase 4c: Unify branch defs at join points (phi-node pattern).
    //
    // When the Luau compiler inlines a function, the inlined code writes results
    // into registers across multiple branches, all converging at a join point.
    // Unlike the pattern in Phase 4b, there is NO dominator def — all defs are
    // in non-dominating branch blocks. Phase 4 can't find a dominator def for
    // the use, and Phase 4b requires exactly 1 used def.
    //
    // Pattern:
    //   block 3: R4 = expr_a  ─┐
    //   block 6: R4 = expr_b  ─┤
    //   block 7: R4 = expr_c  ─┼→ block 15: use R4
    //   ...                    ─┘
    //
    // Fix: for uses still unresolved after Phase 4, check if multiple predecessor
    // blocks define the register. If so, create a unified VarId and bind all
    // the branch defs + the use to it.
    // Collect phi-node declarations to insert into dominator blocks.
    // Each entry is (dominator_block, VarId) — we insert `local x` there.
    let mut phi_decls: Vec<(NodeIndex, VarId)> = Vec::new();

    if let Some(ref dom_tree) = doms {
        // Find uses that are STILL unresolved after Phase 4
        let still_unresolved: Vec<RegRef> = unresolved_uses
            .iter()
            .filter(|u| !use_var.contains_key(u))
            .copied()
            .collect();

        for use_ref in &still_unresolved {
            let use_block = match find_node_containing_pc(func, use_ref.pc) {
                Some(b) => b,
                None => continue,
            };

            // Get predecessor blocks of the use's block
            let preds: Vec<NodeIndex> = func
                .cfg
                .neighbors_directed(use_block, Direction::Incoming)
                .collect();

            if preds.len() < 2 {
                continue;
            }

            // Find the last def of this register in each predecessor block
            let mut pred_defs: Vec<RegRef> = Vec::new();
            for pred_node in &preds {
                let (pred_start, pred_end) = func.cfg[*pred_node].pc_range;
                // Find the last def of this register in this predecessor
                let last_def = accesses
                    .iter()
                    .filter(|a| {
                        a.is_def
                            && a.reg.register == use_ref.register
                            && a.reg.pc >= pred_start
                            && a.reg.pc < pred_end
                    })
                    .max_by_key(|a| a.reg.pc);

                if let Some(def_access) = last_def {
                    // Only consider defs that aren't already bound to a named variable
                    let already_named = def_var
                        .get(&def_access.reg)
                        .map_or(false, |vid| func.vars.get(*vid).name.is_some());
                    if !already_named {
                        pred_defs.push(def_access.reg);
                    }
                }
            }

            // Need at least 2 predecessor defs to form a phi-node
            if pred_defs.len() < 2 {
                continue;
            }

            // Create a unified VarId for all branch defs
            let info = VarInfo::new();
            let unified_vid = func.vars.alloc(info);

            // Bind all predecessor defs to the unified VarId
            for pred_def in &pred_defs {
                def_var.insert(*pred_def, unified_vid);
                let info = func.vars.get_mut(unified_vid);
                if !info.def_pcs.contains(&pred_def.pc) {
                    info.def_pcs.push(pred_def.pc);
                }
            }

            // Bind the use to the same unified VarId
            use_var.insert(*use_ref, unified_vid);

            // Insert `local x` declaration at the immediate dominator of the
            // use block. This ensures the variable is in scope for all branches
            // and the join point.
            if let Some(idom) = dom_tree.immediate_dominator(use_block) {
                phi_decls.push((idom, unified_vid));
            }
        }
    }

    // Insert phi-node LocalDecl statements into dominator blocks.
    // These appear at the end of the block's stmts (before the terminator),
    // which in the structured output means right before the if-tree.
    for (block, var_id) in &phi_decls {
        func.cfg[*block].stmts.push(HirStmt::LocalDecl {
            var: *var_id,
            init: None,
        });
    }

    // Phase 5: Populate reg_map for later lookup (e.g., for-loop variable resolution)
    for (reg, &var_id) in def_var.iter().chain(use_var.iter()) {
        func.vars.bind_reg(*reg, var_id);
    }

    // Phase 6: Rewrite the HIR — replace RegRef with VarId
    rewrite_func(func, &def_var, &use_var);
}

/// Find the scope for a register at a given PC.
/// Returns (name, scope_start, scope_end) if found.
fn find_scope(scopes: &ScopeTree, register: u8, pc: usize) -> Option<(&str, usize, usize)> {
    // Find the widest (outermost) enclosing scope.
    //
    // When the Luau compiler inlines a local function, it reuses the caller's
    // register for the inlined parameter and emits a nested debug scope with
    // the parameter name. E.g. for `for name in ...` calling `addCommandToResults(name)`:
    //   r7 'name'        pc=24..61  (outer — for-loop variable)
    //   r7 'commandName' pc=33..61  (inner — inlined parameter)
    //
    // The inner scope is strictly contained in the outer and should NOT override it.
    // Picking the widest scope gives us the original variable name.
    let mut best: Option<(&str, usize, usize, usize)> = None; // (name, start, end, width)
    for scope in scopes.scopes_for_register(register) {
        if scope.pc_range.start <= pc && pc < scope.pc_range.end {
            let width = scope.pc_range.end - scope.pc_range.start;
            if best.map_or(true, |(_, _, _, w)| width > w) {
                best = Some((&scope.name, scope.pc_range.start, scope.pc_range.end, width));
            }
        }
    }
    best.map(|(name, start, end, _)| (name, start, end))
}

/// Bind defining instructions to their scopes using compiler invariants.
///
/// The Luau compiler starts a variable's scope on the instruction AFTER the
/// defining STORE. So for `local x = expr`, if the STORE is at PC N, the
/// scope starts at PC N+1. For AUX instructions (NewTable, GetImport), the
/// scope starts at PC N+2 because the instruction occupies 2 PC slots.
///
/// For table constructors (DupTable/NewTable + SETTABLEKS), the scope opens
/// after all field-init instructions complete.
///
/// This function iterates over every scope and looks for a def at exactly
/// the expected PC offset. No scanning, no heuristics.
fn bind_scope_initializers(
    func: &mut HirFunc,
    scopes: &ScopeTree,
    accesses: &[RegAccess],
    by_register: &FxHashMap<u8, Vec<&RegAccess>>,
    def_var: &mut FxHashMap<RegRef, VarId>,
    use_var: &FxHashMap<RegRef, VarId>,
) {
    // Build a quick lookup: (register, pc) → &RegAccess for defs
    let mut def_at_pc: FxHashMap<(u8, usize), &RegAccess> = FxHashMap::default();
    for access in accesses {
        if access.is_def {
            def_at_pc.insert((access.reg.register, access.reg.pc), access);
        }
    }

    // For each scope, try to find its defining instruction
    for scope in scopes.all_scopes() {
        let register = scope.register;
        let scope_start = scope.pc_range.start;
        let scope_end = scope.pc_range.end;
        let scope_name = &scope.name;

        // Try the known offsets: scope_start - 1 (normal) and scope_start - 2 (AUX)
        let candidates: &[usize] = if scope_start >= 2 {
            &[scope_start - 1, scope_start - 2]
        } else if scope_start >= 1 {
            &[scope_start - 1]
        } else {
            &[]
        };

        for &candidate_pc in candidates {
            if let Some(access) = def_at_pc.get(&(register, candidate_pc)) {
                // Check it's not already bound to a named variable
                if def_var_has_named(def_var, func, &access.reg) {
                    // Already correctly bound — done for this scope
                    break;
                }

                // For the pc-2 case, verify the instruction actually has an AUX word
                if candidate_pc == scope_start.saturating_sub(2)
                    && scope_start >= 2
                    && candidate_pc != scope_start - 1
                {
                    if !access.has_aux {
                        continue;
                    }
                }

                // Only treat as a declaration if the candidate is in the same
                // basic block as the scope start. When the candidate PC is in
                // a predecessor block (e.g. a then-branch before a join point),
                // the def is conditional and should be an assignment, not a
                // declaration. Phase 3b handles those with None for decl_pc.
                let scope_block = find_node_containing_pc(func, scope_start);
                let candidate_block = find_node_containing_pc(func, candidate_pc);
                let is_same_block = match (scope_block, candidate_block) {
                    (Some(a), Some(b)) => a == b,
                    _ => true, // Fallback: treat as same block if we can't determine
                };
                let decl_pc = if is_same_block {
                    Some(candidate_pc)
                } else {
                    None // Conditional def — not a declaration point
                };

                // Create or reuse the variable for this scope
                let var_id = get_or_create_scope_var(
                    func,
                    register,
                    scope_name,
                    scope_start,
                    scope_end,
                    decl_pc,
                    def_var,
                    use_var,
                    accesses,
                );

                let info = func.vars.get_mut(var_id);
                if !info.def_pcs.contains(&access.reg.pc) {
                    info.def_pcs.push(access.reg.pc);
                }
                def_var.insert(access.reg, var_id);
                break; // Found the initializer for this scope
            }
        }

        // Forward match: scope may start several PCs after the def because
        // of intervening instructions that are part of the initialization.
        //
        // Two patterns:
        // 1. Table constructor: DupTable/NewTable + SETTABLEKS fields
        // 2. Closure: NewClosure/DupClosure + CAPTURE instructions
        //
        // In both cases, the scope opens after the initialization sequence.
        if scope_start >= 1 {
            // Check if any candidate was found above
            let already_bound = candidates.iter().any(|&pc| {
                def_at_pc.get(&(register, pc)).map_or(false, |a| {
                    def_var
                        .get(&a.reg)
                        .map_or(false, |&vid| func.vars.get(vid).name.is_some())
                })
            });
            if !already_bound {
                if let Some(reg_accesses) = by_register.get(&register) {
                    // Find the closest table def and closest closure def before
                    // scope_start, then pick whichever is nearest. This prevents
                    // a table def from stealing a scope that belongs to a later
                    // closure def on the same register (register reuse).
                    let mut best_table: Option<&RegAccess> = None;
                    let mut best_closure: Option<&RegAccess> = None;
                    for access in reg_accesses.iter() {
                        if access.is_def && access.reg.pc < scope_start
                            && !def_var_has_named(def_var, func, &access.reg)
                        {
                            if access.is_table_def {
                                if best_table.map_or(true, |b| access.reg.pc > b.reg.pc) {
                                    best_table = Some(access);
                                }
                            }
                            if access.is_closure_def {
                                if best_closure.map_or(true, |b| access.reg.pc > b.reg.pc) {
                                    best_closure = Some(access);
                                }
                            }
                        }
                    }

                    // Pick the candidate closest to scope_start.
                    let winner = match (best_table, best_closure) {
                        (Some(t), Some(c)) => {
                            if c.reg.pc >= t.reg.pc { Some(c) } else { Some(t) }
                        }
                        (Some(t), None) => Some(t),
                        (None, Some(c)) => {
                            // Only use closure if the scope isn't already bound
                            if !scope_entry_already_bound(
                                func, register, scope_name, scope_start, scope_end,
                                def_var, use_var, accesses,
                            ) {
                                Some(c)
                            } else {
                                None
                            }
                        }
                        (None, None) => None,
                    };

                    // Reject the candidate if another DEF of the same register
                    // exists between the candidate PC and scope_start. This
                    // means the register was reused (e.g., table/closure as a
                    // call arg, then the register reused for a for-loop var).
                    let winner = winner.filter(|w| {
                        !reg_accesses.iter().any(|a| {
                            a.is_def
                                && a.reg.pc > w.reg.pc
                                && a.reg.pc < scope_start
                        })
                    });

                    // For closure candidates, also verify the scope starts
                    // right after the initialization sequence (NewClosure +
                    // Captures). For-loop implicit defs aren't recorded as
                    // RegAccess, so the gap check catches those.
                    let winner = winner.filter(|w| {
                        if w.is_closure_def {
                            let num_captures = match func.exprs.get(
                                find_def_value(func, &w.reg),
                            ) {
                                HirExpr::Closure { captures, .. } => captures.len(),
                                _ => 0,
                            };
                            let expected = w.reg.pc + 1 + num_captures;
                            scope_start <= expected + 1
                        } else {
                            true
                        }
                    });

                    if let Some(access) = winner {
                        let var_id = get_or_create_scope_var(
                            func,
                            register,
                            scope_name,
                            scope_start,
                            scope_end,
                            Some(access.reg.pc),
                            def_var,
                            use_var,
                            accesses,
                        );
                        let info = func.vars.get_mut(var_id);
                        if !info.def_pcs.contains(&access.reg.pc) {
                            info.def_pcs.push(access.reg.pc);
                        }
                        def_var.insert(access.reg, var_id);
                    }
                }
            }
        }
    }

    // Batch backward scan: the Luau compiler batches multi-local declarations.
    //
    // For `local a, b, c = expr1, expr2, expr3`, it emits:
    //   PC N:   R_a = expr1
    //   PC N+1: R_b = expr2
    //   PC N+2: R_c = expr3
    //   PC N+3: scopes for R_a, R_b, R_c all open (same scope_start)
    //
    // The exact-offset pass (pc-1, pc-2) only catches the last scope in
    // a batch (R_c at PC N+2 matches scope_start N+3 - 1). The others
    // need this batch scan.
    //
    // Algorithm:
    // 1. Collect all still-unbound scopes
    // 2. Group by scope_start
    // 3. For each group, collect ALL defs (across all registers) before scope_start,
    //    sorted by PC descending
    // 4. Match: for each scope in the group (by register), find the latest unbound
    //    def on that register before scope_start with no intervening use
    bind_batch_initializers(func, scopes, accesses, by_register, def_var, use_var);
}

/// Batch backward scan for multi-local declarations.
///
/// The Luau compiler emits batches like:
///   PC N:   R_a = expr1
///   PC N+1: R_b = expr2
///   PC N+2: R_c = expr3
///   PC N+3: scopes for R_a, R_b, R_c all open
///
/// For each group of unbound scopes sharing the same scope_start, find
/// the nearest unbound def on each scope's register before scope_start,
/// checking that no intervening use exists on that register.
fn bind_batch_initializers(
    func: &mut HirFunc,
    scopes: &ScopeTree,
    accesses: &[RegAccess],
    by_register: &FxHashMap<u8, Vec<&RegAccess>>,
    def_var: &mut FxHashMap<RegRef, VarId>,
    use_var: &FxHashMap<RegRef, VarId>,
) {
    // Collect unbound scopes: those without a decl_pc yet
    let mut unbound: Vec<&lantern_bytecode::scope_tree::LocalScope> = Vec::new();
    for scope in scopes.all_scopes() {
        if !scope_entry_already_bound(
            func,
            scope.register,
            &scope.name,
            scope.pc_range.start,
            scope.pc_range.end,
            def_var,
            use_var,
            accesses,
        ) {
            unbound.push(scope);
        }
    }

    // Group unbound scopes by scope_start
    let mut by_start: FxHashMap<usize, Vec<&lantern_bytecode::scope_tree::LocalScope>> =
        FxHashMap::default();
    for scope in &unbound {
        by_start
            .entry(scope.pc_range.start)
            .or_default()
            .push(scope);
    }

    // Process each group
    for (scope_start, group) in &by_start {
        let scope_start = *scope_start;
        if scope_start == 0 {
            continue;
        }

        // For each scope in the group, find the nearest unbound def on its register
        // before scope_start with no intervening use.
        //
        // Collect matches as (RegRef, scope_index) to avoid borrow conflicts.
        let mut matches: Vec<(RegRef, usize)> = Vec::new();

        for (idx, scope) in group.iter().enumerate() {
            let register = scope.register;
            if let Some(reg_accesses) = by_register.get(&register) {
                // Find the nearest def before scope_start that isn't already named
                let nearest_def = reg_accesses
                    .iter()
                    .filter(|a| a.is_def && a.reg.pc < scope_start)
                    .filter(|a| !def_var_has_named(def_var, func, &a.reg))
                    .max_by_key(|a| a.reg.pc);

                if let Some(def_access) = nearest_def {
                    // Verify no intervening use between def and scope_start
                    let has_intervening_use = reg_accesses.iter().any(|a| {
                        !a.is_def && a.reg.pc > def_access.reg.pc && a.reg.pc < scope_start
                    });
                    if !has_intervening_use {
                        matches.push((def_access.reg, idx));
                    }
                }
            }
        }

        // Apply matches
        for (def_reg, scope_idx) in matches {
            let scope = group[scope_idx];
            // Only treat as declaration if the def is in the same block as
            // the scope start. Conditional branch defs should be assignments.
            let scope_block = find_node_containing_pc(func, scope.pc_range.start);
            let def_block = find_node_containing_pc(func, def_reg.pc);
            let is_same_block = match (scope_block, def_block) {
                (Some(a), Some(b)) => a == b,
                _ => true,
            };
            let decl_pc = if is_same_block {
                Some(def_reg.pc)
            } else {
                None
            };
            let var_id = get_or_create_scope_var(
                func,
                scope.register,
                &scope.name,
                scope.pc_range.start,
                scope.pc_range.end,
                decl_pc,
                def_var,
                use_var,
                accesses,
            );
            let info = func.vars.get_mut(var_id);
            if !info.def_pcs.contains(&def_reg.pc) {
                info.def_pcs.push(def_reg.pc);
            }
            def_var.insert(def_reg, var_id);
        }
    }
}

/// Check if a specific scope entry already has a named variable binding.
///
/// Unlike a broad "any named def for this register before scope_start",
/// this checks if the exact scope range (start..end) is already recorded
/// on a VarId with a decl_pc set. This prevents defs from *other* scope
/// entries for the same register from blocking the backward scan.
fn scope_entry_already_bound(
    func: &HirFunc,
    register: u8,
    scope_name: &str,
    scope_start: usize,
    scope_end: usize,
    def_var: &FxHashMap<RegRef, VarId>,
    use_var: &FxHashMap<RegRef, VarId>,
    accesses: &[RegAccess],
) -> bool {
    find_existing_scope_var(
        func,
        register,
        scope_name,
        scope_start,
        scope_end,
        def_var,
        use_var,
        accesses,
    )
    .map_or(false, |vid| func.vars.get(vid).decl_pc.is_some())
}

/// Bind pre-scope defs to named variables using CFG structure.
///
/// When the Luau compiler writes a register in multiple code paths before
/// opening its debug scope at a join point, the defs fall outside the scope.
///
/// This function uses the CFG to find the pattern deterministically:
/// 1. Find blocks where a named scope starts
/// 2. For each predecessor block, find the LAST def of that register
/// 3. If the def is unresolved (no scope), bind it to the named variable
///
/// This handles:
/// - if/else both writing R4, scope starting at the join point
/// - Single-path writes before scope (e.g., initialization before scope opens)
fn bind_prescope_defs_via_cfg(
    func: &mut HirFunc,
    scopes: &ScopeTree,
    accesses: &[RegAccess],
    def_var: &mut FxHashMap<RegRef, VarId>,
    use_var: &FxHashMap<RegRef, VarId>,
) {
    // Build a map: block_start_pc → NodeIndex for quick lookup
    let mut pc_to_node: FxHashMap<usize, NodeIndex> = FxHashMap::default();
    for node_idx in func.cfg.node_indices() {
        let (start, _end) = func.cfg[node_idx].pc_range;
        pc_to_node.insert(start, node_idx);
    }

    // Build a lookup for scopes with unconditional initializers.
    // A scope initializer is "unconditional" when it's in the SAME basic block
    // as the scope start. This means the assignment always executes before
    // entering the scope — predecessor defs are dead.
    //
    // If the initializer is in a predecessor block (e.g., the else-branch of
    // an if/else that also writes R4 in the then-branch), it's conditional
    // and predecessor defs should still be bound.
    let mut has_unconditional_initializer: FxHashMap<(u8, usize), bool> = FxHashMap::default();
    for scope in scopes.all_scopes() {
        let register = scope.register;
        let scope_start = scope.pc_range.start;
        // Find the block containing the scope start
        let scope_node = find_node_containing_pc(func, scope_start);
        if let Some(scope_node) = scope_node {
            let (block_start, _) = func.cfg[scope_node].pc_range;
            // Check the known initializer offsets
            for &offset in &[1usize, 2] {
                if scope_start >= offset {
                    let candidate_pc = scope_start - offset;
                    // Only count as unconditional if the initializer is in the same block
                    if candidate_pc >= block_start {
                        for access in accesses {
                            if access.is_def
                                && access.reg.register == register
                                && access.reg.pc == candidate_pc
                            {
                                if def_var_has_named(def_var, func, &access.reg) {
                                    has_unconditional_initializer
                                        .insert((register, scope_start), true);
                                }
                                break;
                            }
                        }
                    }
                }
            }
        }
    }

    // For each scope, find unresolved defs in predecessor blocks
    for scope in scopes.all_scopes() {
        let register = scope.register;
        let scope_start = scope.pc_range.start;
        let scope_end = scope.pc_range.end;
        let scope_name = &scope.name;

        // If this scope has an UNCONDITIONAL initializer in the same block
        // (bound by Phase 3a), skip predecessor binding. The initializer
        // always overwrites the register, making predecessor writes dead.
        //
        // Example: `if cond then R1 = call() end; R1 = self.field`
        // The call() result is dead — R1 is unconditionally overwritten.
        //
        // But if the "initializer" is in a predecessor block (conditional),
        // we still need to bind other predecessor defs:
        // Example: `if cond then R4 = 1 else R4 = 0 end` → both are needed.
        if has_unconditional_initializer.contains_key(&(register, scope_start)) {
            continue;
        }

        // Find the block that contains the scope start
        let scope_node = find_node_containing_pc(func, scope_start);
        let scope_node = match scope_node {
            Some(n) => n,
            None => continue,
        };

        // Collect predecessor blocks
        let preds: Vec<NodeIndex> = func
            .cfg
            .neighbors_directed(scope_node, Direction::Incoming)
            .collect();

        // Only check true predecessor blocks, NOT the scope block itself.
        // Within-block defs are already handled by Phase 3's pc+1/pc+2 lookups.
        for pred_node in preds {
            let pred_block = &func.cfg[pred_node];
            let (pred_start, pred_end) = pred_block.pc_range;

            // Find the LAST def of this register in this predecessor block
            // that is before the scope start and currently unresolved.
            let last_def = accesses
                .iter()
                .filter(|a| {
                    a.is_def
                        && a.reg.register == register
                        && a.reg.pc >= pred_start
                        && a.reg.pc < pred_end
                        && a.reg.pc < scope_start
                        && !def_var_has_named(def_var, func, &a.reg)
                })
                .max_by_key(|a| a.reg.pc);

            if let Some(access) = last_def {
                // Verify no uses of this register between the def and the
                // scope start (the value flows directly into the scope).
                let has_intervening_use = accesses.iter().any(|a| {
                    !a.is_def
                        && a.reg.register == register
                        && a.reg.pc > access.reg.pc
                        && a.reg.pc < scope_start
                });
                if has_intervening_use {
                    continue;
                }

                // Pre-scope branch defs are NOT declaration points — the variable
                // was declared elsewhere (before the if-statement). These are
                // conditional assignments flowing into a join point.
                let var_id = get_or_create_scope_var(
                    func,
                    register,
                    scope_name,
                    scope_start,
                    scope_end,
                    None, // Not a declaration — branch def
                    def_var,
                    use_var,
                    accesses,
                );

                let info = func.vars.get_mut(var_id);
                if !info.def_pcs.contains(&access.reg.pc) {
                    info.def_pcs.push(access.reg.pc);
                }
                def_var.insert(access.reg, var_id);
            }
        }
    }
}

/// Look up a parameter's name from debug scopes.
///
/// For non-vararg functions, parameter scopes start at PC 0.
/// For vararg functions (PREPVARARGS at PC 0), parameter scopes start at PC 1.
/// We find the earliest scope for the register, which is the parameter name.
fn lookup_param_name(scopes: &ScopeTree, register: u8) -> Option<String> {
    scopes
        .scopes_for_register(register)
        .min_by_key(|s| s.pc_range.start)
        .map(|s| s.name.clone())
}

/// Find the CFG node that contains the given PC.
fn find_node_containing_pc(func: &HirFunc, pc: usize) -> Option<NodeIndex> {
    for node_idx in func.cfg.node_indices() {
        let (start, end) = func.cfg[node_idx].pc_range;
        if pc >= start && pc < end {
            return Some(node_idx);
        }
    }
    None
}

/// Find the expression value assigned to a register def (RegAssign target).
fn find_def_value(func: &HirFunc, reg: &RegRef) -> ExprId {
    for node_idx in func.cfg.node_indices() {
        for stmt in &func.cfg[node_idx].stmts {
            if let HirStmt::RegAssign { target, value } = stmt {
                if target.register == reg.register && target.pc == reg.pc {
                    return *value;
                }
            }
        }
    }
    ExprId(0) // fallback — shouldn't happen
}

/// Check if a def is already bound to a NAMED variable (not an unnamed temp).
fn def_var_has_named(def_var: &FxHashMap<RegRef, VarId>, func: &HirFunc, reg: &RegRef) -> bool {
    if let Some(&var_id) = def_var.get(reg) {
        func.vars.get(var_id).name.is_some()
    } else {
        false
    }
}

/// Find or create a VarId for a scope, recording the scope range and declaration PC.
///
/// This encapsulates the common pattern across Phase 3a and 3b:
/// - Look for an existing VarId via `find_existing_scope_var`
/// - If not found, create a new VarInfo with the scope's name
/// - Record the scope PC range on the VarInfo
/// - If `decl_pc` is provided and the VarInfo doesn't have one yet, set it
fn get_or_create_scope_var(
    func: &mut HirFunc,
    register: u8,
    scope_name: &str,
    scope_start: usize,
    scope_end: usize,
    decl_pc: Option<usize>,
    def_var: &FxHashMap<RegRef, VarId>,
    use_var: &FxHashMap<RegRef, VarId>,
    accesses: &[RegAccess],
) -> VarId {
    let var_id = find_existing_scope_var(
        func,
        register,
        scope_name,
        scope_start,
        scope_end,
        def_var,
        use_var,
        accesses,
    )
    .unwrap_or_else(|| {
        let mut info = VarInfo::new();
        info.name = Some(scope_name.to_string());
        func.vars.alloc(info)
    });
    let info = func.vars.get_mut(var_id);
    // Record scope range if not already present
    let range = scope_start..scope_end;
    if !info
        .scope_pcs
        .iter()
        .any(|r| r.start == range.start && r.end == range.end)
    {
        info.scope_pcs.push(range);
    }
    // Set declaration PC if this is the initializer and none is set yet
    if let Some(pc) = decl_pc {
        if info.decl_pc.is_none() {
            info.decl_pc = Some(pc);
        }
    }
    var_id
}

/// Find an existing VarId for a scope if one was already created in Phase 3.
///
/// Each debug scope entry (register, name, pc_range) corresponds to one `local`
/// declaration in the source. Non-overlapping scope entries for the same
/// (register, name) are genuinely different variables (e.g. re-declarations in
/// sequential code, or branch-local declarations in if/elseif branches).
///
/// This function only matches a VarId whose recorded scope_pcs include the
/// target scope range. This prevents merging genuinely different variables.
fn find_existing_scope_var(
    func: &HirFunc,
    register: u8,
    scope_name: &str,
    scope_start: usize,
    scope_end: usize,
    def_var: &FxHashMap<RegRef, VarId>,
    use_var: &FxHashMap<RegRef, VarId>,
    accesses: &[RegAccess],
) -> Option<VarId> {
    let target_range = scope_start..scope_end;

    // Look through defs already bound to named variables for this register.
    // Only match if the VarId's recorded scopes include this exact range.
    for access in accesses {
        if access.is_def && access.reg.register == register {
            if let Some(&var_id) = def_var.get(&access.reg) {
                let info = func.vars.get(var_id);
                if info.name.as_deref() == Some(scope_name)
                    && info
                        .scope_pcs
                        .iter()
                        .any(|r| r.start == target_range.start && r.end == target_range.end)
                {
                    return Some(var_id);
                }
            }
        }
    }
    // Also check use_var — Phase 3 may have bound uses within this scope range
    // to a VarId that Phase 3a hasn't seen yet.
    for access in accesses {
        if !access.is_def
            && access.reg.register == register
            && access.reg.pc >= scope_start
            && access.reg.pc < scope_end
        {
            if let Some(&var_id) = use_var.get(&access.reg) {
                let info = func.vars.get(var_id);
                if info.name.as_deref() == Some(scope_name)
                    && info
                        .scope_pcs
                        .iter()
                        .any(|r| r.start == target_range.start && r.end == target_range.end)
                {
                    return Some(var_id);
                }
            }
        }
    }
    None
}

/// Rewrite all RegRef in the HIR to VarId using the resolved mappings.
/// Uses separate maps for defs (RegAssign targets) and uses (Reg expressions).
fn rewrite_func(
    func: &mut HirFunc,
    def_map: &FxHashMap<RegRef, VarId>,
    use_map: &FxHashMap<RegRef, VarId>,
) {
    // Rewrite expressions (these are all uses)
    let expr_count = func.exprs.len();
    for i in 0..expr_count {
        let expr_id = lantern_hir::arena::ExprId(i as u32);
        let expr = func.exprs.get(expr_id).clone();
        match expr {
            HirExpr::Reg(reg) => {
                if let Some(&var_id) = use_map.get(&reg) {
                    func.exprs.replace(expr_id, HirExpr::Var(var_id));
                }
            }
            HirExpr::Closure {
                proto_id,
                ref captures,
            } => {
                let new_captures: Vec<_> = captures
                    .iter()
                    .map(|cap| {
                        let new_source = match &cap.source {
                            CaptureSource::Register(reg) => {
                                if let Some(&var_id) = use_map.get(reg) {
                                    CaptureSource::Var(var_id)
                                } else {
                                    cap.source.clone()
                                }
                            }
                            other => other.clone(),
                        };
                        lantern_hir::expr::Capture {
                            kind: cap.kind,
                            source: new_source,
                        }
                    })
                    .collect();
                func.exprs.replace(
                    expr_id,
                    HirExpr::Closure {
                        proto_id,
                        captures: new_captures,
                    },
                );
            }
            _ => {}
        }
    }

    // Rewrite statements: RegAssign → LocalDecl or Assign { Local }.
    //
    // Only defs matching decl_pc become LocalDecl (zero-ambiguity from
    // bytecode scope info). Everything else becomes Assign { Local },
    // and the emitter handles the `local` keyword via its declared set.
    let nodes: Vec<_> = func.cfg.node_indices().collect();
    for node_idx in nodes {
        let stmts = std::mem::take(&mut func.cfg[node_idx].stmts);
        let new_stmts: Vec<HirStmt> = stmts
            .into_iter()
            .map(|stmt| rewrite_stmt(stmt, def_map, &func.vars))
            .collect();
        func.cfg[node_idx].stmts = new_stmts;
    }
}

fn rewrite_stmt(
    stmt: HirStmt,
    def_map: &FxHashMap<RegRef, VarId>,
    vars: &lantern_hir::var::VarTable,
) -> HirStmt {
    match stmt {
        HirStmt::RegAssign { target, value } => {
            if let Some(&var_id) = def_map.get(&target) {
                let info = vars.get(var_id);

                // decl_pc from scope analysis: the compiler tells us exactly
                // which instruction is the declaration point.
                if info.decl_pc == Some(target.pc) {
                    HirStmt::LocalDecl {
                        var: var_id,
                        init: Some(value),
                    }
                } else {
                    HirStmt::Assign {
                        target: LValue::Local(var_id),
                        value,
                    }
                }
            } else {
                HirStmt::RegAssign { target, value }
            }
        }
        other => other,
    }
}
