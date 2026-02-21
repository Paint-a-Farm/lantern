use petgraph::algo::dominators::simple_fast;
use petgraph::stable_graph::NodeIndex;
use petgraph::Direction;
use rustc_hash::FxHashMap;

use lantern_bytecode::scope_tree::ScopeTree;
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
                // If a scope covers this PC, the compiler intended this register
                // to have that name. Bind unconditionally — even if the value is
                // immediately overwritten. The scope IS the authority.
                //
                // Previous code had a liveness check here that created unnamed
                // temps for "dead" defs (overwritten before any use). This was
                // wrong: `local _, eventId = call()` repeated 20 times writes
                // r1 each time, and r1 is always "dead", but the scope says `_`.
                let key = (register, scope.0.to_string(), scope.1);
                let var_id = *scope_vars.entry(key).or_insert_with(|| {
                    let mut info = VarInfo::new();
                    info.name = Some(scope.0.to_string());
                    func.vars.alloc(info)
                });

                let info = func.vars.get_mut(var_id);
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
    bind_scope_initializers(func, scopes, &accesses, &by_register, &mut def_var);

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
    bind_prescope_defs_via_cfg(func, scopes, &accesses, &mut def_var);

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
                        _ => true, // Fallback: allow if no dominator info
                    }
                })
                .map(|(_, vid)| *vid);
            if let Some(vid) = var_id {
                use_var.insert(*use_ref, vid);
            }
        }
    }

    // Phase 5: Populate reg_map for later lookup (e.g., for-loop variable resolution)
    for (reg, &var_id) in def_var.iter().chain(use_var.iter()) {
        func.vars.bind_reg(*reg, var_id);
    }

    // Phase 6: Rewrite the HIR — replace RegRef with VarId
    rewrite_func(func, &def_var, &use_var);
}

/// Find the scope for a register at a given PC.
/// Returns (name, scope_start) if found.
fn find_scope(scopes: &ScopeTree, register: u8, pc: usize) -> Option<(&str, usize)> {
    // Find the narrowest enclosing scope
    let mut best: Option<(&str, usize, usize)> = None; // (name, start, width)
    for scope in scopes.scopes_for_register(register) {
        if scope.pc_range.start <= pc && pc < scope.pc_range.end {
            let width = scope.pc_range.end - scope.pc_range.start;
            if best.map_or(true, |(_, _, w)| width < w) {
                best = Some((&scope.name, scope.pc_range.start, width));
            }
        }
    }
    best.map(|(name, start, _)| (name, start))
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
                if candidate_pc == scope_start.saturating_sub(2) && scope_start >= 2 && candidate_pc != scope_start - 1 {
                    if !access.has_aux {
                        continue;
                    }
                }

                // Create or reuse the variable for this scope
                let var_id = find_existing_scope_var(func, register, scope_name, scope_start, def_var, accesses)
                    .unwrap_or_else(|| {
                        let mut info = VarInfo::new();
                        info.name = Some(scope_name.to_string());
                        func.vars.alloc(info)
                    });

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
                    def_var.get(&a.reg).map_or(false, |&vid| {
                        func.vars.get(vid).name.is_some()
                    })
                })
            });
            if !already_bound {
                if let Some(reg_accesses) = by_register.get(&register) {
                    // Try table constructor pattern: find a table def before scope_start
                    // with no intervening uses of this register.
                    'table_search: for access in reg_accesses.iter() {
                        if access.is_def && access.is_table_def && access.reg.pc < scope_start {
                            if !def_var_has_named(def_var, func, &access.reg) {
                                // Verify no uses between def and scope start
                                let has_intervening_use = reg_accesses.iter().any(|a| {
                                    !a.is_def && a.reg.pc > access.reg.pc && a.reg.pc < scope_start
                                });
                                if has_intervening_use {
                                    continue;
                                }
                                let var_id = find_existing_scope_var(func, register, scope_name, scope_start, def_var, accesses)
                                    .unwrap_or_else(|| {
                                        let mut info = VarInfo::new();
                                        info.name = Some(scope_name.to_string());
                                        func.vars.alloc(info)
                                    });
                                let info = func.vars.get_mut(var_id);
                                if !info.def_pcs.contains(&access.reg.pc) {
                                    info.def_pcs.push(access.reg.pc);
                                }
                                def_var.insert(access.reg, var_id);
                                break 'table_search;
                            }
                        }
                    }

                    // Try closure pattern: NewClosure/DupClosure at PC N followed
                    // by CAPTURE instructions, with scope starting after the last
                    // capture. The gap between def and scope can be large (one PC
                    // per captured upvalue).
                    if !def_var_has_named_for_scope(def_var, func, register, scope_start, accesses) {
                        for access in reg_accesses.iter() {
                            if access.is_def && access.is_closure_def && access.reg.pc < scope_start {
                                // Verify no uses of this register between def and scope start
                                let has_intervening_use = reg_accesses.iter().any(|a| {
                                    !a.is_def
                                        && a.reg.pc > access.reg.pc
                                        && a.reg.pc < scope_start
                                });
                                if has_intervening_use {
                                    continue;
                                }
                                if !def_var_has_named(def_var, func, &access.reg) {
                                    let var_id = find_existing_scope_var(func, register, scope_name, scope_start, def_var, accesses)
                                        .unwrap_or_else(|| {
                                            let mut info = VarInfo::new();
                                            info.name = Some(scope_name.to_string());
                                            func.vars.alloc(info)
                                        });
                                    let info = func.vars.get_mut(var_id);
                                    if !info.def_pcs.contains(&access.reg.pc) {
                                        info.def_pcs.push(access.reg.pc);
                                    }
                                    def_var.insert(access.reg, var_id);
                                    break;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

/// Check if a scope already has a named binding from a previous phase.
fn def_var_has_named_for_scope(
    def_var: &FxHashMap<RegRef, VarId>,
    func: &HirFunc,
    register: u8,
    scope_start: usize,
    accesses: &[RegAccess],
) -> bool {
    accesses.iter().any(|a| {
        a.is_def && a.reg.register == register && a.reg.pc < scope_start
            && def_var.get(&a.reg).map_or(false, |&vid| {
                func.vars.get(vid).name.is_some()
            })
    })
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
                            if access.is_def && access.reg.register == register && access.reg.pc == candidate_pc {
                                if def_var_has_named(def_var, func, &access.reg) {
                                    has_unconditional_initializer.insert((register, scope_start), true);
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

        // Check if there's already a VarId for this scope
        // (reuse it if we created one in Phase 3)
        let existing_var = find_existing_scope_var(func, register, scope_name, scope_start, def_var, accesses);

        // Collect predecessor blocks
        let preds: Vec<NodeIndex> = func.cfg
            .neighbors_directed(scope_node, Direction::Incoming)
            .collect();

        // Only check true predecessor blocks, NOT the scope block itself.
        // Within-block defs are already handled by Phase 3's pc+1/pc+2 lookups.
        // Including the scope block here would incorrectly bind earlier register
        // writes (e.g. discarded call results) to named variables.
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

                // Create or reuse the variable for this scope
                let var_id = existing_var.unwrap_or_else(|| {
                    let mut info = VarInfo::new();
                    info.name = Some(scope_name.to_string());
                    func.vars.alloc(info)
                });

                // Merge: if this def was assigned to an unnamed temp, reassign it
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

/// Check if a def is already bound to a NAMED variable (not an unnamed temp).
fn def_var_has_named(
    def_var: &FxHashMap<RegRef, VarId>,
    func: &HirFunc,
    reg: &RegRef,
) -> bool {
    if let Some(&var_id) = def_var.get(reg) {
        func.vars.get(var_id).name.is_some()
    } else {
        false
    }
}

/// Find an existing VarId for a scope if one was already created in Phase 3.
fn find_existing_scope_var(
    func: &HirFunc,
    register: u8,
    scope_name: &str,
    scope_start: usize,
    def_var: &FxHashMap<RegRef, VarId>,
    accesses: &[RegAccess],
) -> Option<VarId> {
    // Look through defs already bound to named variables for this register+scope
    for access in accesses {
        if access.is_def && access.reg.register == register {
            if let Some(&var_id) = def_var.get(&access.reg) {
                let info = func.vars.get(var_id);
                if info.name.as_deref() == Some(scope_name) {
                    // Check if this var was created from the same scope
                    // (it should have def_pcs within or near the scope)
                    if access.reg.pc >= scope_start
                        || access.reg.pc + 3 >= scope_start
                    {
                        return Some(var_id);
                    }
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
            HirExpr::Closure { proto_id, ref captures } => {
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

    // Rewrite statements block by block (RegAssign targets are defs)
    for node_idx in func.cfg.node_indices().collect::<Vec<_>>() {
        let stmts = std::mem::take(&mut func.cfg[node_idx].stmts);
        let new_stmts: Vec<HirStmt> = stmts
            .into_iter()
            .map(|stmt| rewrite_stmt(stmt, def_map))
            .collect();
        func.cfg[node_idx].stmts = new_stmts;
    }
}

fn rewrite_stmt(stmt: HirStmt, def_map: &FxHashMap<RegRef, VarId>) -> HirStmt {
    match stmt {
        HirStmt::RegAssign { target, value } => {
            if let Some(&var_id) = def_map.get(&target) {
                // Check if this is the first def — if so, make it a LocalDecl
                // For now, always emit as Assign; LocalDecl detection comes later
                HirStmt::Assign {
                    target: LValue::Local(var_id),
                    value,
                }
            } else {
                // Unresolved — keep as RegAssign
                HirStmt::RegAssign { target, value }
            }
        }
        // All other statements pass through unchanged
        // (their expressions were already rewritten in the expr pass)
        other => other,
    }
}
