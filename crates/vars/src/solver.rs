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
            let name = scopes.lookup(i, 0).map(|s| s.to_string());
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
    for i in 0..num_params {
        let name = scopes.lookup(i, 0).map(|s| s.to_string());
        let mut info = VarInfo::new();
        info.name = name;
        info.is_param = true;
        let var_id = func.vars.alloc(info);
        func.params.push(var_id);
        // Bind all accesses to this param register that fall within its scope
        if let Some(reg_accesses) = by_register.get(&i) {
            for access in reg_accesses {
                let scope_name = scopes.lookup(i, access.reg.pc);
                let param_name = scopes.lookup(i, 0);
                if scope_name == param_name && param_name.is_some() {
                    if access.is_def {
                        def_var.insert(access.reg, var_id);
                    } else {
                        use_var.insert(access.reg, var_id);
                    }
                }
            }
        }
    }

    // Phase 3: For each register, create variables from scope partitioning.
    // Defs in the same scope create/share a variable. Uses in the same scope
    // also bind to that variable.
    for (&register, reg_accesses) in &by_register {
        // Group by scope: accesses in the same scope → same variable
        let mut scope_vars: FxHashMap<(u8, String, usize), VarId> = FxHashMap::default();

        for access in reg_accesses {
            let map = if access.is_def { &def_var } else { &use_var };
            if map.contains_key(&access.reg) {
                continue; // Already bound (e.g., parameter)
            }

            // For defs, also try pc+1: the bytecode compiler starts the scope
            // at the instruction AFTER the defining instruction (e.g., CALL at pc 4
            // defines x, but x's scope starts at pc 5).
            let scope = find_scope(scopes, register, access.reg.pc)
                .or_else(|| {
                    if access.is_def {
                        find_scope(scopes, register, access.reg.pc + 1)
                    } else {
                        None
                    }
                });
            if let Some(scope) = scope {
                let key = (register, scope.0.to_string(), scope.1);
                let var_id = *scope_vars.entry(key).or_insert_with(|| {
                    let mut info = VarInfo::new();
                    info.name = Some(scope.0.to_string());
                    func.vars.alloc(info)
                });

                // Record def/use on existing variable
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

    // Phase 4: Resolve unscopped uses by finding their reaching def.
    // For each unresolved use of register R at PC p, find the latest
    // def of R at PC < p (strict less-than because reads happen before
    // writes within the same instruction).
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

    for use_ref in &unresolved_uses {
        if let Some(defs) = reaching_defs.get(&use_ref.register) {
            // Find the latest def strictly before this use.
            // Strict < because within a single instruction, reads happen
            // before writes (e.g., CALL reads r0 as function then writes r0
            // as result — the use at PC 5 should resolve to def at PC 3).
            let var_id = defs
                .iter()
                .rev()
                .find(|(def_pc, _)| *def_pc < use_ref.pc)
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
