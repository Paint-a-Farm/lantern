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
    if accesses.is_empty() {
        return;
    }

    // Phase 1: Group accesses by register
    let mut by_register: FxHashMap<u8, Vec<&RegAccess>> = FxHashMap::default();
    for access in &accesses {
        by_register
            .entry(access.reg.register)
            .or_default()
            .push(access);
    }

    // Phase 2: For each register, partition accesses into variables using scopes.
    //
    // Approach: accesses that share a scope are the same variable. Accesses in
    // non-overlapping scopes are different variables. Accesses with no scope info
    // are assigned based on domination (which def reaches this use).
    //
    // For now: simple scope-based partitioning. Each unique scope interval becomes
    // one variable. Accesses with no scope become separate unnamed temporaries.
    let mut reg_pc_to_var: FxHashMap<RegRef, VarId> = FxHashMap::default();

    // Create parameter variables first (r0..r{num_params-1})
    for i in 0..num_params {
        let name = scopes.lookup(i, 0).map(|s| s.to_string());
        let mut info = VarInfo::new();
        info.name = name;
        info.is_param = true;
        let var_id = func.vars.alloc(info);
        // Bind all accesses to this param register that fall within its scope
        if let Some(reg_accesses) = by_register.get(&i) {
            for access in reg_accesses {
                let scope_name = scopes.lookup(i, access.reg.pc);
                let param_name = scopes.lookup(i, 0);
                if scope_name == param_name && param_name.is_some() {
                    reg_pc_to_var.insert(access.reg, var_id);
                }
            }
        }
    }

    // Phase 3: For each register, create variables from scope partitioning
    for (&register, reg_accesses) in &by_register {
        // Group by scope: accesses in the same scope → same variable
        // We use (register, scope_name, scope_start) as the grouping key
        let mut scope_vars: FxHashMap<(u8, String, usize), VarId> = FxHashMap::default();

        for access in reg_accesses {
            if reg_pc_to_var.contains_key(&access.reg) {
                continue; // Already bound (e.g., parameter)
            }

            if let Some(scope) = find_scope(scopes, register, access.reg.pc) {
                let key = (register, scope.0.to_string(), scope.1);
                let var_id = *scope_vars.entry(key).or_insert_with(|| {
                    let mut info = VarInfo::new();
                    info.name = Some(scope.0.to_string());
                    if access.is_def {
                        info.def_pcs.push(access.reg.pc);
                    } else {
                        info.use_pcs.push(access.reg.pc);
                    }
                    func.vars.alloc(info)
                });

                // Record def/use on existing variable
                if scope_vars.contains_key(&(register, scope.0.to_string(), scope.1)) {
                    let info = func.vars.get_mut(var_id);
                    if access.is_def {
                        if !info.def_pcs.contains(&access.reg.pc) {
                            info.def_pcs.push(access.reg.pc);
                        }
                    } else if !info.use_pcs.contains(&access.reg.pc) {
                        info.use_pcs.push(access.reg.pc);
                    }
                }

                reg_pc_to_var.insert(access.reg, var_id);
            } else {
                // No scope info — create a temporary per-def
                // For uses without a preceding def in scope, create unnamed temp
                if access.is_def {
                    let mut info = VarInfo::new();
                    info.def_pcs.push(access.reg.pc);
                    let var_id = func.vars.alloc(info);
                    reg_pc_to_var.insert(access.reg, var_id);
                }
                // Uses without scope: try to find a preceding def for this register
                // by walking backwards through PCs
                // For now, leave unresolved — they'll remain as RegRef in output
            }
        }
    }

    // Phase 4: Resolve unscopped uses by finding their reaching def.
    // Simple approach: for each unresolved use of register R at PC p,
    // find the latest def of R at PC < p that has the same register.
    let mut unresolved_uses: Vec<RegRef> = Vec::new();
    for access in &accesses {
        if !access.is_def && !reg_pc_to_var.contains_key(&access.reg) {
            unresolved_uses.push(access.reg);
        }
    }

    // Build def map: register → sorted list of (pc, var_id)
    let mut def_map: FxHashMap<u8, Vec<(usize, VarId)>> = FxHashMap::default();
    for access in &accesses {
        if access.is_def {
            if let Some(&var_id) = reg_pc_to_var.get(&access.reg) {
                def_map
                    .entry(access.reg.register)
                    .or_default()
                    .push((access.reg.pc, var_id));
            }
        }
    }
    for defs in def_map.values_mut() {
        defs.sort_by_key(|(pc, _)| *pc);
    }

    for use_ref in &unresolved_uses {
        if let Some(defs) = def_map.get(&use_ref.register) {
            // Find the latest def before this use
            let var_id = defs
                .iter()
                .rev()
                .find(|(def_pc, _)| *def_pc <= use_ref.pc)
                .map(|(_, vid)| *vid);
            if let Some(vid) = var_id {
                reg_pc_to_var.insert(*use_ref, vid);
            }
        }
    }

    // Phase 5: Rewrite the HIR — replace RegRef with VarId
    rewrite_func(func, &reg_pc_to_var);
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

/// Rewrite all RegRef in the HIR to VarId using the resolved mapping.
fn rewrite_func(func: &mut HirFunc, mapping: &FxHashMap<RegRef, VarId>) {
    // Rewrite expressions
    let expr_count = func.exprs.len();
    for i in 0..expr_count {
        let expr_id = lantern_hir::arena::ExprId(i as u32);
        let expr = func.exprs.get(expr_id).clone();
        match expr {
            HirExpr::Reg(reg) => {
                if let Some(&var_id) = mapping.get(&reg) {
                    func.exprs.replace(expr_id, HirExpr::Var(var_id));
                }
            }
            HirExpr::Closure { proto_id, ref captures } => {
                let new_captures: Vec<_> = captures
                    .iter()
                    .map(|cap| {
                        let new_source = match &cap.source {
                            CaptureSource::Register(reg) => {
                                if let Some(&var_id) = mapping.get(reg) {
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

    // Rewrite statements block by block
    for node_idx in func.cfg.node_indices().collect::<Vec<_>>() {
        let stmts = std::mem::take(&mut func.cfg[node_idx].stmts);
        let new_stmts: Vec<HirStmt> = stmts
            .into_iter()
            .map(|stmt| rewrite_stmt(stmt, mapping))
            .collect();
        func.cfg[node_idx].stmts = new_stmts;
    }
}

fn rewrite_stmt(stmt: HirStmt, mapping: &FxHashMap<RegRef, VarId>) -> HirStmt {
    match stmt {
        HirStmt::RegAssign { target, value } => {
            if let Some(&var_id) = mapping.get(&target) {
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
