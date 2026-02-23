use std::ops::Range;

use rustc_hash::FxHashMap;

/// Opaque variable identifier. Index into VarTable.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct VarId(pub u32);

/// A raw register reference before variable recovery.
/// Carries the bytecode PC where this access occurs so the
/// constraint solver can look up the correct debug scope.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RegRef {
    pub register: u8,
    pub pc: usize,
    /// True if this instruction has an AUX word (occupies 2 PC slots).
    /// The debug scope for such instructions starts at pc+2, not pc+1.
    pub has_aux: bool,
}

/// Metadata about a single variable after recovery.
#[derive(Debug, Clone)]
pub struct VarInfo {
    /// Debug name from bytecode (if available).
    pub name: Option<String>,
    /// Whether this is a function parameter.
    pub is_param: bool,
    /// Whether this is a for-loop control variable.
    pub is_loop_var: bool,
    /// Bytecode PCs where this variable is defined (written).
    pub def_pcs: Vec<usize>,
    /// Bytecode PCs where this variable is used (read).
    pub use_pcs: Vec<usize>,
    /// Debug scope PC ranges from bytecode that this variable covers.
    ///
    /// For most variables this is a single range. For variables that span
    /// multiple non-overlapping if-branches, the Luau compiler emits separate
    /// scope entries that are merged into one VarId — all ranges are stored.
    ///
    /// This is the definitive source of truth for scoping: the VM knows exactly
    /// which register holds which variable at every PC via these ranges.
    pub scope_pcs: Vec<Range<usize>>,
    /// The bytecode PC of the def that initializes this variable's scope
    /// (the `local x = ...` point). This is the def at `scope_start - 1`
    /// (or `scope_start - 2` for AUX instructions). Only the FIRST scope's
    /// initializer is stored — later branch defs are reassignments.
    ///
    /// When set, the rewrite phase emits this def as `LocalDecl` and all
    /// other defs as `Assign`.
    pub decl_pc: Option<usize>,
}

impl VarInfo {
    pub fn new() -> Self {
        Self {
            name: None,
            is_param: false,
            is_loop_var: false,
            def_pcs: Vec::new(),
            use_pcs: Vec::new(),
            scope_pcs: Vec::new(),
            decl_pc: None,
        }
    }

    /// The earliest scope start PC, if any scope ranges are recorded.
    pub fn earliest_scope_start(&self) -> Option<usize> {
        self.scope_pcs.iter().map(|r| r.start).min()
    }

    /// Check if a PC falls within any of this variable's scope ranges.
    pub fn pc_in_scope(&self, pc: usize) -> bool {
        self.scope_pcs.iter().any(|r| r.start <= pc && pc < r.end)
    }

    /// True if this variable has no debug name — likely a compiler temporary.
    pub fn is_temporary(&self) -> bool {
        self.name.is_none() && !self.is_param && !self.is_loop_var
    }

    /// Display name: debug name if available, else _v{id}.
    /// Lua/Luau keywords are prefixed with `_` to avoid syntax errors.
    pub fn display_name(&self, id: VarId) -> String {
        match &self.name {
            Some(n) => {
                if is_luau_keyword(n) {
                    format!("_{}", n)
                } else {
                    n.clone()
                }
            }
            None => format!("_v{}", id.0),
        }
    }
}

fn is_luau_keyword(s: &str) -> bool {
    // Note: `continue` is intentionally excluded — Luau treats it as a
    // context-sensitive keyword, so it is valid as a variable name.
    matches!(
        s,
        "and"
            | "break"
            | "do"
            | "else"
            | "elseif"
            | "end"
            | "false"
            | "for"
            | "function"
            | "if"
            | "in"
            | "local"
            | "nil"
            | "not"
            | "or"
            | "repeat"
            | "return"
            | "then"
            | "true"
            | "until"
            | "while"
    )
}

/// Table of all variables in a function.
///
/// Variables are created by the constraint solver from register accesses.
/// Each VarId maps to exactly one VarInfo.
#[derive(Debug, Clone)]
pub struct VarTable {
    vars: Vec<VarInfo>,
    /// Reverse map: which VarId was assigned to each (register, pc) pair.
    reg_map: FxHashMap<RegRef, VarId>,
}

impl VarTable {
    pub fn new() -> Self {
        Self {
            vars: Vec::new(),
            reg_map: FxHashMap::default(),
        }
    }

    /// Allocate a new variable.
    pub fn alloc(&mut self, info: VarInfo) -> VarId {
        let id = VarId(self.vars.len() as u32);
        self.vars.push(info);
        id
    }

    /// Get variable info by id.
    pub fn get(&self, id: VarId) -> &VarInfo {
        &self.vars[id.0 as usize]
    }

    /// Get mutable variable info by id.
    pub fn get_mut(&mut self, id: VarId) -> &mut VarInfo {
        &mut self.vars[id.0 as usize]
    }

    /// Map a register access to a variable.
    pub fn bind_reg(&mut self, reg: RegRef, var: VarId) {
        self.reg_map.insert(reg, var);
    }

    /// Look up which variable a register access maps to.
    pub fn lookup_reg(&self, reg: &RegRef) -> Option<VarId> {
        self.reg_map.get(reg).copied()
    }

    /// Iterate all variables.
    pub fn iter(&self) -> impl Iterator<Item = (VarId, &VarInfo)> {
        self.vars
            .iter()
            .enumerate()
            .map(|(i, v)| (VarId(i as u32), v))
    }

    /// Iterate all temporary variables.
    pub fn temporaries(&self) -> impl Iterator<Item = VarId> + '_ {
        self.vars
            .iter()
            .enumerate()
            .filter(|(_, v)| v.is_temporary())
            .map(|(i, _)| VarId(i as u32))
    }

    /// Number of variables.
    pub fn len(&self) -> usize {
        self.vars.len()
    }

    pub fn is_empty(&self) -> bool {
        self.vars.is_empty()
    }
}
