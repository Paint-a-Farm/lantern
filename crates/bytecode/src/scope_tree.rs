use std::ops::Range;

/// A local variable scope from bytecode debug info.
#[derive(Debug, Clone)]
pub struct LocalScope {
    pub register: u8,
    pub name: String,
    /// PC range where this variable is in scope: [start, end).
    pub pc_range: Range<usize>,
}

/// Interval-based lookup for register-to-variable-name mapping.
///
/// Replaces medal's `SCOPE_EXTENSION: usize = 5` hack with proper interval
/// queries. The lifter provides exact PCs, so no extension is needed.
#[derive(Debug, Clone, Default)]
pub struct ScopeTree {
    /// Sorted by (register, start_pc) for efficient lookup.
    scopes: Vec<LocalScope>,
}

impl ScopeTree {
    /// Build a ScopeTree from debug info entries.
    pub fn new(mut scopes: Vec<LocalScope>) -> Self {
        scopes.sort_by_key(|s| (s.register, s.pc_range.start));
        Self { scopes }
    }

    /// Look up the variable name for a register at an exact PC.
    ///
    /// Returns the narrowest enclosing scope (largest start_pc that contains
    /// this PC). No scope extension hack needed.
    pub fn lookup(&self, register: u8, pc: usize) -> Option<&str> {
        self.scopes
            .iter()
            .filter(|s| s.register == register && s.pc_range.start <= pc && pc < s.pc_range.end)
            .max_by_key(|s| s.pc_range.start)
            .map(|s| s.name.as_str())
    }

    /// Check if two PCs on the same register refer to the same source variable.
    ///
    /// Two accesses are "same variable" if they share an overlapping scope with
    /// the same name. This is a hard constraint for the variable recovery solver.
    pub fn same_variable(&self, register: u8, pc_a: usize, pc_b: usize) -> bool {
        match (self.lookup(register, pc_a), self.lookup(register, pc_b)) {
            (Some(a), Some(b)) => std::ptr::eq(a, b) || a == b,
            _ => false,
        }
    }

    /// Check if two PCs on the same register are in different scopes.
    ///
    /// This generates MustNotAlias constraints: if both PCs have names but
    /// from non-overlapping scopes, they are definitely different variables.
    pub fn different_variable(&self, register: u8, pc_a: usize, pc_b: usize) -> bool {
        let scope_a = self.scope_for(register, pc_a);
        let scope_b = self.scope_for(register, pc_b);

        match (scope_a, scope_b) {
            (Some(a), Some(b)) => {
                // Different scopes (non-overlapping ranges) = different variables
                !ranges_overlap(&a.pc_range, &b.pc_range)
            }
            // If either has no scope info, we can't determine
            _ => false,
        }
    }

    /// Get the scope entry for a register at a PC.
    fn scope_for(&self, register: u8, pc: usize) -> Option<&LocalScope> {
        self.scopes
            .iter()
            .filter(|s| s.register == register && s.pc_range.start <= pc && pc < s.pc_range.end)
            .max_by_key(|s| s.pc_range.start)
    }

    /// Get all scopes for a given register.
    pub fn scopes_for_register(&self, register: u8) -> impl Iterator<Item = &LocalScope> {
        self.scopes.iter().filter(move |s| s.register == register)
    }

    /// Get all scopes.
    pub fn all_scopes(&self) -> &[LocalScope] {
        &self.scopes
    }
}

fn ranges_overlap(a: &Range<usize>, b: &Range<usize>) -> bool {
    a.start < b.end && b.start < a.end
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lookup_basic() {
        let tree = ScopeTree::new(vec![
            LocalScope {
                register: 5,
                name: "kioskMode".into(),
                pc_range: 10..20,
            },
            LocalScope {
                register: 5,
                name: "kioskMode".into(),
                pc_range: 25..50,
            },
        ]);

        assert_eq!(tree.lookup(5, 15), Some("kioskMode"));
        assert_eq!(tree.lookup(5, 30), Some("kioskMode"));
        assert_eq!(tree.lookup(5, 22), None); // between scopes
    }

    #[test]
    fn test_different_variable() {
        let tree = ScopeTree::new(vec![
            LocalScope {
                register: 5,
                name: "kioskMode".into(),
                pc_range: 10..20,
            },
            LocalScope {
                register: 5,
                name: "kioskMode".into(),
                pc_range: 25..50,
            },
        ]);

        // Same register, non-overlapping scopes = different variables
        assert!(tree.different_variable(5, 15, 30));
        // Within same scope = not different
        assert!(!tree.different_variable(5, 26, 30));
    }
}
