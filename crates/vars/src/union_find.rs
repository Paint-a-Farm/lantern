/// Weighted quick-union with path compression.
///
/// Each element starts in its own set. merge() unites two sets.
/// find() returns the canonical representative with path compression.
#[allow(dead_code)]
pub struct UnionFind {
    parent: Vec<usize>,
    rank: Vec<u8>,
}

#[allow(dead_code)]
impl UnionFind {
    pub fn new(n: usize) -> Self {
        Self {
            parent: (0..n).collect(),
            rank: vec![0; n],
        }
    }

    /// Find the canonical representative of element `x`.
    pub fn find(&mut self, x: usize) -> usize {
        if self.parent[x] != x {
            self.parent[x] = self.find(self.parent[x]);
        }
        self.parent[x]
    }

    /// Merge the sets containing `x` and `y`.
    /// Returns true if they were in different sets (actually merged).
    pub fn merge(&mut self, x: usize, y: usize) -> bool {
        let rx = self.find(x);
        let ry = self.find(y);
        if rx == ry {
            return false;
        }
        // Union by rank
        match self.rank[rx].cmp(&self.rank[ry]) {
            std::cmp::Ordering::Less => self.parent[rx] = ry,
            std::cmp::Ordering::Greater => self.parent[ry] = rx,
            std::cmp::Ordering::Equal => {
                self.parent[ry] = rx;
                self.rank[rx] += 1;
            }
        }
        true
    }

    /// Check if two elements are in the same set.
    pub fn connected(&mut self, x: usize, y: usize) -> bool {
        self.find(x) == self.find(y)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic() {
        let mut uf = UnionFind::new(5);
        assert!(!uf.connected(0, 1));
        uf.merge(0, 1);
        assert!(uf.connected(0, 1));
        assert!(!uf.connected(0, 2));
        uf.merge(1, 2);
        assert!(uf.connected(0, 2));
    }
}
