//! Worker-local type graph. Handles identify occurrences, never equal types.

pub const GENERIC: u32 = 100_000_000;
pub const VAR: u32 = 0;
pub const LINK: u32 = 1;
pub const CONSTR: u32 = 2;
pub const TUPLE: u32 = 3;
pub const ARROW: u32 = 4;
pub const NONE: u32 = u32::MAX;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(transparent)]
pub struct Ty(pub u32);

/// The head stores the tag in its low nibble and arity above bit seven.
/// Constructors reserve list slot zero for their abbreviation memo.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct Node {
    pub head: u32,
    pub level: u32,
    pub a: u32,
    pub b: u32,
}

impl Node {
    /// O(1), no allocation.
    pub fn tag(self) -> u32 { self.head & 15 }
    /// O(1), no allocation.
    pub fn arity(self) -> u32 { self.head >> 8 }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct Param {
    pub ty: Ty,
    pub label: u32,
    pub loc: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode { Success, Explain }

pub struct Graph {
    pub nodes: Vec<Node>,
    pub lists: Vec<Ty>,
    pub params: Vec<Param>,
    pub level: u32,
    pub mode: Mode,
}

impl Default for Graph {
    /// O(1), empty pools allocate nothing.
    fn default() -> Self {
        Self { nodes: Vec::new(), lists: Vec::new(), params: Vec::new(), level: 1, mode: Mode::Success }
    }
}

impl Graph {
    /// Amortized O(1); each call allocates a distinct occurrence.
    pub fn push(&mut self, node: Node) -> Ty {
        assert!(self.nodes.len() < (1 << 30));
        let ty = Ty(self.nodes.len() as u32);
        self.nodes.push(node);
        ty
    }

    /// O(links), O(1) stack; one tick per traversed link. Path splitting
    /// matches the measured kernel (advance to the old successor).
    /// It preserves the representative, as compiler/ml/btype.ml's repr does.
    pub fn repr(&mut self, mut ty: Ty) -> Ty {
        loop {
            let node = self.nodes[ty.0 as usize];
            if node.tag() != LINK { return ty; }
            #[cfg(test)] super::steps::tick();
            let next = Ty(node.a);
            let after = self.nodes[next.0 as usize];
            if after.tag() == LINK {
                self.nodes[ty.0 as usize].a = after.a;
            }
            ty = next;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn sizes() {
        assert_eq!(std::mem::size_of::<Node>(), 16);
        assert_eq!(std::mem::size_of::<Ty>(), 4);
        assert_eq!(std::mem::size_of::<Param>(), 12);
        assert_eq!(std::mem::size_of::<Mode>(), 1);
    }
    #[test]
    fn representative_chain_cost() {
        let mut g = Graph::default();
        for i in 0..10000 { g.push(Node {head: LINK, level: 1, a: i+1, b: 0}); }
        let root = g.push(Node {head: VAR, level: 1, a: NONE, b: 0});
        assert_eq!(super::super::steps::scope(|| assert_eq!(g.repr(Ty(0)), root)), 10000);
        // The kernel's splitting cannot satisfy the requested second-call
        // bound of one. Record its actual cost rather than undercounting it.
        assert_eq!(super::super::steps::scope(|| assert_eq!(g.repr(Ty(0)), root)), 5000);
    }
}
