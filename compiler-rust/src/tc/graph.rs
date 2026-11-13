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

/// Linear token: close speculations in reverse opening order.
#[derive(Debug)]
pub struct Speculation { mark: usize, depth: usize }

#[derive(Clone, Copy)]
#[repr(C)]
pub struct Change { ty: Ty, before: Node }

pub struct Graph {
    pub nodes: Vec<Node>,
    pub lists: Vec<Ty>,
    pub params: Vec<Param>,
    pub level: u32,
    pub mode: Mode,
    pub trail: Vec<Change>,
    speculation_depth: usize,
}

impl Default for Graph {
    /// O(1), empty pools allocate nothing.
    fn default() -> Self {
        Self { nodes: Vec::new(), lists: Vec::new(), params: Vec::new(), level: 1, mode: Mode::Success, trail: Vec::new(), speculation_depth: 0 }
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

    /// Amortized O(1). Only speculative writes append a 20-byte undo entry.
    pub fn write(&mut self, ty: Ty, node: Node) {
        if self.speculation_depth != 0 {
            self.trail.push(Change { ty, before: self.nodes[ty.0 as usize] });
        }
        self.nodes[ty.0 as usize] = node;
    }

    /// O(1). Link representatives in the caller's direction. The lower-level
    /// variable's supplied name wins (compiler/ml/btype.ml:713-731).
    pub fn link(&mut self, from: Ty, to: Ty) {
        if from == to { return; }
        let source = self.nodes[from.0 as usize];
        let target = self.nodes[to.0 as usize];
        self.write(from, Node { head: LINK, a: to.0, b: 0, ..source });
        if source.tag() == VAR && target.tag() == VAR && source.a != NONE
            && (target.a == NONE || source.level < target.level) {
            self.write(to, Node { a: source.a, ..target });
        }
    }

    /// O(1), no allocation. Nested keeps remain undoable by their parent.
    pub fn speculate(&mut self) -> Speculation {
        self.speculation_depth += 1;
        Speculation { mark: self.trail.len(), depth: self.speculation_depth }
    }

    /// O(1), zero node steps; the outermost keep drops the plain-data log.
    pub fn keep(&mut self, token: Speculation) {
        assert_eq!(token.depth, self.speculation_depth, "non-LIFO speculation");
        self.speculation_depth -= 1;
        if self.speculation_depth == 0 { self.trail.clear(); }
    }

    /// O(writes since open), exactly one step per restored node write.
    pub fn restore(&mut self, token: Speculation) {
        assert_eq!(token.depth, self.speculation_depth, "non-LIFO speculation");
        while self.trail.len() > token.mark {
            #[cfg(test)] super::steps::tick();
            let change = self.trail.pop().unwrap();
            self.nodes[change.ty.0 as usize] = change.before;
        }
        self.speculation_depth -= 1;
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
                self.write(ty, Node { a: after.a, ..node });
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
        assert_eq!(std::mem::size_of::<Change>(), 20);
        assert_eq!(std::mem::size_of::<Speculation>(), 16);
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

#[cfg(test)]
mod trail_tests {
    use super::*;
    #[test]
    fn restore_and_keep_ten_thousand_writes() {
        let mut g = Graph::default();
        let original = Node { head: VAR, level: 1, a: NONE, b: 0 };
        let ty = g.push(original);
        let outer = g.speculate();
        let inner = g.speculate();
        for i in 0..10000 { g.write(ty, Node { level: i, ..original }); }
        assert_eq!(super::super::steps::scope(|| g.keep(inner)), 0);
        assert_eq!(super::super::steps::scope(|| g.restore(outer)), 10000);
        assert_eq!(g.nodes[0], original);
        let token = g.speculate();
        for i in 0..10000 { g.write(ty, Node { level: i, ..original }); }
        assert_eq!(super::super::steps::scope(|| g.keep(token)), 0);
        assert!(g.trail.is_empty());
        g.write(ty, original);
        assert!(g.trail.is_empty());
    }
    #[test]
    fn names_and_compression_are_restored() {
        let mut g = Graph::default();
        let a = g.push(Node { head: VAR, level: 1, a: 42, b: 0 });
        let b = g.push(Node { head: VAR, level: 2, a: 43, b: 1 });
        let c = g.push(Node { head: VAR, level: 3, a: NONE, b: 2 });
        let before = g.nodes.clone();
        let token = g.speculate();
        g.link(a, b);
        assert_eq!(g.nodes[1].a, 42);
        g.link(b, c);
        assert_eq!(g.nodes[2].a, 42);
        assert_eq!(g.repr(a), c);
        g.restore(token);
        assert_eq!(g.nodes, before);
    }
}
