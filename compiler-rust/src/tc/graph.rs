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
    pub fn tag(self) -> u32 {
        self.head & 15
    }
    /// O(1), no allocation.
    pub fn arity(self) -> u32 {
        self.head >> 8
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct Param {
    pub ty: Ty,
    pub label: u32,
    pub loc: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    Success,
    Explain,
}

/// Linear token: close speculations in reverse opening order. The fields
/// are readable inside `tc` so that `unify::Checker::undo_compress` can walk
/// the trail back to `mark` (compiler/ml/btype.ml:792).
#[derive(Debug)]
pub struct Speculation {
    pub(crate) mark: usize,
    pub(crate) depth: usize,
}

#[derive(Clone, Copy)]
#[repr(C)]
pub struct Change {
    pub(crate) ty: Ty,
    pub(crate) before: Node,
}

pub struct Graph {
    pub nodes: Vec<Node>,
    pub lists: Vec<Ty>,
    pub params: Vec<Param>,
    pub level: u32,
    pub mode: Mode,
    pub trail: Vec<Change>,
    pub(crate) speculation_depth: usize,
    pub(crate) work: Vec<Ty>,
    pub(crate) forward: Vec<super::template::Forward>,
    pub(crate) copy_generation: u32,
    /// Instance sources: a variable's name is in the level field, not `a`
    /// (tc/template.rs `descriptor`).
    pub(crate) template_nodes: Vec<Node>,
    pub(crate) template_lists: Vec<Ty>,
    pub(crate) template_params: Vec<Param>,
    pub(crate) template_pools: Vec<super::template::TemplatePools>,
    pub(crate) template_externals: Vec<Ty>,
    pub(crate) instance_externals: Vec<Ty>,
}

impl Default for Graph {
    /// O(1), empty pools allocate nothing.
    fn default() -> Self {
        Self {
            nodes: Vec::new(),
            lists: Vec::new(),
            params: Vec::new(),
            level: 1,
            mode: Mode::Success,
            trail: Vec::new(),
            speculation_depth: 0,
            work: Vec::new(),
            forward: Vec::new(),
            copy_generation: 0,
            template_nodes: Vec::new(),
            template_lists: Vec::new(),
            template_params: Vec::new(),
            template_pools: Vec::new(),
            template_externals: Vec::new(),
            instance_externals: Vec::new(),
        }
    }
}

impl Graph {
    /// O(1): clear plain-data instance pools while retaining their capacity.
    /// Invalidates all local handles and templates with external references;
    /// closed templates remain usable. No speculation may be open.
    pub fn clear_instances(&mut self) {
        assert_eq!(self.speculation_depth, 0, "open speculation at reset");
        self.nodes.clear();
        self.lists.clear();
        self.params.clear();
        self.forward.clear();
        self.work.clear();
        self.instance_externals.clear();
    }

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
            self.trail.push(Change {
                ty,
                before: self.nodes[ty.0 as usize],
            });
        }
        self.nodes[ty.0 as usize] = node;
    }

    /// O(1). Link representatives in the caller's direction. The lower-level
    /// variable's supplied name wins (compiler/ml/btype.ml:713-731).
    pub fn link(&mut self, from: Ty, to: Ty) {
        if from == to {
            return;
        }
        let source = self.nodes[from.0 as usize];
        let target = self.nodes[to.0 as usize];
        self.write(
            from,
            Node {
                head: LINK,
                a: to.0,
                b: 0,
                ..source
            },
        );
        if source.tag() == VAR
            && target.tag() == VAR
            && source.a != NONE
            && (target.a == NONE || source.level < target.level)
        {
            self.write(
                to,
                Node {
                    a: source.a,
                    ..target
                },
            );
        }
    }

    /// O(1), no allocation. Nested keeps remain undoable by their parent.
    pub fn speculate(&mut self) -> Speculation {
        self.speculation_depth += 1;
        Speculation {
            mark: self.trail.len(),
            depth: self.speculation_depth,
        }
    }

    /// O(1), zero node steps; the outermost keep drops the plain-data log.
    pub fn keep(&mut self, token: Speculation) {
        assert_eq!(token.depth, self.speculation_depth, "non-LIFO speculation");
        self.speculation_depth -= 1;
        if self.speculation_depth == 0 {
            self.trail.clear();
        }
    }

    /// O(writes since open), exactly one step per restored node write.
    pub fn restore(&mut self, token: Speculation) {
        assert_eq!(token.depth, self.speculation_depth, "non-LIFO speculation");
        while self.trail.len() > token.mark {
            #[cfg(test)]
            super::steps::tick();
            let change = self.trail.pop().unwrap();
            self.nodes[change.ty.0 as usize] = change.before;
        }
        self.speculation_depth -= 1;
    }

    /// O(links), O(1) stack. Find the representative, then fully compress
    /// the walked path. Count one step per followed link and rewritten node:
    /// at most two per link, one for an already direct link. Writes use the
    /// speculative trail. This preserves compiler/ml/btype.ml's representative.
    #[inline]
    pub fn repr(&mut self, ty: Ty) -> Ty {
        Self::repr_parts(&mut self.nodes, &mut self.trail, self.speculation_depth, ty)
    }

    /// O(links), at most two steps per link. Split borrows let pool iterators
    /// resolve external references without borrowing the entire graph.
    #[inline]
    pub(crate) fn repr_parts(
        nodes: &mut [Node],
        trail: &mut Vec<Change>,
        depth: usize,
        mut ty: Ty,
    ) -> Ty {
        let mut root = ty;
        while nodes[root.0 as usize].tag() == LINK {
            #[cfg(test)]
            super::steps::tick();
            root = Ty(nodes[root.0 as usize].a);
        }
        while ty != root {
            let node = nodes[ty.0 as usize];
            let next = Ty(node.a);
            if next == root {
                break;
            }
            #[cfg(test)]
            super::steps::tick();
            if depth != 0 {
                trail.push(Change { ty, before: node });
            }
            nodes[ty.0 as usize] = Node { a: root.0, ..node };
            ty = next;
        }
        root
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
        for i in 0..10000 {
            g.push(Node {
                head: LINK,
                level: 1,
                a: i + 1,
                b: 0,
            });
        }
        let root = g.push(Node {
            head: VAR,
            level: 1,
            a: NONE,
            b: 0,
        });
        assert_eq!(
            super::super::steps::scope(|| assert_eq!(g.repr(Ty(0)), root)),
            19999
        );
        assert_eq!(
            super::super::steps::scope(|| assert_eq!(g.repr(Ty(0)), root)),
            1
        );
    }
}

#[cfg(test)]
mod trail_tests {
    use super::*;
    #[test]
    fn compression_of_ten_thousand_links_is_undoable() {
        let mut g = Graph::default();
        for i in 0..10000 {
            g.push(Node {
                head: LINK,
                level: 1,
                a: i + 1,
                b: 0,
            });
        }
        let root = g.push(Node {
            head: VAR,
            level: 1,
            a: NONE,
            b: 0,
        });
        let token = g.speculate();
        assert_eq!(
            super::super::steps::scope(|| assert_eq!(g.repr(Ty(0)), root)),
            19999
        );
        assert_eq!(super::super::steps::scope(|| g.restore(token)), 9999);
        for (i, node) in g.nodes[..10000].iter().enumerate() {
            assert_eq!(node.a, i as u32 + 1);
        }
    }
    #[test]
    fn modes_do_not_log_without_explicit_speculation() {
        for mode in [Mode::Success, Mode::Explain] {
            let mut g = Graph {
                mode,
                ..Graph::default()
            };
            assert_eq!(g.mode, mode);
            let ty = g.push(Node {
                head: VAR,
                level: 1,
                a: NONE,
                b: 0,
            });
            g.write(
                ty,
                Node {
                    head: VAR,
                    level: 2,
                    a: NONE,
                    b: 0,
                },
            );
            assert!(g.trail.is_empty());
            let token = g.speculate();
            g.write(
                ty,
                Node {
                    head: VAR,
                    level: 3,
                    a: NONE,
                    b: 0,
                },
            );
            g.restore(token);
            assert_eq!(g.nodes[ty.0 as usize].level, 2);
        }
    }
    #[test]
    fn restore_and_keep_ten_thousand_writes() {
        let mut g = Graph::default();
        let original = Node {
            head: VAR,
            level: 1,
            a: NONE,
            b: 0,
        };
        let ty = g.push(original);
        let outer = g.speculate();
        let inner = g.speculate();
        for i in 0..10000 {
            g.write(
                ty,
                Node {
                    level: i,
                    ..original
                },
            );
        }
        assert_eq!(super::super::steps::scope(|| g.keep(inner)), 0);
        assert_eq!(super::super::steps::scope(|| g.restore(outer)), 10000);
        assert_eq!(g.nodes[0], original);
        let token = g.speculate();
        for i in 0..10000 {
            g.write(
                ty,
                Node {
                    level: i,
                    ..original
                },
            );
        }
        assert_eq!(super::super::steps::scope(|| g.keep(token)), 0);
        assert!(g.trail.is_empty());
        g.write(ty, original);
        assert!(g.trail.is_empty());
    }
    #[test]
    fn names_and_compression_are_restored() {
        let mut g = Graph::default();
        let a = g.push(Node {
            head: VAR,
            level: 1,
            a: 42,
            b: 0,
        });
        let b = g.push(Node {
            head: VAR,
            level: 2,
            a: 43,
            b: 1,
        });
        let c = g.push(Node {
            head: VAR,
            level: 3,
            a: NONE,
            b: 2,
        });
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
