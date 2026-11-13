//! Scheme copies preserve identity through a dense forwarding array.
use super::graph::{ARROW, CONSTR, GENERIC, Graph, NONE, Node, Param, TUPLE, Ty, VAR};

#[derive(Clone, Copy, Default)]
#[repr(C)]
pub(crate) struct Forward {
    pub generation: u32,
    pub target: u32,
}

impl Graph {
    /// O(1) except representative links and amortized arena growth. Allocate
    /// each generic source once; non-generic nodes stay shared. This is the
    /// copy/share decision of compiler/ml/ctype.ml:copy and instance.
    fn copy_ref(&mut self, ty: Ty) -> Ty {
        let ty = self.repr(ty);
        let node = self.nodes[ty.0 as usize];
        if node.level != GENERIC { return ty; }
        let forwarded = self.forward[ty.0 as usize];
        if forwarded.generation == self.copy_generation { return Ty(forwarded.target); }
        #[cfg(test)] super::steps::tick();
        let target = self.push(Node { level: self.level, ..node });
        self.forward[ty.0 as usize] = Forward { generation: self.copy_generation, target: target.0 };
        self.work.push(ty);
        target
    }

    /// O(generic nodes + edges + representative links), O(nodes) reusable
    /// queue space; exactly one node step per copied generic node. Shared
    /// positions remain one node, but different calls allocate different nodes
    /// (compiler/ml/ctype.ml:copy). The generation counter avoids a clearing
    /// pass over the forwarding array. Exhaustion is an explicit error.
    pub fn copy(&mut self, root: Ty) -> Ty {
        self.copy_generation = self.copy_generation.checked_add(1).expect("copy generation exhausted");
        self.work.clear();
        let result = self.copy_ref(root);
        let mut cursor = 0;
        while cursor < self.work.len() {
            let source = self.work[cursor];
            cursor += 1;
            let mut node = self.nodes[source.0 as usize];
            let target = Ty(self.forward[source.0 as usize].target);
            node.level = self.level;
            match node.tag() {
                VAR => {}
                ARROW => {
                    node.a = self.copy_ref(Ty(node.a)).0;
                    let start = self.params.len() as u32;
                    for i in 0..node.arity() {
                        let param = self.params[(node.b + i) as usize];
                        let ty = self.copy_ref(param.ty);
                        self.params.push(Param { ty, ..param });
                    }
                    node.b = start;
                }
                CONSTR | TUPLE => {
                    let old = node.b + u32::from(node.tag() == CONSTR);
                    node.b = self.lists.len() as u32;
                    // Generic constructor copies have a fresh memo, not the
                    // source's memo (compiler/ml/ctype.ml:copy, Tconstr arm).
                    if node.tag() == CONSTR { self.lists.push(Ty(NONE)); }
                    for i in 0..node.arity() {
                        let child = self.lists[(old + i) as usize];
                        let child = self.copy_ref(child);
                        self.lists.push(child);
                    }
                }
                _ => panic!("expected representative descriptor"),
            }
            // Freshly allocated nodes need no undo record: no preexisting
            // node refers to them until the caller publishes the result.
            self.nodes[target.0 as usize] = node;
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::steps;
    #[test]
    fn forwarding_size() { assert_eq!(std::mem::size_of::<Forward>(), 8); }

    #[test]
    fn copy_ten_thousand_nodes_with_shared_positions() {
        std::thread::Builder::new().stack_size(2 * 1024 * 1024).spawn(|| {
            let mut g = Graph::default();
            let mut root = g.push(Node { head: VAR, level: GENERIC, a: NONE, b: 0 });
            for i in 1..10000 {
                let b = g.lists.len() as u32;
                g.lists.push(root);
                let arity = if i % 2 == 1 { g.lists.push(root); 2 } else { 1 };
                root = g.push(Node { head: TUPLE | arity << 8, level: GENERIC, a: 0, b });
            }
            let before = g.nodes.len();
            let mut copied = root;
            assert_eq!(steps::scope(|| copied = g.copy(root)), 10000);
            assert_eq!(g.nodes.len() - before, 10000);
            for node in &g.nodes[before..] {
                if node.arity() == 2 { assert_eq!(g.lists[node.b as usize], g.lists[node.b as usize + 1]); }
            }
            assert_ne!(root, copied);
            assert_ne!(g.copy(root), copied);
            assert_eq!(steps::scope(|| assert_eq!(g.copy(copied), copied)), 0);
        }).unwrap().join().unwrap();
    }
    #[test]
    fn identity_fixtures_2_3_4_7b() {
        let mut g = Graph::default();
        // Fixture 2: annotation generalizes even a ground structure.
        g.begin_def();
        g.lists.push(Ty(NONE));
        let annotated = g.push(Node {head: CONSTR, level: g.level, a: 1, b: 0});
        g.end_def();
        g.generalize_structure(annotated, g.level);
        assert_ne!(g.copy(annotated), g.copy(annotated));
        // Fixture 3: generalized bindings get separate instances.
        g.begin_def();
        let v = g.push(Node {head: VAR, level: g.level, a: NONE, b: 1});
        g.end_def();
        g.generalize(v);
        assert_ne!(g.copy(v), g.copy(v));
        // Fixture 4: a local, non-generalized binding is the same node.
        let local = g.push(Node {head: VAR, level: g.level, a: NONE, b: 2});
        assert_eq!(g.copy(local), local);
        // Fixture 7b: dup shares; independently created equal nodes do not.
        let other = g.push(Node {head: VAR, level: GENERIC, a: NONE, b: 3});
        let b = g.lists.len() as u32;
        g.lists.extend([v, v, v, other, local]);
        let tuple = g.push(Node {head: TUPLE | 5 << 8, level: GENERIC, a: 0, b});
        let out = g.copy(tuple);
        let b = g.nodes[out.0 as usize].b as usize;
        assert_eq!(g.lists[b], g.lists[b+1]);
        assert_eq!(g.lists[b], g.lists[b+2]);
        assert_ne!(g.lists[b+2], g.lists[b+3]);
        assert_eq!(g.lists[b+4], local);
    }
}
