//! Level walks use the graph's reusable explicit stack, not the machine stack.
use super::graph::{ARROW, CONSTR, GENERIC, Graph, NONE, Node, Ty, VAR};

impl Graph {
    /// O(1). The current level is raised at definition entry
    /// (compiler/ml/ctype.ml:146); no node's level is cached elsewhere.
    pub fn begin_def(&mut self) { self.level += 1; }

    /// O(1). Restore the immediately enclosing definition's level
    /// (compiler/ml/ctype.ml:151). Definition entries and exits must balance.
    pub fn end_def(&mut self) {
        assert!(self.level > 1, "unbalanced definition exit");
        self.level -= 1;
    }

    /// O(arity), one push per edge, no allocation per node. With `memo`,
    /// also visit the constructor abbreviation memo, as generalize does.
    pub(crate) fn children(&mut self, node: Node, memo: bool) {
        match node.tag() {
            VAR => {}
            ARROW => {
                self.work.push(Ty(node.a));
                for i in 0..node.arity() {
                    self.work.push(self.params[(node.b + i) as usize].ty);
                }
            }
            CONSTR => {
                if memo {
                    let ty = self.lists[node.b as usize];
                    if ty.0 != NONE { self.work.push(ty); }
                }
                for i in 0..node.arity() {
                    self.work.push(self.lists[(node.b + 1 + i) as usize]);
                }
            }
            super::graph::TUPLE => {
                for i in 0..node.arity() {
                    self.work.push(self.lists[(node.b + i) as usize]);
                }
            }
            _ => panic!("expected representative descriptor"),
        }
    }

    /// O(reachable nodes above target + their edges + representative links).
    /// One step for a pruned root. Levels are written even on ground types:
    /// compiler/ml/ctype.ml:584, update_level. Scope checks belong to R3.
    pub fn lower(&mut self, root: Ty, level: u32) {
        assert_ne!(level, GENERIC);
        self.work.clear();
        self.work.push(root);
        while let Some(ty) = self.work.pop() {
            let ty = self.repr(ty);
            #[cfg(test)] super::steps::tick();
            let node = self.nodes[ty.0 as usize];
            if node.level <= level { continue; }
            self.write(ty, Node { level, ..node });
            self.children(node, false);
        }
    }

    /// O(nodes above current level + their edges + representative links).
    /// One node step per changed node; already generic roots cost zero steps.
    /// Every structure node is generalized too (compiler/ml/ctype.ml:509).
    pub fn generalize(&mut self, root: Ty) {
        self.work.clear();
        self.work.push(root);
        while let Some(ty) = self.work.pop() {
            let ty = self.repr(ty);
            let node = self.nodes[ty.0 as usize];
            if node.level <= self.level || node.level == GENERIC { continue; }
            #[cfg(test)] super::steps::tick();
            self.write(ty, Node { level: GENERIC, ..node });
            self.children(node, true);
        }
    }

    /// O(visited structure nodes + edges + representative links). Generalize
    /// structures but lower variables, compiler/ml/ctype.ml:524-540. Object
    /// paths are not represented by this slice. Clear constructor memos.
    pub fn generalize_structure(&mut self, root: Ty, var_level: u32) {
        self.work.clear();
        self.work.push(root);
        while let Some(ty) = self.work.pop() {
            let ty = self.repr(ty);
            let node = self.nodes[ty.0 as usize];
            if node.level == GENERIC { continue; }
            if node.tag() == VAR && node.level > var_level {
                #[cfg(test)] super::steps::tick();
                self.write(ty, Node { level: var_level, ..node });
            } else if node.level > self.level {
                #[cfg(test)] super::steps::tick();
                // Allocate a replacement list rather than mutate a slot, so
                // the node trail restores the old memo on speculation undo.
                let mut generalized = Node { level: GENERIC, ..node };
                if node.tag() == CONSTR && self.lists[node.b as usize].0 != NONE {
                    generalized.b = self.lists.len() as u32;
                    self.lists.push(Ty(NONE));
                    for i in 0..node.arity() {
                        let child = self.lists[(node.b + i + 1) as usize];
                        self.lists.push(child);
                    }
                }
                self.write(ty, generalized);
                self.children(node, false);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::{graph::TUPLE, steps};

    pub(super) fn chain(g: &mut Graph, n: u32) -> Ty {
        let mut ty = g.push(Node {head: VAR, level: g.level, a: NONE, b: 0});
        for _ in 1..n {
            let b = g.lists.len() as u32;
            g.lists.push(ty);
            ty = g.push(Node {head: TUPLE | 1 << 8, level: g.level, a: 0, b});
        }
        ty
    }
    #[test]
    fn ten_thousand_deep_on_two_mb_stack() {
        std::thread::Builder::new().stack_size(2 * 1024 * 1024).spawn(|| {
            let mut g = Graph::default();
            g.begin_def();
            let root = chain(&mut g, 10000);
            assert_eq!(steps::scope(|| g.lower(root, 2)), 1);
            g.end_def();
            assert_eq!(steps::scope(|| g.generalize(root)), 10000);
            assert_eq!(steps::scope(|| g.generalize(root)), 0);
            assert!(g.nodes.iter().all(|n| n.level == GENERIC));
            assert_eq!(steps::scope(|| g.lower(root, 1)), 10000);
            assert!(g.nodes.iter().all(|n| n.level == 1));
        }).unwrap().join().unwrap();
    }
    #[test]
    fn structure_generalization_keeps_variable_local() {
        let mut g = Graph::default();
        g.begin_def();
        let root = chain(&mut g, 10000);
        g.end_def();
        assert_eq!(steps::scope(|| g.generalize_structure(root, 1)), 10000);
        assert_eq!(g.nodes[0].level, 1);
        assert!(g.nodes[1..].iter().all(|n| n.level == GENERIC));
        assert_eq!(steps::scope(|| g.generalize_structure(root, 1)), 0);
    }
    #[test]
    fn wide_children_are_linear() {
        let mut g = Graph::default();
        for i in 0..10000 {
            let t = g.push(Node { head: VAR, level: 2, a: NONE, b: i });
            g.lists.push(t);
        }
        let root = g.push(Node { head: TUPLE | 10000 << 8, level: 2, a: 0, b: 0 });
        assert_eq!(steps::scope(|| g.lower(root, 1)), 10001);
    }
}
