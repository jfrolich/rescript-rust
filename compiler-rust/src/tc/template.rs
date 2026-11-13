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
        if node.level != GENERIC {
            return ty;
        }
        let forwarded = self.forward[ty.0 as usize];
        if forwarded.generation == self.copy_generation {
            return Ty(forwarded.target);
        }
        #[cfg(test)]
        super::steps::tick();
        let target = self.push(Node {
            level: self.level,
            ..node
        });
        self.forward[ty.0 as usize] = Forward {
            generation: self.copy_generation,
            target: target.0,
        };
        self.work.push(ty);
        target
    }

    /// O(generic nodes + edges + representative links), O(nodes) reusable
    /// queue space; exactly one node step per copied generic node. Shared
    /// positions remain one node, but different calls allocate different nodes
    /// (compiler/ml/ctype.ml:copy). The generation counter avoids a clearing
    /// pass over the forwarding array. Exhaustion is an explicit error.
    pub fn copy(&mut self, root: Ty) -> Ty {
        self.copy_generation = self
            .copy_generation
            .checked_add(1)
            .expect("copy generation exhausted");
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
                    if node.tag() == CONSTR {
                        self.lists.push(Ty(NONE));
                    }
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
    use super::super::steps;
    use super::*;
    #[test]
    fn forwarding_size() {
        assert_eq!(std::mem::size_of::<Forward>(), 8);
    }

    #[test]
    fn copy_ten_thousand_nodes_with_shared_positions() {
        std::thread::Builder::new()
            .stack_size(2 * 1024 * 1024)
            .spawn(|| {
                let mut g = Graph::default();
                let mut root = g.push(Node {
                    head: VAR,
                    level: GENERIC,
                    a: NONE,
                    b: 0,
                });
                for i in 1..10000 {
                    let b = g.lists.len() as u32;
                    g.lists.push(root);
                    let arity = if i % 2 == 1 {
                        g.lists.push(root);
                        2
                    } else {
                        1
                    };
                    root = g.push(Node {
                        head: TUPLE | arity << 8,
                        level: GENERIC,
                        a: 0,
                        b,
                    });
                }
                let before = g.nodes.len();
                let mut copied = root;
                assert_eq!(steps::scope(|| copied = g.copy(root)), 10000);
                assert_eq!(g.nodes.len() - before, 10000);
                for node in &g.nodes[before..] {
                    if node.arity() == 2 {
                        assert_eq!(g.lists[node.b as usize], g.lists[node.b as usize + 1]);
                    }
                }
                assert_ne!(root, copied);
                assert_ne!(g.copy(root), copied);
                assert_eq!(steps::scope(|| assert_eq!(g.copy(copied), copied)), 0);
            })
            .unwrap()
            .join()
            .unwrap();
    }
    #[test]
    fn identity_fixtures_2_3_4_7b() {
        let mut g = Graph::default();
        // Fixture 2: annotation generalizes even a ground structure.
        g.begin_def();
        g.lists.push(Ty(NONE));
        let annotated = g.push(Node {
            head: CONSTR,
            level: g.level,
            a: 1,
            b: 0,
        });
        g.end_def();
        g.generalize_structure(annotated, g.level);
        assert_ne!(g.copy(annotated), g.copy(annotated));
        // Fixture 3: generalized bindings get separate instances.
        g.begin_def();
        let v = g.push(Node {
            head: VAR,
            level: g.level,
            a: NONE,
            b: 1,
        });
        g.end_def();
        g.generalize(v);
        assert_ne!(g.copy(v), g.copy(v));
        // Fixture 4: a local, non-generalized binding is the same node.
        let local = g.push(Node {
            head: VAR,
            level: g.level,
            a: NONE,
            b: 2,
        });
        assert_eq!(g.copy(local), local);
        // Fixture 7b: dup shares; independently created equal nodes do not.
        let other = g.push(Node {
            head: VAR,
            level: GENERIC,
            a: NONE,
            b: 3,
        });
        let b = g.lists.len() as u32;
        g.lists.extend([v, v, v, other, local]);
        let tuple = g.push(Node {
            head: TUPLE | 5 << 8,
            level: GENERIC,
            a: 0,
            b,
        });
        let out = g.copy(tuple);
        let b = g.nodes[out.0 as usize].b as usize;
        assert_eq!(g.lists[b], g.lists[b + 1]);
        assert_eq!(g.lists[b], g.lists[b + 2]);
        assert_ne!(g.lists[b + 2], g.lists[b + 3]);
        assert_eq!(g.lists[b + 4], local);
    }
}

/// The kernel's four-word range shape avoids a 65,535-node scheme limit.
/// References use bit 30 for instance-relative indices; bit 31 stays reserved
/// for frozen handles. A zero-node template holds an external root in nodes.
#[derive(Clone, Copy, Debug)]
#[repr(C)]
pub struct Template {
    pub nodes: u32,
    pub node_len: u32,
    pub lists: u32,
    pub list_len: u32,
}

const RELATIVE: u32 = 1 << 30;

impl Graph {
    /// O(1) plus representative links and amortized arena growth. Assign the
    /// relative reference at first encounter, preserving source sharing.
    fn capture_ref(&mut self, ty: Ty, base: u32) -> Ty {
        let ty = self.repr(ty);
        let node = self.nodes[ty.0 as usize];
        if node.level != GENERIC {
            return ty;
        }
        let row = self.forward[ty.0 as usize];
        if row.generation == self.copy_generation {
            return Ty(row.target);
        }
        #[cfg(test)]
        super::steps::tick();
        let relative = (self.template_nodes.len() as u32 - base) | RELATIVE;
        self.forward[ty.0 as usize] = Forward {
            generation: self.copy_generation,
            target: relative,
        };
        self.template_nodes.push(node);
        self.work.push(ty);
        Ty(relative)
    }

    /// O(generic nodes + edges + representative links), one node step per
    /// captured node and one per list/parameter slot. One queue, no recursion.
    /// Captures the scheme's generic structure by value; callers must capture
    /// again after changing it or generalizing an external reference.
    pub fn capture(&mut self, root: Ty) -> Template {
        self.copy_generation = self
            .copy_generation
            .checked_add(1)
            .expect("copy generation exhausted");
        self.work.clear();
        let base = self.template_nodes.len() as u32;
        let lists = self.template_lists.len() as u32;
        let root = self.capture_ref(root, base);
        if root.0 & RELATIVE == 0 {
            return Template {
                nodes: root.0,
                node_len: 0,
                lists,
                list_len: 0,
            };
        }
        let mut cursor = 0;
        while cursor < self.work.len() {
            let source = self.work[cursor];
            cursor += 1;
            let target = base + (self.forward[source.0 as usize].target & !RELATIVE);
            let mut node = self.nodes[source.0 as usize];
            match node.tag() {
                VAR => {}
                ARROW => {
                    node.a = self.capture_ref(Ty(node.a), base).0;
                    let start = self.template_params.len() as u32;
                    for i in 0..node.arity() {
                        #[cfg(test)]
                        super::steps::tick();
                        let param = self.params[(node.b + i) as usize];
                        let ty = self.capture_ref(param.ty, base);
                        self.template_params.push(Param { ty, ..param });
                    }
                    node.b = start;
                }
                CONSTR | TUPLE => {
                    let old = node.b + u32::from(node.tag() == CONSTR);
                    node.b = self.template_lists.len() as u32 - lists;
                    if node.tag() == CONSTR {
                        #[cfg(test)]
                        super::steps::tick();
                        self.template_lists.push(Ty(NONE));
                    }
                    for i in 0..node.arity() {
                        #[cfg(test)]
                        super::steps::tick();
                        let child = self.lists[(old + i) as usize];
                        let child = self.capture_ref(child, base);
                        self.template_lists.push(child);
                    }
                }
                _ => panic!("expected representative descriptor"),
            }
            self.template_nodes[target as usize] = node;
        }
        Template {
            nodes: base,
            node_len: self.template_nodes.len() as u32 - base,
            lists,
            list_len: self.template_lists.len() as u32 - lists,
        }
    }

    /// O(1) for relative references, O(link depth) for external references.
    fn instance_ref(&mut self, ty: Ty, base: u32) -> Ty {
        if ty.0 == NONE {
            return ty;
        }
        if ty.0 & RELATIVE != 0 {
            return Ty(base + (ty.0 & !RELATIVE));
        }
        let ty = self.repr(ty);
        assert_ne!(
            self.nodes[ty.0 as usize].level, GENERIC,
            "recapture after external generalization"
        );
        ty
    }

    /// O(template nodes + list slots + parameter slots + external links).
    /// One pass: exactly one step per node and per list/parameter slot, no
    /// forwarding lookup, placeholder write or recursive call. Each use gets
    /// distinct generic nodes (compiler/ml/ctype.ml:747-780).
    pub fn instance(&mut self, template: Template) -> Ty {
        if template.node_len == 0 {
            return self.instance_ref(Ty(template.nodes), 0);
        }
        let base = self.nodes.len() as u32;
        let lists = self.lists.len() as u32;
        self.nodes.reserve(template.node_len as usize);
        self.forward.reserve(template.node_len as usize);
        self.lists.reserve(template.list_len as usize);
        for i in 0..template.list_len {
            #[cfg(test)]
            super::steps::tick();
            let ty = self.template_lists[(template.lists + i) as usize];
            let ty = self.instance_ref(ty, base);
            self.lists.push(ty);
        }
        for i in 0..template.node_len {
            #[cfg(test)]
            super::steps::tick();
            let mut node = self.template_nodes[(template.nodes + i) as usize];
            node.level = self.level;
            match node.tag() {
                VAR => {}
                ARROW => {
                    node.a = self.instance_ref(Ty(node.a), base).0;
                    let start = self.params.len() as u32;
                    for j in 0..node.arity() {
                        #[cfg(test)]
                        super::steps::tick();
                        let param = self.template_params[(node.b + j) as usize];
                        let ty = self.instance_ref(param.ty, base);
                        self.params.push(Param { ty, ..param });
                    }
                    node.b = start;
                }
                CONSTR | TUPLE => node.b += lists,
                _ => panic!("invalid template descriptor"),
            }
            self.push(node);
        }
        Ty(base)
    }
}

#[cfg(test)]
mod template_tests {
    use super::super::steps;
    use super::*;
    #[test]
    fn template_size() {
        assert_eq!(std::mem::size_of::<Template>(), 16);
    }
    #[test]
    fn capture_and_instance_ten_thousand_deep() {
        std::thread::Builder::new()
            .stack_size(2 * 1024 * 1024)
            .spawn(|| {
                let mut g = Graph::default();
                let mut root = g.push(Node {
                    head: VAR,
                    level: GENERIC,
                    a: NONE,
                    b: 0,
                });
                for _ in 1..10000 {
                    let b = g.lists.len() as u32;
                    g.lists.push(root);
                    root = g.push(Node {
                        head: TUPLE | 1 << 8,
                        level: GENERIC,
                        a: 0,
                        b,
                    });
                }
                let mut template = Template {
                    nodes: 0,
                    node_len: 0,
                    lists: 0,
                    list_len: 0,
                };
                assert_eq!(steps::scope(|| template = g.capture(root)), 10000 + 9999);
                assert_eq!(template.node_len, 10000);
                assert_eq!(template.list_len, 9999);
                assert_eq!(
                    steps::scope(|| {
                        g.instance(template);
                    }),
                    10000 + 9999
                );
                assert_ne!(g.instance(template), g.instance(template));
            })
            .unwrap()
            .join()
            .unwrap();
    }
    #[test]
    fn parameter_slots_sharing_and_external_links() {
        let mut g = Graph::default();
        let shared = g.push(Node {
            head: VAR,
            level: GENERIC,
            a: 7,
            b: 0,
        });
        let external = g.push(Node {
            head: VAR,
            level: 1,
            a: NONE,
            b: 1,
        });
        let target = g.push(Node {
            head: VAR,
            level: 1,
            a: NONE,
            b: 2,
        });
        for i in 0..10000 {
            g.params.push(Param {
                ty: if i % 2 == 0 { shared } else { external },
                label: i,
                loc: i + 1,
            });
        }
        let root = g.push(Node {
            head: ARROW | 10000 << 8,
            level: GENERIC,
            a: shared.0,
            b: 0,
        });
        let mut template = g.capture(external);
        assert_eq!(g.instance(template), external);
        assert_eq!(steps::scope(|| template = g.capture(root)), 10002);
        g.link(external, target);
        let mut instance = root;
        assert_eq!(
            steps::scope(|| instance = g.instance(template)),
            10002 + 5000
        );
        let node = g.nodes[instance.0 as usize];
        for i in 0..10000 {
            let param = g.params[(node.b + i) as usize];
            assert_eq!(param.label, i);
            assert_eq!(param.loc, i + 1);
            assert_eq!(param.ty, if i % 2 == 0 { Ty(node.a) } else { target });
        }
        assert_ne!(Ty(node.a), shared);
    }
}
