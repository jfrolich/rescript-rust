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
    /// pass over the forwarding array. Also initializes rows for nodes made
    /// since the last copy/capture: each row is initialized at most once per
    /// unit, so the sum of that work is linear in nodes made. Exhaustion of
    /// the generation counter is an explicit error.
    pub fn copy(&mut self, root: Ty) -> Ty {
        self.forward.resize(self.nodes.len(), Forward::default());
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
                // A copy forgets the variable's name: `copy_type_desc`,
                // compiler/ml/btype.ml:510 (`Tvar _ -> Tvar None`).
                VAR => node.a = NONE,
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
                assert_eq!(before, 10000);
                assert!(g.forward.is_empty());
                let mut copied = root;
                assert_eq!(steps::scope(|| copied = g.copy(root)), 10000);
                assert_eq!(g.nodes.len() - before, 10000);
                assert_eq!(g.forward.len(), before);
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
    /// A scheme variable's name is kept beside the instance source, not in
    /// it: the stored node has no name in `a` and the name in its level
    /// field, [`descriptor`] gives the scheme's node back, and an instance
    /// has no name and the level of the instance
    /// (compiler/ml/btype.ml:510).
    #[test]
    fn a_template_keeps_a_variable_name_out_of_the_instance_source() {
        let mut g = Graph::default();
        let var = |a| Node {
            head: VAR,
            level: GENERIC,
            a,
            b: 0,
        };
        let (named, plain) = (g.push(var(7)), g.push(var(NONE)));
        let b = g.lists.len() as u32;
        g.lists.extend([named, plain]);
        let tuple = g.push(Node {
            head: TUPLE | 2 << 8,
            level: GENERIC,
            a: 0,
            b,
        });
        let template = g.capture(tuple);
        let stored: Vec<Node> = g.template_nodes
            [template.nodes as usize..(template.nodes + template.node_len) as usize]
            .to_vec();
        assert_eq!(stored.len(), 3);
        let variables: Vec<Node> = stored
            .iter()
            .copied()
            .filter(|node| node.tag() == VAR)
            .collect();
        assert_eq!(variables.len(), 2);
        // No stored variable has a name where an instance copies it from.
        assert!(variables.iter().all(|node| node.a == NONE));
        let mut names: Vec<u32> = variables.iter().map(|node| node.level).collect();
        names.sort_unstable();
        assert_eq!(names, [7, NONE]);
        // The scheme's own nodes, as its printer and the old checker's
        // bridge read them.
        let mut read: Vec<u32> = variables
            .iter()
            .map(|&node| {
                let scheme = descriptor(node);
                assert_eq!(scheme.level, GENERIC);
                scheme.a
            })
            .collect();
        read.sort_unstable();
        assert_eq!(read, [7, NONE]);
        for &node in stored.iter().filter(|node| node.tag() != VAR) {
            assert_eq!(descriptor(node), node);
        }
        g.begin_def();
        let out = g.instance(template);
        let b = g.nodes[out.0 as usize].b as usize;
        for child in [g.lists[b], g.lists[b + 1]] {
            let node = g.nodes[child.0 as usize];
            assert_eq!(node.tag(), VAR);
            assert_eq!(node.a, NONE, "an instance's variable has no name");
            assert_eq!(node.level, g.level);
        }
    }
}

/// O(1), no allocation: the descriptor a stored template node stands for.
/// Every template node is generic, so its level field is free: a variable
/// keeps its scheme name there and NONE in `a`, which is what an instance
/// copies (compiler/ml/btype.ml:510). Readers that print or convert a scheme
/// (tc/canonical/view.rs, tc/bridge/to_old.rs) read the name through this.
pub(crate) fn descriptor(node: Node) -> Node {
    if node.tag() == VAR {
        Node {
            level: GENERIC,
            a: node.level,
            ..node
        }
    } else {
        node
    }
}

/// Four words, with a pool-range index, avoiding a 65,535-node scheme limit.
/// References use bit 30 for instance-relative indices; bit 31 stays reserved
/// for frozen handles. A zero-node template holds an external root in nodes.
#[derive(Clone, Copy, Debug)]
#[repr(C)]
pub struct Template {
    pub nodes: u32,
    pub node_len: u32,
    pub pools: u32,
    pub list_len: u32,
}

/// Cold ranges read once per instance, not per node. Parameter metadata and
/// external references are pools separate from the four-byte list slots.
#[derive(Clone, Copy)]
#[cfg_attr(test, derive(Debug, PartialEq, Eq))]
#[repr(C)]
pub(crate) struct TemplatePools {
    lists: u32,
    params: u32,
    param_len: u32,
    externals: u32,
    external_len: u32,
}

const RELATIVE: u32 = 1 << 30;

impl Graph {
    /// O(1) plus representative links and amortized arena growth. Assign the
    /// relative reference at first encounter, preserving source sharing.
    fn capture_ref(&mut self, ty: Ty, base: u32) -> Ty {
        let ty = self.repr(ty);
        let node = self.nodes[ty.0 as usize];
        if node.level != GENERIC {
            let external = self.template_externals.len() as u32;
            assert!(external < RELATIVE);
            self.template_externals.push(ty);
            return Ty(external);
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
        assert!(
            matches!(node.tag(), VAR | CONSTR | TUPLE | ARROW),
            "unsupported template descriptor"
        );
        self.template_nodes.push(node);
        self.work.push(ty);
        Ty(relative)
    }

    /// O(generic nodes + edges + representative links), one node step per
    /// captured node and one per list/parameter slot. One queue, no recursion.
    /// Captures the scheme's generic structure by value; callers must capture
    /// again after changing it or generalizing an external reference. Also
    /// initializes rows for nodes made since the last copy/capture; each row
    /// is initialized at most once per unit, so their total cost is linear
    /// in nodes made, not the number of template instances.
    pub fn capture(&mut self, root: Ty) -> Template {
        self.forward.resize(self.nodes.len(), Forward::default());
        let root = self.repr(root);
        if self.nodes[root.0 as usize].level != GENERIC {
            return Template {
                nodes: root.0,
                node_len: 0,
                pools: 0,
                list_len: 0,
            };
        }
        self.copy_generation = self
            .copy_generation
            .checked_add(1)
            .expect("copy generation exhausted");
        self.work.clear();
        let base = self.template_nodes.len() as u32;
        let lists = self.template_lists.len() as u32;
        let params = self.template_params.len() as u32;
        let externals = self.template_externals.len() as u32;
        self.capture_ref(root, base);
        let mut cursor = 0;
        while cursor < self.work.len() {
            let source = self.work[cursor];
            cursor += 1;
            let target = base + (self.forward[source.0 as usize].target & !RELATIVE);
            let mut node = self.nodes[source.0 as usize];
            match node.tag() {
                // The instance source holds no name: an instance copies the
                // node as it is stored, nameless (`copy_type_desc`,
                // compiler/ml/btype.ml:510: `Tvar _ -> Tvar None`), and
                // overwrites the level. The scheme's name moves to the
                // level field, which no instance reads ([`descriptor`]).
                VAR => {
                    node.level = node.a;
                    node.a = NONE;
                }
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
                    node.b = start - params;
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
        let pools = self.template_pools.len() as u32;
        self.template_pools.push(TemplatePools {
            lists,
            params,
            param_len: self.template_params.len() as u32 - params,
            externals,
            external_len: self.template_externals.len() as u32 - externals,
        });
        Template {
            nodes: base,
            node_len: self.template_nodes.len() as u32 - base,
            pools,
            list_len: self.template_lists.len() as u32 - lists,
        }
    }

    /// O(template nodes + list/parameter slots + external references + links).
    /// Validate external references once, then copy each node and slot once.
    /// Exact-size iterators reserve each pool once: no per-node growth check,
    /// placeholder write, forwarding lookup or recursive call. Each use gets
    /// distinct generic nodes (compiler/ml/ctype.ml:747-780), and a copied
    /// variable has no name (compiler/ml/btype.ml:510).
    pub fn instance(&mut self, template: Template) -> Ty {
        if template.node_len == 0 {
            return self.instance_external_root(template);
        }
        let pools = self.template_pools[template.pools as usize];
        if pools.external_len == 0 {
            self.instance_inner::<false>(template, &pools)
        } else {
            self.instance_with_externals(template, &pools)
        }
    }

    /// O(links), out of line: the instance of a template whose root is not
    /// generic is that root's representative, which must still not be generic.
    #[inline(never)]
    fn instance_external_root(&mut self, template: Template) -> Ty {
        let root = self.repr(Ty(template.nodes));
        assert_ne!(
            self.nodes[root.0 as usize].level, GENERIC,
            "recapture after external generalization"
        );
        root
    }

    /// O(nodes + slots + external references + links), out of line so that
    /// the closed instance, inlined into [`Graph::instance`], shares no
    /// registers with the external references' representative lookups.
    #[inline(never)]
    fn instance_with_externals(&mut self, template: Template, pools: &TemplatePools) -> Ty {
        self.instance_inner::<true>(template, pools)
    }

    /// O(nodes + slots + external references + links). Both specializations
    /// share this traversal; closed templates compile without an external
    /// reference case in the per-reference mapping.
    #[inline(always)]
    fn instance_inner<const EXTERNALS: bool>(
        &mut self,
        template: Template,
        pools: &TemplatePools,
    ) -> Ty {
        let Self {
            nodes,
            lists,
            params,
            template_nodes,
            template_lists,
            template_params,
            template_externals,
            instance_externals,
            trail,
            speculation_depth,
            level,
            ..
        } = self;
        let base = nodes.len() as u32;
        let list_base = lists.len() as u32;
        let param_base = params.len() as u32;
        assert!(nodes.len() + (template.node_len as usize) < (1 << 30));
        if EXTERNALS {
            instance_externals.clear();
            let external_source = &template_externals
                [pools.externals as usize..(pools.externals + pools.external_len) as usize];
            instance_externals.extend(external_source.iter().map(|&ty| {
                let ty = Self::repr_parts(nodes, trail, *speculation_depth, ty);
                assert_ne!(
                    nodes[ty.0 as usize].level, GENERIC,
                    "recapture after external generalization"
                );
                ty
            }));
        }
        let at = |ty: Ty| {
            if ty.0 == NONE {
                ty
            } else if EXTERNALS && ty.0 & RELATIVE == 0 {
                instance_externals[(ty.0 - pools.externals) as usize]
            } else {
                Ty(base + (ty.0 & !RELATIVE))
            }
        };
        let slots =
            &template_lists[pools.lists as usize..(pools.lists + template.list_len) as usize];
        lists.extend(slots.iter().map(|&ty| {
            #[cfg(test)]
            super::steps::tick();
            at(ty)
        }));
        if pools.param_len != 0 {
            let arguments =
                &template_params[pools.params as usize..(pools.params + pools.param_len) as usize];
            params.extend(arguments.iter().map(|&param| {
                #[cfg(test)]
                super::steps::tick();
                Param {
                    ty: at(param.ty),
                    ..param
                }
            }));
        }
        // Tag order is VAR, LINK (never captured), CONSTR, TUPLE, ARROW.
        // Capture validates descriptors before publishing template nodes.
        // A stored variable is already nameless; the level written here
        // replaces the name the level field holds ([`descriptor`]).
        let b_addend = [0, 0, list_base, list_base, param_base];
        let source =
            &template_nodes[template.nodes as usize..(template.nodes + template.node_len) as usize];
        nodes.extend(source.iter().map(|&original| {
            #[cfg(test)]
            super::steps::tick();
            let mut node = Node {
                level: *level,
                ..original
            };
            node.b += b_addend[node.tag() as usize];
            if node.tag() == ARROW {
                node.a = at(Ty(node.a)).0;
            }
            node
        }));
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
        assert_eq!(std::mem::size_of::<TemplatePools>(), 20);
    }
    #[test]
    #[should_panic(expected = "unsupported template descriptor")]
    fn capture_rejects_unknown_tags_before_template_write() {
        let mut g = Graph::default();
        let root = g.push(Node {
            head: 15,
            level: GENERIC,
            a: 0,
            b: 0,
        });
        g.capture(root);
    }

    #[test]
    fn ten_thousand_instances_do_not_grow_forwarding() {
        let mut g = Graph::default();
        let root = g.push(Node {
            head: VAR,
            level: GENERIC,
            a: NONE,
            b: 0,
        });
        let template = g.capture(root);
        let rows = g.forward.len();
        assert_eq!(rows, 1);
        assert_eq!(
            steps::scope(|| {
                for _ in 0..10000 {
                    g.instance(template);
                }
            }),
            10000
        );
        assert_eq!(g.forward.len(), rows);
        // Only a new copy/capture initializes the source rows, never rows
        // for the fresh targets made during that operation.
        let source_len = g.nodes.len();
        g.copy(root);
        assert_eq!(g.forward.len(), source_len);
        assert_eq!(g.nodes.len(), source_len + 1);
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
                    pools: 0,
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
    fn closed_arrow_copies_ten_thousand_parameter_slots() {
        let mut g = Graph::default();
        let shared = g.push(Node {
            head: VAR,
            level: GENERIC,
            a: 7,
            b: 0,
        });
        for i in 0..10000 {
            g.params.push(Param {
                ty: shared,
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
        let template = g.capture(root);
        assert_eq!(g.template_pools[template.pools as usize].external_len, 0);
        let mut copied = root;
        assert_eq!(steps::scope(|| copied = g.instance(template)), 10002);
        let node = g.nodes[copied.0 as usize];
        for (i, param) in g.params[node.b as usize..].iter().enumerate() {
            assert_eq!(param.ty, Ty(node.a));
            assert_eq!(param.label, i as u32);
            assert_eq!(param.loc, i as u32 + 1);
        }
        assert_ne!(Ty(node.a), shared);
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
