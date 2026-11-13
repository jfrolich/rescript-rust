//! Freeze generic schemes by item and shared external nodes by occurrence.
use super::graph::{ARROW, CONSTR, Graph, NONE, Node, Param, TUPLE, Ty, VAR};
use super::segment::Segment;

/// O(sum of captured scheme nodes/edges + shared nodes/edges + graph capacity).
/// Captures each root in R1's encounter order, without merging equal nodes.
/// `items` supplies metadata and its already sorted export tables; all payloads
/// referring to templates index `roots`. Constructor paths must already be
/// absolute handles. Its digest is supplied by the signature's producer.
/// Type pools in `items` must be empty. The graph is consumed, so clearing its
/// previous local captures cannot invalidate a caller's template.
///
/// Generic structure is private to an item; non-generic nodes use one dense
/// segment-wide forwarding table. This is the copy/share boundary of
/// compiler/ml/ctype.ml:747-780, including stopping at a non-generic root.
/// Each reachable shared node is traversed once using a queue, not recursion.
pub fn publish(mut graph: Graph, roots: &[Ty], mut items: Segment) -> Segment {
    assert!(items.nodes.is_empty() && items.lists.is_empty() && items.params.is_empty());
    assert!(items.templates.is_empty() && items.template_nodes.is_empty());
    assert!(items.template_lists.is_empty() && items.template_params.is_empty());
    assert!(items.template_pools.is_empty() && items.template_externals.is_empty());
    graph.template_nodes.clear();
    graph.template_lists.clear();
    graph.template_params.clear();
    graph.template_pools.clear();
    graph.template_externals.clear();

    let mut templates = Vec::with_capacity(roots.len());
    for &root in roots {
        #[cfg(test)]
        super::steps::tick();
        templates.push(graph.capture(root));
    }
    let mut shared = Shared::new(graph.nodes.len());
    for template in &mut templates {
        #[cfg(test)]
        super::steps::tick();
        if template.node_len == 0 {
            template.nodes = shared.reference(&mut graph, Ty(template.nodes)).0;
        }
    }
    // These are the slots emitted by capture, not another type-tree walk.
    for i in 0..graph.template_externals.len() {
        #[cfg(test)]
        super::steps::tick();
        let source = graph.template_externals[i];
        graph.template_externals[i] = shared.reference(&mut graph, source);
    }
    shared.finish(&mut graph);
    items.nodes = shared.nodes.into_boxed_slice();
    items.lists = shared.lists.into_boxed_slice();
    items.params = shared.params.into_boxed_slice();
    items.templates = templates.into_boxed_slice();
    items.template_nodes = graph.template_nodes.into_boxed_slice();
    items.template_lists = graph.template_lists.into_boxed_slice();
    items.template_params = graph.template_params.into_boxed_slice();
    items.template_pools = graph.template_pools.into_boxed_slice();
    items.template_externals = graph.template_externals.into_boxed_slice();
    items
}

/// Publication context, allocated once. Only four-byte handles enter its queue.
struct Shared {
    forward: Vec<Ty>,
    queue: Vec<Ty>,
    nodes: Vec<Node>,
    lists: Vec<Ty>,
    params: Vec<Param>,
}

impl Shared {
    /// O(source nodes) dense-table initialization, with no per-node allocation.
    fn new(len: usize) -> Self {
        Self {
            forward: vec![Ty(NONE); len],
            queue: Vec::new(),
            nodes: Vec::new(),
            lists: Vec::new(),
            params: Vec::new(),
        }
    }

    /// Amortized O(1) plus representative links. Each occurrence is queued once.
    fn reference(&mut self, graph: &mut Graph, source: Ty) -> Ty {
        let source = graph.repr(source);
        let slot = &mut self.forward[source.0 as usize];
        if slot.0 == NONE {
            let target = u32::try_from(self.nodes.len()).expect("segment node limit");
            assert!(target < 1 << 30);
            *slot = Ty(target);
            self.nodes.push(graph.nodes[source.0 as usize]);
            self.queue.push(source);
        }
        *slot
    }

    /// O(shared nodes + edges + representative links), one node step per node
    /// and one per parameter/list slot. Preserves cycles and identity without
    /// changing the source's levels, paths or sharing (ctype.ml:copy).
    fn finish(&mut self, graph: &mut Graph) {
        let mut cursor = 0;
        while cursor < self.queue.len() {
            #[cfg(test)]
            super::steps::tick();
            let source = self.queue[cursor];
            cursor += 1;
            let target = self.forward[source.0 as usize];
            let mut node = graph.nodes[source.0 as usize];
            match node.tag() {
                VAR => {}
                ARROW => {
                    node.a = self.reference(graph, Ty(node.a)).0;
                    let start = self.params.len() as u32;
                    for i in 0..node.arity() {
                        #[cfg(test)]
                        super::steps::tick();
                        let param = graph.params[(node.b + i) as usize];
                        let ty = self.reference(graph, param.ty);
                        self.params.push(Param { ty, ..param });
                    }
                    node.b = start;
                }
                CONSTR | TUPLE => {
                    let old = node.b + u32::from(node.tag() == CONSTR);
                    node.b = self.lists.len() as u32;
                    if node.tag() == CONSTR {
                        // Abbreviation caches belong to the importing checker,
                        // not the exported type (compiler/ml/ctype.ml:copy).
                        self.lists.push(Ty(NONE));
                    }
                    for i in 0..node.arity() {
                        #[cfg(test)]
                        super::steps::tick();
                        let child = graph.lists[(old + i) as usize];
                        let ty = self.reference(graph, child);
                        self.lists.push(ty);
                    }
                }
                _ => panic!("expected representative descriptor"),
            }
            self.nodes[target.0 as usize] = node;
        }
    }
}

impl Segment {
    /// O(nodes + slots + template pools), one bulk allocation per nonempty pool.
    /// Creates a worker-owned graph with this segment's absolute local prefix;
    /// templates can then be passed directly to Graph::instance. No forwarding
    /// rows are initialized until a copy/capture, exactly as for a fresh graph.
    pub fn graph(&self) -> Graph {
        Graph {
            nodes: copy_pool(&self.nodes),
            lists: copy_pool(&self.lists),
            params: copy_pool(&self.params),
            template_nodes: copy_pool(&self.template_nodes),
            template_lists: copy_pool(&self.template_lists),
            template_params: copy_pool(&self.template_params),
            template_pools: copy_pool(&self.template_pools),
            template_externals: copy_pool(&self.template_externals),
            ..Graph::default()
        }
    }
}

/// O(pool length), one counted copy per row, one exact-size allocation.
fn copy_pool<T: Copy>(source: &[T]) -> Vec<T> {
    source
        .iter()
        .inspect(|_| {
            #[cfg(test)]
            super::steps::tick();
        })
        .copied()
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tc::{
        graph::GENERIC,
        segment::{ChildTable, ExportItem, ExportKind},
        steps,
    };

    fn variable(graph: &mut Graph, level: u32) -> Ty {
        graph.push(Node {
            head: VAR,
            level,
            a: NONE,
            b: 0,
        })
    }

    #[test]
    fn ten_thousand_one_node_items() {
        let mut graph = Graph::default();
        let roots: Vec<_> = (0..10000).map(|_| variable(&mut graph, GENERIC)).collect();
        let items = Segment {
            items: (0..10000)
                .map(|i| ExportItem {
                    name: i,
                    payload: i,
                    kind: ExportKind::Value,
                })
                .collect(),
            children: Box::new([ChildTable {
                start: 0,
                len: 10000,
            }]),
            ..Segment::default()
        };
        let mut published = None;
        let count = steps::scope(|| published = Some(publish(graph, &roots, items)));
        assert!(count <= 4 * 10000, "{count}");
        let segment = published.unwrap();
        assert_eq!(segment.templates.len(), 10000);
        assert_eq!(segment.template_nodes.len(), 10000);
        assert!(segment.nodes.is_empty());
        let mut graph = segment.graph();
        assert!(graph.forward.is_empty());
        let a = graph.instance(segment.templates[0]);
        let b = graph.instance(segment.templates[1]);
        assert_ne!(a, b);
        assert_eq!(graph.nodes[a.0 as usize], graph.nodes[b.0 as usize]);
    }

    #[test]
    fn exporter_shared_positions_remain_shared_in_an_instance() {
        // checker_identity_08: one exported scheme has repeated positions of
        // one node, while a different equal occurrence must stay different.
        let mut graph = Graph::default();
        let shared = variable(&mut graph, GENERIC);
        let equal = variable(&mut graph, GENERIC);
        graph.lists.extend([shared, shared, equal]);
        let root = graph.push(Node {
            head: TUPLE | 3 << 8,
            level: GENERIC,
            a: 0,
            b: 0,
        });
        let segment = publish(graph, &[root, root], Segment::default());
        assert_eq!(segment.template_nodes.len(), 6);
        let mut graph = segment.graph();
        let a = graph.instance(segment.templates[0]);
        let b = graph.instance(segment.templates[1]);
        let slots = graph.nodes[a.0 as usize].b as usize;
        assert_eq!(graph.lists[slots], graph.lists[slots + 1]);
        assert_ne!(graph.lists[slots], graph.lists[slots + 2]);
        let other = graph.nodes[b.0 as usize].b as usize;
        assert_ne!(graph.lists[slots], graph.lists[other]);
    }

    #[test]
    fn non_generic_nodes_are_shared_across_items_and_cycles_survive() {
        let mut graph = Graph::default();
        let shared = variable(&mut graph, 1);
        graph.lists.extend([shared, shared]);
        let root = graph.push(Node {
            head: TUPLE | 2 << 8,
            level: GENERIC,
            a: 0,
            b: 0,
        });
        let segment = publish(graph, &[root, root, shared], Segment::default());
        assert_eq!(segment.nodes.len(), 1);
        let mut graph = segment.graph();
        let a = graph.instance(segment.templates[0]);
        let b = graph.instance(segment.templates[1]);
        let external = graph.instance(segment.templates[2]);
        for root in [a, b] {
            let slots = graph.nodes[root.0 as usize].b as usize;
            assert_eq!(graph.lists[slots], external);
            assert_eq!(graph.lists[slots + 1], external);
        }
        let mut graph = Graph::default();
        graph.lists.push(Ty(0));
        let cycle = graph.push(Node {
            head: TUPLE | 1 << 8,
            level: 1,
            a: 0,
            b: 0,
        });
        let segment = publish(graph, &[cycle], Segment::default());
        assert_eq!(segment.nodes.len(), 1);
        assert_eq!(segment.lists[0], Ty(0));
    }

    #[test]
    fn deep_publication_uses_a_queue_on_a_two_mb_stack() {
        std::thread::Builder::new()
            .stack_size(2 * 1024 * 1024)
            .spawn(|| {
                for level in [1, GENERIC] {
                    let mut graph = Graph::default();
                    let mut root = variable(&mut graph, level);
                    for _ in 1..10000 {
                        let b = graph.lists.len() as u32;
                        graph.lists.push(root);
                        root = graph.push(Node {
                            head: TUPLE | 1 << 8,
                            level,
                            a: 0,
                            b,
                        });
                    }
                    let mut segment = None;
                    let count = steps::scope(|| {
                        segment = Some(publish(graph, &[root], Segment::default()));
                    });
                    assert!(count <= 4 * 10000, "{count}");
                    let segment = segment.unwrap();
                    assert_eq!(segment.nodes.len() + segment.template_nodes.len(), 10000);
                    let mut loaded = None;
                    let copies = steps::scope(|| loaded = Some(segment.graph()));
                    assert!(copies <= 2 * 10000, "{copies}");
                    loaded.unwrap().instance(segment.templates[0]);
                }
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
