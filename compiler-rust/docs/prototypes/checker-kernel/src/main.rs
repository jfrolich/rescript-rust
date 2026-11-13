//! Measurement probe for CHECKER_REWRITE section 2: what one operation of
//! the designed type graph costs. Not compiler code: a stand-alone program
//! run under cachegrind, one operation per run, with the loop overhead
//! taken out by a run of zero iterations.
//!
//!   checker-kernel OP N
//!
//! The graph keeps what the contract observes (section 2.1): one node per
//! occurrence, links in the specified direction, a level on every node,
//! copy or share by the level, sharing inside a scheme.

use std::hint::black_box;

const GENERIC: u32 = 100_000_000;
const TAG_VAR: u32 = 0;
const TAG_LINK: u32 = 1;
const TAG_CONSTR: u32 = 2;
const TAG_TUPLE: u32 = 3;
const TAG_ARROW: u32 = 4;
/// In a template, a reference with this bit is relative to the instance.
const REL: u32 = 1 << 31;

/// 16 bytes. `head`: tag in bits 0..4, list length in bits 8..32.
/// Var: `a` name. Link: `a` target. Constr: `a` type id, `b` list start.
/// Tuple: `b` list start. Arrow: `a` result, `b` list start.
#[derive(Clone, Copy)]
#[repr(C)]
struct Node {
    head: u32,
    level: u32,
    a: u32,
    b: u32,
}

struct Template {
    node_start: u32,
    node_len: u32,
    list_start: u32,
    list_len: u32,
}

struct Graph {
    nodes: Vec<Node>,
    lists: Vec<u32>,
    tnodes: Vec<Node>,
    tlists: Vec<u32>,
    /// One bit per type id: the declaration is an abbreviation.
    abbreviation: Vec<bool>,
    level: u32,
    /// Writes logged only while a speculation is open.
    trail: Vec<(u32, Node)>,
    speculating: bool,
    steps: u64,
}

impl Graph {
    fn new() -> Self {
        Graph {
            nodes: Vec::with_capacity(1 << 16),
            lists: Vec::with_capacity(1 << 16),
            tnodes: Vec::new(),
            tlists: Vec::new(),
            abbreviation: vec![false; 64],
            level: 1,
            trail: Vec::new(),
            speculating: false,
            steps: 0,
        }
    }

    /// Bulk free of a unit's nodes. Cost: two stores.
    fn reset(&mut self) {
        self.nodes.clear();
        self.lists.clear();
    }

    /// Step counter of the tests; compiled out of the measured build.
    #[inline(always)]
    fn step(&mut self) {
        #[cfg(debug_assertions)]
        {
            self.steps += 1;
        }
    }

    #[inline(always)]
    fn push(&mut self, node: Node) -> u32 {
        let at = self.nodes.len() as u32;
        self.nodes.push(node);
        at
    }

    /// Representative, with path halving. Cost: one load when `t` is one.
    #[inline(always)]
    fn repr(&mut self, mut t: u32) -> u32 {
        loop {
            let node = self.nodes[t as usize];
            if node.head & 0xf != TAG_LINK {
                return t;
            }
            let next = node.a;
            let after = self.nodes[next as usize];
            if after.head & 0xf == TAG_LINK {
                self.nodes[t as usize].a = after.a;
            }
            t = next;
        }
    }

    #[inline(always)]
    fn write(&mut self, t: u32, node: Node) {
        if self.speculating {
            self.trail.push((t, self.nodes[t as usize]));
        }
        self.nodes[t as usize] = node;
    }

    /// One pass over the template: lists first, then nodes. No map, no
    /// recursion. Cost: one step per list slot and one per node.
    fn instance(&mut self, template: &Template) -> u32 {
        let base = self.nodes.len() as u32;
        let list_base = self.lists.len() as u32;
        let at = |r: u32| if r & REL != 0 { base + (r & !REL) } else { r };
        let lists = &self.tlists
            [template.list_start as usize..(template.list_start + template.list_len) as usize];
        self.lists.extend(lists.iter().map(|&r| at(r)));
        let level = self.level;
        let nodes = &self.tnodes
            [template.node_start as usize..(template.node_start + template.node_len) as usize];
        self.nodes.extend(nodes.iter().map(|&node| {
            let mut node = node;
            node.level = level;
            match node.head & 0xf {
                TAG_VAR => {}
                TAG_ARROW => {
                    node.a = at(node.a);
                    node.b += list_base;
                }
                _ => node.b += list_base,
            }
            node
        }));
        #[cfg(debug_assertions)]
        {
            self.steps += template.node_len as u64;
        }
        base
    }

    /// Does `var` occur in `t`, and lower every node of `t` above `level`.
    /// One walk: a node below the variable's level cannot hold it, and a
    /// node at or below the target level has nothing to lower.
    fn bind_walk(&mut self, var: u32, var_level: u32, t: u32) -> bool {
        let t = self.repr(t);
        if t == var {
            return false;
        }
        let node = self.nodes[t as usize];
        if node.level < var_level {
            return true;
        }
        self.step();
        if node.level > var_level {
            let mut lowered = node;
            lowered.level = var_level;
            self.write(t, lowered);
        }
        let tag = node.head & 0xf;
        if tag == TAG_VAR {
            return true;
        }
        let len = node.head >> 8;
        for i in 0..len {
            let child = self.lists[(node.b + i) as usize];
            if !self.bind_walk(var, var_level, child) {
                return false;
            }
        }
        if tag == TAG_ARROW && !self.bind_walk(var, var_level, node.a) {
            return false;
        }
        true
    }

    /// Lower `t` and what it reaches to `level`. Cost: one step per node
    /// above `level`; one compare when the root is not.
    fn lower(&mut self, level: u32, t: u32) {
        let t = self.repr(t);
        let node = self.nodes[t as usize];
        if node.level <= level {
            return;
        }
        self.step();
        let mut lowered = node;
        lowered.level = level;
        self.write(t, lowered);
        let tag = node.head & 0xf;
        if tag == TAG_VAR {
            return;
        }
        for i in 0..node.head >> 8 {
            let child = self.lists[(node.b + i) as usize];
            self.lower(level, child);
        }
        if tag == TAG_ARROW {
            self.lower(level, node.a);
        }
    }

    /// Unify in expression mode. `false` is a failure: the caller checks
    /// the unit again in the explaining mode.
    #[inline(always)]
    fn unify(&mut self, t1: u32, t2: u32) -> bool {
        let t1 = self.repr(t1);
        let t2 = self.repr(t2);
        // The two sides are one node: nothing to do, and no call.
        t1 == t2 || self.unify_distinct(t1, t2)
    }

    /// [`Self::unify`] of two distinct representatives.
    fn unify_distinct(&mut self, t1: u32, t2: u32) -> bool {
        self.step();
        let n1 = self.nodes[t1 as usize];
        let n2 = self.nodes[t2 as usize];
        let tag1 = n1.head & 0xf;
        let tag2 = n2.head & 0xf;
        if tag1 == TAG_VAR {
            if !self.bind_walk(t1, n1.level, t2) {
                return false;
            }
            self.write(t1, Node { head: TAG_LINK, level: n1.level, a: t2, b: 0 });
            return true;
        }
        if tag2 == TAG_VAR {
            if !self.bind_walk(t2, n2.level, t1) {
                return false;
            }
            self.write(t2, Node { head: TAG_LINK, level: n2.level, a: t1, b: 0 });
            return true;
        }
        if n1.head != n2.head {
            return false;
        }
        if tag1 == TAG_CONSTR
            && (n1.a != n2.a || self.abbreviation[n1.a as usize])
        {
            // An abbreviation, or two paths: the expansion road (not probed).
            return false;
        }
        let level = n1.level.min(n2.level);
        if n2.level > level {
            self.lower(level, t2);
        }
        if n1.level > level {
            self.lower(level, t1);
        }
        // The link is written before the children, in this direction.
        self.write(t1, Node { head: TAG_LINK, level, a: t2, b: 0 });
        for i in 0..n1.head >> 8 {
            let c1 = self.lists[(n1.b + i) as usize];
            let c2 = self.lists[(n2.b + i) as usize];
            if !self.unify(c1, c2) {
                self.nodes[t1 as usize] = n1;
                return false;
            }
        }
        if tag1 == TAG_ARROW && !self.unify(n1.a, n2.a) {
            self.nodes[t1 as usize] = n1;
            return false;
        }
        true
    }

    /// Every node reachable from `t` above the current level becomes
    /// generic. Cost: one step per such node.
    fn generalize(&mut self, t: u32) {
        let t = self.repr(t);
        let node = self.nodes[t as usize];
        if node.level <= self.level || node.level == GENERIC {
            return;
        }
        self.step();
        self.nodes[t as usize].level = GENERIC;
        let tag = node.head & 0xf;
        if tag == TAG_VAR {
            return;
        }
        for i in 0..node.head >> 8 {
            let child = self.lists[(node.b + i) as usize];
            self.generalize(child);
        }
        if tag == TAG_ARROW {
            self.generalize(node.a);
        }
    }

    // ---- template construction (setup, not measured) ----

    fn tconstr(&mut self, id: u32, args: &[u32]) -> u32 {
        let start = self.tlists.len() as u32;
        self.tlists.extend_from_slice(args);
        self.tnodes.push(Node {
            head: TAG_CONSTR | (args.len() as u32) << 8,
            level: GENERIC,
            a: id,
            b: start,
        });
        (self.tnodes.len() as u32 - 1) | REL
    }

    fn tvar(&mut self) -> u32 {
        self.tnodes.push(Node { head: TAG_VAR, level: GENERIC, a: 0, b: 0 });
        (self.tnodes.len() as u32 - 1) | REL
    }

    fn tarrow(&mut self, args: &[u32], ret: u32) -> u32 {
        let start = self.tlists.len() as u32;
        self.tlists.extend_from_slice(args);
        self.tnodes.push(Node {
            head: TAG_ARROW | (args.len() as u32) << 8,
            level: GENERIC,
            a: ret,
            b: start,
        });
        (self.tnodes.len() as u32 - 1) | REL
    }
}

/// Builds a template whose root is its last node, then renumbers it so that
/// relative references count from the template's first node.
fn template(graph: &mut Graph, build: impl FnOnce(&mut Graph) -> u32) -> Template {
    let node_start = graph.tnodes.len() as u32;
    let list_start = graph.tlists.len() as u32;
    build(graph);
    let node_len = graph.tnodes.len() as u32 - node_start;
    let list_len = graph.tlists.len() as u32 - list_start;
    // Root first, as the checker's copy allocates it: reverse the nodes.
    graph.tnodes[node_start as usize..].reverse();
    let fix = |r: u32| {
        if r & REL != 0 { (node_len - 1 - ((r & !REL) - node_start)) | REL } else { r }
    };
    for slot in &mut graph.tlists[list_start as usize..] {
        *slot = fix(*slot);
    }
    for node in &mut graph.tnodes[node_start as usize..] {
        if node.head & 0xf == TAG_ARROW {
            node.a = fix(node.a);
        }
        if node.head & 0xf != TAG_VAR {
            node.b -= list_start;
        }
    }
    Template { node_start, node_len, list_start, list_len }
}

const INT: u32 = 1;
const STRING: u32 = 2;
const ARRAY: u32 = 3;
const OPTION: u32 = 4;

/// Scopes: a dense table from interned name to the innermost binding, and
/// an undo log. Binding and lookup hash nothing.
struct Scopes {
    head: Vec<u32>,
    log: Vec<(u32, u32)>,
    binders: Vec<u32>,
}

impl Scopes {
    #[inline(always)]
    fn bind(&mut self, name: u32, ty: u32) -> u32 {
        let binder = self.binders.len() as u32;
        self.binders.push(ty);
        self.log.push((name, self.head[name as usize]));
        self.head[name as usize] = binder;
        binder
    }
    #[inline(always)]
    fn lookup(&self, name: u32) -> u32 {
        self.head[name as usize]
    }
    #[inline(always)]
    fn close(&mut self, mark: usize) {
        while self.log.len() > mark {
            let (name, previous) = self.log.pop().unwrap();
            self.head[name as usize] = previous;
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let op = args.get(1).map(String::as_str).unwrap_or("help");
    let n: u64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(0);
    let mut g = Graph::new();
    // int
    let ground1 = template(&mut g, |g| g.tconstr(INT, &[]));
    // option<array<int>>
    let ground3 = template(&mut g, |g| {
        let int = g.tconstr(INT, &[]);
        let array = g.tconstr(ARRAY, &[int]);
        g.tconstr(OPTION, &[array])
    });
    // (array<'a>, 'a => 'b) => array<'b>
    let scheme7 = template(&mut g, |g| {
        let a = g.tvar();
        let b = g.tvar();
        let array_a = g.tconstr(ARRAY, &[a]);
        let f = g.tarrow(&[a], b);
        let array_b = g.tconstr(ARRAY, &[b]);
        g.tarrow(&[array_a, f], array_b)
    });
    // (string, int) => option<string>
    let fun5 = template(&mut g, |g| {
        let s = g.tconstr(STRING, &[]);
        let i = g.tconstr(INT, &[]);
        let s2 = g.tconstr(STRING, &[]);
        let o = g.tconstr(OPTION, &[s2]);
        g.tarrow(&[s, i], o)
    });
    let mut scopes = Scopes { head: vec![0; 4096], log: Vec::new(), binders: vec![0] };
    for name in 0..4096u32 {
        scopes.bind(name, name);
    }
    const OPS: &[&str] = &["instance1", "instance3", "instance5", "instance7", "unify_same", "two_instance1", "unify_ground1", "two_instance3", "unify_ground3", "two_instance5", "unify_fun5", "var_instance3", "bind_var3", "apply7", "generalize7", "lookup_name", "lookup_binder", "bind_close", "empty"];
    let Some(op_id) = OPS.iter().position(|name| *name == op) else {
        eprintln!("unknown operation {op}");
        std::process::exit(2);
    };
    let op_id = black_box(op_id);
    let mut sink = 0u64;
    for i in 0..n {
        if i & 0xfff == 0 {
            g.reset();
        }
        match op_id {
            0 => sink += g.instance(black_box(&ground1)) as u64,
            1 => sink += g.instance(black_box(&ground3)) as u64,
            2 => sink += g.instance(black_box(&fun5)) as u64,
            3 => sink += g.instance(black_box(&scheme7)) as u64,
            4 => {
                let x = g.instance(black_box(&ground3));
                sink += g.unify(x, black_box(x)) as u64;
            }
            5 => {
                sink += g.instance(black_box(&ground1)) as u64;
                sink += g.instance(black_box(&ground1)) as u64;
            }
            6 => {
                let x = g.instance(black_box(&ground1));
                let y = g.instance(black_box(&ground1));
                sink += g.unify(x, y) as u64;
            }
            7 => {
                sink += g.instance(black_box(&ground3)) as u64;
                sink += g.instance(black_box(&ground3)) as u64;
            }
            8 => {
                let x = g.instance(black_box(&ground3));
                let y = g.instance(black_box(&ground3));
                sink += g.unify(x, y) as u64;
            }
            9 => {
                sink += g.instance(black_box(&fun5)) as u64;
                sink += g.instance(black_box(&fun5)) as u64;
            }
            10 => {
                let x = g.instance(black_box(&fun5));
                let y = g.instance(black_box(&fun5));
                sink += g.unify(x, y) as u64;
            }
            11 => {
                let v = g.push(Node { head: TAG_VAR, level: g.level, a: 0, b: 0 });
                sink += v as u64 + g.instance(black_box(&ground3)) as u64;
            }
            12 => {
                let v = g.push(Node { head: TAG_VAR, level: g.level, a: 0, b: 0 });
                let x = g.instance(black_box(&ground3));
                sink += g.unify(v, x) as u64;
            }
            13 => {
                // xs->Array.map(f) with xs: array<int>, f: int => string.
                let f = g.instance(black_box(&scheme7));
                let node = g.nodes[f as usize];
                let p0 = g.lists[node.b as usize];
                let p1 = g.lists[node.b as usize + 1];
                let xs = g.instance(black_box(&ground1));
                let int = xs;
                let array_int = g.push(Node { head: TAG_CONSTR | 1 << 8, level: g.level, a: ARRAY, b: g.lists.len() as u32 });
                g.lists.push(int);
                sink += g.unify(array_int, p0) as u64;
                let string = g.push(Node { head: TAG_CONSTR, level: g.level, a: STRING, b: 0 });
                let int2 = g.instance(black_box(&ground1));
                let arrow = g.push(Node { head: TAG_ARROW | 1 << 8, level: g.level, a: string, b: g.lists.len() as u32 });
                g.lists.push(int2);
                sink += g.unify(arrow, p1) as u64;
                sink += node.a as u64;
            }
            14 => {
                g.level += 1;
                let x = g.instance(black_box(&scheme7));
                g.level -= 1;
                g.generalize(x);
                sink += x as u64;
            }
            15 => sink += scopes.lookup(black_box((i & 0xfff) as u32)) as u64,
            16 => sink += scopes.binders[black_box((i & 0xfff) as usize)] as u64,
            17 => {
                let mark = scopes.log.len();
                sink += scopes.bind(black_box((i & 0xfff) as u32), i as u32) as u64;
                scopes.close(mark);
                scopes.binders.pop();
            }
            18 => sink += black_box(i),
            _ => unreachable!(),
        }
    }
    println!("{op} n={n} sink={sink} steps={}", g.steps);
    assert_eq!(std::mem::size_of::<Node>(), 16);
}
