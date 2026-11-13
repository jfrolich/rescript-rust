//! R1 operations from docs/prototypes/checker-kernel. The same source modules
//! are compiled here because tc is deliberately not a public compiler API.
//! Run: cargo bench --manifest-path compiler-rust/Cargo.toml --bench tc_kernel -- instance7 1000000
//! For instructions use cachegrind at N and zero, subtract empty; subtract
//! instance7 from generalize7. Unification and names belong to R3 and R4.
#[path = "../src/tc/graph.rs"]
mod graph;
#[path = "../src/tc/level.rs"]
mod level;
#[path = "../src/tc/template.rs"]
mod template;
#[cfg(test)]
mod steps {
    /// O(1), compiled away: cargo bench sets cfg(test), but measurements
    /// must not include the unit-test thread-local counter.
    #[inline(always)]
    pub fn tick() {}
}

use graph::{ARROW, CONSTR, GENERIC, Graph, NONE, Node, Param, Ty, VAR};
use std::hint::black_box;

/// O(arguments); build a setup-only constructor with its reserved memo slot.
fn constr(g: &mut Graph, id: u32, args: &[Ty]) -> Ty {
    let b = g.lists.len() as u32;
    g.lists.push(Ty(NONE));
    g.lists.extend_from_slice(args);
    g.push(Node {head: CONSTR | (args.len() as u32) << 8, level: GENERIC, a: id, b})
}
/// O(arguments); parameter metadata is included in R1's storage cost.
fn arrow(g: &mut Graph, args: &[Ty], result: Ty) -> Ty {
    let b = g.params.len() as u32;
    g.params.extend(args.iter().map(|&ty| Param {ty, label: 0, loc: 0}));
    g.push(Node {head: ARROW | (args.len() as u32) << 8, level: GENERIC, a: result.0, b})
}
/// O(1), construct one distinct variable.
fn var(g: &mut Graph) -> Ty { g.push(Node {head: VAR, level: GENERIC, a: NONE, b: 0}) }

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let op = args.get(1).map(String::as_str).unwrap_or("empty");
    let n: u64 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(0);
    let mut g = Graph::default();
    let int = constr(&mut g, 1, &[]);
    let ground1 = g.capture(int);
    let i = constr(&mut g, 1, &[]);
    let array = constr(&mut g, 3, &[i]);
    let option = constr(&mut g, 4, &[array]);
    let ground3 = g.capture(option);
    let s = constr(&mut g, 2, &[]);
    let i = constr(&mut g, 1, &[]);
    let s2 = constr(&mut g, 2, &[]);
    let option = constr(&mut g, 4, &[s2]);
    let f = arrow(&mut g, &[s, i], option);
    let fun5 = g.capture(f);
    let a = var(&mut g);
    let b = var(&mut g);
    let array_a = constr(&mut g, 3, &[a]);
    let f = arrow(&mut g, &[a], b);
    let array_b = constr(&mut g, 3, &[b]);
    let f = arrow(&mut g, &[array_a, f], array_b);
    let scheme7 = g.capture(f);
    // The reference's "7" operation actually contains six distinct nodes.
    let ops = ["instance1", "instance3", "instance5", "instance7", "generalize7", "empty", "lower7", "copy7", "repr", "restore", "keep"];
    let Some(index) = ops.iter().position(|&s| s == op) else {
        eprintln!("operation {op} is not implemented by R1; supported: {}", ops.join(", "));
        std::process::exit(2);
    };
    let index = black_box(index);
    let mut sink = 0u64;
    for i in 0..n {
        if i & 0xfff == 0 {
            g.nodes.clear(); g.lists.clear(); g.params.clear(); g.forward.clear();
        }
        match index {
            0 => sink += g.instance(black_box(ground1)).0 as u64,
            1 => sink += g.instance(black_box(ground3)).0 as u64,
            2 => sink += g.instance(black_box(fun5)).0 as u64,
            3 => sink += g.instance(black_box(scheme7)).0 as u64,
            4 => {
                g.begin_def();
                let root = g.instance(black_box(scheme7));
                g.end_def();
                g.generalize(root);
                sink += root.0 as u64;
            }
            5 => sink += black_box(i),
            6 => {
                g.begin_def();
                let root = g.instance(black_box(scheme7));
                g.end_def();
                g.lower(root, 1);
                sink += root.0 as u64;
            }
            7 => {
                let root = g.instance(black_box(scheme7));
                g.level = 0;
                g.generalize(root);
                g.level = 1;
                sink += g.copy(root).0 as u64;
            }
            8 => {
                let root = g.instance(black_box(ground1));
                sink += g.repr(black_box(root)).0 as u64;
            }
            9 | 10 => {
                let root = g.instance(black_box(ground1));
                let token = g.speculate();
                g.write(root, Node {level: 2, ..g.nodes[root.0 as usize]});
                if index == 9 { g.restore(token); } else { g.keep(token); }
                sink += root.0 as u64;
            }
            _ => unreachable!(),
        }
    }
    println!("{op} n={n} sink={}", black_box(sink));
}
