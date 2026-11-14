//! R1 operations from docs/prototypes/checker-kernel, using the production
//! crate API (no cfg(test) counters or duplicate source modules).
//! Run: cargo bench --manifest-path compiler-rust/Cargo.toml --bench tc_kernel -- instance7 1000000
//! For instructions use cachegrind at N and zero, subtract empty; subtract
//! instance7 from generalize7. For unification subtract its `build_*` twin.
//! Names belong to R4.
//! `checker_instance1..7` are `instance1..7` through `Checker::instance`
//! with an empty nullary memo (R3b).
use rescript_compiler::tc::expand::TypeTable;
use rescript_compiler::tc::graph::{ARROW, CONSTR, GENERIC, Graph, NONE, Node, Param, Ty, VAR};
use rescript_compiler::tc::unify::Checker;
use std::hint::black_box;

/// O(arguments); build a setup-only constructor with its reserved memo slot.
fn constr(g: &mut Graph, id: u32, args: &[Ty]) -> Ty {
    constr_at(g, id, args, GENERIC)
}
/// O(arguments); setup-only construction at the requested definition level.
fn constr_at(g: &mut Graph, id: u32, args: &[Ty], level: u32) -> Ty {
    let b = g.lists.len() as u32;
    g.lists.push(Ty(NONE));
    g.lists.extend_from_slice(args);
    g.push(Node {
        head: CONSTR | (args.len() as u32) << 8,
        level,
        a: id,
        b,
    })
}
/// O(arguments); parameter metadata is included in R1's storage cost.
fn arrow(g: &mut Graph, args: &[Ty], result: Ty) -> Ty {
    let b = g.params.len() as u32;
    g.params.extend(args.iter().map(|&ty| Param {
        ty,
        label: 0,
        loc: 0,
    }));
    g.push(Node {
        head: ARROW | (args.len() as u32) << 8,
        level: GENERIC,
        a: result.0,
        b,
    })
}
/// O(1), construct one distinct variable.
fn var(g: &mut Graph) -> Ty {
    var_at(g, GENERIC)
}
/// O(1); setup-only fresh variable at the requested definition level.
fn var_at(g: &mut Graph, level: u32) -> Ty {
    g.push(Node {
        head: VAR,
        level,
        a: NONE,
        b: 0,
    })
}

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
    let ops = [
        "instance1",
        "instance3",
        "instance5",
        "instance7",
        "generalize7",
        "empty",
        "lower7",
        "copy7",
        "repr",
        "restore",
        "keep",
        "checker_instance1",
        "checker_instance3",
        "checker_instance5",
        "checker_instance7",
        "build_vars",
        "unify_vars",
        "build_ground1",
        "unify_ground1",
        "build_ground3",
        "unify_ground3",
        "build_vars_local",
        "unify_vars_local",
        "build_ground1_local",
        "unify_ground1_local",
        "build_ground3_local",
        "unify_ground3_local",
    ];
    let Some(index) = ops.iter().position(|&s| s == op) else {
        eprintln!(
            "operation {op} is not implemented by R1; supported: {}",
            ops.join(", ")
        );
        std::process::exit(2);
    };
    let index = black_box(index);
    let mut sink = 0u64;
    if index >= 15 {
        let local = index >= 21;
        let shape = ((index - 15) % 6) / 2;
        let unify = index % 2 == 0;
        let mut c = Checker::new(g, TypeTable::default());
        if local {
            c.g.begin_def();
        }
        let level = if local { c.g.level } else { GENERIC };
        // Both members of each pair build identical fresh operands and consume
        // identical handles. Subtract the build-only run, not the empty loop.
        for i in 0..n {
            if i & 0xfff == 0 {
                c.g.clear_instances();
            }
            let mut operand = || match shape {
                0 => var_at(&mut c.g, level),
                1 => constr_at(&mut c.g, 1, &[], level),
                2 => {
                    let left = constr_at(&mut c.g, 1, &[], level);
                    let right = constr_at(&mut c.g, 2, &[], level);
                    constr_at(&mut c.g, 3, &[left, right], level)
                }
                _ => unreachable!(),
            };
            let left = black_box(operand());
            let right = black_box(operand());
            if unify {
                c.unify(left, right).expect("equal benchmark operands");
            }
            sink += left.0 as u64 + right.0 as u64;
        }
        println!("{op} n={n} sink={}", black_box(sink));
        return;
    }
    if index >= 11 {
        let template = [ground1, ground3, fun5, scheme7][index - 11];
        let mut c = Checker::new(g, TypeTable::default());
        for i in 0..n {
            if i & 0xfff == 0 {
                c.g.clear_instances();
            }
            sink += c.instance(black_box(template)).0 as u64;
        }
        println!("{op} n={n} sink={}", black_box(sink));
        return;
    }
    for i in 0..n {
        if i & 0xfff == 0 {
            g.clear_instances();
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
                g.write(
                    root,
                    Node {
                        level: 2,
                        ..g.nodes[root.0 as usize]
                    },
                );
                if index == 9 {
                    g.restore(token);
                } else {
                    g.keep(token);
                }
                sink += root.0 as u64;
            }
            _ => unreachable!(),
        }
    }
    println!("{op} n={n} sink={}", black_box(sink));
}
