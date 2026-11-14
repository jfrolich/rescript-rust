//! R1 operations from docs/prototypes/checker-kernel, using the production
//! crate API (no cfg(test) counters or duplicate source modules).
//! Run: cargo bench --manifest-path compiler-rust/Cargo.toml --bench tc_kernel -- instance7 1000000
//! For instructions use cachegrind at N and zero, subtract empty; subtract
//! instance7 from generalize7. For unification subtract its `build_*` twin.
//! The R4 operations (`binder` to `intern`, CHECKER_REWRITE.md section 9.3,
//! decision 5) take an interned `Name`; subtract the empty loop.
//! `checker_instance1..7` are `instance1..7` through `Checker::instance`
//! with an empty nullary memo (R3b).
use rescript_compiler::tc::expand::TypeTable;
use rescript_compiler::tc::graph::{ARROW, CONSTR, GENERIC, Graph, NONE, Node, Param, Ty, VAR};
use rescript_compiler::tc::name_table::Name;
use rescript_compiler::tc::scope::{Binder, BinderKind, Key, Namespace, Scopes};
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

/// O(layers x members): setup only. Scope 0 entered, then `layers` opened
/// tables of `members` values each, outermost first: layer `l` holds
/// `{l}{i}` for `i` below `members` (`a` is the outermost).
fn layered(layers: u8, members: u32) -> Scopes {
    let mut s = Scopes::new();
    s.enter();
    let mut rows = Vec::new();
    for l in 0..layers {
        rows.clear();
        for i in 0..members {
            let key = Key::new(
                s.names.intern(&format!("{}{i}", (b'a' + l) as char)),
                Namespace::Value,
            );
            rows.push((key, s.binders.push(key, i, 0, BinderKind::Let)));
        }
        let table = s.table_from(&rows);
        s.open(table, 0, 0, 0);
    }
    s
}
/// O(1): the value key of a name the setup interned.
fn value(s: &Scopes, text: &str) -> Key {
    Key::new(
        s.names.find(text).expect("interned by the setup"),
        Namespace::Value,
    )
}
/// The R4 operations; see the module comment.
fn names(op: &str, index: usize, n: u64) {
    let mut sink = 0u64;
    match index {
        // `binders.payload[b]` for a binder in an array of 1,000.
        27 => {
            let mut s = layered(0, 0);
            let key = Key::new(s.names.intern("x"), Namespace::Value);
            for i in 0..1_000 {
                s.binders.push(key, i, 0, BinderKind::Let);
            }
            for _ in 0..n {
                let b: Binder = black_box(Binder(537));
                sink += s.binders.payload[b.0 as usize] as u64;
            }
        }
        // `find` of a name bound after two opened layers of 256 members;
        // the name is also a member of the inner layer, which it hides.
        28 => {
            let mut s = layered(2, 256);
            let key = value(&s, "b100");
            let b = s.binders.push(key, 7, 0, BinderKind::Let);
            s.bind(b);
            for _ in 0..n {
                let found = s.find(black_box(key)).expect("bound");
                sink += found.item.0 as u64;
            }
        }
        // `find` of a name with no binding, in the inner of two layers.
        29 => {
            let s = layered(2, 256);
            let key = value(&s, "b100");
            for _ in 0..n {
                let found = s.find(black_box(key)).expect("a member");
                sink += found.item.0 as u64;
            }
        }
        // `find` of a name in the third layer after missing two.
        30 => {
            let s = layered(3, 256);
            let key = value(&s, "a100");
            for _ in 0..n {
                let found = s.find(black_box(key)).expect("a member");
                sink += found.item.0 as u64;
            }
        }
        // `enter`, `push`, `bind`, `leave`; the per-unit rows are reset to
        // the frozen prefix every 4,096 iterations, as instances are cleared.
        31 => {
            let mut s = layered(0, 0);
            let key = Key::new(s.names.intern("x"), Namespace::Value);
            s.freeze();
            for i in 0..n {
                if i & 0xfff == 0 {
                    s.reset();
                }
                s.enter();
                let b = s.binders.push(black_box(key), 0, 0, BinderKind::Let);
                s.bind(b);
                s.leave();
                sink += b.0 as u64;
            }
        }
        // `NameTable::intern` of an 8-byte name already in the table.
        32 => {
            let mut s = layered(1, 256);
            let text = "abcdefgh";
            s.names.intern(text);
            for _ in 0..n {
                let name: Name = s.names.intern(black_box(text));
                sink += name.0 as u64;
            }
        }
        _ => unreachable!(),
    }
    println!("{op} n={n} sink={}", black_box(sink));
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
        "binder",
        "find_local",
        "find_open",
        "find_miss2",
        "bind_leave",
        "intern",
    ];
    let Some(index) = ops.iter().position(|&s| s == op) else {
        eprintln!(
            "operation {op} is not implemented by R1; supported: {}",
            ops.join(", ")
        );
        std::process::exit(2);
    };
    let index = black_box(index);
    if index >= 27 {
        names(op, index, n);
        return;
    }
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
