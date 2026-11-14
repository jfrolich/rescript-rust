//! Acceptance tests of R3 (CHECKER_REWRITE.md, "R3 as designed"). The tests
//! on the old checker run today; the tests on the new graph are ignored
//! until the slice named in their `ignore` builds what they call. A builder
//! removes the `ignore` and changes nothing else in a test.
//!
//! The new-graph tests build nodes by hand and make the calls the walk will
//! make (R5), in OCaml's order: an application unifies the argument's type
//! with the parameter's (`unify env actual expected`).

use std::sync::Arc;

use super::differential::{Fault, Op, Tier, compare, compile};
use super::expand::{ABBREV, ALIAS, ExpandMode, Manifest, TypeInfo};
use super::graph::{ARROW, CONSTR, GENERIC, Graph, LINK, Mode, NONE, Node, Param, TUPLE, Ty, VAR};
use super::steps;
use super::template::Template;
use super::unify::Checker;

// Type indices of the hand-built declaration table.
const INT: u32 = 0;
const STRING: u32 = 1;
const UNIT: u32 = 2;
/// `type myint = int`
const MYINT: u32 = 3;
/// `type a = int`
const A: u32 = 4;
/// `type b = int`
const B: u32 = 5;
/// `type phantom<'a> = int`
const PHANTOM: u32 = 6;
/// `type cb = int => unit`
const CB: u32 = 7;
/// `type r = {n: int, m: int}`
const R: u32 = 8;
/// `type box<'a> = {value: 'a, count: myint}`
const BOX: u32 = 9;
/// `module M = { type t }`
const T: u32 = 10;
/// `module N = M`: `N.t`
const NT: u32 = 11;
/// `type pa<'x> = ('x, int)`
const PA: u32 = 12;
/// `type pb<'x> = ('x, int)`
const PB: u32 = 13;
const TYPES: usize = 14;

fn var_at(c: &mut Checker, level: u32) -> Ty {
    let serial = c.g.nodes.len() as u32;
    c.g.push(Node {
        head: VAR,
        level,
        a: NONE,
        b: serial,
    })
}

fn constr_at(c: &mut Checker, level: u32, ty: u32, args: &[Ty]) -> Ty {
    let b = c.g.lists.len() as u32;
    c.g.lists.push(Ty(NONE));
    c.g.lists.extend_from_slice(args);
    c.g.push(Node {
        head: CONSTR | (args.len() as u32) << 8,
        level,
        a: ty,
        b,
    })
}

fn tuple_at(c: &mut Checker, level: u32, elements: &[Ty]) -> Ty {
    let b = c.g.lists.len() as u32;
    c.g.lists.extend_from_slice(elements);
    c.g.push(Node {
        head: TUPLE | (elements.len() as u32) << 8,
        level,
        a: 0,
        b,
    })
}

fn arrow_at(c: &mut Checker, level: u32, params: &[Ty], result: Ty) -> Ty {
    let b = c.g.params.len() as u32;
    for &ty in params {
        c.g.params.push(Param {
            ty,
            label: NONE,
            loc: NONE,
        });
    }
    c.g.push(Node {
        head: ARROW | (params.len() as u32) << 8,
        level,
        a: result.0,
        b,
    })
}

/// A variable, a constructor, a tuple, an arrow at the current level.
fn var(c: &mut Checker) -> Ty {
    let level = c.g.level;
    var_at(c, level)
}
fn constr(c: &mut Checker, ty: u32, args: &[Ty]) -> Ty {
    let level = c.g.level;
    constr_at(c, level, ty, args)
}
fn tuple(c: &mut Checker, elements: &[Ty]) -> Ty {
    let level = c.g.level;
    tuple_at(c, level, elements)
}
fn arrow(c: &mut Checker, params: &[Ty], result: Ty) -> Ty {
    let level = c.g.level;
    arrow_at(c, level, params, result)
}

/// Declare `type_index` as an abbreviation with these generic parameter
/// nodes and this generic body: one template of the tuple
/// `(params.., body)`, as bridge/from_old.rs publishes a declaration.
fn abbreviation(c: &mut Checker, type_index: u32, params: &[Ty], body: Ty) {
    let mut roots = params.to_vec();
    roots.push(body);
    let scheme = tuple_at(c, GENERIC, &roots);
    let template = c.g.capture(scheme);
    // Right after a capture the forwarding row of a captured node holds its
    // template reference (tc/template.rs, `capture_ref`).
    let first = c.types.roots.len() as u32;
    for &param in params {
        let reference = Ty(c.g.forward[param.0 as usize].target);
        c.types.roots.push(reference);
    }
    let body = Ty(c.g.forward[body.0 as usize].target);
    let manifest = c.types.manifests.len() as u32;
    c.types.manifests.push(Manifest {
        template,
        params: first,
        body,
    });
    c.types.rows[type_index as usize] = TypeInfo {
        manifest,
        scope: 0,
        newtype: NONE,
        arity: params.len() as u16,
        flags: ABBREV,
        reserved: 0,
    };
}

/// A checker at level 2 (inside one definition) with the declarations above.
fn checker(mode: Mode) -> Checker {
    let graph = Graph {
        mode,
        ..Graph::default()
    };
    let mut c = Checker::new(graph, Default::default());
    c.types.rows = vec![
        TypeInfo {
            manifest: NONE,
            scope: 0,
            newtype: NONE,
            arity: 0,
            flags: 0,
            reserved: 0,
        };
        TYPES
    ];
    for (ty, arity) in [(PHANTOM, 1), (BOX, 1), (PA, 1), (PB, 1)] {
        c.types.rows[ty as usize].arity = arity;
    }
    for ty in [MYINT, A, B] {
        let body = constr_at(&mut c, GENERIC, INT, &[]);
        abbreviation(&mut c, ty, &[], body);
    }
    let param = var_at(&mut c, GENERIC);
    let body = constr_at(&mut c, GENERIC, INT, &[]);
    abbreviation(&mut c, PHANTOM, &[param], body);
    let int = constr_at(&mut c, GENERIC, INT, &[]);
    let unit = constr_at(&mut c, GENERIC, UNIT, &[]);
    let body = arrow_at(&mut c, GENERIC, &[int], unit);
    abbreviation(&mut c, CB, &[], body);
    for ty in [PA, PB] {
        let param = var_at(&mut c, GENERIC);
        let int = constr_at(&mut c, GENERIC, INT, &[]);
        let body = tuple_at(&mut c, GENERIC, &[param, int]);
        abbreviation(&mut c, ty, &[param], body);
    }
    c.types.rows[NT as usize] = TypeInfo {
        manifest: T,
        scope: 0,
        newtype: NONE,
        arity: 0,
        flags: ALIAS,
        reserved: 0,
    };
    c.g.begin_def();
    c
}

/// The type index in the representative of `ty`: the name it prints with (O1).
fn path(c: &mut Checker, ty: Ty) -> u32 {
    let ty = c.g.repr(ty);
    let node = c.g.nodes[ty.0 as usize];
    assert_eq!(node.tag(), CONSTR, "representative is not a constructor");
    node.a
}

/// A template of a generic scheme built by `build` one level up.
fn scheme(c: &mut Checker, build: impl FnOnce(&mut Checker) -> Ty) -> Template {
    c.g.begin_def();
    let root = build(c);
    c.g.end_def();
    c.g.generalize(root);
    c.g.capture(root)
}

/// The i-th child of a tuple or the i-th argument of a constructor.
fn child(c: &mut Checker, ty: Ty, index: u32) -> Ty {
    let ty = c.g.repr(ty);
    let node = c.g.nodes[ty.0 as usize];
    let first = node.b + u32::from(node.tag() == CONSTR);
    c.g.lists[(first + index) as usize]
}

// ---------------------------------------------------------------------------
// On the old checker, today: the evidence of decisions 1 to 3.
// ---------------------------------------------------------------------------

/// The canonical signature the old checker publishes for a program.
fn old_signature(source: &str) -> String {
    let program = compile(source.to_string());
    let ctx = crate::types::context::TypeContext::new(Arc::new(crate::context::IdGenerator::new()));
    let unit = crate::cmi::portable_types::internalize_pers_struct(program.unit.clone(), &ctx);
    crate::types::canonical_sig::canonical_signature(&ctx, "Case", &unit.ps_sig, None, None)
}

fn assert_lines(signature: &str, lines: &[&str]) {
    for line in lines {
        assert!(
            signature.lines().any(|found| found == *line),
            "missing line\n{line}\nin\n{signature}"
        );
    }
}

/// Decision 3 (O11). The memo of nullary abbreviations shows in a canonical
/// signature: after one application of `f`, a later instance of `f` in the
/// same definition has both its `N.t` (and `a`) nodes linked to the result
/// node of the first instance (`@3`). Without an application nothing is
/// shared, and an abbreviation with an argument is never shared.
#[test]
fn old_checker_nullary_memo_shows_in_the_canonical_signature() {
    let signature = old_signature(
        "module M = { type t }\nmodule N = M\n\
         let f = (x: N.t) => x\n\
         let twice = j => (f(j), f)\n\
         let noapp = (f, f)\n\
         let twoapps = (j, k) => (f(j), f(k))\n\
         type a = int\n\
         let fa = (x: a) => x\n\
         let twicea = j => (fa(j), fa)\n\
         let noappa = (fa, fa)\n\
         type p<'x> = ('x, int)\n\
         let fp = (x: p<string>) => x\n\
         let twicep = j => (fp(j), fp)\n",
    );
    assert_lines(
        &signature,
        &[
            "value twice: &0((&1(N.t)) => &2(tuple(&3(N.t), &4((@3) => @3))))",
            "value noapp: &0(tuple(&1((&2(N.t)) => &3(N.t)), &4((&5(N.t)) => &6(N.t))))",
            "value twoapps: &0((&1(N.t), &2(N.t)) => &3(tuple(@2, @2)))",
            "value twicea: &0((&1(a)) => &2(tuple(&3(a), &4((@3) => @3))))",
            "value noappa: &0(tuple(&1((&2(a)) => &3(a)), &4((&5(a)) => &6(a))))",
            "value twicep: &0((&1(p<&2(string)>)) => &3(tuple(&4(p<&5(string)>), &6((&7(p<&8(string)>)) => &9(p<&10(string)>)))))",
        ],
    );
}

/// Decision 2 (the abbreviation case of O5). Unifying a node of one
/// abbreviation with a node of another leaves two nodes with two names: the
/// result of `same(x, y)` is named by its first argument and the other
/// argument keeps its own name, in both orders, for nullary and for
/// parameterised abbreviations. A plain node unified with an abbreviation
/// takes the abbreviation's name in both orders (fixture 1).
#[test]
fn old_checker_abbreviation_pair_keeps_two_nodes() {
    let signature = old_signature(
        "type a = int\ntype b = int\n\
         type pa<'x> = ('x, int)\ntype pb<'x> = ('x, int)\n\
         let same = (x, y) => if true { x } else { y }\n\
         let nullary = (x: a, y: b) => (same(x, y), x, y)\n\
         let nullary_rev = (x: a, y: b) => (same(y, x), x, y)\n\
         let param = (x: pa<string>, y: pb<string>) => (same(x, y), x, y)\n\
         let param_rev = (x: pa<string>, y: pb<string>) => (same(y, x), x, y)\n\
         let plain = (x: a, y: int) => (same(x, y), x, y)\n\
         let plain_rev = (x: a, y: int) => (same(y, x), x, y)\n",
    );
    assert_lines(
        &signature,
        &[
            "value nullary: &0((&1(a), &2(b)) => &3(tuple(&4(a), @4, &5(b))))",
            "value nullary_rev: &0((&1(a), &2(b)) => &3(tuple(&4(b), &5(a), @4)))",
            "value param: &0((&1(pa<&2(string)>), &3(pb<&4(string)>)) => &5(tuple(&6(pa<&7(string)>), &8(pa<&9(string)>), &10(pb<&11(string)>))))",
            "value param_rev: &0((&1(pa<&2(string)>), &3(pb<&4(string)>)) => &5(tuple(&6(pb<&7(string)>), &8(pa<&9(string)>), &10(pb<&11(string)>))))",
            "value plain: &0((&1(a), &2(int)) => &3(tuple(&4(a), @4, &5(int))))",
            "value plain_rev: &0((&1(a), &2(int)) => &3(tuple(&4(a), @4, &5(int))))",
        ],
    );
}

/// The program of decision 1: positions that are one node in the exporter,
/// positions that are equal but two nodes, and a scheme with both.
const SHARING: &str = "let dup = x => (x, x)\n\
    let two = (1, 2)\n\
    type a = int\n\
    let pair = (x: a) => (x, x)\n\
    external both: ('a, 'a, int, int) => ('a, int) = \"both\"\n";

/// Decision 1. An instance built from a segment shares exactly the nodes
/// the old checker's instance of the same value shares: for every value,
/// two instances are compared in the harness's form, which numbers shared
/// nodes. `dup`'s components are one node, `two`'s are two.
#[test]
fn instance_from_a_segment_shares_what_the_old_instance_shares() {
    let program = compile(SHARING.to_string());
    assert_eq!(program.values, ["dup", "two", "pair", "both"]);
    for value in 0..program.values.len() as u16 {
        let ops = [Op::BeginDef, Op::Instance(value), Op::Instance(value)];
        let outcome = compare(u64::from(value), &program, Tier::Kernel, &ops, Fault::None)
            .unwrap_or_else(|report| panic!("{report}"));
        let shares = outcome.form.contains('@');
        // `dup` and `both` have a node at two positions. `two` has two equal
        // nodes, and each use of the annotated `x` of `pair` is a copy (O10).
        assert_eq!(shares, value == 0 || value == 3, "{}", outcome.form);
    }
}

/// The harness's kernel tier found that R1's instance keeps a variable's
/// name where the old checker's drops it (`copy_type_desc`,
/// compiler/ml/btype.ml:510: `Tvar _ as ty -> if keep_names then ty else
/// Tvar None`). Above the kernel tier the form prints names, so this
/// compares them: an instance and a copy of a scheme with named variables.
#[test]
fn instance_drops_variable_names() {
    let program = compile(SHARING.to_string());
    let ops = [Op::BeginDef, Op::Instance(3), Op::EndDef, Op::Generalize(0), Op::Copy(0)];
    let outcome = compare(0, &program, Tier::Expand, &ops, Fault::None)
        .unwrap_or_else(|report| panic!("{report}"));
    assert!(!outcome.form.contains("'a"), "{}", outcome.form);
}

/// The same with the memo-aware instance of R3b.
#[test]
fn memo_aware_instance_shares_what_the_old_instance_shares() {
    let program = compile(SHARING.to_string());
    for value in 0..program.values.len() as u16 {
        let ops = [Op::BeginDef, Op::Instance(value), Op::Instance(value)];
        compare(u64::from(value), &program, Tier::Expand, &ops, Fault::None)
            .unwrap_or_else(|report| panic!("{report}"));
    }
}

// ---------------------------------------------------------------------------
// R3a: variables, structures, the two modes.
// ---------------------------------------------------------------------------

/// `n` one-element tuples around an `int`, all at the current level.
fn chain(c: &mut Checker, n: u32) -> Ty {
    let mut ty = constr(c, INT, &[]);
    for _ in 1..n {
        ty = tuple(c, &[ty]);
    }
    ty
}

/// A tuple of `n` one-element tuples, each around its own `int`:
/// `2n + 1` nodes, no subtree below the root larger than two nodes.
fn wide(c: &mut Checker, n: u32) -> Ty {
    let mut elements = Vec::new();
    for _ in 0..n {
        let int = constr(c, INT, &[]);
        elements.push(tuple(c, &[int]));
    }
    tuple(c, &elements)
}

#[test]
fn unify_of_equal_wide_types_is_linear() {
    let mut c = checker(Mode::Success);
    let (left, right) = (wide(&mut c, 5000), wide(&mut c, 5000));
    let pairs = 10_001;
    let nodes = c.g.nodes.len();
    let count = steps::scope(|| c.unify(left, right).unwrap());
    // Each pair: the pair itself, two pruned level walks, and the
    // occurrence walk of its right side (at most 2 nodes below the root;
    // the root's walk is the whole type once).
    assert!(count <= 8 * pairs, "{count} steps for {pairs} pairs");
    assert_eq!(c.g.nodes.len(), nodes, "unification of equal types makes no node");
    assert_eq!(c.g.repr(left), c.g.repr(right));
    // The link was written left to right (compiler/ml/ctype.ml:2331).
    assert_eq!(c.g.repr(left), right);
    // Again: one link to follow, nothing else.
    assert!(steps::scope(|| c.unify(left, right).unwrap()) <= 1);
    assert!(c.g.trail.is_empty(), "Mode::Success logs nothing");
}

/// A chain 10,000 deep runs on a 2 MB stack. Its cost is OCaml's: one
/// occurrence walk per structure pair over the right side
/// (compiler/ml/ctype.ml:2330), so the sum of the subtree sizes, plus at
/// most 260 steps a pair for everything else.
#[test]
fn unify_of_equal_deep_types_fits_the_stack() {
    std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .spawn(|| {
            let mut c = checker(Mode::Success);
            let n = 10_000u64;
            let (left, right) = (chain(&mut c, n as u32), chain(&mut c, n as u32));
            let count = steps::scope(|| c.unify(left, right).unwrap());
            assert!(count >= n);
            assert!(count <= n * (n + 1) / 2 + 260 * n, "{count}");
            assert_eq!(c.g.repr(left), right);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn binding_a_variable_is_one_walk_of_the_type() {
    std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .spawn(|| {
            // The type at the variable's level: nothing to lower.
            let mut c = checker(Mode::Success);
            let ty = chain(&mut c, 10_000);
            let v = var(&mut c);
            let count = steps::scope(|| c.unify(v, ty).unwrap());
            assert!(count <= 20_000, "{count}");
            assert_eq!(c.g.repr(v), ty);

            // The type above the variable's level: the same walk lowers it.
            let mut c = checker(Mode::Success);
            let v = var(&mut c);
            c.g.begin_def();
            let ty = chain(&mut c, 10_000);
            let count = steps::scope(|| c.unify(v, ty).unwrap());
            assert!(count <= 20_000, "{count}");
            let level = c.g.nodes[v.0 as usize].level;
            assert!(c.g.nodes[ty.0 as usize].level == level);
            assert!(c.g.nodes.iter().all(|node| node.level <= level || node.level == GENERIC));

            // The type's root below the variable's level: still one walk,
            // because the occurrence test has no level cut (next test).
            let mut c = checker(Mode::Success);
            let ty = chain(&mut c, 10_000);
            c.g.begin_def();
            let v = var(&mut c);
            let count = steps::scope(|| c.unify(v, ty).unwrap());
            assert!(count <= 20_000, "{count}");
            assert_eq!(c.g.repr(v), ty);
        })
        .unwrap()
        .join()
        .unwrap();
}

/// A node below a variable's level can hold the variable (a node made after
/// `end_def` around a variable of the definition): the binding must fail
/// (O13), so the occurrence test cannot stop at a lower level.
#[test]
fn binding_finds_the_variable_under_a_lower_root() {
    let mut c = checker(Mode::Success);
    c.g.begin_def();
    let v = var(&mut c);
    c.g.end_def();
    let holder = tuple(&mut c, &[v]);
    assert!(c.g.nodes[holder.0 as usize].level < c.g.nodes[v.0 as usize].level);
    assert!(c.unify(v, holder).is_err());
    let mut c = checker(Mode::Success);
    c.g.begin_def();
    let v = var(&mut c);
    c.g.end_def();
    let holder = tuple(&mut c, &[v]);
    assert!(c.unify(holder, v).is_err());
}

/// `update_level` stops at a node that is not above the target level and
/// does not look below it (`if ty.level > level`,
/// compiler/ml/ctype.ml:586): a node above the target that is reached only
/// through such a node keeps its level, and one that is also a child of a
/// lowered node is lowered, in whichever order the walk meets the two
/// paths. The occurrence test of a binding goes everywhere; its level
/// update does not. Both modes leave the same levels: `Mode::Explain` runs
/// OCaml's two walks, `Mode::Success` the combined one. Added in review of
/// R3a; expected values from the OCaml lines, not from a run.
#[test]
fn binding_lowers_only_what_update_level_reaches() {
    fn level(c: &Checker, ty: Ty) -> u32 {
        c.g.nodes[ty.0 as usize].level
    }
    for (explain, mode) in [(false, Mode::Success), (true, Mode::Explain)] {
        for shield_first in [false, true] {
            // `checker` returns at level 2: the variable's level.
            let mut c = checker(mode);
            let v = var(&mut c);
            assert_eq!(level(&c, v), 2);
            let hidden = constr_at(&mut c, 4, INT, &[]);
            let shared = constr_at(&mut c, 4, INT, &[]);
            // Not above the variable: the level update stops here.
            let shield = tuple_at(&mut c, 1, &[hidden, shared]);
            let top = constr_at(&mut c, 4, STRING, &[]);
            let children = if shield_first {
                [shield, shared, top]
            } else {
                [top, shared, shield]
            };
            let root = tuple_at(&mut c, 4, &children);
            c.unify(v, root).unwrap();
            let case = (explain, shield_first);
            assert_eq!(c.g.repr(v), root, "{case:?}");
            assert_eq!(level(&c, root), 2, "{case:?}");
            assert_eq!(level(&c, top), 2, "{case:?}");
            assert_eq!(level(&c, shield), 1, "{case:?}");
            assert_eq!(level(&c, shared), 2, "{case:?}: a child of the lowered root");
            assert_eq!(level(&c, hidden), 4, "{case:?}: only below the shield");
        }
        // A root that is not above the variable: nothing is lowered.
        let mut c = checker(mode);
        let v = var(&mut c);
        let hidden = constr_at(&mut c, 4, INT, &[]);
        let root = tuple_at(&mut c, 2, &[hidden]);
        c.unify(v, root).unwrap();
        assert_eq!(level(&c, hidden), 4, "explain {explain}");
    }
}

/// Links are written in OCaml's direction (O2, CHECKER_REDESIGN I.2.1).
#[test]
fn link_directions() {
    let mut c = checker(Mode::Success);
    // A variable becomes the other node, whichever side it is on.
    let (v, int) = (var(&mut c), constr(&mut c, INT, &[]));
    c.unify(v, int).unwrap();
    assert_eq!(c.g.repr(v), int);
    let (v, int) = (var(&mut c), constr(&mut c, INT, &[]));
    c.unify(int, v).unwrap();
    assert_eq!(c.g.repr(v), int);
    // Two variables: the left one links to the right one.
    let (l, r) = (var(&mut c), var(&mut c));
    c.unify(l, r).unwrap();
    assert_eq!(c.g.repr(l), r);
    // Two nullary constructors of one type: left to right, and the right
    // one is lowered to the left one's level (`update_level !env t1.level
    // t2; link_type t1 t2`, ctype.ml:2248-2257). `checker` returns inside
    // one definition, so the left node is made at level 2 and the right one
    // at level 3, and the survivor ends at 2.
    let l = constr(&mut c, INT, &[]);
    assert_eq!(c.g.nodes[l.0 as usize].level, 2);
    c.g.begin_def();
    let r = constr(&mut c, INT, &[]);
    assert_eq!(c.g.nodes[r.0 as usize].level, 3);
    c.unify(l, r).unwrap();
    assert_eq!(c.g.repr(l), r);
    assert_eq!(c.g.nodes[r.0 as usize].level, 2);
    // Structures: left to right, before the children: the children of the
    // right node are the survivors.
    let (li, ri) = (constr(&mut c, INT, &[]), constr(&mut c, INT, &[]));
    let (l, r) = (tuple(&mut c, &[li]), tuple(&mut c, &[ri]));
    c.unify(l, r).unwrap();
    assert_eq!(c.g.repr(l), r);
    assert_eq!(c.g.repr(li), ri);
    // Different constructors, different lengths, an arrow against a tuple.
    let (i, s) = (constr(&mut c, INT, &[]), constr(&mut c, STRING, &[]));
    assert!(c.unify(i, s).is_err());
    let (i, j) = (constr(&mut c, INT, &[]), constr(&mut c, INT, &[]));
    let (one, two) = (tuple(&mut c, &[i]), tuple(&mut c, &[i, j]));
    assert!(c.unify(one, two).is_err());
    let f = arrow(&mut c, &[i], j);
    assert!(c.unify(f, one).is_err());
}

/// Decision 5: in `Mode::Success` a top-level unification opens no
/// speculation and logs nothing; a failure sets `unexplained_failure` and
/// leaves no trace. What it wrote stays written: the unit is checked again.
#[test]
fn success_mode_keeps_nothing_for_a_failure() {
    let mut c = checker(Mode::Success);
    let (i, s) = (constr(&mut c, INT, &[]), constr(&mut c, STRING, &[]));
    let (v, w) = (var(&mut c), var(&mut c));
    let (l, r) = (tuple(&mut c, &[v, i]), tuple(&mut c, &[w, s]));
    assert!(c.unify(l, r).is_err());
    assert!(c.unexplained_failure);
    assert!(c.g.trail.is_empty() && c.trace.is_empty() && c.saved.is_empty());
    assert_eq!(c.g.speculation_depth, 0);
    assert_eq!(c.depth, 0);
    assert!(c.frames.is_empty(), "the stack is emptied on failure");

    // Under a speculation the failure is the speculation's owner's: it is
    // not unexplained, and a restore puts every node back.
    let mut c = checker(Mode::Success);
    let (i, s) = (constr(&mut c, INT, &[]), constr(&mut c, STRING, &[]));
    let (v, w) = (var(&mut c), var(&mut c));
    let (l, r) = (tuple(&mut c, &[v, i]), tuple(&mut c, &[w, s]));
    let before = c.g.nodes.clone();
    let token = c.g.speculate();
    assert!(c.unify(l, r).is_err());
    assert!(!c.unexplained_failure);
    c.g.restore(token);
    assert_eq!(c.g.nodes, before);
}

/// Decision 5: in `Mode::Explain` a top-level unification opens a
/// speculation; a success keeps it (the trail is empty afterwards); a
/// failure undoes path compression only, restores the linked structure's
/// descriptor (`t1'.desc <- d1`), keeps the trace and is not unexplained.
#[test]
fn explain_mode_keeps_the_trace_and_undoes_compression() {
    let mut c = checker(Mode::Explain);
    let (l, r) = (var(&mut c), var(&mut c));
    c.unify(l, r).unwrap();
    assert!(c.g.trail.is_empty() && c.trace.is_empty());
    assert_eq!(c.g.speculation_depth, 0);

    // v0 -> v1 -> v2 -> int: a chain a `repr` would compress.
    let int = constr(&mut c, INT, &[]);
    let v2 = var(&mut c);
    let v1 = var(&mut c);
    let v0 = var(&mut c);
    for (from, to) in [(v2, int), (v1, v2), (v0, v1)] {
        c.g.nodes[from.0 as usize] = Node {
            head: LINK,
            level: 2,
            a: to.0,
            b: 0,
        };
    }
    let s = constr(&mut c, STRING, &[]);
    let w = var(&mut c);
    let (l, r) = (tuple(&mut c, &[w, v0]), tuple(&mut c, &[int, s]));
    assert!(c.unify(l, r).is_err());
    assert!(!c.unexplained_failure);
    assert_eq!(c.trace.first(), Some(&[l, r]), "outermost pair first");
    assert_eq!(c.trace.len(), 2);
    // Compression undone, the variable's binding kept, the tuple restored.
    assert_eq!(c.g.nodes[v0.0 as usize].a, v1.0);
    assert_eq!(c.g.repr(w), int);
    assert_eq!(c.g.nodes[l.0 as usize].tag(), TUPLE);
    assert!(c.g.trail.is_empty());
    assert_eq!(c.g.speculation_depth, 0);
}

/// Decision 6 of section 8.6: in `Mode::Explain`, outside a speculation
/// whose owner restores, a binding checks occurrence before it writes a
/// level (`occur`, then `link_type`, then `update_level`;
/// compiler/ml/ctype.ml:2216-2225). A failed top-level unification there
/// undoes path compression only, so this pins that a binding that fails on
/// occurrence leaves every level of the type as it was, although the type
/// has nodes above the variable's level that the combined walk of
/// `Mode::Success` would have lowered before it met the variable.
#[test]
fn explain_mode_binding_fails_before_it_lowers() {
    let mut c = checker(Mode::Explain);
    let v = var(&mut c);
    c.g.begin_def();
    let int = constr(&mut c, INT, &[]);
    let inner = tuple(&mut c, &[int]);
    let holder = tuple(&mut c, &[v, inner]);
    c.g.end_def();
    let levels: Vec<u32> = c.g.nodes.iter().map(|node| node.level).collect();
    assert!(levels[holder.0 as usize] > levels[v.0 as usize]);
    assert!(c.unify(v, holder).is_err());
    let after: Vec<u32> = c.g.nodes.iter().map(|node| node.level).collect();
    assert_eq!(after, levels, "no level was written");
    assert_eq!(c.g.nodes[v.0 as usize].tag(), VAR);
    assert!(c.g.trail.is_empty());
    assert_eq!(c.g.speculation_depth, 0);
    assert!(!c.unexplained_failure);
}

// ---------------------------------------------------------------------------
// R3b: expansion and the two memos.
// ---------------------------------------------------------------------------

#[test]
fn expansion_is_memorized_per_node_and_per_nullary_type() {
    let mut c = checker(Mode::Success);
    // Nullary: every node of the type shares one expansion while the memo
    // lives (`simple_abbrevs`, compiler/ml/ctype.ml:200).
    let (a1, a2) = (constr(&mut c, A, &[]), constr(&mut c, A, &[]));
    let e1 = c.expand_head(a1, ExpandMode::Safe).unwrap();
    assert_eq!(path(&mut c, e1), INT);
    assert_eq!(path(&mut c, a1), A, "expansion does not link the node");
    let nodes = c.g.nodes.len();
    for _ in 0..10_000 {
        assert_eq!(c.expand_head(a1, ExpandMode::Safe).unwrap(), e1);
        assert_eq!(c.expand_head(a2, ExpandMode::Safe).unwrap(), e1);
    }
    assert_eq!(c.g.nodes.len(), nodes, "a memo hit makes no node");
    assert_eq!(c.find_repr(A), a1);
    assert_eq!(c.find_repr(B).0, NONE);
    // The nullary memo is not in slot 0, so generalize does not visit it.
    assert_eq!(c.g.lists[c.g.nodes[a1.0 as usize].b as usize].0, NONE);

    // With an argument: slot 0 of the node, one expansion per node.
    let s = constr(&mut c, STRING, &[]);
    let (p1, p2) = (constr(&mut c, PA, &[s]), constr(&mut c, PA, &[s]));
    let x1 = c.expand_head(p1, ExpandMode::Safe).unwrap();
    let x2 = c.expand_head(p2, ExpandMode::Safe).unwrap();
    assert_ne!(x1, x2);
    assert_eq!(c.g.nodes[x1.0 as usize].tag(), TUPLE);
    // The parameter is bound to the argument node itself.
    let first = child(&mut c, x1, 0);
    assert_eq!(c.g.repr(first), s);
    assert_eq!(c.find_expansion(p1, false), x1);
    let nodes = c.g.nodes.len();
    assert_eq!(c.expand_head(p1, ExpandMode::Safe).unwrap(), x1);
    assert_eq!(c.g.nodes.len(), nodes);

    // Cleanup forgets both memos; the next expansion is a new node.
    c.cleanup_abbrev();
    assert_eq!(c.find_repr(A).0, NONE);
    assert_eq!(c.find_expansion(p1, false).0, NONE);
    assert_ne!(c.expand_head(a1, ExpandMode::Safe).unwrap(), e1);
    // A change of scope is a cleanup; the same scope is not.
    c.set_env(7);
    let e = c.expand_head(a1, ExpandMode::Safe).unwrap();
    c.set_env(7);
    assert_eq!(c.expand_head(a2, ExpandMode::Safe).unwrap(), e);
    c.set_env(8);
    assert_ne!(c.expand_head(a2, ExpandMode::Safe).unwrap(), e);
    // An abstract type does not expand; a phantom parameter is dropped (O9).
    let i = constr(&mut c, INT, &[]);
    assert_eq!(c.expand_head(i, ExpandMode::Safe).unwrap(), i);
    let v = var(&mut c);
    let ph = constr(&mut c, PHANTOM, &[v]);
    let e = c.expand_head(ph, ExpandMode::Safe).unwrap();
    assert_eq!(path(&mut c, e), INT);
    // A path through a module alias expands to the type it names.
    let nt = constr(&mut c, NT, &[]);
    let e = c.expand_head(nt, ExpandMode::Safe).unwrap();
    assert_eq!(path(&mut c, e), T);
    assert_eq!(path(&mut c, nt), NT);
}

/// O11 on the new graph: while the nullary memo names a node, every copy of
/// a nullary constructor of that type is a link to it; after a cleanup, and
/// for a type with an argument, a copy is its own node.
#[test]
fn a_copy_of_a_nullary_constructor_links_to_the_memorized_node() {
    for ty in [A, NT] {
        let mut c = checker(Mode::Success);
        let f = scheme(&mut c, |c| {
            let (x, y) = (constr(c, ty, &[]), constr(c, ty, &[]));
            arrow(c, &[x], y)
        });
        let first = c.instance(f);
        let second = c.instance(f);
        // No memo: nothing is shared (`noapp`).
        let (r1, r2) = (Ty(c.g.nodes[first.0 as usize].a), Ty(c.g.nodes[second.0 as usize].a));
        assert_ne!(c.g.repr(r1), c.g.repr(r2));
        // Expanding the first result memorizes that node (`twice`).
        c.expand_head(r1, ExpandMode::Safe).unwrap();
        let third = c.instance(f);
        let node = c.g.nodes[third.0 as usize];
        let (param, result) = (c.g.params[node.b as usize].ty, Ty(node.a));
        assert_eq!(c.g.repr(param), r1);
        assert_eq!(c.g.repr(result), r1);
        assert_eq!(path(&mut c, result), ty);
        // The general copy makes the same lookup.
        c.g.begin_def();
        let local = constr(&mut c, ty, &[]);
        c.g.end_def();
        c.g.generalize(local);
        let copied = c.copy(local);
        assert_eq!(c.g.repr(copied), r1);
        // After a cleanup a copy is its own node again.
        c.cleanup_abbrev();
        let fourth = c.instance(f);
        let result = Ty(c.g.nodes[fourth.0 as usize].a);
        assert_eq!(c.g.repr(result), result);
    }
    // With an argument the copy never links (`twicep`).
    let mut c = checker(Mode::Success);
    let f = scheme(&mut c, |c| {
        let s = constr(c, STRING, &[]);
        constr(c, PA, &[s])
    });
    let first = c.instance(f);
    c.expand_head(first, ExpandMode::Safe).unwrap();
    let second = c.instance(f);
    assert_eq!(c.g.repr(second), second);
    assert_ne!(first, second);
}

/// `simple_abbrevs () := Mnil` (compiler/ml/ctype.ml:519, 543): a
/// generalization forgets the nullary memo, so a later copy of a nullary
/// constructor is its own node again. `Graph::generalize` alone forgets
/// nothing (the test above relies on it).
#[test]
fn a_generalization_forgets_the_nullary_memo() {
    for structure in [false, true] {
        let mut c = checker(Mode::Success);
        let f = scheme(&mut c, |c| {
            let (x, y) = (constr(c, A, &[]), constr(c, A, &[]));
            arrow(c, &[x], y)
        });
        let first = c.instance(f);
        let r1 = Ty(c.g.nodes[first.0 as usize].a);
        c.expand_head(r1, ExpandMode::Safe).unwrap();
        let second = c.instance(f);
        let shared = Ty(c.g.nodes[second.0 as usize].a);
        assert_eq!(c.g.repr(shared), r1);
        assert_ne!(c.memo.live, 0);
        let generation = c.memo.generation;
        let root = var(&mut c);
        if structure {
            let level = c.g.level;
            c.generalize_structure(root, level);
        } else {
            c.generalize(root);
        }
        assert_eq!(c.memo.live, 0);
        assert_eq!(c.memo.generation, generation + 1);
        let third = c.instance(f);
        let result = Ty(c.g.nodes[third.0 as usize].a);
        assert_eq!(c.g.repr(result), result);
        assert_ne!(result, r1);
        // With no live row a generalization leaves the generation alone.
        let root = var(&mut c);
        c.generalize(root);
        assert_eq!(c.memo.generation, generation + 1);
    }
}

/// Decision 4: with an empty nullary memo the memo-aware instance is R1's
/// instance: the same nodes, the same steps.
#[test]
fn instance_with_an_empty_memo_costs_what_r1_costs() {
    let build = |c: &mut Checker| {
        scheme(c, |c| {
            let mut ty = constr(c, A, &[]);
            for _ in 1..10_000 {
                let other = constr(c, A, &[]);
                ty = tuple(c, &[ty, other]);
            }
            ty
        })
    };
    let mut plain = checker(Mode::Success);
    let template = build(&mut plain);
    let before = plain.g.nodes.len();
    let r1 = steps::scope(|| {
        plain.g.instance(template);
    });
    let made = plain.g.nodes.len() - before;

    let mut c = checker(Mode::Success);
    let template = build(&mut c);
    let before = c.g.nodes.len();
    let empty = steps::scope(|| {
        c.instance(template);
    });
    assert_eq!(empty, r1);
    assert_eq!(c.g.nodes.len() - before, made);

    // With a live memo: one lookup more per nullary constructor copied.
    let a = constr(&mut c, A, &[]);
    c.expand_head(a, ExpandMode::Safe).unwrap();
    let live = steps::scope(|| {
        c.instance(template);
    });
    assert!(live <= r1 + 2 * 10_000, "{live} against {r1}");
}

// ---------------------------------------------------------------------------
// R3d: lowering with scopes, and the walk an application runs.
// ---------------------------------------------------------------------------

/// Without a scoped type, the checked lowering is R1's: the same levels,
/// the same steps.
#[test]
fn lower_without_scopes_costs_what_r1_costs() {
    let mut plain = checker(Mode::Success);
    plain.g.begin_def();
    let ty = chain(&mut plain, 10_000);
    let r1 = steps::scope(|| plain.g.lower(ty, 1));
    let mut c = checker(Mode::Success);
    c.g.begin_def();
    let ty = chain(&mut c, 10_000);
    let count = steps::scope(|| c.lower(ty, 1).unwrap());
    assert_eq!(count, r1);
    assert!(c.g.nodes.iter().all(|node| node.level == 1 || node.level == GENERIC));
    assert!(c.g.trail.is_empty());
}

/// O12: a constructor cannot be lowered below its scope; an abbreviation is
/// replaced by its expansion to avoid that (compiler/ml/ctype.ml:590-600),
/// which renames the node.
#[test]
fn lower_checks_scopes_and_expands_to_escape() {
    let mut c = checker(Mode::Success);
    c.types.rows[T as usize].scope = 2;
    c.types.rows[A as usize].scope = 2;
    c.types.scoped = 2;
    c.g.begin_def();
    // An abstract type below its scope: a clash, and nothing stays lowered
    // below the scope's level in a node of that type.
    let t = constr(&mut c, T, &[]);
    let holder = tuple(&mut c, &[t]);
    assert!(c.lower(holder, 1).is_err());
    assert!(c.lower(holder, 2).is_ok());
    assert_eq!(c.g.nodes[t.0 as usize].level, 2);
    // An abbreviation below its scope: the node becomes its expansion.
    c.g.begin_def();
    let a = constr(&mut c, A, &[]);
    let holder = tuple(&mut c, &[a]);
    c.lower(holder, 1).unwrap();
    assert_eq!(path(&mut c, a), INT);
    let a = c.g.repr(a);
    assert_eq!(c.g.nodes[a.0 as usize].level, 1);
    assert!(c.g.trail.is_empty());
    assert_eq!(c.g.speculation_depth, 0);
}

/// Decision 3 on the new graph, as the old checker reaches it: an
/// application lowers the callee's instance (`lower_args`), which expands
/// the result; a later instance of the same scheme then has both its
/// nullary nodes linked to the first instance's result node.
#[test]
fn an_application_memorizes_the_result_node() {
    for ty in [A, NT] {
        let mut c = checker(Mode::Success);
        let f = scheme(&mut c, |c| {
            let (x, y) = (constr(c, ty, &[]), constr(c, ty, &[]));
            arrow(c, &[x], y)
        });
        // `f(j)`.
        let j = var(&mut c);
        let callee = c.instance(f);
        c.lower_args(callee);
        let node = c.g.nodes[callee.0 as usize];
        let (param, result) = (c.g.params[node.b as usize].ty, Ty(node.a));
        c.unify(j, param).unwrap();
        // `f` again, in the same definition.
        let again = c.instance(f);
        let node = c.g.nodes[again.0 as usize];
        let (param2, result2) = (c.g.params[node.b as usize].ty, Ty(node.a));
        // twice: &0((&1(a)) => &2(tuple(&3(a), &4((@3) => @3))))
        assert_eq!(c.g.repr(result2), result);
        assert_eq!(c.g.repr(param2), result);
        assert_ne!(c.g.repr(j), result, "the first parameter is its own node");
        assert_eq!(c.g.repr(j), param);
        assert_eq!(path(&mut c, result), ty);
    }
}

// ---------------------------------------------------------------------------
// R3c: abbreviations in unification. The fixtures of CHECKER_REDESIGN I.2.3
// and the program of CHECKER_REWRITE 2.4 idea 1, read by the path of the
// representative.
// ---------------------------------------------------------------------------

/// Fixture 1, `let g = a => { ignore(a + 1); takesMyInt(a); a }`:
/// `myint => myint`. A plain node becomes the unexpanded abbreviation node,
/// whichever side it is on (compiler/ml/ctype.ml:2299-2303, 2331).
#[test]
fn fixture_1_plain_node_takes_the_abbreviation() {
    for swapped in [false, true] {
        let mut c = checker(Mode::Success);
        let a = var(&mut c);
        let int = constr(&mut c, INT, &[]);
        c.unify(a, int).unwrap();
        let myint = constr(&mut c, MYINT, &[]);
        if swapped {
            c.unify(myint, a).unwrap();
        } else {
            c.unify(a, myint).unwrap();
        }
        assert_eq!(path(&mut c, a), MYINT);
        assert_eq!(c.g.repr(a), myint);
        assert_eq!(c.g.repr(int), myint);
    }
}

/// Fixture 6b, `let mk = a => { let v = {n: a, m: 0}; takesMyInt(a); v }`:
/// `myint => r`. `a` is the node of one instance of the label; another
/// instance of the label is not renamed.
#[test]
fn fixture_6b_one_label_instance_is_renamed() {
    let mut c = checker(Mode::Success);
    // The label `n`: its type and the record's.
    let label = scheme(&mut c, |c| {
        let (n, r) = (constr(c, INT, &[]), constr(c, R, &[]));
        tuple(c, &[n, r])
    });
    let a = var(&mut c);
    let first = c.instance(label);
    let n = child(&mut c, first, 0);
    c.unify(a, n).unwrap();
    let myint = constr(&mut c, MYINT, &[]);
    c.unify(a, myint).unwrap();
    assert_eq!(path(&mut c, a), MYINT);
    let second = c.instance(label);
    let n = child(&mut c, second, 0);
    assert_eq!(path(&mut c, n), INT);
    let r = child(&mut c, first, 1);
    assert_eq!(path(&mut c, r), R);
}

/// Fixture 7: `let pairConst = (1, 2)` and
/// `let h = q => { ignore(q == pairConst); let (a, _) = q; takesMyInt(a); q }`:
/// `h: ((myint, int)) => (myint, int)`, `pairConst: (int, int)`. The link
/// lands on a node inside `q`'s type (O6).
#[test]
fn fixture_7_link_inside_another_bindings_type() {
    let mut c = checker(Mode::Success);
    let pair_const = scheme(&mut c, |c| {
        let (x, y) = (constr(c, INT, &[]), constr(c, INT, &[]));
        tuple(c, &[x, y])
    });
    let q = var(&mut c);
    let instance = c.instance(pair_const);
    c.unify(q, instance).unwrap();
    // The pattern `(a, _)` against `q`.
    let (a, rest) = (var(&mut c), var(&mut c));
    let pattern = tuple(&mut c, &[a, rest]);
    c.unify(pattern, q).unwrap();
    let myint = constr(&mut c, MYINT, &[]);
    c.unify(a, myint).unwrap();
    let (first, second) = (child(&mut c, q, 0), child(&mut c, q, 1));
    assert_eq!(path(&mut c, first), MYINT);
    assert_eq!(path(&mut c, second), INT);
    // The scheme is untouched: a new instance is `(int, int)`.
    let fresh = c.instance(pair_const);
    let first = child(&mut c, fresh, 0);
    assert_eq!(path(&mut c, first), INT);
}

/// Fixture 9: `type phantom<'a> = int`,
/// `let h = (a, w) => { ignore(a == x); takesP(a, w); a }` with
/// `takesP: (phantom<'a>, 'a) => unit`: `(phantom<'a>, 'a) => phantom<'a>`.
/// A ground node gains a variable (O9).
#[test]
fn fixture_9_ground_node_gains_a_variable() {
    let mut c = checker(Mode::Success);
    let (a, w) = (var(&mut c), var(&mut c));
    let int = constr(&mut c, INT, &[]);
    c.unify(a, int).unwrap();
    let takes = scheme(&mut c, |c| {
        let v = var(c);
        let p = constr(c, PHANTOM, &[v]);
        tuple(c, &[p, v])
    });
    let instance = c.instance(takes);
    let (p, v) = (child(&mut c, instance, 0), child(&mut c, instance, 1));
    c.unify(a, p).unwrap();
    c.unify(w, v).unwrap();
    assert_eq!(path(&mut c, a), PHANTOM);
    let argument = child(&mut c, a, 0);
    assert_eq!(c.g.repr(argument), c.g.repr(w));
    let w = c.g.repr(w);
    let node = c.g.nodes[w.0 as usize];
    assert_eq!(node.tag(), VAR);
}

/// Fixture 10 and decision 2: `type a = int`, `type b = int`,
/// `let g = v => { takesA(v); takesB(v); v }` is `a => a`, and `b => b`
/// with the calls swapped. The first link names the node; unifying the two
/// abbreviation nodes links the *expansion* of the left one to the right
/// node (compiler/ml/ctype.ml:2299, 2331: `link_type t1' t2`), so the two
/// nodes stay two nodes.
#[test]
#[ignore = "R3c build"]
fn fixture_10_two_abbreviations_stay_two_nodes() {
    for (first, second) in [(A, B), (B, A)] {
        let mut c = checker(Mode::Success);
        let v = var(&mut c);
        let x = constr(&mut c, first, &[]);
        c.unify(v, x).unwrap();
        let y = constr(&mut c, second, &[]);
        c.unify(v, y).unwrap();
        assert_eq!(path(&mut c, v), first);
        assert_eq!(c.g.repr(v), x);
        assert_eq!(c.g.repr(y), y, "the second abbreviation node is not linked");
        // The left node's expansion is now the right node.
        let expansion = c.find_expansion(x, false);
        assert_ne!(expansion.0, NONE);
        assert_eq!(c.g.repr(expansion), y);
    }
    // With an argument (the abbreviation fixture of O5): the same rule, the
    // memo being slot 0 of the left node, and the arguments are not unified
    // with each other: the two expansions' components are.
    let mut c = checker(Mode::Success);
    let (s1, s2) = (constr(&mut c, STRING, &[]), constr(&mut c, STRING, &[]));
    let (x, y) = (constr(&mut c, PA, &[s1]), constr(&mut c, PB, &[s2]));
    c.unify(x, y).unwrap();
    assert_eq!(path(&mut c, x), PA);
    assert_eq!(path(&mut c, y), PB);
    assert_ne!(c.g.repr(x), c.g.repr(y));
    let expansion = c.find_expansion(x, false);
    assert_eq!(c.g.repr(expansion), y);
    // `'x := string` on both sides, then the tuples' first components met.
    assert_eq!(c.g.repr(s1), c.g.repr(s2));
    // Two nodes of ONE parameterised abbreviation unify their arguments and
    // link node to node, left to right, with no expansion made.
    let mut c = checker(Mode::Success);
    let (s1, s2) = (constr(&mut c, STRING, &[]), constr(&mut c, STRING, &[]));
    let (x, y) = (constr(&mut c, PA, &[s1]), constr(&mut c, PA, &[s2]));
    let nodes = c.g.nodes.len();
    c.unify(x, y).unwrap();
    assert_eq!(c.g.repr(x), y);
    assert_eq!(c.g.repr(s1), s2);
    assert_eq!(c.g.nodes.len(), nodes, "same path: no expansion");
}

/// Fixture 11: `type cb = int => unit`,
/// `let g = f => { plainF(f); takesCb(f); f }`: `cb => cb`. A node that is
/// not a constructor is linked to the abbreviation.
#[test]
fn fixture_11_arrow_takes_the_abbreviation() {
    let mut c = checker(Mode::Success);
    let f = var(&mut c);
    let (int, unit) = (constr(&mut c, INT, &[]), constr(&mut c, UNIT, &[]));
    let plain = arrow(&mut c, &[int], unit);
    c.unify(f, plain).unwrap();
    let cb = constr(&mut c, CB, &[]);
    c.unify(f, cb).unwrap();
    assert_eq!(path(&mut c, f), CB);
    assert_eq!(c.g.repr(plain), cb);
}

/// CHECKER_REWRITE 2.4, idea 1: `type box<'a> = {value: 'a, count: myint}`,
/// `let g = n => { let b: box<string> = {value: "", count: n}; (n, b) }` is
/// `myint => (myint, box<string>)`: the variable links to the *copy* of
/// the label's `myint`, which survives as the representative.
#[test]
fn idea_1_the_label_copy_survives() {
    let mut c = checker(Mode::Success);
    let count = scheme(&mut c, |c| {
        let v = var(c);
        let (field, record) = (constr(c, MYINT, &[]), constr(c, BOX, &[v]));
        tuple(c, &[field, record])
    });
    let n = var(&mut c);
    let string = constr(&mut c, STRING, &[]);
    let expected = constr(&mut c, BOX, &[string]);
    let label = c.instance(count);
    let (field, record) = (child(&mut c, label, 0), child(&mut c, label, 1));
    c.unify(record, expected).unwrap();
    c.unify(n, field).unwrap();
    assert_eq!(path(&mut c, n), MYINT);
    assert_eq!(c.g.repr(n), field, "the copy is the representative");
    assert_eq!(c.g.nodes[field.0 as usize].level, 2);
}

/// The variable-in-a-constructor case (compiler/ml/ctype.ml:2240-2241): a
/// variable that occurs only in a phantom argument is bound to the
/// constructor; one that occurs in a real argument is a clash (O13).
#[test]
fn occurrence_through_an_abbreviation() {
    let mut c = checker(Mode::Success);
    let v = var(&mut c);
    let ph = constr(&mut c, PHANTOM, &[v]);
    assert!(c.unify(v, ph).is_ok());
    let mut c = checker(Mode::Success);
    let v = var(&mut c);
    let p = constr(&mut c, PA, &[v]);
    assert!(c.unify(v, p).is_err());
}

// ---------------------------------------------------------------------------
// R3c: the cost of the expanding occurrence test.
// ---------------------------------------------------------------------------

/// `v` against a tuple of 10,000 `phantom<v>`: the binding walk reaches `v`
/// under every element, and `occur_rec`'s retry expands each `phantom<v>`
/// once (compiler/ml/ctype.ml:1396-1402). Linear, on a 2 MB stack.
#[test]
fn occurrence_retry_through_ten_thousand_phantoms_is_linear() {
    std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .spawn(|| {
            let n = 10_000u64;
            let mut c = checker(Mode::Success);
            let v = var(&mut c);
            let elements: Vec<Ty> = (0..n).map(|_| constr(&mut c, PHANTOM, &[v])).collect();
            let wide = tuple(&mut c, &elements);
            // Measured: 13 steps an element, most of them the expansion
            // (two loop steps, one parameter, the 3-node template).
            let count = steps::scope(|| c.unify(v, wide).unwrap());
            assert!(count <= 14 * n, "{count}");
            assert_eq!(c.g.repr(v), wide);
            for &element in &elements {
                assert_ne!(c.find_expansion(element, false).0, NONE);
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

/// `v` against `phantom<phantom<...<v>>>`, 10,000 deep: a variable in a
/// constructor goes to `unify2` (ctype.ml:2240), whose `occur` finds `v`
/// and expands only the innermost constructor. Linear, on a 2 MB stack.
#[test]
fn occurrence_retry_down_ten_thousand_constructors_fits_the_stack() {
    std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .spawn(|| {
            let n = 10_000u64;
            let mut c = checker(Mode::Success);
            let v = var(&mut c);
            let mut chain = v;
            for _ in 0..n {
                chain = constr(&mut c, PHANTOM, &[chain]);
            }
            let count = steps::scope(|| c.unify(v, chain).unwrap());
            assert!(count <= 6 * n, "{count}");
            assert_eq!(c.g.repr(v), chain);
        })
        .unwrap()
        .join()
        .unwrap();
}
