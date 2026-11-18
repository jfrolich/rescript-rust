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
use super::expand::{ABBREV, ALIAS, ExpandMode, INHERITS, Manifest, TypeInfo};
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
    // Two nodes of ONE parameterised abbreviation are expanded as well: only
    // two nullary constructors of one path link node to node
    // (compiler/ml/ctype.ml:2248-2257); every other pair of constructors
    // goes to unify2, which expands both heads ("abbreviations with at
    // least one parameter are systematically expanded",
    // ctype.ml:1785-1790). So again the left node's expansion is linked to
    // the right node, the two nodes stay two, and the expansions'
    // components meet.
    let mut c = checker(Mode::Success);
    let (s1, s2) = (constr(&mut c, STRING, &[]), constr(&mut c, STRING, &[]));
    let (x, y) = (constr(&mut c, PA, &[s1]), constr(&mut c, PA, &[s2]));
    let nodes = c.g.nodes.len();
    c.unify(x, y).unwrap();
    assert_eq!(path(&mut c, x), PA);
    assert_ne!(c.g.repr(x), c.g.repr(y));
    let expansion = c.find_expansion(x, false);
    assert_ne!(expansion.0, NONE);
    assert_eq!(c.g.repr(expansion), y);
    assert_eq!(c.g.repr(s1), c.g.repr(s2));
    assert!(c.g.nodes.len() > nodes, "same path, one parameter: both expand");
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
// R3c: the cost of the expanding occurrence test and of the recursion repair.
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

/// A tuple of 10,000 variables against `wide<t>`, an abbreviation of a
/// 10,000-element tuple of `int` whose argument is that tuple: the right
/// side was expanded and the left head occurs in it, so after the children
/// the recursion repair forgets the memo, expands again and tests that the
/// expansion is closed over the arguments (ctype.ml:2428-2436). Linear.
#[test]
fn recursion_repair_over_ten_thousand_elements_is_linear() {
    std::thread::Builder::new()
        .stack_size(2 * 1024 * 1024)
        .spawn(|| {
            let n = 10_000u64;
            let mut c = checker(Mode::Success);
            let wide_type = c.types.rows.len() as u32;
            c.types.rows.push(c.types.rows[PHANTOM as usize]);
            let param = var_at(&mut c, GENERIC);
            let ints: Vec<Ty> = (0..n)
                .map(|_| constr_at(&mut c, GENERIC, INT, &[]))
                .collect();
            let body = tuple_at(&mut c, GENERIC, &ints);
            abbreviation(&mut c, wide_type, &[param], body);
            let vars: Vec<Ty> = (0..n).map(|_| var(&mut c)).collect();
            let left = tuple(&mut c, &vars);
            let right = constr(&mut c, wide_type, &[left]);
            let before = c.g.nodes.len() as u64;
            let count = steps::scope(|| c.unify(left, right).unwrap());
            assert!(count <= 12 * n, "{count}");
            assert_eq!(c.g.repr(left), right);
            assert_eq!(path(&mut c, vars[0]), INT);
            // Two expansions: the first, and the repair's.
            assert!(c.g.nodes.len() as u64 - before >= 2 * (n + 1));
            let expansion = c.find_expansion(right, false);
            assert!(
                u64::from(expansion.0) > before + n,
                "the repair's expansion"
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

/// `unify_var` (compiler/ml/ctype.ml:2752-2771) writes the level before the
/// link, so of two named variables the name is chosen by the levels after
/// it (btype.ml:727): the target keeps its own, where `unify1_var`, which
/// links first, gives it the lower variable's. A variable in a constructor
/// goes to `unify` (ctype.ml:2755); a failure starts the trace with the
/// pair.
#[test]
fn unify_var_lowers_before_it_links() {
    let named = |c: &mut Checker, level: u32, name: u32| {
        let v = var_at(c, level);
        c.g.nodes[v.0 as usize].a = name;
        v
    };
    let mut c = checker(Mode::Success);
    let (v, w) = (named(&mut c, 2, 10), named(&mut c, 3, 20));
    c.unify_var(v, w).unwrap();
    assert_eq!(c.g.repr(v), w);
    assert_eq!(c.g.nodes[w.0 as usize].a, 20);
    assert_eq!(c.g.nodes[w.0 as usize].level, 2);
    let mut c = checker(Mode::Success);
    let (v, w) = (named(&mut c, 2, 10), named(&mut c, 3, 20));
    c.unify(v, w).unwrap();
    assert_eq!(c.g.nodes[w.0 as usize].a, 10, "unify1_var links first");

    let mut c = checker(Mode::Success);
    let v = var(&mut c);
    let ph = constr(&mut c, PHANTOM, &[v]);
    c.unify_var(v, ph).unwrap();
    assert_eq!(c.g.repr(v), ph);

    let mut c = checker(Mode::Explain);
    let v = var(&mut c);
    let p = constr(&mut c, PA, &[v]);
    let tuple_of_v = tuple(&mut c, &[v, v]);
    assert!(c.unify_var(v, tuple_of_v).is_err());
    assert_eq!(c.trace, [[v, tuple_of_v]]);
    assert_eq!(c.g.repr(v), v);
    assert!(c.unify_var(v, p).is_err());
    assert_eq!(c.g.repr(v), v);
}

// ---------------------------------------------------------------------------
// R3m: inherited memo entries (section 8.6, decisions 16, 19 and 26).
// ---------------------------------------------------------------------------

/// Append to the table four abbreviations with a parameter whose bodies
/// name each other, all marked [`INHERITS`]:
/// `q<'a> = ('a, q<'a>)`, `m1<'a> = ('a, m2<'a>)`, `m2<'a> = ('a, m3<'a>)`,
/// `m3<'a> = (m1<'a>, m2<'a>)`. (ReScript accepts such a cycle only through
/// an object or a variant; the graph does not care, and a tuple keeps these
/// tests on R3m alone.) Returns `[q, m1, m2, m3]`.
fn inheriting(c: &mut Checker) -> [u32; 4] {
    let first = c.types.rows.len() as u32;
    let types = [first, first + 1, first + 2, first + 3];
    for _ in types {
        c.types.rows.push(c.types.rows[PHANTOM as usize]);
    }
    let [q, m1, m2, m3] = types;
    for (ty, bodies) in [(q, [NONE, q]), (m1, [NONE, m2]), (m2, [NONE, m3]), (m3, [m1, m2])] {
        let param = var_at(c, GENERIC);
        let elements = bodies.map(|element| match element {
            NONE => param,
            element => constr_at(c, GENERIC, element, &[param]),
        });
        let body = tuple_at(c, GENERIC, &elements);
        abbreviation(c, ty, &[param], body);
        c.types.rows[ty as usize].flags |= INHERITS;
    }
    types
}

/// The representative of element `index` of the tuple `ty`, and its
/// descriptor.
fn element(c: &mut Checker, ty: Ty, index: u32) -> (Ty, Node) {
    let at = child(c, ty, index);
    let at = c.g.repr(at);
    (at, c.g.nodes[at.0 as usize])
}

/// The rule of R3m, by hand, where the harness cannot go (`forget_abbrev`
/// is no operation of it). `e1 = m1<int>` expands to `(int, c2)`, `c2 =
/// m2<int>` to `(int, c3)`, and `c3 = m3<int>` to `(m1<int>, m2<int>)`.
/// The copy of a constructor asks `find_repr p !abbrevs`
/// (compiler/ml/ctype.ml:780-782):
///
/// ```text
/// let rec find_repr p1 = function
///   | Mnil -> None
///   | Mcons (Public, p2, ty, _, _) when Path.same p1 p2 -> Some ty
///   | Mcons (_, _, _, _, rem) -> find_repr p1 rem
///   | Mlink {contents = rem} -> find_repr p1 rem
/// ```
///
/// and `c3`'s list is `c3`'s entry, then `c2`'s, then `e1`'s
/// (`Mlink !abbreviations`, ctype.ml:796-798). So with every entry in
/// place both elements are links: to `e1` and to `c2`. The same two
/// answers are observed on the old checker through objects
/// (`differential::tests::old_checker_inherits_entries_along_the_chain`).
///
/// A forgotten entry is taken out of the list and the tail stays
/// (`forget_abbrev_rec`, compiler/ml/btype.ml:636-644: `Mcons (_, path',
/// _, _, rem) when Path.same path path' -> rem`): after
/// `forget_abbrev(c2)` the walk from `c3` passes `c2`'s row and still
/// finds `e1`, and the copy of `m2<int>` finds nothing and is a new node
/// whose row continues with `c3`'s.
/// Reaches: R3m.
#[test]
fn an_inherited_entry_is_found_past_a_forgotten_one() {
    for forget in [false, true] {
        let mut c = checker(Mode::Success);
        let [_, m1, m2, m3] = inheriting(&mut c);
        let int = constr(&mut c, INT, &[]);
        let e1 = constr(&mut c, m1, &[int]);
        let x1 = c.expand_head(e1, ExpandMode::Unif).unwrap();
        let (c2, node) = element(&mut c, x1, 1);
        assert_eq!((node.tag(), node.a), (CONSTR, m2));
        let x2 = c.expand_head(c2, ExpandMode::Unif).unwrap();
        let (c3, node) = element(&mut c, x2, 1);
        assert_eq!((node.tag(), node.a), (CONSTR, m3));
        if forget {
            c.forget_abbrev(c2);
        }
        let made = c.g.nodes.len() as u32;
        let x3 = c.expand_head(c3, ExpandMode::Unif).unwrap();
        assert_eq!(element(&mut c, x3, 0).0, e1, "forget: {forget}");
        let (second, node) = element(&mut c, x3, 1);
        if forget {
            assert!(second.0 >= made, "a node of this expansion");
            assert_eq!((node.tag(), node.a), (CONSTR, m2));
            // Its row continues with c3's: expanding it links `m3<int>`
            // to c3 (`Mlink`, ctype.ml:796-798).
            let x4 = c.expand_head(second, ExpandMode::Unif).unwrap();
            assert_eq!(element(&mut c, x4, 1).0, c3);
        } else {
            assert_eq!(second, c2);
        }
    }
}

/// The step relation of decision 16, and the memory formula of decision
/// 25. `q<q<...q<int>>>`, n deep: expanding the head of each node from the
/// outside in is, per node, one instance of the four-node template, one
/// row, and a chain walk of one row (the copy of `q<'a>` finds the node
/// being expanded first, `find_repr`, compiler/ml/ctype.ml:720-724, and
/// becomes a link to it, ctype.ml:782). So the steps at n = 10,000 are at
/// most 11 times those at n = 1,000, there is one row per expanded node and
/// none for a copy, and the pool is `16 * rows + 4 * by_slot` bytes with
/// `by_slot` no longer than the list pool.
/// Reaches: R3m.
#[test]
fn expanding_the_heads_down_nested_recursive_nodes_is_linear() {
    let run = |n: u32| {
        let mut c = checker(Mode::Success);
        let [q, ..] = inheriting(&mut c);
        let mut nodes = vec![constr(&mut c, INT, &[])];
        for _ in 0..n {
            let inner = *nodes.last().unwrap();
            nodes.push(constr(&mut c, q, &[inner]));
        }
        let count = steps::scope(|| {
            for index in (1..=n as usize).rev() {
                let expansion = c.expand_head(nodes[index], ExpandMode::Unif).unwrap();
                assert_eq!(element(&mut c, expansion, 1).0, nodes[index]);
                assert_eq!(element(&mut c, expansion, 0).0, nodes[index - 1]);
            }
        });
        let chains = &c.memo.chains;
        assert_eq!(chains.rows.len(), n as usize);
        assert!(chains.by_slot.len() <= c.g.lists.len());
        let bytes = 16 * chains.rows.len() + 4 * chains.by_slot.len();
        assert!(bytes <= 16 * n as usize + 4 * c.g.lists.len(), "{bytes}");
        count
    };
    let (small, large) = (run(1_000), run(10_000));
    assert!(large <= 11 * small, "{small} {large}");
}

/// A manifest that inherits nothing pays the test of one flag: expanding
/// `pa<int>` (`type pa<'x> = ('x, int)`, not [`INHERITS`]) takes the steps
/// it takes today (observed, before R3m: 12) and reads or
/// writes no row of the pool, which stays unallocated. Runs today and
/// stays as it is when R3m is built.
#[test]
fn an_abbreviation_that_inherits_nothing_reads_no_row() {
    let mut c = checker(Mode::Success);
    let int = constr(&mut c, INT, &[]);
    let node = constr(&mut c, PA, &[int]);
    let count = steps::scope(|| {
        c.expand_head(node, ExpandMode::Unif).unwrap();
    });
    assert_eq!(count, 12);
    assert_eq!(c.memo.chains.rows.capacity(), 0);
    assert_eq!(c.memo.chains.by_slot.capacity(), 0);
    // And with the nullary memo live (the other reader of the pass over an
    // instance's nodes): the same pool, still unallocated.
    let myint = constr(&mut c, MYINT, &[]);
    c.expand_head(myint, ExpandMode::Unif).unwrap();
    let node = constr(&mut c, PA, &[int]);
    c.expand_head(node, ExpandMode::Unif).unwrap();
    assert_eq!(c.memo.chains.rows.capacity(), 0);
    assert_eq!(c.memo.chains.by_slot.capacity(), 0);
}

/// Which types `TypeTable::from_segment` marks [`INHERITS`]: those whose
/// manifest has a constructor with arguments of a type that expands, on
/// the identifier's row and on the row of the path through the unit alike.
/// `a1` names only an abstract type with arguments and `ro` only nullary
/// constructors: an expansion of either copies no constructor that could
/// be linked or expanded, and pays nothing (decision 19). `m1` names `m2`,
/// declared after it: the marks are made when every row exists.
/// Reaches: R3m.
#[test]
fn the_table_marks_the_types_whose_expansions_inherit() {
    let program = compile(
        "type t1<'a>\n\
         type a1<'a> = ('a, t1<'a>)\n\
         type a2<'a> = (a1<'a>, int)\n\
         type r<'a> = {f: a1<'a>}\n\
         type rec ro = {\"hd\": int, \"tl\": ro}\n\
         type rec po<'a> = {\"hd\": 'a, \"tl\": po<'a>}\n\
         type rec m1<'a> = {\"a\": 'a, \"n\": m2<'a>}\n\
         and m2<'a> = {\"a\": 'a, \"n\": m1<'a>}\n\
         external v: (a1<int>, a2<int>, r<int>, ro, po<int>, m1<int>, m2<int>) = \"v\"\n"
            .to_string(),
    );
    let new = super::differential::New::convert(&program, Tier::Kernel);
    let table = super::expand::TypeTable::from_segment(&new.segment);
    let pools = &new.segment.signature;
    let mut seen = 0;
    for (index, row) in pools.paths.iter().enumerate() {
        let name = match *row {
            super::segment::PathRow::Ident(ident) => pools.identifiers[ident as usize].name,
            super::segment::PathRow::Dot { name, .. } => name,
            super::segment::PathRow::Apply { .. } => continue,
        };
        let range = pools.strings[name as usize];
        let name = &pools.bytes[range.start as usize..(range.start + range.len) as usize];
        let inherits = match name {
            b"a2" | b"po" | b"m1" | b"m2" => true,
            b"t1" | b"a1" | b"r" | b"ro" | b"int" => false,
            _ => continue,
        };
        let flags = table.info(index as u32).flags;
        assert_eq!(flags & INHERITS != 0, inherits, "{}", String::from_utf8_lossy(name));
        seen += 1;
    }
    // Every declared type has two rows: its identifier and `Case.name`.
    assert!(seen >= 17, "{seen}");
}

// ---------------------------------------------------------------------------
// R3e: objects, fields and mutability cells (section 8.6, decision 27).
// ---------------------------------------------------------------------------

use super::rows::{FieldRef, cell_mutable, cell_node, cell_repr};
use super::segment::{EXTENDED, ExtraDescriptor, Range};

/// The index of a name, interned by text in the checker's name texts.
fn name(c: &mut Checker, text: &str) -> u32 {
    let names = &mut c.extras.names;
    if let Some(found) = (0..names.spans.len() as u32).find(|&at| names.text(at) == text.as_bytes()) {
        return found;
    }
    let start = names.bytes.len() as u32;
    names.bytes.extend_from_slice(text.as_bytes());
    names.spans.push(Range { start, len: text.len() as u32 });
    names.spans.len() as u32 - 1
}

/// An extended node at `level` with a new descriptor row and these slots.
fn extended_at(c: &mut Checker, level: u32, descriptor: ExtraDescriptor, slots: &[Ty]) -> Ty {
    let a = c.extras.descriptors.len() as u32;
    c.extras.descriptors.push(descriptor);
    let b = c.g.lists.len() as u32;
    c.g.lists.extend_from_slice(slots);
    c.g.push(Node {
        head: TUPLE | EXTENDED | (slots.len() as u32) << 8,
        level,
        a,
        b,
    })
}

/// A new mutability cell.
fn cell(c: &mut Checker, mutable: bool) -> Ty {
    c.g.push(cell_node(mutable))
}

fn nil_at(c: &mut Checker, level: u32) -> Ty {
    extended_at(c, level, ExtraDescriptor::Nil, &[])
}

/// `poly(ty;)`: the type of an object field (typecore.ml:3662).
fn poly_at(c: &mut Checker, level: u32, ty: Ty) -> Ty {
    extended_at(c, level, ExtraDescriptor::Poly, &[ty])
}

/// A field node `label: poly(ty;); rest` with the given cell.
fn field_at(c: &mut Checker, level: u32, label: &str, cell: Ty, ty: Ty, rest: Ty) -> Ty {
    let name = name(c, label);
    let typ = poly_at(c, level, ty);
    extended_at(c, level, ExtraDescriptor::Field { name, mutability: cell.0 }, &[typ, rest])
}

/// An object at the current level: the fields in the order given, each
/// `(label, mutable, type)` with a cell of its own, ending in `rest`.
/// Returns the object and its field nodes, first field first.
fn obj(c: &mut Checker, fields: &[(&str, bool, Ty)], rest: Ty) -> (Ty, Vec<Ty>) {
    let level = c.g.level;
    let mut list = rest;
    let mut nodes = Vec::new();
    for &(label, mutable, ty) in fields.iter().rev() {
        let cell = cell(c, mutable);
        list = field_at(c, level, label, cell, ty, list);
        nodes.push(list);
    }
    nodes.reverse();
    (extended_at(c, level, ExtraDescriptor::Object, &[list]), nodes)
}

/// The names of an object's fields in list order (links followed), and
/// what the list ends in.
fn row(c: &mut Checker, object: Ty) -> (Vec<String>, Ty) {
    let object = c.g.repr(object);
    let node = c.g.nodes[object.0 as usize];
    let mut at = c.g.repr(c.g.lists[node.b as usize]);
    let mut names = Vec::new();
    loop {
        let node = c.g.nodes[at.0 as usize];
        let field = node.head & EXTENDED != 0;
        match field.then(|| c.extras.descriptors[node.a as usize]) {
            Some(ExtraDescriptor::Field { name, .. }) => {
                names.push(String::from_utf8(c.extras.names.text(name).to_vec()).unwrap());
                at = c.g.repr(c.g.lists[node.b as usize + 1]);
            }
            _ => return (names, at),
        }
    }
}

/// The class of a field node's cell.
fn class(c: &Checker, field: Ty) -> Ty {
    let node = c.g.nodes[field.0 as usize];
    let ExtraDescriptor::Field { mutability, .. } = c.extras.descriptors[node.a as usize] else {
        panic!("not a field");
    };
    cell_repr(&c.g, Ty(mutability))
}

/// Fields each side lacks (compiler/ml/ctype.ml:2467-2486):
///
/// ```text
/// let pairs, miss1, miss2 = associate_fields fields1 fields2 in
/// let va = make_rowvar (min l1 l2) (miss2 = []) rest1 (miss1 = []) rest2 in
/// unify env (build_fields l1 miss1 va) rest2;
/// unify env rest1 (build_fields l2 miss2 va);
/// ```
///
/// `{.. b, a}` against `{.. c}`, both rests variables: neither list is
/// used as it is, so `va` is a new variable; the right rest is bound to a
/// new `a; b; va` (sorted by name, `flatten_fields`, ctype.ml:323, though
/// the left list has `b` first) and the left rest to a new `c; va`. Each
/// built field has the descriptor of the field it copies (`mutability =
/// f_mut`, ctype.ml:325-328): no descriptor row is made, none is written.
/// The two objects are linked left to right (`link_type t1' t2`,
/// ctype.ml:2331) and no field node is.
/// Reaches: R3e.
#[test]
fn fields_a_side_lacks_are_built_on_one_row_variable() {
    let mut c = checker(Mode::Success);
    let int = constr(&mut c, INT, &[]);
    let (rest1, rest2) = (var(&mut c), var(&mut c));
    let (left, lf) = obj(&mut c, &[("b", false, int), ("a", true, int)], rest1);
    let (right, rf) = obj(&mut c, &[("c", false, int)], rest2);
    let descriptors = c.extras.descriptors.clone();
    let nodes = c.g.nodes.len() as u32;
    c.unify(left, right).unwrap();
    assert_eq!(c.extras.descriptors, descriptors, "no descriptor row made or written");
    assert_eq!(c.g.nodes.len() as u32 - nodes, 4, "three fields and one variable");
    assert_eq!(c.g.repr(left), right);
    let (names, end) = row(&mut c, right);
    assert_eq!(names, ["c", "a", "b"]);
    assert!(end.0 >= nodes && c.g.nodes[end.0 as usize].tag() == VAR);
    assert_eq!(c.g.nodes[end.0 as usize].level, 2);
    // The left list, read from its own first field: b, a, then c, va.
    let built_c = c.g.repr(rest1);
    assert_eq!(c.g.nodes[built_c.0 as usize].a, c.g.nodes[rf[0].0 as usize].a);
    let built_a = c.g.repr(rest2);
    assert_eq!(c.g.nodes[built_a.0 as usize].a, c.g.nodes[lf[1].0 as usize].a);
    assert!(cell_mutable(&c.g, class(&c, built_a)));
    assert_eq!(class(&c, built_a), class(&c, lf[1]));
    assert_eq!(c.g.repr(lf[0]), lf[0], "a field node is not linked");
}

/// A closed row gains nothing and an open one takes what it lacks
/// (ctype.ml:2478-2486). `{a, b}` closed against `{.. a}`: the left lacks
/// nothing of the right, so `va` is the left rest (`use1`); the right rest
/// is bound to `b; nil` and `unify rest1 va` is one node on both sides.
/// The other way, `{a}` closed against `{.. a, b}`: `va` is the right rest
/// (`use2`), and `unify rest1 (b; va)` is `Tnil` against a field: a clash
/// (`_, _ -> raise (Unify [])`, ctype.ml:2425).
/// Reaches: R3e.
#[test]
fn a_closed_row_takes_no_field() {
    let mut c = checker(Mode::Success);
    let int = constr(&mut c, INT, &[]);
    let nil = nil_at(&mut c, 2);
    let rest = var(&mut c);
    let (closed, _) = obj(&mut c, &[("a", false, int), ("b", false, int)], nil);
    let (open, _) = obj(&mut c, &[("a", false, int)], rest);
    let nodes = c.g.nodes.len();
    c.unify(closed, open).unwrap();
    assert_eq!(c.g.nodes.len() - nodes, 1, "one built field");
    let (names, end) = row(&mut c, open);
    assert_eq!((names, end), (vec!["a".to_string(), "b".to_string()], nil));

    for swap in [false, true] {
        let mut c = checker(Mode::Success);
        let int = constr(&mut c, INT, &[]);
        let nil = nil_at(&mut c, 2);
        let rest = var(&mut c);
        let (closed, _) = obj(&mut c, &[("a", false, int)], nil);
        let (open, _) = obj(&mut c, &[("a", false, int), ("b", false, int)], rest);
        let result = if swap { c.unify(open, closed) } else { c.unify(closed, open) };
        assert!(result.is_err(), "swap {swap}");
    }
}

/// Common fields are unified in name order, and what a failure leaves in
/// `Mode::Explain` (ctype.ml:2487-2517). `{b: int, a: int}` against `{a:
/// string, b: unit}`, both closed: the pair of `a` fails first although
/// `b` is first in the left list. The trace is the pair of the objects,
/// the pair of two new one-field lists for `a` (`Tfield {f1 with rest =
/// newty Tnil}`, ctype.ml:2493-2510), the pair of the two field types, and
/// the pair that clashed. The left rest, linked to the right one by the
/// tail unification (`Tnil, Tnil`, ctype.ml:2412), has its descriptor back
/// (`rest1.desc <- d1`, ctype.ml:2514), and so has the left object
/// (`t1'.desc <- d1`, ctype.ml:2437).
/// Reaches: R3e.
#[test]
fn common_fields_unify_in_name_order_and_a_failure_restores_the_rests() {
    let mut c = checker(Mode::Explain);
    let (int, string, unit) = (constr(&mut c, INT, &[]), constr(&mut c, STRING, &[]), constr(&mut c, UNIT, &[]));
    let (nil1, nil2) = (nil_at(&mut c, 2), nil_at(&mut c, 2));
    let (left, lf) = obj(&mut c, &[("b", false, int), ("a", false, int)], nil1);
    let (right, rf) = obj(&mut c, &[("a", false, string), ("b", false, unit)], nil2);
    assert!(c.unify(left, right).is_err());
    assert_eq!(c.trace.len(), 4, "{:?}", c.trace);
    assert_eq!(c.trace[0], [left, right]);
    let [f1, f2] = c.trace[1];
    for (made, source) in [(f1, lf[1]), (f2, rf[0])] {
        assert_ne!(made, source);
        assert_eq!(c.g.nodes[made.0 as usize].a, c.g.nodes[source.0 as usize].a, "name and cell");
        assert_eq!(child(&mut c, made, 0), child(&mut c, source, 0));
        let rest = child(&mut c, made, 1);
        let rest = c.g.nodes[rest.0 as usize];
        assert_eq!(c.extras.descriptors[rest.a as usize], ExtraDescriptor::Nil);
    }
    let types = [child(&mut c, lf[1], 0), child(&mut c, rf[0], 0)];
    assert_eq!(c.trace[2], types);
    assert_eq!(c.trace[3], [int, string]);
    assert_eq!(c.g.repr(nil1), nil1);
    assert_eq!(c.g.repr(left), left);
}

/// `unify_mutability` (ctype.ml:2520-2539), arm by arm:
///
/// ```text
/// | Mutability_value Immutable, Mutability_value Mutable ->
///   if open1 then set_mutability r1 (Mutability_value Asttypes.Mutable)
///   else raise (Unify [])
/// | Mutability_value Mutable, Mutability_value Immutable ->
///   if open2 then set_mutability r2 (Mutability_value Asttypes.Mutable)
///   else raise (Unify [])
/// ...
/// set_mutability r2 (Mutability_link r1)
/// ```
///
/// `open1` and `open2` are read before the rests are unified
/// (ctype.ml:2476): an open immutable row against a closed mutable one is
/// promoted although the tail unification closes it first. The right
/// class is linked to the left one whatever the values. A restore puts
/// both writes back (`Cmutability`, btype.ml:745-747). The same answers
/// are observed on the old checker
/// (`differential::tests::old_checker_duplicates_the_cells_of_an_open_row`).
/// Reaches: R3e.
#[test]
fn mutability_is_promoted_on_the_open_side_and_classes_merge() {
    // (left open, left mutable, right open, right mutable) -> unifies
    let cases = [
        (true, false, true, true, true),
        (true, true, true, false, true),
        (true, false, false, true, true),
        (false, false, true, true, false),
        (false, true, true, false, true),
        (true, true, false, false, false),
        (false, false, false, true, false),
        (false, false, false, false, true),
        (false, true, false, true, true),
    ];
    for (open1, mut1, open2, mut2, unifies) in cases {
        let mut c = checker(Mode::Success);
        let int = constr(&mut c, INT, &[]);
        let rest1 = if open1 { var(&mut c) } else { nil_at(&mut c, 2) };
        let rest2 = if open2 { var(&mut c) } else { nil_at(&mut c, 2) };
        let (left, lf) = obj(&mut c, &[("x", mut1, int)], rest1);
        let (right, rf) = obj(&mut c, &[("x", mut2, int)], rest2);
        let (r1, r2) = (class(&c, lf[0]), class(&c, rf[0]));
        let descriptors = c.extras.descriptors.clone();
        let token = c.g.speculate();
        let result = c.unify(left, right);
        assert_eq!(result.is_ok(), unifies, "{open1} {mut1} {open2} {mut2}");
        assert_eq!(c.extras.descriptors, descriptors);
        if unifies {
            assert_eq!(class(&c, rf[0]), r1, "the right class links to the left");
            assert_eq!(cell_mutable(&c.g, r1), mut1 || mut2);
        }
        c.restore(token);
        assert_eq!((class(&c, lf[0]), class(&c, rf[0])), (r1, r2));
        assert_eq!((cell_mutable(&c.g, r1), cell_mutable(&c.g, r2)), (mut1, mut2));
    }
}

/// `make_rowvar` (ctype.ml:2445-2465) when both lists are used as they
/// are: `va` is the left rest, and of a named left rest and an unnamed
/// right one the right takes the name (`Tvar (Some _ as name), _ -> if
/// use2 then set_name rest2 name`) before the two are unified, so the
/// name survives the link of the left variable to the right
/// (ctype.ml:2242-2243).
/// Reaches: R3e.
#[test]
fn the_row_variable_keeps_a_name() {
    let mut c = checker(Mode::Success);
    let int = constr(&mut c, INT, &[]);
    let (rest1, rest2) = (var_at(&mut c, 3), var(&mut c));
    c.g.nodes[rest1.0 as usize].a = 7;
    let (left, _) = obj(&mut c, &[("x", false, int)], rest1);
    let (right, _) = obj(&mut c, &[("x", false, int)], rest2);
    c.unify(left, right).unwrap();
    assert_eq!(c.g.repr(rest1), rest2);
    assert_eq!(c.g.nodes[rest2.0 as usize].a, 7);
    assert_eq!(c.g.nodes[rest2.0 as usize].level, 2);
}

/// What a failure leaves of the name `make_rowvar` gave (ctype.ml:2477-2482,
/// 2512-2517): `let d1 = rest1.desc and d2 = rest2.desc` is read after
/// `make_rowvar`, so the descriptor a failure puts back on the right rest
/// is the named one (`set_name rest2 name`, ctype.ml:2458). `{x: int, ..}`
/// with a named rest against `{x: string, ..}` in `Mode::Explain`: the
/// left rest, linked to the right one by the tail unification, is a
/// variable of its own again, and the right rest keeps the name.
/// Reaches: R3e.
#[test]
fn a_failure_keeps_the_name_the_row_variable_was_given() {
    let mut c = checker(Mode::Explain);
    let (int, string) = (constr(&mut c, INT, &[]), constr(&mut c, STRING, &[]));
    let (rest1, rest2) = (var_at(&mut c, 3), var(&mut c));
    c.g.nodes[rest1.0 as usize].a = 7;
    let (left, _) = obj(&mut c, &[("x", false, int)], rest1);
    let (right, _) = obj(&mut c, &[("x", false, string)], rest2);
    assert!(c.unify(left, right).is_err());
    assert_eq!(c.g.repr(rest1), rest1);
    assert_eq!(c.g.nodes[rest1.0 as usize].a, 7);
    assert_eq!(c.g.repr(rest2), rest2);
    assert_eq!(c.g.nodes[rest2.0 as usize].a, 7);
}

/// The arms of unify3 beside the object's (ctype.ml:2322-2324, 2412-2413,
/// 2424). Two field nodes go to `unify_fields` with no link of their own
/// (`Tfield _, Tfield _ -> unify_fields env t1' t2'`): the rests are
/// unified and the two field nodes stay two. Two `Tnil` link. Two
/// polymorphic types without variables link and unify their bodies. An
/// object against a tuple, and a field against `Tnil`, clash.
/// Reaches: R3e.
#[test]
fn the_other_arms_of_objects() {
    let mut c = checker(Mode::Success);
    let int = constr(&mut c, INT, &[]);
    let (rest1, rest2) = (var(&mut c), var(&mut c));
    let (_, lf) = obj(&mut c, &[("x", false, int)], rest1);
    let (_, rf) = obj(&mut c, &[("x", false, int)], rest2);
    c.unify(lf[0], rf[0]).unwrap();
    assert_eq!(c.g.repr(rest1), rest2);
    assert_eq!((c.g.repr(lf[0]), c.g.repr(rf[0])), (lf[0], rf[0]));

    let (nil1, nil2) = (nil_at(&mut c, 2), nil_at(&mut c, 2));
    c.unify(nil1, nil2).unwrap();
    assert_eq!(c.g.repr(nil1), nil2);

    let v = var(&mut c);
    let (p1, p2) = (poly_at(&mut c, 2, v), poly_at(&mut c, 2, int));
    c.unify(p1, p2).unwrap();
    assert_eq!((c.g.repr(p1), c.g.repr(v)), (p2, int));

    let nil = nil_at(&mut c, 2);
    let (object, fields) = obj(&mut c, &[("x", false, int)], nil);
    let pair = tuple(&mut c, &[int, int]);
    assert!(c.unify(object, pair).is_err());
    let nil = nil_at(&mut c, 2);
    assert!(c.unify(fields[0], nil).is_err());
}

/// Where the occurrence tests cross an object. `occur_rec` does not
/// (`| Tobject _ | Tvariant _ -> ()`, ctype.ml:1403): a variable is bound
/// to an object that holds it. `deep_occur` does (`| Tobject ty | Tlink ty
/// | Tsubst ty -> deep_occur_budget t0 budget ty`, ctype.ml:1735), and it
/// decides the route of a variable against a constructor (`Tvar _,
/// Tconstr _ when deep_occur t1 t2 -> unify2 env t1 t2`, ctype.ml:
/// 2240-2241). The two differ for `v` (level 2) against `id<obj>` (level
/// 3) where `obj = {x: v}` is at level 1 and `type id<'a> = 'a`: unify2
/// expands the constructor to `obj` and lowers both sides to the lower of
/// the two expanded levels, 1 (ctype.ml:2283-2285), before unify3 links
/// `v` to the constructor node (`occur` finds nothing: ctype.ml:2316-2319).
/// Without the route the binding would lower the constructor to the
/// variable's level, 2. In both modes.
/// Reaches: R3e.
#[test]
fn the_route_of_a_variable_crosses_an_object_and_the_occurrence_test_does_not() {
    for mode in [Mode::Success, Mode::Explain] {
        let mut c = checker(mode);
        let v = var(&mut c);
        let nil = nil_at(&mut c, 2);
        let (object, _) = obj(&mut c, &[("x", false, v)], nil);
        c.unify(v, object).unwrap();
        assert_eq!(c.g.repr(v), object, "{mode:?}");

        let mut c = checker(mode);
        let id = c.types.rows.len() as u32;
        c.types.rows.push(c.types.rows[PHANTOM as usize]);
        let param = var_at(&mut c, GENERIC);
        abbreviation(&mut c, id, &[param], param);
        let v = var(&mut c);
        let nil = nil_at(&mut c, 1);
        let cell = cell(&mut c, false);
        let field = field_at(&mut c, 1, "x", cell, v, nil);
        let object = extended_at(&mut c, 1, ExtraDescriptor::Object, &[field]);
        let wrapped = constr_at(&mut c, 3, id, &[object]);
        c.unify(v, wrapped).unwrap();
        assert_eq!(c.g.repr(v), wrapped, "{mode:?}");
        assert_eq!(c.g.nodes[wrapped.0 as usize].level, 1, "{mode:?}");
    }
}

/// A scheme `({.. a, x} as 'r, 'r)` whose row ends in a generic variable,
/// and one that ends in `Tnil`, captured as templates.
fn object_scheme(c: &mut Checker, open: bool, fields: u32) -> (Template, Vec<Ty>) {
    let mut nodes = Vec::new();
    let template = scheme(c, |c| {
        let int = constr(c, INT, &[]);
        let rest = if open { var(c) } else { nil_at(c, c.g.level) };
        let labels: Vec<String> = (0..fields).map(|at| format!("f{at:05}")).collect();
        let list: Vec<(&str, bool, Ty)> =
            labels.iter().enumerate().map(|(at, label)| (label.as_str(), at % 2 == 1, int)).collect();
        let (object, made) = obj(c, &list, rest);
        nodes = made;
        tuple(c, &[object, object])
    });
    (template, nodes)
}

/// An instance duplicates the cells of an open row and shares those of a
/// closed one (compiler/ml/btype.ml:527-530):
///
/// ```text
/// let mutability =
///   if fresh_mutability || row_terminator_generic f_.rest then
///     dup_mutability f_.mutability
///   else mutability_ref_repr f_.mutability
/// ```
///
/// Two instances of the open scheme: each field has a new descriptor row
/// and a cell that is neither the scheme's nor the other instance's, with
/// the scheme's value; the scheme's cells are their own representatives
/// again after each instance (`end_type_copy_session`, btype.ml:449-456).
/// An instance of the closed scheme makes no descriptor row and no cell.
/// `template_has_open_row` tells the two apart. Observed on the old
/// checker: `old_checker_duplicates_the_cells_of_an_open_row`.
/// Reaches: R3e.
#[test]
fn an_instance_duplicates_the_cells_of_an_open_row() {
    let field_of = |c: &mut Checker, root: Ty, index: u32| {
        let object = child(c, root, 0);
        let mut at = child(c, object, 0);
        for _ in 0..index {
            at = child(c, at, 1);
        }
        c.g.repr(at)
    };
    let mut c = checker(Mode::Success);
    let (open, scheme_fields) = object_scheme(&mut c, true, 2);
    let has = |c: &Checker, template| {
        let slots = super::template::slots(&c.g.template_lists, &c.g.template_pools, template);
        super::rows::template_has_open_row(&c.g.template_nodes, slots, &c.extras.descriptors, template)
    };
    assert!(has(&c, open));
    let descriptors = c.extras.descriptors.len();
    let (first, second) = (c.instance_open(open), c.instance_open(open));
    assert_eq!(c.extras.descriptors.len(), descriptors + 4);
    for index in 0..2 {
        let source = class(&c, scheme_fields[index as usize]);
        let (a, b) = (field_of(&mut c, first, index), field_of(&mut c, second, index));
        let (ca, cb) = (class(&c, a), class(&c, b));
        assert!(ca != cb && ca != source && cb != source);
        assert_eq!(cell_mutable(&c.g, ca), index == 1);
        assert_eq!(c.g.nodes[source.0 as usize], cell_node(index == 1), "the session ended");
    }
    assert!(c.extras.session.is_empty());

    let mut c = checker(Mode::Success);
    let (closed, scheme_fields) = object_scheme(&mut c, false, 2);
    assert!(!has(&c, closed));
    let (descriptors, nodes) = (c.extras.descriptors.len(), c.g.nodes.len());
    let root = c.instance_open(closed);
    assert_eq!(c.extras.descriptors.len(), descriptors);
    let field = field_of(&mut c, root, 0);
    assert_eq!(class(&c, field), class(&c, scheme_fields[0]));
    let with_pass = c.g.nodes.len() - nodes;
    let nodes = c.g.nodes.len();
    c.instance(closed);
    assert_eq!(c.g.nodes.len() - nodes, with_pass, "no cell made");
}

/// Steps of objects, as relations between n = 1,000 and n = 10,000 fields
/// (name comparisons of the sort are not steps: O(n log n) byte
/// comparisons, stated in `flatten_fields`):
/// - unifying two closed objects of n common fields, the left list in
///   reverse name order: at most 11 times;
/// - unifying `{.. f0..fn}` with `{.. g0..gn}`, n fields built on each
///   side: at most 11 times, and 2n + 1 nodes made;
/// - an instance of an open row of n fields (the terminator of the row is
///   found once, not once per field, btype.ml:474-506): at most 11 times;
/// - an instance of a closed row through `Checker::instance`: exactly the
///   steps of `Graph::instance` (no pass).
///
/// Reaches: R3e.
#[test]
fn objects_of_ten_thousand_fields_are_linear() {
    let common = |n: u32| {
        let mut c = checker(Mode::Success);
        let int = constr(&mut c, INT, &[]);
        let labels: Vec<String> = (0..n).map(|at| format!("f{at:05}")).collect();
        let forward: Vec<(&str, bool, Ty)> = labels.iter().map(|label| (label.as_str(), false, int)).collect();
        let backward: Vec<(&str, bool, Ty)> = forward.iter().rev().copied().collect();
        let (nil1, nil2) = (nil_at(&mut c, 2), nil_at(&mut c, 2));
        let (left, _) = obj(&mut c, &backward, nil1);
        let (right, _) = obj(&mut c, &forward, nil2);
        steps::scope(|| c.unify(left, right).unwrap())
    };
    let (small, large) = (common(1_000), common(10_000));
    assert!(large <= 11 * small, "common: {small} {large}");

    let disjoint = |n: u32| {
        let mut c = checker(Mode::Success);
        let int = constr(&mut c, INT, &[]);
        let f: Vec<String> = (0..n).map(|at| format!("f{at:05}")).collect();
        let g: Vec<String> = (0..n).map(|at| format!("g{at:05}")).collect();
        let f: Vec<(&str, bool, Ty)> = f.iter().map(|label| (label.as_str(), false, int)).collect();
        let g: Vec<(&str, bool, Ty)> = g.iter().map(|label| (label.as_str(), false, int)).collect();
        let (rest1, rest2) = (var(&mut c), var(&mut c));
        let (left, _) = obj(&mut c, &f, rest1);
        let (right, _) = obj(&mut c, &g, rest2);
        let nodes = c.g.nodes.len() as u32;
        let count = steps::scope(|| c.unify(left, right).unwrap());
        assert_eq!(c.g.nodes.len() as u32 - nodes, 2 * n + 1);
        count
    };
    let (small, large) = (disjoint(1_000), disjoint(10_000));
    assert!(large <= 11 * small, "disjoint: {small} {large}");

    let instance = |n: u32| {
        let mut c = checker(Mode::Success);
        let (open, _) = object_scheme(&mut c, true, n);
        steps::scope(|| {
            c.instance_open(open);
        })
    };
    let (small, large) = (instance(1_000), instance(10_000));
    assert!(large <= 11 * small, "instance: {small} {large}");

    let mut c = checker(Mode::Success);
    let (closed, _) = object_scheme(&mut c, false, 10_000);
    let through = steps::scope(|| {
        c.instance(closed);
    });
    let kernel = steps::scope(|| {
        c.g.instance(closed);
    });
    assert_eq!(through, kernel);
}

/// The stack entry of a flattened field is 12 bytes; a cell is a node.
#[test]
fn sizes_of_object_rows() {
    assert_eq!(std::mem::size_of::<FieldRef>(), 12);
    assert_eq!(std::mem::size_of::<ExtraDescriptor>(), 12);
    assert_eq!(std::mem::size_of_val(&cell_node(true)), 16);
}

// ---------------------------------------------------------------------------
// R3f: polymorphic variant rows (section 8.6, decision 34).
// ---------------------------------------------------------------------------

use super::rows::{FieldRepr, RES_EITHER, RES_KIND, field_repr, published_slots};
use super::segment::{RowFieldKind, RowFieldRow, VariantRow};

/// One tag of a hand-built row.
#[derive(Clone, Copy)]
enum Tag {
    /// `Rpresent`, with its argument or none.
    Present(Option<Ty>),
    Absent,
    /// `Reither (c, tl, m, ref None)` with at most one type.
    Either(bool, Option<Ty>, bool),
}

/// An unopened variant node at `level`, as a segment publishes one
/// (tc/bridge/from_old.rs, `variant`): the slots are the tags' types in
/// order, then `more`; each `Reither` field has the slot its reference
/// will have (`Extras::from_segment`). `name` is a path index or `NONE`.
fn variant_at(c: &mut Checker, level: u32, tags: &[(&str, Tag)], more: Ty, closed: bool, name: u32) -> Ty {
    let start = c.extras.row_fields.len() as u32;
    let mut slots = Vec::new();
    for &(label, tag) in tags {
        let name = name_index(c, label);
        let (ty, kind) = match tag {
            Tag::Present(ty) => (ty, RowFieldKind::Present),
            Tag::Absent => (None, RowFieldKind::Absent),
            Tag::Either(constant, ty, matched) => (ty, RowFieldKind::Either { constant, matched }),
        };
        let types = Range { start: slots.len() as u32, len: u32::from(ty.is_some()) };
        slots.extend(ty);
        c.extras.row_fields.push(RowFieldRow { name, types, link: NONE, kind });
    }
    let more_slot = slots.len() as u32;
    slots.push(more);
    let row = VariantRow {
        fields: Range { start, len: tags.len() as u32 },
        more: more_slot,
        name,
        name_arguments: Range::default(),
        closed,
        fixed: false,
    };
    let mut slot = published_slots(row, &c.extras.row_fields);
    for field in &mut c.extras.row_fields[start as usize..] {
        if matches!(field.kind, RowFieldKind::Either { .. }) {
            field.link = slot;
            slot += 1;
        }
    }
    c.extras.variants.push(row);
    let index = c.extras.variants.len() as u32 - 1;
    extended_at(c, level, ExtraDescriptor::Variant(index), &slots)
}

/// [`name`], under a name that a parameter called `name` does not hide.
fn name_index(c: &mut Checker, text: &str) -> u32 {
    name(c, text)
}

/// The row of `ty` as `row_repr` gives it (compiler/ml/btype.ml:126-135):
/// every tag with its field read through its references, outermost node
/// first; the last node's row; the representative of its `more`.
fn read_row(c: &mut Checker, ty: Ty) -> (Vec<(String, FieldRepr)>, VariantRow, Ty) {
    let mut at = c.g.repr(ty);
    let mut tags = Vec::new();
    loop {
        let node = c.g.nodes[at.0 as usize];
        let ExtraDescriptor::Variant(row) = c.extras.descriptors[node.a as usize] else {
            panic!("not a variant");
        };
        let row = c.extras.variants[row as usize];
        for index in row.fields.start..row.fields.start + row.fields.len {
            let field = c.extras.row_fields[index as usize];
            let label = String::from_utf8(c.extras.names.text(field.name).to_vec()).unwrap();
            tags.push((label, field_repr(&c.g, node.b, node.arity(), field)));
        }
        let more = c.g.repr(c.g.lists[(node.b + row.more) as usize]);
        let inner = c.g.nodes[more.0 as usize];
        let variant = inner.head & EXTENDED != 0
            && matches!(c.extras.descriptors[inner.a as usize], ExtraDescriptor::Variant(_));
        if !variant {
            return (tags, row, more);
        }
        at = more;
    }
}

/// [`read_row`] as text: `[closed fixed A B() C- D?cm1 | more as name]`:
/// a present tag, one with an argument, an absent one, a `Reither` one
/// with its flags and how many types it has; `more` is `'` (a variable),
/// `nil` or `t` (a constructor).
fn shape(c: &mut Checker, ty: Ty) -> String {
    let (tags, row, more) = read_row(c, ty);
    let mut text = String::from("[");
    for flag in [(row.closed, "closed "), (row.fixed, "fixed ")] {
        if flag.0 {
            text.push_str(flag.1);
        }
    }
    for (label, field) in tags {
        text.push_str(&label);
        match field.kind {
            RowFieldKind::Present if field.first.0 == NONE => {}
            RowFieldKind::Present => text.push_str("()"),
            RowFieldKind::Absent => text.push('-'),
            RowFieldKind::Either { constant, matched } => {
                text.push('?');
                text.push_str(if constant { "c" } else { "" });
                text.push_str(if matched { "m" } else { "" });
                text.push_str(&field.types.to_string());
            }
        }
        text.push(' ');
    }
    let node = c.g.nodes[more.0 as usize];
    text.push_str(match node.tag() {
        VAR => "| '",
        CONSTR => "| t",
        _ => "| nil",
    });
    if row.name != NONE {
        text.push_str(&format!(" as {}", row.name));
    }
    text.push(']');
    text
}

/// The rows unification must not write (section 8.6, decision 18).
type Rows = (Vec<ExtraDescriptor>, Vec<VariantRow>, Vec<RowFieldRow>);

fn rows_now(c: &Checker) -> Rows {
    (c.extras.descriptors.clone(), c.extras.variants.clone(), c.extras.row_fields.clone())
}

/// Every row that existed at `before` is as it was.
fn assert_rows_kept(c: &Checker, before: &Rows) {
    assert_eq!(c.extras.descriptors[..before.0.len()], before.0[..], "a descriptor row was written");
    assert_eq!(c.extras.variants[..before.1.len()], before.1[..], "a variant row was written");
    assert_eq!(c.extras.row_fields[..before.2.len()], before.2[..], "a row-field row was written");
}

/// Opening a node (section 8.6, decision 34): `[< #A(int) | #B | #C(int)]`
/// with `#A` and `#B` `Reither` and `#C` present has three published
/// slots (`int`, `int`, `more`). Opened it has five: slot 3 is `#A`'s
/// first chain node, `Reither (false, [int], false, e)` with a new
/// unresolved `e`, and so is `#A`'s type slot; slot 4 is `#B`'s unresolved
/// reference. Three nodes, one holder; no row is made or written; every
/// field reads as before (`row_field_repr`, compiler/ml/btype.ml:112-121),
/// except that a `Reither` field now names its reference. A second
/// opening, and the opening of a row without a `Reither` field, do
/// nothing.
/// Reaches: R3f.
#[test]
fn opening_a_row_gives_each_reither_field_a_reference() {
    let mut c = checker(Mode::Success);
    let (a, b) = (constr(&mut c, INT, &[]), constr(&mut c, INT, &[]));
    let more = var(&mut c);
    let tags = [
        ("A", Tag::Either(false, Some(a), false)),
        ("B", Tag::Either(true, None, false)),
        ("C", Tag::Present(Some(b))),
    ];
    let ty = variant_at(&mut c, 2, &tags, more, true, NONE);
    let (before, _, _) = read_row(&mut c, ty);
    let rows = rows_now(&c);
    let nodes = c.g.nodes.len();
    let opened = c.open_row(ty);
    assert_eq!(rows_now(&c), rows, "no row made or written");
    assert_eq!(c.g.nodes.len() - nodes, 3);
    assert_eq!(c.extras.holders.len(), 1);
    assert_eq!(opened, c.g.nodes[ty.0 as usize]);
    assert_eq!(opened.arity(), 5);
    let slot = |c: &Checker, index: u32| c.g.lists[(opened.b + index) as usize];
    let first = slot(&c, 3);
    assert_eq!(slot(&c, 0), first, "the type slot names the chain node");
    assert_eq!((slot(&c, 1), slot(&c, 2)), (b, more));
    let chain = c.g.nodes[first.0 as usize];
    assert_eq!((chain.tag(), chain.head & EXTENDED, chain.a & RES_KIND), (TUPLE, 0, RES_EITHER));
    assert_eq!((chain.arity(), chain.level, c.g.lists[chain.b as usize]), (2, 2, a));
    let end = c.g.lists[chain.b as usize + 1];
    assert_eq!(c.extras.holders[c.g.nodes[end.0 as usize].b as usize].node, first);
    for reference in [end, slot(&c, 4)] {
        let node = c.g.nodes[reference.0 as usize];
        assert_eq!((node.tag(), node.level, node.a), (VAR, 2, NONE));
    }
    let (after, _, _) = read_row(&mut c, ty);
    for ((_, was), (_, is)) in before.iter().zip(&after) {
        assert_eq!((was.first, was.types, was.kind), (is.first, is.types, is.kind));
    }
    assert_eq!((after[0].1.end, after[1].1.end, after[2].1.end), (end, slot(&c, 4), Ty(NONE)));
    let nodes = c.g.nodes.len();
    assert_eq!(c.open_row(ty), opened);
    let plain = variant_at(&mut c, 2, &[("C", Tag::Present(None))], more, true, NONE);
    let node = c.g.nodes[plain.0 as usize];
    assert_eq!(c.open_row(plain), node);
    assert_eq!(c.g.nodes.len(), nodes + 1, "only the node this test pushed");
}

/// Two open rows with no tag in common (compiler/ml/ctype.ml:380-386,
/// 2548-2552, 2596-2616):
///
/// ```text
/// | [p1], _ when not (List.mem_assoc (fst p1) fi2) -> (fi1, fi2, [])
/// ...
/// else newty2 (Ext_pervasives.min_int rm1.level rm2.level) (Tvar None)
/// ...
/// let ty = newgenty (Tvariant {row0 with row_fields = rest}) in
/// update_level !env rm.level ty;
/// link_type rm ty
/// ```
///
/// `[> #A(int)]` against `[> #B]`: no pair; `more` is a new variable at
/// level 2; row 2's variable becomes a new row `[#A(int) | more]` and row
/// 1's a new row `[#B | more]`, both at the level of the variable they
/// replace. Three nodes. The left node is linked to the right one
/// (`link_type t1' t2`, ctype.ml:2331), whose row now reads `B A()`.
/// Reaches: R3f.
#[test]
fn an_open_row_takes_the_tags_it_lacks() {
    let mut c = checker(Mode::Success);
    let int = constr(&mut c, INT, &[]);
    let (rm1, rm2) = (var(&mut c), var(&mut c));
    let left = variant_at(&mut c, 2, &[("A", Tag::Present(Some(int)))], rm1, false, NONE);
    let right = variant_at(&mut c, 2, &[("B", Tag::Present(None))], rm2, false, NONE);
    let rows = rows_now(&c);
    let nodes = c.g.nodes.len() as u32;
    c.unify(left, right).unwrap();
    assert_rows_kept(&c, &rows);
    assert_eq!(c.g.nodes.len() as u32 - nodes, 3, "a variable and two rows");
    assert_eq!(c.g.repr(left), right);
    assert_eq!(shape(&mut c, right), "[B A() | ']");
    assert_eq!(shape(&mut c, rm1), "[B | ']");
    assert_eq!(shape(&mut c, rm2), "[A() | ']");
    let (_, _, more) = read_row(&mut c, right);
    assert!(more.0 >= nodes);
    assert_eq!(c.g.nodes[more.0 as usize].level, 2);
    for built in [rm1, rm2] {
        let built = c.g.repr(built);
        assert_eq!(c.g.nodes[built.0 as usize].level, 2, "lowered from the generic level");
    }
    // Unifying them again is one node on both sides.
    let nodes = c.g.nodes.len();
    c.unify(left, right).unwrap();
    assert_eq!(c.g.nodes.len(), nodes);
}

/// A closed row closes the other and takes nothing; the static row
/// (compiler/ml/ctype.ml:2553, 2596-2616, 2630-2636):
///
/// ```text
/// and closed = row1.row_closed || row2.row_closed in
/// ...
/// if static_row row1 then
///   let rm = row_more row1 in
///   if is_Tvar rm then link_type rm (newty2 rm.level Tnil)
/// ```
///
/// `[#A(int) | #B]` closed against `[> #A(int)]`, in both orders: one
/// pair, `#B` goes to the open row, both rows get a closed rest, the two
/// `int` are unified, and since row 1 read again (`static_row` calls
/// `row_repr`, btype.ml:162-170) is closed with no `Reither` field, the
/// new variable becomes `Tnil`. Four nodes: the variable, two rows, the
/// `Tnil`.
/// Reaches: R3f.
#[test]
fn a_closed_row_closes_the_other_and_a_static_row_ends_in_nil() {
    for swap in [false, true] {
        let mut c = checker(Mode::Success);
        let (i1, i2) = (constr(&mut c, INT, &[]), constr(&mut c, INT, &[]));
        let (rm1, rm2) = (var(&mut c), var(&mut c));
        let tags = [("A", Tag::Present(Some(i1))), ("B", Tag::Present(None))];
        let closed = variant_at(&mut c, 2, &tags, rm1, true, NONE);
        let open = variant_at(&mut c, 2, &[("A", Tag::Present(Some(i2)))], rm2, false, NONE);
        let rows = rows_now(&c);
        let nodes = c.g.nodes.len();
        let (left, right) = if swap { (open, closed) } else { (closed, open) };
        c.unify(left, right).unwrap();
        assert_rows_kept(&c, &rows);
        assert_eq!(c.g.nodes.len() - nodes, 4, "swap {swap}");
        assert_eq!(shape(&mut c, right), "[closed A() B | nil]", "swap {swap}");
        assert_eq!(shape(&mut c, rm2), "[closed B | nil]");
        assert_eq!(shape(&mut c, rm1), "[closed | nil]");
        assert_eq!(c.g.repr(i1), c.g.repr(i2), "the arguments of the common tag are unified");
    }
}

/// The two clashes of a row that may not gain a tag, in `Mode::Explain`
/// (compiler/ml/ctype.ml:2564-2573, 2596-2604, 2637-2641):
///
/// ```text
/// then raise (Unify [(mkvariant [] true, mkvariant [] true)]);
/// ...
/// (if (rest <> [] && (row.row_closed || row_fixed row)) || ...
///  then
///    let t1 = mkvariant [] true and t2 = mkvariant rest false in
///    raise (Unify [(if row == row1 then (t1, t2) else (t2, t1))]));
/// ...
/// with exn -> log_type rm1; rm1.desc <- md1; log_type rm2; rm2.desc <- md2;
/// ```
///
/// Closed `[#A]` against open `[> #B]`: `set_more row2 [A]` links row 2's
/// variable; `set_more row1 [B]` clashes with the pair (an empty closed
/// row, an open row of `#B`). Afterwards row 2's variable is a variable
/// again and the left node is not linked (`t1'.desc <- d1`, ctype.ml:2437).
/// Closed `[#A]` against closed `[#B]`: the empty type, before anything is
/// linked; the pair is two empty closed rows.
/// Reaches: R3f.
#[test]
fn a_closed_row_refuses_a_tag_and_the_empty_type_is_a_clash() {
    for both_closed in [false, true] {
        let mut c = checker(Mode::Explain);
        let (rm1, rm2) = (var(&mut c), var(&mut c));
        let left = variant_at(&mut c, 2, &[("A", Tag::Present(None))], rm1, true, NONE);
        let right = variant_at(&mut c, 2, &[("B", Tag::Present(None))], rm2, both_closed, NONE);
        let rows = rows_now(&c);
        assert!(c.unify(left, right).is_err());
        assert_rows_kept(&c, &rows);
        assert_eq!((c.g.repr(left), c.g.repr(rm1), c.g.repr(rm2)), (left, rm1, rm2));
        assert_eq!(c.g.nodes[rm2.0 as usize].tag(), VAR);
        assert_eq!(shape(&mut c, left), "[closed A | ']");
        let trace = c.trace.clone();
        assert_eq!(trace.len(), 2);
        assert_eq!(trace[0], [left, right]);
        let pair = [shape(&mut c, trace[1][0]), shape(&mut c, trace[1][1])];
        let expected = if both_closed { ["[closed | ']", "[closed | ']"] } else { ["[closed | ']", "[B | ']"] };
        assert_eq!(pair, expected, "both closed {both_closed}");
        assert!(c.frames.is_empty() && c.saved.is_empty());
    }
}

/// `Reither` against a present tag, and `filter_row_fields`
/// (compiler/ml/ctype.ml:388-397, 2711-2717):
///
/// ```text
/// | Reither (_, _, false, e) when erase -> set_row_field e Rabsent; fi
/// ...
/// | Reither (false, tl, _, e1), Rpresent (Some t2) when not fixed1 -> (
///   set_row_field e1 f2;
///   update_level !env (repr more).level t2;
///   try List.iter (fun t1 -> unify env t1 t2) tl
/// ```
///
/// `[< #A(int) | #B]` (both `Reither`, closed) against `[> #A(int)]`: `#A`
/// becomes present and its type is unified with the right one; `#B`
/// stays `Reither` and goes to the open row with its reference (the old
/// checker shows the same row: `[closed #A(int) #B?c^0() | ']`,
/// `differential::tests::old_checker_resolves_a_shared_reference_for_
/// every_holder`). Against the closed `[#A(int)]`, `#B` is erased: absent
/// and not in the rest, and the row is static.
/// Reaches: R3f.
#[test]
fn a_reither_tag_becomes_present_and_a_closed_row_erases_the_others() {
    for closed in [false, true] {
        let mut c = checker(Mode::Success);
        let (i1, i2) = (constr(&mut c, INT, &[]), constr(&mut c, INT, &[]));
        let (rm1, rm2) = (var(&mut c), var(&mut c));
        let tags = [("A", Tag::Either(false, Some(i1), false)), ("B", Tag::Either(true, None, false))];
        let left = variant_at(&mut c, 2, &tags, rm1, true, NONE);
        let right = variant_at(&mut c, 2, &[("A", Tag::Present(Some(i2)))], rm2, closed, NONE);
        let rows = rows_now(&c);
        c.unify(left, right).unwrap();
        assert_rows_kept(&c, &rows);
        assert_eq!(c.g.repr(i1), c.g.repr(i2));
        let expected = if closed { "[closed A() | nil]" } else { "[closed A() B?c0 | ']" };
        assert_eq!(shape(&mut c, right), expected, "closed {closed}");
    }
}

/// How a test makes a tag from the `int` node of its row.
type Kind = fn(Ty) -> Tag;

/// Two rows, each with the one tag `X` of kind `left` and `right`, both
/// open; what `X` is in the right row afterwards, or `None` for a clash.
fn tag_pair(left: Kind, right: Kind, fixed: bool) -> Option<String> {
    let mut c = checker(Mode::Success);
    let (i1, i2) = (constr(&mut c, INT, &[]), constr(&mut c, INT, &[]));
    let rm1 = var(&mut c);
    // A row whose `more` is a constructor is fixed (`row_fixed`,
    // compiler/ml/btype.ml:153-160).
    let rm2 = if fixed { constr(&mut c, T, &[]) } else { var(&mut c) };
    let l = variant_at(&mut c, 2, &[("X", left(i1))], rm1, false, NONE);
    let r = variant_at(&mut c, 2, &[("X", right(i2))], rm2, false, NONE);
    let rows = rows_now(&c);
    let result = c.unify(l, r);
    assert_rows_kept(&c, &rows);
    result.ok()?;
    let text = shape(&mut c, r);
    Some(text.split(' ').next().unwrap().trim_start_matches('[').to_string())
}

/// `unify_row_field`, one pair of kinds at a time, in the order of its
/// arms (compiler/ml/ctype.ml:2643-2730). `X()` is present with an
/// argument, `X` present without, `X-` absent, `X?cm2` `Reither` with its
/// flags and two types.
///
/// - `Rpresent (Some t1), Rpresent (Some t2) -> unify env t1 t2`;
///   `Rpresent None, Rpresent None -> ()`.
/// - Two `Reither`, no row fixed, neither matched (ctype.ml:2676-2708):
///   each side gains the types of the other it lacks (`remq`), `c` is
///   `c1 || c2`. With one matched (`redo`, ctype.ml:2663-2675) the types
///   are unified first: `if c1 || c2 then raise (Unify [])`; otherwise
///   the two `int` become one node and neither side gains a type.
/// - Two `Reither` of one length, a row fixed, neither constant (PR#7496,
///   ctype.ml:2652-2661): both get a `Reither` with no type and one new
///   reference, and the types are unified pairwise.
/// - `Reither (_, _, false, e1), Rabsent when not fixed1 -> set_row_field
///   e1 f2`, and mirrored; a matched one clashes.
/// - `Reither (false, tl, _, e1), Rpresent (Some t2) when not fixed1`, and
///   mirrored; `Reither (true, [], _, e1), Rpresent None`, and mirrored.
/// - `| _ -> raise (Unify [])`.
///
/// Reaches: R3f.
#[test]
fn each_pair_of_tag_kinds() {
    let some: Kind = |ty| Tag::Present(Some(ty));
    let none: Kind = |_| Tag::Present(None);
    let absent: Kind = |_| Tag::Absent;
    let either: Kind = |ty| Tag::Either(false, Some(ty), false);
    let constant: Kind = |_| Tag::Either(true, None, false);
    let matched: Kind = |ty| Tag::Either(false, Some(ty), true);
    let constant_matched: Kind = |_| Tag::Either(true, None, true);
    let cases: [(&str, Kind, Kind, Option<&str>); 20] = [
        ("some some", some, some, Some("X()")),
        ("none none", none, none, Some("X")),
        ("some none", some, none, None),
        ("either either", either, either, Some("X?2")),
        ("constant either", constant, either, Some("X?c1")),
        ("either constant", either, constant, Some("X?c1")),
        ("matched either", matched, either, Some("X?m1")),
        ("constant-matched either", constant_matched, either, None),
        ("either absent", either, absent, Some("X-")),
        ("absent either", absent, either, Some("X-")),
        ("matched absent", matched, absent, None),
        ("absent absent", absent, absent, Some("X-")),
        ("either some", either, some, Some("X()")),
        ("some either", some, either, Some("X()")),
        ("constant none", constant, none, Some("X")),
        ("none constant", none, constant, Some("X")),
        ("constant some", constant, some, None),
        ("either none", either, none, None),
        ("none absent", none, absent, None),
        ("absent some", absent, some, None),
    ];
    for (label, left, right, expected) in cases {
        assert_eq!(tag_pair(left, right, false).as_deref(), expected, "{label}");
    }
    // A fixed row 2: PR#7496 for two `Reither` of one length; and the arms
    // guarded by `when not fixed2` clash.
    assert_eq!(tag_pair(either, either, true).as_deref(), Some("X?1"));
    assert_eq!(tag_pair(some, either, true), None);
    assert_eq!(tag_pair(absent, either, true), None);
    assert_eq!(tag_pair(either, some, true).as_deref(), Some("X()"));
}

/// The name of the row (compiler/ml/ctype.ml:2574-2586):
///
/// ```text
/// if row1.row_name <> None && (row1.row_closed || empty r2)
///    && ((not row2.row_closed) || (keep (fun f1 f2 -> (f1, f2)) && empty r1))
/// then row1.row_name
/// ```
///
/// A named closed `[#A]` against an open `[> #A]`: row 1's name. A named
/// closed `[< #A | #B]` (`#B` `Reither`) against a closed `[#A]` without a
/// name: `r1` is `#B`, which is not absent when the name is chosen, so
/// neither test holds and the row has no name.
/// Reaches: R3f.
#[test]
fn the_row_keeps_a_name_only_when_it_stays_the_named_row() {
    let mut c = checker(Mode::Success);
    let (rm1, rm2) = (var(&mut c), var(&mut c));
    let left = variant_at(&mut c, 2, &[("A", Tag::Present(None))], rm1, true, 5);
    let right = variant_at(&mut c, 2, &[("A", Tag::Present(None))], rm2, false, NONE);
    c.unify(left, right).unwrap();
    assert_eq!(shape(&mut c, right), "[closed A | nil as 5]");

    let mut c = checker(Mode::Success);
    let (rm1, rm2) = (var(&mut c), var(&mut c));
    let tags = [("A", Tag::Present(None)), ("B", Tag::Either(true, None, false))];
    let left = variant_at(&mut c, 2, &tags, rm1, true, 5);
    let right = variant_at(&mut c, 2, &[("A", Tag::Present(None))], rm2, true, NONE);
    c.unify(left, right).unwrap();
    assert_eq!(shape(&mut c, right), "[closed A | nil]");
}

/// A fixed row (compiler/ml/ctype.ml:2548-2551, 2596-2612; `row_fixed`,
/// btype.ml:153-160: a row whose `more` is a constructor):
///
/// ```text
/// let more = if fixed1 then rm1 else if fixed2 then rm2 else ...
/// ...
/// if row_fixed row then
///   if more == rm then () else if is_Tvar rm then link_type rm more
///   else unify env rm more
/// ```
///
/// Open `[> #A]` against the fixed `[#A | #B | t]`: `more` is the fixed
/// row's; nothing is made for it; the open row's variable becomes a new
/// row `[#B | t]` marked fixed. Open `[> #A | #C]` against it: the fixed
/// row would gain `#C`, a clash.
/// Reaches: R3f.
#[test]
fn a_fixed_row_gains_nothing() {
    let mut c = checker(Mode::Success);
    let rm1 = var(&mut c);
    let rm2 = constr(&mut c, T, &[]);
    let open = variant_at(&mut c, 2, &[("A", Tag::Present(None))], rm1, false, NONE);
    let tags = [("A", Tag::Present(None)), ("B", Tag::Present(None))];
    let fixed = variant_at(&mut c, 2, &tags, rm2, false, NONE);
    let nodes = c.g.nodes.len();
    c.unify(open, fixed).unwrap();
    assert_eq!(c.g.nodes.len() - nodes, 1, "the row the open one gains");
    assert_eq!(shape(&mut c, fixed), "[A B | t]");
    assert_eq!(shape(&mut c, rm1), "[fixed B | t]");
    let (_, _, more) = read_row(&mut c, rm1);
    assert_eq!(more, rm2);

    let mut c = checker(Mode::Success);
    let rm1 = var(&mut c);
    let rm2 = constr(&mut c, T, &[]);
    let wide = [("A", Tag::Present(None)), ("C", Tag::Present(None))];
    let open = variant_at(&mut c, 2, &wide, rm1, false, NONE);
    let fixed = variant_at(&mut c, 2, &tags, rm2, false, NONE);
    assert!(c.unify(open, fixed).is_err());
}

/// The cost of rows, as relations between n = 1,000 and n = 10,000 (the
/// name comparisons of the sort are not steps): two closed rows of n
/// common tags listed in opposite orders; two open rows of n tags each
/// with none in common; a row of n tags against a row that is a chain of
/// n nodes of one tag each (`row_repr`, compiler/ml/btype.ml:126-135).
/// Reaches: R3f.
#[test]
fn rows_of_ten_thousand_tags_are_linear() {
    let labels = |prefix: &str, n: u32| -> Vec<String> {
        (0..n).map(|at| format!("{prefix}{at:05}")).collect()
    };
    let common = |n: u32| {
        let mut c = checker(Mode::Success);
        let labels = labels("t", n);
        let forward: Vec<(&str, Tag)> = labels.iter().map(|l| (l.as_str(), Tag::Present(None))).collect();
        let backward: Vec<(&str, Tag)> = forward.iter().rev().copied().collect();
        let (rm1, rm2) = (var(&mut c), var(&mut c));
        let left = variant_at(&mut c, 2, &backward, rm1, true, NONE);
        let right = variant_at(&mut c, 2, &forward, rm2, true, NONE);
        steps::scope(|| c.unify(left, right).unwrap())
    };
    let (small, large) = (common(1_000), common(10_000));
    assert!(large <= 11 * small, "common: {small} {large}");

    let disjoint = |n: u32| {
        let mut c = checker(Mode::Success);
        let (f, g) = (labels("f", n), labels("g", n));
        let f: Vec<(&str, Tag)> = f.iter().map(|l| (l.as_str(), Tag::Present(None))).collect();
        let g: Vec<(&str, Tag)> = g.iter().map(|l| (l.as_str(), Tag::Present(None))).collect();
        let (rm1, rm2) = (var(&mut c), var(&mut c));
        let left = variant_at(&mut c, 2, &f, rm1, false, NONE);
        let right = variant_at(&mut c, 2, &g, rm2, false, NONE);
        let nodes = c.g.nodes.len();
        let count = steps::scope(|| c.unify(left, right).unwrap());
        assert_eq!(c.g.nodes.len() - nodes, 3, "a changed row is one node, whatever it gains");
        count
    };
    let (small, large) = (disjoint(1_000), disjoint(10_000));
    assert!(large <= 11 * small, "disjoint: {small} {large}");

    let chain = |n: u32| {
        let mut c = checker(Mode::Success);
        let labels = labels("t", n);
        let flat: Vec<(&str, Tag)> = labels.iter().map(|l| (l.as_str(), Tag::Present(None))).collect();
        let rm1 = var(&mut c);
        let left = variant_at(&mut c, 2, &flat, rm1, false, NONE);
        let mut right = var(&mut c);
        for label in &labels {
            right = variant_at(&mut c, 2, &[(label.as_str(), Tag::Present(None))], right, false, NONE);
        }
        steps::scope(|| c.unify(left, right).unwrap())
    };
    let (small, large) = (chain(1_000), chain(10_000));
    assert!(large <= 11 * small, "chain: {small} {large}");
}

/// A clash below a swapped `unify3` is reported reversed, also when
/// `set_more` made it (compiler/ml/ctype.ml:2299-2303, 2600-2606):
///
/// ```text
/// if unify_eq t1 t1' || not (unify_eq t2 t2') then unify3 env t1 t1' t2 t2'
/// else
///   try unify3 env t2 t2' t1 t1'
///   with Unify trace ->
///     raise (Unify (List.map (fun (x, y) -> (y, x)) trace))
/// ...
/// (if (rest <> [] && (row.row_closed || row_fixed row))
///     || (closed && row_fixed row && not row.row_closed)
///  then
///    let t1 = mkvariant [] true and t2 = mkvariant rest false in
///    raise (Unify [(if row == row1 then (t1, t2) else (t2, t1))]));
/// ```
///
/// `pv` (an abbreviation of the closed `[#N]`) against `[> #C]` (the shape
/// of generated seed 2000082): unify3 runs on `([> #C], [#N])`, so row 1 is
/// the open one and `set_more row2 [C]` raises `([C], [closed])`; the
/// reversal makes the last pair (the closed empty row, the row of `#C`).
/// Reaches: R3f.
#[test]
fn a_set_more_clash_below_a_swapped_unify3_is_reversed() {
    let mut c = checker(Mode::Explain);
    let pv = c.types.rows.len() as u32;
    c.types.rows.push(c.types.rows[MYINT as usize]);
    let nil = nil_at(&mut c, GENERIC);
    let body = variant_at(&mut c, GENERIC, &[("N", Tag::Present(None))], nil, true, NONE);
    abbreviation(&mut c, pv, &[], body);
    let left = constr(&mut c, pv, &[]);
    let rm = var(&mut c);
    let right = variant_at(&mut c, 2, &[("C", Tag::Present(None))], rm, false, NONE);
    assert!(c.unify(left, right).is_err());
    let trace = c.trace.clone();
    assert_eq!(trace[0], [left, right]);
    let last = trace[trace.len() - 1];
    let pair = [shape(&mut c, last[0]), shape(&mut c, last[1])];
    assert_eq!(pair, ["[closed | ']", "[C | ']"]);
}

/// An entry already in the trace when the enclosing pairs are added is
/// reversed below a swapped `unify3` too (compiler/ml/ctype.ml:2301-2303,
/// 600):
///
/// ```text
/// try unify3 env t2 t2' t1 t1'
/// with Unify trace ->
///   raise (Unify (List.map (fun (x, y) -> (y, x)) trace))
/// ...
/// if level < get_level env p then raise (Unify [(ty, newvar2 level)]);
/// ```
///
/// `pa<'x>` (`('x, int)`) with `'x` at level 1 against `(t, int)`, `t` of
/// scope 2: unify3 runs on the tuple and the expansion, and the child pair
/// `(t, 'x)` fails later, as a frame: lowering `t` to level 1 escapes with
/// `(t, newvar)`. The reversal makes the pairs below the top one
/// `('x, t)` and `(newvar, t)`.
/// Reaches: R3d.
#[test]
fn an_escape_below_a_swapped_unify3_is_reversed() {
    let mut c = checker(Mode::Explain);
    c.types.rows[T as usize].scope = 2;
    c.types.scoped = 2;
    let x = var_at(&mut c, 1);
    let left = constr(&mut c, PA, &[x]);
    let t = constr(&mut c, T, &[]);
    let int = constr(&mut c, INT, &[]);
    let right = tuple(&mut c, &[t, int]);
    assert!(c.unify(left, right).is_err());
    let trace = c.trace.clone();
    assert_eq!(trace.len(), 3);
    assert_eq!(trace[0], [left, right]);
    assert_eq!(trace[1], [x, t]);
    assert_eq!(trace[2][1], t);
    let escaped = c.g.nodes[trace[2][0].0 as usize];
    assert_eq!((escaped.tag(), escaped.level), (VAR, 1));
}

// ---------------------------------------------------------------------------
// R3g: universal variables and polymorphic types (section 8.6, decisions
// 49 to 51).
// ---------------------------------------------------------------------------

use super::rows::{PolyScope, partner_node};

/// A universal variable with no name at `level` (`newty2 level (Tunivar
/// None)`), with a descriptor row of its own, counted (`Extras::univar`).
fn univar_at(c: &mut Checker, level: u32) -> Ty {
    let a = c.extras.univar(NONE);
    let b = c.g.lists.len() as u32;
    c.g.push(Node {
        head: TUPLE | EXTENDED,
        level,
        a,
        b,
    })
}

/// `Tpoly (body, binders)` at `level`: slot 0 the body, then the bound
/// variables (tc/segment.rs, `ExtraDescriptor::Poly`).
fn poly_of(c: &mut Checker, level: u32, body: Ty, binders: &[Ty]) -> Ty {
    let mut slots = vec![body];
    slots.extend_from_slice(binders);
    extended_at(c, level, ExtraDescriptor::Poly, &slots)
}

/// `poly((first, second, third); [u, v])` at level 2 over two new
/// universal variables `u` and `v`, the tuple's elements chosen among
/// them by index (0 is `u`, 1 is `v`): the type, `u`, `v`.
fn two_binders(c: &mut Checker, elements: [usize; 3], order: [usize; 2]) -> (Ty, [Ty; 2]) {
    let vars = [univar_at(c, 2), univar_at(c, 2)];
    let body = tuple_at(c, 2, &elements.map(|at| vars[at]));
    (poly_of(c, 2, body, &order.map(|at| vars[at])), vars)
}

/// The nodes a failed unification must leave as they were.
fn nodes_now(c: &Checker) -> Vec<Node> {
    c.g.nodes.clone()
}

/// Universal variables are paired by position in the two binder lists,
/// never by name or by count (compiler/ml/ctype.ml:1544-1559, 1670-1672,
/// 2244-2247):
///
/// ```text
/// | (cl1, cl2) :: rem -> (
///   match (find_univ t1 cl1, find_univ t2 cl2) with
///   | Some {contents = Some t'2}, Some _ when t2 == repr t'2 -> ()
///   | Some ({contents = None} as r1), Some ({contents = None} as r2) ->
///     set_univar r1 t2;
///     set_univar r2 t1
///   | None, None -> unify_univar t1 t2 rem
///   | _ -> raise (Unify []))
/// | [] -> raise (Unify [])
/// ...
/// let cl1 = List.map (fun t -> (t, ref None)) tl1
/// and cl2 = List.map (fun t -> (t, ref None)) tl2 in
/// univar_pairs := (cl1, cl2) :: (cl2, cl1) :: old_univars;
/// ...
/// | Tunivar _, Tunivar _ ->
///   unify_univar t1 t2 !(current_univar_pairs ());
///   update_level !env t1.level t2;
///   link_type t1 t2
/// ```
///
/// Witnesses, observed on the old checker in
/// `differential::tests::old_checker_pairs_universal_variables_by_position`:
/// - `poly((u, v, u); u v)` against `poly((v', u', v'); v' u')`: the
///   first variables pair and the second ones pair, whatever they are
///   called; each left variable is a link to its partner, the left type a
///   link to the right one, and no scope stays open.
/// - `poly((u, v, u); u v)` against `poly((u', v', v'); u' v')`: the third
///   element pairs the first variable with the second: a clash. In the
///   explaining mode the trace is the two types, the two bodies, and the
///   two variables as they stood (`u` is a link to `u'` by then: the pair
///   is `(u', v')`).
/// - `poly((u, u, v); u v)` against `poly((u', v', v'); u' v')`: `u` has
///   `u'` as its partner when it meets `v'`: a clash (the first arm needs
///   `t2 == repr t'2`, the second two empty partners).
///
/// No descriptor row is written.
/// Reaches: R3g.
#[test]
fn universal_variables_pair_by_position() {
    let mut c = checker(Mode::Success);
    let (left, [u, v]) = two_binders(&mut c, [0, 1, 0], [0, 1]);
    let (right, [u2, v2]) = two_binders(&mut c, [1, 0, 1], [1, 0]);
    let rows = rows_now(&c);
    c.unify(left, right).unwrap();
    assert_eq!(c.g.repr(left), right);
    // `u` is the first bound variable of the left type, `v2` of the right.
    assert_eq!((c.g.repr(u), c.g.repr(v)), (v2, u2));
    assert!(c.scopes.is_empty() && c.frames.is_empty());
    assert_rows_kept(&c, &rows);

    for (first, second) in [([0, 1, 0], [0, 1, 1]), ([0, 0, 1], [0, 1, 1])] {
        for mode in [Mode::Success, Mode::Explain] {
            let mut c = checker(mode);
            let (left, _) = two_binders(&mut c, first, [0, 1]);
            let (right, [u2, v2]) = two_binders(&mut c, second, [0, 1]);
            assert!(c.unify(left, right).is_err(), "{first:?} {second:?}");
            assert!(c.scopes.is_empty() && c.frames.is_empty() && c.saved.is_empty());
            if mode == Mode::Explain {
                assert_eq!(c.trace.len(), 3, "{:?}", c.trace);
                assert_eq!(c.trace[0], [left, right]);
                assert_eq!(c.trace[2], [u2, v2]);
            }
        }
    }
}

/// The scopes are searched innermost first, and a pair that neither list
/// of a scope holds goes on to the next (compiler/ml/ctype.ml:1557,
/// `None, None -> unify_univar t1 t2 rem`); a variable of an outer scope
/// against one the inner scope binds is refused at the inner scope (one
/// found, the other not: `| _ -> raise (Unify [])`, ctype.ml:1558).
/// Observed on the old checker in
/// `differential::tests::old_checker_searches_the_scopes_innermost_first`.
/// Witnesses: `poly(poly((a, b); b); a)` against the same shape unifies
/// and pairs `a` with `a'` from inside the inner scope; against
/// `poly(poly((b', a'); b'); a')` it fails at the first element, `a`
/// against `b'`, the last pair of the trace.
/// Reaches: R3g.
#[test]
fn a_variable_of_an_outer_scope_pairs_in_its_scope() {
    let nested = |c: &mut Checker, swap: bool| {
        let (a, b) = (univar_at(c, 2), univar_at(c, 2));
        let body = if swap {
            tuple_at(c, 2, &[b, a])
        } else {
            tuple_at(c, 2, &[a, b])
        };
        let inner = poly_of(c, 2, body, &[b]);
        (poly_of(c, 2, inner, &[a]), a, b)
    };
    let mut c = checker(Mode::Success);
    let (left, a, b) = nested(&mut c, false);
    let (right, a2, b2) = nested(&mut c, false);
    c.unify(left, right).unwrap();
    assert_eq!((c.g.repr(a), c.g.repr(b)), (a2, b2));
    assert!(c.scopes.is_empty());

    let mut c = checker(Mode::Explain);
    let (left, a, _) = nested(&mut c, false);
    let (right, _, b2) = nested(&mut c, true);
    assert!(c.unify(left, right).is_err());
    assert_eq!(c.trace.len(), 4, "{:?}", c.trace);
    assert_eq!(c.trace[3], [a, b2]);
    assert!(c.scopes.is_empty() && c.frames.is_empty());
}

/// What the scopes hold and who cuts them back (section 8.6, decision
/// 50). `enter_poly` pushes one [`PolyScope`] and one partner node per
/// bound variable; a pairing writes two partner nodes (`set_univar`,
/// compiler/ml/btype.ml:739-741, which logs `Cuniv`). A failure cuts the
/// scopes back (`univar_pairs := old_univars; raise exn`,
/// compiler/ml/ctype.ml:1677-1679) in both modes; inside a speculation
/// its owner's restore puts every node back, partner nodes included,
/// with no log of its own.
/// Reaches: R3g.
#[test]
fn a_failure_leaves_no_scope_and_a_restore_undoes_the_pairings() {
    let mut c = checker(Mode::Success);
    let (left, _) = two_binders(&mut c, [0, 1, 0], [0, 1]);
    let (right, _) = two_binders(&mut c, [0, 1, 1], [0, 1]);
    let before = nodes_now(&c);
    let token = c.g.speculate();
    assert!(c.unify(left, right).is_err());
    assert!(c.scopes.is_empty() && c.frames.is_empty());
    // Four partner nodes (two variables a side), consecutive, and nothing
    // else: the scope named the first.
    assert_eq!(c.g.nodes.len(), before.len() + 4);
    c.restore(token);
    assert_eq!(c.g.nodes[..before.len()], before[..]);
    for node in &c.g.nodes[before.len()..] {
        assert_eq!(
            *node,
            partner_node(Ty(NONE)),
            "a pairing survived the restore"
        );
    }
    // Entering alone: what one scope is.
    let mut c = checker(Mode::Success);
    let (left, _) = two_binders(&mut c, [0, 1, 0], [0, 1]);
    let (right, _) = two_binders(&mut c, [0, 1, 0], [0, 1]);
    let (l, r) = (c.g.nodes[left.0 as usize], c.g.nodes[right.0 as usize]);
    let nodes = c.g.nodes.len() as u32;
    c.enter_poly(l, r).unwrap();
    assert_eq!(
        c.scopes,
        [PolyScope {
            left: l.b + 1,
            right: r.b + 1,
            left_len: 2,
            right_len: 2,
            partners: Ty(nodes)
        }]
    );
    assert_eq!(c.frames.len(), 2);
    assert_eq!(c.frames[0].kind, super::unify::FrameKind::LeavePoly);
    assert_eq!(c.frames[0].extra, 0);
    assert_eq!(
        [c.frames[1].left, c.frames[1].right],
        [c.g.lists[l.b as usize], c.g.lists[r.b as usize]]
    );
}

/// `enter_poly` tests escape BEFORE it pushes the scopes and before the
/// bodies are unified (compiler/ml/ctype.ml:1656-1669):
///
/// ```text
/// let tl1 = List.map repr tl1 and tl2 = List.map repr tl2 in
/// if
///   List.exists (fun t -> Type_set.mem t known_univars) tl1
///   && univars_escape env old_univars tl1 (newty (Tpoly (t2, tl2)))
///   || List.exists (fun t -> Type_set.mem t known_univars) tl2
///      && univars_escape env old_univars tl2 (newty (Tpoly (t1, tl1)))
/// then raise (Unify []);
/// ```
///
/// The cases of `differential::tests::old_checker_tests_escape_before_
/// the_bodies` (observed), by hand. Left: `outer = poly(inner; u)`,
/// `inner = poly((u, second); u)`: `u` is bound twice. Right: `outer' =
/// poly(inner'; u')`, `inner' = poly((first', second'); w')`.
/// - `inner' = poly((w', u'); w')`: the family of `u` is `u` and `u'`
///   (`get_univar_family`, ctype.ml:1612-1623), and `u'` is in `inner'`
///   outside a binder of the family: a clash. The trace is the two outer
///   types and the two inner types; every node is as it was, apart from
///   the inner types' link put back; the only nodes made are the two
///   partner nodes of the outer scope.
/// - The same with `second` an arrow, which could not unify with `u'`:
///   the same trace (a test after the bodies would end at the arrow).
/// - `inner' = poly((w', w'); w')`: no variable of the family in
///   `inner'`: the bodies unify, `u` is a link to `w'`, and `u'`, which
///   no body names, stays a node of its own.
///
/// Reaches: R3g.
#[test]
fn a_known_binder_escapes_before_the_bodies() {
    let build = |c: &mut Checker, arrow: bool, right: [usize; 2]| {
        let u = univar_at(c, 2);
        let second = if arrow {
            let x = var(c);
            arrow_at(c, 2, &[x], x)
        } else {
            u
        };
        let body = tuple_at(c, 2, &[u, second]);
        let inner = poly_of(c, 2, body, &[u]);
        let outer = poly_of(c, 2, inner, &[u]);
        let vars = [univar_at(c, 2), univar_at(c, 2)];
        let body2 = tuple_at(c, 2, &right.map(|at| vars[at]));
        let inner2 = poly_of(c, 2, body2, &[vars[1]]);
        let outer2 = poly_of(c, 2, inner2, &[vars[0]]);
        ([outer, inner, outer2, inner2], u, vars)
    };
    for arrow in [false, true] {
        let mut c = checker(Mode::Explain);
        // `(w', u')`: index 1 is `w'`, index 0 is `u'`.
        let ([outer, inner, outer2, inner2], _, _) = build(&mut c, arrow, [1, 0]);
        let before = nodes_now(&c);
        assert!(c.unify(outer, outer2).is_err());
        assert_eq!(
            c.trace,
            [[outer, outer2], [inner, inner2]],
            "arrow: {arrow}"
        );
        assert_eq!(c.g.nodes[..before.len()], before[..]);
        assert_eq!(c.g.nodes.len(), before.len() + 2);
        assert!(c.scopes.is_empty() && c.frames.is_empty());
    }
    let mut c = checker(Mode::Success);
    let ([outer, _, outer2, _], u, [u2, w2]) = build(&mut c, false, [1, 1]);
    c.unify(outer, outer2).unwrap();
    assert_eq!([c.g.repr(u), c.g.repr(u2)], [w2, u2]);
    // Directly: the family walk. `binder` binds `u`; `other` names `u'`.
    let mut c = checker(Mode::Success);
    let ([outer, inner, outer2, inner2], _, _) = build(&mut c, false, [1, 0]);
    let d = [outer, inner, outer2, inner2].map(|ty| c.g.nodes[ty.0 as usize]);
    c.enter_poly(d[0], d[2]).unwrap();
    assert!(c.univars_escape(d[1], d[3]));
    assert!(
        !c.univars_escape(d[3], d[1]),
        "`w'` has no partner and `inner` does not name it"
    );
}

/// A universal variable outside its binder (compiler/ml/ctype.ml:
/// 1563-1607, 2216-2219):
///
/// ```text
/// | Tunivar _ ->
///   if not (Type_set.mem ty bound) then raise (Unify [(ty, newgenvar ())])
/// | Tpoly (ty, tyl) ->
///   let bound = List.fold_right Type_set.add (List.map repr tyl) bound in
///   occur_rec bound ty
/// | Tconstr (_, [], _) -> ()
/// | Tconstr (p, tl, _) -> (
///   try
///     let td = Env.find_type p env in
///     List.iter2
///       (fun t v ->
///         if Variance.(mem May_pos v || mem May_neg v) then
///           occur_rec bound t)
///       tl td.type_variance
///   with Not_found -> List.iter (occur_rec bound) tl)
/// ...
/// let unify1_var env t1 t2 =
///   assert (is_Tvar t1);
///   occur env t1 t2;
///   occur_univar env t2;
/// ```
///
/// Observed on the old checker in `differential::tests::old_checker_
/// refuses_a_free_universal_variable`. Witnesses: a variable against `u`,
/// and against `(int, u)`, is refused, in the explaining mode with the
/// pair of the unification and then the pair of `u` and a new GENERIC
/// variable; against `poly((int, u); u)` it is bound. `phantom<u>`: the
/// hand-built table has no declaration row, so the argument is visited
/// and the variable refused (`with Not_found`); with the parameter marked
/// as one the type does not use, the variable is bound.
/// Reaches: R3g.
#[test]
fn a_free_universal_variable_is_refused() {
    for mode in [Mode::Success, Mode::Explain] {
        let mut c = checker(mode);
        let u = univar_at(&mut c, 2);
        let int = constr(&mut c, INT, &[]);
        let pair = tuple(&mut c, &[int, u]);
        let closed = poly_of(&mut c, 2, pair, &[u]);
        let phantom = constr(&mut c, PHANTOM, &[u]);
        for target in [u, pair, phantom] {
            for reversed in [false, true] {
                let x = var(&mut c);
                let before = nodes_now(&c);
                let result = if reversed {
                    c.unify(target, x)
                } else {
                    c.unify(x, target)
                };
                assert!(result.is_err());
                assert_eq!(
                    c.g.nodes[..before.len()],
                    before[..],
                    "nothing is linked or lowered"
                );
                if mode == Mode::Explain {
                    assert_eq!(c.trace.len(), 2, "{:?}", c.trace);
                    assert_eq!(c.trace[0], if reversed { [target, x] } else { [x, target] });
                    let [free, fresh] = c.trace[1];
                    let fresh = c.g.nodes[fresh.0 as usize];
                    assert_eq!(
                        (free, fresh.tag(), fresh.level, fresh.a),
                        (u, VAR, GENERIC, NONE)
                    );
                }
            }
        }
        let x = var(&mut c);
        c.unify(x, closed).unwrap();
        assert_eq!(c.g.repr(x), closed);
        // `phantom`'s parameter does not occur in its body.
        c.types.variances = vec![NONE; TYPES];
        c.types.variances[PHANTOM as usize] = 0;
        c.types.occurs = vec![0];
        let x = var(&mut c);
        c.unify(x, phantom).unwrap();
        assert_eq!(c.g.repr(x), phantom);
    }
}

/// The walk of `occur_univar` finds the FIRST free universal variable in
/// `iter_type_expr`'s order, binds the variables of a polymorphic type
/// for its body only, and visits a node again when the context it was
/// visited in has closed (compiler/ml/ctype.ml:1565-1589: `bound`,
/// `visited`; compiler/ml/btype.ml:250-272).
/// - `((p, q) => r, s)` with four universal variables: the answer is `p`
///   (an arrow's parameters, then its result, then the next element).
/// - `(poly((u, v); u), w)`: `v` (inside the polymorphic type and not
///   bound by it), before `w`.
/// - `shared = (u, int)`, `(poly(shared; u), shared)`: inside the
///   polymorphic type `u` is bound and `shared` is visited; outside, that
///   context has closed, `shared` is visited again and `u` is free.
/// - `(shared, poly(shared; u))` with `u` free at the first element: `u`.
/// - `poly(poly((u, v); v); u)`: nothing; an inner type that binds `u`
///   again inside leaves `u` bound after it: `poly((poly(u; u), u); u)`.
/// - A type without a universal variable: nothing.
///
/// Reaches: R3g.
#[test]
fn the_first_free_universal_variable_is_found_in_order() {
    let mut c = checker(Mode::Success);
    let [p, q, r, s] = [0; 4].map(|_| univar_at(&mut c, 2));
    let arrow = arrow_at(&mut c, 2, &[p, q], r);
    let ty = tuple(&mut c, &[arrow, s]);
    assert_eq!(c.free_univar(ty), p);

    let [u, v, w] = [0; 3].map(|_| univar_at(&mut c, 2));
    let body = tuple(&mut c, &[u, v]);
    let poly = poly_of(&mut c, 2, body, &[u]);
    let ty = tuple(&mut c, &[poly, w]);
    assert_eq!(c.free_univar(ty), v);

    let u = univar_at(&mut c, 2);
    let int = constr(&mut c, INT, &[]);
    let shared = tuple(&mut c, &[u, int]);
    let poly = poly_of(&mut c, 2, shared, &[u]);
    let ty = tuple(&mut c, &[poly, shared]);
    assert_eq!(c.free_univar(ty), u);
    assert_eq!(c.free_univar(poly).0, NONE);
    let ty = tuple(&mut c, &[shared, poly]);
    assert_eq!(c.free_univar(ty), u);

    let [u, v] = [0; 2].map(|_| univar_at(&mut c, 2));
    let body = tuple(&mut c, &[u, v]);
    let inner = poly_of(&mut c, 2, body, &[v]);
    let outer = poly_of(&mut c, 2, inner, &[u]);
    assert_eq!(c.free_univar(outer).0, NONE);
    assert_eq!(c.free_univar(inner), u);

    let u = univar_at(&mut c, 2);
    let again = poly_of(&mut c, 2, u, &[u]);
    let body = tuple(&mut c, &[again, u]);
    let outer = poly_of(&mut c, 2, body, &[u]);
    assert_eq!(c.free_univar(outer).0, NONE);

    let int = constr(&mut c, INT, &[]);
    let ty = tuple(&mut c, &[int, int]);
    assert_eq!(c.free_univar(ty).0, NONE);
    assert!(c.extras.open_polys.is_empty() && c.g.work.is_empty());
}

/// The pair `occur_univar` raises is made below unify3, so a swapped
/// unify3 reverses it (compiler/ml/ctype.ml:2299-2303, 2316-2323):
///
/// ```text
/// if unify_eq t1 t1' || not (unify_eq t2 t2') then unify3 env t1 t1' t2 t2'
/// else
///   try unify3 env t2 t2' t1 t1'
///   with Unify trace ->
///     raise (Unify (List.map (fun (x, y) -> (y, x)) trace))
/// ...
/// | Tvar _, _ ->
///   occur !env t1' t2;
///   occur_univar !env t2;
///   link_type t1' t2
/// ```
///
/// Witness: `type k<'a, 'b> = 'b`, and `k<x, u>` against the variable
/// `x`, with `u` a universal variable. `x` occurs in `k<x, u>`, so the
/// pair goes to unify2 (`deep_occur`, ctype.ml:2240-2241); the left head
/// expands to `u` and the right one is its own expansion: unify3 runs on
/// `(x, x, k<x, u>, u)`, swapped. `occur` passes (the expansion does not
/// hold `x`); `occur_univar` of `k<x, u>` finds `u`. The trace: the pair
/// of the unification as written, then `(the new variable, u)`, reversed.
/// The other way round (`x` against `k<x, u>`) unify3 is not swapped and
/// the pair is `(u, the new variable)`.
/// Reaches: R3g.
#[test]
fn a_free_universal_variable_below_a_swapped_unify3_is_reversed() {
    for swapped in [true, false] {
        let mut c = checker(Mode::Explain);
        let k = c.types.rows.len() as u32;
        c.types.rows.push(c.types.rows[INT as usize]);
        let (a, b) = (var_at(&mut c, GENERIC), var_at(&mut c, GENERIC));
        abbreviation(&mut c, k, &[a, b], b);
        let x = var(&mut c);
        let u = univar_at(&mut c, 2);
        let applied = constr(&mut c, k, &[x, u]);
        let result = if swapped {
            c.unify(applied, x)
        } else {
            c.unify(x, applied)
        };
        assert!(result.is_err());
        assert_eq!(c.trace.len(), 2, "{:?}", c.trace);
        assert_eq!(
            c.trace[0],
            if swapped { [applied, x] } else { [x, applied] }
        );
        let [first, second] = c.trace[1];
        let (free, fresh) = if swapped {
            (second, first)
        } else {
            (first, second)
        };
        assert_eq!(free, u, "swapped: {swapped}");
        let fresh = c.g.nodes[fresh.0 as usize];
        assert_eq!((fresh.tag(), fresh.level), (VAR, GENERIC));
    }
}

/// A `LeavePoly` frame carries no pair and no swap: the entries of a
/// clash in the bodies of two polymorphic types below a swapped unify3
/// are reversed by the `Linked` frame of the two types, as OCaml's
/// handler reverses the whole trace (compiler/ml/ctype.ml:2299-2303; the
/// lines are quoted above `a_free_universal_variable_below_a_swapped_
/// unify3_is_reversed`; section 8.6, decisions 42 and 51).
///
/// Witness: `type ap = poly((u, int); u)` (an abbreviation of a
/// polymorphic type), and `ap` against `poly((u', string); u')`. The left
/// head expands and the right one does not: unify3 runs on the swapped
/// pair. The bodies clash at `int` against `string`. The trace: `(ap,
/// the right type)` as written; then the two bodies and the two
/// constructors, each LEFT first (the expansion's body, then the right
/// type's; `int`, then `string`), although unify3 took them right first.
/// No scope stays open.
/// Reaches: R3g.
#[test]
fn a_clash_in_the_bodies_below_a_swapped_unify3_is_reversed() {
    let mut c = checker(Mode::Explain);
    let ap = c.types.rows.len() as u32;
    c.types.rows.push(c.types.rows[INT as usize]);
    let u = univar_at(&mut c, GENERIC);
    let int = constr_at(&mut c, GENERIC, INT, &[]);
    let body = tuple_at(&mut c, GENERIC, &[u, int]);
    let manifest = poly_of(&mut c, GENERIC, body, &[u]);
    abbreviation(&mut c, ap, &[], manifest);
    let left = constr(&mut c, ap, &[]);
    let u2 = univar_at(&mut c, 2);
    let string = constr(&mut c, STRING, &[]);
    let body2 = tuple(&mut c, &[u2, string]);
    let right = poly_of(&mut c, 2, body2, &[u2]);
    assert!(c.unify(left, right).is_err());
    assert_eq!(c.trace.len(), 3, "{:?}", c.trace);
    assert_eq!(c.trace[0], [left, right]);
    assert_eq!(c.trace[1][1], body2);
    let (left_body, left_constructor) = (c.trace[1][0], c.trace[2][0]);
    let second = child(&mut c, left_body, 1);
    assert_eq!(path(&mut c, second), INT);
    assert_eq!(c.trace[2][1], string);
    assert_eq!(path(&mut c, left_constructor), INT);
    assert!(c.scopes.is_empty() && c.frames.is_empty() && c.saved.is_empty());
}

/// PR#6744 in `unify_row_field` (compiler/ml/ctype.ml:2685-2704):
///
/// ```text
/// let split_univars =
///   List.partition (fun ty ->
///       try occur_univar !env ty; true with Unify _ -> false)
/// in
/// let tl1', tlu1 = split_univars tl1'
/// and tl2', tlu2 = split_univars tl2' in
/// (match (tlu1, tlu2) with
/// | [], [] -> ()
/// | tu1 :: tlu1, _ :: _ ->
///   (* Attempt to merge all the types containing univars *)
///   if not !(passive_variants ()) then
///     List.iter (unify env tu1) (tlu1 @ tlu2)
/// | tu :: _, [] | [], tu :: _ -> occur_univar !env tu);
/// (* Is this handling of levels really principal? *)
/// List.iter (update_level !env (repr more).level) (tl1' @ tl2');
/// let e = ref None in
/// let f1' = Reither (c1 || c2, tl1', m1 || m2, e)
/// and f2' = Reither (c1 || c2, tl2', m1 || m2, e) in
/// ```
///
/// Witnesses, both inside two polymorphic types so that the variables
/// have a scope:
/// - `poly([< #A(u)]; u)` against `poly([< #A(u')]; u')`: each field
///   would gain the other's type, and both hold a universal variable:
///   they are unified instead, the type row 1 would gain first (`unify
///   env tu1`: `u'` becomes a link to `u`), and neither field gains a
///   type (one each).
/// - `poly([< #A(u)]; u)` against `poly([< #A(int)]; u')`: only one side
///   holds a universal variable: a clash, in the explaining mode with the
///   pair of `u` and a new variable last.
///
/// No row is written.
/// Reaches: R3f, R3g.
#[test]
fn the_types_that_hold_a_universal_variable_are_unified_not_gained() {
    let side = |c: &mut Checker, univar: bool| {
        let u = univar_at(c, 2);
        let ty = if univar { u } else { constr(c, INT, &[]) };
        let more = var(c);
        let row = variant_at(
            c,
            2,
            &[("A", Tag::Either(false, Some(ty), false))],
            more,
            true,
            NONE,
        );
        (poly_of(c, 2, row, &[u]), row, u)
    };
    let mut c = checker(Mode::Success);
    let (left, row1, u) = side(&mut c, true);
    let (right, row2, u2) = side(&mut c, true);
    let rows = rows_now(&c);
    c.unify(left, right).unwrap();
    assert_eq!(c.g.repr(u2), u);
    assert_rows_kept(&c, &rows);
    // The left row's node is a link to the right one by now; the right
    // node's field has its one type and nothing gained.
    let (tags, _, _) = read_row(&mut c, row2);
    assert_eq!(tags.len(), 1);
    assert_eq!((tags[0].1.types, c.g.repr(tags[0].1.first)), (1, u));
    assert_eq!(c.g.repr(row1), c.g.repr(row2));
    assert!(c.scopes.is_empty() && c.frames.is_empty() && c.saved.is_empty());

    for mode in [Mode::Success, Mode::Explain] {
        let mut c = checker(mode);
        let (left, _, u) = side(&mut c, true);
        let (right, _, _) = side(&mut c, false);
        assert!(c.unify(left, right).is_err());
        assert!(c.scopes.is_empty() && c.frames.is_empty());
        if mode == Mode::Explain {
            let [free, fresh] = *c.trace.last().expect("trace");
            assert_eq!(free, u, "{:?}", c.trace);
            assert_eq!(c.g.nodes[fresh.0 as usize].level, GENERIC);
        }
    }
}

/// A closed row with the one tag `#A`, `Reither (false, types, false, ref
/// None)` with any number of types (a conjunction), unopened, at level 2.
fn conjunctive_row(c: &mut Checker, types: &[Ty], more: Ty) -> Ty {
    let name = name_index(c, "A");
    let start = c.extras.row_fields.len() as u32;
    let kind = RowFieldKind::Either {
        constant: false,
        matched: false,
    };
    let published = types.len() as u32 + 1;
    c.extras.row_fields.push(RowFieldRow {
        name,
        types: Range {
            start: 0,
            len: types.len() as u32,
        },
        link: published,
        kind,
    });
    c.extras.variants.push(VariantRow {
        fields: Range { start, len: 1 },
        more: types.len() as u32,
        name: NONE,
        name_arguments: Range::default(),
        closed: true,
        fixed: false,
    });
    let index = c.extras.variants.len() as u32 - 1;
    let mut slots = types.to_vec();
    slots.push(more);
    extended_at(c, 2, ExtraDescriptor::Variant(index), &slots)
}

/// What two `Reither` fields gain is decided before the types that hold
/// a universal variable are unified (section 8.6, decisions 53 and 58;
/// compiler/ml/ctype.ml:2685-2706):
///
/// ```text
/// let tl2' = remq tl2 tl1 and tl1' = remq tl1 tl2 in
/// let tl1', tlu1 = split_univars tl1' and tl2', tlu2 = split_univars tl2' in
/// (match (tlu1, tlu2) with
/// | [], [] -> ()
/// | tu1 :: tlu1, _ :: _ ->
///   if not !(passive_variants ()) then List.iter (unify env tu1) (tlu1 @ tlu2)
/// | tu :: _, [] | [], tu :: _ -> occur_univar !env tu);
/// List.iter (update_level !env (repr more).level) (tl1' @ tl2');
/// let e = ref None in
/// let f1' = Reither (c1 || c2, tl1', m1 || m2, e)
/// and f2' = Reither (c1 || c2, tl2', m1 || m2, e) in
/// ```
///
/// Witness (the old checker's side is `differential::tests::
/// old_checker_gains_a_type_the_holders_made_a_duplicate`): `poly([< #A((u,
/// x)) & x]; u)` against `poly([< #A((u', x')) & x']; u')`. `tl1'` is
/// `[(u', x'); x']`: the tuple holds a universal variable, `x'` is kept.
/// The two tuples are unified, which makes `x'` a link to `x`... and the
/// field of row 1 still gains `x'`: it reads `[(u, x); x; x]`, three
/// types of which the last two are one node, and so does the field of
/// row 2. A join that compared the lists again after the unification
/// would gain nothing (two types): what `split_univars` did before the
/// sixth skeleton turn. The body is `Checker::join_either`'s second run
/// and the arm of `Checker::split_univars` with holders on both sides.
/// Reaches: R3f, R3g.
#[test]
fn a_field_gains_what_it_lacked_before_the_holders_were_unified() {
    for mode in [Mode::Success, Mode::Explain] {
        let mut c = checker(mode);
        let side = |c: &mut Checker| {
            let u = univar_at(c, 2);
            let x = var(c);
            let holder = tuple(c, &[u, x]);
            let more = var(c);
            let row = conjunctive_row(c, &[holder, x], more);
            (poly_of(c, 2, row, &[u]), row, holder, x)
        };
        let (left, _, holder1, x1) = side(&mut c);
        let (right, row2, holder2, x2) = side(&mut c);
        let rows = rows_now(&c);
        c.unify(left, right).unwrap();
        assert_rows_kept(&c, &rows);
        assert_eq!(c.g.repr(holder1), c.g.repr(holder2));
        assert_eq!(c.g.repr(x1), c.g.repr(x2));
        let (tags, _, _) = read_row(&mut c, row2);
        assert_eq!(tags[0].1.types, 3, "{mode:?}");
        let mut types = Vec::new();
        let row2 = c.g.repr(row2);
        let node = c.g.nodes[row2.0 as usize];
        let ExtraDescriptor::Variant(index) = c.extras.descriptors[node.a as usize] else {
            panic!("a variant");
        };
        let field = c.extras.row_fields[c.extras.variants[index as usize].fields.start as usize];
        super::rows::field_types(&c.g, node.b, node.arity(), field, &mut types);
        let types: Vec<Ty> = types.into_iter().map(|ty| c.g.repr(ty)).collect();
        let x = c.g.repr(x1);
        assert_eq!(types, [c.g.repr(holder1), x, x]);
        assert!(c.scopes.is_empty() && c.frames.is_empty() && c.saved.is_empty());
    }
}

/// An open row `[> #tag] as P<argument>` at `level`, unopened: slot 0 its
/// row variable (new, at `level`), slot 1 the argument of its name.
fn named_row(c: &mut Checker, level: u32, tag: &str, argument: Option<Ty>) -> Ty {
    let name = name_index(c, tag);
    let start = c.extras.row_fields.len() as u32;
    c.extras.row_fields.push(RowFieldRow {
        name,
        types: Range::default(),
        link: NONE,
        kind: RowFieldKind::Present,
    });
    c.extras.variants.push(VariantRow {
        fields: Range { start, len: 1 },
        more: 0,
        name: if argument.is_some() { PA } else { NONE },
        name_arguments: Range {
            start: 1,
            len: u32::from(argument.is_some()),
        },
        closed: false,
        fixed: false,
    });
    let index = c.extras.variants.len() as u32 - 1;
    let mut slots = vec![var_at(c, level)];
    slots.extend(argument);
    extended_at(c, level, ExtraDescriptor::Variant(index), &slots)
}

/// A row cannot keep a name that is below its scope: `update_level`
/// drops it (compiler/ml/ctype.ml:615-621):
///
/// ```text
/// | Tvariant row ->
///   let row = row_repr row in
///   (match row.row_name with
///   | Some (p, _tl) when level < get_level env p ->
///     log_type ty;
///     ty.desc <- Tvariant {row with row_name = None}
///   | _ -> ());
///   set_level ty level;
///   iter_type_expr (update_level env level expand) ty
/// ```
///
/// Witness: `[> #A] as P<y>` at level 2, `P` of scope 2, `y` in no field.
/// - Lowered to 1: the row has no name, `y` stays at 2 (the walk reads
///   the new descriptor, whose name has no arguments), the row variable
///   is at 1, the tag is there.
/// - With the scope of `P` at 1 the name stays and `y` is lowered.
/// - A second node `[> #B]` over the same row variable, after the
///   variable is linked to a row `[> #C] as P<y>`: lowering the first
///   node drops the name for it alone (`ty.desc <-`): the first reads
///   `A C` without a name, the second `B C` with `P`.
/// - In a speculation the write is undone.
///
/// Reaches the variant arm of `lower_scoped` and both branches of
/// `Checker::lower_row_name`.
#[test]
fn lowering_a_row_below_the_scope_of_its_name_drops_the_name() {
    let scoped = |scope: u32| {
        let mut c = checker(Mode::Success);
        c.types.rows[PA as usize].scope = scope;
        c.types.scoped = 1;
        c.g.begin_def();
        c
    };
    let mut c = scoped(2);
    let y = var_at(&mut c, 2);
    let named = named_row(&mut c, 2, "A", Some(y));
    let token = c.g.speculate();
    c.lower(named, 1).unwrap();
    let (_, row, more) = read_row(&mut c, named);
    assert_eq!((row.name, row.name_arguments.len), (NONE, 0));
    assert_eq!(shape(&mut c, named), "[A | ']");
    let level = |c: &Checker, ty: Ty| c.g.nodes[ty.0 as usize].level;
    assert_eq!((level(&c, named), level(&c, more), level(&c, y)), (1, 1, 2));
    assert!(!c.deep_occur(y, named));
    c.g.restore(token);
    let (_, row, more) = read_row(&mut c, named);
    assert_eq!((row.name, row.name_arguments.len), (PA, 1));
    assert_eq!((level(&c, named), level(&c, more), level(&c, y)), (2, 2, 2));

    let mut c = scoped(1);
    let y = var_at(&mut c, 2);
    let named = named_row(&mut c, 2, "A", Some(y));
    let before = c.g.nodes[named.0 as usize];
    c.lower(named, 1).unwrap();
    let after = c.g.nodes[named.0 as usize];
    assert_eq!((after.a, after.b, after.level), (before.a, before.b, 1));
    assert_eq!(read_row(&mut c, named).1.name, PA);
    assert_eq!(level(&c, y), 1);

    let mut c = scoped(2);
    let variable = var_at(&mut c, 2);
    let first = variant_at(&mut c, 2, &[("A", Tag::Present(None))], variable, false, NONE);
    let second = variant_at(&mut c, 2, &[("B", Tag::Present(None))], variable, false, NONE);
    let y = var_at(&mut c, 2);
    let last = named_row(&mut c, 2, "C", Some(y));
    c.g.link(variable, last);
    c.lower(first, 1).unwrap();
    assert_eq!(shape(&mut c, first), "[A C | ']");
    assert_eq!(read_row(&mut c, first).1.name, NONE);
    assert_eq!(shape(&mut c, second), format!("[B C | ' as {PA}]"));
    assert_eq!(read_row(&mut c, second).1.name, PA);
    assert_eq!((level(&c, first), level(&c, second), level(&c, last), level(&c, y)), (1, 2, 2, 2));
}

/// The arguments of a row's name are children of the row only while the
/// row is the one its chain ends in (section 8.6, decision 60;
/// compiler/ml/btype.ml:229-241, `iter_row`):
///
/// ```text
/// match (repr row.row_more).desc with
/// | Tvariant row -> iter_row f row
/// | Tvar _ | Tunivar _ | Tsubst _ | Tconstr _ | Tnil ->
///   Misc.may (fun (_, l) -> List.iter f l) row.row_name
/// ```
///
/// Witness, per walk: `[> #B]` unified with `[> #A] as P<y>` at level 2,
/// `y` in no field. The named row is the right node, gains `#B` through
/// a variant node its row variable is linked to, and the merged row has
/// no name (ctype.ml:2574-2586, 2596-2616). Then, each on a graph of its
/// own:
/// - `Checker::lower` of the row to level 1 leaves `y` at 2
///   (`update_level`, ctype.ml:584-630, through `iter_type_expr`);
/// - `Checker::generalize` after the definition leaves `y` at 2
///   (`generalize`, ctype.ml:509-516);
/// - `Checker::deep_occur` of `y` in the row is false (ctype.ml:1735-1782);
/// - a variable of level 1 bound to the row (the binding walk, which
///   lowers below a row) leaves `y` at 2;
/// - with `y` a universal variable, `Checker::free_univar` of the row
///   finds none (`occur_univar`, ctype.ml:1563-1607);
/// - `Checker::univars_escape` of a binder of that universal variable in
///   a polymorphic type whose body is the row is false
///   (ctype.ml:1630-1652);
/// - a `Checker::copy` of the generalized row with `y` generic makes one
///   variable, the row variable's, and no copy of `y` (`row_repr` gives a
///   copy the innermost row's name, compiler/ml/btype.ml:126-135,
///   ctype.ml:800-868).
///
/// The old checker's side, observed: `differential::tests::
/// old_checker_does_not_reach_the_arguments_of_a_stale_row_name`. Before
/// the sixth skeleton turn every one of these walks reached `y` (each
/// pushes every slot of a node); the body is
/// `Checker::drop_name_children`, called by `Checker::unify_row`. While
/// the row IS the innermost, its name's arguments are children: the
/// last block.
/// Reaches: R3f, R3n, R3g.
#[test]
fn the_arguments_of_a_stale_row_name_are_not_children() {
    // The named row after it gained `#B`, and the argument of its name.
    let stale = |c: &mut Checker, y: Ty| {
        let other = named_row(c, 2, "B", None);
        let named = named_row(c, 2, "A", Some(y));
        let rows = rows_now(c);
        c.unify(other, named).unwrap();
        assert_rows_kept(c, &rows);
        assert_eq!(shape(c, named), "[A B | ']");
        named
    };
    let level = |c: &mut Checker, ty: Ty| {
        let ty = c.g.repr(ty);
        c.g.nodes[ty.0 as usize].level
    };
    for mode in [Mode::Success, Mode::Explain] {
        let mut c = checker(mode);
        let y = var(&mut c);
        let named = stale(&mut c, y);
        c.lower(named, 1).unwrap();
        assert_eq!((level(&mut c, named), level(&mut c, y)), (1, 2), "lower");

        let mut c = checker(mode);
        let y = var(&mut c);
        let named = stale(&mut c, y);
        c.g.end_def();
        c.generalize(named);
        assert_eq!(
            (level(&mut c, named), level(&mut c, y)),
            (GENERIC, 2),
            "generalize"
        );

        let mut c = checker(mode);
        let y = var(&mut c);
        let named = stale(&mut c, y);
        assert!(!c.deep_occur(y, named), "deep_occur");

        let mut c = checker(mode);
        let y = var(&mut c);
        let named = stale(&mut c, y);
        let v = var_at(&mut c, 1);
        c.unify(v, named).unwrap();
        assert_eq!((level(&mut c, named), level(&mut c, y)), (1, 2), "binding");

        let mut c = checker(mode);
        let u = univar_at(&mut c, 2);
        let named = stale(&mut c, u);
        assert_eq!(c.free_univar(named), Ty(NONE), "free_univar");
        let binder = poly_of(&mut c, 2, u, &[u]);
        let w = univar_at(&mut c, 2);
        let other = poly_of(&mut c, 2, named, &[w]);
        let (binder, other) = (c.g.nodes[binder.0 as usize], c.g.nodes[other.0 as usize]);
        assert!(!c.univars_escape(binder, other), "univars_escape");

        let mut c = checker(mode);
        let y = var_at(&mut c, GENERIC);
        let named = stale(&mut c, y);
        c.g.end_def();
        c.generalize(named);
        let first = c.g.nodes.len();
        let copy = c.copy(named);
        assert_eq!(shape(&mut c, copy), "[A B | ']");
        let variables = c.g.nodes[first..]
            .iter()
            .filter(|node| node.tag() == VAR)
            .count();
        assert_eq!(variables, 1, "copy");
    }
    // The innermost row's name: its argument is a child.
    let mut c = checker(Mode::Success);
    let y = var(&mut c);
    let named = named_row(&mut c, 2, "A", Some(y));
    assert!(c.deep_occur(y, named));
    c.lower(named, 1).unwrap();
    assert_eq!(level(&mut c, y), 1);
}

/// `free_univar` over a variant row (compiler/ml/btype.ml:229-241,
/// 263-265; ctype.ml:1563-1607): the fields' types, then the arguments
/// of the name, then the row variable:
///
/// ```text
/// | Tvariant row ->
///   iter_row f row;
///   f (row_more row)
/// ```
///
/// Witnesses, each a row at level 2 with free universal variables in
/// three places, found in that order:
/// - `[> #A(u0)] as P<u1>` whose row variable is the universal variable
///   `u2`: `u0`;
/// - `[> #A(int)] as P<u1>` over `u2`: `u1`;
/// - `[> #A(int)]` over `u2`: `u2`;
/// - inside `poly(...; u2)`, the same row: none (the row variable is
///   bound);
/// - an OPENED row `[< #A(u0)]` (`Reither`, its type under the chain
///   node of its reference): `u0`; and after that reference is resolved
///   to absent, none: `iter_row` visits what `row_field_repr` gives.
///
/// The body is the `Variant` arm of
/// `Checker::push_free_univar_children`.
/// Reaches: R3f, R3g.
#[test]
fn a_free_universal_variable_is_found_in_a_row_in_order() {
    let mut c = checker(Mode::Success);
    // `[> #A(argument)] as P<named>` over `more`.
    let row = |c: &mut Checker, argument: Ty, named: Option<Ty>, more: Ty| {
        let name = name_index(c, "A");
        let start = c.extras.row_fields.len() as u32;
        c.extras.row_fields.push(RowFieldRow {
            name,
            types: Range { start: 0, len: 1 },
            link: NONE,
            kind: RowFieldKind::Present,
        });
        c.extras.variants.push(VariantRow {
            fields: Range { start, len: 1 },
            more: 1,
            name: if named.is_some() { PA } else { NONE },
            name_arguments: Range {
                start: 2,
                len: u32::from(named.is_some()),
            },
            closed: false,
            fixed: false,
        });
        let index = c.extras.variants.len() as u32 - 1;
        let mut slots = vec![argument, more];
        slots.extend(named);
        extended_at(c, 2, ExtraDescriptor::Variant(index), &slots)
    };
    let [u0, u1, u2] = [(); 3].map(|()| univar_at(&mut c, 2));
    let int = constr(&mut c, INT, &[]);
    let first = row(&mut c, u0, Some(u1), u2);
    assert_eq!(c.free_univar(first), u0);
    let second = row(&mut c, int, Some(u1), u2);
    assert_eq!(c.free_univar(second), u1);
    let third = row(&mut c, int, None, u2);
    assert_eq!(c.free_univar(third), u2);
    let bound = poly_of(&mut c, 2, third, &[u2]);
    assert_eq!(c.free_univar(bound), Ty(NONE));

    let more = var(&mut c);
    let either = variant_at(
        &mut c,
        2,
        &[("A", Tag::Either(false, Some(u0), false))],
        more,
        true,
        NONE,
    );
    c.open_row(either);
    assert_eq!(c.free_univar(either), u0);
    let (tags, _, _) = read_row(&mut c, either);
    let holders = c.resolve(tags[0].1.end, super::rows::RES_ABSENT, Ty(NONE));
    c.settle(holders, super::rows::RES_ABSENT);
    assert_eq!(c.free_univar(either), Ty(NONE));
}

/// The split of the types that hold a universal variable while the
/// variants are passive (compiler/ml/ctype.ml:2693-2703):
///
/// ```text
/// | tu1 :: tlu1, _ :: _ ->
///   (* Attempt to merge all the types containing univars *)
///   if not !(passive_variants ()) then
///     List.iter (unify env tu1) (tlu1 @ tlu2)
/// | tu :: _, [] | [], tu :: _ -> occur_univar !env tu);
/// (* Is this handling of levels really principal? *)
/// List.iter (update_level !env (repr more).level) (tl1' @ tl2');
/// ```
///
/// Witness: `poly([< #A(z & (u, x))]; u)` against `poly([< #A(z' & (u',
/// x'))]; u')`, every type at level 2 and the two row variables at level
/// 1, with `Extras::passive_variants` set (nothing in `tc` sets it: the
/// typing of a pattern for an exhaustiveness check does, `with_passive_
/// variants`, ctype.ml:2189-2202, from typecore.ml:1931; section 8.9).
/// The two tuples hold a universal variable and are NOT unified and NOT
/// lowered: they stay two nodes at level 2. `z` and `z'` are gained and
/// lowered to the level of the merged row variable, 1. Each field then
/// has its two types and the one it gained. The holder comes after the
/// kept type in each list, so that the place between the two kept
/// ranges of the scratch holds a holder: the range `Checker::join_either`
/// lowered before the review of R3g (section 8.6, decision 54). The
/// bodies are the passive arm of `Checker::split_univars` and the two
/// lowering loops of `Checker::join_either`.
/// Reaches: R3f, R3g.
#[test]
fn passive_variants_keep_the_levels_of_the_types_that_hold_a_universal_variable() {
    let mut c = checker(Mode::Success);
    c.extras.passive_variants = true;
    let side = |c: &mut Checker| {
        let u = univar_at(c, 2);
        let (x, z) = (var(c), var(c));
        let holder = tuple(c, &[u, x]);
        let more = var_at(c, 1);
        let row = conjunctive_row(c, &[z, holder], more);
        (poly_of(c, 2, row, &[u]), row, holder, z)
    };
    let (left, _, holder1, z1) = side(&mut c);
    let (right, row2, holder2, z2) = side(&mut c);
    c.unify(left, right).unwrap();
    let level = |c: &Checker, ty: Ty| c.g.nodes[ty.0 as usize].level;
    assert_ne!(c.g.repr(holder1), c.g.repr(holder2));
    assert_eq!((level(&c, holder1), level(&c, holder2)), (2, 2));
    assert_eq!((level(&c, z1), level(&c, z2)), (1, 1));
    let (tags, _, more) = read_row(&mut c, row2);
    assert_eq!(tags[0].1.types, 3);
    assert_eq!(level(&c, more), 1);
    assert!(c.scopes.is_empty() && c.frames.is_empty() && c.saved.is_empty());
}

/// The cost of the two walks for universal variables, as relations
/// between n = 1,000 and n = 10,000 (section 8.6, decisions 56 and 59).
/// - `Checker::free_univar` over a tuple of n variables inside one
///   binder: one visit a node, linear.
/// - `Checker::free_univar` over a chain of n polymorphic types WITHOUT
///   bound variables in which every type is held twice, once under such
///   a type and once outside it: `t(0)` is the bound variable, `t(i + 1)`
///   is `(poly(t(i);), t(i))`, the whole inside one binder. A
///   polymorphic type without bound variables adds nothing to `bound`
///   (`List.fold_right Type_set.add (List.map repr tyl) bound`,
///   compiler/ml/ctype.ml:1587-1589), so OCaml visits each node once
///   (ctype.ml:1569-1581: with the same `bound` a node is not visited
///   again). So does the walk: exactly `2n + 1` visits (n tuples, n
///   polymorphic types, the binder), ZERO extra. Before the sixth
///   skeleton turn such a type opened a context, a node first met inside
///   it was visited again after it was left, and this chain took `2^n`
///   visits: the test would not end.
/// - `Checker::univars_escape` of a known binder over a tuple of n
///   variables: the family pass and one visit a node, linear.
///
/// Reaches: R3g.
#[test]
fn the_walks_for_universal_variables_at_ten_thousand() {
    let wide = |n: u32| {
        let mut c = checker(Mode::Success);
        let u = univar_at(&mut c, 2);
        let mut elements: Vec<Ty> = (0..n).map(|_| var(&mut c)).collect();
        elements.push(u);
        let body = tuple(&mut c, &elements);
        let ty = poly_of(&mut c, 2, body, &[u]);
        let mut found = u;
        let count = steps::scope(|| found = c.free_univar(ty));
        assert_eq!(found, Ty(NONE));
        count
    };
    let (small, large) = (wide(1_000), wide(10_000));
    assert!(large <= 11 * small, "wide: {small} {large}");

    let shared = |n: u32| {
        let mut c = checker(Mode::Success);
        let u = univar_at(&mut c, 2);
        let mut ty = u;
        for _ in 0..n {
            let inner = poly_of(&mut c, 2, ty, &[]);
            ty = tuple(&mut c, &[inner, ty]);
        }
        let ty = poly_of(&mut c, 2, ty, &[u]);
        let mut found = u;
        let count = steps::scope(|| found = c.free_univar(ty));
        assert_eq!(found, Ty(NONE));
        count
    };
    assert_eq!(shared(1_000), 2 * 1_000 + 1);
    assert_eq!(shared(10_000), 2 * 10_000 + 1);

    let escape = |n: u32| {
        let mut c = checker(Mode::Success);
        // An open scope that pairs `u` with `u2`, so that a type that
        // binds `u` again has a known binder.
        let (u, u2) = (univar_at(&mut c, 2), univar_at(&mut c, 2));
        let (outer1, outer2) = (poly_of(&mut c, 2, u, &[u]), poly_of(&mut c, 2, u2, &[u2]));
        let (n1, n2) = (c.g.nodes[outer1.0 as usize], c.g.nodes[outer2.0 as usize]);
        let partners = c.g.push(partner_node(Ty(NONE)));
        c.g.push(partner_node(Ty(NONE)));
        c.scopes.push(PolyScope {
            left: n1.b + 1,
            right: n2.b + 1,
            left_len: 1,
            right_len: 1,
            partners,
        });
        let binder = poly_of(&mut c, 2, u, &[u]);
        let w = univar_at(&mut c, 2);
        let elements: Vec<Ty> = (0..n).map(|_| var(&mut c)).collect();
        let body = tuple(&mut c, &elements);
        let other = poly_of(&mut c, 2, body, &[w]);
        let (binder, other) = (c.g.nodes[binder.0 as usize], c.g.nodes[other.0 as usize]);
        let mut escapes = true;
        let count = steps::scope(|| escapes = c.univars_escape(binder, other));
        assert!(!escapes);
        // With `u2` in the body it escapes: `u2` is in the family of `u`.
        let body = tuple(&mut c, &[u2]);
        let other = poly_of(&mut c, 2, body, &[w]);
        let other = c.g.nodes[other.0 as usize];
        assert!(c.univars_escape(binder, other));
        c.scopes.clear();
        count
    };
    let (small, large) = (escape(1_000), escape(10_000));
    assert!(large <= 11 * small, "escape: {small} {large}");
}

/// The cost of universal variables, as relations between n = 1,000 and
/// n = 10,000.
/// - n bound variables, the body the last of them: `unify_univar` scans
///   the two lists of the one scope (`find_univ`, compiler/ml/ctype.ml:
///   1546-1551), `enter_poly` makes n partner nodes a side: linear.
/// - n nested polymorphic types of one variable each, the innermost body
///   the outermost variable: `unify_univar` passes n scopes, linear in n;
///   but `enter_poly` marks the variables of every open scope at each
///   entry, as OCaml rebuilds `known_univars` (ctype.ml:1658-1662), and
///   the occurrence test walks each right type (ctype.ml:2330): the
///   whole is quadratic, at most 110 times the steps for ten times n.
/// - A row of n `Reither` tags of which one has a type that holds a
///   universal variable, inside two polymorphic types: each joined tag
///   tests the types it gains with one walk of a node without children:
///   linear.
///
/// Reaches: R3f, R3g.
#[test]
fn universal_variables_at_ten_thousand() {
    let binders = |n: u32| {
        let mut c = checker(Mode::Success);
        let side = |c: &mut Checker| {
            let vars: Vec<Ty> = (0..n).map(|_| univar_at(c, 2)).collect();
            poly_of(c, 2, vars[n as usize - 1], &vars)
        };
        let (left, right) = (side(&mut c), side(&mut c));
        let count = steps::scope(|| c.unify(left, right).unwrap());
        assert!(c.scopes.is_empty());
        count
    };
    let (small, large) = (binders(1_000), binders(10_000));
    assert!(large <= 11 * small, "binders: {small} {large}");

    let nested = |n: u32| {
        let mut c = checker(Mode::Success);
        let side = |c: &mut Checker| {
            let vars: Vec<Ty> = (0..n).map(|_| univar_at(c, 2)).collect();
            let mut ty = vars[0];
            for &var in vars.iter().rev() {
                ty = poly_of(c, 2, ty, &[var]);
            }
            ty
        };
        let (left, right) = (side(&mut c), side(&mut c));
        let count = steps::scope(|| c.unify(left, right).unwrap());
        assert!(c.scopes.is_empty());
        count
    };
    let (small, large) = (nested(1_000), nested(10_000));
    assert!(large <= 110 * small, "nested: {small} {large}");

    let row = |n: u32| {
        let mut c = checker(Mode::Success);
        let labels: Vec<String> = (0..n).map(|at| format!("t{at:05}")).collect();
        let side = |c: &mut Checker| {
            let u = univar_at(c, 2);
            let tags: Vec<(&str, Tag)> = labels
                .iter()
                .enumerate()
                .map(|(at, label)| {
                    let ty = if at == 0 { u } else { constr(c, INT, &[]) };
                    (label.as_str(), Tag::Either(false, Some(ty), false))
                })
                .collect();
            let more = var(c);
            let row = variant_at(c, 2, &tags, more, true, NONE);
            poly_of(c, 2, row, &[u])
        };
        let (left, right) = (side(&mut c), side(&mut c));
        steps::scope(|| c.unify(left, right).unwrap())
    };
    let (small, large) = (row(1_000), row(10_000));
    assert!(large <= 11 * small, "row: {small} {large}");
}

/// What a universal variable and a polymorphic type cost in memory, and
/// what the scopes hold (section 8.6, decision 50). A universal variable
/// is one 16-byte node and no slot, its 12-byte descriptor row shared by
/// every copy; a polymorphic type of `k` variables is one node and `1 +
/// k` slots: `16 + 4 * (1 + k)` bytes. A scope is 20 bytes and one
/// 16-byte partner node per bound variable. Runs today.
#[test]
fn sizes_of_universal_variables() {
    assert_eq!(std::mem::size_of::<PolyScope>(), 20);
    assert_eq!(std::mem::size_of::<super::rows::Completion>(), 8);
    assert_eq!(std::mem::size_of_val(&partner_node(Ty(NONE))), 16);
    let mut c = checker(Mode::Success);
    let (nodes, lists, rows) = (c.g.nodes.len(), c.g.lists.len(), c.extras.descriptors.len());
    let (poly, [u, v]) = two_binders(&mut c, [0, 1, 0], [0, 1]);
    // Two variables, the body tuple, the polymorphic type; 3 + 3 slots.
    assert_eq!((c.g.nodes.len() - nodes, c.g.lists.len() - lists), (4, 6));
    assert_eq!(c.g.nodes[poly.0 as usize].arity(), 3);
    assert_eq!(
        (
            c.g.nodes[u.0 as usize].arity(),
            c.g.nodes[v.0 as usize].arity()
        ),
        (0, 0)
    );
    assert_eq!(c.extras.univars, 2);
    // A copy makes nodes and slots and no descriptor row.
    let rows_before = c.extras.descriptors.len();
    assert_eq!(rows_before - rows, 3);
    c.g.end_def();
    c.g.generalize(poly);
    let copy = c.copy(poly);
    assert_ne!(copy, poly);
    assert_eq!(c.extras.descriptors.len(), rows_before);
    assert_eq!(c.extras.univars, 2);
}

// ---------------------------------------------------------------------------
// R3p: packages (section 8.6, decision 52).
// ---------------------------------------------------------------------------

use super::rows::{Completion, PackageDecls};
use super::segment::PackageRow;
use std::cell::RefCell;
use std::rc::Rc;

/// The questions a [`Supplier`] was asked, shared with the test.
type Calls = Rc<RefCell<Vec<(u32, &'static str, u32)>>>;

/// What a hand-built module type answers for one name.
#[derive(Clone, Copy, PartialEq, Debug)]
enum Answer {
    /// `type name = int`.
    Int,
    Abstract,
    Missing,
    Other,
}

/// The declarations of the package tests: `names[position]` is the text
/// of a name; a module type `path` answers `answers[(path, text)]`, and
/// `Missing` for a name it does not list; two different paths are
/// compatible when `compatible` says so. Every call is recorded in
/// `calls`: `(path, text, level)` for a completion, `(left path, right
/// path, u32::MAX)` under the text `"compatible"` for the last question.
struct Supplier {
    names: Vec<&'static str>,
    answers: Vec<(u32, &'static str, Answer)>,
    compatible: bool,
    calls: Calls,
}

impl PackageDecls for Supplier {
    fn compare(&self, left: u32, right: u32) -> std::cmp::Ordering {
        self.names[left as usize].cmp(self.names[right as usize])
    }
    fn complete(&mut self, c: &mut Checker, path: u32, name: u32, level: u32) -> Completion {
        let text = self.names[name as usize];
        self.calls.borrow_mut().push((path, text, level));
        let answer = self
            .answers
            .iter()
            .find(|entry| entry.0 == path && entry.1 == text);
        match answer.map_or(Answer::Missing, |entry| entry.2) {
            Answer::Int => Completion::Type(constr_at(c, level, INT, &[])),
            Answer::Abstract => Completion::Abstract,
            Answer::Missing => Completion::Missing,
            Answer::Other => Completion::Other,
        }
    }
    fn compatible(&mut self, c: &mut Checker, left: Node, right: Node) -> bool {
        let path = |c: &Checker, node: Node| match c.extras.descriptors[node.a as usize] {
            ExtraDescriptor::Package(row) => c.extras.packages[row as usize].path,
            _ => panic!("not a package"),
        };
        self.calls
            .borrow_mut()
            .push((path(c, left), "compatible", path(c, right)));
        self.compatible
    }
}

/// `Tpackage (path, names, arguments)` at `level`: the names are the
/// `arguments.len()` positions from `first` on in the supplier's pool.
fn package_at(c: &mut Checker, level: u32, path: u32, first: u32, arguments: &[Ty]) -> Ty {
    let len = arguments.len() as u32;
    let row = c.extras.packages.len() as u32;
    c.extras.packages.push(PackageRow {
        path,
        longidents: Range { start: first, len },
        arguments: Range { start: 0, len },
    });
    extended_at(c, level, ExtraDescriptor::Package(row), arguments)
}

/// A checker whose declarations are a [`Supplier`], and the calls it
/// will record.
fn with_supplier(
    mode: Mode,
    names: &[&'static str],
    answers: &[(u32, &'static str, Answer)],
    compatible: bool,
) -> (Checker, Calls) {
    let mut c = checker(mode);
    let calls = Rc::new(RefCell::new(Vec::new()));
    c.packages = Some(Box::new(Supplier {
        names: names.to_vec(),
        answers: answers.to_vec(),
        compatible,
        calls: calls.clone(),
    }));
    (c, calls)
}

/// Two packages of one module type unify their types name by name, in
/// name order, and ask nothing of the declarations (compiler/ml/ctype.ml:
/// 2172-2181, 2416-2423):
///
/// ```text
/// let unify_package env unify_list lv1 p1 n1 tl1 lv2 p2 n2 tl2 =
///   let ntl2 = complete_type_list env n1 lv2 (Mty_ident p2) n2 tl2
///   and ntl1 = complete_type_list env n2 lv1 (Mty_ident p1) n1 tl1 in
///   unify_list (List.map snd ntl1) (List.map snd ntl2);
///   if
///     eq_package_path env p1 p2
///     || !package_subtype env p1 n1 tl1 p2 n2 tl2
///        && !package_subtype env p2 n2 tl2 p1 n1 tl1
///   then ()
///   else raise Not_found
/// ...
/// | Tpackage (p1, n1, tl1), Tpackage (p2, n2, tl2) -> (
///   try
///     unify_package !env (unify_list env) t1.level p1 n1 tl1 t2.level p2 n2
///       tl2
///   with Not_found ->
///     if !(umode ()) = Expression then raise (Unify []);
/// ```
///
/// Witnesses, module type 7 with the names `t` and `u`:
/// - `{t = x, u = int}` against `{t = string, u = y}`: `x` is `string`
///   and `y` is `int`; the left node is a link to the right one; no frame
///   and no saved descriptor stays; the declarations are not asked.
/// - `{t = int, u = int}` against `{t = string, u = string}`: a clash at
///   `t`, the first name: the trace is the two packages, then `int` and
///   `string` of `t`.
///
/// Reaches: R3p.
#[test]
fn packages_of_one_module_type_unify_name_by_name() {
    let names = ["t", "u", "t", "u"];
    let (mut c, calls) = with_supplier(Mode::Success, &names, &[], false);
    let (x, y) = (var(&mut c), var(&mut c));
    let (int, string) = (constr(&mut c, INT, &[]), constr(&mut c, STRING, &[]));
    let left = package_at(&mut c, 2, 7, 0, &[x, int]);
    let right = package_at(&mut c, 2, 7, 2, &[string, y]);
    c.unify(left, right).unwrap();
    assert_eq!(
        (c.g.repr(left), c.g.repr(x), c.g.repr(y)),
        (right, string, int)
    );
    assert!(c.frames.is_empty() && c.saved.is_empty() && calls.borrow().is_empty());
    assert!(c.packages.is_some(), "the supplier is put back");

    let (mut c, _) = with_supplier(Mode::Explain, &names, &[], false);
    let ints = [constr(&mut c, INT, &[]), constr(&mut c, INT, &[])];
    let strings = [constr(&mut c, STRING, &[]), constr(&mut c, STRING, &[])];
    let left = package_at(&mut c, 2, 7, 0, &ints);
    let right = package_at(&mut c, 2, 7, 2, &strings);
    assert!(c.unify(left, right).is_err());
    assert_eq!(c.trace, [[left, right], [ints[0], strings[0]]]);
    assert!(c.frames.is_empty() && c.saved.is_empty() && c.packages.is_some());
}

/// A name one package lists and the other does not is completed from the
/// OTHER package's module type, at the level of the unification
/// (`complete_type_list`, compiler/ml/ctype.ml:2135-2169):
///
/// ```text
/// | n :: nl, ((n2, _) as nt2) :: ntl' when Longident.cmp n n2 >= 0 ->
///   nt2 :: complete (if Longident.cmp n n2 = 0 then nl else nl1) ntl'
/// | n :: nl, _ -> (
///   try
///     let path =
///       Env.lookup_type (concat_longident (Longident.Lident "Pkg") n) env'
///     in
///     match Env.find_type path env' with
///     | { type_arity = 0; type_kind = Type_abstract; type_private = Public;
///         type_manifest = Some t2 } ->
///       (n, nondep_instance env' lv2 id2 t2) :: complete nl ntl2
///     ...
///     | _ -> raise Exit
///   with
///   | Not_found when allow_absent -> complete nl ntl2
///   | Exit -> raise Not_found)
/// ```
///
/// Witnesses. Left: module type 7, `{t = x}` at level 2. Right: module
/// type 7, `{t = int, u = y}` at level 1.
/// - Module type 7 declares `type u = int`: the declarations are asked
///   once, for `(7, "u")` at level 1 (the lower of the two), and `y` is
///   `int`.
/// - The other way round the question is the same.
/// - `u` abstract, missing, or another declaration: a clash, in the
///   explaining mode with the two packages as the only pair, and no frame
///   or saved descriptor left.
/// - No declarations (`Checker::packages` is `None`): a clash.
/// - Different module types (7 and 8) with the same names: the lists are
///   unified FIRST and the declarations asked last whether the two are
///   compatible; a refusal is a clash with the two packages as the only
///   pair, after `x` was bound.
///
/// Reaches: R3p.
#[test]
fn a_package_is_completed_from_the_other_module_type() {
    let names = ["t", "t", "u"];
    for reversed in [false, true] {
        let (mut c, calls) = with_supplier(Mode::Success, &names, &[(7, "u", Answer::Int)], false);
        let (x, y) = (var(&mut c), var_at(&mut c, 1));
        let int = constr_at(&mut c, 1, INT, &[]);
        let left = package_at(&mut c, 2, 7, 0, &[x]);
        let right = package_at(&mut c, 1, 7, 1, &[int, y]);
        if reversed {
            c.unify(right, left).unwrap()
        } else {
            c.unify(left, right).unwrap()
        }
        assert_eq!(*calls.borrow(), [(7, "u", 1)], "reversed: {reversed}");
        assert_eq!(c.g.repr(x), int);
        assert_eq!(path(&mut c, y), INT);
        assert!(c.frames.is_empty() && c.saved.is_empty());
    }
    for answer in [Answer::Abstract, Answer::Missing, Answer::Other] {
        let (mut c, _) = with_supplier(Mode::Explain, &names, &[(7, "u", answer)], true);
        let (x, y) = (var(&mut c), var(&mut c));
        let int = constr(&mut c, INT, &[]);
        let left = package_at(&mut c, 2, 7, 0, &[x]);
        let right = package_at(&mut c, 2, 7, 1, &[int, y]);
        assert!(c.unify(left, right).is_err(), "{answer:?}");
        assert_eq!(c.trace, [[left, right]]);
        assert!(c.frames.is_empty() && c.saved.is_empty() && c.packages.is_some());
        assert_eq!(c.g.repr(x), x, "nothing was unified");
    }
    let mut c = checker(Mode::Success);
    let (x, int) = (var(&mut c), constr(&mut c, INT, &[]));
    let left = package_at(&mut c, 2, 7, 0, &[x]);
    let right = package_at(&mut c, 2, 7, 0, &[int]);
    assert!(c.unify(left, right).is_err());

    for compatible in [true, false] {
        let (mut c, calls) = with_supplier(Mode::Explain, &["t", "t"], &[], compatible);
        let (x, int) = (var(&mut c), constr(&mut c, INT, &[]));
        let left = package_at(&mut c, 2, 7, 0, &[x]);
        let right = package_at(&mut c, 2, 8, 1, &[int]);
        assert_eq!(c.unify(left, right).is_ok(), compatible);
        assert_eq!(*calls.borrow(), [(7, "compatible", 8)]);
        assert!(c.frames.is_empty() && c.saved.is_empty());
        if !compatible {
            assert_eq!(c.trace, [[left, right]]);
        }
    }
}

/// The cost of two packages of n names: one merge, one comparison a
/// name, one pair a name: at most 11 times the steps for ten times the
/// names, with every second name completed.
/// Reaches: R3p.
#[test]
fn packages_of_ten_thousand_names_are_linear() {
    let run = |n: u32| {
        let texts: Vec<&'static str> = (0..n)
            .map(|at| &*Box::leak(format!("t{at:05}").into_boxed_str()))
            .collect();
        // The left lists every name, the right every second one.
        let mut names = texts.clone();
        names.extend(texts.iter().step_by(2));
        let answers: Vec<(u32, &'static str, Answer)> =
            texts.iter().map(|&text| (7, text, Answer::Int)).collect();
        let (mut c, calls) = with_supplier(Mode::Success, &names, &answers, false);
        let all: Vec<Ty> = (0..n).map(|_| constr(&mut c, INT, &[])).collect();
        let half: Vec<Ty> = (0..n.div_ceil(2)).map(|_| var(&mut c)).collect();
        let left = package_at(&mut c, 2, 7, 0, &all);
        let right = package_at(&mut c, 2, 7, n, &half);
        let count = steps::scope(|| c.unify(left, right).unwrap());
        assert_eq!(calls.borrow().len() as u32, n / 2);
        count
    };
    let (small, large) = (run(1_000), run(10_000));
    assert!(large <= 11 * small, "{small} {large}");
}

// ---------------------------------------------------------------------------
// Pattern mode (R3h, R3r; CHECKER_REWRITE 8.9)
// ---------------------------------------------------------------------------

use super::expand::{DATATYPE, NEWTYPE, Newtype};
use super::rows::{DeclMatch, LocalDecls};
use super::unify::UnifyMode;

/// `(type n0)` at level 1 and `(type n1)` at level 2: locally abstract.
const N0: u32 = 14;
const N1: u32 = 15;
/// `type k<'a>` of another unit: abstract, not injective.
const K: u32 = 16;
/// `type d<'a> = D('a)` and `type e<'a> = E('a)` of another unit.
const D: u32 = 17;
const E: u32 = 18;
/// `type t2` of another unit: abstract, as `T`.
const T2: u32 = 19;
/// `type k2<'a, 'b>` of another unit: abstract, not injective.
const K2: u32 = 20;
/// `array<'a>`: predefined, without a manifest.
const ARR: u32 = 21;
/// `type wrap<'x> = k<'x>` of another unit.
const WRAP: u32 = 22;
/// The first type `reify` makes.
const FRESH: u32 = 23;

/// The supplier of the hand-built tests: counts the fresh types from
/// [`FRESH`], records the name index each was asked with, and answers
/// `compare` with `answer` after pushing `members`.
struct Fresh {
    next: u32,
    asked: std::rc::Rc<std::cell::RefCell<Vec<u32>>>,
    answer: DeclMatch,
    members: Vec<[Ty; 2]>,
}

impl LocalDecls for Fresh {
    fn fresh_abstract(&mut self, name: u32) -> u32 {
        self.asked.borrow_mut().push(name);
        self.next += 1;
        self.next - 1
    }

    fn compare(&mut self, c: &mut Checker, _: u32, _: u32) -> DeclMatch {
        for &[left, right] in &self.members {
            c.push_compatible(left, right);
        }
        self.answer
    }
}

/// [`checker`] with the declarations of pattern mode: `int`, `string`,
/// `unit` and `array` are predefined (`LOCAL` and `PREDEF`), `n0` and
/// `n1` locally abstract types of the newtype levels 1 and 2, `k`, `d`,
/// `e`, `t2`, `k2` and `wrap` types of another unit, and a supplier
/// whose record of asked names is returned.
fn pattern_checker(mode: Mode) -> (Checker, std::rc::Rc<std::cell::RefCell<Vec<u32>>>) {
    let mut c = checker(mode);
    for ty in [INT, STRING, UNIT] {
        c.types.set_local(ty);
        c.types.set_predefined(ty);
    }
    let row = |arity: u16, flags: u8| TypeInfo {
        manifest: NONE,
        scope: 0,
        newtype: NONE,
        arity,
        flags,
        reserved: 0,
    };
    for level in [1, 2] {
        c.types.newtypes.push(Newtype {
            level,
            expansion_level: level,
        });
        c.types.rows.push(TypeInfo {
            scope: level,
            newtype: c.types.newtypes.len() as u32 - 1,
            ..row(0, NEWTYPE)
        });
        c.types.scoped += 1;
    }
    c.types.rows.extend([
        row(1, 0),
        row(1, DATATYPE),
        row(1, DATATYPE),
        row(0, 0),
        row(2, 0),
        row(1, 0),
        row(1, 0),
    ]);
    c.types.set_local(ARR);
    c.types.set_predefined(ARR);
    let level = std::mem::replace(&mut c.g.level, GENERIC);
    let parameter = var(&mut c);
    let body = constr(&mut c, K, &[parameter]);
    c.g.level = level;
    abbreviation(&mut c, WRAP, &[parameter], body);
    assert_eq!(c.types.rows.len() as u32, FRESH);
    let asked = std::rc::Rc::new(std::cell::RefCell::new(Vec::new()));
    c.locals = Some(Box::new(Fresh {
        next: FRESH,
        asked: asked.clone(),
        answer: DeclMatch::Clash,
        members: Vec::new(),
    }));
    (c, asked)
}

/// A variable at `level` whose name is `text`.
fn named_var_at(c: &mut Checker, level: u32, text: &str) -> Ty {
    let name = name_index(c, text);
    let ty = var_at(c, level);
    c.g.nodes[ty.0 as usize].a = name;
    ty
}

/// The checker is as a pattern unification must leave it, on either
/// result: expression mode, both flags off, no newtype level, no pair
/// assumed, no frame, no open attempt.
fn assert_pattern_left(c: &Checker) {
    assert!(c.umode == UnifyMode::Expression);
    assert!(!c.generate_equations && !c.assume_injective);
    assert_eq!(c.newtype_level, 0);
    assert!(c.pairs.keys.is_empty() && c.compatible.keys.is_empty());
    assert!(c.frames.is_empty() && c.tries.is_empty() && c.scopes.is_empty());
}

/// Witness: `let f = (type a, x: t<a>) => switch x { | Int => ... }`
/// with `type rec t<_> = Int: t<int>`: the result `t<int>` of the
/// constructor against `t<a>`, at the arguments. A locally abstract type
/// against a type that is not one gets the equation on either side
/// (compiler/ml/ctype.ml:2385-2392), the two nodes stay two nodes, and
/// the type is no longer `instantiable`. Under the equation an
/// expression unification of the two succeeds by expansion. After
/// `cut_equations(0)` the row is what it was and a new `n0` does not
/// unify with `int`.
///
/// Reaches: R3h.
#[test]
#[ignore = "R3h build"]
fn an_equation_goes_to_the_locally_abstract_type_and_links_nothing() {
    for swapped in [false, true] {
        let (mut c, _) = pattern_checker(Mode::Success);
        let before = c.types.rows[N0 as usize];
        let (n0, int) = (constr(&mut c, N0, &[]), constr(&mut c, INT, &[]));
        let pair = if swapped { [int, n0] } else { [n0, int] };
        assert!(c.unify_pattern(2, true, true, pair[0], pair[1]).is_ok());
        assert_pattern_left(&c);
        assert_eq!(c.equations.len(), 1);
        assert_eq!(
            (c.equations[0].type_index, c.equations[0].previous),
            (N0, before)
        );
        let row = c.types.rows[N0 as usize];
        assert_eq!(row.flags & (ABBREV | NEWTYPE), ABBREV | NEWTYPE);
        assert!(!c.types.instantiable(N0));
        assert_eq!((c.g.repr(n0), c.g.repr(int)), (n0, int));
        let (other, target) = (constr(&mut c, N0, &[]), constr(&mut c, INT, &[]));
        assert!(c.unify(other, target).is_ok());
        c.cut_equations(0);
        assert!(c.equations.is_empty());
        assert_eq!(c.types.rows[N0 as usize], before);
        let (other, target) = (constr(&mut c, N0, &[]), constr(&mut c, INT, &[]));
        assert!(c.unify(other, target).is_err());
    }
}

/// Witness: `(type a, type b, x: eq<a, b>) => switch x { | Refl => ... }`
/// with `Refl: eq<'c, 'c>`, `b` declared inside `a`. Of two locally
/// abstract types the one of the higher newtype level gets the equation,
/// on either side (compiler/ml/ctype.ml:2373-2384): `n1` (level 2), with
/// `n0` (level 1) its body. A locally abstract type against an abstract
/// type of another unit (`find_newtype_level` gives `(0, 0)` for it,
/// ctype.ml:2085-2091): the locally abstract one. Two abstract types of
/// another unit have one level: the RIGHT one gets it (`else (path',
/// t1')`).
///
/// Reaches: R3h.
#[test]
#[ignore = "R3h build"]
fn of_two_instantiable_types_the_newer_gets_the_equation() {
    for (left, right, source) in [
        (N0, N1, N1),
        (N1, N0, N1),
        (N0, T, N0),
        (T, N0, N0),
        (T, T2, T2),
        (T2, T, T),
    ] {
        let (mut c, _) = pattern_checker(Mode::Success);
        let (l, r) = (constr(&mut c, left, &[]), constr(&mut c, right, &[]));
        assert!(c.unify_pattern(2, true, true, l, r).is_ok());
        assert_eq!(c.equations.len(), 1, "{left} {right}");
        assert_eq!(c.equations[0].type_index, source, "{left} {right}");
        let other = if source == left { right } else { left };
        let node = constr(&mut c, source, &[]);
        let expansion = c.expand_head(node, ExpandMode::Unif).unwrap();
        assert_eq!(path(&mut c, expansion), other);
    }
}

/// Witness: `Pair: t<(int, string)>` against `t<a>`. The body of an
/// equation is a generic copy (`duplicate_type destination`,
/// compiler/ml/ctype.ml:2095): every node of it is generic, it is not
/// the destination, and the destination has the levels it had. An
/// expansion of the type is a copy at the level of the node expanded.
///
/// Reaches: R3h.
#[test]
#[ignore = "R3h build"]
fn the_body_of_an_equation_is_a_generic_copy() {
    let (mut c, _) = pattern_checker(Mode::Success);
    let (int, string) = (constr(&mut c, INT, &[]), constr(&mut c, STRING, &[]));
    let destination = tuple(&mut c, &[int, string]);
    let n0 = constr(&mut c, N0, &[]);
    assert!(c.unify_pattern(2, true, true, n0, destination).is_ok());
    let manifest = c.types.manifests[c.types.rows[N0 as usize].manifest as usize];
    let body = manifest.body;
    assert_ne!(body, destination);
    for ty in [body, child(&mut c, body, 0), child(&mut c, body, 1)] {
        assert_eq!(c.g.nodes[ty.0 as usize].level, GENERIC);
    }
    for ty in [destination, int, string] {
        assert_eq!(c.g.nodes[ty.0 as usize].level, 2);
    }
    let expansion = c.expand_head(n0, ExpandMode::Unif).unwrap();
    assert!(expansion != body && expansion != destination);
    assert_eq!(c.g.nodes[expansion.0 as usize].level, 2);
    let second = child(&mut c, expansion, 1);
    assert_eq!(path(&mut c, second), STRING);
}

/// Witness: `Pack: t<('x, ('y, 'x))>` against `t<a>` after the instance
/// of the constructor: its variables are at the newtype level. `reify`
/// makes one new abstract type for each variable, in the order
/// `iter_type_expr` visits them, each once (compiler/ml/ctype.ml:
/// 1828-1840): the supplier is asked with the name of `x`, then of `y`.
/// Each variable is a link to a nullary constructor of its type at the
/// variable's level; the type's row is a locally abstract type of the
/// newtype level (`new_declaration (Some (newtype_level, newtype_level))
/// None`, ctype.ml:1816).
///
/// Reaches: R3h.
#[test]
#[ignore = "R3h build"]
fn reify_makes_one_type_for_each_variable_in_visit_order() {
    let (mut c, asked) = pattern_checker(Mode::Success);
    let (x, y) = (named_var_at(&mut c, 2, "x"), named_var_at(&mut c, 3, "y"));
    let inner = tuple(&mut c, &[y, x]);
    let destination = tuple(&mut c, &[x, inner]);
    let n0 = constr(&mut c, N0, &[]);
    assert!(c.unify_pattern(2, true, true, n0, destination).is_ok());
    assert_eq!(
        *asked.borrow(),
        [name_index(&mut c, "x"), name_index(&mut c, "y")]
    );
    for (variable, level, ty) in [(x, 2, FRESH), (y, 3, FRESH + 1)] {
        let node = c.g.repr(variable);
        assert_ne!(node, variable);
        assert_eq!(path(&mut c, node), ty);
        assert_eq!(c.g.nodes[node.0 as usize].level, level);
        let row = c.types.rows[ty as usize];
        assert_eq!((row.flags, row.arity), (NEWTYPE, 0));
        let newtype = c.types.newtypes[row.newtype as usize];
        assert_eq!((newtype.level, newtype.expansion_level), (2, 2));
    }
    assert_eq!(c.equations.len(), 1);
}

/// Witness: a variable of the scrutinee's type that is older than the
/// pattern (`(x: t<'a>) => switch x { | Int => ... }` inside a function
/// whose `'a` is not generalized yet). `reify` links the variable to its
/// new type and THEN refuses it, because it is below the newtype level
/// (`link_type ty t; if ty.level < newtype_level then raise (Unify [(t,
/// newvar2 ty.level)])`, compiler/ml/ctype.ml:1837-1839): the
/// unification fails, the variable stays a link (observed on the old
/// checker: decision 62), no equation is added, and in the explaining
/// mode the last pair of the trace is the new type and a new variable at
/// the variable's level.
///
/// Reaches: R3h.
#[test]
#[ignore = "R3h build"]
fn reify_links_a_variable_below_the_newtype_level_and_clashes() {
    for mode in [Mode::Success, Mode::Explain] {
        let (mut c, _) = pattern_checker(mode);
        let old = var_at(&mut c, 1);
        let int = constr(&mut c, INT, &[]);
        let destination = tuple(&mut c, &[old, int]);
        let n0 = constr(&mut c, N0, &[]);
        assert!(c.unify_pattern(2, true, true, n0, destination).is_err());
        assert_pattern_left(&c);
        assert!(c.equations.is_empty());
        let node = c.g.repr(old);
        assert_ne!(node, old);
        assert_eq!(path(&mut c, node), FRESH);
        assert_eq!(c.g.nodes[node.0 as usize].level, 1);
        if mode == Mode::Explain {
            let [left, right] = *c.trace.last().unwrap();
            assert_eq!(left, node);
            let variable = c.g.nodes[right.0 as usize];
            assert_eq!((variable.tag(), variable.level), (VAR, 1));
        }
    }
}

/// Witness: `Int: t<int>` against `t<k<a>>`'s argument and its
/// relatives: two constructors of one type in pattern mode
/// (compiler/ml/ctype.ml:2349-2358). As `unify_gadt` runs it
/// (`assume_injective`) the arguments are unified with equations:
/// `k<n0>` against `k<int>` gives `n0 := int`. Without
/// `assume_injective` a data type (`d`) and a type of the unit (`LOCAL`,
/// here set on `box`) still do. Without `generate_equations` the
/// arguments are unified without equations: `n0` against `int` is then
/// reified and nothing more (ctype.ml:2393-2397): a success and no
/// equation. The two constructor nodes are never linked, and the flags
/// are what they were afterwards (`set_mode_pattern` puts them back,
/// ctype.ml:256-273).
///
/// Reaches: R3h.
#[test]
#[ignore = "R3h build"]
fn the_arguments_of_one_type_are_unified_by_the_flags() {
    for (ty, generate, injective, equation) in [
        (K, true, true, true),
        (D, true, false, true),
        (BOX, true, false, true),
        (K, false, true, false),
        (K, false, false, false),
        (D, false, false, false),
    ] {
        let (mut c, _) = pattern_checker(Mode::Success);
        c.types.set_local(BOX);
        let (n0, int) = (constr(&mut c, N0, &[]), constr(&mut c, INT, &[]));
        let (left, right) = (constr(&mut c, ty, &[n0]), constr(&mut c, ty, &[int]));
        assert!(c.unify_pattern(2, generate, injective, left, right).is_ok());
        assert_pattern_left(&c);
        assert_eq!(
            c.equations.len(),
            usize::from(equation),
            "{ty} {generate} {injective}"
        );
        assert_eq!((c.g.repr(left), c.g.repr(right)), (left, right));
        assert_eq!((c.g.repr(n0), c.g.repr(int)), (n0, int));
    }
}

/// Witness: `Pair: t<(int, int)>` against `t<(a, int)>`. Two structures
/// in pattern mode are assumed equal and NOT linked (`Pattern ->
/// add_type_equality t1' t2'`, compiler/ml/ctype.ml:2327-2331): the old
/// checker links them and is no judge here (decision 62). The two
/// tuples are two nodes afterwards, the equation `n0 := int` is added,
/// and the table of assumed pairs is empty again. A clash below
/// (`(n0, (int, int))` against `(int, (int, int, int))`: `unify_list`
/// of two lengths) leaves both tuples as they
/// were, in both modes, and the equation its first element added stays
/// until the caller cuts it (`env` is not restored by a failure).
///
/// Reaches: R3h.
#[test]
#[ignore = "R3h build"]
fn two_structures_are_assumed_equal_and_not_linked() {
    for mode in [Mode::Success, Mode::Explain] {
        for clash in [false, true] {
            let (mut c, _) = pattern_checker(mode);
            let (n0, int) = (constr(&mut c, N0, &[]), constr(&mut c, INT, &[]));
            // The clash is two tuples of different lengths, which no
            // arm of a constructor takes (`mcomp` is R3r's).
            let ints: Vec<Ty> = (0..5).map(|_| constr(&mut c, INT, &[])).collect();
            let (first, second) = if clash {
                (tuple(&mut c, &ints[..2]), tuple(&mut c, &ints[2..]))
            } else {
                (ints[0], ints[1])
            };
            let (left, right) = (tuple(&mut c, &[n0, first]), tuple(&mut c, &[int, second]));
            let (l, r) = (c.g.nodes[left.0 as usize], c.g.nodes[right.0 as usize]);
            let result = c.unify_pattern(2, true, true, left, right);
            assert_eq!(result.is_err(), clash);
            assert_pattern_left(&c);
            assert_eq!(
                (c.g.nodes[left.0 as usize], c.g.nodes[right.0 as usize]),
                (l, r)
            );
            assert_eq!(c.equations.len(), 1);
            assert_eq!(c.equations[0].type_index, N0);
            if clash && mode == Mode::Explain {
                assert_eq!(c.trace.first(), Some(&[left, right]));
            }
        }
    }
}

/// Witness: `(type a, type b, x: eq<a, b>, w: eq<a, int>, y: b): a =>
/// switch (x, w) { | (Refl, Refl) => y }`: in the case, `b` against `a`
/// in expression mode under `b := a` and `a := int`. The arm of `unify`
/// for two locally abstract types under local constraints expands the
/// NEWER one, once, and no more ("Do not use local constraints more than
/// necessary", compiler/ml/ctype.ml:2258-2269):
///
/// ```text
/// if find_newtype_level !env p1 < find_newtype_level !env p2 then
///   unify env t1 (try_expand_once !env t2)
/// else unify env (try_expand_once !env t1) t2
/// ```
///
/// `n1` (level 2) expands to a copy of its body, a node of `n0`, which
/// the arm for two constructors of one type links to the other `n0`
/// node (ctype.ml:2248-2257): the memorized expansion of the `n1` node
/// IS that node afterwards, and `n0`, which has an equation too, was
/// never expanded: its memo is empty. Without the arm unify2 would
/// expand both heads to `int`.
///
/// The equations are added in the order `n1 := n0` (both instantiable:
/// the newer is the source, ctype.ml:2376-2387), then `n0 := int`; the
/// expansion level of each is the newtype level of its pattern
/// (`Env.add_local_constraint`, compiler/ml/env.ml:1805-1810).
///
/// Reaches: R3h.
#[test]
#[ignore = "R3h build"]
fn the_newer_of_two_locally_abstract_types_is_expanded_once() {
    let (mut c, _) = pattern_checker(Mode::Success);
    let (n1, older) = (constr(&mut c, N1, &[]), constr(&mut c, N0, &[]));
    assert!(c.unify_pattern(3, true, true, n1, older).is_ok());
    let (n0, int) = (constr(&mut c, N0, &[]), constr(&mut c, INT, &[]));
    assert!(c.unify_pattern(4, true, true, n0, int).is_ok());
    assert_eq!(c.equations.len(), 2);
    assert_eq!(
        (c.equations[0].type_index, c.equations[1].type_index),
        (N1, N0)
    );
    assert_eq!(
        (c.find_newtype_level(N1), c.find_newtype_level(N0)),
        ((2, 3), (1, 4))
    );
    let (left, right) = (constr(&mut c, N1, &[]), constr(&mut c, N0, &[]));
    assert!(c.unify(left, right).is_ok());
    assert_eq!((c.g.repr(left), c.g.repr(right)), (left, right));
    let expansion = c.find_expansion(left, false);
    assert_eq!(c.g.repr(expansion), right);
    assert_eq!(c.find_expansion(right, false).0, NONE);
    // The other way round the same type is expanded: the newer one,
    // now on the right. The `n1` node stays a node, and the `n0` node is
    // linked to a node of `n0`.
    let (left, right) = (constr(&mut c, N0, &[]), constr(&mut c, N1, &[]));
    assert!(c.unify(left, right).is_ok());
    assert_eq!(c.g.repr(right), right);
    assert_eq!(path(&mut c, left), N0);
}

/// Which types an equation may name its own type in
/// (`local_non_recursive_abbrev`, compiler/ml/ctype.ml:1503-1536, called
/// with `strict = false`; `add_gadt_equation` adds nothing and does not
/// clash when it answers false, ctype.ml:2093-2094):
///
/// ```text
/// | Tconstr (p', args, _abbrev) -> (
///   if Path.same p p' then raise Occur;
///   if (not strict) && is_contractive env p' then ()
///   else
///     let visited = ty :: visited in
///     try
///       (* try expanding, since [p] could be hidden *)
///       local_non_recursive_abbrev strict visited env p
///         (try_expand_head try_expand_once env ty)
///     with Cannot_expand ->
///       let params =
///         try (Env.find_type p' env).type_params with Not_found -> args
///       in
///       List.iter2
///         (fun tv ty ->
///           let strict = strict || not (is_Tvar (repr tv)) in
///           local_non_recursive_abbrev strict visited env p ty)
///         params args)
/// | _ ->
///   if strict then
/// ```
///
/// The first four cases are source programs both compilers were run on
/// (the review of the sixth skeleton turn): `type rec eq<_, _> = Refl:
/// eq<'a, 'a>` and `let f = (type a, x: eq<a, T>, y: a): T => switch x {
/// | Refl => y }`. For `T` = `(a, int)`, `array<a>` and `box<a>` with
/// `type box<'a> = Box('a)` both ACCEPT: the equation is added (a tuple
/// at the top is not searched while not strict; a predefined type
/// without a manifest and a data type are contractive, ctype.ml:
/// 1371-1375, and not entered). For `T` = `M.t<a>` with `module M: {type
/// t<'a>} = {type t<'a> = int}` both REFUSE ("This has type: a / But
/// this switch is expected to return: M.t<a>"): an abstract constructor
/// is not contractive and cannot be expanded, so its arguments are
/// walked, and no equation is added.
///
/// The others follow from the lines above: an abbreviation is expanded
/// first, so `wrap<a>` with `type wrap<'x> = k<'x>` is refused and
/// `pa<a>` with `type pa<'x> = ('x, int)` is added; below an abstract
/// constructor the walk is still not strict, so `k<(a, int)>` is added
/// (`strict || not (is_Tvar (repr tv))`, ctype.ml:1522: the declared
/// parameter of `k` is a variable; this case was NOT run through the
/// compilers), unless the parameter of the
/// declaration is not a variable (`TypeTable::constrained`), or the type
/// has no declaration and the argument is not a variable (`with
/// Not_found -> args`).
///
/// Reaches: R3h.
#[test]
#[ignore = "R3h build"]
fn an_equation_names_its_type_only_below_a_structure_or_a_contractive_type() {
    /// A type index the table has no row for.
    const UNDECLARED: u32 = 1_000;
    let pair = |c: &mut Checker| {
        let (inner, int) = (constr(c, N0, &[]), constr(c, INT, &[]));
        tuple(c, &[inner, int])
    };
    let of = |ty: u32| move |c: &mut Checker| {
        let inner = constr(c, N0, &[]);
        constr(c, ty, &[inner])
    };
    let over_pair = |ty: u32| move |c: &mut Checker| {
        let argument = pair(c);
        constr(c, ty, &[argument])
    };
    type Build = Box<dyn Fn(&mut Checker) -> Ty>;
    let cases: [(&str, Build, bool, bool); 10] = [
        ("(a, int)", Box::new(pair), false, true),
        ("array<a>", Box::new(of(ARR)), false, true),
        ("d<a>", Box::new(of(D)), false, true),
        ("k<a>", Box::new(of(K)), false, false),
        ("wrap<a>", Box::new(of(WRAP)), false, false),
        ("pa<a>", Box::new(of(PA)), false, true),
        ("k<(a, int)>", Box::new(over_pair(K)), false, true),
        ("k<(a, int)>, constrained", Box::new(over_pair(K)), true, false),
        ("undeclared<(a, int)>", Box::new(over_pair(UNDECLARED)), false, false),
        ("d<(a, int)>", Box::new(over_pair(D)), false, true),
    ];
    for (text, build, constrained, added) in cases {
        let (mut c, _) = pattern_checker(Mode::Success);
        if constrained {
            c.types.constrained_bits = vec![0; K as usize + 1];
            c.types.constrained_bits[K as usize] = 1;
        }
        let destination = build(&mut c);
        let n0 = constr(&mut c, N0, &[]);
        assert!(c.unify_pattern(2, true, true, n0, destination).is_ok(), "{text}");
        assert_pattern_left(&c);
        assert_eq!(c.equations.len(), usize::from(added), "{text}");
        let flags = c.types.rows[N0 as usize].flags;
        assert_eq!(flags & ABBREV != 0, added, "{text}");
        if added {
            // Under the equation the type expands to a copy of the
            // destination in which a node of the type itself is a link
            // to the node expanded (`find_repr`, ctype.ml:720, 782: the
            // memo is written before the body is copied).
            let node = constr(&mut c, N0, &[]);
            let expansion = c.expand_head(node, ExpandMode::Unif).unwrap();
            assert_ne!(expansion, node, "{text}");
        }
    }
}

/// The occurrence test of a variable in pattern mode (`occur_full` with
/// `allow_recursive`, compiler/ml/ctype.ml:1467-1490; `occur_rec`,
/// 1384-1408):
///
/// ```text
/// | Tconstr (p, _tl, _abbrev) -> (
///   if allow_recursive && is_contractive env p then ()
///   else
/// ...
/// | Tobject _ | Tvariant _ -> ()
/// | _ ->
///   if allow_recursive || Type_set.mem ty visited then ()
/// ```
///
/// A structure that is not a constructor is not entered, nor is a
/// contractive constructor (a data type, a predefined type without a
/// manifest). So in pattern mode a variable is bound to a tuple, to a
/// data type or to `array` that holds it, where expression mode
/// clashes; the levels are lowered as by any binding (`update_level
/// env t1.level t2`, ctype.ml:2222): `w`, of level 2 below the tuple,
/// is at the variable's level 1 afterwards. Through a constructor that
/// is not contractive the occurrence is a clash in both modes, directly
/// (`k<'v>`) and through an abbreviation that expands to one
/// (`wrap<'v>`); below a structure below such a constructor it is not
/// one (`k<('v, int)>`). A variable against a constructor that holds it
/// goes to unify2 first (`Tvar _, Tconstr _ when deep_occur t1 t2`,
/// ctype.ml:2240), whose variable arm makes the same test (2316-2319).
///
/// Reaches: R3h.
#[test]
#[ignore = "R3h build"]
fn a_variable_is_bound_to_a_type_that_holds_it_below_a_structure() {
    for mode in [Mode::Success, Mode::Explain] {
        let build = |c: &mut Checker, shape: u32, v: Ty| -> Ty {
            let int = constr(c, INT, &[]);
            match shape {
                0 => tuple(c, &[v, int]),
                1 => constr(c, D, &[v]),
                2 => constr(c, ARR, &[v]),
                3 => constr(c, K, &[v]),
                4 => constr(c, WRAP, &[v]),
                _ => {
                    let pair = tuple(c, &[v, int]);
                    constr(c, K, &[pair])
                }
            }
        };
        for (shape, pattern) in [(0, true), (1, true), (2, true), (3, false), (4, false), (5, true)] {
            for swapped in [false, true] {
                let (mut c, _) = pattern_checker(mode);
                let v = var_at(&mut c, 1);
                let ty = build(&mut c, shape, v);
                let pair = if swapped { [ty, v] } else { [v, ty] };
                let result = c.unify_pattern(2, true, true, pair[0], pair[1]);
                assert_eq!(result.is_ok(), pattern, "{shape} {swapped}");
                assert_pattern_left(&c);
                if pattern {
                    let root = c.g.repr(v);
                    assert_eq!(root, c.g.repr(ty), "{shape} {swapped}");
                    assert_ne!(c.g.nodes[root.0 as usize].tag(), VAR);
                    assert_eq!(c.g.nodes[root.0 as usize].level, 1, "{shape} {swapped}");
                } else {
                    assert_eq!(c.g.repr(v), v, "{shape} {swapped}");
                }
                // Expression mode refuses every one of them.
                let (mut c, _) = pattern_checker(mode);
                let v = var_at(&mut c, 1);
                let ty = build(&mut c, shape, v);
                let pair = if swapped { [ty, v] } else { [v, ty] };
                assert!(c.unify(pair[0], pair[1]).is_err(), "{shape} {swapped}");
            }
        }
        // The levels below the structure are lowered.
        let (mut c, _) = pattern_checker(mode);
        let (v, w) = (var_at(&mut c, 1), var_at(&mut c, 2));
        let inner = tuple(&mut c, &[w, v]);
        let ty = tuple(&mut c, &[v, inner]);
        assert!(c.unify_pattern(2, true, true, v, ty).is_ok());
        for node in [ty, inner, w] {
            assert_eq!(c.g.nodes[node.0 as usize].level, 1);
        }
    }
}

/// Witness: a pattern whose type has 10,000 components. Relations
/// between 1,000 and 10,000 (CHECKER_REWRITE 8.9, "Step tests"):
/// - a chain of n nested tuples against a second chain of the same
///   shape in pattern mode: the steps are linear in the pairs, no node
///   of either chain is a link, the table of assumed pairs is empty;
/// - `reify` of a tuple of n variables, each named twice: every
///   variable is visited once, steps linear, n types made; and of a
///   chain of n tuples each naming the one below twice (n + 1 nodes,
///   2^n paths): steps linear, one type made;
/// - n equations added and cut: steps linear, every row what it was.
///
/// Reaches: R3h.
#[test]
#[ignore = "R3h build"]
fn pattern_mode_at_ten_thousand() {
    let chain = |c: &mut Checker, n: u32| {
        let mut ty = constr(c, INT, &[]);
        for _ in 0..n {
            let int = constr(c, INT, &[]);
            ty = tuple(c, &[int, ty]);
        }
        ty
    };
    let structures = |n: u32| {
        let (mut c, _) = pattern_checker(Mode::Success);
        let (left, right) = (chain(&mut c, n), chain(&mut c, n));
        let nodes = c.g.nodes.len();
        let mut result = Err(super::unify::Clash);
        let count = steps::scope(|| result = c.unify_pattern(2, true, true, left, right));
        assert!(result.is_ok());
        assert_pattern_left(&c);
        // The nullary `int` pairs are linked in every mode
        // (ctype.ml:2248-2257); no tuple is.
        for index in 0..nodes {
            let node = c.g.nodes[index];
            assert!(node.tag() != LINK || path(&mut c, Ty(index as u32)) == INT);
        }
        count
    };
    let (small, large) = (structures(1_000), structures(10_000));
    assert!(large <= 11 * small, "structures: {small} {large}");

    let reified = |n: u32| {
        let (mut c, asked) = pattern_checker(Mode::Success);
        let variables: Vec<Ty> = (0..n).map(|_| var(&mut c)).collect();
        let mut elements = variables.clone();
        elements.extend(&variables);
        let ty = tuple(&mut c, &elements);
        c.newtype_level = 2;
        let mut result = Err(super::unify::Clash);
        let count = steps::scope(|| result = c.reify(ty));
        assert!(result.is_ok());
        assert_eq!(asked.borrow().len(), n as usize);
        count
    };
    let (small, large) = (reified(1_000), reified(10_000));
    assert!(large <= 11 * small, "reify: {small} {large}");

    // A chain of n tuples, each naming the one below twice, over one
    // variable: n + 1 nodes and 2^n paths. Every node is visited once.
    let shared = |n: u32| {
        let (mut c, asked) = pattern_checker(Mode::Success);
        let mut ty = var(&mut c);
        for _ in 0..n {
            ty = tuple(&mut c, &[ty, ty]);
        }
        c.newtype_level = 2;
        let mut result = Err(super::unify::Clash);
        let count = steps::scope(|| result = c.reify(ty));
        assert!(result.is_ok());
        assert_eq!(asked.borrow().len(), 1);
        count
    };
    let (small, large) = (shared(1_000), shared(10_000));
    assert!(large <= 11 * small, "reify of shared nodes: {small} {large}");

    let equations = |n: u32| {
        let (mut c, _) = pattern_checker(Mode::Success);
        let first = c.types.rows.len() as u32;
        for _ in 0..n {
            let row = c.types.rows[T as usize];
            c.types.rows.push(row);
        }
        let before = c.types.rows.clone();
        let count = steps::scope(|| {
            for index in 0..n {
                let (ty, int) = (constr(&mut c, first + index, &[]), constr(&mut c, INT, &[]));
                assert!(c.unify_pattern(2, true, true, ty, int).is_ok());
            }
            assert_eq!(c.equations.len(), n as usize);
            c.cut_equations(0);
        });
        assert_eq!(c.types.rows, before);
        count
    };
    let (small, large) = (equations(1_000), equations(10_000));
    assert!(large <= 11 * small, "equations: {small} {large}");
}

/// Witness: an equation whose destination has 10,000 nodes that share
/// their children: `t(0) = int`, `t(i + 1) = k2<t(i), t(i)>` for an
/// abstract `k2`, n + 1 nodes and 2^n paths. Relations between 1,000
/// and 10,000:
/// - `non_recursive_abbrev` visits a node once however many paths reach
///   it (twice at most: once strictly, compiler/ml/ctype.ml:1503-1529):
///   linear, where OCaml's list of the nodes on the way walks every
///   path; with `n0` at the bottom the answer is false, after as many
///   steps;
/// - `duplicate` keeps the sharing (`duplicate_type`, ctype.ml:496): n +
///   1 new nodes, all generic, linear steps, and the destination has the
///   levels it had and no speculation is left open.
///
/// Reaches: R3h.
#[test]
#[ignore = "R3h build"]
fn an_equation_over_ten_thousand_shared_nodes_is_linear() {
    let run = |n: u32, strict: bool, bottom: u32| {
        let (mut c, _) = pattern_checker(Mode::Success);
        if strict {
            c.types.constrained_bits = vec![0; K2 as usize + 1];
            c.types.constrained_bits[K2 as usize] = 3;
        }
        let mut ty = constr(&mut c, bottom, &[]);
        for _ in 0..n {
            ty = constr(&mut c, K2, &[ty, ty]);
        }
        let nodes = c.g.nodes.len();
        let mut answer = Ok(false);
        let walk = steps::scope(|| answer = c.non_recursive_abbrev(N0, ty));
        assert_eq!(answer, Ok(bottom != N0));
        assert!(c.frames.is_empty());
        let levels: Vec<u32> = c.g.nodes.iter().map(|node| node.level).collect();
        let mut copy = ty;
        let duplicate = steps::scope(|| copy = c.duplicate(ty));
        assert_ne!(copy, ty);
        assert_eq!(c.g.nodes.len(), nodes + n as usize + 1);
        assert!(c.g.nodes[nodes..].iter().all(|node| node.level == GENERIC));
        let after: Vec<u32> = c.g.nodes[..nodes].iter().map(|node| node.level).collect();
        assert_eq!(after, levels);
        assert_eq!(c.g.speculation_depth, 0);
        (walk, duplicate)
    };
    for (strict, bottom) in [(false, INT), (true, INT), (false, N0), (true, N0)] {
        let (small, large) = (run(1_000, strict, bottom), run(10_000, strict, bottom));
        assert!(large.0 <= 11 * small.0, "walk {strict} {bottom}: {small:?} {large:?}");
        assert!(large.1 <= 11 * small.1, "duplicate {strict} {bottom}: {small:?} {large:?}");
    }
}

/// Witness: `Int: t<k<int>>` against `t<k<a>>` below a constructor
/// whose arguments were already entered (`generate_equations` on,
/// `assume_injective` off), `k` abstract and of another unit. Its
/// argument is not injective: it is unified without equations under a
/// snapshot, and when that fails the graph goes back and both arguments
/// are reified (compiler/ml/ctype.ml:2358-2375).
/// - `k<n0>` against `k<int>`: no equation, a success.
/// - `k<'v>` against `k<int>`: the attempt succeeds and is kept: `'v`
///   is a link to `int`.
/// - `k<('v, (int, int))>` against `k<(int, (int, int, int))>`: the
///   attempt binds `'v` to `int` and then fails at the two tuples of
///   different lengths; the graph goes back, so `'v` is a variable
///   again, and is reified: a link to the first fresh type, not to
///   `int`. (With `generate_equations` off a constructor against
///   anything is reified and never clashes, ctype.ml:2396-2400: an
///   attempt fails on two structures of different shapes.)
/// - two arguments, `k2<'v, ('w, (int, int))>` against `k2<int, (string,
///   (int, int, int))>`: each argument is its own attempt, with its own
///   snapshot taken when the attempt is reached (`List.iter2`,
///   ctype.ml:2364-2375): the first binds `'v` to `int` and is kept, the
///   second fails and goes back to what the first left: `'v` is `int`
///   and `'w` a fresh type.
/// - with the parameter marked injective (`injective_bits`), `k<n0>`
///   against `k<int>` gives `n0 := int`.
///
/// No attempt is left open and, in `Mode::Success`, no speculation.
///
/// Reaches: R3h, R3r.
#[test]
#[ignore = "R3r build"]
fn an_argument_that_is_not_injective_is_tried_and_then_reified() {
    for mode in [Mode::Success, Mode::Explain] {
        let (mut c, _) = pattern_checker(mode);
        let (n0, int) = (constr(&mut c, N0, &[]), constr(&mut c, INT, &[]));
        let (left, right) = (constr(&mut c, K, &[n0]), constr(&mut c, K, &[int]));
        assert!(c.unify_pattern(2, true, false, left, right).is_ok());
        assert_pattern_left(&c);
        assert!(c.equations.is_empty());
        assert_eq!(c.g.speculation_depth, 0);

        let (v, int) = (var(&mut c), constr(&mut c, INT, &[]));
        let (left, right) = (constr(&mut c, K, &[v]), constr(&mut c, K, &[int]));
        assert!(c.unify_pattern(2, true, false, left, right).is_ok());
        assert_eq!(c.g.repr(v), int);

        let ints = |c: &mut Checker, n: usize| {
            let elements: Vec<Ty> = (0..n).map(|_| constr(c, INT, &[])).collect();
            tuple(c, &elements)
        };
        let (v, int) = (var(&mut c), constr(&mut c, INT, &[]));
        let (two, three) = (ints(&mut c, 2), ints(&mut c, 3));
        let (l, r) = (tuple(&mut c, &[v, two]), tuple(&mut c, &[int, three]));
        let (left, right) = (constr(&mut c, K, &[l]), constr(&mut c, K, &[r]));
        assert!(c.unify_pattern(2, true, false, left, right).is_ok());
        assert_pattern_left(&c);
        let node = c.g.repr(v);
        assert_eq!(path(&mut c, node), FRESH);
        assert_eq!(c.g.speculation_depth, 0);

        let (v, w) = (var(&mut c), var(&mut c));
        let (int, string) = (constr(&mut c, INT, &[]), constr(&mut c, STRING, &[]));
        let (two, three) = (ints(&mut c, 2), ints(&mut c, 3));
        let (l, r) = (tuple(&mut c, &[w, two]), tuple(&mut c, &[string, three]));
        let (left, right) = (constr(&mut c, K2, &[v, l]), constr(&mut c, K2, &[int, r]));
        assert!(c.unify_pattern(2, true, false, left, right).is_ok());
        assert_pattern_left(&c);
        assert_eq!(c.g.repr(v), int);
        let node = c.g.repr(w);
        assert_eq!(path(&mut c, node), FRESH + 1);
        assert_eq!(c.g.speculation_depth, 0);

        c.types.injective_bits = vec![0; K as usize + 1];
        c.types.injective_bits[K as usize] = 1;
        let (n0, int) = (constr(&mut c, N0, &[]), constr(&mut c, INT, &[]));
        let (left, right) = (constr(&mut c, K, &[n0]), constr(&mut c, K, &[int]));
        assert!(c.unify_pattern(2, true, false, left, right).is_ok());
        assert_eq!(c.equations.len(), 1);
    }
}

/// Witness: a constructor whose result is `t<[> #A]>` against a
/// scrutinee `t<[> #A | #B]>` whose row was fixed by an earlier case.
/// Two variants in pattern mode are unified under a snapshot; when that
/// fails the graph goes back, both are reified and, with equations,
/// compared with `mcomp` (compiler/ml/ctype.ml:2402-2411).
/// - a fixed row `[> #A]` (made by `reify`) against an open row with
///   one more tag: `unify_row` refuses to extend the fixed row, `mcomp`
///   accepts (no row is closed): a success, the two rows are two nodes,
///   the open one is a fixed row afterwards (observed on the old
///   checker: decision 62);
/// - two closed rows `[#A]` and `[#B]`: `mcomp` refuses (a present tag
///   the other closed row lacks, ctype.ml:1991-1994): a clash;
/// - the same without `generate_equations`: no `mcomp`, a success.
///
/// Reaches: R3f, R3h, R3r.
#[test]
#[ignore = "R3r build"]
fn rows_that_clash_are_reified_and_compared() {
    for mode in [Mode::Success, Mode::Explain] {
        let (mut c, _) = pattern_checker(mode);
        let (more1, more2) = (var(&mut c), var(&mut c));
        let fixed = variant_at(&mut c, 2, &[("A", Tag::Present(None))], more1, false, NONE);
        c.newtype_level = 2;
        assert!(c.reify(fixed).is_ok());
        c.newtype_level = 0;
        assert!(shape(&mut c, fixed).contains("fixed"));
        let open = variant_at(
            &mut c,
            2,
            &[("A", Tag::Present(None)), ("B", Tag::Present(None))],
            more2,
            false,
            NONE,
        );
        assert!(c.unify_pattern(2, true, true, fixed, open).is_ok());
        assert_pattern_left(&c);
        assert_eq!((c.g.repr(fixed), c.g.repr(open)), (fixed, open));
        assert!(shape(&mut c, open).contains("fixed"));
        // The row variable is a link to a fixed row without tags over
        // the fresh type (`link_type m (newty2 m.level (Tvariant row))`,
        // ctype.ml:1848-1851), not to the type itself.
        let tail = c.g.repr(more2);
        assert_eq!(shape(&mut c, tail), "[fixed | t]");
        let (_, _, more) = read_row(&mut c, open);
        assert_eq!(path(&mut c, more), FRESH + 1);

        for (generate, clash) in [(true, true), (false, false)] {
            let (nil1, nil2) = (
                extended_at(&mut c, 2, ExtraDescriptor::Nil, &[]),
                extended_at(&mut c, 2, ExtraDescriptor::Nil, &[]),
            );
            let left = variant_at(&mut c, 2, &[("A", Tag::Present(None))], nil1, true, NONE);
            let right = variant_at(&mut c, 2, &[("B", Tag::Present(None))], nil2, true, NONE);
            let result = c.unify_pattern(2, generate, true, left, right);
            assert_eq!(result.is_err(), clash);
            assert_pattern_left(&c);
            assert_eq!((c.g.repr(left), c.g.repr(right)), (left, right));
        }
    }
}

/// Witness: `Int: t<int>` against `t<string>`, `t<M.t>`, `t<d<int>>`:
/// what `mcomp` answers (compiler/ml/ctype.ml:1905-2039), one line an
/// arm. It never links: every node is its own representative
/// afterwards, and its table is empty.
/// - a variable against anything: compatible;
/// - `int` against `string`, both bare identifiers that are not locally
///   abstract (`non_aliasable`): a clash;
/// - `M.t`, abstract and of another unit, against `int`: compatible
///   (`Type_abstract, Type_abstract`);
/// - `M.t` against a tuple: compatible; `int` against a tuple: a clash
///   (`non_aliasable p decl || is_datatype decl`);
/// - a tuple against an arrow: a clash; `(int, M.t)` against `(int,
///   myint)`: compatible, through the expansion of `myint`;
/// - `d<int>` against `d<string>`: compatible while the parameter is
///   not injective, a clash when it is;
/// - `d<int>` against `e<int>`, two data types: what the supplier
///   answers: `Clash`; `Members` with no pair: compatible; `Members`
///   after pushing the pair of `int` and `string`: a clash; with no
///   supplier: a clash (CHECKER_REWRITE 8.9, "No supplier").
///
/// Reaches: R3r.
#[test]
#[ignore = "R3r build"]
fn mcomp_answers_by_the_declarations() {
    let (mut c, _) = pattern_checker(Mode::Success);
    let int = |c: &mut Checker| constr(c, INT, &[]);
    let (v, i, s, t) = (
        var(&mut c),
        int(&mut c),
        constr(&mut c, STRING, &[]),
        constr(&mut c, T, &[]),
    );
    let pair = {
        let (a, b) = (int(&mut c), int(&mut c));
        tuple(&mut c, &[a, b])
    };
    let function = {
        let (a, b) = (int(&mut c), int(&mut c));
        arrow(&mut c, &[a], b)
    };
    let (with_t, with_myint) = {
        let (a, b, m) = (int(&mut c), int(&mut c), constr(&mut c, MYINT, &[]));
        let t = constr(&mut c, T, &[]);
        (tuple(&mut c, &[a, t]), tuple(&mut c, &[b, m]))
    };
    let (d_int, d_string) = {
        let (a, b) = (int(&mut c), constr(&mut c, STRING, &[]));
        (constr(&mut c, D, &[a]), constr(&mut c, D, &[b]))
    };
    let nodes = c.g.nodes.len();
    for (left, right, compatible) in [
        (v, pair, true),
        (i, s, false),
        (t, i, true),
        (t, pair, true),
        (i, pair, false),
        (pair, function, false),
        (with_t, with_myint, true),
        (d_int, d_string, true),
    ] {
        assert_eq!(
            c.mcomp(left, right).is_ok(),
            compatible,
            "{left:?} {right:?}"
        );
        assert!(c.compatible.keys.is_empty());
    }
    for node in &c.g.nodes[..nodes] {
        assert_ne!(node.tag(), LINK);
    }
    c.types.injective_bits = vec![0; D as usize + 1];
    c.types.injective_bits[D as usize] = 1;
    assert!(c.mcomp(d_int, d_string).is_err());

    let e_int = {
        let a = int(&mut c);
        constr(&mut c, E, &[a])
    };
    let supplier = |answer: DeclMatch, members: Vec<[Ty; 2]>| -> Option<Box<dyn LocalDecls>> {
        Some(Box::new(Fresh {
            next: FRESH,
            asked: Default::default(),
            answer,
            members,
        }))
    };
    assert!(c.mcomp(d_int, e_int).is_err());
    c.locals = supplier(DeclMatch::Members, Vec::new());
    assert!(c.mcomp(d_int, e_int).is_ok());
    c.locals = supplier(DeclMatch::Members, vec![[i, s]]);
    assert!(c.mcomp(d_int, e_int).is_err());
    c.locals = None;
    assert!(c.mcomp(d_int, e_int).is_err());
    assert!(c.compatible.keys.is_empty());
}

/// Witness: two types of 10,000 components that `mcomp` compares.
/// Relation between 1,000 and 10,000: two tuples of n elements whose
/// elements are the SAME n-deep chain pairwise (every element of the
/// left is one node, every element of the right another): the table
/// (`Type_pairs.find type_pairs (t1', t2')`, compiler/ml/ctype.ml:
/// 1922-1924) makes the second and every later pair of the chains one
/// lookup, so the steps are linear in n. Without the table every
/// element walks the chain again: n times n pairs, a hundred times the
/// steps for ten times n. The width is n: at a fixed width the relation
/// holds with or without the table.
///
/// Reaches: R3r.
#[test]
#[ignore = "R3r build"]
fn mcomp_at_ten_thousand() {
    let run = |n: u32| {
        let (mut c, _) = pattern_checker(Mode::Success);
        let chain = |c: &mut Checker| {
            let mut ty = constr(c, T, &[]);
            for _ in 0..n {
                let int = constr(c, INT, &[]);
                ty = tuple(c, &[int, ty]);
            }
            ty
        };
        let (a, b) = (chain(&mut c), chain(&mut c));
        let (left, right) = (
            tuple(&mut c, &vec![a; n as usize]),
            tuple(&mut c, &vec![b; n as usize]),
        );
        let mut result = Err(super::unify::Clash);
        let count = steps::scope(|| result = c.mcomp(left, right));
        assert!(result.is_ok());
        assert!(c.compatible.keys.is_empty() && c.frames.is_empty());
        count
    };
    let (small, large) = (run(1_000), run(10_000));
    assert!(large <= 11 * small, "mcomp: {small} {large}");
}

/// Witness: a pattern over n arguments that are not injective, each of
/// which fails and falls back: a tuple of n `k<(int, int)>` against a
/// tuple of n `k<(int, int, int)>` with `generate_equations` on and
/// `assume_injective` off. Each argument is one attempt
/// (compiler/ml/ctype.ml:2364-2375): started when it is reached, failed
/// at the two tuples of different lengths, taken back and reified. A
/// clash is recovered by the LAST record of `Checker::tries` alone: one
/// step a record, whatever lies below it in `frames` (here the n - 1
/// pairs still to come). Relation between 1,000 and 10,000: linear; a
/// `recover` that looks for its frame from the base of the unification
/// reads n frames a clash and takes a hundred times the steps.
///
/// Reaches: R3h, R3r.
#[test]
#[ignore = "R3r build"]
fn recovering_ten_thousand_attempts_is_linear() {
    let run = |n: u32| {
        let (mut c, _) = pattern_checker(Mode::Success);
        let side = |c: &mut Checker, width: usize| {
            let elements: Vec<Ty> = (0..n)
                .map(|_| {
                    let ints: Vec<Ty> = (0..width).map(|_| constr(c, INT, &[])).collect();
                    let argument = tuple(c, &ints);
                    constr(c, K, &[argument])
                })
                .collect();
            tuple(c, &elements)
        };
        let (left, right) = (side(&mut c, 2), side(&mut c, 3));
        let mut result = Err(super::unify::Clash);
        let count = steps::scope(|| result = c.unify_pattern(2, true, false, left, right));
        assert!(result.is_ok());
        assert_pattern_left(&c);
        assert_eq!(c.g.speculation_depth, 0);
        count
    };
    let (small, large) = (run(1_000), run(10_000));
    assert!(large <= 11 * small, "recover: {small} {large}");
}

/// Decision 60 in pattern mode. Witness: `[> #A] as P<y>` (the LEFT
/// node, its own last row) against `[> #B]` in pattern mode, `y` in no
/// field. Pattern mode links neither variant node (`Pattern ->
/// add_type_equality t1' t2'`, compiler/ml/ctype.ml:2327-2332), so the
/// home of row 1 is the left node itself, still a variant node whose
/// `more` is linked to a variant node by `set_more` (`link_type rm ty`,
/// ctype.ml:2616): the arguments of its name are children no longer
/// (`iter_row`, compiler/ml/btype.ml:229-241):
///
/// ```text
/// match (repr row.row_more).desc with
/// | Tvariant row -> iter_row f row
/// | Tvar _ | Tunivar _ | Tsubst _ | Tconstr _ | Tnil ->
///   Misc.may (fun (_, l) -> List.iter f l) row.row_name
/// ```
///
/// A lowering of the left row to level 1 leaves `y` at 2, and
/// `deep_occur` of `y` in it is false. In expression mode the same pair
/// links the left node to the right one and the right row, which gained
/// `#A`, is what a walk reaches: `y` is not reached either.
///
/// Reaches: R3f, R3h, R3r.
#[test]
#[ignore = "R3r build"]
fn a_named_row_on_the_left_loses_its_arguments_in_pattern_mode() {
    for mode in [Mode::Success, Mode::Explain] {
        for pattern in [true, false] {
            let (mut c, _) = pattern_checker(mode);
            let y = var(&mut c);
            let named = named_row(&mut c, 2, "A", Some(y));
            let other = named_row(&mut c, 2, "B", None);
            let result = if pattern {
                c.unify_pattern(2, true, true, named, other)
            } else {
                c.unify(named, other)
            };
            assert!(result.is_ok());
            assert_eq!(c.g.repr(named) == named, pattern);
            // In pattern mode the left node is read: its own tag, then
            // the one it gained; in expression mode the right node.
            let expected = if pattern { "[A B | ']" } else { "[B A | ']" };
            assert_eq!(shape(&mut c, named), expected);
            assert!(!c.deep_occur(y, named), "{pattern}");
            c.lower(named, 1).unwrap();
            let root = c.g.repr(named);
            assert_eq!(
                (c.g.nodes[root.0 as usize].level, c.g.nodes[y.0 as usize].level),
                (1, 2),
                "{pattern}"
            );
        }
    }
}
