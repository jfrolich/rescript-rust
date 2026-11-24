//! Tests of the functions the probe before T6x-f adds to the interface
//! (`PROBE-ADD n` in `bir/lower/js.rs` and `js_stmt.rs`), on J rows. Each
//! builds a small tree, calls the function, and compares the result with
//! what the by-id code of trunk gives for the same tree: the same tree is
//! built in a second arena that starts equal, the trunk code runs there,
//! and `Bir::dump` of the two must be equal.
use super::{E, Rows};
use crate::bir::lower::js::Js;
use crate::bir::lower::scope::Scope;
use crate::bir::{Bir, JsPayload, JsxHeader, NodeId, PropertySpan, StrId, VarId};
use crate::emit::row::Kind;
use crate::js_ir::arena::FieldPos;
use crate::lambda::LamLoc;
use crate::name::Name;

/// What both sides start from: an arena that counts JavaScript
/// occurrences, two variables and an interned name.
struct Unit {
    b: Bir,
    x: VarId,
    f: VarId,
    name: StrId,
}

fn unit() -> Unit {
    let mut b = Bir::default();
    b.begin_bulk();
    b.js_scope = Some(Scope::new(0));
    let x = b.new_var_id(Name::new("x"), 1);
    let f = b.new_var_id(Name::new("f"), 2);
    let name = b.intern_text("name");
    Unit { b, x, f, name }
}

/// A handle that is not attached: the comparison reads its node in the
/// arena's dump.
fn done(_: E) {}

/// A JSX element of `children` children (and its tag) whose callee is the
/// variable `f`, made with `Js::jsx_apart` (the callee given after the
/// operands) or, as trunk does, with `Js::jsx` (the callee pushed first).
/// Returns the steps the interface counted.
fn jsx(u: &mut Unit, children: u32, apart: bool) -> u64 {
    let mut r = Rows::default();
    let a = &mut u.b;
    let info = a.js_info(JsPayload::Jsx(JsxHeader {
        spread: false,
        props: PropertySpan { start: 0, len: 0 },
        children,
        key: false,
        multi: children > 1,
        fragment: false,
    }));
    let mark = r.mark();
    if apart {
        for _ in 0..=children {
            let value = r.var(a, u.x);
            r.push(value);
        }
        let callee = r.var(a, u.f);
        let before = r.steps();
        done(r.jsx_apart(a, callee, mark, info, true));
        r.steps() - before
    } else {
        // Trunk: the operands wait in a vector until the callee is made,
        // and the callee is pushed first.
        let mut values = Vec::new();
        for _ in 0..=children {
            values.push(r.var(a, u.x));
        }
        let callee = r.var(a, u.f);
        r.push(callee);
        for value in values {
            r.push(value);
        }
        let before = r.steps();
        done(r.jsx(a, mark, info, true));
        r.steps() - before
    }
}

/// PROBE-ADD 1: the element `jsx_apart` makes is the one `jsx` makes with
/// the callee pushed first, with the same steps; the steps grow by one an
/// operand from 1,000 to 10,000 children.
#[test]
fn a_jsx_element_with_its_callee_apart_is_the_element_jsx_makes() {
    let mut counts = [0; 2];
    for (at, children) in [1_000u32, 10_000].into_iter().enumerate() {
        let (mut left, mut right) = (unit(), unit());
        let apart = jsx(&mut left, children, true);
        let trunk = jsx(&mut right, children, false);
        assert_eq!(left.b.dump(), right.b.dump());
        assert_eq!(apart, trunk);
        counts[at] = apart;
    }
    // One step, the callee, the tag and the children: n + 3.
    assert_eq!(counts[1] - 3, 10 * (counts[0] - 3));
}

/// `x.name.name...`, `depth` reads deep, the leaf with a comment and every
/// third read with a location, and the reads alternating in tag bit.
fn chain(r: &mut Rows, u: &mut Unit, depth: u32) -> E {
    let a = &mut u.b;
    let mut value = r.var(a, u.x);
    r.comment(a, &mut value, u.name);
    for read in 0..depth {
        value = r.dot(a, value, u.name, FieldPos::NONE, read % 2 == 1);
        if read % 3 == 0 {
            r.locate(a, &mut value, LamLoc::NONE);
        }
    }
    value
}

/// The copy of `export.rs::copy_replacement` and `jsx.rs::duplicate_jsx_key`
/// on trunk, by id: the reads pushed from the top, the leaf copied with
/// its cold data, then each read from the innermost out.
fn copy_by_id(r: &mut Rows, a: &mut Bir, node: NodeId, made: &mut Vec<u32>) -> E {
    let mut spine = Vec::new();
    let mut at = <Rows as Js>::at(node);
    while r.kind(a, at) == Kind::Dot {
        spine.push(NodeId(r.id(a, at)));
        at = r.operand(a, at, 0);
    }
    let leaf = <Rows as Js>::at(NodeId(r.id(a, at)));
    let mut copy = r.copy_leaf(a, leaf);
    r.copy_cold(a, leaf, &mut copy);
    made.push(r.id(a, Rows::of(&copy)));
    while let Some(read) = spine.pop() {
        let read = <Rows as Js>::at(read);
        let (name, position) = r.member_of(a, read).expect("a static read");
        let tag = r.aux(a, read) != 0;
        copy = r.dot(a, copy, name, position, tag);
        r.copy_cold(a, read, &mut copy);
        made.push(r.id(a, Rows::of(&copy)));
    }
    copy
}

/// PROBE-ADD 2: `copy_members` makes the nodes trunk's copy makes, in the
/// same order, with the same cold data and the same steps, and reports
/// their ids in that order; its steps are one a node, from 1,000 to
/// 10,000 reads.
#[test]
fn a_copy_of_a_member_chain_is_the_copy_trunk_makes_by_id() {
    let mut counts = [0; 2];
    for (at, depth) in [1_000u32, 10_000].into_iter().enumerate() {
        let (mut left, mut right) = (unit(), unit());
        let (mut r, mut t) = (Rows::default(), Rows::default());
        let original = chain(&mut r, &mut left, depth);
        let (mut ours, mut theirs) = (Vec::new(), Vec::new());
        let before = r.steps();
        let copy = r.copy_members(&mut left.b, Rows::of(&original), |id| ours.push(id));
        let steps = r.steps() - before;
        let source = chain(&mut t, &mut right, depth);
        let before = t.steps();
        let expected = copy_by_id(&mut t, &mut right.b, Rows::of(&source), &mut theirs);
        assert_eq!(steps, t.steps() - before);
        assert_eq!(ours, theirs);
        assert_eq!(left.b.dump(), right.b.dump());
        assert_eq!(left.b.js_scope.as_ref().unwrap().uses[left.x.index()].remaining, 2);
        done(original);
        done(copy);
        done(source);
        done(expected);
        counts[at] = steps;
    }
    // One step the leaf and one each read: depth + 1.
    assert_eq!(counts[1] - 1, 10 * (counts[0] - 1));
}
