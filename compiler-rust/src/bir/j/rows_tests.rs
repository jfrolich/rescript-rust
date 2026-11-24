//! Tests of the functions the probe before T6x-f adds to the interface
//! (`PROBE-ADD n` in `bir/lower/js.rs` and `js_stmt.rs`), on J rows. Each
//! builds a small tree, calls the function, and compares the result with
//! what the by-id code of trunk gives for the same tree: the same tree is
//! built in a second arena that starts equal, the trunk code runs there,
//! and `Bir::dump` of the two must be equal.
use super::{E, Rows};
use crate::bir::lower::js::Js;
use crate::bir::lower::scope::Scope;
use crate::bir::{Bir, JsPayload, JsxHeader, PropertySpan, VarId};
use crate::name::Name;

/// What both sides start from: an arena that counts JavaScript
/// occurrences and two variables.
struct Unit {
    b: Bir,
    x: VarId,
    f: VarId,
}

fn unit() -> Unit {
    let mut b = Bir::default();
    b.begin_bulk();
    b.js_scope = Some(Scope::new(0));
    let x = b.new_var_id(Name::new("x"), 1);
    let f = b.new_var_id(Name::new("f"), 2);
    Unit { b, x, f }
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
