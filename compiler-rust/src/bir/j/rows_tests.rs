//! Tests of the expression functions THREE_TREES 11.4, "T6x-e and T6x-f:
//! the fold reads where its rows are" adds to the interface, on J rows.
//! Each builds a small tree, calls the function, and compares the result
//! with what the code of trunk gives for the same tree: the same tree is
//! built in a second arena that starts equal, the trunk code runs there on
//! the rows themselves, and `Bir::dump` of the two must be equal.
use super::{E, Rows};
use crate::bir::lower::js::Js;
use crate::bir::lower::scope::Scope;
use crate::bir::{Bir, JsPayload, JsxHeader, NodeId, PropertySpan, StrId, VarId, View};
use crate::js_ir::arena::FieldPos;
use crate::lambda::LamLoc;
use crate::name::Name;

/// What both sides start from: an arena that counts JavaScript
/// occurrences, two variables and an interned name.
pub(in crate::bir::j) struct Unit {
    pub(in crate::bir::j) b: Bir,
    pub(in crate::bir::j) x: VarId,
    pub(in crate::bir::j) f: VarId,
    pub(in crate::bir::j) name: StrId,
}

pub(in crate::bir::j) fn unit() -> Unit {
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
/// variable `f`: made with `Js::jsx_element`, the callee given after the
/// operands, or as the row itself (`plain::node` over the callee, the tag
/// and the children: the row with the callee first). Returns the steps the
/// interface counted for the element.
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
        done(r.jsx_element(a, callee, mark, info, true));
        r.steps() - before
    } else {
        let mut values = vec![NodeId(0)];
        for _ in 0..=children {
            values.push(r.var(a, u.x).0);
        }
        values[0] = r.var(a, u.f).0;
        crate::bir::j::plain::node(a, View::JJsx { values: &values, info }, 1);
        u64::from(children) + 3
    }
}

/// The element `jsx_element` makes is the row with the callee first; its
/// steps are one, and one per operand with the callee counted, at 1,000
/// and at 10,000 children; operands pushed before the mark are still
/// there.
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
    // The operands below the mark are not moved.
    let mut u = unit();
    let mut r = Rows::default();
    let below = r.var(&mut u.b, u.x);
    let below_id = r.id(&u.b, Rows::of(&below));
    r.push(below);
    let info = u.b.js_info(JsPayload::Jsx(JsxHeader {
        spread: false,
        props: PropertySpan { start: 0, len: 0 },
        children: 0,
        key: false,
        multi: false,
        fragment: false,
    }));
    let mark = r.mark();
    let tag = r.var(&mut u.b, u.x);
    r.push(tag);
    let callee = r.var(&mut u.b, u.f);
    let callee_id = r.id(&u.b, Rows::of(&callee));
    let element = r.jsx_element(&mut u.b, callee, mark, info, false);
    assert_eq!(r.id(&u.b, r.operand(&u.b, Rows::of(&element), 0)), callee_id);
    let below = r.pop();
    assert_eq!(r.id(&u.b, Rows::of(&below)), below_id);
}

/// `x.name.name...`, `depth` reads deep, the leaf with a comment and every
/// third read with a location, and the reads alternating in tag bit.
pub(in crate::bir::j) fn chain(r: &mut Rows, u: &mut Unit, depth: u32) -> E {
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
/// on trunk, over the rows themselves: the reads pushed from the top, the
/// leaf copied with its cold data, then each read from the innermost out.
pub(in crate::bir::j) fn copy_on_rows(r: &mut Rows, a: &mut Bir, node: NodeId, made: &mut Vec<u32>) -> E {
    let mut spine = Vec::new();
    let mut at = node;
    while let View::JDot { object, .. } = a.view(at) {
        spine.push(at);
        at = object;
    }
    let mut copy = r.copy_leaf(a, at);
    r.copy_cold(a, at, &mut copy);
    made.push(copy.0.0);
    while let Some(read) = spine.pop() {
        let (name, position) = r.member_of(a, read).expect("a static read");
        let tag = r.aux(a, read) != 0;
        copy = r.dot(a, copy, name, position, tag);
        r.copy_cold(a, read, &mut copy);
        made.push(copy.0.0);
    }
    copy
}

/// `copy_members` makes the nodes trunk's copy makes, in the same order,
/// with the same cold data and the same steps, and reports their ids in
/// that order; its steps are one a node, from 1,000 to 10,000 reads; the
/// original keeps its references.
#[test]
fn a_copy_of_a_member_chain_is_the_copy_trunk_makes() {
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
        let expected = copy_on_rows(&mut t, &mut right.b, source.0, &mut theirs);
        assert_eq!(steps, t.steps() - before);
        assert_eq!(ours, theirs);
        assert_eq!(ours.len() as u32, depth + 1);
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

/// `Js::release` and the leaf constructors leave the operand stack alone:
/// operands pushed before them are popped after them, in order.
#[test]
fn a_release_and_a_leaf_leave_the_operand_stack_alone() {
    let mut u = unit();
    let mut r = Rows::default();
    let a = &mut u.b;
    let (first, second) = (r.var(a, u.x), r.var(a, u.f));
    let ids = [r.id(a, Rows::of(&first)), r.id(a, Rows::of(&second))];
    r.push(first);
    r.push(second);
    let chain_text = a.intern_text("text");
    let number = a.intern_const(crate::bir::Constant::Int(7));
    let leaves = [
        r.var(a, u.x),
        r.int_literal(a, 3),
        r.number(a, number),
        r.string(a, "s"),
        r.str(a, chain_text),
        r.boolean(a, true),
        r.null(a),
        r.undefined(a, true),
        r.json(a, chain_text),
        r.raw(a, chain_text, false),
    ];
    for leaf in leaves {
        r.release(a, leaf);
    }
    let (second, first) = (r.pop(), r.pop());
    assert_eq!([r.id(a, Rows::of(&first)), r.id(a, Rows::of(&second))], ids);
    assert_eq!(r.operands.len(), 0);
}

/// An imported module of the unit.
fn module(a: &mut Bir) -> crate::bir::ImportId {
    a.pools.j_modules.push(crate::js_ir::ModuleId {
        id: crate::ident::Ident::new("M", 0, crate::ident::IdentFlags::NONE),
        kind: crate::js_ir::Kind::Ml,
        dynamic_import: false,
    });
    crate::bir::ImportId(a.pools.j_modules.len() as u32 - 1)
}

/// What `Js::references` finds below `e`, sorted, and the nodes it read.
fn found(r: &mut Rows, a: &mut Bir, e: &E) -> (Vec<String>, u32) {
    let mut found = Vec::new();
    let before = r.steps();
    let read = r.references(a, e, |_, _, reference| found.push(format!("{reference:?}")));
    assert_eq!(r.steps(), before, "a reader counts no step");
    assert!(r.work.is_empty());
    found.sort();
    (found, read)
}

#[test]
fn the_references_below_an_expression_are_found_and_a_function_is_not_entered() {
    use crate::bir::lower::js::Found;
    use crate::bir::lower::js_stmt::JsStmt;
    let mut u = unit();
    let mut r = Rows::default();
    let a = &mut u.b;
    let m = module(a);
    // `f(x, M.name, function () { return x }, [f])`.
    let callee = r.var(a, u.f);
    let callee_id = r.id(a, Rows::of(&callee));
    let mark = r.mark();
    let x = r.var(a, u.x);
    let x_id = r.id(a, Rows::of(&x));
    r.push(x);
    let member = r.qualified(a, m, Some(u.name));
    let member_id = r.id(a, Rows::of(&member));
    r.push(member);
    let inner = r.var(a, u.x);
    let returned = r.return_(a, inner);
    let body = r.list(a, 1, std::iter::once(returned));
    let header = a.function_header(Default::default(), Default::default(), LamLoc::NONE);
    let function = r.function(a, header, body);
    r.push(function);
    let inner_mark = r.mark();
    let element = r.var(a, u.f);
    let element_id = r.id(a, Rows::of(&element));
    r.push(element);
    let array = r.array(a, inner_mark, 0);
    r.push(array);
    let info = a.js_info(JsPayload::Call(Default::default()));
    let call = r.call(a, callee, mark, info);
    let mut expected = [
        Found::Var { var: u.f, id: callee_id },
        Found::Var { var: u.x, id: x_id },
        Found::Module { module: m, id: member_id },
        Found::Function(header),
        Found::Var { var: u.f, id: element_id },
    ]
    .map(|reference| format!("{reference:?}"));
    expected.sort();
    // The call, its callee, three operands that are leaves or a literal,
    // the array and its element: the body of the function is not read.
    assert_eq!(found(&mut r, a, &call), (expected.to_vec(), 7));
    // The expression is the caller's still.
    assert_eq!(r.arity(a, Rows::of(&call)), 5);
    done(call);
}

/// The walk of `references` runs above what `Rows::work` holds, as the walk of
/// a returned value does (THREE_TREES 11.4, "T6r: the naming replay behind
/// the interface", decision 5).
#[test]
fn the_walk_of_references_leaves_what_the_work_stack_held() {
    let mut u = unit();
    let mut r = Rows::default();
    let a = &mut u.b;
    // `[f, x]`.
    let mark = r.mark();
    let first = r.var(a, u.f);
    r.push(first);
    let second = r.var(a, u.x);
    r.push(second);
    let array = r.array(a, mark, 0);
    r.work.push(NodeId(7));
    let mut references = 0;
    let read = r.references(a, &array, |_, _, _| references += 1);
    assert_eq!((references, read), (2, 3));
    assert_eq!(r.work, [NodeId(7)]);
    done(array);
}

#[test]
fn the_references_of_an_expression_cost_one_read_a_node_at_any_depth_and_width() {
    assert_eq!(std::mem::size_of::<crate::bir::lower::js::Found>(), 12);
    assert_eq!(std::mem::size_of::<crate::bir::lower::js::JsxHead>(), 1);
    let mut reads = Vec::new();
    for size in [1_000u32, 10_000] {
        let mut u = unit();
        let mut r = Rows::default();
        let a = &mut u.b;
        // `size` deep: `x, (x, (x, ...))`; `size` wide: `[x, x, ...]`.
        let build = |r: &mut Rows, a: &mut Bir| {
            let mut deep = r.var(a, u.x);
            for _ in 0..size {
                let first = r.var(a, u.x);
                deep = r.seq(a, first, deep);
            }
            let mark = r.mark();
            for _ in 0..size {
                let value = r.var(a, u.x);
                r.push(value);
            }
            let wide = r.array(a, mark, 0);
            r.seq(a, deep, wide)
        };
        let value = build(&mut r, a);
        let mut references = 0;
        let read = r.references(a, &value, |_, _, _| references += 1);
        assert_eq!(references, 2 * size + 1);
        // The sequences, their operands, the array and its elements.
        assert_eq!(read, 3 * size + 3);
        reads.push(read);
        let again = build(&mut r, a);
        let allocations = allocation_counter::measure(|| {
            r.references(a, &again, |_, _, _| {});
        });
        assert_eq!(allocations.count_total, 0, "{allocations:?}");
        done(value);
        done(again);
    }
    assert_eq!(reads[1] - 3, 10 * (reads[0] - 3));
}

#[test]
fn the_callee_and_the_tag_of_a_jsx_element_are_told_by_their_ids() {
    use crate::bir::lower::js::JsxHead;
    let mut u = unit();
    let mut r = Rows::default();
    let a = &mut u.b;
    let info = a.js_info(JsPayload::Jsx(JsxHeader {
        spread: false,
        props: PropertySpan { start: 0, len: 0 },
        children: 1,
        key: false,
        multi: false,
        fragment: false,
    }));
    let mark = r.mark();
    // The tag is a member of `x`: the climb from the reference ends at the
    // member, which is the operand.
    let base = r.var(a, u.x);
    let base_id = r.id(a, Rows::of(&base));
    let tag = r.dot(a, base, u.name, FieldPos::NONE, false);
    let tag_id = r.id(a, Rows::of(&tag));
    r.push(tag);
    let child = r.var(a, u.x);
    let child_id = r.id(a, Rows::of(&child));
    r.push(child);
    let callee = r.var(a, u.f);
    let callee_id = r.id(a, Rows::of(&callee));
    // Nothing holds the callee yet.
    assert_eq!(r.jsx_head(a, callee_id), None);
    let before = r.steps();
    let element = r.jsx_element(a, callee, mark, info, true);
    let counted = r.steps();
    assert_eq!(r.jsx_head(a, callee_id), Some((JsxHead::Callee, info)));
    assert_eq!(r.jsx_head(a, tag_id), Some((JsxHead::Tag, info)));
    assert_eq!(r.jsx_head(a, child_id), None, "an operand after the tag");
    assert_eq!(r.jsx_head(a, base_id), None, "below the tag: the owner is the member");
    assert_eq!(r.jsx_head(a, r.id(a, Rows::of(&element))), None);
    assert_eq!(r.steps(), counted, "a reader counts no step");
    assert!(counted > before);
    // The callee of a call is no JSX operand.
    let callee = r.var(a, u.f);
    let callee_id = r.id(a, Rows::of(&callee));
    let info = a.js_info(JsPayload::Call(Default::default()));
    let mark = r.mark();
    let call = r.call(a, callee, mark, info);
    assert_eq!(r.jsx_head(a, callee_id), None);
    done(element);
    done(call);
}
