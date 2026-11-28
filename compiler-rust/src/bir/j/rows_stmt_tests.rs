//! Tests of the statement functions THREE_TREES 11.4, "T6x-e and T6x-f:
//! the fold reads where its rows are" adds to the interface, on J rows.
//! Each builds a small tree, calls the function, and compares the result
//! with what the code of trunk gives for the same tree, run on the rows
//! themselves in a second arena that starts equal.
use super::S;
use crate::bir::j::rows::tests::{Unit, chain, copy_on_rows, unit};
use crate::bir::j::rows::{E, Rows};
use crate::bir::lower::js::Js;
use crate::bir::lower::js_stmt::JsStmt;
use crate::bir::{Bir, JsPayload, NodeId, VarId, View};
use crate::name::Name;
use crate::emit::row::Kind;
use crate::lambda::LamLoc;
use crate::lambda::lam_compat::LetKind;

/// A block of `width` statements: `x;` but for statement `width / 2`,
/// `let f = x;`.
fn block(r: &mut Rows, u: &mut Unit, width: u32) -> S {
    let a = &mut u.b;
    let mut statements = Vec::new();
    for index in 0..width {
        let x = r.var(a, u.x);
        statements.push(if index == width / 2 {
            r.declare(a, LetKind::Strict, u.f, Some(x))
        } else {
            r.exp(a, x)
        });
    }
    let list = r.list(a, width, statements.into_iter());
    r.block_of(a, list)
}

/// The rows of the statements of `block`, read from the arena.
fn rows(a: &Bir, block: &S) -> Vec<NodeId> {
    let View::SBlock { statements } = a.view(block.0) else { panic!("a block") };
    statements.to_vec()
}

/// What the fold reads of a statement: its id, kind, variable and the id
/// of its value.
fn read(r: &Rows, a: &Bir, s: &S) -> (u32, Kind, Option<VarId>, Option<u32>) {
    (
        r.stmt_id(a, s),
        r.stmt_kind(a, s),
        r.declared(a, s),
        r.value_of(a, s).map(|value| r.id(a, value)),
    )
}

/// The length of a block is the number of its statements, at any width,
/// and the read counts no step.
#[test]
fn the_length_of_a_block_is_the_number_of_its_statements() {
    for width in [0, 5, 1_000] {
        let mut u = unit();
        let mut r = Rows::default();
        let b = block(&mut r, &mut u, width);
        let steps = r.steps();
        assert_eq!(r.block_len(&u.b, &b), width);
        assert_eq!(r.steps(), steps);
        r.release_stmt(&mut u.b, b);
    }
}

/// A statement of a block read by its index is the statement at that row,
/// the read counts no step and reads the same number of rows at 1,000 and
/// at 10,000 statements, whatever the index.
#[test]
fn a_statement_of_a_block_is_read_by_its_index_where_it_is() {
    let mut reads = Vec::new();
    for width in [1_000u32, 10_000] {
        let mut u = unit();
        let mut r = Rows::default();
        let b = block(&mut r, &mut u, width);
        let rows = rows(&u.b, &b);
        let steps = r.steps();
        for index in [0, width / 2, width - 1] {
            u.b.steps.set(0);
            let ours = r.with_block_stmt(&u.b, &b, index, |s| read(&r, &u.b, s));
            reads.push(u.b.steps.get());
            assert_eq!(ours, read(&r, &u.b, &S(rows[index as usize])));
        }
        assert_eq!(r.steps(), steps);
        r.release_stmt(&mut u.b, b);
    }
    // A declaration reads one row more than an expression statement (its
    // value's); the position and the width change nothing.
    assert_eq!(reads[0], reads[2]);
    assert_eq!(reads[..3], reads[3..]);
}

/// A statement of a block lent with the implementation and the pools is
/// changed in place as trunk changed it at its row, and the lend counts no
/// step.
#[test]
fn a_statement_of_a_block_is_lent_to_an_edit_where_it_is() {
    let (mut left, mut right) = (unit(), unit());
    let (mut r, mut t) = (Rows::default(), Rows::default());
    let mut ours = block(&mut r, &mut left, 5);
    let theirs = block(&mut t, &mut right, 5);
    let steps = r.steps();
    let kind = r.lend_block_stmt(&mut left.b, &mut ours, 3, |js, a, s| {
        js.locate_stmt(a, s, LamLoc::NONE);
        js.stmt_kind(a, s)
    });
    assert_eq!(r.steps(), steps);
    let mut statement = S(rows(&right.b, &theirs)[3]);
    t.locate_stmt(&mut right.b, &mut statement, LamLoc::NONE);
    assert_eq!(kind, t.stmt_kind(&right.b, &statement));
    assert_eq!(left.b.dump(), right.b.dump());
    r.release_stmt(&mut left.b, ours);
    t.release_stmt(&mut right.b, theirs);
}

/// A statement taken out of a block by its index and released leaves the
/// arena as trunk's `release_row` left it (`Bir::detach` and
/// `Bir::release` of the row); the statements after it keep their
/// indexes; the take counts one step; the block is released with its hole.
#[test]
fn a_statement_taken_out_of_a_block_leaves_a_hole() {
    let (mut left, mut right) = (unit(), unit());
    let (mut r, t) = (Rows::default(), Rows::default());
    let mut ours = block(&mut r, &mut left, 5);
    let theirs = block(&mut Rows::default(), &mut right, 5);
    let before = rows(&left.b, &ours);
    let steps = r.steps();
    let taken = r.take_block_stmt(&mut left.b, &mut ours, 2);
    assert_eq!(r.steps(), steps + 1);
    assert_eq!(taken.0, before[2]);
    r.release_stmt(&mut left.b, taken);
    let row = rows(&right.b, &theirs)[2];
    right.b.detach(row);
    right.b.release(row);
    assert_eq!(left.b.dump(), right.b.dump());
    assert_eq!(r.block_len(&left.b, &ours), 5);
    for index in [3, 4] {
        let id = r.with_block_stmt(&left.b, &ours, index, |s| r.stmt_id(&left.b, s));
        assert_eq!(id, before[index as usize].0);
    }
    r.release_stmt(&mut left.b, ours);
    right.b.release(NodeId(t.stmt_id(&right.b, &theirs)));
    assert_eq!(left.b.dump(), right.b.dump());
}

/// A hole is not read: the two readers and a second take panic on it.
#[test]
#[should_panic(expected = "a statement taken out of its block")]
fn a_hole_of_a_block_is_not_read() {
    let mut u = unit();
    let mut r = Rows::default();
    let mut b = block(&mut r, &mut u, 3);
    let taken = r.take_block_stmt(&mut u.b, &mut b, 1);
    r.release_stmt(&mut u.b, taken);
    r.with_block_stmt(&u.b, &b, 1, |_| ());
}

/// `let t = x.name.name...`, `depth` reads deep, for a fresh variable `t`.
fn declaration(r: &mut Rows, u: &mut Unit, depth: u32) -> S {
    let value = chain(r, u, depth);
    let t = u.b.new_var_id(Name::new("t"), 3);
    r.declare(&mut u.b, LetKind::Strict, t, Some(value))
}

/// The value of a statement the caller holds is copied with the functions
/// of the expression half: the reference `value_of` gives borrows the
/// statement and not the pools. The copy is the one trunk made of the
/// initialiser at its row, and of a leaf without cold data `copy_leaf`.
#[test]
fn the_value_of_a_statement_in_hand_is_copied_without_a_function_of_its_own() {
    let (mut left, mut right) = (unit(), unit());
    let (mut r, mut t) = (Rows::default(), Rows::default());
    let ours = declaration(&mut r, &mut left, 7);
    let theirs = declaration(&mut t, &mut right, 7);
    let (mut made, mut expected) = (Vec::new(), Vec::new());
    let value = r.value_of(&left.b, &ours).expect("an initialiser");
    let copy = r.copy_members(&mut left.b, value, |id| made.push(id));
    let initialiser = t.value_of(&right.b, &theirs).expect("an initialiser");
    let trunk = copy_on_rows(&mut t, &mut right.b, initialiser, &mut expected);
    assert_eq!(made, expected);
    assert_eq!(left.b.dump(), right.b.dump());
    r.release(&mut left.b, copy);
    t.release(&mut right.b, trunk);
    let (ours, theirs) = (declaration(&mut r, &mut left, 0), declaration(&mut t, &mut right, 0));
    let value = r.value_of(&left.b, &ours).expect("an initialiser");
    let copy = r.copy_leaf(&mut left.b, value);
    let initialiser = t.value_of(&right.b, &theirs).expect("an initialiser");
    let trunk = t.copy_leaf(&mut right.b, initialiser);
    assert_eq!(left.b.dump(), right.b.dump());
    r.release(&mut left.b, copy);
    t.release(&mut right.b, trunk);
}

/// `f(x, x, ..)` with `uses` references to `x` as arguments, after `pad`
/// arguments that refer to `f`, as an expression statement.
fn call(r: &mut Rows, u: &mut Unit, pad: u32, uses: u32) -> S {
    let a = &mut u.b;
    let info = a.js_info(JsPayload::Call(Default::default()));
    let callee = r.var(a, u.f);
    let mark = r.mark();
    for _ in 0..pad {
        let value = r.var(a, u.f);
        r.push(value);
    }
    for _ in 0..uses {
        let value = r.var(a, u.x);
        r.push(value);
    }
    let call = r.call(a, callee, mark, info);
    r.exp(a, call)
}

/// The references a substitution finds, replaced by trunk's code: each
/// site of `x` that stands in the statement, from the last recorded, is
/// written over with a fresh reference to `f` (`Bir::replace`).
fn replace_at_sites(r: &mut Rows, u: &mut Unit) -> u32 {
    let scope = u.b.js_scope.as_ref().expect("sites");
    let mut at = scope.site_heads[u.x.index()];
    let mut nodes = Vec::new();
    while at != 0 {
        let site = scope.sites[at as usize - 1];
        at = site.next;
        if site.node != NodeId(u32::MAX) {
            nodes.push(site.node);
        }
    }
    for &node in &nodes {
        let copy: E = r.var(&mut u.b, u.f);
        u.b.replace(node, copy.0);
    }
    nodes.len() as u32
}

/// `substitute` replaces the references trunk replaced at their sites and
/// leaves the same arena; it returns their number; its steps are one a
/// node read, linear from 1,000 to 10,000 references, and it stops at the
/// last reference it was asked for.
#[test]
fn the_references_to_a_variable_in_a_statement_are_replaced_where_they_are() {
    let mut counts = [0; 2];
    for (at, uses) in [1_000u32, 10_000].into_iter().enumerate() {
        let (mut left, mut right) = (unit(), unit());
        let (mut r, mut t) = (Rows::default(), Rows::default());
        let mut ours = call(&mut r, &mut left, 3, uses);
        let theirs = call(&mut t, &mut right, 3, uses);
        let id = r.stmt_id(&left.b, &ours);
        let before = r.steps();
        let f = left.f;
        let replaced = r.substitute(&mut left.b, &mut ours, left.x, uses, |js, a| js.var(a, f));
        counts[at] = r.steps() - before;
        assert_eq!(replaced, uses);
        assert_eq!(r.stmt_id(&left.b, &ours), id);
        assert_eq!(replace_at_sites(&mut t, &mut right), uses);
        assert_eq!(left.b.dump(), right.b.dump());
        assert_eq!(left.b.js_scope.as_ref().unwrap().uses[left.x.index()].remaining, 0);
        r.release_stmt(&mut left.b, ours);
        t.release_stmt(&mut right.b, theirs);
    }
    // The statement and the call, then per reference its node and the
    // reference `make` builds; the callee and the padding are not reached.
    assert_eq!(counts[1] - 2, 10 * (counts[0] - 2));
    // Asked for fewer than there are, it stops there and leaves the rest.
    let mut u = unit();
    let mut r = Rows::default();
    let mut s = call(&mut r, &mut u, 0, 5);
    let f = u.f;
    assert_eq!(r.substitute(&mut u.b, &mut s, u.x, 2, |js, a| js.var(a, f)), 2);
    assert_eq!(u.b.js_scope.as_ref().unwrap().uses[u.x.index()].remaining, 3);
    // Asked for none, it reads nothing.
    let before = r.steps();
    assert_eq!(r.substitute(&mut u.b, &mut s, u.x, 0, |js, a| js.var(a, f)), 0);
    assert_eq!(r.steps(), before);
    r.release_stmt(&mut u.b, s);
}

/// `f(x, x.name, function () { return f(x, x); }, x);`: references to `x`
/// at two depths and inside a function literal. The references inside the
/// literal are built first, so the order of the sites (newest first: the
/// last argument, the object of the read, the first argument, then the
/// two of the literal) is not the order of the walk (the last argument,
/// the two of the literal, the object, the first argument).
fn nested(r: &mut Rows, u: &mut Unit) -> S {
    let a = &mut u.b;
    let header = a.function_header(crate::bir::VarSpan { start: 0, len: 0 }, Default::default(), LamLoc::NONE);
    let info = a.js_info(JsPayload::Call(Default::default()));
    let callee = r.var(a, u.f);
    let mark = r.mark();
    for _ in 0..2 {
        let value = r.var(a, u.x);
        r.push(value);
    }
    let inner = r.call(a, callee, mark, info);
    let returned = r.return_(a, inner);
    let body = r.list(a, 1, std::iter::once(returned));
    let function = r.function(a, header, body);
    let info = a.js_info(JsPayload::Call(Default::default()));
    let callee = r.var(a, u.f);
    let mark = r.mark();
    let first = r.var(a, u.x);
    r.push(first);
    let object = r.var(a, u.x);
    let read = r.dot(a, object, u.name, crate::js_ir::arena::FieldPos::NONE, false);
    r.push(read);
    r.push(function);
    let last = r.var(a, u.x);
    r.push(last);
    let call = r.call(a, callee, mark, info);
    r.exp(a, call)
}

/// THREE_TREES 11.4, "T6x-e and T6x-f: the fold reads where its rows are",
/// decision 16: where the order of the walk and the order of the sites
/// differ, `substitute` still leaves the arena trunk's replacement at the
/// sites leaves: every node at the same id, the same counts. What differs
/// is the site each copy got (a copy is a new `Var`, recorded when it is
/// made, so the copies' sites are in the order they were made): the two
/// site tables hold the same nodes for `f`, in another order.
#[test]
fn a_substitution_at_two_depths_and_inside_a_function_is_trunks_but_for_the_order_of_the_new_sites() {
    let (mut left, mut right) = (unit(), unit());
    let (mut r, mut t) = (Rows::default(), Rows::default());
    let mut ours = nested(&mut r, &mut left);
    let theirs = nested(&mut t, &mut right);
    let f = left.f;
    assert_eq!(r.substitute(&mut left.b, &mut ours, left.x, 5, |js, a| js.var(a, f)), 5);
    assert_eq!(replace_at_sites(&mut t, &mut right), 5);
    assert_eq!(left.b.dump(), right.b.dump());
    let sites = |u: &Unit, var: VarId| {
        let scope = u.b.js_scope.as_ref().expect("sites");
        let (mut at, mut nodes) = (scope.site_heads[var.index()], Vec::new());
        while at != 0 {
            let site = scope.sites[at as usize - 1];
            at = site.next;
            if site.node != NodeId(u32::MAX) {
                nodes.push(site.node);
            }
        }
        nodes
    };
    assert!(sites(&left, left.x).is_empty() && sites(&right, right.x).is_empty());
    let (ours_f, mut theirs_f) = (sites(&left, left.f), sites(&right, right.f));
    assert_eq!(ours_f.len(), 7);
    // The same nodes; the five copies in the order each side made them.
    assert_ne!(ours_f, theirs_f, "the walk and the sites agree on this shape: the test shows nothing");
    let mut sorted = ours_f.clone();
    sorted.sort();
    theirs_f.sort();
    assert_eq!(sorted, theirs_f);
    let scope = |u: &Unit| u.b.js_scope.as_ref().unwrap().uses[u.f.index()];
    assert_eq!(scope(&left), scope(&right));
    r.release_stmt(&mut left.b, ours);
    t.release_stmt(&mut right.b, theirs);
}

/// A call that is asked for fewer references than the statement holds
/// stops at the last it was asked for: its steps depend on what it was
/// asked for and not on what is left. With `asked` of `uses` references
/// in a flat call the walk reads the statement, the call and `asked`
/// arguments, and `make` builds `asked` references: asked for 100 it costs
/// the same with 1,000 and with 10,000 references, and each further
/// reference asked for costs two steps.
#[test]
fn a_substitution_that_stops_with_references_left_reads_no_further() {
    let steps = |uses: u32, asked: u32| {
        let mut u = unit();
        let mut r = Rows::default();
        let mut s = call(&mut r, &mut u, 3, uses);
        let f = u.f;
        let before = r.steps();
        assert_eq!(r.substitute(&mut u.b, &mut s, u.x, asked, |js, a| js.var(a, f)), asked);
        let steps = r.steps() - before;
        assert_eq!(u.b.js_scope.as_ref().unwrap().uses[u.x.index()].remaining, uses - asked);
        r.release_stmt(&mut u.b, s);
        steps
    };
    assert_eq!(steps(10_000, 100), steps(1_000, 100));
    assert_eq!(steps(10_000, 1_000) - steps(10_000, 100), 2 * 900);
    assert_eq!(steps(10_000, 10_000) - steps(10_000, 1_000), 2 * 9_000);
}

/// The stated cost: one call reads the nodes of the statement up to its
/// last reference, so a reference behind n other nodes costs n, at 1,000
/// and at 10,000, and a variable that is not there costs the statement.
#[test]
fn a_substitution_reads_the_statement_up_to_the_last_reference() {
    let mut counts = [0; 2];
    for (at, pad) in [1_000u32, 10_000].into_iter().enumerate() {
        let mut u = unit();
        let mut r = Rows::default();
        // The walk reads the arguments from the last: the one reference
        // comes first in the call and is read last.
        let a = &mut u.b;
        let callee = r.var(a, u.f);
        let mark = r.mark();
        let value = r.var(a, u.x);
        r.push(value);
        for _ in 0..pad {
            let value = r.var(a, u.f);
            r.push(value);
        }
        let info = a.js_info(JsPayload::Call(Default::default()));
        let value = r.call(a, callee, mark, info);
        let mut s = r.exp(a, value);
        let f = u.f;
        let before = r.steps();
        assert_eq!(r.substitute(&mut u.b, &mut s, u.x, 1, |js, a| js.var(a, f)), 1);
        counts[at] = r.steps() - before;
        r.release_stmt(&mut u.b, s);
    }
    assert_eq!(counts[1] - counts[0], 9_000);
}

/// What replaces a reference is a chain the implementation copies with its
/// own work stack while the walk's is in use.
#[test]
fn a_substitution_by_a_copied_chain_keeps_the_walk() {
    let mut u = unit();
    let mut r = Rows::default();
    let master = chain(&mut r, &mut u, 4);
    let mut s = call(&mut r, &mut u, 2, 3);
    let replaced = r.substitute(&mut u.b, &mut s, u.x, 3, |js, a| js.copy_members(a, Rows::of(&master), |_| {}));
    assert_eq!(replaced, 3);
    // The master's own leaf is the one reference to `x` left.
    assert_eq!(u.b.js_scope.as_ref().unwrap().uses[u.x.index()].remaining, 4);
    let value = r.value_of(&u.b, &s).expect("the call");
    for index in 3..6 {
        assert_eq!(r.kind(&u.b, r.operand(&u.b, value, index)), Kind::Dot);
    }
    r.release_stmt(&mut u.b, s);
    r.release(&mut u.b, master);
}

/// The alias of a declaration is read through its id: the variable of an
/// initialiser that is a reference, and nothing for any other statement.
#[test]
fn the_variable_a_declaration_aliases_is_read_through_its_id() {
    let mut u = unit();
    let mut r = Rows::default();
    let alias = declaration(&mut r, &mut u, 0);
    let member = declaration(&mut r, &mut u, 1);
    let t = u.b.new_var_id(Name::new("t"), 4);
    let bare = r.declare(&mut u.b, LetKind::Strict, t, None);
    let x = r.var(&mut u.b, u.x);
    let statement = r.exp(&mut u.b, x);
    assert_eq!(r.alias_at(&u.b, r.stmt_id(&u.b, &alias)), Some(u.x));
    for other in [&member, &bare, &statement] {
        assert_eq!(r.alias_at(&u.b, r.stmt_id(&u.b, other)), None);
    }
}

/// `return value` as the one statement of a list in flight, `value` a row
/// built on the arena.
fn returning(r: &mut Rows, u: &mut Unit, value: NodeId) -> crate::bir::ListId {
    let statement = r.return_(&mut u.b, Rows::from_node(value));
    r.list(&mut u.b, 1, std::iter::once(statement))
}

/// A call of `callee` without an argument, as a row.
fn call_of(u: &mut Unit, callee: VarId) -> NodeId {
    let info = u.b.js_info(JsPayload::Call(Default::default()));
    let callee = u.b.new_node(View::Var { var: callee }, 0);
    u.b.new_node(View::JCall { callee, args: &[], info }, 0)
}

/// The calls `JsStmt::return_calls` gives for `value`, and the nodes it
/// read.
fn calls(r: &mut Rows, u: &mut Unit, value: NodeId, last: bool) -> (Vec<(VarId, u32)>, u32) {
    let list = returning(r, u, value);
    let mut found = Vec::new();
    let before = r.steps();
    let read = r.return_calls(&mut u.b, list, 0, last, |_, var, call| found.push((var, call)));
    assert_eq!(r.steps(), before, "a reader counts no step");
    assert!(r.work.is_empty());
    (found, read)
}

#[test]
fn the_calls_a_return_ends_in_are_read_through_conditionals_and_sequences() {
    let mut u = unit();
    let (f, x) = (u.f, u.x);
    let mut r = Rows::default();
    // `return f()`: a site only when the `return` ends its list.
    let call = call_of(&mut u, f);
    assert_eq!(calls(&mut r, &mut u, call, true), (vec![(u.f, call.0)], 1));
    let call = call_of(&mut u, f);
    assert_eq!(calls(&mut r, &mut u, call, false), (vec![], 1));
    // `return (x, f())`: the last operand, as its sequence.
    let (first, second) = (u.b.new_node(View::Var { var: u.x }, 0), call_of(&mut u, f));
    let value = u.b.new_node(View::JSeq { first, second }, 0);
    assert_eq!(calls(&mut r, &mut u, value, true), (vec![(u.f, second.0)], 2));
    let (first, second) = (u.b.new_node(View::Var { var: u.x }, 0), call_of(&mut u, f));
    let value = u.b.new_node(View::JSeq { first, second }, 0);
    assert_eq!(calls(&mut r, &mut u, value, false), (vec![], 2));
    // `return x ? f() : (x, x())`: both branches whatever `last` is, the
    // then-branch first; the test is not read.
    for last in [true, false] {
        let condition = call_of(&mut u, x);
        let then_ = call_of(&mut u, f);
        let (first, second) = (call_of(&mut u, f), call_of(&mut u, x));
        let else_ = u.b.new_node(View::JSeq { first, second }, 0);
        let value = u.b.new_node(View::JCond { condition, then_, else_ }, 0);
        assert_eq!(calls(&mut r, &mut u, value, last), (vec![(u.f, then_.0), (u.x, second.0)], 4));
    }
    // A call of something that is no variable, and a value that is no
    // call, give nothing.
    let callee = call_of(&mut u, f);
    let info = u.b.js_info(JsPayload::Call(Default::default()));
    let value = u.b.new_node(View::JCall { callee, args: &[], info }, 0);
    assert_eq!(calls(&mut r, &mut u, value, true), (vec![], 1));
    let value = u.b.new_node(View::Var { var: u.x }, 0);
    assert_eq!(calls(&mut r, &mut u, value, true), (vec![], 1));
}

/// `x ? (x ? ... f() ... : x()) : x()`, the conditionals nested `depth`
/// deep in their then-branches.
fn nested_conditionals(u: &mut Unit, depth: u32) -> NodeId {
    let (f, x) = (u.f, u.x);
    let mut value = call_of(u, f);
    for _ in 0..depth {
        let condition = u.b.new_node(View::Var { var: u.x }, 0);
        let else_ = call_of(u, x);
        value = u.b.new_node(View::JCond { condition, then_: value, else_ }, 0);
    }
    value
}

#[test]
fn the_calls_of_a_return_cost_two_reads_a_conditional_at_any_depth() {
    let mut reads = Vec::new();
    for depth in [1_000, 10_000] {
        let mut u = unit();
        let mut r = Rows::default();
        let value = nested_conditionals(&mut u, depth);
        let (found, read) = calls(&mut r, &mut u, value, false);
        // Each conditional and its else-branch, and the innermost call.
        assert_eq!(read, 2 * depth + 1);
        assert_eq!(found.len() as u32, depth + 1);
        assert_eq!(found[0].0, u.f, "the innermost then-branch is read first");
        reads.push(read);
        // A second walk of a value as deep allocates nothing.
        let again = nested_conditionals(&mut u, depth);
        let list = returning(&mut r, &mut u, again);
        let allocations = allocation_counter::measure(|| {
            r.return_calls(&mut u.b, list, 0, false, |_, _, _| {});
        });
        assert_eq!(allocations.count_total, 0, "{allocations:?}");
    }
    assert_eq!(reads[1] - 1, 10 * (reads[0] - 1));
}

#[test]
fn the_walk_of_a_return_leaves_what_the_work_stack_held() {
    let mut u = unit();
    let mut r = Rows::default();
    let value = nested_conditionals(&mut u, 3);
    let list = returning(&mut r, &mut u, value);
    r.work.push(NodeId(7));
    let mut found = 0;
    r.return_calls(&mut u.b, list, 0, true, |_, _, _| found += 1);
    assert_eq!(found, 4);
    assert_eq!(r.work, [NodeId(7)]);
}

#[test]
#[should_panic(expected = "not a return statement")]
fn the_calls_of_a_statement_that_is_no_return_are_not_read() {
    let mut u = unit();
    let mut r = Rows::default();
    let x = r.var(&mut u.b, u.x);
    let statement = r.exp(&mut u.b, x);
    let list = r.list(&mut u.b, 1, std::iter::once(statement));
    r.return_calls(&mut u.b, list, 0, true, |_, _, _| {});
}

/// The statements of THREE_TREES 11.4, "T6r: the naming replay behind the
/// interface", slice T6r-c: what the replay reads of a statement in hand
/// and takes out of it.
mod replay {
    use super::*;
    use crate::bir::lower::js_stmt::Range;

    /// The list of one `x;`.
    pub(super) fn body(r: &mut Rows, u: &mut Unit) -> crate::bir::ListId {
        let x = r.var(&mut u.b, u.x);
        let statement = r.exp(&mut u.b, x);
        r.list(&mut u.b, 1, std::iter::once(statement))
    }

    /// A variable nothing binds yet.
    pub(super) fn fresh(u: &mut Unit) -> VarId {
        let order = u.b.vars.len() as u32 + 1;
        u.b.new_var_id(Name::new("v"), order)
    }

    /// `for (let var = x; var <= end; ++var) { x; }`, or without the first
    /// value.
    pub(super) fn range(r: &mut Rows, u: &mut Unit, var: VarId, init: bool, end: E) -> S {
        let init = init.then(|| r.var(&mut u.b, u.x));
        let list = body(r, u);
        r.for_range(&mut u.b, var, Range { init, end, direction: 0 }, list, None)
    }

    #[test]
    fn the_binder_of_a_statement_is_the_variable_it_binds() {
        let mut u = unit();
        let mut r = Rows::default();
        let steps = |r: &Rows| r.steps();
        // A declaration, with and without a value.
        let x = r.var(&mut u.b, u.x);
        let declaration = r.declare(&mut u.b, LetKind::Strict, u.f, Some(x));
        let var = fresh(&mut u);
        let bare = r.declare(&mut u.b, LetKind::Variable, var, None);
        let before = steps(&r);
        assert_eq!(r.binder(&u.b, &declaration), Some(u.f));
        assert_eq!(r.binder(&u.b, &bare), Some(var));
        // A range loop names its variable with and without a first value.
        for init in [true, false] {
            let (var, end) = (fresh(&mut u), r.var(&mut u.b, u.x));
            let looped = range(&mut r, &mut u, var, init, end);
            assert_eq!(r.binder(&u.b, &looped), Some(var));
        }
        // A loop over an iterable, awaited or not.
        for awaited in [false, true] {
            let iterable = r.var(&mut u.b, u.x);
            let (var, list) = (fresh(&mut u), body(&mut r, &mut u));
            let looped = r.for_of(&mut u.b, var, iterable, list, None, awaited);
            assert_eq!(r.binder(&u.b, &looped), Some(var));
        }
        // A `try`: the exception of its handler, nothing without one.
        let (tried, handler, finaliser) = (body(&mut r, &mut u), body(&mut r, &mut u), body(&mut r, &mut u));
        let var = fresh(&mut u);
        let caught = r.try_(&mut u.b, tried, Some((var, handler)), Some(finaliser));
        assert_eq!(r.binder(&u.b, &caught), Some(var));
        let (tried, finaliser) = (body(&mut r, &mut u), body(&mut r, &mut u));
        let uncaught = r.try_(&mut u.b, tried, None, Some(finaliser));
        assert_eq!(r.binder(&u.b, &uncaught), None);
        // The statements only the bridge makes: a rest declaration binds,
        // a range loop over an existing variable does not.
        let info = u.b.js_info(JsPayload::Rest(crate::bir::RestSpan { start: 0, len: 0 }));
        let value = u.b.new_node(View::Var { var: u.x }, 0);
        let var = fresh(&mut u);
        let rest = Rows::stmt_from_node(u.b.new_node(View::SRest { var, value, info }, 0));
        assert_eq!(r.binder(&u.b, &rest), Some(var));
        let variable = u.b.new_node(View::Var { var: u.f }, 0);
        let end = u.b.new_node(View::JNull, 0);
        let list = body(&mut r, &mut u);
        let block = Rows::stmt_node(r.block_of(&mut u.b, list));
        let existing =
            Rows::stmt_from_node(u.b.new_node(View::SForRangeExisting { variable, parts: &[end, block], label: None }, 0));
        assert_eq!(r.binder(&u.b, &existing), None);
        // Any other statement binds nothing, and no read counts a step.
        let before_other = steps(&r);
        let x = r.var(&mut u.b, u.x);
        let effect = r.exp(&mut u.b, x);
        let assigned = {
            let x = r.var(&mut u.b, u.x);
            r.assign(&mut u.b, u.f, x)
        };
        let after_other = steps(&r);
        assert_eq!(r.binder(&u.b, &effect), None);
        assert_eq!(r.binder(&u.b, &assigned), None);
        assert_eq!(steps(&r), after_other);
        assert!(before_other > before);
    }

    #[test]
    fn the_status_of_a_declaration_is_read_apart_from_its_kind() {
        use crate::js_ir::op::UsedStats;
        let mut u = unit();
        let mut r = Rows::default();
        // The interface writes every declaration as used, with a value or
        // without one.
        let x = r.var(&mut u.b, u.x);
        let declaration = r.declare(&mut u.b, LetKind::Alias, u.f, Some(x));
        let var = fresh(&mut u);
        let bare = r.declare(&mut u.b, LetKind::Variable, var, None);
        let steps = r.steps();
        assert_eq!(r.status(&u.b, &declaration), UsedStats::Used as u8);
        assert_eq!(r.stmt_aux(&u.b, &declaration), LetKind::Alias as u8);
        assert_eq!(r.status(&u.b, &bare), UsedStats::Used as u8);
        // A status a pass wrote is read whatever the kind is, and a rest
        // declaration's descriptor bit is not part of it.
        for (kind, status) in [(LetKind::Strict, UsedStats::DeadPure), (LetKind::Variable, UsedStats::DeadNonPure)] {
            let var = fresh(&mut u);
            let value = u.b.new_node(View::JNull, 0);
            let aux = kind as u16 | (status as u16) << 2;
            let dead = Rows::stmt_from_node(u.b.new_node(View::SDecl { var, value: Some(value) }, aux));
            assert_eq!(r.status(&u.b, &dead), status as u8);
            assert_eq!(r.stmt_aux(&u.b, &dead), kind as u8);
        }
        let info = u.b.js_info(JsPayload::Rest(crate::bir::RestSpan { start: 0, len: 0 }));
        let value = u.b.new_node(View::Var { var: u.x }, 0);
        let var = fresh(&mut u);
        let aux = (1 << 15) | (UsedStats::DeadNonPure as u16) << 2 | LetKind::Strict as u16;
        let rest = Rows::stmt_from_node(u.b.new_node(View::SRest { var, value, info }, aux));
        assert_eq!(r.status(&u.b, &rest), UsedStats::DeadNonPure as u8);
        assert_eq!(r.steps(), steps, "a reader counts no step");
    }

    #[test]
    #[should_panic(expected = "not a declaration")]
    fn the_status_of_a_statement_that_declares_nothing_is_not_read() {
        let mut u = unit();
        let mut r = Rows::default();
        let x = r.var(&mut u.b, u.x);
        let statement = r.exp(&mut u.b, x);
        r.status(&u.b, &statement);
    }

    #[test]
    fn a_range_loop_gives_its_variable_and_the_kind_of_its_bound() {
        let mut u = unit();
        let mut r = Rows::default();
        // The bound is read with a first value before it and without one.
        for init in [true, false] {
            let (var, end) = (fresh(&mut u), r.int_literal(&mut u.b, 3));
            let looped = range(&mut r, &mut u, var, init, end);
            let steps = r.steps();
            assert_eq!(r.range_of(&u.b, &looped), Some((Some(var), Kind::Number)));
            assert_eq!(r.steps(), steps, "a reader counts no step");
        }
        let (var, end) = (fresh(&mut u), r.var(&mut u.b, u.x));
        let looped = range(&mut r, &mut u, var, true, end);
        assert_eq!(r.range_of(&u.b, &looped), Some((Some(var), Kind::Var)));
        // A bound that is neither: the kind says so, the bound is not
        // handed out.
        let (var, object) = (fresh(&mut u), r.var(&mut u.b, u.x));
        let end = r.dot(&mut u.b, object, u.name, crate::js_ir::arena::FieldPos::NONE, false);
        let looped = range(&mut r, &mut u, var, false, end);
        assert_eq!(r.range_of(&u.b, &looped), Some((Some(var), Kind::Dot)));
        // A loop over an existing variable (the bridge's): the variable of
        // its target when that is a reference.
        for reference in [true, false] {
            let variable = if reference { u.b.new_node(View::Var { var: u.f }, 0) } else { u.b.new_node(View::JNull, 0) };
            let end = u.b.new_node(View::JNull, 0);
            let list = body(&mut r, &mut u);
            let block = Rows::stmt_node(r.block_of(&mut u.b, list));
            let existing =
                Rows::stmt_from_node(u.b.new_node(View::SForRangeExisting { variable, parts: &[end, block], label: None }, 0));
            assert_eq!(r.range_of(&u.b, &existing), Some((reference.then_some(u.f), Kind::Null)));
        }
        // No other statement is a range loop.
        let (var, iterable, list) = (fresh(&mut u), r.var(&mut u.b, u.x), body(&mut r, &mut u));
        let looped = r.for_of(&mut u.b, var, iterable, list, None, false);
        assert_eq!(r.range_of(&u.b, &looped), None);
        let x = r.var(&mut u.b, u.x);
        let statement = r.exp(&mut u.b, x);
        assert_eq!(r.range_of(&u.b, &statement), None);
    }

    /// `switch (x) { ...actions }` of `actions` actions, each the block of
    /// one `x;`.
    pub(super) fn switch(r: &mut Rows, u: &mut Unit, actions: u32) -> S {
        let mut blocks = Vec::new();
        for _ in 0..actions {
            let list = body(r, u);
            blocks.push(r.block_of(&mut u.b, list));
        }
        let list = r.list(&mut u.b, actions, blocks.into_iter());
        let header = u.b.switch_record(crate::bir::SwitchRecord {
            constants: 0,
            keys: crate::bir::KeySpan { start: 0, len: 0 },
            clauses: crate::bir::ClauseSpan { start: 0, len: 0 },
            has_default: false,
            consts_full: false,
            blocks_full: false,
            dispatch: crate::lambda::SwitchDispatch::Direct,
        });
        let scrutinee = r.var(&mut u.b, u.x);
        r.switch(&mut u.b, scrutinee, list, header, false)
    }

    /// `try { x; } catch (var) { x; } finally { x; }`, with the parts
    /// asked for.
    pub(super) fn tried(r: &mut Rows, u: &mut Unit, handler: bool, finaliser: bool) -> S {
        let list = body(r, u);
        let handler = handler.then(|| (fresh(u), body(r, u)));
        let finaliser = finaliser.then(|| body(r, u));
        r.try_(&mut u.b, list, handler, finaliser)
    }

    #[test]
    fn a_statement_says_how_many_lists_it_holds() {
        let mut u = unit();
        let mut r = Rows::default();
        let mut counts = Vec::new();
        let mut count = |r: &Rows, u: &Unit, s: &S| {
            let steps = r.steps();
            counts.push(r.bodies(&u.b, s));
            assert_eq!(r.steps(), steps, "a reader counts no step");
        };
        // A block, explicit or not, of any width.
        let list = body(&mut r, &mut u);
        let plain = r.block_of(&mut u.b, list);
        count(&r, &u, &plain);
        let list = r.list(&mut u.b, 0, std::iter::empty());
        let explicit = r.explicit_block(&mut u.b, list);
        count(&r, &u, &explicit);
        // An `if`: both lists as the interface builds it, one without an
        // else-block (the rules make that one).
        let (test, yes, no) = (r.var(&mut u.b, u.x), body(&mut r, &mut u), body(&mut r, &mut u));
        let both = r.if_plain(&mut u.b, test, yes, no);
        count(&r, &u, &both);
        let list = body(&mut r, &mut u);
        let then_ = Rows::stmt_node(r.block_of(&mut u.b, list));
        let condition = u.b.new_node(View::Var { var: u.x }, 0);
        let guard = Rows::stmt_from_node(u.b.new_node(View::SIf { condition, then_, else_: None }, 0));
        count(&r, &u, &guard);
        // The loops.
        let (condition, list) = (r.var(&mut u.b, u.x), body(&mut r, &mut u));
        let looped = r.while_(&mut u.b, condition, list, None);
        count(&r, &u, &looped);
        for init in [true, false] {
            let (var, end) = (fresh(&mut u), r.var(&mut u.b, u.x));
            let looped = range(&mut r, &mut u, var, init, end);
            count(&r, &u, &looped);
        }
        let (var, iterable, list) = (fresh(&mut u), r.var(&mut u.b, u.x), body(&mut r, &mut u));
        let looped = r.for_of(&mut u.b, var, iterable, list, None, true);
        count(&r, &u, &looped);
        // A `try`: the body, and the handler and the finaliser it has.
        for (handler, finaliser) in [(true, false), (false, true), (true, true)] {
            let statement = tried(&mut r, &mut u, handler, finaliser);
            count(&r, &u, &statement);
        }
        // A `switch`: one list an action.
        for actions in [0, 1, 5] {
            let statement = switch(&mut r, &mut u, actions);
            count(&r, &u, &statement);
        }
        // A statement without a list.
        let x = r.var(&mut u.b, u.x);
        let effect = r.exp(&mut u.b, x);
        count(&r, &u, &effect);
        let x = r.var(&mut u.b, u.x);
        let returned = r.return_(&mut u.b, x);
        count(&r, &u, &returned);
        assert_eq!(counts, [1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 3, 0, 1, 5, 0, 0]);
    }

    /// Take list `index` of `s`, take each statement of it, list them
    /// again and put the list back, as the replay does. Returns the ids of
    /// the statements, in order.
    fn walk(r: &mut Rows, u: &mut Unit, s: &mut S, index: u32) -> Vec<u32> {
        let list = r.body(&mut u.b, s, index);
        let len = r.len(&u.b, list);
        let mut taken = Vec::new();
        for at in 0..len {
            taken.push(r.take_at(&mut u.b, list, at));
        }
        let ids: Vec<u32> = taken.iter().map(|statement| r.stmt_id(&u.b, statement)).collect();
        let rebuilt = r.list(&mut u.b, len, taken.into_iter());
        r.set_body(&mut u.b, s, index, rebuilt);
        ids
    }

    /// The ids of the children of the block that is list `index` of `s`,
    /// read from the arena.
    fn listed(u: &Unit, s: &S, index: u32) -> Vec<u32> {
        let View::SBlock { statements } = u.b.view(Rows::body_block(&u.b, s, index)) else { panic!("a block") };
        statements.iter().map(|statement| statement.0).collect()
    }

    #[test]
    fn the_lists_of_a_statement_are_taken_and_put_back_by_their_index() {
        let mut u = unit();
        let mut r = Rows::default();
        let mut statements = Vec::new();
        statements.push(block(&mut r, &mut u, 4));
        let (test, yes) = (r.var(&mut u.b, u.x), body(&mut r, &mut u));
        let no = {
            let (x, y) = (r.var(&mut u.b, u.x), r.var(&mut u.b, u.f));
            let (first, second) = (r.exp(&mut u.b, x), r.exp(&mut u.b, y));
            r.list(&mut u.b, 2, [first, second].into_iter())
        };
        statements.push(r.if_plain(&mut u.b, test, yes, no));
        let (condition, list) = (r.var(&mut u.b, u.x), body(&mut r, &mut u));
        statements.push(r.while_(&mut u.b, condition, list, None));
        for init in [true, false] {
            let (var, end) = (fresh(&mut u), r.var(&mut u.b, u.x));
            statements.push(range(&mut r, &mut u, var, init, end));
        }
        let (var, iterable, list) = (fresh(&mut u), r.var(&mut u.b, u.x), body(&mut r, &mut u));
        statements.push(r.for_of(&mut u.b, var, iterable, list, None, false));
        statements.push(tried(&mut r, &mut u, true, true));
        statements.push(switch(&mut r, &mut u, 3));
        for mut statement in statements {
            let id = r.stmt_id(&u.b, &statement);
            let kind = r.stmt_kind(&u.b, &statement);
            let count = r.bodies(&u.b, &statement);
            assert_ne!(count, 0, "{kind:?}");
            for index in 0..count {
                let before = listed(&u, &statement, index);
                let steps = r.steps();
                let ids = walk(&mut r, &mut u, &mut statement, index);
                // One step to take the list, one to put it back, and what
                // `take_at` and `list` count for its statements.
                assert_eq!(r.steps() - steps, 2 + 1 + 2 * before.len() as u64, "{kind:?}");
                assert_eq!(ids, before, "{kind:?}: the statements in order");
                assert_eq!(listed(&u, &statement, index), before, "{kind:?}: the list put back");
            }
            // The statement is the same statement, and whole.
            assert_eq!((r.stmt_id(&u.b, &statement), r.stmt_kind(&u.b, &statement)), (id, kind));
            assert_eq!(r.bodies(&u.b, &statement), count);
            r.release_stmt(&mut u.b, statement);
        }
    }

    #[test]
    fn a_block_keeps_its_braces_and_its_location_over_a_list_put_back() {
        let mut u = unit();
        let mut r = Rows::default();
        let list = body(&mut r, &mut u);
        let mut explicit = r.explicit_block(&mut u.b, list);
        r.locate_stmt(&mut u.b, &mut explicit, LamLoc::NONE);
        let list = body(&mut r, &mut u);
        let mut plain = r.block_of(&mut u.b, list);
        for (statement, aux) in [(&mut explicit, 1), (&mut plain, 0)] {
            walk(&mut r, &mut u, statement, 0);
            assert_eq!(r.stmt_kind(&u.b, statement), Kind::Block);
            assert_eq!(r.stmt_aux(&u.b, statement), aux);
        }
        assert!(r.stmt_located(&u.b, &explicit) && !r.stmt_located(&u.b, &plain));
    }

    /// The cost of a list taken and put back does not grow with the list:
    /// the same steps at 1,000 and at 10,000 statements when no statement
    /// is taken, and no allocation.
    #[test]
    fn a_list_taken_and_put_back_untouched_costs_two_steps_at_any_width() {
        let mut steps = Vec::new();
        for width in [1_000u32, 10_000] {
            let mut u = unit();
            let mut r = Rows::default();
            let mut b = block(&mut r, &mut u, width);
            let before = r.steps();
            let allocations = allocation_counter::measure(|| {
                let list = r.body(&mut u.b, &mut b, 0);
                assert_eq!(r.len(&u.b, list), width);
                r.set_body(&mut u.b, &mut b, 0, list);
            });
            assert_eq!(allocations.count_total, 0, "{allocations:?}");
            steps.push(r.steps() - before);
            assert_eq!(r.block_len(&u.b, &b), width);
        }
        assert_eq!(steps, [2, 2]);
    }

    #[test]
    #[should_panic(expected = "statement list 1 of a statement that has no such list")]
    fn a_list_a_statement_does_not_hold_is_not_taken() {
        let mut u = unit();
        let mut r = Rows::default();
        let mut b = block(&mut r, &mut u, 2);
        r.body(&mut u.b, &mut b, 1);
    }

    #[test]
    #[should_panic(expected = "a statement put back into a list it was not taken from")]
    fn a_statement_of_another_list_is_not_put_back() {
        let mut u = unit();
        let mut r = Rows::default();
        let mut b = block(&mut r, &mut u, 2);
        r.body(&mut u.b, &mut b, 0);
        let other = body(&mut r, &mut u);
        r.set_body(&mut u.b, &mut b, 0, other);
    }

    #[test]
    #[should_panic(expected = "an action of a switch that is no block")]
    fn an_action_of_a_switch_is_a_block() {
        let mut u = unit();
        let mut r = Rows::default();
        let actions = body(&mut r, &mut u);
        let header = u.b.switch_record(crate::bir::SwitchRecord {
            constants: 0,
            keys: crate::bir::KeySpan { start: 0, len: 0 },
            clauses: crate::bir::ClauseSpan { start: 0, len: 0 },
            has_default: false,
            consts_full: false,
            blocks_full: false,
            dispatch: crate::lambda::SwitchDispatch::Direct,
        });
        let scrutinee = r.var(&mut u.b, u.x);
        r.switch(&mut u.b, scrutinee, actions, header, false);
    }

    /// A function literal over `width` statements `x;`, as the value of
    /// `let var = function`, and its header.
    pub(super) fn literal(r: &mut Rows, u: &mut Unit, width: u32) -> (S, crate::bir::FuncId) {
        let header = u.b.function_header(crate::bir::VarSpan { start: 0, len: 0 }, Default::default(), LamLoc::NONE);
        let mut statements = Vec::new();
        for _ in 0..width {
            let x = r.var(&mut u.b, u.x);
            statements.push(r.exp(&mut u.b, x));
        }
        let list = r.list(&mut u.b, width, statements.into_iter());
        let function = r.function(&mut u.b, header, list);
        let var = fresh(u);
        (r.declare(&mut u.b, LetKind::Strict, var, Some(function)), header)
    }

    /// The ids of the statements of the body of the literal of `header`,
    /// read from the arena.
    fn body_of(u: &Unit, header: crate::bir::FuncId) -> Vec<u32> {
        let View::SBlock { statements } = u.b.view(Rows::literal_block(&u.b, header)) else { panic!("a block") };
        statements.iter().map(|statement| statement.0).collect()
    }

    #[test]
    fn the_body_of_a_function_literal_is_taken_and_put_back_by_its_header() {
        let mut u = unit();
        let mut r = Rows::default();
        // Two literals: a header names its own.
        let (first, one) = literal(&mut r, &mut u, 3);
        let (second, two) = literal(&mut r, &mut u, 2);
        for (header, width) in [(two, 2), (one, 3)] {
            let before = body_of(&u, header);
            assert_eq!(before.len(), width);
            let steps = r.steps();
            let list = r.literal_body(&mut u.b, header);
            assert_eq!(r.len(&u.b, list) as usize, width);
            let taken: Vec<S> = (0..width as u32).map(|at| r.take_at(&mut u.b, list, at)).collect();
            assert_eq!(taken.iter().map(|statement| r.stmt_id(&u.b, statement)).collect::<Vec<_>>(), before);
            let rebuilt = r.list(&mut u.b, width as u32, taken.into_iter());
            r.set_literal_body(&mut u.b, header, rebuilt);
            assert_eq!(r.steps() - steps, 2 + 1 + 2 * width as u64);
            assert_eq!(body_of(&u, header), before);
        }
        // The literals are where they were: the value of their statement.
        for (statement, header) in [(&first, one), (&second, two)] {
            let value = r.value_of(&u.b, statement).expect("a declaration with a value");
            assert_eq!(r.function_of(&u.b, value), Some(header));
        }
    }

    /// Taking the body of a literal and putting it back is O(1): the same
    /// two steps at 1,000 and at 10,000 statements, and no allocation.
    #[test]
    fn the_body_of_a_function_literal_costs_two_steps_at_any_width() {
        let mut steps = Vec::new();
        for width in [1_000u32, 10_000] {
            let mut u = unit();
            let mut r = Rows::default();
            let (_statement, header) = literal(&mut r, &mut u, width);
            let before = r.steps();
            let allocations = allocation_counter::measure(|| {
                let list = r.literal_body(&mut u.b, header);
                assert_eq!(r.len(&u.b, list), width);
                r.set_literal_body(&mut u.b, header, list);
            });
            assert_eq!(allocations.count_total, 0, "{allocations:?}");
            steps.push(r.steps() - before);
            assert_eq!(body_of(&u, header).len() as u32, width);
        }
        assert_eq!(steps, [2, 2]);
    }

    #[test]
    #[should_panic(expected = "a function literal that is not there")]
    fn the_body_of_a_header_without_a_literal_is_not_taken() {
        let mut u = unit();
        let mut r = Rows::default();
        let header = u.b.function_header(crate::bir::VarSpan { start: 0, len: 0 }, Default::default(), LamLoc::NONE);
        r.literal_body(&mut u.b, header);
    }

    #[test]
    #[should_panic(expected = "a statement put back into a list it was not taken from")]
    fn a_statement_of_another_list_is_not_put_back_into_a_literal() {
        let mut u = unit();
        let mut r = Rows::default();
        let (_statement, header) = literal(&mut r, &mut u, 2);
        r.literal_body(&mut u.b, header);
        let other = body(&mut r, &mut u);
        r.set_literal_body(&mut u.b, header, other);
    }
}
