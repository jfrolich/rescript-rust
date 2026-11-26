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
