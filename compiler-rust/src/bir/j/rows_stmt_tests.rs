//! Tests of the statement functions the probe before T6x-f adds to the
//! interface (`PROBE-ADD n` in `bir/lower/js_stmt.rs`), on J rows. Each
//! builds a small tree, calls the function, and compares the result with
//! what the by-id code of trunk gives for the same tree.
use super::S;
use crate::bir::j::rows::Rows;
use crate::bir::lower::js::Js;
use crate::bir::lower::js_stmt::JsStmt;
use crate::bir::lower::scope::Scope;
use crate::bir::{Bir, NodeId, VarId};
use crate::emit::row::Kind;
use crate::lambda::LamLoc;
use crate::lambda::lam_compat::LetKind;
use crate::name::Name;

/// What both sides start from: an arena that counts JavaScript
/// occurrences and two variables.
struct Unit {
    b: Bir,
    x: VarId,
    t: VarId,
}

fn unit() -> Unit {
    let mut b = Bir::default();
    b.begin_bulk();
    b.js_scope = Some(Scope::new(0));
    let x = b.new_var_id(Name::new("x"), 1);
    let t = b.new_var_id(Name::new("t"), 2);
    Unit { b, x, t }
}

/// A block of `width` statements: `x;` but for statement `width / 2`,
/// `let t = x;`.
fn block(r: &mut Rows, u: &mut Unit, width: u32) -> S {
    let a = &mut u.b;
    let mut statements = Vec::new();
    for index in 0..width {
        let x = r.var(a, u.x);
        statements.push(if index == width / 2 {
            r.declare(a, LetKind::Strict, u.t, Some(x))
        } else {
            r.exp(a, x)
        });
    }
    let list = r.list(a, width, statements.into_iter());
    r.block_of(a, list)
}

/// The ids of the statements of `block`, as trunk's `build_rows` read them.
fn ids(r: &Rows, a: &Bir, block: &S) -> Vec<u32> {
    let mut ids = Vec::new();
    r.block_ids(a, block, |id| ids.push(id));
    ids
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

/// PROBE-ADD 3: the length of a block is the number of ids trunk read.
#[test]
fn the_length_of_a_block_is_the_number_of_its_statements() {
    let mut u = unit();
    let mut r = Rows::default();
    let b = block(&mut r, &mut u, 5);
    assert_eq!(r.block_len(&u.b, &b) as usize, ids(&r, &u.b, &b).len());
    r.release_stmt(&mut u.b, b);
}

/// PROBE-ADD 4: a statement of a block read by its index is the statement
/// trunk read by its id, and the read counts no step.
#[test]
fn a_statement_of_a_block_is_read_by_its_index_where_it_is() {
    let mut u = unit();
    let mut r = Rows::default();
    let b = block(&mut r, &mut u, 5);
    let ids = ids(&r, &u.b, &b);
    let steps = r.steps();
    for index in [0, 2, 4] {
        let ours = r.with_block_stmt_at(&u.b, &b, index, |s| read(&r, &u.b, s));
        let trunk = read(&r, &u.b, &<Rows as JsStmt>::stmt_from_node(NodeId(ids[index as usize])));
        assert_eq!(ours, trunk);
    }
    assert_eq!(r.steps(), steps);
    r.release_stmt(&mut u.b, b);
}

/// PROBE-ADD 5: a statement of a block lent with the implementation and
/// the pools is changed in place as trunk changed it by its id, and the
/// lend counts no step.
#[test]
fn a_statement_of_a_block_is_lent_to_an_edit_where_it_is() {
    let (mut left, mut right) = (unit(), unit());
    let (mut r, mut t) = (Rows::default(), Rows::default());
    let mut ours = block(&mut r, &mut left, 5);
    let theirs = block(&mut t, &mut right, 5);
    let steps = r.steps();
    let kind = r.with_block_stmt_mut(&mut left.b, &mut ours, 3, |js, a, s| {
        js.locate_stmt(a, s, LamLoc::NONE);
        js.stmt_kind(a, s)
    });
    assert_eq!(r.steps(), steps);
    let id = ids(&t, &right.b, &theirs)[3];
    let mut statement = <Rows as JsStmt>::stmt_from_node(NodeId(id));
    t.locate_stmt(&mut right.b, &mut statement, LamLoc::NONE);
    assert_eq!(kind, t.stmt_kind(&right.b, &statement));
    assert_eq!(left.b.dump(), right.b.dump());
    r.release_stmt(&mut left.b, ours);
    t.release_stmt(&mut right.b, theirs);
}

/// PROBE-ADD 6: a statement taken out of a block by its index and released
/// leaves the arena as trunk's `release_row` left it (`Bir::detach` and
/// `Bir::release` by id); the statements after it keep their indexes; the
/// take counts one step.
#[test]
fn a_statement_taken_out_of_a_block_leaves_a_hole() {
    let (mut left, mut right) = (unit(), unit());
    let (mut r, t) = (Rows::default(), Rows::default());
    let mut ours = block(&mut r, &mut left, 5);
    let theirs = block(&mut Rows::default(), &mut right, 5);
    let before = ids(&r, &left.b, &ours);
    let steps = r.steps();
    let taken = r.take_from_block(&mut left.b, &mut ours, 2);
    assert_eq!(r.steps(), steps + 1);
    assert_eq!(r.stmt_id(&left.b, &taken), before[2]);
    r.release_stmt(&mut left.b, taken);
    let id = NodeId(ids(&t, &right.b, &theirs)[2]);
    right.b.detach(id);
    right.b.release(id);
    assert_eq!(left.b.dump(), right.b.dump());
    assert_eq!(r.block_len(&left.b, &ours), 5);
    for index in [3, 4] {
        let id = r.with_block_stmt_at(&left.b, &ours, index, |s| r.stmt_id(&left.b, s));
        assert_eq!(id, before[index as usize]);
    }
    // A block with a hole is released as trunk released the block it had
    // detached a statement from.
    r.release_stmt(&mut left.b, ours);
    right.b.release(NodeId(t.stmt_id(&right.b, &theirs)));
    assert_eq!(left.b.dump(), right.b.dump());
}

/// `let t = x.name.name...`, `depth` reads deep, the reads with a location.
fn declaration(r: &mut Rows, u: &mut Unit, depth: u32) -> S {
    let a = &mut u.b;
    let name = a.intern_text("name");
    let mut value = r.var(a, u.x);
    for _ in 0..depth {
        value = r.dot(a, value, name, crate::js_ir::arena::FieldPos::NONE, false);
        r.locate(a, &mut value, LamLoc::NONE);
    }
    r.declare(a, LetKind::Strict, u.t, Some(value))
}

/// Trunk's copy of a replacement that is a chain of member reads, by id
/// (`export.rs::copy_replacement`): the reads pushed from the top, the
/// leaf copied with its cold data, then each read from the innermost out.
fn copy_by_id(r: &mut Rows, a: &mut Bir, node: NodeId, made: &mut Vec<u32>) -> crate::bir::j::rows::E {
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

/// PROBE-ADD 7: the copy of a statement's value is the copy trunk made of
/// the initialiser by its id: the chain and its cold data (a literal
/// replacement), `copy_leaf` without (a module member); the same nodes,
/// ids reported in order, the same steps, one a node from 1,000 to 10,000
/// reads.
#[test]
fn a_copy_of_a_statement_value_is_the_copy_trunk_makes_by_id() {
    let mut counts = [0; 2];
    for (at, depth) in [1_000u32, 10_000].into_iter().enumerate() {
        let (mut left, mut right) = (unit(), unit());
        let (mut r, mut t) = (Rows::default(), Rows::default());
        let ours = declaration(&mut r, &mut left, depth);
        let theirs = declaration(&mut t, &mut right, depth);
        let (mut made, mut expected) = (Vec::new(), Vec::new());
        let before = r.steps();
        let copy = r.copy_value(&mut left.b, &ours, true, |id| made.push(id));
        let steps = r.steps() - before;
        let initialiser = NodeId(t.id(&right.b, t.value_of(&right.b, &theirs).unwrap()));
        let before = t.steps();
        let trunk = copy_by_id(&mut t, &mut right.b, initialiser, &mut expected);
        assert_eq!(steps, t.steps() - before);
        assert_eq!(made, expected);
        assert_eq!(left.b.dump(), right.b.dump());
        counts[at] = steps;
        r.release(&mut left.b, copy);
        t.release(&mut right.b, trunk);
    }
    assert_eq!(counts[1] - 1, 10 * (counts[0] - 1));
    // Without cold data, of a leaf: `copy_leaf`, as trunk copied a module
    // member.
    let (mut left, mut right) = (unit(), unit());
    let (mut r, mut t) = (Rows::default(), Rows::default());
    let ours = declaration(&mut r, &mut left, 0);
    let theirs = declaration(&mut t, &mut right, 0);
    let mut made = Vec::new();
    let copy = r.copy_value(&mut left.b, &ours, false, |id| made.push(id));
    let initialiser = NodeId(t.id(&right.b, t.value_of(&right.b, &theirs).unwrap()));
    let trunk = t.copy_leaf(&mut right.b, <Rows as Js>::at(initialiser));
    assert_eq!(made, [t.id(&right.b, Rows::of(&trunk))]);
    assert_eq!(left.b.dump(), right.b.dump());
    r.release(&mut left.b, copy);
    t.release(&mut right.b, trunk);
}
