//! The statement half of the lowering's interface (THREE_TREES 11.4, "T6:
//! the interface" (a); slice T6l). [`Js`] is the expression half.
//!
//! # What a statement and a list are
//!
//! A statement in flight ([`JsStmt::S`]) is owned by whoever holds its
//! handle: the lowering's statement stack (`out.rs`) for the statements of
//! a run, a constructor for the statement it is given. It is not `Copy`.
//!
//! A list in flight ([`JsStmt::L`]) is a finished run of statements that
//! no statement holds yet: the body of a loop before the loop is built, a
//! branch before its `if`. It is made by [`JsStmt::list`] from the
//! statements of a run, each moved once, and it is consumed by the
//! constructor it is given to, which makes the block. A constructor takes
//! a body as a list and never as a block statement: the block is the
//! implementation's. A list is `Copy` (it is an index), so the type does
//! not stop a second use; the implementation panics on one ("a statement
//! attached twice" on rows, "a statement taken twice" on the builder).
//!
//! The interface has no staging stack: the lowering has one
//! (`StatementStack`), and a second one behind the interface would move
//! every statement twice.
//!
//! # Plain functions and rule functions
//!
//! As in [`Js`]. The rule functions are J-S1 ([`JsStmt::exp_rule`]), J-S3
//! ([`JsStmt::if_`]) and J-M14 ([`JsStmt::effect`],
//! [`JsStmt::effect_if_impure`]). No other statement rule of
//! BACKEND_LOWERING 6 is called by the lowering: J-S2 and J-S5 are done on
//! its stack, and J-S4 has no call (a switch is built as given).
//!
//! # Cost
//!
//! Every function is O(1) unless its comment says otherwise. A constructor
//! that consumes a list costs one step per statement of the list (it
//! adopts each once). Nothing here allocates in a warm unit.
use super::js::{Js, Pools};
use crate::bir::{FuncId, ListId, NodeId, StrId, SwitchId, VarId};
use crate::emit::row::Kind;
use crate::lambda::LamLoc;
use crate::lambda::lam_compat::LetKind;

/// The bounds of a range loop. `init` is `None` when the variable is
/// declared before the loop and the loop starts from it; `direction` is a
/// `ForDirection`.
pub struct Range<E> {
    /// The first value.
    pub init: Option<E>,
    /// The bound.
    pub end: E,
    /// A `ForDirection`.
    pub direction: u16,
}

/// The statement half of the interface.
pub trait JsStmt: Js {
    /// A statement in flight. Not `Copy`.
    type S;
    /// A statement list in flight. `Copy`; at most 8 bytes.
    type L: Copy;

    // ---- The transition (deleted by T6x with their last call) ----

    /// The handle of a J statement built outside the interface. O(1).
    fn stmt_from_node(node: NodeId) -> Self::S;
    /// The J row of a statement, for a caller that is not converted. O(1).
    fn stmt_node(s: Self::S) -> NodeId;
    /// The list of a pool list made outside the interface (by
    /// `StatementStack::take_list`). O(1).
    fn list_from(list: ListId) -> Self::L;
    /// The pool list of a list, for a caller that is not converted. O(1).
    fn list_id(list: Self::L) -> ListId;

    // ---- Reading a statement in hand ----

    /// The kind of the statement. O(1).
    fn stmt_kind(&self, a: &Pools, s: &Self::S) -> Kind;
    /// The `aux` of the statement's kind as [`Kind`] documents it: the
    /// `LetKind` of a `Declare` (its low two bits), 1 for a string
    /// `Switch`, 1 for a `Block` that is explicit. O(1).
    fn stmt_aux(&self, a: &Pools, s: &Self::S) -> u8;
    /// The expression the statement evaluates first: the value of an
    /// `Exp`, a `Return`, a `Throw` and a `Declare` that has one, the test
    /// of an `If`, the condition of a `While`, the scrutinee of a
    /// `Switch`. `None` for every other statement. O(1).
    fn value_of<'r>(&self, a: &'r Pools, s: &'r Self::S) -> Option<Self::Ref<'r>>;

    /// Whether the statement has a source location. O(1). (T6o.)
    fn stmt_located(&self, a: &Pools, s: &Self::S) -> bool;

    // ---- Lists ----

    /// The list of `len` statements, in the order given. One step per
    /// statement, each moved once; no allocation in a warm unit. Panics
    /// when `statements` does not yield `len`.
    fn list(&mut self, a: &mut Pools, len: u32, statements: impl Iterator<Item = Self::S>) -> Self::L;
    /// The number of statements of a list in flight. O(1).
    fn len(&self, a: &Pools, list: Self::L) -> u32;
    /// The kind of statement `index` of a list in flight. O(1). Panics
    /// when `index` is not below [`JsStmt::len`].
    fn kind_at(&self, a: &Pools, list: Self::L, index: u32) -> Kind;
    /// Statement `index` moved out of a list in flight that no statement
    /// holds. One step. The list may not be given to a constructor after
    /// it: every statement of it is taken, or none.
    fn take_at(&mut self, a: &mut Pools, list: Self::L, index: u32) -> Self::S;

    // ---- Statements (plain) ----

    /// `value;`.
    fn exp(&mut self, a: &mut Pools, value: Self::E) -> Self::S;
    /// `var = value;`: marks the variable assigned, counts its occurrence
    /// and records the site.
    fn assign(&mut self, a: &mut Pools, var: VarId, value: Self::E) -> Self::S;
    /// `let var = value;` or `let var;`, with the declaration kind. Binds
    /// the variable.
    fn declare(&mut self, a: &mut Pools, kind: LetKind, var: VarId, value: Option<Self::E>) -> Self::S;
    /// `return value;`.
    fn return_(&mut self, a: &mut Pools, value: Self::E) -> Self::S;
    /// `throw value;`.
    fn throw(&mut self, a: &mut Pools, value: Self::E) -> Self::S;
    /// `debugger;`.
    fn debugger(&mut self, a: &mut Pools) -> Self::S;
    /// `break;` or `break label;`.
    fn break_(&mut self, a: &mut Pools, label: Option<StrId>) -> Self::S;
    /// `continue;` or `continue label;`.
    fn continue_(&mut self, a: &mut Pools, label: Option<StrId>) -> Self::S;
    /// The statements of `list` as one statement that prints without
    /// braces of its own (the body of something, or a run to splice). One
    /// step per statement.
    fn block_of(&mut self, a: &mut Pools, list: Self::L) -> Self::S;
    /// `{ ...list }` as written: a block that keeps its braces. One step
    /// per statement.
    fn explicit_block(&mut self, a: &mut Pools, list: Self::L) -> Self::S;
    /// `if (test) { yes } else { no }` as given: both blocks are kept, an
    /// empty one too, and the test is not rewritten (not J-S3). One step
    /// per statement of both lists.
    fn if_plain(&mut self, a: &mut Pools, test: Self::E, yes: Self::L, no: Self::L) -> Self::S;
    /// `while (condition) { body }`, with its label. One step per
    /// statement of the body.
    fn while_(&mut self, a: &mut Pools, condition: Self::E, body: Self::L, label: Option<StrId>) -> Self::S;
    /// `for (let var = init; var <direction> end; ...) { body }`. Binds the
    /// variable. One step per statement of the body.
    fn for_range(&mut self, a: &mut Pools, var: VarId, range: Range<Self::E>, body: Self::L, label: Option<StrId>) -> Self::S;
    /// `for (const var of iterable) { body }`; `awaited` makes it `for
    /// await`. Binds the variable. One step per statement of the body.
    fn for_of(
        &mut self,
        a: &mut Pools,
        var: VarId,
        iterable: Self::E,
        body: Self::L,
        label: Option<StrId>,
        awaited: bool,
    ) -> Self::S;
    /// `switch (scrutinee) { ...actions }` as given (not J-S4): `actions`
    /// holds one statement per clause of `header`, the default last;
    /// `string` says the keys are strings. One step per action.
    fn switch(&mut self, a: &mut Pools, scrutinee: Self::E, actions: Self::L, header: SwitchId, string: bool) -> Self::S;
    /// `try { body } catch (exception) { handler } finally { finaliser }`:
    /// a handler with its exception variable, a finaliser, or both.
    /// Panics without either. One step per statement of the lists.
    fn try_(&mut self, a: &mut Pools, body: Self::L, handler: Option<(VarId, Self::L)>, finaliser: Option<Self::L>) -> Self::S;
    /// The function literal of `header` with `body`. Strictly pure
    /// whatever its body is (a literal runs nothing). One step per
    /// statement of the body: the list is adopted, not copied.
    fn function(&mut self, a: &mut Pools, header: FuncId, body: Self::L) -> Self::E;

    // ---- What later slices add (each body is its slice's) ----

    /// Give the statement the source location `loc`; a comment it has is
    /// kept. O(1). (T6m: `prim.rs`, the statement of a `debugger` and of a
    /// raise; T6o: `location.rs`, the first statement of a switch run.)
    fn locate_stmt(&mut self, a: &mut Pools, s: &mut Self::S, loc: LamLoc);
    /// The value of an `Exp`, a `Return` or a `Throw`, taken out; the
    /// statement is released. One step. Panics on any other statement.
    /// (T6n: `cond.rs`, a lone expression statement that becomes the value,
    /// and the fold of `e1; e2; return v` into a comma.)
    fn take_value(&mut self, a: &mut Pools, s: Self::S) -> Self::E;
    /// The statements of a block statement, given to `sink` in order, each
    /// moved once; the block is released. One step and one per statement.
    /// Panics on a statement that is not a `Block`. (T6n: `cond.rs`,
    /// `unnest`; T6o: `untagged.rs`, a cached run that is staged.)
    fn unblock(&mut self, a: &mut Pools, s: Self::S, sink: impl FnMut(Self::S));

    // ---- Rules of BACKEND_LOWERING 6 ----

    /// J-S1: the statement of a value used for its effect. Its cost: one
    /// visit per comma operand dropped; counted as one step.
    fn exp_rule(&mut self, a: &mut Pools, value: Self::E) -> Self::S;
    /// J-S3: `if` with its simplifications; may return a statement that is
    /// not an `if`. Its cost: that of the rule (BACKEND_LOWERING 6);
    /// counted as one step and one per statement of both lists.
    fn if_(&mut self, a: &mut Pools, test: Self::E, yes: Self::L, no: Self::L) -> Self::S;
    /// J-M14: the statements of a value used for its effect, given to
    /// `sink` in order; a value without effect gives none and is released.
    /// Its cost: that of the rule (one visit per comma operand, and the
    /// nodes it releases); counted as one step and one per statement
    /// given. No allocation in a warm unit.
    fn effect(&mut self, a: &mut Pools, value: Self::E, sink: impl FnMut(Self::S));
    /// J-M14 for the test of an `if` whose branches are empty: nothing
    /// for a pure test, which is released; otherwise its statement. One
    /// step, and one per statement given.
    fn effect_if_impure(&mut self, a: &mut Pools, value: Self::E, sink: impl FnMut(Self::S));
}

#[cfg(test)]
#[path = "js_stmt_tests.rs"]
mod tests;
