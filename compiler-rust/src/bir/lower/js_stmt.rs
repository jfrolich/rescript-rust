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
//! ([`JsStmt::if_`], and [`JsStmt::if_head`] for its rules 0 to 6 over two
//! runs of the caller's stack) and J-M14 ([`JsStmt::effect`],
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

/// The runs of statements [`JsStmt::if_head`] works on. The lowering's
/// statement stack implements it (T6x-a): a run is a span of its slots,
/// and a branch that is kept stays where it was lowered. The functions
/// that release or move statements take the implementation and the pools,
/// because the runs own handles and the implementation owns what is behind
/// them.
pub trait Runs<B: JsStmt> {
    /// A run. `Copy`; at most 8 bytes.
    type Run: Copy;
    /// Drop the explicit empty blocks of `run`, each released. On the
    /// statement stack: two binary searches among the empty blocks it
    /// noted and one step per empty block of the run; no other statement
    /// of the run is read.
    fn trim(&mut self, js: &mut B, a: &mut Pools, run: Self::Run);
    /// A run without a statement. O(1).
    fn empty(&mut self) -> Self::Run;
    /// The last statement of `run`, read in place; `None` for a run
    /// without one. O(1) on a run that ends in a statement.
    fn last(&mut self, run: Self::Run) -> Option<&B::S>;
    /// The statement of a run that holds exactly one, read in place. O(1)
    /// on a run that starts with a statement: its first two are looked at.
    fn only(&mut self, run: Self::Run) -> Option<&B::S>;
    /// Release every statement of `run` ([`JsStmt::release_stmt`]); the run
    /// is consumed. One step per node released.
    fn release(&mut self, js: &mut B, a: &mut Pools, run: Self::Run);
    /// The statements of `run` as a list in flight ([`JsStmt::list`]), each
    /// moved once; the run is consumed. One step and one per statement.
    fn take(&mut self, js: &mut B, a: &mut Pools, run: Self::Run) -> B::L;
}

/// What [`JsStmt::if_head`] leaves of a conditional: the statement that
/// goes before the kept branch, if there is one, and the kept branch, which
/// was not moved. 16 bytes with the statement of rows and a run of 8.
pub struct IfHead<S, R> {
    /// The guard, the folded `return`, the test as a statement, or an
    /// empty block where the rule leaves nothing else.
    pub statement: Option<S>,
    /// The run that follows `statement`, where it was.
    pub tail: R,
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
    /// The id of the statement, read in place: what [`Js::owner`] gives for
    /// its value, what [`JsStmt::block_ids`] gives for it once a block
    /// holds it, and a key for [`Js::kind_of`]. It does not change while
    /// the statement lives, and no other live statement has it. O(1): on
    /// rows the row; on the builder the `node_id` of the owned node, one
    /// load. (T6x-a: the statement stack keys its empty-block table by it,
    /// since a slot is reused; `export.rs::build_rows` stores it for each
    /// row of the top level.)
    fn stmt_id(&self, a: &Pools, s: &Self::S) -> u32;

    // ---- Lists ----

    /// The list of `len` statements, in the order given. One step, and one
    /// per statement, each moved once; no allocation in a warm unit. Panics
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
    /// Statement `index` of a list in flight, read where it is: `read` is
    /// given the statement by reference, for the readers of a statement in
    /// hand ([`JsStmt::stmt_kind`], [`JsStmt::declared`],
    /// [`JsStmt::stmt_aux`], [`JsStmt::value_of`]), and what it returns is
    /// returned. The statement stays in the list, which is given to a
    /// constructor afterwards as if it had not been read. A reference into
    /// the statement ([`JsStmt::value_of`]) does not outlive `read`: what
    /// the caller keeps is a fact or an id ([`Js::id`]).
    ///
    /// O(1) and whatever `read` costs: the statement is found by its
    /// position, and no other statement of the list is read. Counts no
    /// step (a reader); allocates nothing. Panics when `index` is not
    /// below [`JsStmt::len`], and where a statement can be absent (the
    /// builder) when it was taken out before. (T6x-b3b: `close::decide`,
    /// which reads each declaration and each `return` of a list between
    /// the list's making and the constructor that consumes it.)
    fn with_stmt_at<R>(&self, a: &Pools, list: Self::L, index: u32, read: impl FnOnce(&Self::S) -> R) -> R;

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
    /// Whether the statement is a block (explicit or not) without a
    /// statement. O(1). (T6n: `cond.rs`, an empty block placed in a slot
    /// is noted for the `if` above it; T6o: the empty action of a switch.)
    fn is_empty_block(&self, a: &Pools, s: &Self::S) -> bool;
    /// The kind of the last statement of the then-block of an `If`, or of
    /// its else-block when `otherwise`; `None` when that block has no
    /// statement or the `If` has no such block. O(1). Panics on a
    /// statement that is not an `If`. (T6n: `cond.rs::merge_tail_guard`
    /// reads whether a guard ends in a jump and has nothing in its else.)
    fn branch_last_kind(&self, a: &Pools, s: &Self::S, otherwise: bool) -> Option<Kind>;
    /// The variable a `Declare` or a `Rest` binds; `None` for any other
    /// statement. O(1). (T6q: `export.rs`, the rows of the top level.)
    fn declared(&self, a: &Pools, s: &Self::S) -> Option<VarId>;
    /// The ids of the statements of a block, given to `sink` in order; the
    /// statements stay in the block. O(statements); counts no step (a
    /// reader). Panics on a statement that is not a `Block`. (T6q:
    /// `export.rs::build_rows`, the rows of a top-level block.)
    fn block_ids(&self, a: &Pools, s: &Self::S, sink: impl FnMut(u32));
    // PROBE-ADD 3: the number of statements of a block statement the caller holds.
    /// The number of statements of the block statement `block`, a taken
    /// one ([`JsStmt::take_from_block`]) counted: the bound of the indexes
    /// [`JsStmt::with_block_stmt_at`] reads. The caller owns `block` (the
    /// statement stack holds it, or another block the caller reads). An
    /// implementation that owns its nodes gives the length of the block's
    /// statement vector. O(1); counts no step (a reader). Panics on a
    /// statement that is not a `Block`. (`export.rs::build_rows`.)
    fn block_len(&self, a: &Pools, block: &Self::S) -> u32;
    // PROBE-ADD 4: a statement of a block statement the caller holds, read where it is, by its index.
    /// Statement `index` of the block statement `block`, read where it is:
    /// `read` is given it by reference, as [`JsStmt::with_stmt_at`] gives a
    /// statement of a list in flight, and what it returns is returned. A
    /// block the statement stack holds is not a list in flight: its
    /// statements are its own, and stay in it. The caller owns `block`;
    /// the block owns the statement. An implementation that owns its nodes
    /// lends `&block.statements[index]`; on rows the statement is the
    /// entry of the block's pool list, named for the length of the call.
    /// O(1) and whatever `read` costs; counts no step; allocates nothing.
    /// Panics on a statement that is not a `Block`, when `index` is not
    /// below [`JsStmt::block_len`], and where a statement can be absent
    /// (the builder) when it was taken out. (`export.rs`: the rows of a
    /// block of the top level.)
    fn with_block_stmt_at<R>(&self, a: &Pools, block: &Self::S, index: u32, read: impl FnOnce(&Self::S) -> R) -> R;
    // PROBE-ADD 5: a statement of a block statement the caller holds, lent with the implementation and the pools.
    /// Statement `index` of the block statement `block`, lent to `edit`
    /// with the implementation and the pools, so that `edit` may call a
    /// function that takes them mutably (a copy of its value, a release, a
    /// reader that counts steps) or change the statement in place; what
    /// `edit` returns is returned. `edit` may not put another statement in
    /// its place (on rows a statement written into the reference is
    /// dropped). The caller owns `block`; the block owns the statement. An
    /// implementation that owns its nodes lends `&mut
    /// block.statements[index]`; on rows the statement is the entry of the
    /// block's pool list. O(1) and whatever `edit` costs; counts no step;
    /// allocates nothing. Panics as [`JsStmt::with_block_stmt_at`] does.
    /// (`export.rs`: a row nested in a block, when a copy, a release or
    /// `JsStmt::effect_free` reads it.)
    fn with_block_stmt_mut<R>(
        &mut self,
        a: &mut Pools,
        block: &mut Self::S,
        index: u32,
        edit: impl FnOnce(&mut Self, &mut Pools, &mut Self::S) -> R,
    ) -> R;
    // PROBE-ADD 7: a copy of the value of a statement the caller holds, as `copy_members` (or `copy_leaf`) copies it.
    /// A copy of the expression statement `s` evaluates first
    /// ([`JsStmt::value_of`]): with `cold`, what [`Js::copy_members`] gives
    /// for it (the member reads down to their leaf and the leaf, each with
    /// its cold data); without, what [`Js::copy_leaf`] gives (the value is a
    /// leaf; no cold data). `made` is given the id of each node made, in
    /// order. A `Ref` that `value_of` gives borrows the pools, which a copy
    /// takes mutably, so the copy is asked of the statement and not of the
    /// reference. The caller owns `s` (the statement stack, a block it
    /// lends, or the fold's tables hold it); the copy is the caller's. An
    /// implementation that owns its nodes reads the value in `s` and makes
    /// a new owned chain. One step per node made; allocates nothing once
    /// the implementation's work stack has the chain's depth. Panics on a
    /// statement without a value, and without `cold` on a value that is
    /// not a leaf. (`export.rs::copy_replacement`: a literal or a module
    /// member that is a row's initialiser.)
    fn copy_value(&mut self, a: &mut Pools, s: &Self::S, cold: bool, made: impl FnMut(u32)) -> Self::E;
    // PROBE-ADD 6: a statement of a block statement the caller holds, taken out by its index, leaving a hole.
    /// Statement `index` of the block statement `block` moved out, to the
    /// caller, who owns it from here. The block keeps a hole at `index`:
    /// the indexes of the statements after it do not change, and a block
    /// with a hole is given to nothing but this function, the readers of
    /// its other statements and [`JsStmt::release_stmt`], which releases
    /// what it still holds. On rows the statement is detached from the
    /// block (`Bir::detach`) and its entry stays in the block's pool list;
    /// an implementation that owns its nodes takes it out of the slot and
    /// leaves the slot empty. One step (it takes a node apart); O(1); no
    /// allocation. Panics on a statement that is not a `Block`, when
    /// `index` is not below [`JsStmt::block_len`], and on a hole.
    /// (`export.rs`: a removed row of a block, and the statements of a
    /// dissolved block, by their index.)
    fn take_from_block(&mut self, a: &mut Pools, block: &mut Self::S, index: u32) -> Self::S;
    /// S:1053 `js_statement_no_side_effects`: the statement runs no code
    /// that can be observed. An expression statement and a `return` are
    /// free when their value is strictly pure (E:15); a block, an `if`, a
    /// `while`, a range loop, a `switch` and a `try` when every statement
    /// and expression below them is; a `throw`, a `debugger`, a jump, a
    /// declaration and a loop over an iterable never are. One step per
    /// node read; the read stops at the first effect. An implementation
    /// that keeps the fact with the statement answers in O(1). (T6q:
    /// `export.rs::has_toplevel_effect`; the review of the T6l skeleton,
    /// decisions 4 and 9.)
    fn effect_free(&mut self, a: &Pools, s: &Self::S) -> bool;
    /// A copy of the statement `s` and everything below it: the binders
    /// and the static labels inside it are fresh, and `(fresh, source)` is
    /// appended to `fresh` for each binder, in the order the fresh
    /// variables were made. One step per node copied; allocates nothing
    /// once the implementation's copy storage and `fresh` have their
    /// capacity. (T6o: `untagged.rs::copy_dispatch_output`, an action of a
    /// dispatch that is emitted more than once.)
    fn copy_stmt(&mut self, a: &mut Pools, s: &Self::S, fresh: &mut Vec<(VarId, VarId)>) -> Self::S;
    /// `s` is not used: its references and sites are given back. One step
    /// per node released. (T6n: `cond.rs::release_run`, a discarded run.)
    fn release_stmt(&mut self, a: &mut Pools, s: Self::S);
    /// `if (test) yes else no` over two block statements the caller holds,
    /// as given: both are kept and the test is not rewritten (not J-S3).
    /// O(1): the blocks are moved in, their statements are not read.
    /// (T6n: `cond.rs`, the guard of a tail conditional.)
    fn if_blocks(&mut self, a: &mut Pools, test: Self::E, yes: Self::S, no: Self::S) -> Self::S;
    /// An `If` taken apart: its test, its then-block and its else-block if
    /// it has one, each moved out; the statement is released. One step;
    /// O(1): no statement of a block is read. Panics on a statement that
    /// is not an `If`. (T6n: `cond.rs::merge_tail_guard`.)
    fn take_if(&mut self, a: &mut Pools, s: Self::S) -> (Self::E, Self::S, Option<Self::S>);

    // ---- Rules of BACKEND_LOWERING 6 ----

    /// J-S1: the statement of a value used for its effect. Its cost: one
    /// visit per comma operand dropped; counted as one step.
    fn exp_rule(&mut self, a: &mut Pools, value: Self::E) -> Self::S;
    /// J-S3: `if` with its simplifications; may return a statement that is
    /// not an `if`. Its cost: that of the rule (BACKEND_LOWERING 6);
    /// counted as one step and one per statement of both lists.
    fn if_(&mut self, a: &mut Pools, test: Self::E, yes: Self::L, no: Self::L) -> Self::S;
    /// J-S3 rules 0 to 6 over two runs the caller holds (`runs` is its
    /// statement stack), for a conditional whose kept branch stays where it
    /// was lowered: the empty blocks of both runs are dropped, a boolean
    /// test keeps one run and releases the other, a negation is stripped
    /// and the runs are swapped, two lone `return`s fold into one, a lone
    /// `return` in the else-run or a then-run that ends in a jump becomes a
    /// guard and the other run is the tail. `None` when none of these
    /// applies: `test`, `yes` and `no` are then what the rules made of
    /// them (the negations stripped, the runs swapped), for
    /// [`JsStmt::if_`] over the two runs taken as lists. Otherwise the
    /// test and the runs that are not the tail are consumed.
    ///
    /// Its cost: that of the rule; counted as one step, and what `runs`
    /// counts for the statements it releases and takes (one per node
    /// released, one per statement moved into the guard's list); a
    /// negation stripped is O(1) and counts no step. The tail is not
    /// scanned and not moved: of a run that is kept, the empty blocks it
    /// noted are dropped ([`Runs::trim`]) and at most [`Runs::last`] and
    /// [`Runs::only`] are asked. No allocation in a warm unit. (T6x-a:
    /// `cond.rs::if_in_place`, the one call of `norm::simplify_if_head`
    /// from the lowering.)
    fn if_head<R: Runs<Self>>(
        &mut self,
        a: &mut Pools,
        runs: &mut R,
        test: &mut Self::E,
        yes: &mut R::Run,
        no: &mut R::Run,
    ) -> Option<IfHead<Self::S, R::Run>>
    where
        Self: Sized;
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
