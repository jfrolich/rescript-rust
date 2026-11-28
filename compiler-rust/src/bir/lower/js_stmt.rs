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
use crate::bir::{FuncId, StrId, SwitchId, VarId};
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
    /// `Switch`. `None` for every other statement. O(1). The reference
    /// borrows the statement and not the pools, so that the value of a
    /// statement the caller holds can be given to a function that takes
    /// the pools mutably ([`Js::copy_members`], [`Js::copy_leaf`]).
    fn value_of<'r>(&self, a: &Pools, s: &'r Self::S) -> Option<Self::Ref<'r>>;

    /// Whether the statement has a source location. O(1). (T6o.)
    fn stmt_located(&self, a: &Pools, s: &Self::S) -> bool;
    /// The id of the statement, read in place: what [`Js::owner`] gives for
    /// its value, the id it has once a block holds it, and a key for
    /// [`Js::kind_of`]. It does not change while
    /// the statement lives, and no other live statement has it. O(1): on
    /// rows the row; on the builder the `node_id` of the owned node, one
    /// load. (T6x-a: the statement stack keys its empty-block table by it,
    /// since a slot is reused; `export.rs::row_of` keys its table by the
    /// id of each row's statement.)
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
    /// reader). Panics on a statement that is not a `Block`. Compiled for
    /// tests since T6x-e3: `export.rs::build_rows` reads a block with
    /// [`JsStmt::block_len`] and [`JsStmt::with_block_stmt`].
    #[cfg(test)]
    fn block_ids(&self, a: &Pools, s: &Self::S, sink: impl FnMut(u32));
    /// The number of statements of the block statement `block`, one that
    /// [`JsStmt::take_block_stmt`] took out counted: the bound of the
    /// indexes the three functions below take. O(1); counts no step (a
    /// reader). Panics on a statement that is not a `Block`. (THREE_TREES
    /// 11.4, "T6x-e and T6x-f: the fold reads where its rows are",
    /// decision 3: `export.rs::build_rows`.)
    fn block_len(&self, a: &Pools, block: &Self::S) -> u32;
    /// Statement `index` of the block statement `block`, read where it is:
    /// `read` is given it by reference, as [`JsStmt::with_stmt_at`] gives a
    /// statement of a list in flight, and what it returns is returned. A
    /// block the statement stack holds is not a list in flight: its
    /// statements are its own and stay in it. The caller holds `block`;
    /// the block owns the statement. A reference into the statement
    /// ([`JsStmt::value_of`]) does not outlive `read`.
    ///
    /// O(1) and whatever `read` costs: the statement is found by its
    /// position, and no other statement of the block is read. Counts no
    /// step; allocates nothing. Panics on a statement that is not a
    /// `Block`, when `index` is not below [`JsStmt::block_len`], and on a
    /// statement that was taken out. (Decision 3: `export.rs`, every read
    /// of a row that stands in a block of the top level.)
    fn with_block_stmt<R>(&self, a: &Pools, block: &Self::S, index: u32, read: impl FnOnce(&Self::S) -> R) -> R;
    /// Statement `index` of the block statement `block`, lent to `edit`
    /// with the implementation and the pools, so that `edit` may call a
    /// function that takes them mutably (a copy of its value, a reader
    /// that counts steps, [`JsStmt::substitute`], this function again for
    /// a block inside the block); what `edit` returns is returned. `edit`
    /// may not put another statement in its place. The caller holds
    /// `block`; the block owns the statement.
    ///
    /// O(1) and whatever `edit` costs; counts no step; allocates nothing.
    /// Panics as [`JsStmt::with_block_stmt`] does. (Decision 3:
    /// `export.rs`, a row nested in a block when `JsStmt::effect_free`, a
    /// copy or a substitution reads it.)
    fn lend_block_stmt<R>(
        &mut self,
        a: &mut Pools,
        block: &mut Self::S,
        index: u32,
        edit: impl FnOnce(&mut Self, &mut Pools, &mut Self::S) -> R,
    ) -> R;
    /// Statement `index` of the block statement `block` moved out, to the
    /// caller, who owns it from here. The block keeps a hole at `index`:
    /// the indexes of the statements after it do not change. A block with
    /// a hole is given to nothing but this function, the two readers
    /// above for its other statements, [`JsStmt::block_len`] and
    /// [`JsStmt::release_stmt`], which releases what the block still
    /// holds: it is never given to a list or a constructor, so a hole is
    /// never printed. One step (it takes a node apart); O(1). On rows the
    /// statement is detached and its entry stays in the block's list; an
    /// implementation that owns its nodes leaves an empty statement in the
    /// slot, which costs one node of its arena for each statement taken.
    /// Panics on a statement that is not a `Block`, when `index` is not
    /// below [`JsStmt::block_len`], and on a hole. (Decision 3:
    /// `export.rs::coerced_list`, the statements of a block it dissolves
    /// and a removed row of one.)
    fn take_block_stmt(&mut self, a: &mut Pools, block: &mut Self::S, index: u32) -> Self::S;
    /// Replace references to the variable `var` inside the statement `s`,
    /// which the caller holds, each by what `make` gives: at most `uses`
    /// of them, and the walk stops at the last. Returns the number
    /// replaced. A reference is a `Var` node of exactly `var` (a copy of
    /// the variable is another variable); what replaces it is not entered.
    /// `make` is called once per reference replaced, with the
    /// implementation and the pools, and gives a detached expression,
    /// which is consumed. The statement stays where it is and keeps its
    /// id. The facts of the nodes above a replaced reference are those of
    /// the implementation's own replacement (on rows `Bir::replace`); the
    /// caller replaces a strictly pure reference by a strictly pure
    /// expression. The caller substitutes only a variable that is never
    /// assigned (the export fold moves no declaration of
    /// `LetKind::Variable`): what an implementation does with a
    /// reference that is the target of an assignment is not specified
    /// (rows replace it as any other `Var`; the builder passes it), and
    /// a caller that knows how many references the statement holds
    /// checks the number returned against it.
    ///
    /// One step per node of the statement the walk reads, until the last
    /// reference replaced: O(nodes of the statement) for one call. A
    /// caller that substitutes k variables in one statement of n nodes
    /// pays k times n. Allocates nothing once the implementation's work
    /// stack has the statement's width and depth. (Decision 6:
    /// `export.rs::substitute_after`, for each later row that holds a use
    /// of a moved variable.)
    fn substitute(
        &mut self,
        a: &mut Pools,
        s: &mut Self::S,
        var: VarId,
        uses: u32,
        make: impl FnMut(&mut Self, &mut Pools) -> Self::E,
    ) -> u32;
    /// The variable the declaration whose statement has the id `id` binds
    /// its own to: the variable of its initialiser when that is a
    /// reference, `None` for a declaration without one or with any other
    /// initialiser and for a statement that is no `Declare`. `id` is a key
    /// (a variable's binder, `JsStmt::stmt_id`): the fact is the
    /// implementation's, kept where the declaration is made, and the node
    /// is not handed out. O(1) on rows; on an implementation that owns its
    /// nodes a search among the declarations whose initialiser is a
    /// reference, O(log of their number). Counts no step. (Decision 7:
    /// `export.rs::alias_of`, a variable no row declares.)
    fn alias_at(&self, a: &Pools, id: u32) -> Option<VarId>;
    /// The calls a `return` ends in when the flatten pass has split its
    /// value (THREE_TREES 11.4, "T4c design" (a)): of the value of the
    /// `Return` that is statement `index` of the list in flight `list`,
    /// both branches of a conditional, the last operand of a sequence, and
    /// a call whose callee is a reference to a variable. `visit` is given
    /// the pools, the variable called and the id of the call (a key), once
    /// per such call, a then-branch before its else-branch. `last` says
    /// that the `return` is the last statement of its list: a call that is
    /// the whole value, or the end of a sequence that is, is given only
    /// then; below a conditional every such call is given (the flatten
    /// pass gives each branch a list of its own). The statement stays in
    /// the list. Returns the number of nodes read.
    ///
    /// One read per conditional and sequence between the value and its
    /// calls and one per node they end in: a test, the head of a sequence
    /// and the arguments of a call are not read. Counts no step (a reader;
    /// the caller counts the number returned). The walk is the
    /// implementation's, over its own work stack (a reference cannot be
    /// kept across calls of `visit`): no recursion on the depth of the
    /// value, and nothing allocated once the stack has held a value whose
    /// conditionals nest as deep. Panics when `index` is not below
    /// [`JsStmt::len`] and on a statement that is not a `Return`.
    /// (THREE_TREES 11.4, "T6r: the naming replay behind the interface",
    /// decision 5: `close::decide`, the return arm.)
    fn return_calls(
        &mut self,
        a: &mut Pools,
        list: Self::L,
        index: u32,
        last: bool,
        visit: impl FnMut(&mut Pools, VarId, u32),
    ) -> u32;
    /// The variable the statement binds: that of a `Declare` or a `Rest`,
    /// the variable of a range loop (with or without a first value: the
    /// loop names it) and of a loop over an iterable, the exception of a
    /// `Try` that has a handler. `None` for every other statement, a range
    /// loop over an existing variable too (it binds nothing). O(1): on
    /// rows one read of the row; on an implementation that owns its nodes
    /// the statement's row of facts (`emit::row::Row::payload`), no node.
    /// Counts no step. (THREE_TREES 11.4, "T6r: the naming replay behind
    /// the interface", decision 7: `names.rs`, `Replay::statement`, the
    /// binder a statement names before its literals and lists, and the
    /// catch variable `Replay::child` names between the body and the
    /// handler of a `try`.)
    fn binder(&self, a: &Pools, s: &Self::S) -> Option<VarId>;
    /// The status a `Declare` or a `Rest` carries: its `UsedStats` as a
    /// number (`js_ir::op::UsedStats`), which says whether the printer
    /// omits the declaration, writes its value alone or writes it with its
    /// binder. It is not part of [`JsStmt::stmt_aux`], which gives the
    /// `LetKind` alone. O(1): on rows the bits of the row's `aux` above
    /// the kind; on an implementation that owns its nodes the same bits of
    /// the statement's row of facts. Counts no step. Panics on a statement
    /// that is neither. (THREE_TREES 11.4, "T6r: the naming replay behind
    /// the interface", decision 7: `names.rs`, `Replay::declaration`.)
    fn status(&self, a: &Pools, s: &Self::S) -> u8;
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
