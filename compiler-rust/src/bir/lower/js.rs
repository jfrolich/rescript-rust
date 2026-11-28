//! The lowering's interface to the JavaScript it writes (THREE_TREES 11.4,
//! "T6: the interface"): the expression half. The statement half is
//! `JsStmt` (T6l).
//!
//! The lowering names no J opcode. It calls a function of [`Js`], gets a
//! handle, and gives the handle to the function that attaches it. A handle
//! is not `Copy`: the function it is given to consumes it. What stands
//! behind the trait is one of two implementations, chosen where the
//! lowering is instantiated and never at run time:
//!
//! - `bir::j::rows::Rows`, until the flip: J rows of the lowering's `Bir`,
//!   written by the calls of `bir/j/plain.rs` and `bir/j/norm.rs` the
//!   lowering makes today;
//! - the builder over oxc nodes (`emit/builder.rs` and the rules of phase
//!   B), from T6v for tests and from T6s for check mode.
//!
//! Nothing is stored between a call and the nodes it writes.
//!
//! # The two families
//!
//! A *plain* function builds the node it is asked for. A *rule* function is
//! a row of BACKEND_LOWERING 6 and may return an operand, a literal or
//! another node; its cost is the row's. The lowering chooses the family
//! where it chooses `plain::` or `norm::` today.
//!
//! # Reading
//!
//! A node is read through a reference ([`Js::Ref`], `Copy`) taken from a
//! handle with [`Js::of`] or from another reference with [`Js::operand`].
//! Every reader is O(1) unless its comment says otherwise; none walks.
//!
//! # Operand lists
//!
//! The operands of a call, a literal or a template go through the operand
//! stack of the implementation: take a [`Mark`], [`Js::push`] the handles,
//! give the mark to the constructor. [`Js::unpack_rev`] is the way back.
//!
//! # The pools
//!
//! `Pools` is the lowering's arena of pools and variables (a `Bir` until
//! the flip). It is a parameter of every function, beside the
//! implementation, so that a call borrows two fields of the lowering's
//! state and not the state.
use crate::bir::{Bir, ConstId, FuncId, ImportId, JsId, StrId, VarId};
use crate::emit::row::Kind;
use crate::js_ir::BinOp;
use crate::js_ir::arena::FieldPos;
use crate::js_ir::op::LengthObject;
use crate::lambda::LamLoc;

/// The lowering's pools and variables.
pub type Pools = Bir;

/// Where the operands of the next list constructor start on the operand
/// stack ([`Js::mark`]). 4 bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Mark(pub(crate) u32);

/// What [`Js::references`] finds below an expression: a reference to a
/// variable or to an imported module with the id of its node (a key: what
/// [`Js::owner`] climbs from), or a function literal, which is not
/// entered. 12 bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Found {
    /// A reference to a variable.
    Var {
        /// The variable.
        var: VarId,
        /// The id of the reference.
        id: u32,
    },
    /// A reference to an imported module or to a member of one.
    Module {
        /// The module.
        module: ImportId,
        /// The id of the reference.
        id: u32,
    },
    /// A function literal, by its header.
    Function(FuncId),
}

/// Which of the two leading operands of a JSX element a node is
/// ([`Js::jsx_head`]). One byte.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum JsxHead {
    /// The runtime function the element calls when it is not printed as
    /// JSX.
    Callee,
    /// The tag.
    Tag,
}

/// The expression half of the interface.
pub trait Js {
    /// An expression in flight. Not `Copy`.
    type E;
    /// A node read by reference: the node of a handle, or an operand of a
    /// node read by reference. At most 16 bytes.
    type Ref<'r>: Copy
    where
        Self: 'r;

    // ---- The implementation ----

    /// Room for `operands` pending operands: at most one allocation, none
    /// when the capacity is there.
    fn reserve(&mut self, operands: usize);
    /// Unit operations so far: one per function of this trait that builds
    /// or takes apart, one per operand of a list constructor and of
    /// [`Js::unpack_rev`], one per node [`Js::copy`] copies, and one per
    /// node released ([`Js::release`], [`Js::drop_operands`],
    /// [`Js::keep_operand`]). A reader counts nothing. O(1).
    fn steps(&self) -> u64;

    // ---- Reading ----

    /// The reference of a handle's node. O(1).
    fn of<'r>(e: &'r Self::E) -> Self::Ref<'r>;
    /// The id of the node: the key of a mark or a site. O(1).
    fn id(&self, a: &Pools, r: Self::Ref<'_>) -> u32;
    /// The J-level kind. O(1).
    fn kind(&self, a: &Pools, r: Self::Ref<'_>) -> Kind;
    /// Whether the node has every flag of `flags` (`emit::row::flag`:
    /// `PURE`, `STRICT`, `DELAY_SAFE`, `SUBEXPR`, `DUPLICABLE`). O(1).
    fn has(&self, a: &Pools, r: Self::Ref<'_>, flags: u16) -> bool;
    /// The `aux` of the node's kind, as [`Kind`] documents it: the `BinOp`
    /// of a `Bin`, the value of a `Bool`, the unit bit of an `Undefined`,
    /// the tag bit of a `Dot`, the mutability of an `Array` or a
    /// `BlockLit`, the identity bit of an `Optional`, the literal bit of a
    /// `Template`, the statement bit of a `Raw`, the children bit of a
    /// `Jsx`. Not defined for a `Number` (read it with [`Js::int`],
    /// [`Js::is_float`], [`Js::bigint`]) and for a `Var`. O(1).
    fn aux(&self, a: &Pools, r: Self::Ref<'_>) -> u8;
    /// The value of an integer or character literal. O(1).
    fn int(&self, a: &Pools, r: Self::Ref<'_>) -> Option<i32>;
    /// Whether the node is a float literal. O(1).
    fn is_float(&self, a: &Pools, r: Self::Ref<'_>) -> bool;
    /// The sign and digits of a bigint literal, as the constant pool spells
    /// them (`+12`, `-0`). O(1).
    fn bigint<'r>(&self, a: &'r Pools, r: Self::Ref<'r>) -> Option<&'r str>;
    /// The text of a string literal, or of a template literal without
    /// interpolation (its cooked text; `None` when it has none). O(1).
    fn text<'r>(&self, a: &'r Pools, r: Self::Ref<'r>) -> Option<&'r str>;
    /// The variable of a reference. O(1).
    fn var_of(&self, a: &Pools, r: Self::Ref<'_>) -> Option<VarId>;
    /// The module and member of a module reference. O(1).
    fn qualified_of(&self, a: &Pools, r: Self::Ref<'_>) -> Option<(ImportId, Option<StrId>)>;
    /// The name and position of a member read. O(1).
    fn member_of(&self, a: &Pools, r: Self::Ref<'_>) -> Option<(StrId, FieldPos)>;
    /// The header of a function literal. O(1).
    fn function_of(&self, a: &Pools, r: Self::Ref<'_>) -> Option<FuncId>;
    /// The `JsId` of a call, an object, a block, a template, a tagged
    /// template, a JSX element or a record rest. O(1).
    fn info_of(&self, a: &Pools, r: Self::Ref<'_>) -> Option<JsId>;
    /// The number of operands. O(1).
    fn arity(&self, a: &Pools, r: Self::Ref<'_>) -> u32;
    /// Operand `index`, in the order of the node's fields in
    /// `bir/node.rs` (a call: the callee, then the arguments). O(1).
    /// Panics when `index` is not below [`Js::arity`].
    fn operand<'r>(&self, a: &'r Pools, r: Self::Ref<'r>, index: u32) -> Self::Ref<'r>;
    /// Whether the node has a source location. O(1).
    fn located(&self, a: &Pools, r: Self::Ref<'_>) -> bool;
    /// A:90 `runs_no_code`. One step per member of a chain of field reads
    /// with a position, to its base.
    fn runs_no_code(&self, a: &Pools, r: Self::Ref<'_>) -> bool;
    /// The interned text of a string literal; `None` for any other node, a
    /// template too. O(1): no text is read or interned. (T6m: the key of
    /// a pair in `Pmakedict` becomes a property key.)
    fn str_of(&self, a: &Pools, r: Self::Ref<'_>) -> Option<StrId>;

    // ---- Reading by id (T6q: `export.rs` climbs from a site) ----

    /// The id of the node that `id` is an operand of, or of the statement
    /// that holds it; `None` for a node nothing holds. `id` is an
    /// expression's or a statement's ([`Js::id`], a site's node, a
    /// variable's binder). O(1).
    fn owner(&self, a: &Pools, id: u32) -> Option<u32>;
    /// The kind of the node `id`, an expression's or a statement's. O(1).
    fn kind_of(&self, a: &Pools, id: u32) -> Kind;
    /// Whether the node `id` is what its owner calls: the callee of a
    /// call, of a `new` or of a flat call, or the tag of a tagged
    /// template. O(1): one read of the owner, no scan of its operands.
    fn is_callee(&self, a: &Pools, id: u32) -> bool;
    /// When the node `id` is the runtime callee or the tag of a JSX element
    /// (its first or its second operand): which of the two, and the
    /// element's information. `None` for any other node, an operand of a
    /// JSX element after its second too. `id` is a key ([`Js::id`], the top
    /// of a climb with [`Js::owner`]); the element is not handed out. O(1):
    /// one read of the owner and two comparisons, no scan of its operands;
    /// counts no step. An implementation that owns its nodes writes the
    /// fact beside the owner where the element is built. (THREE_TREES
    /// 11.4, "T6r: the naming replay behind the interface", decision 4:
    /// `names.rs`, `Log::unprinted`, the top of the climb from a reference
    /// in a unit that preserves JSX.)
    fn jsx_head(&self, a: &Pools, id: u32) -> Option<(JsxHead, JsId)>;
    /// One above the largest id a node of the unit has now: the size of a
    /// table indexed by id. O(1). (T6q: `export.rs::row_of`.)
    fn id_bound(&self, a: &Pools) -> u32;
    /// B:237 `ocaml_eq_expression`: whether two expressions are equal as
    /// the rules of J compare them. Deliberately partial: a kind it does
    /// not know is unequal to itself. One step per pair of nodes it
    /// inspects, the mismatching pair included, added to `steps`; bounded
    /// by the smaller of the two trees; stops at the first mismatch.
    /// (T6q: `export.rs::equivalent_later`.)
    fn equal(&self, a: &Pools, left: Self::Ref<'_>, right: Self::Ref<'_>, steps: &mut usize) -> bool;

    // ---- Leaves (plain; O(1) unless said) ----
    //
    // A leaf constructor leaves the operand stack alone: it does not read
    // it and does not change it, so a leaf may be made between two pushes
    // and between two pops of a list being collected or taken apart.

    /// A reference to `var`. Counts the occurrence and records its site.
    /// The node is strictly pure (`STRICT`) as built, on every
    /// implementation: the lowering does not mark it with `assume_strict`.
    fn var(&mut self, a: &mut Pools, var: VarId) -> Self::E;
    /// An imported module, or `member` of it. Counts the import's use and
    /// records the site.
    fn qualified(&mut self, a: &mut Pools, module: ImportId, member: Option<StrId>) -> Self::E;
    /// An integer literal.
    fn int_literal(&mut self, a: &mut Pools, value: i32) -> Self::E;
    /// The number literal of a constant (an integer, a float, a bigint).
    fn number(&mut self, a: &mut Pools, value: ConstId) -> Self::E;
    /// A string literal. O(length): the text is interned.
    fn string(&mut self, a: &mut Pools, text: &str) -> Self::E;
    /// A string literal of an interned text.
    fn str(&mut self, a: &mut Pools, text: StrId) -> Self::E;
    /// A boolean literal.
    fn boolean(&mut self, a: &mut Pools, value: bool) -> Self::E;
    /// `null`.
    fn null(&mut self, a: &mut Pools) -> Self::E;
    /// `undefined`; `unit` marks the unit value.
    fn undefined(&mut self, a: &mut Pools, unit: bool) -> Self::E;
    /// A JSON literal.
    fn json(&mut self, a: &mut Pools, text: StrId) -> Self::E;
    /// Raw JavaScript; `statement` says it stands as a statement.
    fn raw(&mut self, a: &mut Pools, text: StrId, statement: bool) -> Self::E;

    // ---- Operators and members (plain; O(1)) ----

    /// `left op right`, as given (not J-E4).
    fn bin_plain(&mut self, a: &mut Pools, op: BinOp, left: Self::E, right: Self::E) -> Self::E;
    /// `first, second`, as given (not J-M1).
    fn seq(&mut self, a: &mut Pools, first: Self::E, second: Self::E) -> Self::E;
    /// `typeof value`, as given (not J-M9).
    fn typeof_plain(&mut self, a: &mut Pools, value: Self::E) -> Self::E;
    /// `left in right`.
    fn in_(&mut self, a: &mut Pools, left: Self::E, right: Self::E) -> Self::E;
    /// `object[index]`.
    fn index(&mut self, a: &mut Pools, object: Self::E, index: Self::E) -> Self::E;
    /// `object.name`; `position` is the field's position in its block,
    /// `tag` says the read is of a block's tag.
    fn dot(&mut self, a: &mut Pools, object: Self::E, name: StrId, position: FieldPos, tag: bool) -> Self::E;
    /// `await value`.
    fn await_(&mut self, a: &mut Pools, value: Self::E) -> Self::E;
    /// `...value`.
    fn spread(&mut self, a: &mut Pools, value: Self::E) -> Self::E;
    /// `Some(value)`; `identity` says it prints as its value.
    fn optional(&mut self, a: &mut Pools, value: Self::E, identity: bool) -> Self::E;
    /// The record rest of `value` with the descriptor `info`.
    fn record_rest(&mut self, a: &mut Pools, value: Self::E, info: JsId) -> Self::E;
    /// `callee(...args)`, `args` one array expression.
    fn flat_call(&mut self, a: &mut Pools, callee: Self::E, args: Self::E) -> Self::E;

    // ---- Operand lists ----

    /// The operands pushed from here on belong to the next list
    /// constructor. O(1).
    fn mark(&self) -> Mark;
    /// One operand of the list being collected. O(1): a move.
    fn push(&mut self, operand: Self::E);
    /// The last operand pushed. O(1). Panics on an empty stack.
    fn pop(&mut self) -> Self::E;
    /// `callee(operands since mark)` with the call information `info`. One
    /// step per operand.
    fn call(&mut self, a: &mut Pools, callee: Self::E, mark: Mark, info: JsId) -> Self::E;
    /// `new callee(operands since mark)`: the argument list is present,
    /// with no operand too. One step per operand.
    fn new_(&mut self, a: &mut Pools, callee: Self::E, mark: Mark) -> Self::E;
    /// `tag` applied to the template `info` with the operands since mark.
    /// One step per operand.
    fn tagged(&mut self, a: &mut Pools, tag: Self::E, mark: Mark, info: JsId) -> Self::E;
    /// An array literal of the operands since mark; `mutability` is the
    /// `aux` of [`Kind::Array`]. One step per operand.
    fn array(&mut self, a: &mut Pools, mark: Mark, mutability: u8) -> Self::E;
    /// A block literal with the tag information `info`. One step per
    /// operand.
    fn block(&mut self, a: &mut Pools, mark: Mark, info: JsId, mutability: u8) -> Self::E;
    /// An object literal whose keys are `info`, in the operands' order. One
    /// step per operand. Panics when the operands are not as many as the
    /// keys.
    fn object(&mut self, a: &mut Pools, mark: Mark, info: JsId) -> Self::E;
    /// A JSX element with the header `info`, its callee given apart from
    /// its operands, as [`Js::call`] takes a callee: `callee`, then the
    /// operands since `mark` (the tag and what the header counts: a
    /// spread, the properties, the children, a key). The lowering builds
    /// the callee after the operands (built earlier, its module would be
    /// registered before the key's runtime module), so it pushes each
    /// operand as it is converted and gives the callee here. One step, and
    /// one per operand, the callee counted as one. On rows the callee is
    /// put below the operands on the stack, which moves each operand once
    /// (4 bytes), and the list is written once; an implementation that
    /// owns its nodes moves
    /// `callee` into the element and the operands off its stack, and moves
    /// nothing twice. No allocation once the operand stack has its
    /// capacity. Panics when the operands are not the tag and what the
    /// header counts. (THREE_TREES 11.4, "T6x-e and T6x-f: the fold reads
    /// where its rows are", decision 1: `jsx.rs::compile_jsx`.)
    fn jsx_element(&mut self, a: &mut Pools, callee: Self::E, mark: Mark, info: JsId, has_children: bool) -> Self::E;

    // ---- Taking apart, copying, releasing ----

    /// Operand `index` of `e`; the node and its other operands are
    /// released. One step, and one per node released.
    fn keep_operand(&mut self, a: &mut Pools, e: Self::E, index: u32) -> Self::E;
    /// The operands of `e` pushed onto the operand stack last operand
    /// first, so that [`Js::pop`] gives them in order; the node itself is
    /// released. Returns their number. One step, and one per operand.
    fn unpack_rev(&mut self, a: &mut Pools, e: Self::E) -> u32;
    /// The operands of `e` moved onto the operand stack last operand
    /// first, as [`Js::unpack_rev`], but the node stays: `e` is a node
    /// without operands, to be given to [`Js::refill`] or released and to
    /// nothing else. Returns their number. One step, and one per operand.
    /// (T6p: `args.rs`, a literal or a member callee whose operands are
    /// held in variables.)
    fn take_operands(&mut self, a: &mut Pools, e: &mut Self::E) -> u32;
    /// The node `e` over the operands pushed since `mark` in place of the
    /// ones [`Js::take_operands`] took: the same kind, `aux`, call
    /// information, location, comment and character; plain (no rule), its
    /// facts those the plain constructor of its kind computes. `e` is
    /// released. One step. Defined for an `Optional`, an `Array`, a
    /// `BlockLit`, an `Object` and a `Dot`; panics on any other kind and
    /// when the number of operands differs from the number taken.
    fn refill(&mut self, a: &mut Pools, e: Self::E, mark: Mark) -> Self::E;
    /// A copy of the node `r` and everything below it
    /// (`Bir::copy_subtree` without a renaming: the binders inside it are
    /// fresh and not reported; [`Js::copy_fresh`] reports them). One step
    /// per node copied; allocates nothing once the implementation's copy
    /// storage has its capacity and the tree has no binder.
    fn copy(&mut self, a: &mut Pools, r: Self::Ref<'_>) -> Self::E;
    /// [`Js::copy`] that reports the binders it freshened: `(fresh,
    /// source)` is appended to `fresh` for each, in the order the fresh
    /// variables were made, so that the caller gives each fresh variable
    /// its identifier. One step per node copied; allocates nothing once
    /// the implementation's copy storage and `fresh` have their capacity.
    /// (T6o: `untagged.rs`, a scrutinee that is not a variable.)
    fn copy_fresh(&mut self, a: &mut Pools, r: Self::Ref<'_>, fresh: &mut Vec<(VarId, VarId)>) -> Self::E;
    /// A new leaf with the kind, `aux` and payload of the leaf `r` and none
    /// of its cold data ([`Js::copy_cold`] gives that). O(1). Panics when
    /// `r` has an operand.
    fn copy_leaf(&mut self, a: &mut Pools, r: Self::Ref<'_>) -> Self::E;
    /// A copy of a chain of member reads: of the reads from `r` down to
    /// the first node that is not one (a `Dot` of any position, a tag read
    /// too) and of that node, which is a leaf. It is [`Js::copy_leaf`] of
    /// the leaf, then one [`Js::dot`] per read from the innermost out with
    /// the name, position and tag bit of its original, and each node is
    /// given the cold data of its original ([`Js::copy_cold`]) as it is
    /// made. No flag is set beyond what those constructors set. `made` is
    /// given the id of each node made, in that order: a key (the caller
    /// forgets what a table indexed by id held for a slot the
    /// implementation reused), never a way back to the node. The walk is
    /// the implementation's because a reference taken with [`Js::operand`]
    /// borrows the pools and cannot be held across the constructors. `r`
    /// is the caller's node and stays whole; the copy is the caller's.
    ///
    /// One step per node made (the leaf and each read), what `copy_leaf`
    /// and `dot` count; the chain is read once more to find its leaf,
    /// which counts nothing. Allocates nothing once the implementation's
    /// work stack has the chain's depth. Panics when the leaf has an
    /// operand. (THREE_TREES 11.4, "T6x-e and T6x-f: the fold reads where
    /// its rows are", decision 2: `jsx.rs::duplicate_jsx_key` and
    /// `export.rs::copy_replacement`.)
    fn copy_members(&mut self, a: &mut Pools, r: Self::Ref<'_>, made: impl FnMut(u32)) -> Self::E;
    /// Every reference and every function literal at or below `e`, each
    /// given to `visit` once with the implementation, to read by key
    /// ([`Js::owner`], [`Js::kind_of`], [`Js::jsx_head`]), and with the
    /// pools: a reference to a variable, a
    /// reference to an imported module, the header of a function literal.
    /// A function literal is not entered. `e` is the caller's and is not
    /// changed; `visit` may write the pools (the lowering's tables), not
    /// the nodes. The order of the visits is the implementation's (the
    /// caller builds a set). Returns the number of nodes read.
    ///
    /// One read per node at or below `e` outside function literals:
    /// O(nodes); counts no step (a reader; the caller counts the number
    /// returned). The walk is the implementation's, over its own work
    /// stack, because a reference taken with [`Js::operand`] borrows the
    /// pools and cannot be kept across calls of `visit`: no recursion on
    /// the depth of the expression. Allocates nothing once that stack has
    /// the expression's width and depth. (THREE_TREES 11.4, "T6r: the
    /// naming replay behind the interface", decision 5: `names::adopt`,
    /// an expression built before the scope it moves into opened.)
    fn references(&mut self, a: &mut Pools, e: &Self::E, visit: impl FnMut(&Self, &mut Pools, Found)) -> u32;
    /// `e` is not used: its references and sites are given back. One step
    /// per node released. The operand stack is not read and not changed:
    /// operands pushed before the call are there after it, in order.
    fn release(&mut self, a: &mut Pools, e: Self::E);
    /// The operands since `mark` are not used. One step per node released.
    fn drop_operands(&mut self, a: &mut Pools, mark: Mark);

    // ---- Facts the caller knows, and cold data (O(1)) ----

    /// The caller knows `e` is strictly pure (E:15) by how it was built:
    /// what `bir::j::pure_expression` asserts today.
    fn assume_strict(&mut self, a: &mut Pools, e: &mut Self::E);
    /// Give `e` the source location `loc`.
    fn locate(&mut self, a: &mut Pools, e: &mut Self::E, loc: LamLoc);
    /// Give `e` the comment `text`. The builder keeps no decoration
    /// comment; a pure annotation is the call information's.
    fn comment(&mut self, a: &mut Pools, e: &mut Self::E, text: StrId);
    /// Give `to` the location, comment and character of `from`, where
    /// `from` has them.
    fn copy_cold(&mut self, a: &mut Pools, from: Self::Ref<'_>, to: &mut Self::E);

    // ---- The rules of BACKEND_LOWERING 6 (each: the row's cost) ----

    /// J-E1 `string_append`.
    fn append(&mut self, a: &mut Pools, left: Self::E, right: Self::E) -> Self::E;
    /// J-E2 `length`.
    fn length(&mut self, a: &mut Pools, value: Self::E, of: LengthObject) -> Self::E;
    /// J-E3 `is_null_or_undefined`.
    fn is_nullish(&mut self, a: &mut Pools, value: Self::E) -> Self::E;
    /// J-E4 `bin` (which reaches J-E5 and J-E6 for `&&` and `||`).
    fn bin(&mut self, a: &mut Pools, op: BinOp, left: Self::E, right: Self::E) -> Self::E;
    /// J-E5 `js_and`.
    fn and(&mut self, a: &mut Pools, left: Self::E, right: Self::E) -> Self::E;
    /// J-E6 `js_or`.
    fn or(&mut self, a: &mut Pools, left: Self::E, right: Self::E) -> Self::E;
    /// J-E7 `cond`.
    fn cond(&mut self, a: &mut Pools, test: Self::E, then: Self::E, otherwise: Self::E) -> Self::E;
    /// J-E8 `not`.
    fn not(&mut self, a: &mut Pools, value: Self::E) -> Self::E;
    /// J-M0 `remove_pure_subexpression`: what is left of `value`, or
    /// nothing.
    fn without_pure(&mut self, a: &mut Pools, value: Self::E) -> Option<Self::E>;
    /// J-M1 `js_seq`.
    fn seq_rule(&mut self, a: &mut Pools, first: Self::E, second: Self::E) -> Self::E;
    /// J-M2 `compile_nullish_strict_comparison`; `neq` for `!==`.
    fn nullish_eq(&mut self, a: &mut Pools, neq: bool, left: Self::E, right: Self::E) -> Self::E;
    /// J-M2 `compile_int_equality`.
    fn int_eq(&mut self, a: &mut Pools, left: Self::E, right: Self::E) -> Self::E;
    /// J-M3 `to_int32`.
    fn to_int32(&mut self, a: &mut Pools, value: Self::E) -> Self::E;
    /// J-M3 `int32_bor`.
    fn int_or(&mut self, a: &mut Pools, left: Self::E, right: Self::E) -> Self::E;
    /// J-M4 `int32_add`, or `int32_minus` with `subtract`.
    fn int_add(&mut self, a: &mut Pools, subtract: bool, left: Self::E, right: Self::E) -> Self::E;
    /// J-M5 `int32_mul`.
    fn int_mul(&mut self, a: &mut Pools, left: Self::E, right: Self::E) -> Self::E;
    /// J-M6 `int32_pow`.
    fn int_pow(&mut self, a: &mut Pools, left: Self::E, right: Self::E) -> Self::E;
    /// J-M7 `int32_lsl`.
    fn int_lsl(&mut self, a: &mut Pools, left: Self::E, right: Self::E) -> Self::E;
    /// J-M8 `int32_lsr`.
    fn int_lsr(&mut self, a: &mut Pools, left: Self::E, right: Self::E) -> Self::E;
    /// J-M8 `int32_bxor`.
    fn int_xor(&mut self, a: &mut Pools, left: Self::E, right: Self::E) -> Self::E;
    /// J-M8 `int32_band`.
    fn int_and(&mut self, a: &mut Pools, left: Self::E, right: Self::E) -> Self::E;
    /// J-M9 `ocaml_typeof_expr`.
    fn typeof_(&mut self, a: &mut Pools, value: Self::E) -> Self::E;
    /// J-M10 `int_bnot`.
    fn bnot(&mut self, a: &mut Pools, value: Self::E) -> Self::E;
    /// J-M11: field `index` (named `field` in a record) of a strictly pure
    /// literal; `Err` gives the value back when the rule does not apply.
    fn project(&mut self, a: &mut Pools, value: Self::E, field: Option<&str>, index: Option<i32>) -> Result<Self::E, Self::E>;
    /// J-M11 `poly_var_tag_access`, or `poly_var_value_access` with
    /// `payload`.
    fn poly_var(&mut self, a: &mut Pools, value: Self::E, payload: bool) -> Self::E;
    /// J-M12 `interpolated_template` of `segments` and the operands since
    /// mark. One step per operand.
    fn template(&mut self, a: &mut Pools, segments: &[crate::string_literal::TemplateSegment], mark: Mark) -> Self::E;
    /// J-M13 `int32_div_expr`; `check` adds the test for zero.
    fn int_div(&mut self, a: &mut Pools, check: bool, left: Self::E, right: Self::E) -> Self::E;
    /// J-M13 `int32_mod_expr`.
    fn int_mod(&mut self, a: &mut Pools, check: bool, left: Self::E, right: Self::E) -> Self::E;
}

#[cfg(test)]
#[path = "js_tests.rs"]
mod tests;
