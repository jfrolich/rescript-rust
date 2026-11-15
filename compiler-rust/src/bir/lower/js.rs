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
//!
//! Slice T6k builds the bodies of `Rows`. Until then this module is
//! compiled for tests and its tests are ignored as "T6k build".
use crate::bir::{Bir, ConstId, FuncId, ImportId, JsId, NodeId, StrId, VarId};
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

/// The expression half of the interface.
pub trait Js {
    /// An expression in flight. Not `Copy`.
    type E;
    /// A node read by reference: the node of a handle, or an operand of a
    /// node read by reference. At most 16 bytes.
    type Ref<'r>: Copy
    where
        Self: 'r;

    // ---- The transition (deleted by T6x with their last call) ----

    /// The handle of a J row built outside the interface. O(1).
    fn from_node(node: NodeId) -> Self::E;
    /// The J row of a handle, for a caller that is not converted. O(1).
    fn node(e: Self::E) -> NodeId;
    /// The reference of a J row built outside the interface. O(1).
    fn at<'r>(node: NodeId) -> Self::Ref<'r>;

    // ---- The implementation ----

    /// Room for `operands` pending operands: at most one allocation, none
    /// when the capacity is there.
    fn reserve(&mut self, operands: usize);
    /// Unit operations so far: one per function of this trait that builds,
    /// takes apart, copies or releases, and one per operand of a list
    /// constructor, of [`Js::unpack_rev`], and per node [`Js::copy`] and
    /// [`Js::release`] visit. A reader counts nothing. O(1).
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
    /// interpolation (its cooked text; `None` when it has none, as
    /// `State::primitive_string` reads it today).
    /// O(1).
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

    // ---- Leaves (plain; O(1) unless said) ----

    /// A reference to `var`. Counts the occurrence and records its site.
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
    /// `new callee(operands since mark)`. One step per operand.
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
    /// step per operand.
    fn object(&mut self, a: &mut Pools, mark: Mark, info: JsId) -> Self::E;
    /// A JSX element with the header `info`. One step per operand.
    fn jsx(&mut self, a: &mut Pools, mark: Mark, info: JsId, has_children: bool) -> Self::E;

    // ---- Taking apart, copying, releasing ----

    /// Operand `index` of `e`; the node and its other operands are
    /// released. One step, and one per node released.
    fn keep_operand(&mut self, a: &mut Pools, e: Self::E, index: u32) -> Self::E;
    /// The operands of `e` pushed onto the operand stack last operand
    /// first, so that [`Js::pop`] gives them in order; the node itself is
    /// released. Returns their number. One step per operand.
    fn unpack_rev(&mut self, a: &mut Pools, e: Self::E) -> u32;
    /// A copy of the node `r` and everything below it
    /// (`Bir::copy_subtree` without a renaming: the binders inside it are
    /// fresh). One step per node copied.
    fn copy(&mut self, a: &mut Pools, r: Self::Ref<'_>) -> Self::E;
    /// A new leaf with the kind, `aux` and payload of the leaf `r` and none
    /// of its cold data ([`Js::copy_cold`] gives that). O(1). Panics when
    /// `r` has an operand.
    fn copy_leaf(&mut self, a: &mut Pools, r: Self::Ref<'_>) -> Self::E;
    /// `e` is not used: its references and sites are given back. One step
    /// per node released.
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
