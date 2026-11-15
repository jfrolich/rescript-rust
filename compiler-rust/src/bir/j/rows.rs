//! The first implementation of the lowering's interface (THREE_TREES 11.4,
//! "T6: the interface" (b)): J rows of the lowering's `Bir`. Every function
//! is the call of `plain.rs`, `norm.rs` or `Bir` that the lowering makes
//! today, so the rows written are today's rows. Deleted by the flip (T6s).
//!
//! `Rows` holds the operand stack and the step count and nothing else: the
//! nodes are the pools' (`Pools` is the lowering's `Bir`).
//!
//! Slice T6k builds the bodies marked `todo!("T6k")`. The transition
//! functions, `of`, `reserve`, `steps`, `mark`, `push`, `pop` and `kind_of`
//! are the representation and are built.
//!
//! # What each body is
//!
//! | Function | Body |
//! | --- | --- |
//! | a leaf | `plain::node` with the leaf's view (`int_literal`: `plain::int`; `string`: `plain::string`; `boolean`: `plain::boolean`); `aux` is the unit bit of `undefined` and the statement bit of `raw`, 0 otherwise |
//! | `bin_plain`, `seq` | `plain::bin`, `plain::seq` |
//! | the other plain functions | `plain::node` with the view of the same name; `aux` is the tag bit of `dot`, the identity bit of `optional`, 0 otherwise |
//! | a list constructor | `plain::node` with `&self.operands[mark..]` as the list (the callee or tag is not on the stack), then the stack is cut back to the mark; `aux` is the mutability of `array` and `block` and the children bit of `jsx` |
//! | a rule function | the function of `norm.rs` named in THREE_TREES 11.4, "T6: the interface" (c); `template` gives `jm12_interpolated_template` the operands since the mark and cuts the stack back; `project` returns `Err(value)` when `jm11_projection` returns `None` (it has consumed nothing then) |
//! | `kind` | `kind_of` of the node's operation |
//! | `has` | `NodeFlags` has `PURE` 1, `STRICT` 8, `DELAY_SAFE` 16, `J_SUBEXPR` 32; the interface's bits are 1, 2, 4, 8: `(f & 1) \| ((f >> 2) & 0b1110)`. `DUPLICABLE` is `Bir::j_duplicable` of the node, read only when the flag is asked for |
//! | `aux` | the node's `aux`, truncated to 8 bits |
//! | `int` | `plain::int_of` |
//! | `text` | the text of a `JStr`; for a `JTemplate` whose `aux` is 1, the cooked text of its one part, `None` when the part has none (the body of `State::primitive_string` today; `plain::string_of` differs: it gives the empty string) |
//! | `is_float`, `bigint` | the constant of a `JNumber`: `Constant::Float`; the text of `Constant::BigInt` |
//! | `var_of`, `qualified_of`, `member_of`, `function_of`, `info_of` | the fields of the view of that kind; `None` for any other kind |
//! | `arity`, `operand` | `View::child_count`, `View::child_at` |
//! | `located` | `NodeFlags::JS_LOC_PRESENT` |
//! | `runs_no_code` | `facts::runs_no_code` |
//! | `keep_operand` | `child_at`, `Bir::detach` of the operand, `Bir::release` of the node |
//! | `unpack_rev` | for the operands from the last to the first: `detach`, push; then `release` of the node |
//! | `copy` | `Bir::copy_subtree(r, &[])` |
//! | `copy_leaf` | `plain::node` with the view and `aux` of `r`, for `Var`, `JQualified`, `JNumber`, `JStr`, `JJson`, `JRaw`, `JBool`, `JNull`, `JUndefined` and a `JTemplate` without values; a panic for any other |
//! | `release`, `drop_operands` | `Bir::release` of the node; of each operand since the mark, then the stack is cut back |
//! | `assume_strict` | `NodeFlags::STRICT` set on the node |
//! | `locate` | `Bir::set_cold` with `loc` and the comment the node has, and `JS_LOC_PRESENT` set |
//! | `comment` | `Bir::set_cold` with the comment and the location the node has (`LamLoc::NONE` when it has none); the flags are not touched |
//! | `copy_cold` | `plain::copy_cold`, then the character of `from` (`Node::js_char`) set on `to` when `from` has one |
//!
//! Steps (`Js::steps`): one for every function that builds a node, takes
//! one apart or releases one (`without_pure` and `project` too, whatever
//! they return); a list constructor, `template` and `drop_operands` one
//! more per operand since the mark; `unpack_rev` one more per operand;
//! `copy` one per node the arena grew by, at least one. A reader, `mark`,
//! `push`, `pop`, `reserve`, and the four functions of cold data and
//! `assume_strict` count nothing.
use crate::bir::lower::js::{Js, Mark, Pools};
use crate::bir::{ConstId, FuncId, ImportId, JsId, NodeId, Op, StrId, VarId};
use crate::emit::row::Kind;
use crate::js_ir::BinOp;
use crate::js_ir::arena::FieldPos;
use crate::js_ir::op::LengthObject;
use crate::lambda::LamLoc;

/// An expression in flight on J rows: the row's id. 4 bytes; not `Copy`.
#[derive(Debug, PartialEq, Eq)]
pub struct E(NodeId);

/// The J rows behind the interface. 32 bytes.
#[derive(Default)]
pub struct Rows {
    /// Operands of the list constructors, pushed by the caller.
    operands: Vec<NodeId>,
    /// [`Js::steps`].
    steps: u64,
}

/// The interface's kind of a J operation. O(1): one `match`. Panics on an
/// operation of level L other than `Var`.
pub(crate) fn kind_of(op: Op) -> Kind {
    match op {
        Op::Var => Kind::Var,
        Op::JBin => Kind::Bin,
        Op::JNot => Kind::Not,
        Op::JBnot => Kind::Bnot,
        Op::JTypeof => Kind::Typeof,
        Op::JIn => Kind::In,
        Op::JCond => Kind::Cond,
        Op::JSeq => Kind::Seq,
        Op::JCall => Kind::Call,
        Op::JFlatCall => Kind::FlatCall,
        Op::JNew => Kind::New,
        Op::JIndex => Kind::Index,
        Op::JDot => Kind::Dot,
        Op::JLength => Kind::Length,
        Op::JIsNullish => Kind::IsNullish,
        Op::JStrAppend => Kind::StrAppend,
        Op::JFun => Kind::Fun,
        Op::JObject => Kind::Object,
        Op::JArray => Kind::Array,
        Op::JBlockLit => Kind::BlockLit,
        Op::JOptional => Kind::Optional,
        Op::JJsx => Kind::Jsx,
        Op::JTemplate => Kind::Template,
        Op::JTagged => Kind::Tagged,
        Op::JRaw => Kind::Raw,
        Op::JAwait => Kind::Await,
        Op::JSpread => Kind::Spread,
        Op::JQualified => Kind::Qualified,
        Op::JNumber => Kind::Number,
        Op::JStr => Kind::Str,
        Op::JBool => Kind::Bool,
        Op::JNull => Kind::Null,
        Op::JUndefined => Kind::Undefined,
        Op::JJson => Kind::Json,
        Op::JRecordRest => Kind::RecordRest,
        Op::SBlock => Kind::Block,
        Op::SDecl => Kind::Declare,
        Op::SExp => Kind::Exp,
        Op::SIf => Kind::If,
        Op::SWhile => Kind::While,
        Op::SForRangeExisting => Kind::ForRangeExisting,
        Op::SForRange => Kind::ForRange,
        Op::SForOf => Kind::ForOf,
        Op::SForAwaitOf => Kind::ForAwaitOf,
        Op::SSwitch => Kind::Switch,
        Op::SReturn => Kind::Return,
        Op::SThrow => Kind::Throw,
        Op::STry => Kind::Try,
        Op::SBreak => Kind::Break,
        Op::SContinue => Kind::Continue,
        Op::SDebugger => Kind::Debugger,
        Op::SRest => Kind::Rest,
        other => unreachable!("{other:?} is not a J operation"),
    }
}

impl Js for Rows {
    type E = E;
    type Ref<'r> = NodeId;

    #[inline]
    fn from_node(node: NodeId) -> E {
        E(node)
    }
    #[inline]
    fn node(e: E) -> NodeId {
        e.0
    }
    #[inline]
    fn at<'r>(node: NodeId) -> Self::Ref<'r> {
        node
    }

    fn reserve(&mut self, operands: usize) {
        self.operands.reserve(operands);
    }
    #[inline]
    fn steps(&self) -> u64 {
        self.steps
    }

    #[inline]
    fn of(e: &E) -> NodeId {
        e.0
    }
    #[inline]
    fn id(&self, a: &Pools, r: NodeId) -> u32 {
        let _inputs = (a, r);
        todo!("T6k")
    }
    #[inline]
    fn kind(&self, a: &Pools, r: NodeId) -> Kind {
        let _inputs = (a, r);
        todo!("T6k")
    }
    #[inline]
    fn has(&self, a: &Pools, r: NodeId, flags: u16) -> bool {
        let _inputs = (a, r, flags);
        todo!("T6k")
    }
    #[inline]
    fn aux(&self, a: &Pools, r: NodeId) -> u8 {
        let _inputs = (a, r);
        todo!("T6k")
    }
    #[inline]
    fn int(&self, a: &Pools, r: NodeId) -> Option<i32> {
        let _inputs = (a, r);
        todo!("T6k")
    }
    #[inline]
    fn is_float(&self, a: &Pools, r: NodeId) -> bool {
        let _inputs = (a, r);
        todo!("T6k")
    }
    #[inline]
    fn bigint<'r>(&self, a: &'r Pools, r: NodeId) -> Option<&'r str> {
        let _inputs = (a, r);
        todo!("T6k")
    }
    #[inline]
    fn text<'r>(&self, a: &'r Pools, r: NodeId) -> Option<&'r str> {
        let _inputs = (a, r);
        todo!("T6k")
    }
    #[inline]
    fn var_of(&self, a: &Pools, r: NodeId) -> Option<VarId> {
        let _inputs = (a, r);
        todo!("T6k")
    }
    #[inline]
    fn qualified_of(&self, a: &Pools, r: NodeId) -> Option<(ImportId, Option<StrId>)> {
        let _inputs = (a, r);
        todo!("T6k")
    }
    #[inline]
    fn member_of(&self, a: &Pools, r: NodeId) -> Option<(StrId, FieldPos)> {
        let _inputs = (a, r);
        todo!("T6k")
    }
    #[inline]
    fn function_of(&self, a: &Pools, r: NodeId) -> Option<FuncId> {
        let _inputs = (a, r);
        todo!("T6k")
    }
    #[inline]
    fn info_of(&self, a: &Pools, r: NodeId) -> Option<JsId> {
        let _inputs = (a, r);
        todo!("T6k")
    }
    #[inline]
    fn arity(&self, a: &Pools, r: NodeId) -> u32 {
        let _inputs = (a, r);
        todo!("T6k")
    }
    #[inline]
    fn operand(&self, a: &Pools, r: NodeId, index: u32) -> NodeId {
        let _inputs = (a, r, index);
        todo!("T6k")
    }
    #[inline]
    fn located(&self, a: &Pools, r: NodeId) -> bool {
        let _inputs = (a, r);
        todo!("T6k")
    }
    fn runs_no_code(&self, a: &Pools, r: NodeId) -> bool {
        let _inputs = (a, r);
        todo!("T6k")
    }

    #[inline]
    fn var(&mut self, a: &mut Pools, var: VarId) -> E {
        let _inputs = (a, var);
        todo!("T6k")
    }
    #[inline]
    fn qualified(&mut self, a: &mut Pools, module: ImportId, member: Option<StrId>) -> E {
        let _inputs = (a, module, member);
        todo!("T6k")
    }
    #[inline]
    fn int_literal(&mut self, a: &mut Pools, value: i32) -> E {
        let _inputs = (a, value);
        todo!("T6k")
    }
    #[inline]
    fn number(&mut self, a: &mut Pools, value: ConstId) -> E {
        let _inputs = (a, value);
        todo!("T6k")
    }
    #[inline]
    fn string(&mut self, a: &mut Pools, text: &str) -> E {
        let _inputs = (a, text);
        todo!("T6k")
    }
    #[inline]
    fn str(&mut self, a: &mut Pools, text: StrId) -> E {
        let _inputs = (a, text);
        todo!("T6k")
    }
    #[inline]
    fn boolean(&mut self, a: &mut Pools, value: bool) -> E {
        let _inputs = (a, value);
        todo!("T6k")
    }
    #[inline]
    fn null(&mut self, a: &mut Pools) -> E {
        let _inputs = a;
        todo!("T6k")
    }
    #[inline]
    fn undefined(&mut self, a: &mut Pools, unit: bool) -> E {
        let _inputs = (a, unit);
        todo!("T6k")
    }
    #[inline]
    fn json(&mut self, a: &mut Pools, text: StrId) -> E {
        let _inputs = (a, text);
        todo!("T6k")
    }
    #[inline]
    fn raw(&mut self, a: &mut Pools, text: StrId, statement: bool) -> E {
        let _inputs = (a, text, statement);
        todo!("T6k")
    }

    #[inline]
    fn bin_plain(&mut self, a: &mut Pools, op: BinOp, left: E, right: E) -> E {
        let _inputs = (a, op, left, right);
        todo!("T6k")
    }
    #[inline]
    fn seq(&mut self, a: &mut Pools, first: E, second: E) -> E {
        let _inputs = (a, first, second);
        todo!("T6k")
    }
    #[inline]
    fn typeof_plain(&mut self, a: &mut Pools, value: E) -> E {
        let _inputs = (a, value);
        todo!("T6k")
    }
    #[inline]
    fn in_(&mut self, a: &mut Pools, left: E, right: E) -> E {
        let _inputs = (a, left, right);
        todo!("T6k")
    }
    #[inline]
    fn index(&mut self, a: &mut Pools, object: E, index: E) -> E {
        let _inputs = (a, object, index);
        todo!("T6k")
    }
    #[inline]
    fn dot(&mut self, a: &mut Pools, object: E, name: StrId, position: FieldPos, tag: bool) -> E {
        let _inputs = (a, object, name, position, tag);
        todo!("T6k")
    }
    #[inline]
    fn await_(&mut self, a: &mut Pools, value: E) -> E {
        let _inputs = (a, value);
        todo!("T6k")
    }
    #[inline]
    fn spread(&mut self, a: &mut Pools, value: E) -> E {
        let _inputs = (a, value);
        todo!("T6k")
    }
    #[inline]
    fn optional(&mut self, a: &mut Pools, value: E, identity: bool) -> E {
        let _inputs = (a, value, identity);
        todo!("T6k")
    }
    #[inline]
    fn record_rest(&mut self, a: &mut Pools, value: E, info: JsId) -> E {
        let _inputs = (a, value, info);
        todo!("T6k")
    }
    #[inline]
    fn flat_call(&mut self, a: &mut Pools, callee: E, args: E) -> E {
        let _inputs = (a, callee, args);
        todo!("T6k")
    }

    #[inline]
    fn mark(&self) -> Mark {
        Mark(self.operands.len() as u32)
    }
    #[inline]
    fn push(&mut self, operand: E) {
        self.operands.push(operand.0);
    }
    #[inline]
    fn pop(&mut self) -> E {
        E(self.operands.pop().expect("an operand"))
    }
    fn call(&mut self, a: &mut Pools, callee: E, mark: Mark, info: JsId) -> E {
        let _inputs = (a, callee, mark, info);
        todo!("T6k")
    }
    fn new_(&mut self, a: &mut Pools, callee: E, mark: Mark) -> E {
        let _inputs = (a, callee, mark);
        todo!("T6k")
    }
    fn tagged(&mut self, a: &mut Pools, tag: E, mark: Mark, info: JsId) -> E {
        let _inputs = (a, tag, mark, info);
        todo!("T6k")
    }
    fn array(&mut self, a: &mut Pools, mark: Mark, mutability: u8) -> E {
        let _inputs = (a, mark, mutability);
        todo!("T6k")
    }
    fn block(&mut self, a: &mut Pools, mark: Mark, info: JsId, mutability: u8) -> E {
        let _inputs = (a, mark, info, mutability);
        todo!("T6k")
    }
    fn object(&mut self, a: &mut Pools, mark: Mark, info: JsId) -> E {
        let _inputs = (a, mark, info);
        todo!("T6k")
    }
    fn jsx(&mut self, a: &mut Pools, mark: Mark, info: JsId, has_children: bool) -> E {
        let _inputs = (a, mark, info, has_children);
        todo!("T6k")
    }

    fn keep_operand(&mut self, a: &mut Pools, e: E, index: u32) -> E {
        let _inputs = (a, e, index);
        todo!("T6k")
    }
    fn unpack_rev(&mut self, a: &mut Pools, e: E) -> u32 {
        let _inputs = (a, e);
        todo!("T6k")
    }
    fn copy(&mut self, a: &mut Pools, r: NodeId) -> E {
        let _inputs = (a, r);
        todo!("T6k")
    }
    fn copy_leaf(&mut self, a: &mut Pools, r: NodeId) -> E {
        let _inputs = (a, r);
        todo!("T6k")
    }
    fn release(&mut self, a: &mut Pools, e: E) {
        let _inputs = (a, e);
        todo!("T6k")
    }
    fn drop_operands(&mut self, a: &mut Pools, mark: Mark) {
        let _inputs = (a, mark);
        todo!("T6k")
    }

    #[inline]
    fn assume_strict(&mut self, a: &mut Pools, e: &mut E) {
        let _inputs = (a, e);
        todo!("T6k")
    }
    fn locate(&mut self, a: &mut Pools, e: &mut E, loc: LamLoc) {
        let _inputs = (a, e, loc);
        todo!("T6k")
    }
    fn comment(&mut self, a: &mut Pools, e: &mut E, text: StrId) {
        let _inputs = (a, e, text);
        todo!("T6k")
    }
    fn copy_cold(&mut self, a: &mut Pools, from: NodeId, to: &mut E) {
        let _inputs = (a, from, to);
        todo!("T6k")
    }

    fn append(&mut self, a: &mut Pools, left: E, right: E) -> E {
        let _inputs = (a, left, right);
        todo!("T6k")
    }
    fn length(&mut self, a: &mut Pools, value: E, of: LengthObject) -> E {
        let _inputs = (a, value, of);
        todo!("T6k")
    }
    fn is_nullish(&mut self, a: &mut Pools, value: E) -> E {
        let _inputs = (a, value);
        todo!("T6k")
    }
    fn bin(&mut self, a: &mut Pools, op: BinOp, left: E, right: E) -> E {
        let _inputs = (a, op, left, right);
        todo!("T6k")
    }
    fn and(&mut self, a: &mut Pools, left: E, right: E) -> E {
        let _inputs = (a, left, right);
        todo!("T6k")
    }
    fn or(&mut self, a: &mut Pools, left: E, right: E) -> E {
        let _inputs = (a, left, right);
        todo!("T6k")
    }
    fn cond(&mut self, a: &mut Pools, test: E, then: E, otherwise: E) -> E {
        let _inputs = (a, test, then, otherwise);
        todo!("T6k")
    }
    fn not(&mut self, a: &mut Pools, value: E) -> E {
        let _inputs = (a, value);
        todo!("T6k")
    }
    fn without_pure(&mut self, a: &mut Pools, value: E) -> Option<E> {
        let _inputs = (a, value);
        todo!("T6k")
    }
    fn seq_rule(&mut self, a: &mut Pools, first: E, second: E) -> E {
        let _inputs = (a, first, second);
        todo!("T6k")
    }
    fn nullish_eq(&mut self, a: &mut Pools, neq: bool, left: E, right: E) -> E {
        let _inputs = (a, neq, left, right);
        todo!("T6k")
    }
    fn int_eq(&mut self, a: &mut Pools, left: E, right: E) -> E {
        let _inputs = (a, left, right);
        todo!("T6k")
    }
    fn to_int32(&mut self, a: &mut Pools, value: E) -> E {
        let _inputs = (a, value);
        todo!("T6k")
    }
    fn int_or(&mut self, a: &mut Pools, left: E, right: E) -> E {
        let _inputs = (a, left, right);
        todo!("T6k")
    }
    fn int_add(&mut self, a: &mut Pools, subtract: bool, left: E, right: E) -> E {
        let _inputs = (a, subtract, left, right);
        todo!("T6k")
    }
    fn int_mul(&mut self, a: &mut Pools, left: E, right: E) -> E {
        let _inputs = (a, left, right);
        todo!("T6k")
    }
    fn int_pow(&mut self, a: &mut Pools, left: E, right: E) -> E {
        let _inputs = (a, left, right);
        todo!("T6k")
    }
    fn int_lsl(&mut self, a: &mut Pools, left: E, right: E) -> E {
        let _inputs = (a, left, right);
        todo!("T6k")
    }
    fn int_lsr(&mut self, a: &mut Pools, left: E, right: E) -> E {
        let _inputs = (a, left, right);
        todo!("T6k")
    }
    fn int_xor(&mut self, a: &mut Pools, left: E, right: E) -> E {
        let _inputs = (a, left, right);
        todo!("T6k")
    }
    fn int_and(&mut self, a: &mut Pools, left: E, right: E) -> E {
        let _inputs = (a, left, right);
        todo!("T6k")
    }
    fn typeof_(&mut self, a: &mut Pools, value: E) -> E {
        let _inputs = (a, value);
        todo!("T6k")
    }
    fn bnot(&mut self, a: &mut Pools, value: E) -> E {
        let _inputs = (a, value);
        todo!("T6k")
    }
    fn project(&mut self, a: &mut Pools, value: E, field: Option<&str>, index: Option<i32>) -> Result<E, E> {
        let _inputs = (a, value, field, index);
        todo!("T6k")
    }
    fn poly_var(&mut self, a: &mut Pools, value: E, payload: bool) -> E {
        let _inputs = (a, value, payload);
        todo!("T6k")
    }
    fn template(&mut self, a: &mut Pools, segments: &[crate::string_literal::TemplateSegment], mark: Mark) -> E {
        let _inputs = (a, segments, mark);
        todo!("T6k")
    }
    fn int_div(&mut self, a: &mut Pools, check: bool, left: E, right: E) -> E {
        let _inputs = (a, check, left, right);
        todo!("T6k")
    }
    fn int_mod(&mut self, a: &mut Pools, check: bool, left: E, right: E) -> E {
        let _inputs = (a, check, left, right);
        todo!("T6k")
    }
}
