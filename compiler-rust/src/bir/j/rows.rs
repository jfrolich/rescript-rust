//! The first implementation of the lowering's interface (THREE_TREES 11.4,
//! "T6: the interface" (b)): J rows of the lowering's `Bir`. Every function
//! is the call of `plain.rs`, `norm.rs` or `Bir` that the lowering makes
//! today, so the rows written are today's rows. Deleted by the flip (T6s).
//!
//! `Rows` holds the operand stack and the step count and nothing else: the
//! nodes are the pools' (`Pools` is the lowering's `Bir`).
//!
//! The transition functions, `of`, `reserve`, `steps`, `mark`, `push`,
//! `pop` and `kind_of` are the representation; every other body is the row
//! of the table below.
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
use crate::bir::j::{facts, norm, plain};
use crate::bir::{Cold, ConstId, Constant, FuncId, ImportId, JsId, JsPayload, NodeFlags, NodeId, Op, StrId, VarId, View};
use crate::emit::row::{Kind, flag};
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
    fn id(&self, _: &Pools, r: NodeId) -> u32 {
        r.0
    }
    #[inline]
    fn kind(&self, a: &Pools, r: NodeId) -> Kind {
        kind_of(a.node(r).op())
    }
    #[inline]
    fn has(&self, a: &Pools, r: NodeId, flags: u16) -> bool {
        let f = u16::from(a.node(r).flags().0);
        let mut ours = (f & 1) | ((f >> 2) & 0b1110);
        if flags & flag::DUPLICABLE != 0 && a.j_duplicable.get(r.index()).copied().unwrap_or(false) {
            ours |= flag::DUPLICABLE;
        }
        ours & flags == flags
    }
    #[inline]
    fn aux(&self, a: &Pools, r: NodeId) -> u8 {
        a.node(r).aux() as u8
    }
    #[inline]
    fn int(&self, a: &Pools, r: NodeId) -> Option<i32> {
        plain::int_of(a, r)
    }
    #[inline]
    fn is_float(&self, a: &Pools, r: NodeId) -> bool {
        matches!(a.view(r), View::JNumber { value } if matches!(a.constant(value), Constant::Float(_)))
    }
    #[inline]
    fn bigint<'r>(&self, a: &'r Pools, r: NodeId) -> Option<&'r str> {
        match a.view(r) {
            View::JNumber { value } => match a.constant(value) {
                Constant::BigInt(digits) => Some(a.text(*digits)),
                _ => None,
            },
            _ => None,
        }
    }
    #[inline]
    fn text<'r>(&self, a: &'r Pools, r: NodeId) -> Option<&'r str> {
        match a.view(r) {
            View::JStr { text } => Some(a.text(text)),
            View::JTemplate { info, .. } if a.node(r).aux() == 1 => {
                let JsPayload::Template(parts) = a.javascript(info) else {
                    unreachable!("a template's parts")
                };
                a.template_parts(*parts)[0].cooked.map(|text| a.text(text))
            }
            _ => None,
        }
    }
    #[inline]
    fn var_of(&self, a: &Pools, r: NodeId) -> Option<VarId> {
        match a.view(r) {
            View::Var { var } => Some(var),
            _ => None,
        }
    }
    #[inline]
    fn qualified_of(&self, a: &Pools, r: NodeId) -> Option<(ImportId, Option<StrId>)> {
        match a.view(r) {
            View::JQualified { module, member } => Some((module, member)),
            _ => None,
        }
    }
    #[inline]
    fn member_of(&self, a: &Pools, r: NodeId) -> Option<(StrId, FieldPos)> {
        match a.view(r) {
            View::JDot { property, position, .. } => Some((property, position)),
            _ => None,
        }
    }
    #[inline]
    fn function_of(&self, a: &Pools, r: NodeId) -> Option<FuncId> {
        match a.view(r) {
            View::JFun { header, .. } => Some(header),
            _ => None,
        }
    }
    #[inline]
    fn info_of(&self, a: &Pools, r: NodeId) -> Option<JsId> {
        match a.view(r) {
            View::JCall { info, .. }
            | View::JObject { info, .. }
            | View::JBlockLit { info, .. }
            | View::JTemplate { info, .. }
            | View::JTagged { info, .. }
            | View::JJsx { info, .. }
            | View::JRecordRest { info, .. } => Some(info),
            _ => None,
        }
    }
    #[inline]
    fn arity(&self, a: &Pools, r: NodeId) -> u32 {
        a.view(r).child_count() as u32
    }
    #[inline]
    fn operand(&self, a: &Pools, r: NodeId, index: u32) -> NodeId {
        a.view(r).child_at(index as usize)
    }
    #[inline]
    fn located(&self, a: &Pools, r: NodeId) -> bool {
        a.node(r).flags().contains(NodeFlags::JS_LOC_PRESENT)
    }
    fn runs_no_code(&self, a: &Pools, r: NodeId) -> bool {
        facts::runs_no_code(a, r)
    }

    #[inline]
    fn var(&mut self, a: &mut Pools, var: VarId) -> E {
        self.leaf(a, View::Var { var }, 0)
    }
    #[inline]
    fn qualified(&mut self, a: &mut Pools, module: ImportId, member: Option<StrId>) -> E {
        self.leaf(a, View::JQualified { module, member }, 0)
    }
    #[inline]
    fn int_literal(&mut self, a: &mut Pools, value: i32) -> E {
        self.steps += 1;
        E(plain::int(a, value))
    }
    #[inline]
    fn number(&mut self, a: &mut Pools, value: ConstId) -> E {
        self.leaf(a, View::JNumber { value }, 0)
    }
    #[inline]
    fn string(&mut self, a: &mut Pools, text: &str) -> E {
        self.steps += 1;
        E(plain::string(a, text))
    }
    #[inline]
    fn str(&mut self, a: &mut Pools, text: StrId) -> E {
        self.leaf(a, View::JStr { text }, 0)
    }
    #[inline]
    fn boolean(&mut self, a: &mut Pools, value: bool) -> E {
        self.steps += 1;
        E(plain::boolean(a, value))
    }
    #[inline]
    fn null(&mut self, a: &mut Pools) -> E {
        self.leaf(a, View::JNull, 0)
    }
    #[inline]
    fn undefined(&mut self, a: &mut Pools, unit: bool) -> E {
        self.leaf(a, View::JUndefined, u16::from(unit))
    }
    #[inline]
    fn json(&mut self, a: &mut Pools, text: StrId) -> E {
        self.leaf(a, View::JJson { text }, 0)
    }
    #[inline]
    fn raw(&mut self, a: &mut Pools, text: StrId, statement: bool) -> E {
        self.leaf(a, View::JRaw { text }, u16::from(statement))
    }

    #[inline]
    fn bin_plain(&mut self, a: &mut Pools, op: BinOp, left: E, right: E) -> E {
        self.steps += 1;
        E(plain::bin(a, op, left.0, right.0))
    }
    #[inline]
    fn seq(&mut self, a: &mut Pools, first: E, second: E) -> E {
        self.steps += 1;
        E(plain::seq(a, first.0, second.0))
    }
    #[inline]
    fn typeof_plain(&mut self, a: &mut Pools, value: E) -> E {
        self.leaf(a, View::JTypeof { value: value.0 }, 0)
    }
    #[inline]
    fn in_(&mut self, a: &mut Pools, left: E, right: E) -> E {
        self.leaf(a, View::JIn { left: left.0, right: right.0 }, 0)
    }
    #[inline]
    fn index(&mut self, a: &mut Pools, object: E, index: E) -> E {
        self.leaf(a, View::JIndex { object: object.0, index: index.0 }, 0)
    }
    #[inline]
    fn dot(&mut self, a: &mut Pools, object: E, name: StrId, position: FieldPos, tag: bool) -> E {
        self.leaf(a, View::JDot { object: object.0, property: name, position }, u16::from(tag))
    }
    #[inline]
    fn await_(&mut self, a: &mut Pools, value: E) -> E {
        self.leaf(a, View::JAwait { value: value.0 }, 0)
    }
    #[inline]
    fn spread(&mut self, a: &mut Pools, value: E) -> E {
        self.leaf(a, View::JSpread { value: value.0 }, 0)
    }
    #[inline]
    fn optional(&mut self, a: &mut Pools, value: E, identity: bool) -> E {
        self.leaf(a, View::JOptional { value: value.0 }, u16::from(identity))
    }
    #[inline]
    fn record_rest(&mut self, a: &mut Pools, value: E, info: JsId) -> E {
        self.leaf(a, View::JRecordRest { value: value.0, info }, 0)
    }
    #[inline]
    fn flat_call(&mut self, a: &mut Pools, callee: E, args: E) -> E {
        self.leaf(a, View::JFlatCall { callee: callee.0, args: args.0 }, 0)
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
        let start = self.since(mark);
        let id = plain::node(a, View::JCall { callee: callee.0, args: &self.operands[start..], info }, 0);
        self.cut(start, id)
    }
    fn new_(&mut self, a: &mut Pools, callee: E, mark: Mark) -> E {
        let start = self.since(mark);
        let id = plain::node(a, View::JNew { callee: callee.0, args: &self.operands[start..] }, 0);
        self.cut(start, id)
    }
    fn tagged(&mut self, a: &mut Pools, tag: E, mark: Mark, info: JsId) -> E {
        let start = self.since(mark);
        let id = plain::node(a, View::JTagged { tag: tag.0, values: &self.operands[start..], info }, 0);
        self.cut(start, id)
    }
    fn array(&mut self, a: &mut Pools, mark: Mark, mutability: u8) -> E {
        let start = self.since(mark);
        let id = plain::node(a, View::JArray { values: &self.operands[start..] }, u16::from(mutability));
        self.cut(start, id)
    }
    fn block(&mut self, a: &mut Pools, mark: Mark, info: JsId, mutability: u8) -> E {
        let start = self.since(mark);
        let id = plain::node(a, View::JBlockLit { values: &self.operands[start..], info }, u16::from(mutability));
        self.cut(start, id)
    }
    fn object(&mut self, a: &mut Pools, mark: Mark, info: JsId) -> E {
        let start = self.since(mark);
        let id = plain::node(a, View::JObject { values: &self.operands[start..], info }, 0);
        self.cut(start, id)
    }
    fn jsx(&mut self, a: &mut Pools, mark: Mark, info: JsId, has_children: bool) -> E {
        let start = self.since(mark);
        let id = plain::node(a, View::JJsx { values: &self.operands[start..], info }, u16::from(has_children));
        self.cut(start, id)
    }

    fn keep_operand(&mut self, a: &mut Pools, e: E, index: u32) -> E {
        self.steps += 1;
        let kept = a.view(e.0).child_at(index as usize);
        a.detach(kept);
        a.release(e.0);
        E(kept)
    }
    fn unpack_rev(&mut self, a: &mut Pools, e: E) -> u32 {
        let count = a.view(e.0).child_count();
        self.steps += 1 + count as u64;
        for index in (0..count).rev() {
            let operand = a.view(e.0).child_at(index);
            a.detach(operand);
            self.operands.push(operand);
        }
        a.release(e.0);
        count as u32
    }
    fn copy(&mut self, a: &mut Pools, r: NodeId) -> E {
        let before = a.nodes.len();
        let copy = a.copy_subtree(r, &[]);
        self.steps += (a.nodes.len() - before).max(1) as u64;
        E(copy)
    }
    fn copy_leaf(&mut self, a: &mut Pools, r: NodeId) -> E {
        let aux = a.node(r).aux();
        let view = match a.view(r) {
            View::Var { var } => View::Var { var },
            View::JQualified { module, member } => View::JQualified { module, member },
            View::JNumber { value } => View::JNumber { value },
            View::JStr { text } => View::JStr { text },
            View::JJson { text } => View::JJson { text },
            View::JRaw { text } => View::JRaw { text },
            View::JBool => View::JBool,
            View::JNull => View::JNull,
            View::JUndefined => View::JUndefined,
            View::JTemplate { info, values: [] } => View::JTemplate { info, values: &[] },
            other => panic!("copy_leaf of a node with operands: {other:?}"),
        };
        self.leaf(a, view, aux)
    }
    fn release(&mut self, a: &mut Pools, e: E) {
        self.steps += 1;
        a.release(e.0);
    }
    fn drop_operands(&mut self, a: &mut Pools, mark: Mark) {
        let start = self.since(mark);
        self.steps += 1 + (self.operands.len() - start) as u64;
        for &operand in &self.operands[start..] {
            a.release(operand);
        }
        self.operands.truncate(start);
    }

    #[inline]
    fn assume_strict(&mut self, a: &mut Pools, e: &mut E) {
        let mut flags = a.node(e.0).flags();
        flags.0 |= NodeFlags::STRICT;
        a.nodes[e.0.index()].set_flags(flags);
    }
    fn locate(&mut self, a: &mut Pools, e: &mut E, loc: LamLoc) {
        let comment = a.cold(e.0).and_then(|cold| cold.comment);
        a.set_cold(e.0, Cold { loc, comment });
        let mut flags = a.node(e.0).flags();
        flags.0 |= NodeFlags::JS_LOC_PRESENT;
        a.nodes[e.0.index()].set_flags(flags);
    }
    fn comment(&mut self, a: &mut Pools, e: &mut E, text: StrId) {
        let loc = a.cold(e.0).map_or(LamLoc::NONE, |cold| cold.loc);
        a.set_cold(e.0, Cold { loc, comment: Some(text) });
    }
    fn copy_cold(&mut self, a: &mut Pools, from: NodeId, to: &mut E) {
        plain::copy_cold(a, from, to.0);
        if let Some(code) = a.node(from).js_char() {
            a.nodes[to.0.index()].set_js_char(code);
        }
    }

    fn append(&mut self, a: &mut Pools, left: E, right: E) -> E {
        self.steps += 1;
        E(norm::je1_string_append(a, left.0, right.0))
    }
    fn length(&mut self, a: &mut Pools, value: E, of: LengthObject) -> E {
        self.steps += 1;
        E(norm::je2_length(a, value.0, of))
    }
    fn is_nullish(&mut self, a: &mut Pools, value: E) -> E {
        self.steps += 1;
        E(norm::je3_is_null_or_undefined(a, value.0))
    }
    fn bin(&mut self, a: &mut Pools, op: BinOp, left: E, right: E) -> E {
        self.steps += 1;
        E(norm::je4_bin(a, op, left.0, right.0))
    }
    fn and(&mut self, a: &mut Pools, left: E, right: E) -> E {
        self.steps += 1;
        E(norm::je5_js_and(a, left.0, right.0))
    }
    fn or(&mut self, a: &mut Pools, left: E, right: E) -> E {
        self.steps += 1;
        E(norm::je6_js_or(a, left.0, right.0))
    }
    fn cond(&mut self, a: &mut Pools, test: E, then: E, otherwise: E) -> E {
        self.steps += 1;
        E(norm::je7_cond(a, test.0, then.0, otherwise.0))
    }
    fn not(&mut self, a: &mut Pools, value: E) -> E {
        self.steps += 1;
        E(norm::je8_not(a, value.0))
    }
    fn without_pure(&mut self, a: &mut Pools, value: E) -> Option<E> {
        self.steps += 1;
        norm::jm0_remove_pure_subexpression(a, value.0).map(E)
    }
    fn seq_rule(&mut self, a: &mut Pools, first: E, second: E) -> E {
        self.steps += 1;
        E(norm::jm1_js_seq(a, first.0, second.0))
    }
    fn nullish_eq(&mut self, a: &mut Pools, neq: bool, left: E, right: E) -> E {
        self.steps += 1;
        E(norm::jm2_nullish_strict_comparison(a, neq, left.0, right.0))
    }
    fn int_eq(&mut self, a: &mut Pools, left: E, right: E) -> E {
        self.steps += 1;
        E(norm::jm2_int_equality(a, left.0, right.0))
    }
    fn to_int32(&mut self, a: &mut Pools, value: E) -> E {
        self.steps += 1;
        E(norm::jm3_to_int32(a, value.0))
    }
    fn int_or(&mut self, a: &mut Pools, left: E, right: E) -> E {
        self.steps += 1;
        E(norm::jm3_int32_bor(a, left.0, right.0))
    }
    fn int_add(&mut self, a: &mut Pools, subtract: bool, left: E, right: E) -> E {
        self.steps += 1;
        E(norm::jm4_int32_add_sub(a, subtract, left.0, right.0))
    }
    fn int_mul(&mut self, a: &mut Pools, left: E, right: E) -> E {
        self.steps += 1;
        E(norm::jm5_int32_mul(a, left.0, right.0))
    }
    fn int_pow(&mut self, a: &mut Pools, left: E, right: E) -> E {
        self.steps += 1;
        E(norm::jm6_int32_pow(a, left.0, right.0))
    }
    fn int_lsl(&mut self, a: &mut Pools, left: E, right: E) -> E {
        self.steps += 1;
        E(norm::jm7_int32_lsl(a, left.0, right.0))
    }
    fn int_lsr(&mut self, a: &mut Pools, left: E, right: E) -> E {
        self.steps += 1;
        E(norm::jm8_int32_lsr(a, left.0, right.0))
    }
    fn int_xor(&mut self, a: &mut Pools, left: E, right: E) -> E {
        self.steps += 1;
        E(norm::jm8_int32_bxor(a, left.0, right.0))
    }
    fn int_and(&mut self, a: &mut Pools, left: E, right: E) -> E {
        self.steps += 1;
        E(norm::jm8_int32_band(a, left.0, right.0))
    }
    fn typeof_(&mut self, a: &mut Pools, value: E) -> E {
        self.steps += 1;
        E(norm::jm9_typeof(a, value.0))
    }
    fn bnot(&mut self, a: &mut Pools, value: E) -> E {
        self.steps += 1;
        E(norm::jm10_int_bnot(a, value.0))
    }
    fn project(&mut self, a: &mut Pools, value: E, field: Option<&str>, index: Option<i32>) -> Result<E, E> {
        self.steps += 1;
        norm::jm11_projection(a, value.0, field, index).map(E).ok_or(value)
    }
    fn poly_var(&mut self, a: &mut Pools, value: E, payload: bool) -> E {
        self.steps += 1;
        E(norm::jm11_poly_var_access(a, value.0, payload))
    }
    fn template(&mut self, a: &mut Pools, segments: &[crate::string_literal::TemplateSegment], mark: Mark) -> E {
        let start = self.since(mark);
        let id = norm::jm12_interpolated_template(a, segments, self.operands[start..].iter().copied());
        self.cut(start, id)
    }
    fn int_div(&mut self, a: &mut Pools, check: bool, left: E, right: E) -> E {
        self.steps += 1;
        E(norm::jm13_int32_div(a, check, left.0, right.0))
    }
    fn int_mod(&mut self, a: &mut Pools, check: bool, left: E, right: E) -> E {
        self.steps += 1;
        E(norm::jm13_int32_mod(a, check, left.0, right.0))
    }
}

impl Rows {
    /// `plain::node` of `view` with `aux`, and its step. O(1).
    #[inline]
    fn leaf(&mut self, a: &mut Pools, view: View<'_>, aux: u16) -> E {
        self.steps += 1;
        E(plain::node(a, view, aux))
    }
    /// The index of `mark` on the operand stack. O(1).
    #[inline]
    fn since(&self, mark: Mark) -> usize {
        let start = mark.0 as usize;
        debug_assert!(start <= self.operands.len(), "a mark above the operand stack");
        start
    }
    /// The stack cut back to `start` after a list constructor built `id`
    /// from the operands above it: one step, and one per operand. O(1).
    #[inline]
    fn cut(&mut self, start: usize, id: NodeId) -> E {
        self.steps += 1 + (self.operands.len() - start) as u64;
        self.operands.truncate(start);
        E(id)
    }
}
