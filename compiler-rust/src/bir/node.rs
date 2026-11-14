//! Packed nodes and typed views. One schema defines encoding, decoding and
//! traversal, so adding an operand cannot silently omit it from copy or release.
use super::pools::*;
use crate::js_ir::arena::FieldPos;
use smallvec::SmallVec;
use std::collections::HashMap;

/// Cached effects and positional information.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
#[repr(transparent)]
pub struct NodeFlags(pub(super) u8);
impl NodeFlags {
    /// Evaluation has no observable effects.
    pub const PURE: u8 = 1;
    /// Evaluation allocates no runtime values.
    pub const NO_ALLOC: u8 = 2;
    /// Source metadata is present.
    pub const HAS_LOC: u8 = 4;
    /// The expression's value is discarded.
    pub const VALUE_UNUSED: u8 = 16;
    /// A let's released, pure value is no longer evaluated.
    pub const DEAD: u8 = 32;
    /// JS metadata distinguishes absent locations from an explicit NONE handle.
    pub const JS_LOC_PRESENT: u8 = 64;
    /// A JNumber carries an optional character decoration in its spare word.
    pub const JS_CHAR_PRESENT: u8 = 128;
    /// L-only: a pure Let/Seq spine ending in the unit constant.
    /// Shares the J strict-purity bit; L and J operations are disjoint.
    pub const TRIVIAL_UNIT: u8 = 8;
    /// J-only: strict purity.
    pub const STRICT: u8 = 8;
    /// J-only: removable by E:146 is_pure_subexpression (not general purity).
    pub const J_SUBEXPR: u8 = Self::DEAD;
    /// J-only: safe to defer evaluation, reusing the L discarded-value bit.
    pub const DELAY_SAFE: u8 = Self::VALUE_UNUSED;
    /// L-only: the subtree holds an `Exit` that is not under a `Fun`
    /// (`Lam_exit_code.has_exit`, lam_exit_code.ml:35). Reuses the bit that
    /// only a `JNumber` reads as `JS_CHAR_PRESENT`.
    pub const HAS_EXIT: u8 = Self::JS_CHAR_PRESENT;
    /// L-only, never on a `Var`: the subtree holds, outside a `Fun`, a
    /// construct that is lowered to statements in every continuation (C:5139
    /// lambda_contains_statement_value_form). Reuses the bit level J reads as
    /// `JS_LOC_PRESENT`.
    pub const HAS_STATEMENT: u8 = Self::JS_LOC_PRESENT;
    /// L-only facts maintained together from immediate child flags.
    pub(super) const CONTROL: u8 = Self::HAS_EXIT | Self::HAS_STATEMENT | Self::TRIVIAL_UNIT;
    /// Test a flag.
    pub fn contains(self, flag: u8) -> bool {
        self.0 & flag != 0
    }
}
/// Hot representation. Only this module interprets the packed operands.
#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct Node {
    op: Op,
    flags: NodeFlags,
    aux: u16,
    words: [u32; 3],
}

pub(super) struct Renaming<'a> {
    pub nodes: &'a super::edit::DenseMap<NodeId>,
    pub vars: &'a super::edit::DenseMap<VarId>,
    pub funcs: &'a super::edit::DenseMap<FuncId>,
    pub catches: &'a super::edit::DenseMap<CatchId>,
    pub labels: &'a HashMap<u32, u32>,
    pub js: &'a super::edit::DenseMap<JsId>,
}

trait Operand<'a>: Sized {
    fn encode(self, lists: &mut Lists) -> u32;
    fn decode(raw: u32, lists: &'a Lists) -> Self;
    fn child_count(self) -> usize { 0 }
    fn child_at(self, _at: usize) -> NodeId { unreachable!("metadata has no children") }
    fn remap(raw: u32, _lists: &mut Lists, _map: &Renaming<'_>) -> u32 {
        raw
    }
}
macro_rules! payload {
    ($($ty:ident),*) => {$(
        impl Operand<'_> for $ty {
            fn encode(self, _lists: &mut Lists) -> u32 { self.0 }
            fn decode(raw: u32, _lists: &Lists) -> Self { Self(raw) }
        }
    )*};
}
payload!(ConstId, PrimId, ApplyId, SwitchId, StrId, ImportId);
macro_rules! renamed {
    ($ty:ident, $table:ident) => {
        impl Operand<'_> for $ty {
            fn encode(self, _lists: &mut Lists) -> u32 {
                self.0
            }
            fn decode(raw: u32, _lists: &Lists) -> Self {
                Self(raw)
            }
            fn remap(raw: u32, _lists: &mut Lists, map: &Renaming<'_>) -> u32 {
                map.$table.get(&Self(raw)).copied().unwrap_or(Self(raw)).0
            }
        }
    };
}
renamed!(VarId, vars);
renamed!(FuncId, funcs);
renamed!(CatchId, catches);
renamed!(JsId, js);
impl Operand<'_> for u32 {
    fn encode(self, _lists: &mut Lists) -> u32 {
        self
    }
    fn decode(raw: u32, _lists: &Lists) -> Self {
        raw
    }
    fn remap(raw: u32, _lists: &mut Lists, map: &Renaming<'_>) -> u32 {
        map.labels.get(&raw).copied().unwrap_or(raw)
    }
}
impl Operand<'_> for NodeId {
    fn encode(self, _lists: &mut Lists) -> u32 {
        self.0
    }
    fn decode(raw: u32, _lists: &Lists) -> Self {
        Self(raw)
    }
    fn child_count(self) -> usize { 1 }
    fn child_at(self, at: usize) -> NodeId { assert_eq!(at, 0); self }
    fn remap(raw: u32, _lists: &mut Lists, map: &Renaming<'_>) -> u32 {
        map.nodes[&Self(raw)].0
    }
}
impl Operand<'_> for Option<NodeId> {
    fn encode(self, _lists: &mut Lists) -> u32 {
        self.map_or(u32::MAX, |n| n.0)
    }
    fn decode(raw: u32, _lists: &Lists) -> Self {
        (raw != u32::MAX).then_some(NodeId(raw))
    }
    fn child_count(self) -> usize { usize::from(self.is_some()) }
    fn child_at(self, at: usize) -> NodeId { assert_eq!(at, 0); self.expect("optional child") }
    fn remap(raw: u32, _lists: &mut Lists, map: &Renaming<'_>) -> u32 {
        if raw == u32::MAX {
            raw
        } else {
            map.nodes[&NodeId(raw)].0
        }
    }
}
macro_rules! optional_payload {
    ($ty:ident) => {
        impl Operand<'_> for Option<$ty> {
            fn encode(self, _lists: &mut Lists) -> u32 {
                self.map_or(u32::MAX, |id| id.0)
            }
            fn decode(raw: u32, _lists: &Lists) -> Self {
                (raw != u32::MAX).then_some($ty(raw))
            }
            fn remap(raw: u32, lists: &mut Lists, map: &Renaming<'_>) -> u32 {
                if raw == u32::MAX {
                    raw
                } else {
                    <$ty>::remap(raw, lists, map)
                }
            }
        }
    };
}
optional_payload!(StrId);
optional_payload!(VarId);
impl Operand<'_> for FieldPos {
    fn encode(self, _lists: &mut Lists) -> u32 {
        self.get().unwrap_or(i32::MIN) as u32
    }
    fn decode(raw: u32, _lists: &Lists) -> Self {
        Self::new((raw != i32::MIN as u32).then_some(raw as i32))
    }
}
impl<'a> Operand<'a> for &'a [NodeId] {
    fn encode(self, lists: &mut Lists) -> u32 {
        lists.push(self).0
    }
    fn decode(raw: u32, lists: &'a Lists) -> Self {
        lists.get(ListId(raw))
    }
    fn child_count(self) -> usize { self.len() }
    fn child_at(self, at: usize) -> NodeId { self[at] }
    fn remap(raw: u32, lists: &mut Lists, map: &Renaming<'_>) -> u32 {
        lists.mapped(ListId(raw), |n| map.nodes[&n]).0
    }
}

macro_rules! nodes {
    ($($op:ident $( { $($field:ident: $ty:ty),* } )?),* $(,)?) => {
        /// One-byte operation tag.
        #[repr(u8)]
        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        pub enum Op {
            $(#[doc = concat!("`", stringify!($op), "` operation.")] $op,)*
            /// Released slot.
            Free,
        }
        /// Typed operands. Child lists are borrowed immutable slices.
        #[derive(Debug, Clone, Copy)]
        pub enum View<'a> {
            $(#[doc = concat!("`", stringify!($op), "` operation and its operands.")]
            $op $( { $(#[doc = concat!(stringify!($field), " operand.")] $field: $ty),* } )?,)*
        }
        impl Node {
            pub(super) fn pack<'a>(view: View<'a>, aux: u16, lists: &mut Lists) -> Self {
                let mut words = [0; 3];
                let op = match view { $(
                    View::$op $({ $($field),* })? => {
                        let operands: &[u32] = &[$($($field.encode(lists)),*)?];
                        words[..operands.len()].copy_from_slice(operands);
                        Op::$op
                    }
                ),* };
                Self { op, flags: NodeFlags::default(), aux, words }
            }
            pub(super) fn view<'a>(self, lists: &'a Lists) -> View<'a> {
                let mut words = self.words.into_iter();
                match self.op {
                    $(Op::$op => View::$op $({ $($field: <$ty>::decode(words.next().unwrap(), lists)),* })?,)*
                    Op::Free => panic!("released Bir node"),
                }
            }
            pub(super) fn remap<'a>(self, lists: &mut Lists, map: &'a Renaming<'_>) -> Self {
                let mut result = self;
                let mut words = result.words.iter_mut();
                match self.op {
                    $(Op::$op => { $($(let word = words.next().unwrap(); *word = <$ty>::remap(*word, lists, map);)*)? },)*
                    Op::Free => panic!("cannot copy released node"),
                }
                result
            }
        }
        impl View<'_> {
            /// O(1): at most three immediate operand lengths, without copying a list.
            pub(super) fn child_count(self) -> usize {
                match self { $(Self::$op $({ $($field),* })? => 0 $($(+ $field.child_count())*)? ),* }
            }
            /// O(1): select an edge among at most three immediate operands.
            pub(super) fn child_at(self, mut at: usize) -> NodeId {
                match self { $(Self::$op $({ $($field),* })? => { $($(
                    let count = $field.child_count();
                    if at < count { return $field.child_at(at); }
                    at -= count;
                )*)? }),* }
                panic!("child index out of bounds: {at}")
            }
            pub(super) fn children(self) -> SmallVec<[NodeId; 4]> {
                (0..self.child_count()).map(|at| self.child_at(at)).collect()
            }
            /// The children, pushed on `out` (`children` without its
            /// inline vector, which spills past four). Cost: one push per
            /// child; nothing is allocated once `out` has the capacity.
            pub(super) fn children_into(self, out: &mut Vec<NodeId>) {
                out.extend((0..self.child_count()).map(|at| self.child_at(at)));
            }
        }
    };
}

// The three operands map to a/b/c in BACKEND_REDESIGN.md B.3. Aux holds
// the existing enum discriminant for LetKind/BinOp/direction/length kind,
// a boolean for JBool/JUndefined/JOptional, or a function's arity.
// JRaw's aux distinguishes expression (0) from statement (1).
// J bridge encodings: SBlock 0=list/1=explicit statement; JDot 0=static
// index/1=block tag; JNew 0=absent args/1=present; JTemplate 0=interpolated/
// 1=literal; JJsx records children-list presence; SSwitch 0=int/1=string.
// SDecl packs LetKind in bits 0..2 and UsedStats above it. Arrays/blocks use
// 0=immutable, 1=mutable, 2=NA (the fact engine tests zero for immutable).
// Imported SRest uses bit 15 when value is a retained JRecordRest descriptor.
// JNumber's unused second word holds an optional char, flagged JS_CHAR_PRESENT.
// JFun uses the existing method flag and FunctionAttribute for return-unit,
// async and directives. JQualified's ImportId also indexes pools.j_modules.
nodes! {
    Var { var: VarId },
    Global { module: ImportId },
    Const { value: ConstId },
    Apply { callee: NodeId, args: &'a [NodeId], info: ApplyId },
    Fun { body: NodeId, header: FuncId },
    Let { var: VarId, value: Option<NodeId>, body: NodeId },
    LetRec { first: VarId, values: &'a [NodeId], body: NodeId },
    Prim { args: &'a [NodeId], primitive: PrimId },
    Switch { scrutinee: NodeId, actions: &'a [NodeId], header: SwitchId },
    StrSwitch { scrutinee: NodeId, actions: &'a [NodeId], header: SwitchId },
    Exit { label: u32, args: &'a [NodeId] },
    Catch { body: NodeId, handler: NodeId, header: CatchId },
    Try { body: NodeId, exception: VarId, handler: NodeId },
    TryFinally { body: NodeId, finaliser: NodeId },
    If { condition: NodeId, then_: NodeId, else_: NodeId },
    Seq { first: NodeId, second: NodeId },
    While { condition: NodeId, body: NodeId },
    For { var: VarId, parts: &'a [NodeId] },
    ForOf { var: VarId, iterable: NodeId, body: NodeId },
    ForAwaitOf { var: VarId, iterable: NodeId, body: NodeId },
    Assign { var: VarId, value: NodeId },
    Break,
    Continue,
    JBin { left: NodeId, right: NodeId },
    JNot { value: NodeId },
    JBnot { value: NodeId },
    JTypeof { value: NodeId },
    JIn { left: NodeId, right: NodeId },
    JCond { condition: NodeId, then_: NodeId, else_: NodeId },
    JSeq { first: NodeId, second: NodeId },
    JCall { callee: NodeId, args: &'a [NodeId], info: JsId },
    JFlatCall { callee: NodeId, args: NodeId },
    JNew { callee: NodeId, args: &'a [NodeId] },
    JIndex { object: NodeId, index: NodeId },
    JDot { object: NodeId, property: StrId, position: FieldPos },
    JLength { value: NodeId },
    JIsNullish { value: NodeId },
    JStrAppend { left: NodeId, right: NodeId },
    JFun { body: NodeId, header: FuncId },
    JObject { values: &'a [NodeId], info: JsId },
    JArray { values: &'a [NodeId] },
    JBlockLit { values: &'a [NodeId], info: JsId },
    JOptional { value: NodeId },
    JJsx { values: &'a [NodeId], info: JsId },
    JTemplate { values: &'a [NodeId], info: JsId },
    JTagged { tag: NodeId, values: &'a [NodeId], info: JsId },
    JRaw { text: StrId },
    JAwait { value: NodeId },
    JSpread { value: NodeId },
    JQualified { module: ImportId, member: Option<StrId> },
    JNumber { value: ConstId },
    JStr { text: StrId },
    JBool,
    JNull,
    JUndefined,
    JJson { text: StrId },
    JRecordRest { value: NodeId, info: JsId },
    SBlock { statements: &'a [NodeId] },
    SDecl { var: VarId, value: Option<NodeId> },
    SExp { value: NodeId },
    SIf { condition: NodeId, then_: NodeId, else_: Option<NodeId> },
    SWhile { condition: NodeId, body: NodeId, label: Option<StrId> },
    SForRangeExisting { variable: NodeId, parts: &'a [NodeId], label: Option<StrId> },
    SForRange { var: VarId, parts: &'a [NodeId], label: Option<StrId> },
    SForOf { var: VarId, parts: &'a [NodeId], label: Option<StrId> },
    SForAwaitOf { var: VarId, parts: &'a [NodeId], label: Option<StrId> },
    SSwitch { scrutinee: NodeId, actions: &'a [NodeId], header: SwitchId },
    SReturn { value: NodeId },
    SThrow { value: NodeId },
    STry { parts: &'a [NodeId], exception: Option<VarId> },
    SBreak { label: Option<StrId> },
    SContinue { label: Option<StrId> },
    SDebugger,
    SRest { var: VarId, value: NodeId, info: JsId },
}

impl Node {
    pub(super) fn free() -> Self {
        Self {
            op: Op::Free,
            flags: NodeFlags::default(),
            aux: 0,
            words: [0; 3],
        }
    }
    /// Operation tag.
    pub fn op(self) -> Op {
        self.op
    }
    /// Cached properties.
    pub fn flags(self) -> NodeFlags {
        self.flags
    }
    /// Operation-specific small payload (see the schema's encoding notes).
    pub fn aux(self) -> u16 {
        self.aux
    }
    /// Borrow the existing switch action-list handle. O(1).
    pub(crate) fn switch_actions(self) -> ListId {
        assert!(matches!(self.op, Op::Switch | Op::StrSwitch));
        ListId(self.words[1])
    }
    /// O(1): retain the existing primitive operand-list handle without copying
    /// its elements into a traversal resume record.
    pub(crate) fn primitive_arguments(self) -> ListId {
        assert_eq!(self.op, Op::Prim);
        ListId(self.words[0])
    }
    /// O(1): the argument-list handle of an exit, for a traversal resume
    /// record that does not copy the arguments.
    pub(crate) fn exit_arguments(self) -> ListId {
        assert_eq!(self.op, Op::Exit);
        ListId(self.words[1])
    }
    /// Original integer character decoration; not necessarily the integer value.
    pub fn js_char(self) -> Option<i32> {
        (self.op == Op::JNumber && self.flags.contains(NodeFlags::JS_CHAR_PRESENT))
            .then_some(self.words[1] as i32)
    }
    pub(super) fn set_js_char(&mut self, code: i32) {
        assert_eq!(self.op, Op::JNumber);
        self.flags.0 |= NodeFlags::JS_CHAR_PRESENT;
        self.words[1] = code as u32;
    }
    /// O(1): retain a source application's argument-list identity.
    pub(super) fn apply_args(self) -> ListId {
        assert_eq!(self.op, Op::Apply);
        ListId(self.words[1])
    }
    /// O(1): borrow an SBlock's list identity without copying its elements.
    pub(super) fn block_list_id(self) -> Option<ListId> {
        (self.op == Op::SBlock).then_some(ListId(self.words[0]))
    }
    /// O(1): encode a switch over a finalized action list and pooled header.
    pub(super) fn switch_list(
        scrutinee: NodeId,
        actions: ListId,
        header: SwitchId,
        aux: u16,
    ) -> Self {
        Self {
            op: Op::SSwitch,
            flags: NodeFlags::default(),
            aux,
            words: [scrutinee.0, actions.0, header.0],
        }
    }
    /// O(1): encode a call or construction over a finalized argument list.
    pub(super) fn call_list(callee: NodeId, args: ListId, info: Option<JsId>) -> Self {
        Self {
            op: if info.is_some() { Op::JCall } else { Op::JNew },
            flags: NodeFlags::default(),
            aux: u16::from(info.is_none()),
            words: [callee.0, args.0, info.map_or(0, |id| id.0)],
        }
    }
    /// O(1): encode an object over finalized operand and metadata pools.
    pub(super) fn object_list(list: ListId, info: JsId) -> Self {
        Self {
            op: Op::JObject,
            flags: NodeFlags::default(),
            aux: 0,
            words: [list.0, info.0, 0],
        }
    }
    /// O(1): encode JSX over its finalized operand list and cold shape.
    /// Replace only immutable block metadata with an equivalent owned payload
    /// at the export boundary; child links and cached expression facts stay valid.
    pub(super) fn set_block_info(&mut self, info: JsId) {
        assert_eq!(self.op(), Op::JBlockLit);
        self.words[1] = info.0;
    }

    pub(super) fn jsx_list(list: ListId, info: JsId, aux: u16) -> Self {
        Self { op: Op::JJsx, aux, ..Self::object_list(list, info) }
    }
    pub(super) fn block_list(list: ListId) -> Self {
        Self { op: Op::SBlock, flags: NodeFlags::default(), aux: 0, words: [list.0, 0, 0] }
    }
    pub(super) fn explicit_block_list(list: ListId) -> Self {
        Self { aux: 1, ..Self::block_list(list) }
    }
    pub(super) fn set_flags(&mut self, flags: NodeFlags) {
        self.flags = flags;
    }
    /// The site of a `Var` or of a `JQualified` in the lowering arena
    /// (`lower::scope::Site`), kept in the leaf's unused word (the second
    /// of a `Var`, the third of a `JQualified`) so that it moves with the
    /// node's content. O(1).
    pub(super) fn site(self) -> u32 {
        match self.op {
            Op::Var => self.words[1],
            Op::JQualified => self.words[2],
            op => unreachable!("{op:?} has no site"),
        }
    }
    pub(super) fn set_site(&mut self, site: u32) {
        match self.op {
            Op::Var => self.words[1] = site,
            Op::JQualified => self.words[2] = site,
            op => unreachable!("{op:?} has no site"),
        }
    }
    /// The reference prints as `globalThis.name` (`lower::globals`). O(1).
    pub(super) fn var_qualified(self) -> bool {
        assert_eq!(self.op, Op::Var);
        self.aux & 1 != 0
    }
    pub(super) fn set_var_qualified(&mut self) {
        assert_eq!(self.op, Op::Var);
        self.aux |= 1;
    }
    pub(super) fn kill_value(&mut self) {
        assert_eq!(self.op, Op::Let);
        self.words[1] = u32::MAX;
        self.flags.0 |= NodeFlags::DEAD;
    }
}
