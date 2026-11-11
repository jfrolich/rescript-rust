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
    /// Tail position in a function.
    pub const TAIL: u8 = 8;
    /// The expression's value is discarded.
    pub const VALUE_UNUSED: u8 = 16;
    /// A let's released, pure value is no longer evaluated.
    pub const DEAD: u8 = 32;
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
    pub nodes: &'a HashMap<NodeId, NodeId>,
    pub vars: &'a HashMap<VarId, VarId>,
    pub funcs: &'a HashMap<FuncId, FuncId>,
    pub catches: &'a HashMap<CatchId, CatchId>,
    pub labels: &'a HashMap<u32, u32>,
    pub js: &'a HashMap<JsId, JsId>,
}

trait Operand<'a>: Sized {
    fn encode(self, lists: &mut Lists) -> u32;
    fn decode(raw: u32, lists: &'a Lists) -> Self;
    fn children(self, _out: &mut SmallVec<[NodeId; 4]>) {}
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
    fn children(self, out: &mut SmallVec<[NodeId; 4]>) {
        out.push(self);
    }
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
    fn children(self, out: &mut SmallVec<[NodeId; 4]>) {
        out.extend(self);
    }
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
        self.get().map_or(u32::MAX, |n| n as u32)
    }
    fn decode(raw: u32, _lists: &Lists) -> Self {
        Self::new((raw != u32::MAX).then_some(raw as i32))
    }
}
impl<'a> Operand<'a> for &'a [NodeId] {
    fn encode(self, lists: &mut Lists) -> u32 {
        lists.push(self).0
    }
    fn decode(raw: u32, lists: &'a Lists) -> Self {
        lists.get(ListId(raw))
    }
    fn children(self, out: &mut SmallVec<[NodeId; 4]>) {
        out.extend_from_slice(self);
    }
    fn remap(raw: u32, lists: &mut Lists, map: &Renaming<'_>) -> u32 {
        let values: Vec<_> = lists
            .get(ListId(raw))
            .iter()
            .map(|n| map.nodes[n])
            .collect();
        lists.push(&values).0
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
            pub(super) fn children(self) -> SmallVec<[NodeId; 4]> {
                let mut result = SmallVec::new();
                match self { $(Self::$op $({ $($field),* })? => { $($($field.children(&mut result);)*)? }),* }
                result
            }
        }
    };
}

// The three operands map to a/b/c in BACKEND_REDESIGN.md B.3. Aux holds
// the existing enum discriminant for LetKind/BinOp/direction/length kind,
// a boolean for JBool/JUndefined/JOptional, or a function's arity.
// JRaw's aux distinguishes expression (0) from statement (1).
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
    pub(super) fn set_flags(&mut self, flags: NodeFlags) {
        self.flags = flags;
    }
    pub(super) fn kill_value(&mut self) {
        assert_eq!(self.op, Op::Let);
        self.words[1] = u32::MAX;
        self.flags.0 |= NodeFlags::DEAD;
    }
}
