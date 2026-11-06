//! Compilation-owned indexed storage for optimized Lambda.
//!
//! The dense node array contains only tags and `u32` payload indices. Large
//! payloads and ordered child lists live in side tables. The conversion APIs
//! are compatibility boundaries for the staged migration and are not used by
//! the production pipeline yet.

use crate::lambda::LamLoc;
use ahash::AHashSet;

use crate::ident::Ident;
use crate::lambda::lam_compat::LetKind;
use crate::lambda::lam_pass_collect::ExternalArityResolver;
use crate::lambda::lam_pass_collect_indexed::{
    IndexedLamStats, collect_info, collect_info_with_external_arity,
};
use crate::lambda::{
    ApInfo, Apply, Constant, DirectionFlag, FunctionAttribute, LFunction, Lambda, LambdaSwitch,
    PrimInfo, Primitive, SwitchDispatch, SwitchKey,
};

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub(crate) struct NodeId(u32);

impl NodeId {
    pub fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Debug, Clone, Copy, Default)]
struct ItemRange {
    start: u32,
    len: u32,
}

impl ItemRange {
    fn checked(start: usize, len: usize) -> Self {
        let end = start
            .checked_add(len)
            .and_then(|end| u32::try_from(end).ok())
            .expect("indexed Lambda side table exceeds u32");
        Self {
            start: u32::try_from(start).expect("indexed Lambda side table exceeds u32"),
            len: end - start as u32,
        }
    }

    fn bounds(self) -> std::ops::Range<usize> {
        let start = self.start as usize;
        start..start + self.len as usize
    }
}

/// Compact hot node. Each integer indexes the matching cold payload vector.
#[derive(Debug, Clone, Copy)]
pub(crate) enum IndexedNode {
    Var(u32),
    GlobalModule(u32),
    Const(u32),
    Apply(u32),
    Function(u32),
    Let(u32),
    LetRec(u32),
    Prim(u32),
    Switch(u32),
    StringSwitch(u32),
    StaticRaise(u32),
    StaticCatch(u32),
    TryWith(u32),
    /// Index into `binaries`: `(body, finally)`.
    TryFinally(u32),
    IfThenElse(u32),
    Sequence(u32),
    Break,
    Continue,
    While(u32),
    For(u32),
    ForOf(u32),
    ForAwaitOf(u32),
    Assign(u32),
}

#[derive(Clone)]
struct GlobalPayload(Ident);
#[derive(Clone)]
struct ApplyPayload(NodeId, ItemRange, ApInfo);
#[derive(Clone)]
struct FunctionPayload(i32, ItemRange, NodeId, FunctionAttribute, LamLoc);
#[derive(Clone)]
struct LetPayload(LetKind, Ident, NodeId, NodeId);
#[derive(Clone)]
struct LetRecPayload(ItemRange, NodeId);
#[derive(Clone)]
struct PrimPayload(Primitive, ItemRange, LamLoc);
#[derive(Clone)]
struct SwitchPayload {
    scrutinee: NodeId,
    consts_full: bool,
    consts: ItemRange,
    blocks_full: bool,
    blocks: ItemRange,
    fail_action: Option<NodeId>,
    dispatch: SwitchDispatch,
}
#[derive(Clone)]
struct StringSwitchPayload(NodeId, ItemRange, Option<NodeId>);
#[derive(Clone)]
struct StaticRaisePayload(i32, ItemRange);
#[derive(Clone)]
struct StaticCatchPayload(NodeId, i32, ItemRange, NodeId);
#[derive(Clone)]
struct TryWithPayload(NodeId, Ident, NodeId);
#[derive(Clone)]
struct TernaryPayload(NodeId, NodeId, NodeId);
#[derive(Clone)]
struct BinaryPayload(NodeId, NodeId);
#[derive(Clone)]
struct ForPayload(Ident, NodeId, NodeId, DirectionFlag, NodeId);
#[derive(Clone)]
struct ForOfPayload(Ident, NodeId, NodeId);
#[derive(Clone)]
struct AssignPayload(Ident, NodeId);

/// Borrowed semantic view. Slices retain the source order recorded by the
/// producer; traversals must not infer order from node allocation.
pub(crate) enum NodeView<'a> {
    Var(&'a Ident),
    GlobalModule(&'a Ident),
    Const(&'a Constant),
    Apply(NodeId, &'a [NodeId], &'a ApInfo),
    Function(i32, &'a [Ident], NodeId, &'a FunctionAttribute, LamLoc),
    Let(LetKind, &'a Ident, NodeId, NodeId),
    LetRec(&'a [(Ident, NodeId)], NodeId),
    Prim(&'a Primitive, &'a [NodeId], &'a LamLoc),
    Switch {
        scrutinee: NodeId,
        consts_full: bool,
        consts: &'a [(SwitchKey, NodeId)],
        blocks_full: bool,
        blocks: &'a [(SwitchKey, NodeId)],
        fail_action: Option<NodeId>,
        dispatch: &'a SwitchDispatch,
    },
    StringSwitch(NodeId, &'a [(String, NodeId)], Option<NodeId>),
    StaticRaise(i32, &'a [NodeId]),
    StaticCatch(NodeId, i32, &'a [Ident], NodeId),
    TryWith(NodeId, &'a Ident, NodeId),
    TryFinally(NodeId, NodeId),
    IfThenElse(NodeId, NodeId, NodeId),
    Sequence(NodeId, NodeId),
    Break,
    Continue,
    While(NodeId, NodeId),
    For(&'a Ident, NodeId, NodeId, DirectionFlag, NodeId),
    ForOf(&'a Ident, NodeId, NodeId),
    ForAwaitOf(&'a Ident, NodeId, NodeId),
    Assign(&'a Ident, NodeId),
}

/// Short-lived owned snapshot used by append-only rewrites. It clones only
/// one node's metadata and child IDs, never a recursive Lambda subtree.
#[derive(Clone)]
pub(crate) enum NodeSnapshot {
    Var(Ident),
    GlobalModule(Ident),
    Const(Constant),
    Apply(NodeId, Vec<NodeId>, ApInfo),
    Function(i32, Vec<Ident>, NodeId, FunctionAttribute, LamLoc),
    Let(LetKind, Ident, NodeId, NodeId),
    LetRec(Vec<(Ident, NodeId)>, NodeId),
    Prim(Primitive, Vec<NodeId>, LamLoc),
    Switch {
        scrutinee: NodeId,
        consts_full: bool,
        consts: Vec<(SwitchKey, NodeId)>,
        blocks_full: bool,
        blocks: Vec<(SwitchKey, NodeId)>,
        fail_action: Option<NodeId>,
        dispatch: SwitchDispatch,
    },
    StringSwitch(NodeId, Vec<(String, NodeId)>, Option<NodeId>),
    StaticRaise(i32, Vec<NodeId>),
    StaticCatch(NodeId, i32, Vec<Ident>, NodeId),
    TryWith(NodeId, Ident, NodeId),
    TryFinally(NodeId, NodeId),
    IfThenElse(NodeId, NodeId, NodeId),
    Sequence(NodeId, NodeId),
    Break,
    Continue,
    While(NodeId, NodeId),
    For(Ident, NodeId, NodeId, DirectionFlag, NodeId),
    ForOf(Ident, NodeId, NodeId),
    ForAwaitOf(Ident, NodeId, NodeId),
    Assign(Ident, NodeId),
}

/// Opaque node IDs are interpreted only through this owning store.
pub(crate) struct IndexedLambda {
    root: NodeId,
    nodes: Vec<IndexedNode>,
    idents: Vec<Ident>,
    constants: Vec<Constant>,
    globals: Vec<GlobalPayload>,
    applies: Vec<ApplyPayload>,
    functions: Vec<FunctionPayload>,
    lets: Vec<LetPayload>,
    letrecs: Vec<LetRecPayload>,
    prims: Vec<PrimPayload>,
    switches: Vec<SwitchPayload>,
    string_switches: Vec<StringSwitchPayload>,
    static_raises: Vec<StaticRaisePayload>,
    static_catches: Vec<StaticCatchPayload>,
    try_withs: Vec<TryWithPayload>,
    ternaries: Vec<TernaryPayload>,
    binaries: Vec<BinaryPayload>,
    fors: Vec<ForPayload>,
    for_ofs: Vec<ForOfPayload>,
    assigns: Vec<AssignPayload>,
    children: Vec<NodeId>,
    bindings: Vec<(Ident, NodeId)>,
    switch_cases: Vec<(SwitchKey, NodeId)>,
    string_cases: Vec<(String, NodeId)>,
}

impl IndexedLambda {
    pub(crate) fn from_lambda(lambda: Lambda) -> Self {
        let mut store = Self::empty();
        store.root = store.lower(lambda);
        store
    }

    fn empty() -> Self {
        Self {
            root: NodeId(0),
            nodes: vec![],
            idents: vec![],
            constants: vec![],
            globals: vec![],
            applies: vec![],
            functions: vec![],
            lets: vec![],
            letrecs: vec![],
            prims: vec![],
            switches: vec![],
            string_switches: vec![],
            static_raises: vec![],
            static_catches: vec![],
            try_withs: vec![],
            ternaries: vec![],
            binaries: vec![],
            fors: vec![],
            for_ofs: vec![],
            assigns: vec![],
            children: vec![],
            bindings: vec![],
            switch_cases: vec![],
            string_cases: vec![],
        }
    }

    pub(crate) fn root(&self) -> NodeId {
        self.root
    }
    pub(crate) fn set_root(&mut self, root: NodeId) {
        assert!(
            root.index() < self.nodes.len(),
            "indexed Lambda root is foreign or out of range"
        );
        self.root = root;
    }
    pub(crate) fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// Imports one recursive Lambda payload at an explicit compatibility boundary.
    pub(crate) fn append_compat_lambda(&mut self, lambda: Lambda) -> NodeId {
        self.lower(lambda)
    }

    pub(crate) fn node(&self, id: NodeId) -> IndexedNode {
        self.nodes[id.index()]
    }

    pub(crate) fn view(&self, id: NodeId) -> NodeView<'_> {
        match self.node(id) {
            IndexedNode::Var(i) => NodeView::Var(&self.idents[i as usize]),
            IndexedNode::GlobalModule(i) => {
                let p = &self.globals[i as usize];
                NodeView::GlobalModule(&p.0)
            }
            IndexedNode::Const(i) => NodeView::Const(&self.constants[i as usize]),
            IndexedNode::Apply(i) => {
                let p = &self.applies[i as usize];
                NodeView::Apply(p.0, &self.children[p.1.bounds()], &p.2)
            }
            IndexedNode::Function(i) => {
                let p = &self.functions[i as usize];
                NodeView::Function(p.0, &self.idents[p.1.bounds()], p.2, &p.3, p.4)
            }
            IndexedNode::Let(i) => {
                let p = &self.lets[i as usize];
                NodeView::Let(p.0, &p.1, p.2, p.3)
            }
            IndexedNode::LetRec(i) => {
                let p = &self.letrecs[i as usize];
                NodeView::LetRec(&self.bindings[p.0.bounds()], p.1)
            }
            IndexedNode::Prim(i) => {
                let p = &self.prims[i as usize];
                NodeView::Prim(&p.0, &self.children[p.1.bounds()], &p.2)
            }
            IndexedNode::Switch(i) => {
                let p = &self.switches[i as usize];
                NodeView::Switch {
                    scrutinee: p.scrutinee,
                    consts_full: p.consts_full,
                    consts: &self.switch_cases[p.consts.bounds()],
                    blocks_full: p.blocks_full,
                    blocks: &self.switch_cases[p.blocks.bounds()],
                    fail_action: p.fail_action,
                    dispatch: &p.dispatch,
                }
            }
            IndexedNode::StringSwitch(i) => {
                let p = &self.string_switches[i as usize];
                NodeView::StringSwitch(p.0, &self.string_cases[p.1.bounds()], p.2)
            }
            IndexedNode::StaticRaise(i) => {
                let p = &self.static_raises[i as usize];
                NodeView::StaticRaise(p.0, &self.children[p.1.bounds()])
            }
            IndexedNode::StaticCatch(i) => {
                let p = &self.static_catches[i as usize];
                NodeView::StaticCatch(p.0, p.1, &self.idents[p.2.bounds()], p.3)
            }
            IndexedNode::TryWith(i) => {
                let p = &self.try_withs[i as usize];
                NodeView::TryWith(p.0, &p.1, p.2)
            }
            IndexedNode::TryFinally(i) => {
                let p = &self.binaries[i as usize];
                NodeView::TryFinally(p.0, p.1)
            }
            IndexedNode::IfThenElse(i) => {
                let p = &self.ternaries[i as usize];
                NodeView::IfThenElse(p.0, p.1, p.2)
            }
            IndexedNode::Sequence(i) => {
                let p = &self.binaries[i as usize];
                NodeView::Sequence(p.0, p.1)
            }
            IndexedNode::Break => NodeView::Break,
            IndexedNode::Continue => NodeView::Continue,
            IndexedNode::While(i) => {
                let p = &self.binaries[i as usize];
                NodeView::While(p.0, p.1)
            }
            IndexedNode::For(i) => {
                let p = &self.fors[i as usize];
                NodeView::For(&p.0, p.1, p.2, p.3, p.4)
            }
            IndexedNode::ForOf(i) => {
                let p = &self.for_ofs[i as usize];
                NodeView::ForOf(&p.0, p.1, p.2)
            }
            IndexedNode::ForAwaitOf(i) => {
                let p = &self.for_ofs[i as usize];
                NodeView::ForAwaitOf(&p.0, p.1, p.2)
            }
            IndexedNode::Assign(i) => {
                let p = &self.assigns[i as usize];
                NodeView::Assign(&p.0, p.1)
            }
        }
    }

    pub(crate) fn materialize(&self) -> Lambda {
        self.materialize_node(self.root)
    }

    pub(crate) fn materialize_node(&self, id: NodeId) -> Lambda {
        match self.view(id) {
            NodeView::Var(id) => Lambda::Lvar(*id),
            NodeView::GlobalModule(id) => Lambda::LglobalModule(*id),
            NodeView::Const(c) => Lambda::Lconst(c.clone()),
            NodeView::Apply(func, args, info) => Lambda::Lapply(Box::new(Apply {
                ap_func: Box::new(self.materialize_node(func)),
                ap_args: args.iter().map(|x| self.materialize_node(*x)).collect(),
                ap_info: info.clone(),
            })),
            NodeView::Function(arity, params, body, attr, loc) => {
                Lambda::Lfunction(Box::new(LFunction {
                    arity,
                    params: params.to_vec(),
                    body: Box::new(self.materialize_node(body)),
                    attr: attr.clone(),
                    loc,
                }))
            }
            NodeView::Let(kind, ident, value, body) => Lambda::Llet(
                kind,
                *ident,
                Box::new(self.materialize_node(value)),
                Box::new(self.materialize_node(body)),
            ),
            NodeView::LetRec(bindings, body) => Lambda::Lletrec(
                bindings
                    .iter()
                    .map(|(ident, value)| (*ident, self.materialize_node(*value)))
                    .collect(),
                Box::new(self.materialize_node(body)),
            ),
            NodeView::Prim(primitive, args, loc) => Lambda::Lprim(Box::new(PrimInfo {
                primitive: primitive.clone(),
                args: args.iter().map(|x| self.materialize_node(*x)).collect(),
                loc: *loc,
            })),
            NodeView::Switch {
                scrutinee,
                consts_full,
                consts,
                blocks_full,
                blocks,
                fail_action,
                dispatch,
            } => Lambda::Lswitch(
                Box::new(self.materialize_node(scrutinee)),
                Box::new(LambdaSwitch {
                    sw_consts_full: consts_full,
                    sw_consts: consts
                        .iter()
                        .map(|(key, value)| (key.clone(), self.materialize_node(*value)))
                        .collect(),
                    sw_blocks_full: blocks_full,
                    sw_blocks: blocks
                        .iter()
                        .map(|(key, value)| (key.clone(), self.materialize_node(*value)))
                        .collect(),
                    sw_failaction: fail_action.map(|value| Box::new(self.materialize_node(value))),
                    sw_dispatch: dispatch.clone(),
                }),
            ),
            NodeView::StringSwitch(scrutinee, cases, default) => Lambda::LstringSwitch(
                Box::new(self.materialize_node(scrutinee)),
                cases
                    .iter()
                    .map(|(key, value)| (key.clone(), self.materialize_node(*value)))
                    .collect(),
                default.map(|value| Box::new(self.materialize_node(value))),
            ),
            NodeView::StaticRaise(exit, args) => Lambda::LstaticRaise(
                exit,
                args.iter().map(|x| self.materialize_node(*x)).collect(),
            ),
            NodeView::StaticCatch(body, exit, params, handler) => Lambda::LstaticCatch(
                Box::new(self.materialize_node(body)),
                (exit, params.to_vec()),
                Box::new(self.materialize_node(handler)),
            ),
            NodeView::TryWith(body, ident, handler) => Lambda::LtryWith(
                Box::new(self.materialize_node(body)),
                *ident,
                Box::new(self.materialize_node(handler)),
            ),
            NodeView::TryFinally(body, finally) => Lambda::LtryFinally(
                Box::new(self.materialize_node(body)),
                Box::new(self.materialize_node(finally)),
            ),
            NodeView::IfThenElse(a, b, c) => Lambda::LifThenElse(
                Box::new(self.materialize_node(a)),
                Box::new(self.materialize_node(b)),
                Box::new(self.materialize_node(c)),
            ),
            NodeView::Sequence(a, b) => Lambda::Lsequence(
                Box::new(self.materialize_node(a)),
                Box::new(self.materialize_node(b)),
            ),
            NodeView::Break => Lambda::Lbreak,
            NodeView::Continue => Lambda::Lcontinue,
            NodeView::While(a, b) => Lambda::Lwhile(
                Box::new(self.materialize_node(a)),
                Box::new(self.materialize_node(b)),
            ),
            NodeView::For(ident, start, end, direction, body) => Lambda::Lfor(
                *ident,
                Box::new(self.materialize_node(start)),
                Box::new(self.materialize_node(end)),
                direction,
                Box::new(self.materialize_node(body)),
            ),
            NodeView::ForOf(ident, iterable, body) => Lambda::Lfor_of(
                *ident,
                Box::new(self.materialize_node(iterable)),
                Box::new(self.materialize_node(body)),
            ),
            NodeView::ForAwaitOf(ident, iterable, body) => Lambda::Lfor_await_of(
                *ident,
                Box::new(self.materialize_node(iterable)),
                Box::new(self.materialize_node(body)),
            ),
            NodeView::Assign(ident, value) => {
                Lambda::Lassign(*ident, Box::new(self.materialize_node(value)))
            }
        }
    }

    pub(crate) fn snapshot(&self, id: NodeId) -> NodeSnapshot {
        match self.view(id) {
            NodeView::Var(id) => NodeSnapshot::Var(*id),
            NodeView::GlobalModule(id) => NodeSnapshot::GlobalModule(*id),
            NodeView::Const(value) => NodeSnapshot::Const(value.clone()),
            NodeView::Apply(function, args, info) => {
                NodeSnapshot::Apply(function, args.to_vec(), info.clone())
            }
            NodeView::Function(arity, params, body, attr, loc) => {
                NodeSnapshot::Function(arity, params.to_vec(), body, attr.clone(), loc)
            }
            NodeView::Let(kind, id, value, body) => NodeSnapshot::Let(kind, *id, value, body),
            NodeView::LetRec(bindings, body) => NodeSnapshot::LetRec(bindings.to_vec(), body),
            NodeView::Prim(primitive, args, loc) => {
                NodeSnapshot::Prim(primitive.clone(), args.to_vec(), *loc)
            }
            NodeView::Switch {
                scrutinee,
                consts_full,
                consts,
                blocks_full,
                blocks,
                fail_action,
                dispatch,
            } => NodeSnapshot::Switch {
                scrutinee,
                consts_full,
                consts: consts.to_vec(),
                blocks_full,
                blocks: blocks.to_vec(),
                fail_action,
                dispatch: dispatch.clone(),
            },
            NodeView::StringSwitch(scrutinee, cases, default) => {
                NodeSnapshot::StringSwitch(scrutinee, cases.to_vec(), default)
            }
            NodeView::StaticRaise(exit, args) => NodeSnapshot::StaticRaise(exit, args.to_vec()),
            NodeView::StaticCatch(body, exit, params, handler) => {
                NodeSnapshot::StaticCatch(body, exit, params.to_vec(), handler)
            }
            NodeView::TryWith(body, id, handler) => NodeSnapshot::TryWith(body, *id, handler),
            NodeView::TryFinally(body, finally) => NodeSnapshot::TryFinally(body, finally),
            NodeView::IfThenElse(a, b, c) => NodeSnapshot::IfThenElse(a, b, c),
            NodeView::Sequence(a, b) => NodeSnapshot::Sequence(a, b),
            NodeView::Break => NodeSnapshot::Break,
            NodeView::Continue => NodeSnapshot::Continue,
            NodeView::While(a, b) => NodeSnapshot::While(a, b),
            NodeView::For(id, start, end, direction, body) => {
                NodeSnapshot::For(*id, start, end, direction, body)
            }
            NodeView::ForOf(id, iterable, body) => NodeSnapshot::ForOf(*id, iterable, body),
            NodeView::ForAwaitOf(id, iterable, body) => {
                NodeSnapshot::ForAwaitOf(*id, iterable, body)
            }
            NodeView::Assign(id, value) => NodeSnapshot::Assign(*id, value),
        }
    }

    pub(crate) fn append(&mut self, node: NodeSnapshot) -> NodeId {
        macro_rules! payload_node {
            ($table:ident, $payload:expr, $variant:ident) => {{
                let index = Self::push_payload(&mut self.$table, $payload);
                self.push_node(IndexedNode::$variant(index))
            }};
        }
        match node {
            NodeSnapshot::Var(id) => payload_node!(idents, id, Var),
            NodeSnapshot::GlobalModule(id) => {
                payload_node!(globals, GlobalPayload(id), GlobalModule)
            }
            NodeSnapshot::Const(value) => payload_node!(constants, value, Const),
            NodeSnapshot::Apply(function, args, info) => {
                let args = self.push_children(args);
                payload_node!(applies, ApplyPayload(function, args, info), Apply)
            }
            NodeSnapshot::Function(arity, params, body, attr, loc) => {
                let params = self.push_idents(params);
                payload_node!(
                    functions,
                    FunctionPayload(arity, params, body, attr, loc),
                    Function
                )
            }
            NodeSnapshot::Let(kind, id, value, body) => {
                payload_node!(lets, LetPayload(kind, id, value, body), Let)
            }
            NodeSnapshot::LetRec(bindings, body) => {
                let start = self.bindings.len();
                self.bindings.extend(bindings);
                let range = ItemRange::checked(start, self.bindings.len() - start);
                payload_node!(letrecs, LetRecPayload(range, body), LetRec)
            }
            NodeSnapshot::Prim(primitive, args, loc) => {
                let args = self.push_children(args);
                payload_node!(prims, PrimPayload(primitive, args, loc), Prim)
            }
            NodeSnapshot::Switch {
                scrutinee,
                consts_full,
                consts,
                blocks_full,
                blocks,
                fail_action,
                dispatch,
            } => {
                let start = self.switch_cases.len();
                self.switch_cases.extend(consts);
                let consts = ItemRange::checked(start, self.switch_cases.len() - start);
                let start = self.switch_cases.len();
                self.switch_cases.extend(blocks);
                let blocks = ItemRange::checked(start, self.switch_cases.len() - start);
                payload_node!(
                    switches,
                    SwitchPayload {
                        scrutinee,
                        consts_full,
                        consts,
                        blocks_full,
                        blocks,
                        fail_action,
                        dispatch
                    },
                    Switch
                )
            }
            NodeSnapshot::StringSwitch(scrutinee, cases, default) => {
                let start = self.string_cases.len();
                self.string_cases.extend(cases);
                let cases = ItemRange::checked(start, self.string_cases.len() - start);
                payload_node!(
                    string_switches,
                    StringSwitchPayload(scrutinee, cases, default),
                    StringSwitch
                )
            }
            NodeSnapshot::StaticRaise(exit, args) => {
                let args = self.push_children(args);
                payload_node!(static_raises, StaticRaisePayload(exit, args), StaticRaise)
            }
            NodeSnapshot::StaticCatch(body, exit, params, handler) => {
                let params = self.push_idents(params);
                payload_node!(
                    static_catches,
                    StaticCatchPayload(body, exit, params, handler),
                    StaticCatch
                )
            }
            NodeSnapshot::TryWith(body, id, handler) => {
                payload_node!(try_withs, TryWithPayload(body, id, handler), TryWith)
            }
            NodeSnapshot::TryFinally(body, finally) => {
                payload_node!(binaries, BinaryPayload(body, finally), TryFinally)
            }
            NodeSnapshot::IfThenElse(a, b, c) => {
                payload_node!(ternaries, TernaryPayload(a, b, c), IfThenElse)
            }
            NodeSnapshot::Sequence(a, b) => payload_node!(binaries, BinaryPayload(a, b), Sequence),
            NodeSnapshot::Break => self.push_node(IndexedNode::Break),
            NodeSnapshot::Continue => self.push_node(IndexedNode::Continue),
            NodeSnapshot::While(a, b) => payload_node!(binaries, BinaryPayload(a, b), While),
            NodeSnapshot::For(id, start, end, direction, body) => {
                payload_node!(fors, ForPayload(id, start, end, direction, body), For)
            }
            NodeSnapshot::ForOf(id, iterable, body) => {
                payload_node!(for_ofs, ForOfPayload(id, iterable, body), ForOf)
            }
            NodeSnapshot::ForAwaitOf(id, iterable, body) => {
                payload_node!(for_ofs, ForOfPayload(id, iterable, body), ForAwaitOf)
            }
            NodeSnapshot::Assign(id, value) => {
                payload_node!(assigns, AssignPayload(id, value), Assign)
            }
        }
    }

    fn node_side_payload_shallow_bytes(&self, node: NodeId) -> usize {
        let range_bytes = |range: ItemRange, item_size: usize| range.len as usize * item_size;
        match self.node(node) {
            IndexedNode::Var(_) => std::mem::size_of::<Ident>(),
            IndexedNode::GlobalModule(_) => std::mem::size_of::<GlobalPayload>(),
            IndexedNode::Const(_) => std::mem::size_of::<Constant>(),
            IndexedNode::Apply(index) => {
                let payload = &self.applies[index as usize];
                std::mem::size_of::<ApplyPayload>()
                    + range_bytes(payload.1, std::mem::size_of::<NodeId>())
            }
            IndexedNode::Function(index) => {
                let payload = &self.functions[index as usize];
                std::mem::size_of::<FunctionPayload>()
                    + range_bytes(payload.1, std::mem::size_of::<Ident>())
            }
            IndexedNode::Let(_) => std::mem::size_of::<LetPayload>(),
            IndexedNode::LetRec(index) => {
                let payload = &self.letrecs[index as usize];
                std::mem::size_of::<LetRecPayload>()
                    + range_bytes(payload.0, std::mem::size_of::<(Ident, NodeId)>())
            }
            IndexedNode::Prim(index) => {
                let payload = &self.prims[index as usize];
                std::mem::size_of::<PrimPayload>()
                    + range_bytes(payload.1, std::mem::size_of::<NodeId>())
            }
            IndexedNode::Switch(index) => {
                let payload = &self.switches[index as usize];
                std::mem::size_of::<SwitchPayload>()
                    + range_bytes(payload.consts, std::mem::size_of::<(SwitchKey, NodeId)>())
                    + range_bytes(payload.blocks, std::mem::size_of::<(SwitchKey, NodeId)>())
            }
            IndexedNode::StringSwitch(index) => {
                let payload = &self.string_switches[index as usize];
                std::mem::size_of::<StringSwitchPayload>()
                    + range_bytes(payload.1, std::mem::size_of::<(String, NodeId)>())
            }
            IndexedNode::StaticRaise(index) => {
                let payload = &self.static_raises[index as usize];
                std::mem::size_of::<StaticRaisePayload>()
                    + range_bytes(payload.1, std::mem::size_of::<NodeId>())
            }
            IndexedNode::StaticCatch(index) => {
                let payload = &self.static_catches[index as usize];
                std::mem::size_of::<StaticCatchPayload>()
                    + range_bytes(payload.2, std::mem::size_of::<Ident>())
            }
            IndexedNode::TryWith(_) => std::mem::size_of::<TryWithPayload>(),
            IndexedNode::IfThenElse(_) => std::mem::size_of::<TernaryPayload>(),
            IndexedNode::Sequence(_) | IndexedNode::While(_) | IndexedNode::TryFinally(_) => {
                std::mem::size_of::<BinaryPayload>()
            }
            IndexedNode::Break | IndexedNode::Continue => 0,
            IndexedNode::For(_) => std::mem::size_of::<ForPayload>(),
            IndexedNode::ForOf(_) | IndexedNode::ForAwaitOf(_) => {
                std::mem::size_of::<ForOfPayload>()
            }
            IndexedNode::Assign(_) => std::mem::size_of::<AssignPayload>(),
        }
    }

    #[cfg(test)]
    pub(crate) fn reachable_unique_nodes(&self, roots: &[NodeId]) -> usize {
        fn visit(store: &IndexedLambda, node: NodeId, seen: &mut AHashSet<NodeId>) {
            if !seen.insert(node) {
                return;
            }
            let mut child = |node| visit(store, node, seen);
            match store.view(node) {
                NodeView::Apply(function, args, _) => {
                    child(function);
                    for node in args {
                        child(*node);
                    }
                }
                NodeView::Function(_, _, body, _, _) => child(body),
                NodeView::Let(_, _, value, body) => {
                    child(value);
                    child(body);
                }
                NodeView::LetRec(bindings, body) => {
                    for (_, node) in bindings {
                        child(*node);
                    }
                    child(body);
                }
                NodeView::Prim(_, args, _) | NodeView::StaticRaise(_, args) => {
                    for node in args {
                        child(*node);
                    }
                }
                NodeView::Switch {
                    scrutinee,
                    consts,
                    blocks,
                    fail_action,
                    ..
                } => {
                    child(scrutinee);
                    for (_, node) in consts {
                        child(*node);
                    }
                    for (_, node) in blocks {
                        child(*node);
                    }
                    if let Some(node) = fail_action {
                        child(node);
                    }
                }
                NodeView::StringSwitch(scrutinee, cases, default) => {
                    child(scrutinee);
                    for (_, node) in cases {
                        child(*node);
                    }
                    if let Some(node) = default {
                        child(node);
                    }
                }
                NodeView::StaticCatch(body, _, _, handler)
                | NodeView::TryWith(body, _, handler)
                | NodeView::TryFinally(body, handler) => {
                    child(body);
                    child(handler);
                }
                NodeView::IfThenElse(a, b, c) | NodeView::For(_, a, b, _, c) => {
                    child(a);
                    child(b);
                    child(c);
                }
                NodeView::Sequence(a, b)
                | NodeView::While(a, b)
                | NodeView::ForOf(_, a, b)
                | NodeView::ForAwaitOf(_, a, b) => {
                    child(a);
                    child(b);
                }
                NodeView::Assign(_, value) => child(value),
                NodeView::Var(_)
                | NodeView::GlobalModule(_)
                | NodeView::Const(_)
                | NodeView::Break
                | NodeView::Continue => {}
            }
        }
        let mut seen = AHashSet::new();
        for root in roots {
            assert!(
                self.contains(*root),
                "indexed Lambda diagnostic root is out of range"
            );
            visit(self, *root, &mut seen);
        }
        seen.len()
    }

    pub(crate) fn contains(&self, node: NodeId) -> bool {
        node.index() < self.nodes.len()
    }

    fn push_node(&mut self, node: IndexedNode) -> NodeId {
        let id = NodeId(u32::try_from(self.nodes.len()).expect("indexed Lambda exceeds u32 nodes"));
        self.nodes.push(node);
        id
    }

    #[cfg(test)]
    pub(crate) fn append_sequence(&mut self, first: NodeId, second: NodeId) -> NodeId {
        let payload = Self::push_payload(&mut self.binaries, BinaryPayload(first, second));
        self.push_node(IndexedNode::Sequence(payload))
    }

    fn push_payload<T>(table: &mut Vec<T>, payload: T) -> u32 {
        let index = u32::try_from(table.len()).expect("indexed Lambda payload table exceeds u32");
        table.push(payload);
        index
    }

    fn push_children(&mut self, values: Vec<NodeId>) -> ItemRange {
        let start = self.children.len();
        self.children.extend(values);
        ItemRange::checked(start, self.children.len() - start)
    }

    fn push_idents(&mut self, values: Vec<Ident>) -> ItemRange {
        let start = self.idents.len();
        self.idents.extend(values);
        ItemRange::checked(start, self.idents.len() - start)
    }

    fn lower_many(&mut self, values: Vec<Lambda>) -> ItemRange {
        let lowered = values.into_iter().map(|value| self.lower(value)).collect();
        self.push_children(lowered)
    }

    fn lower(&mut self, lambda: Lambda) -> NodeId {
        macro_rules! payload_node {
            ($table:ident, $payload:expr, $variant:ident) => {{
                let index = Self::push_payload(&mut self.$table, $payload);
                self.push_node(IndexedNode::$variant(index))
            }};
        }
        match lambda {
            Lambda::Lvar(id) => payload_node!(idents, id, Var),
            Lambda::LglobalModule(id) => {
                payload_node!(globals, GlobalPayload(id), GlobalModule)
            }
            Lambda::Lconst(c) => payload_node!(constants, c, Const),
            Lambda::Lapply(apply) => {
                let func = self.lower(*apply.ap_func);
                let args = self.lower_many(apply.ap_args);
                payload_node!(applies, ApplyPayload(func, args, apply.ap_info), Apply)
            }
            Lambda::Lfunction(func) => {
                let body = self.lower(*func.body);
                let params = self.push_idents(func.params);
                payload_node!(
                    functions,
                    FunctionPayload(func.arity, params, body, func.attr, func.loc),
                    Function
                )
            }
            Lambda::Llet(kind, id, value, body) => {
                let value = self.lower(*value);
                let body = self.lower(*body);
                payload_node!(lets, LetPayload(kind, id, value, body), Let)
            }
            Lambda::Lletrec(values, body) => {
                let values = values
                    .into_iter()
                    .map(|(id, value)| (id, self.lower(value)))
                    .collect::<Vec<_>>();
                let start = self.bindings.len();
                self.bindings.extend(values);
                let range = ItemRange::checked(start, self.bindings.len() - start);
                let body = self.lower(*body);
                payload_node!(letrecs, LetRecPayload(range, body), LetRec)
            }
            Lambda::Lprim(info) => {
                let args = self.lower_many(info.args);
                payload_node!(prims, PrimPayload(info.primitive, args, info.loc), Prim)
            }
            Lambda::Lswitch(scrutinee, switch) => {
                let scrutinee = self.lower(*scrutinee);
                let values = switch
                    .sw_consts
                    .into_iter()
                    .map(|(key, value)| (key, self.lower(value)))
                    .collect::<Vec<_>>();
                let start = self.switch_cases.len();
                self.switch_cases.extend(values);
                let consts = ItemRange::checked(start, self.switch_cases.len() - start);
                let values = switch
                    .sw_blocks
                    .into_iter()
                    .map(|(key, value)| (key, self.lower(value)))
                    .collect::<Vec<_>>();
                let start = self.switch_cases.len();
                self.switch_cases.extend(values);
                let blocks = ItemRange::checked(start, self.switch_cases.len() - start);
                let fail_action = switch.sw_failaction.map(|value| self.lower(*value));
                payload_node!(
                    switches,
                    SwitchPayload {
                        scrutinee,
                        consts_full: switch.sw_consts_full,
                        consts,
                        blocks_full: switch.sw_blocks_full,
                        blocks,
                        fail_action,
                        dispatch: switch.sw_dispatch
                    },
                    Switch
                )
            }
            Lambda::LstringSwitch(scrutinee, cases, default) => {
                let scrutinee = self.lower(*scrutinee);
                let values = cases
                    .into_iter()
                    .map(|(key, value)| (key, self.lower(value)))
                    .collect::<Vec<_>>();
                let start = self.string_cases.len();
                self.string_cases.extend(values);
                let cases = ItemRange::checked(start, self.string_cases.len() - start);
                let default = default.map(|value| self.lower(*value));
                payload_node!(
                    string_switches,
                    StringSwitchPayload(scrutinee, cases, default),
                    StringSwitch
                )
            }
            Lambda::LstaticRaise(id, args) => {
                let args = self.lower_many(args);
                payload_node!(static_raises, StaticRaisePayload(id, args), StaticRaise)
            }
            Lambda::LstaticCatch(body, (id, params), handler) => {
                let body = self.lower(*body);
                let params = self.push_idents(params);
                let handler = self.lower(*handler);
                payload_node!(
                    static_catches,
                    StaticCatchPayload(body, id, params, handler),
                    StaticCatch
                )
            }
            Lambda::LtryWith(body, id, handler) => {
                let body = self.lower(*body);
                let handler = self.lower(*handler);
                payload_node!(try_withs, TryWithPayload(body, id, handler), TryWith)
            }
            Lambda::LtryFinally(body, finally) => {
                let body = self.lower(*body);
                let finally = self.lower(*finally);
                payload_node!(binaries, BinaryPayload(body, finally), TryFinally)
            }
            Lambda::LifThenElse(a, b, c) => {
                let a = self.lower(*a);
                let b = self.lower(*b);
                let c = self.lower(*c);
                payload_node!(ternaries, TernaryPayload(a, b, c), IfThenElse)
            }
            Lambda::Lsequence(a, b) => {
                let a = self.lower(*a);
                let b = self.lower(*b);
                payload_node!(binaries, BinaryPayload(a, b), Sequence)
            }
            Lambda::Lbreak => self.push_node(IndexedNode::Break),
            Lambda::Lcontinue => self.push_node(IndexedNode::Continue),
            Lambda::Lwhile(a, b) => {
                let a = self.lower(*a);
                let b = self.lower(*b);
                payload_node!(binaries, BinaryPayload(a, b), While)
            }
            Lambda::Lfor(id, start, end, direction, body) => {
                let start = self.lower(*start);
                let end = self.lower(*end);
                let body = self.lower(*body);
                payload_node!(fors, ForPayload(id, start, end, direction, body), For)
            }
            Lambda::Lfor_of(id, iterable, body) => {
                let iterable = self.lower(*iterable);
                let body = self.lower(*body);
                payload_node!(for_ofs, ForOfPayload(id, iterable, body), ForOf)
            }
            Lambda::Lfor_await_of(id, iterable, body) => {
                let iterable = self.lower(*iterable);
                let body = self.lower(*body);
                payload_node!(for_ofs, ForOfPayload(id, iterable, body), ForAwaitOf)
            }
            Lambda::Lassign(id, value) => {
                let value = self.lower(*value);
                payload_node!(assigns, AssignPayload(id, value), Assign)
            }
        }
    }
}

/// Root-directed occupancy report for the append-only indexed store.
/// `lam_analysis::size` is deliberately not used: it is a weighted inline
/// heuristic rather than a node, edge, or byte count.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IndexedStorageMeasurements {
    /// Number of hot-node allocations retained in the append-only store.
    pub node_allocations: usize,
    /// Semantic child edges visited from the current root, including repeated
    /// visits through shared nodes.
    pub current_root_edge_visits: usize,
    /// Unique nodes reachable from the canonical current root.
    pub current_root_unique_nodes: usize,
    /// Unique nodes reachable from identifier metadata roots.
    pub metadata_unique_nodes: usize,
    /// Unique nodes reachable from grouped backend and export-map roots.
    pub backend_unique_nodes: usize,
    /// Unique union of current-root, backend-root, and metadata reachability.
    pub live_unique_nodes: usize,
    /// Allocated nodes outside the live union.
    pub superseded_nodes: usize,
    /// Occupied bytes in the dense hot-node vector.
    pub hot_node_occupied_bytes: usize,
    /// Allocated capacity bytes in the dense hot-node vector.
    pub hot_node_capacity_bytes: usize,
    /// Shallow bytes occupied by side-table elements. Heap allocations nested
    /// inside `Ident`, `Constant`, `Primitive`, locations, and strings are
    /// intentionally excluded rather than reported as an underestimated deep
    /// total.
    pub side_payload_shallow_occupied_bytes: usize,
    /// Allocated capacity bytes for all side-table vectors, excluding nested heaps.
    pub side_payload_shallow_capacity_bytes: usize,
    /// Always false until exhaustive nested-allocation accounting is implemented.
    pub nested_heap_bytes_included: bool,
    /// Shallow side-payload bytes reachable from the current root.
    pub current_live_side_payload_shallow_bytes: usize,
    /// Shallow side-payload bytes reachable through backend roots but not the
    /// canonical grouped root.
    pub backend_retained_only_side_payload_shallow_bytes: usize,
    /// Shallow side-payload bytes reachable only through identifier metadata.
    pub metadata_retained_only_side_payload_shallow_bytes: usize,
    /// Shallow side-payload bytes unreachable from current, backend, and metadata roots.
    pub superseded_unreachable_side_payload_shallow_bytes: usize,
}

/// Owns the canonical indexed root, its append-only store, and every metadata
/// table containing IDs into that store. Public pass entrypoints operate on
/// the current root only, so callers cannot accidentally pair a raw `NodeId`
/// from another compilation with this store. Private recursive helpers follow
/// the same-store contract used by the compiler's other index arenas.
pub struct IndexedLambdaContext {
    store: IndexedLambda,
    /// Present only during the single-tree optimizer phase. Grouping consumes
    /// this authority; backend groups then become the only live program roots.
    optimizer_root: Option<NodeId>,
    metadata: IndexedLamStats,
    /// Roots retained by the grouped pre-JS result after coercion. The
    /// canonical optimizer root remains `store.root`; these immutable roots
    /// are a single-owner view over the same store, not another mutation API.
    backend_roots: Vec<NodeId>,
    #[cfg(test)]
    substitution_table_peak_unique_nodes: usize,
    #[cfg(test)]
    beta_substitution_peak_unique_nodes: usize,
}

impl IndexedLambdaContext {
    /// Creates one compilation-owned store and metadata context.
    pub fn from_lambda(lambda: Lambda, exports: impl IntoIterator<Item = Ident>) -> Self {
        let store = IndexedLambda::from_lambda(lambda);
        let optimizer_root = Some(store.root());
        Self {
            store,
            optimizer_root,
            metadata: IndexedLamStats::new(exports),
            backend_roots: Vec::new(),
            #[cfg(test)]
            substitution_table_peak_unique_nodes: 0,
            #[cfg(test)]
            beta_substitution_peak_unique_nodes: 0,
        }
    }

    #[cfg(test)]
    pub(crate) fn from_store(
        store: IndexedLambda,
        exports: impl IntoIterator<Item = Ident>,
    ) -> Self {
        let optimizer_root = Some(store.root());
        Self {
            store,
            optimizer_root,
            metadata: IndexedLamStats::new(exports),
            backend_roots: Vec::new(),
            substitution_table_peak_unique_nodes: 0,
            beta_substitution_peak_unique_nodes: 0,
        }
    }

    /// Collects identifier metadata from the canonical current root.
    pub fn collect_info(&mut self) {
        let root = self.store.root();
        collect_info(&self.store, &mut self.metadata, root);
    }

    /// Collects metadata while resolving external arities in reference order.
    pub fn collect_info_with_external_arity(&mut self, resolver: &mut ExternalArityResolver<'_>) {
        let root = self.store.root();
        collect_info_with_external_arity(&self.store, &mut self.metadata, root, resolver);
    }

    pub(crate) fn metadata(&self) -> &IndexedLamStats {
        &self.metadata
    }

    pub(crate) fn metadata_mut(&mut self) -> &mut IndexedLamStats {
        &mut self.metadata
    }

    /// Materializes the canonical root at the inactive compatibility boundary.
    pub fn materialize(&self) -> Lambda {
        self.store.materialize_node(self.current_root())
    }

    /// Returns all hot-node allocations, including superseded generations.
    pub fn node_count(&self) -> usize {
        self.store.node_count()
    }

    /// Measures current, metadata-retained, and superseded arena storage.
    pub fn storage_measurements(&self) -> IndexedStorageMeasurements {
        fn walk(
            store: &IndexedLambda,
            node: NodeId,
            unique: &mut AHashSet<NodeId>,
            edges: &mut usize,
            count_repeated_edges: bool,
        ) {
            let first_visit = unique.insert(node);
            if !first_visit && !count_repeated_edges {
                return;
            }
            let mut child = |node| {
                *edges += 1;
                walk(store, node, unique, edges, count_repeated_edges);
            };
            match store.view(node) {
                NodeView::Apply(function, args, _) => {
                    child(function);
                    for node in args {
                        child(*node);
                    }
                }
                NodeView::Function(_, _, body, _, _) => child(body),
                NodeView::Let(_, _, value, body) => {
                    child(value);
                    child(body);
                }
                NodeView::LetRec(bindings, body) => {
                    for (_, node) in bindings {
                        child(*node);
                    }
                    child(body);
                }
                NodeView::Prim(_, args, _) | NodeView::StaticRaise(_, args) => {
                    for node in args {
                        child(*node);
                    }
                }
                NodeView::Switch {
                    scrutinee,
                    consts,
                    blocks,
                    fail_action,
                    ..
                } => {
                    child(scrutinee);
                    for (_, node) in consts {
                        child(*node);
                    }
                    for (_, node) in blocks {
                        child(*node);
                    }
                    if let Some(node) = fail_action {
                        child(node);
                    }
                }
                NodeView::StringSwitch(scrutinee, cases, default) => {
                    child(scrutinee);
                    for (_, node) in cases {
                        child(*node);
                    }
                    if let Some(node) = default {
                        child(node);
                    }
                }
                NodeView::StaticCatch(body, _, _, handler)
                | NodeView::TryWith(body, _, handler)
                | NodeView::TryFinally(body, handler) => {
                    child(body);
                    child(handler);
                }
                NodeView::IfThenElse(a, b, c) | NodeView::For(_, a, b, _, c) => {
                    child(a);
                    child(b);
                    child(c);
                }
                NodeView::Sequence(a, b)
                | NodeView::While(a, b)
                | NodeView::ForOf(_, a, b)
                | NodeView::ForAwaitOf(_, a, b) => {
                    child(a);
                    child(b);
                }
                NodeView::Assign(_, value) => child(value),
                NodeView::Var(_)
                | NodeView::GlobalModule(_)
                | NodeView::Const(_)
                | NodeView::Break
                | NodeView::Continue => {}
            }
        }
        fn bytes<T>(values: &Vec<T>) -> (usize, usize) {
            (
                values.len() * std::mem::size_of::<T>(),
                values.capacity() * std::mem::size_of::<T>(),
            )
        }
        let mut current = AHashSet::new();
        let mut current_edges = 0;
        if let Some(root) = self.optimizer_root {
            walk(&self.store, root, &mut current, &mut current_edges, true);
        }
        let mut metadata = AHashSet::new();
        let mut ignored_edges = 0;
        for root in self.metadata.retained_roots() {
            assert!(
                self.store.contains(root),
                "indexed Lambda metadata root is out of range"
            );
            walk(&self.store, root, &mut metadata, &mut ignored_edges, false);
        }
        let mut backend = AHashSet::new();
        for root in self.backend_roots.iter().copied() {
            assert!(
                self.store.contains(root),
                "indexed Lambda backend root is out of range"
            );
            walk(&self.store, root, &mut backend, &mut ignored_edges, false);
        }
        let mut live = current.clone();
        live.extend(backend.iter().copied());
        live.extend(metadata.iter().copied());
        let tables = [
            bytes(&self.store.idents),
            bytes(&self.store.constants),
            bytes(&self.store.globals),
            bytes(&self.store.applies),
            bytes(&self.store.functions),
            bytes(&self.store.lets),
            bytes(&self.store.letrecs),
            bytes(&self.store.prims),
            bytes(&self.store.switches),
            bytes(&self.store.string_switches),
            bytes(&self.store.static_raises),
            bytes(&self.store.static_catches),
            bytes(&self.store.try_withs),
            bytes(&self.store.ternaries),
            bytes(&self.store.binaries),
            bytes(&self.store.fors),
            bytes(&self.store.for_ofs),
            bytes(&self.store.assigns),
            bytes(&self.store.children),
            bytes(&self.store.bindings),
            bytes(&self.store.switch_cases),
            bytes(&self.store.string_cases),
        ];
        let (side_occupied, side_capacity) = tables
            .into_iter()
            .fold((0, 0), |(ao, ac), (o, c)| (ao + o, ac + c));
        let payload_bytes = |nodes: &AHashSet<NodeId>| {
            nodes
                .iter()
                .map(|node| self.store.node_side_payload_shallow_bytes(*node))
                .sum::<usize>()
        };
        let backend_only = backend
            .difference(&current)
            .copied()
            .collect::<AHashSet<_>>();
        let metadata_only = metadata
            .difference(&current)
            .filter(|node| !backend.contains(node))
            .copied()
            .collect::<AHashSet<_>>();
        let unreachable = (0..self.store.nodes.len())
            .map(|index| NodeId(index as u32))
            .filter(|node| !live.contains(node))
            .collect::<AHashSet<_>>();
        let current_payload = payload_bytes(&current);
        let backend_only_payload = payload_bytes(&backend_only);
        let metadata_only_payload = payload_bytes(&metadata_only);
        let unreachable_payload = payload_bytes(&unreachable);
        debug_assert_eq!(
            current_payload + backend_only_payload + metadata_only_payload + unreachable_payload,
            side_occupied
        );
        IndexedStorageMeasurements {
            node_allocations: self.store.nodes.len(),
            current_root_edge_visits: current_edges,
            current_root_unique_nodes: current.len(),
            metadata_unique_nodes: metadata.len(),
            backend_unique_nodes: backend.len(),
            live_unique_nodes: live.len(),
            superseded_nodes: self.store.nodes.len() - live.len(),
            hot_node_occupied_bytes: self.store.nodes.len() * std::mem::size_of::<IndexedNode>(),
            hot_node_capacity_bytes: self.store.nodes.capacity()
                * std::mem::size_of::<IndexedNode>(),
            side_payload_shallow_occupied_bytes: side_occupied,
            side_payload_shallow_capacity_bytes: side_capacity,
            nested_heap_bytes_included: false,
            current_live_side_payload_shallow_bytes: current_payload,
            backend_retained_only_side_payload_shallow_bytes: backend_only_payload,
            metadata_retained_only_side_payload_shallow_bytes: metadata_only_payload,
            superseded_unreachable_side_payload_shallow_bytes: unreachable_payload,
        }
    }

    pub(crate) fn store(&self) -> &IndexedLambda {
        &self.store
    }

    pub(crate) fn store_mut(&mut self) -> &mut IndexedLambda {
        &mut self.store
    }

    /// Imports one function body returned by the CMJ resolver into this
    /// compilation's existing store. JS lowering calls this only after the
    /// reference eligibility checks and resolver query have selected the
    /// function for beta reduction.
    pub(crate) fn import_cmj_function(&mut self, function: LFunction) -> NodeId {
        self.store
            .append_compat_lambda(Lambda::Lfunction(Box::new(function)))
    }

    /// Splits the owner-held store and metadata. Optimizer passes and
    /// consumer-side indexed beta (after grouping has consumed
    /// `optimizer_root`) share the same state.
    pub(crate) fn parts_mut(&mut self) -> (&mut IndexedLambda, &mut IndexedLamStats) {
        (&mut self.store, &mut self.metadata)
    }

    #[cfg(test)]
    pub(crate) fn record_beta_substitution_peak(&mut self, peak: usize) {
        self.beta_substitution_peak_unique_nodes = peak;
    }

    #[cfg(test)]
    pub(crate) fn beta_substitution_peak_unique_nodes(&self) -> usize {
        self.beta_substitution_peak_unique_nodes
    }

    pub(crate) fn current_root(&self) -> NodeId {
        self.optimizer_root
            .expect("indexed Lambda optimizer root was consumed by grouping")
    }

    pub(crate) fn register_backend_roots(&mut self, roots: impl IntoIterator<Item = NodeId>) {
        let roots = roots.into_iter().collect::<Vec<_>>();
        assert!(
            roots.iter().all(|root| self.store.contains(*root)),
            "indexed Lambda backend root is out of range"
        );
        // Coercion consumes the single-tree program authority even for an
        // empty module. No group RHS is mislabeled as a whole program root.
        self.optimizer_root = None;
        self.backend_roots = roots;
    }

    #[cfg(test)]
    pub(crate) fn backend_roots(&self) -> &[NodeId] {
        &self.backend_roots
    }

    pub(crate) fn replace_root(&mut self, root: NodeId) {
        assert!(
            self.optimizer_root.is_some(),
            "cannot replace a consumed optimizer root"
        );
        self.store.set_root(root);
        self.optimizer_root = Some(root);
    }

    #[cfg(test)]
    pub(crate) fn record_substitution_table_peak(&mut self, peak: usize) {
        self.substitution_table_peak_unique_nodes = peak;
    }

    #[cfg(test)]
    pub(crate) fn substitution_table_peak_unique_nodes(&self) -> usize {
        self.substitution_table_peak_unique_nodes
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ident::IdentFlags;
    use crate::lambda::ApplyStatus;

    fn id(name: &str, stamp: i32) -> Ident {
        Ident::new(name, stamp, IdentFlags::NONE)
    }
    fn assert_round_trip(lambda: Lambda) {
        let expected = format!("{lambda:#?}");
        let indexed = IndexedLambda::from_lambda(lambda.clone());
        assert_eq!(expected, format!("{:#?}", indexed.materialize()));

        let context = IndexedLambdaContext::from_lambda(lambda.clone(), []);
        let mut indexed_sexp = Vec::new();
        crate::lambda::sexp_lambda::print_indexed_context(&context, true, &mut indexed_sexp)
            .unwrap();
        let mut recursive_sexp = Vec::new();
        crate::lambda::sexp_lambda::print_lambda_with_locs(&lambda, &mut recursive_sexp).unwrap();
        assert_eq!(indexed_sexp, recursive_sexp);
    }

    #[test]
    fn compact_node_is_two_words() {
        assert_eq!(std::mem::size_of::<IndexedNode>(), 8);
        assert_eq!(std::mem::size_of::<NodeId>(), 4);
    }

    #[test]
    fn round_trip_preserves_node_families_and_order() {
        let x = id("x", 1);
        let y = id("y", 2);
        let loc = LamLoc::NONE;
        let var = || Lambda::Lvar(x);
        let int = || Lambda::Lconst(Constant::int(1));
        for leaf in [
            var(),
            Lambda::LglobalModule(y),
            int(),
            Lambda::Lbreak,
            Lambda::Lcontinue,
        ] {
            assert_round_trip(leaf);
        }
        let info = ApInfo {
            loc,
            status: ApplyStatus::InferFull,
        };
        let samples = vec![
            Lambda::Lapply(Box::new(Apply {
                ap_func: Box::new(var()),
                ap_args: vec![int(), Lambda::Lvar(y)],
                ap_info: info,
            })),
            Lambda::Lfunction(Box::new(LFunction {
                loc: LamLoc::NONE,
                arity: 2,
                params: vec![x, y],
                body: Box::new(var()),
                attr: FunctionAttribute {
                    async_: true,
                    ..FunctionAttribute::default()
                },
            })),
            Lambda::Llet(LetKind::Strict, x, Box::new(int()), Box::new(var())),
            Lambda::Lletrec(vec![(x, int()), (y, var())], Box::new(var())),
            Lambda::Lprim(Box::new(PrimInfo {
                primitive: Primitive::Pnot,
                args: vec![int(), var()],
                loc,
            })),
            Lambda::Lswitch(
                Box::new(var()),
                Box::new(LambdaSwitch {
                    sw_consts_full: false,
                    sw_consts: vec![(SwitchKey::Int(2), int()), (SwitchKey::Int(1), var())],
                    sw_blocks_full: true,
                    sw_blocks: vec![(SwitchKey::Int(4), int()), (SwitchKey::Int(3), var())],
                    sw_failaction: Some(Box::new(int())),
                    sw_dispatch: SwitchDispatch::Direct,
                }),
            ),
            Lambda::LstringSwitch(
                Box::new(var()),
                vec![("b".into(), int()), ("a".into(), var())],
                Some(Box::new(int())),
            ),
            Lambda::LstaticRaise(3, vec![int(), var()]),
            Lambda::LstaticCatch(Box::new(var()), (3, vec![x, y]), Box::new(int())),
            Lambda::LtryWith(Box::new(var()), y, Box::new(int())),
            Lambda::LifThenElse(Box::new(var()), Box::new(int()), Box::new(Lambda::Lvar(y))),
            Lambda::Lsequence(Box::new(var()), Box::new(int())),
            Lambda::Lwhile(Box::new(var()), Box::new(int())),
            Lambda::Lfor(
                x,
                Box::new(int()),
                Box::new(Lambda::Lconst(Constant::int(9))),
                DirectionFlag::Downto,
                Box::new(var()),
            ),
            Lambda::Lfor_of(x, Box::new(var()), Box::new(int())),
            Lambda::Lfor_await_of(x, Box::new(var()), Box::new(int())),
            Lambda::Lassign(x, Box::new(int())),
        ];
        for sample in samples {
            assert_round_trip(sample);
        }
    }

    #[test]
    fn shared_child_payload_is_counted_once_in_live_storage() {
        let mut store = IndexedLambda::from_lambda(Lambda::Lconst(Constant::int(5)));
        let shared = store.root;
        let root = store.append_sequence(shared, shared);
        store.set_root(root);
        let context = IndexedLambdaContext::from_store(store, []);
        let metrics = context.storage_measurements();
        assert_eq!(metrics.current_root_edge_visits, 2);
        assert_eq!(metrics.current_root_unique_nodes, 2);
        assert_eq!(
            metrics.current_live_side_payload_shallow_bytes,
            std::mem::size_of::<Constant>() + std::mem::size_of::<BinaryPayload>()
        );
        assert_eq!(
            metrics.current_live_side_payload_shallow_bytes,
            metrics.side_payload_shallow_occupied_bytes
        );
    }

    #[test]
    fn shared_child_is_unchanged_by_independent_parent_rewrite() {
        let mut indexed = IndexedLambda::from_lambda(Lambda::Lconst(Constant::int(5)));
        let shared = indexed.root;
        let p = IndexedLambda::push_payload(&mut indexed.binaries, BinaryPayload(shared, shared));
        let first = indexed.push_node(IndexedNode::Sequence(p));
        let p = IndexedLambda::push_payload(&mut indexed.binaries, BinaryPayload(shared, shared));
        let second = indexed.push_node(IndexedNode::Sequence(p));
        let replacement = indexed.push_node(IndexedNode::Break);
        let p =
            IndexedLambda::push_payload(&mut indexed.binaries, BinaryPayload(replacement, shared));
        let rewritten = indexed.push_node(IndexedNode::Sequence(p));
        assert!(
            matches!(indexed.materialize_node(rewritten), Lambda::Lsequence(a, b) if matches!(*a, Lambda::Lbreak) && matches!(*b, Lambda::Lconst(Constant::Int { i: 5, .. })))
        );
        for parent in [first, second] {
            assert!(
                matches!(indexed.materialize_node(parent), Lambda::Lsequence(a, b) if matches!(*a, Lambda::Lconst(Constant::Int { i: 5, .. })) && matches!(*b, Lambda::Lconst(Constant::Int { i: 5, .. })))
            );
        }
        assert_eq!(indexed.node_count(), 5);
    }
}
