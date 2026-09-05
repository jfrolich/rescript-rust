//! Compilation-owned indexed storage for optimized Lambda.
//!
//! The dense node array contains only tags and `u32` payload indices. Large
//! payloads and ordered child lists live in side tables. The conversion APIs
//! are compatibility boundaries for the staged migration and are not used by
//! the production pipeline yet.

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
use crate::location::Location;

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
struct GlobalPayload(Ident, bool);
#[derive(Clone)]
struct ApplyPayload(NodeId, ItemRange, ApInfo, bool);
#[derive(Clone)]
struct FunctionPayload(i32, ItemRange, NodeId, FunctionAttribute);
#[derive(Clone)]
struct LetPayload(LetKind, Ident, NodeId, NodeId);
#[derive(Clone)]
struct LetRecPayload(ItemRange, NodeId);
#[derive(Clone)]
struct PrimPayload(Primitive, ItemRange, Location);
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
    GlobalModule(&'a Ident, bool),
    Const(&'a Constant),
    Apply(NodeId, &'a [NodeId], &'a ApInfo, bool),
    Function(i32, &'a [Ident], NodeId, &'a FunctionAttribute),
    Let(LetKind, &'a Ident, NodeId, NodeId),
    LetRec(&'a [(Ident, NodeId)], NodeId),
    Prim(&'a Primitive, &'a [NodeId], &'a Location),
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
    GlobalModule(Ident, bool),
    Const(Constant),
    Apply(NodeId, Vec<NodeId>, ApInfo, bool),
    Function(i32, Vec<Ident>, NodeId, FunctionAttribute),
    Let(LetKind, Ident, NodeId, NodeId),
    LetRec(Vec<(Ident, NodeId)>, NodeId),
    Prim(Primitive, Vec<NodeId>, Location),
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

    pub(crate) fn node(&self, id: NodeId) -> IndexedNode {
        self.nodes[id.index()]
    }

    pub(crate) fn view(&self, id: NodeId) -> NodeView<'_> {
        match self.node(id) {
            IndexedNode::Var(i) => NodeView::Var(&self.idents[i as usize]),
            IndexedNode::GlobalModule(i) => {
                let p = &self.globals[i as usize];
                NodeView::GlobalModule(&p.0, p.1)
            }
            IndexedNode::Const(i) => NodeView::Const(&self.constants[i as usize]),
            IndexedNode::Apply(i) => {
                let p = &self.applies[i as usize];
                NodeView::Apply(p.0, &self.children[p.1.bounds()], &p.2, p.3)
            }
            IndexedNode::Function(i) => {
                let p = &self.functions[i as usize];
                NodeView::Function(p.0, &self.idents[p.1.bounds()], p.2, &p.3)
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
            NodeView::Var(id) => Lambda::Lvar(id.clone()),
            NodeView::GlobalModule(id, dynamic) => Lambda::LglobalModule(id.clone(), dynamic),
            NodeView::Const(c) => Lambda::Lconst(c.clone()),
            NodeView::Apply(func, args, info, jsx) => Lambda::Lapply(Apply {
                ap_func: Box::new(self.materialize_node(func)),
                ap_args: args.iter().map(|x| self.materialize_node(*x)).collect(),
                ap_info: info.clone(),
                ap_transformed_jsx: jsx,
            }),
            NodeView::Function(arity, params, body, attr) => Lambda::Lfunction(LFunction {
                arity,
                params: params.to_vec(),
                body: Box::new(self.materialize_node(body)),
                attr: attr.clone(),
            }),
            NodeView::Let(kind, ident, value, body) => Lambda::Llet(
                kind,
                ident.clone(),
                Box::new(self.materialize_node(value)),
                Box::new(self.materialize_node(body)),
            ),
            NodeView::LetRec(bindings, body) => Lambda::Lletrec(
                bindings
                    .iter()
                    .map(|(ident, value)| (ident.clone(), self.materialize_node(*value)))
                    .collect(),
                Box::new(self.materialize_node(body)),
            ),
            NodeView::Prim(primitive, args, loc) => Lambda::Lprim(PrimInfo {
                primitive: primitive.clone(),
                args: args.iter().map(|x| self.materialize_node(*x)).collect(),
                loc: loc.clone(),
            }),
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
                LambdaSwitch {
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
                },
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
                ident.clone(),
                Box::new(self.materialize_node(handler)),
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
                ident.clone(),
                Box::new(self.materialize_node(start)),
                Box::new(self.materialize_node(end)),
                direction,
                Box::new(self.materialize_node(body)),
            ),
            NodeView::ForOf(ident, iterable, body) => Lambda::Lfor_of(
                ident.clone(),
                Box::new(self.materialize_node(iterable)),
                Box::new(self.materialize_node(body)),
            ),
            NodeView::ForAwaitOf(ident, iterable, body) => Lambda::Lfor_await_of(
                ident.clone(),
                Box::new(self.materialize_node(iterable)),
                Box::new(self.materialize_node(body)),
            ),
            NodeView::Assign(ident, value) => {
                Lambda::Lassign(ident.clone(), Box::new(self.materialize_node(value)))
            }
        }
    }

    pub(crate) fn snapshot(&self, id: NodeId) -> NodeSnapshot {
        match self.view(id) {
            NodeView::Var(id) => NodeSnapshot::Var(id.clone()),
            NodeView::GlobalModule(id, dynamic) => NodeSnapshot::GlobalModule(id.clone(), dynamic),
            NodeView::Const(value) => NodeSnapshot::Const(value.clone()),
            NodeView::Apply(function, args, info, jsx) => {
                NodeSnapshot::Apply(function, args.to_vec(), info.clone(), jsx)
            }
            NodeView::Function(arity, params, body, attr) => {
                NodeSnapshot::Function(arity, params.to_vec(), body, attr.clone())
            }
            NodeView::Let(kind, id, value, body) => {
                NodeSnapshot::Let(kind, id.clone(), value, body)
            }
            NodeView::LetRec(bindings, body) => NodeSnapshot::LetRec(bindings.to_vec(), body),
            NodeView::Prim(primitive, args, loc) => {
                NodeSnapshot::Prim(primitive.clone(), args.to_vec(), loc.clone())
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
            NodeView::TryWith(body, id, handler) => {
                NodeSnapshot::TryWith(body, id.clone(), handler)
            }
            NodeView::IfThenElse(a, b, c) => NodeSnapshot::IfThenElse(a, b, c),
            NodeView::Sequence(a, b) => NodeSnapshot::Sequence(a, b),
            NodeView::Break => NodeSnapshot::Break,
            NodeView::Continue => NodeSnapshot::Continue,
            NodeView::While(a, b) => NodeSnapshot::While(a, b),
            NodeView::For(id, start, end, direction, body) => {
                NodeSnapshot::For(id.clone(), start, end, direction, body)
            }
            NodeView::ForOf(id, iterable, body) => NodeSnapshot::ForOf(id.clone(), iterable, body),
            NodeView::ForAwaitOf(id, iterable, body) => {
                NodeSnapshot::ForAwaitOf(id.clone(), iterable, body)
            }
            NodeView::Assign(id, value) => NodeSnapshot::Assign(id.clone(), value),
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
            NodeSnapshot::GlobalModule(id, dynamic) => {
                payload_node!(globals, GlobalPayload(id, dynamic), GlobalModule)
            }
            NodeSnapshot::Const(value) => payload_node!(constants, value, Const),
            NodeSnapshot::Apply(function, args, info, jsx) => {
                let args = self.push_children(args);
                payload_node!(applies, ApplyPayload(function, args, info, jsx), Apply)
            }
            NodeSnapshot::Function(arity, params, body, attr) => {
                let params = self.push_idents(params);
                payload_node!(
                    functions,
                    FunctionPayload(arity, params, body, attr),
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
            Lambda::LglobalModule(id, dynamic) => {
                payload_node!(globals, GlobalPayload(id, dynamic), GlobalModule)
            }
            Lambda::Lconst(c) => payload_node!(constants, c, Const),
            Lambda::Lapply(apply) => {
                let func = self.lower(*apply.ap_func);
                let args = self.lower_many(apply.ap_args);
                payload_node!(
                    applies,
                    ApplyPayload(func, args, apply.ap_info, apply.ap_transformed_jsx),
                    Apply
                )
            }
            Lambda::Lfunction(func) => {
                let body = self.lower(*func.body);
                let params = self.push_idents(func.params);
                payload_node!(
                    functions,
                    FunctionPayload(func.arity, params, body, func.attr),
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
    /// Unique nodes reachable from metadata roots, before unioning with the
    /// current root.
    pub metadata_unique_nodes: usize,
    /// Unique union of current-root and metadata-root reachability.
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
}

/// Owns the canonical indexed root, its append-only store, and every metadata
/// table containing IDs into that store. Public pass entrypoints operate on
/// the current root only, so callers cannot accidentally pair a raw `NodeId`
/// from another compilation with this store. Private recursive helpers follow
/// the same-store contract used by the compiler's other index arenas.
pub struct IndexedLambdaContext {
    store: IndexedLambda,
    metadata: IndexedLamStats,
}

impl IndexedLambdaContext {
    /// Creates one compilation-owned store and metadata context.
    pub fn from_lambda(lambda: Lambda, exports: impl IntoIterator<Item = Ident>) -> Self {
        Self {
            store: IndexedLambda::from_lambda(lambda),
            metadata: IndexedLamStats::new(exports),
        }
    }

    #[cfg(test)]
    pub(crate) fn from_store(
        store: IndexedLambda,
        exports: impl IntoIterator<Item = Ident>,
    ) -> Self {
        Self {
            store,
            metadata: IndexedLamStats::new(exports),
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

    /// Materializes the canonical root at the inactive compatibility boundary.
    pub fn materialize(&self) -> Lambda {
        self.store.materialize()
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
                NodeView::Apply(function, args, _, _) => {
                    child(function);
                    for node in args {
                        child(*node);
                    }
                }
                NodeView::Function(_, _, body, _) => child(body),
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
                | NodeView::TryWith(body, _, handler) => {
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
                | NodeView::GlobalModule(_, _)
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
        walk(
            &self.store,
            self.store.root(),
            &mut current,
            &mut current_edges,
            true,
        );
        let mut metadata = AHashSet::new();
        let mut ignored_edges = 0;
        for root in self.metadata.retained_roots() {
            assert!(
                self.store.contains(root),
                "indexed Lambda metadata root is out of range"
            );
            walk(&self.store, root, &mut metadata, &mut ignored_edges, false);
        }
        let mut live = current.clone();
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
        IndexedStorageMeasurements {
            node_allocations: self.store.nodes.len(),
            current_root_edge_visits: current_edges,
            current_root_unique_nodes: current.len(),
            metadata_unique_nodes: metadata.len(),
            live_unique_nodes: live.len(),
            superseded_nodes: self.store.nodes.len() - live.len(),
            hot_node_occupied_bytes: self.store.nodes.len() * std::mem::size_of::<IndexedNode>(),
            hot_node_capacity_bytes: self.store.nodes.capacity()
                * std::mem::size_of::<IndexedNode>(),
            side_payload_shallow_occupied_bytes: side_occupied,
            side_payload_shallow_capacity_bytes: side_capacity,
            nested_heap_bytes_included: false,
        }
    }

    pub(crate) fn store(&self) -> &IndexedLambda {
        &self.store
    }

    pub(crate) fn store_mut(&mut self) -> &mut IndexedLambda {
        &mut self.store
    }

    pub(crate) fn current_root(&self) -> NodeId {
        self.store.root()
    }

    pub(crate) fn replace_root(&mut self, root: NodeId) {
        self.store.set_root(root);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ident::IdentFlags;
    use crate::lambda::{ApplyStatus, InlineAttribute};

    fn id(name: &str, stamp: i32) -> Ident {
        Ident::new(name, stamp, IdentFlags::NONE)
    }
    fn assert_round_trip(lambda: Lambda) {
        let expected = format!("{lambda:#?}");
        let indexed = IndexedLambda::from_lambda(lambda);
        assert_eq!(expected, format!("{:#?}", indexed.materialize()));
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
        let loc = Location::none();
        let var = || Lambda::Lvar(x.clone());
        let int = || Lambda::Lconst(Constant::int(1));
        for leaf in [
            var(),
            Lambda::LglobalModule(y.clone(), true),
            int(),
            Lambda::Lbreak,
            Lambda::Lcontinue,
        ] {
            assert_round_trip(leaf);
        }
        let info = ApInfo {
            loc: loc.clone(),
            inlined: InlineAttribute::Always,
            status: ApplyStatus::InferFull,
        };
        let samples = vec![
            Lambda::Lapply(Apply {
                ap_func: Box::new(var()),
                ap_args: vec![int(), Lambda::Lvar(y.clone())],
                ap_info: info,
                ap_transformed_jsx: true,
            }),
            Lambda::Lfunction(LFunction {
                arity: 2,
                params: vec![x.clone(), y.clone()],
                body: Box::new(var()),
                attr: FunctionAttribute {
                    async_: true,
                    ..FunctionAttribute::default()
                },
            }),
            Lambda::Llet(LetKind::Strict, x.clone(), Box::new(int()), Box::new(var())),
            Lambda::Lletrec(
                vec![(x.clone(), int()), (y.clone(), var())],
                Box::new(var()),
            ),
            Lambda::Lprim(PrimInfo {
                primitive: Primitive::Pnot,
                args: vec![int(), var()],
                loc: loc.clone(),
            }),
            Lambda::Lswitch(
                Box::new(var()),
                LambdaSwitch {
                    sw_consts_full: false,
                    sw_consts: vec![(SwitchKey::Int(2), int()), (SwitchKey::Int(1), var())],
                    sw_blocks_full: true,
                    sw_blocks: vec![(SwitchKey::Int(4), int()), (SwitchKey::Int(3), var())],
                    sw_failaction: Some(Box::new(int())),
                    sw_dispatch: SwitchDispatch::Direct,
                },
            ),
            Lambda::LstringSwitch(
                Box::new(var()),
                vec![("b".into(), int()), ("a".into(), var())],
                Some(Box::new(int())),
            ),
            Lambda::LstaticRaise(3, vec![int(), var()]),
            Lambda::LstaticCatch(
                Box::new(var()),
                (3, vec![x.clone(), y.clone()]),
                Box::new(int()),
            ),
            Lambda::LtryWith(Box::new(var()), y.clone(), Box::new(int())),
            Lambda::LifThenElse(
                Box::new(var()),
                Box::new(int()),
                Box::new(Lambda::Lvar(y.clone())),
            ),
            Lambda::Lsequence(Box::new(var()), Box::new(int())),
            Lambda::Lwhile(Box::new(var()), Box::new(int())),
            Lambda::Lfor(
                x.clone(),
                Box::new(int()),
                Box::new(Lambda::Lconst(Constant::int(9))),
                DirectionFlag::Downto,
                Box::new(var()),
            ),
            Lambda::Lfor_of(x.clone(), Box::new(var()), Box::new(int())),
            Lambda::Lfor_await_of(x.clone(), Box::new(var()), Box::new(int())),
            Lambda::Lassign(x, Box::new(int())),
        ];
        for sample in samples {
            assert_round_trip(sample);
        }
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
