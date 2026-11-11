//! Arena storage for the optimized Lambda IR.
//!
//! One [`LamArena`] holds every Lambda node of a compilation unit. Nodes are
//! 16-byte `Copy` values in one dense `Vec`; they refer to each other through
//! `u32` handles ([`Lam`]). Everything that does not fit in 16 bytes lives in
//! per-kind side tables:
//!
//! - identifiers in `idents` ([`IdentId`]; parameter and `let rec` binder
//!   lists are contiguous runs in the same table),
//! - constants, primitives (+ location), application info, function headers,
//!   switch metadata and static-catch headers in their own tables,
//! - child lists in one length-prefixed pool ([`LamList`]),
//! - string-switch keys in one text buffer.
//!
//! Nodes and payloads are immutable once pushed. OCaml Lambda is an
//! immutable tree whose passes rebuild changed spines and share everything
//! else; the arena gives the same semantics directly. A pass that rewrites a
//! node appends a new 16-byte node that reuses the old payload handles, so
//! rebuilding never clones a `Primitive`, `Constant` or child list it did not
//! change. Unchanged subtrees keep their handle, and a handle may be referenced
//! from several parents or from pass metadata (the counterpart of OCaml
//! physical sharing and of the tree port's `clone()`), because nothing is
//! mutated in place. The whole arena is freed at once with its compilation.

use crate::ident::Ident;
use crate::lambda::LamLoc;
use crate::lambda::lam_compat::{self, Comparison, LetKind};
use crate::lambda::lam_constant::{self, Constant};
use crate::lambda::lam_primitive::Primitive;
use crate::lambda::lam_tag_info::TagInfo;
use crate::lambda::{
    ApInfo, Apply, DirectionFlag, FunctionAttribute, LFunction, Lambda, LambdaSwitch, PrimInfo,
    SwitchDispatch, SwitchKey,
};

macro_rules! handle {
    ($(#[$m:meta])* $name:ident) => {
        $(#[$m])*
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
        #[repr(transparent)]
        pub struct $name(u32);

        impl $name {
            /// Position of this handle in its arena table.
            #[inline]
            pub fn index(self) -> usize {
                self.0 as usize
            }
        }
    };
}

handle!(
    /// A Lambda node. Interpret only through the arena that created it.
    Lam
);
handle!(
    /// A length-prefixed list of nodes in the arena's list pool.
    LamList
);
handle!(
    /// An identifier in the arena's identifier table.
    IdentId
);
handle!(
    /// A constant in the arena's constant table.
    ConstId
);
handle!(
    /// A primitive payload in the arena's primitive table.
    PrimId
);
handle!(
    /// An application payload in the arena's application table.
    ApplyId
);
handle!(
    /// A function header in the arena's function table.
    FuncId
);
handle!(
    /// A switch payload in the arena's switch table.
    SwitchId
);
handle!(
    /// A string-switch payload in the arena's string-switch table.
    StrSwitchId
);
handle!(
    /// A static-catch header in the arena's catch table.
    CatchId
);

#[inline]
fn checked_u32(n: usize) -> u32 {
    u32::try_from(n).expect("Lambda arena exceeds u32 capacity")
}

/// A contiguous run of identifiers in the identifier table.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct IdentSpan {
    start: u32,
    len: u32,
}

impl IdentSpan {
    /// Number of identifiers in the run.
    pub fn len(self) -> usize {
        self.len as usize
    }
    /// Whether the run holds no identifiers.
    pub fn is_empty(self) -> bool {
        self.len == 0
    }
}

/// Hot node. Fields are handles into the arena tables; see the module docs.
#[derive(Debug, Clone, Copy)]
pub enum Node {
    /// `Lvar`: a variable reference.
    Var(IdentId),
    /// `LglobalModule`: a reference to a global module.
    GlobalModule(IdentId),
    /// `Lconst`: a constant.
    Const(ConstId),
    /// `Lapply`: a function application.
    Apply {
        /// The applied function.
        func: Lam,
        /// The arguments.
        args: LamList,
        /// Location, inline and uncurry information.
        info: ApplyId,
    },
    /// `Lfunction`: a function definition.
    Function {
        /// The function body.
        body: Lam,
        /// Arity, parameters, attributes and location.
        info: FuncId,
    },
    /// `Llet`: a non-recursive binding.
    Let {
        /// How the binding may be inlined or eliminated.
        kind: LetKind,
        /// The bound identifier.
        id: IdentId,
        /// The bound value.
        value: Lam,
        /// The scope of the binding.
        body: Lam,
    },
    /// `ids` starts a run of `values.len()` identifiers.
    LetRec {
        /// The first of the binders.
        ids: IdentId,
        /// The bound values, one per binder.
        values: LamList,
        /// The scope of the bindings.
        body: Lam,
    },
    /// `Lprim`: a primitive operation.
    Prim {
        /// The operands.
        args: LamList,
        /// The primitive and its location.
        info: PrimId,
    },
    /// `actions` holds the const actions, then the block actions, then the
    /// fail action if the payload has one.
    Switch {
        /// The value switched on.
        scrut: Lam,
        /// Case actions, laid out as described above.
        actions: LamList,
        /// Case keys, fullness flags and dispatch.
        info: SwitchId,
    },
    /// `actions` holds one action per key, then the default if any.
    StringSwitch {
        /// The string switched on.
        scrut: Lam,
        /// Case actions, laid out as described above.
        actions: LamList,
        /// Case keys and default presence.
        info: StrSwitchId,
    },
    /// `LstaticRaise`: a jump to the handler of an enclosing static catch.
    StaticRaise {
        /// The handler's label.
        label: i32,
        /// Values for the handler's parameters.
        args: LamList,
    },
    /// `LstaticCatch`: a body whose static raises jump to `handler`.
    StaticCatch {
        /// The protected body.
        body: Lam,
        /// The code run on a static raise to this label.
        handler: Lam,
        /// The label and the handler's parameters.
        info: CatchId,
    },
    /// `LtryWith`: exception handling.
    TryWith {
        /// The protected body.
        body: Lam,
        /// The identifier bound to the raised exception.
        id: IdentId,
        /// The code run when the body raises.
        handler: Lam,
    },
    /// `LifThenElse`.
    If {
        /// The condition.
        cond: Lam,
        /// The branch taken when the condition holds.
        then_: Lam,
        /// The branch taken otherwise.
        else_: Lam,
    },
    /// `Lsequence`: evaluate the first, then the second.
    Sequence(Lam, Lam),
    /// `Lbreak`: leave the enclosing loop.
    Break,
    /// `Lcontinue`: start the enclosing loop's next iteration.
    Continue,
    /// `Lwhile`: condition and body.
    While(Lam, Lam),
    /// `kids` is `[start; finish; body]`.
    For {
        /// Whether the loop counts up or down.
        dir: DirectionFlag,
        /// The loop variable.
        id: IdentId,
        /// Bounds and body, as described above.
        kids: LamList,
    },
    /// `LforOf`: a `for...of` loop.
    ForOf {
        /// The loop variable.
        id: IdentId,
        /// The iterated value.
        iter: Lam,
        /// The loop body.
        body: Lam,
    },
    /// `LforAwaitOf`: a `for await...of` loop.
    ForAwaitOf {
        /// The loop variable.
        id: IdentId,
        /// The async iterated value.
        iter: Lam,
        /// The loop body.
        body: Lam,
    },
    /// `Lassign`: assignment to a mutable variable.
    Assign {
        /// The assigned variable.
        id: IdentId,
        /// The new value.
        value: Lam,
    },
}

/// Side-table payload of a [`Node::Prim`].
#[derive(Debug, Clone)]
pub struct PrimPayload {
    /// The operation.
    pub primitive: Primitive,
    /// Where the operation comes from in the source.
    pub loc: LamLoc,
}

/// Side-table payload of a [`Node::Apply`].
#[derive(Debug, Clone)]
pub struct ApplyPayload {
    /// Location, inline and uncurry information.
    pub info: ApInfo,
    /// Whether the application is a JSX call produced by the JSX transform.
    pub transformed_jsx: bool,
}

/// Side-table payload of a [`Node::Function`].
#[derive(Debug, Clone)]
pub struct FuncPayload {
    /// The function's arity.
    pub arity: i32,
    /// The parameters, in the identifier table.
    pub params: IdentSpan,
    /// Inline, async and other function attributes.
    pub attr: FunctionAttribute,
    /// Where the function is defined.
    pub loc: LamLoc,
}

/// Side-table payload of a [`Node::Switch`]: keys and flags; the actions live in the node.
#[derive(Debug, Clone)]
pub struct SwitchPayload {
    /// Whether the constant cases cover every constant constructor.
    pub consts_full: bool,
    /// Whether the block cases cover every block constructor.
    pub blocks_full: bool,
    /// Whether the node's action list ends with a fail action.
    pub has_fail: bool,
    const_keys: (u32, u32),
    block_keys: (u32, u32),
    /// How the runtime tells the cases apart.
    pub dispatch: SwitchDispatch,
}

impl SwitchPayload {
    /// Number of constant cases.
    pub fn n_consts(&self) -> usize {
        self.const_keys.1 as usize
    }
    /// Number of block cases.
    pub fn n_blocks(&self) -> usize {
        self.block_keys.1 as usize
    }
}

/// Side-table payload of a [`Node::StringSwitch`]: the case keys; the actions live in the node.
#[derive(Debug, Clone, Copy)]
pub struct StrSwitchPayload {
    keys: (u32, u32),
    /// Whether the node's action list ends with a default action.
    pub has_default: bool,
}

impl StrSwitchPayload {
    /// Number of cases, not counting the default.
    pub fn n_cases(&self) -> usize {
        self.keys.1 as usize
    }
}

/// Side-table payload of a [`Node::StaticCatch`].
#[derive(Debug, Clone, Copy)]
pub struct CatchPayload {
    /// The label static raises jump to.
    pub label: i32,
    /// The handler's parameters, in the identifier table.
    pub params: IdentSpan,
}

/// Decoded view of a switch node's actions.
#[derive(Debug, Clone, Copy)]
pub struct SwitchActions<'a> {
    /// Actions of the constant cases, in key order.
    pub consts: &'a [Lam],
    /// Actions of the block cases, in key order.
    pub blocks: &'a [Lam],
    /// The action taken when no case matches.
    pub fail: Option<Lam>,
}

/// Owned description of a new switch, used when keys are not reused.
#[derive(Debug, Clone)]
pub struct SwitchSpec {
    /// Whether the constant cases cover every constant constructor.
    pub consts_full: bool,
    /// Constant case keys and their actions.
    pub consts: Vec<(SwitchKey, Lam)>,
    /// Whether the block cases cover every block constructor.
    pub blocks_full: bool,
    /// Block case keys and their actions.
    pub blocks: Vec<(SwitchKey, Lam)>,
    /// The action taken when no case matches.
    pub fail: Option<Lam>,
    /// How the runtime tells the cases apart.
    pub dispatch: SwitchDispatch,
}

/// A node with its payloads, shaped like the recursive [`Lambda`], for
/// read-only matching. Variants without borrowed fields can be held while
/// the arena is mutated.
#[derive(Clone, Copy)]
pub enum View<'a> {
    /// See [`Node::Var`].
    Var(Ident),
    /// See [`Node::GlobalModule`].
    GlobalModule(Ident),
    /// See [`Node::Const`].
    Const(&'a Constant),
    /// See [`Node::Apply`].
    Apply {
        /// The applied function.
        func: Lam,
        /// The arguments.
        args: &'a [Lam],
        /// Location, inline and uncurry information.
        info: &'a ApInfo,
        /// Whether the application is a JSX call produced by the JSX transform.
        transformed_jsx: bool,
    },
    /// See [`Node::Function`].
    Function {
        /// The parameters.
        params: &'a [Ident],
        /// The function body.
        body: Lam,
        /// Arity, attributes and location.
        func: &'a FuncPayload,
    },
    /// See [`Node::Let`]: kind, binder, value, body.
    Let(LetKind, Ident, Lam, Lam),
    /// See [`Node::LetRec`]: binders, values, body.
    LetRec(&'a [Ident], &'a [Lam], Lam),
    /// See [`Node::Prim`]: primitive, operands, location.
    Prim(&'a Primitive, &'a [Lam], LamLoc),
    /// See [`Node::Switch`]: scrutinee and cases.
    Switch(Lam, SwitchView<'a>),
    /// See [`Node::StringSwitch`]: scrutinee and cases.
    StringSwitch(Lam, StrSwitchView<'a>),
    /// See [`Node::StaticRaise`]: label and arguments.
    StaticRaise(i32, &'a [Lam]),
    /// See [`Node::StaticCatch`]: body, label, handler parameters, handler.
    StaticCatch(Lam, i32, &'a [Ident], Lam),
    /// See [`Node::TryWith`]: body, exception binder, handler.
    TryWith(Lam, Ident, Lam),
    /// See [`Node::If`]: condition, then branch, else branch.
    If(Lam, Lam, Lam),
    /// See [`Node::Sequence`].
    Sequence(Lam, Lam),
    /// See [`Node::Break`].
    Break,
    /// See [`Node::Continue`].
    Continue,
    /// See [`Node::While`]: condition and body.
    While(Lam, Lam),
    /// See [`Node::For`]: variable, start, finish, direction, body.
    For(Ident, Lam, Lam, DirectionFlag, Lam),
    /// See [`Node::ForOf`]: variable, iterable, body.
    ForOf(Ident, Lam, Lam),
    /// See [`Node::ForAwaitOf`]: variable, iterable, body.
    ForAwaitOf(Ident, Lam, Lam),
    /// See [`Node::Assign`]: variable and value.
    Assign(Ident, Lam),
}

/// The keys and actions of a switch node.
#[derive(Clone, Copy)]
pub struct SwitchView<'a> {
    /// Flags and dispatch of the switch.
    pub payload: &'a SwitchPayload,
    /// Keys of the constant cases.
    pub const_keys: &'a [SwitchKey],
    /// Keys of the block cases.
    pub block_keys: &'a [SwitchKey],
    /// The case actions.
    pub actions: SwitchActions<'a>,
}

impl<'a> SwitchView<'a> {
    /// The constant cases as (key, action) pairs.
    pub fn consts(&self) -> impl Iterator<Item = (&'a SwitchKey, Lam)> + 'a {
        self.const_keys
            .iter()
            .zip(self.actions.consts.iter().copied())
    }
    /// The block cases as (key, action) pairs.
    pub fn blocks(&self) -> impl Iterator<Item = (&'a SwitchKey, Lam)> + 'a {
        self.block_keys
            .iter()
            .zip(self.actions.blocks.iter().copied())
    }
}

/// The cases and default of a string switch node.
#[derive(Clone, Copy)]
pub struct StrSwitchView<'a> {
    arena: &'a LamArena,
    info: StrSwitchId,
    /// One action per case, in key order.
    pub actions: &'a [Lam],
    /// The action taken when no key matches.
    pub default: Option<Lam>,
}

impl<'a> StrSwitchView<'a> {
    /// Number of cases, not counting the default.
    pub fn len(&self) -> usize {
        self.actions.len()
    }
    /// Whether the switch has no cases.
    pub fn is_empty(&self) -> bool {
        self.actions.is_empty()
    }
    /// The key of case `i`.
    pub fn key(&self, i: usize) -> &'a str {
        self.arena.str_switch_key(self.info, i)
    }
    /// The cases as (key, action) pairs.
    pub fn cases(&self) -> impl Iterator<Item = (&'a str, Lam)> + 'a {
        let (arena, info) = (self.arena, self.info);
        self.actions
            .iter()
            .enumerate()
            .map(move |(i, lam)| (arena.str_switch_key(info, i), *lam))
    }
}

/// Owner of every Lambda node of a compilation unit and of their side tables; see the module docs.
#[derive(Clone)]
pub struct LamArena {
    nodes: Vec<Node>,
    /// Length-prefixed lists: `pool[h]` holds the length as a `Lam`, the
    /// elements follow. `LamList(0)` is the shared empty list.
    pool: Vec<Lam>,
    idents: Vec<Ident>,
    consts: Vec<Constant>,
    prims: Vec<PrimPayload>,
    applies: Vec<ApplyPayload>,
    funcs: Vec<FuncPayload>,
    switches: Vec<SwitchPayload>,
    switch_keys: Vec<SwitchKey>,
    str_switches: Vec<StrSwitchPayload>,
    str_keys: Vec<(u32, u32)>,
    text: String,
    catches: Vec<CatchPayload>,
}

/// A program: an arena and the root of its term.
#[derive(Clone)]
pub struct LamProgram {
    /// The arena holding the program's nodes.
    pub arena: LamArena,
    /// The program's term.
    pub root: Lam,
}

impl LamProgram {
    /// The program as a recursive Lambda, for dumps and tests.
    pub fn to_tree(&self) -> Lambda {
        self.arena.export(self.root)
    }
}

impl Default for LamArena {
    fn default() -> Self {
        Self::new()
    }
}

const _: () = assert!(std::mem::size_of::<Node>() == 16);

impl LamArena {
    /// The shared empty list.
    pub const EMPTY: LamList = LamList(0);

    /// An empty arena.
    pub fn new() -> Self {
        Self::with_capacity(0)
    }

    /// Pre-sizes the node and list tables for about `nodes` nodes.
    pub fn with_capacity(nodes: usize) -> Self {
        let mut pool = Vec::with_capacity(nodes / 2 + 1);
        pool.push(Lam(0));
        Self {
            nodes: Vec::with_capacity(nodes),
            pool,
            idents: Vec::with_capacity(nodes / 2),
            consts: Vec::with_capacity(nodes / 8),
            prims: Vec::with_capacity(nodes / 4),
            applies: Vec::with_capacity(nodes / 8),
            funcs: Vec::with_capacity(nodes / 16),
            switches: Vec::new(),
            switch_keys: Vec::new(),
            str_switches: Vec::new(),
            str_keys: Vec::new(),
            text: String::new(),
            catches: Vec::new(),
        }
    }

    /// Number of nodes pushed so far, reachable or not.
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    /// A stamp at least as large as every identifier in this arena. Includes
    /// identifiers from eliminated nodes: fresh-name generation needs an
    /// upper bound, not a walk of the reachable term.
    pub(crate) fn ident_stamp_bound(&self) -> i32 {
        self.idents.iter().map(Ident::stamp).max().unwrap_or(0).max(0)
    }

    // ---------------------------------------------------------------- reads

    /// The node behind `lam`.
    #[inline]
    pub fn node(&self, lam: Lam) -> Node {
        self.nodes[lam.index()]
    }

    /// The identifier behind `id`.
    #[inline]
    pub fn ident(&self, id: IdentId) -> Ident {
        self.idents[id.index()]
    }

    /// The identifiers of `span`.
    #[inline]
    pub fn idents(&self, span: IdentSpan) -> &[Ident] {
        &self.idents[span.start as usize..(span.start + span.len) as usize]
    }

    /// The `len` identifiers starting at `start` (a `LetRec` binder run).
    #[inline]
    pub fn ident_run(&self, start: IdentId, len: usize) -> &[Ident] {
        &self.idents[start.index()..start.index() + len]
    }

    /// The elements of `list`.
    #[inline]
    pub fn list(&self, list: LamList) -> &[Lam] {
        let h = list.index();
        let len = self.pool[h].0 as usize;
        &self.pool[h + 1..h + 1 + len]
    }

    /// Number of elements of `list`.
    #[inline]
    pub fn list_len(&self, list: LamList) -> usize {
        self.pool[list.index()].0 as usize
    }

    /// The constant behind `id`.
    #[inline]
    pub fn constant(&self, id: ConstId) -> &Constant {
        &self.consts[id.index()]
    }

    /// The primitive payload behind `id`.
    #[inline]
    pub fn prim_payload(&self, id: PrimId) -> &PrimPayload {
        &self.prims[id.index()]
    }

    /// The application payload behind `id`.
    #[inline]
    pub fn apply_payload(&self, id: ApplyId) -> &ApplyPayload {
        &self.applies[id.index()]
    }

    /// The function header behind `id`.
    #[inline]
    pub fn func_payload(&self, id: FuncId) -> &FuncPayload {
        &self.funcs[id.index()]
    }

    /// The parameters of the function header `id`.
    #[inline]
    pub fn params(&self, id: FuncId) -> &[Ident] {
        self.idents(self.funcs[id.index()].params)
    }

    /// The switch payload behind `id`.
    #[inline]
    pub fn switch_payload(&self, id: SwitchId) -> &SwitchPayload {
        &self.switches[id.index()]
    }

    /// Keys of the constant cases of switch `id`.
    pub fn switch_const_keys(&self, id: SwitchId) -> &[SwitchKey] {
        let (s, l) = self.switches[id.index()].const_keys;
        &self.switch_keys[s as usize..(s + l) as usize]
    }

    /// Keys of the block cases of switch `id`.
    pub fn switch_block_keys(&self, id: SwitchId) -> &[SwitchKey] {
        let (s, l) = self.switches[id.index()].block_keys;
        &self.switch_keys[s as usize..(s + l) as usize]
    }

    /// Splits a switch node's `actions` into constant, block and fail actions.
    pub fn switch_actions(&self, info: SwitchId, actions: LamList) -> SwitchActions<'_> {
        let p = &self.switches[info.index()];
        let all = self.list(actions);
        let nc = p.n_consts();
        let nb = p.n_blocks();
        SwitchActions {
            consts: &all[..nc],
            blocks: &all[nc..nc + nb],
            fail: p.has_fail.then(|| all[nc + nb]),
        }
    }

    /// The string-switch payload behind `id`.
    #[inline]
    pub fn str_switch_payload(&self, id: StrSwitchId) -> StrSwitchPayload {
        self.str_switches[id.index()]
    }

    /// The key of case `i` of string switch `id`.
    pub fn str_switch_key(&self, id: StrSwitchId, i: usize) -> &str {
        let (s, l) = self.str_switches[id.index()].keys;
        assert!(i < l as usize);
        let (ts, tl) = self.str_keys[s as usize + i];
        &self.text[ts as usize..(ts + tl) as usize]
    }

    /// The cases (key, action) and default of a string switch.
    pub fn str_switch_cases(
        &self,
        info: StrSwitchId,
        actions: LamList,
    ) -> (impl Iterator<Item = (&str, Lam)> + '_, Option<Lam>) {
        let p = self.str_switches[info.index()];
        let all = self.list(actions);
        let n = p.n_cases();
        let default = p.has_default.then(|| all[n]);
        (
            (0..n).map(move |i| (self.str_switch_key(info, i), all[i])),
            default,
        )
    }

    /// The static-catch header behind `id`.
    #[inline]
    pub fn catch_payload(&self, id: CatchId) -> CatchPayload {
        self.catches[id.index()]
    }

    // --------------------------------------------------------------- views

    /// The node with its payloads, shaped like the recursive [`Lambda`].
    pub fn view(&self, lam: Lam) -> View<'_> {
        match self.node(lam) {
            Node::Var(id) => View::Var(self.ident(id)),
            Node::GlobalModule(id) => View::GlobalModule(self.ident(id)),
            Node::Const(c) => View::Const(self.constant(c)),
            Node::Apply { func, args, info } => {
                let p = &self.applies[info.index()];
                View::Apply {
                    func,
                    args: self.list(args),
                    info: &p.info,
                    transformed_jsx: p.transformed_jsx,
                }
            }
            Node::Function { body, info } => View::Function {
                params: self.params(info),
                body,
                func: &self.funcs[info.index()],
            },
            Node::Let {
                kind,
                id,
                value,
                body,
            } => View::Let(kind, self.ident(id), value, body),
            Node::LetRec { ids, values, body } => {
                let values = self.list(values);
                View::LetRec(self.ident_run(ids, values.len()), values, body)
            }
            Node::Prim { args, info } => {
                let p = &self.prims[info.index()];
                View::Prim(&p.primitive, self.list(args), p.loc)
            }
            Node::Switch {
                scrut,
                actions,
                info,
            } => View::Switch(
                scrut,
                SwitchView {
                    payload: &self.switches[info.index()],
                    const_keys: self.switch_const_keys(info),
                    block_keys: self.switch_block_keys(info),
                    actions: self.switch_actions(info, actions),
                },
            ),
            Node::StringSwitch {
                scrut,
                actions,
                info,
            } => {
                let all = self.list(actions);
                let p = self.str_switch_payload(info);
                let n = p.n_cases();
                View::StringSwitch(
                    scrut,
                    StrSwitchView {
                        arena: self,
                        info,
                        actions: &all[..n],
                        default: p.has_default.then(|| all[n]),
                    },
                )
            }
            Node::StaticRaise { label, args } => View::StaticRaise(label, self.list(args)),
            Node::StaticCatch {
                body,
                handler,
                info,
            } => {
                let p = self.catch_payload(info);
                View::StaticCatch(body, p.label, self.idents(p.params), handler)
            }
            Node::TryWith { body, id, handler } => View::TryWith(body, self.ident(id), handler),
            Node::If { cond, then_, else_ } => View::If(cond, then_, else_),
            Node::Sequence(a, b) => View::Sequence(a, b),
            Node::Break => View::Break,
            Node::Continue => View::Continue,
            Node::While(a, b) => View::While(a, b),
            Node::For { dir, id, kids } => {
                let (start, finish, body) = self.for_parts(kids);
                View::For(self.ident(id), start, finish, dir, body)
            }
            Node::ForOf { id, iter, body } => View::ForOf(self.ident(id), iter, body),
            Node::ForAwaitOf { id, iter, body } => View::ForAwaitOf(self.ident(id), iter, body),
            Node::Assign { id, value } => View::Assign(self.ident(id), value),
        }
    }

    /// The elements of `list`, copied out so the arena can be borrowed
    /// mutably while they are visited.
    #[inline]
    pub fn list_small(&self, list: LamList) -> smallvec::SmallVec<[Lam; 8]> {
        smallvec::SmallVec::from_slice(self.list(list))
    }

    // ------------------------------------------------------- shape helpers

    /// The identifier of a variable node.
    #[inline]
    pub fn as_var(&self, lam: Lam) -> Option<Ident> {
        match self.node(lam) {
            Node::Var(id) => Some(self.ident(id)),
            _ => None,
        }
    }

    /// The constant of a constant node.
    #[inline]
    pub fn as_const(&self, lam: Lam) -> Option<&Constant> {
        match self.node(lam) {
            Node::Const(c) => Some(self.constant(c)),
            _ => None,
        }
    }

    /// Whether `lam` is a constant node.
    #[inline]
    pub fn is_const(&self, lam: Lam) -> bool {
        matches!(self.node(lam), Node::Const(_))
    }

    /// `(primitive, args, loc)` of a primitive node.
    #[inline]
    pub fn as_prim(&self, lam: Lam) -> Option<(&Primitive, &[Lam], LamLoc)> {
        match self.node(lam) {
            Node::Prim { args, info } => {
                let p = &self.prims[info.index()];
                Some((&p.primitive, self.list(args), p.loc))
            }
            _ => None,
        }
    }

    /// Whether `lam` is the unit constant.
    pub fn is_unit(&self, lam: Lam) -> bool {
        matches!(
            self.as_const(lam),
            Some(Constant::JsUndefined { is_unit: true })
        )
    }

    // ------------------------------------------------------ payload pushes

    /// Appends `node` and returns its handle.
    #[inline]
    pub fn push(&mut self, node: Node) -> Lam {
        let id = Lam(checked_u32(self.nodes.len()));
        self.nodes.push(node);
        id
    }

    /// Appends one identifier to the identifier table.
    #[inline]
    pub fn add_ident(&mut self, id: Ident) -> IdentId {
        let i = IdentId(checked_u32(self.idents.len()));
        self.idents.push(id);
        i
    }

    /// Appends `ids` as one contiguous run.
    pub fn add_idents(&mut self, ids: &[Ident]) -> IdentSpan {
        let start = checked_u32(self.idents.len());
        self.idents.extend_from_slice(ids);
        IdentSpan {
            start,
            len: checked_u32(ids.len()),
        }
    }

    /// Appends `ids` as one contiguous run.
    pub fn add_idents_iter(&mut self, ids: impl IntoIterator<Item = Ident>) -> IdentSpan {
        let start = self.idents.len();
        self.idents.extend(ids);
        IdentSpan {
            start: checked_u32(start),
            len: checked_u32(self.idents.len() - start),
        }
    }

    /// Appends `items` as one list; an empty slice gives [`Self::EMPTY`].
    pub fn add_list(&mut self, items: &[Lam]) -> LamList {
        if items.is_empty() {
            return Self::EMPTY;
        }
        let h = LamList(checked_u32(self.pool.len()));
        self.pool.push(Lam(checked_u32(items.len())));
        self.pool.extend_from_slice(items);
        h
    }

    /// Appends `items` as one list; an empty iterator gives [`Self::EMPTY`].
    pub fn add_list_iter(&mut self, items: impl IntoIterator<Item = Lam>) -> LamList {
        let h = self.pool.len();
        self.pool.push(Lam(0));
        self.pool.extend(items);
        let len = self.pool.len() - h - 1;
        if len == 0 {
            self.pool.pop();
            return Self::EMPTY;
        }
        self.pool[h] = Lam(checked_u32(len));
        LamList(checked_u32(h))
    }

    /// A copy of `list` (so it can be traversed while the arena grows).
    #[inline]
    pub fn list_vec(&self, list: LamList) -> smallvec::SmallVec<[Lam; 8]> {
        smallvec::SmallVec::from_slice(self.list(list))
    }

    /// Appends a constant payload.
    pub fn add_const(&mut self, c: Constant) -> ConstId {
        let i = ConstId(checked_u32(self.consts.len()));
        self.consts.push(c);
        i
    }

    /// Appends a primitive payload.
    pub fn add_prim(&mut self, primitive: Primitive, loc: LamLoc) -> PrimId {
        let i = PrimId(checked_u32(self.prims.len()));
        self.prims.push(PrimPayload { primitive, loc });
        i
    }

    /// Appends an application payload.
    pub fn add_apply(&mut self, info: ApInfo, transformed_jsx: bool) -> ApplyId {
        let i = ApplyId(checked_u32(self.applies.len()));
        self.applies.push(ApplyPayload {
            info,
            transformed_jsx,
        });
        i
    }

    /// Appends a function header.
    pub fn add_func(
        &mut self,
        arity: i32,
        params: IdentSpan,
        attr: FunctionAttribute,
        loc: LamLoc,
    ) -> FuncId {
        let i = FuncId(checked_u32(self.funcs.len()));
        self.funcs.push(FuncPayload {
            arity,
            params,
            attr,
            loc,
        });
        i
    }

    fn add_switch_keys(&mut self, keys: impl IntoIterator<Item = SwitchKey>) -> (u32, u32) {
        let start = self.switch_keys.len();
        self.switch_keys.extend(keys);
        (
            checked_u32(start),
            checked_u32(self.switch_keys.len() - start),
        )
    }

    /// Payload for a switch with the given keys; actions are supplied by the
    /// node.
    pub fn add_switch(
        &mut self,
        consts_full: bool,
        const_keys: impl IntoIterator<Item = SwitchKey>,
        blocks_full: bool,
        block_keys: impl IntoIterator<Item = SwitchKey>,
        has_fail: bool,
        dispatch: SwitchDispatch,
    ) -> SwitchId {
        let const_keys = self.add_switch_keys(const_keys);
        let block_keys = self.add_switch_keys(block_keys);
        let i = SwitchId(checked_u32(self.switches.len()));
        self.switches.push(SwitchPayload {
            consts_full,
            blocks_full,
            has_fail,
            const_keys,
            block_keys,
            dispatch,
        });
        i
    }

    /// The same switch keys and dispatch, with a different fail presence.
    pub fn switch_with_fail(&mut self, info: SwitchId, has_fail: bool) -> SwitchId {
        if self.switches[info.index()].has_fail == has_fail {
            return info;
        }
        let mut p = self.switches[info.index()].clone();
        p.has_fail = has_fail;
        let i = SwitchId(checked_u32(self.switches.len()));
        self.switches.push(p);
        i
    }

    /// Payload for a string switch with the given keys; actions are supplied by
    /// the node.
    pub fn add_str_switch<'k>(
        &mut self,
        keys: impl IntoIterator<Item = &'k str>,
        has_default: bool,
    ) -> StrSwitchId {
        let start = self.str_keys.len();
        for key in keys {
            let ts = checked_u32(self.text.len());
            self.text.push_str(key);
            self.str_keys.push((ts, checked_u32(key.len())));
        }
        let i = StrSwitchId(checked_u32(self.str_switches.len()));
        self.str_switches.push(StrSwitchPayload {
            keys: (checked_u32(start), checked_u32(self.str_keys.len() - start)),
            has_default,
        });
        i
    }

    /// The same string-switch keys with a different default presence.
    pub fn str_switch_with_default(&mut self, info: StrSwitchId, has_default: bool) -> StrSwitchId {
        let mut p = self.str_switches[info.index()];
        if p.has_default == has_default {
            return info;
        }
        p.has_default = has_default;
        let i = StrSwitchId(checked_u32(self.str_switches.len()));
        self.str_switches.push(p);
        i
    }

    /// Appends a static-catch header.
    pub fn add_catch(&mut self, label: i32, params: IdentSpan) -> CatchId {
        let i = CatchId(checked_u32(self.catches.len()));
        self.catches.push(CatchPayload { label, params });
        i
    }

    // ------------------------------------------------- plain constructors

    /// A variable reference.
    pub fn var(&mut self, id: Ident) -> Lam {
        let id = self.add_ident(id);
        self.push(Node::Var(id))
    }

    /// A global module reference.
    pub fn global_module(&mut self, id: Ident) -> Lam {
        let id = self.add_ident(id);
        self.push(Node::GlobalModule(id))
    }

    /// A constant.
    pub fn const_(&mut self, c: Constant) -> Lam {
        let c = self.add_const(c);
        self.push(Node::Const(c))
    }

    /// The `true` constant.
    pub fn true_(&mut self) -> Lam {
        self.const_(Constant::JsTrue)
    }

    /// The `false` constant.
    pub fn false_(&mut self) -> Lam {
        self.const_(Constant::JsFalse)
    }

    /// The unit constant.
    pub fn unit(&mut self) -> Lam {
        self.const_(Constant::JsUndefined { is_unit: true })
    }

    /// A function definition.
    pub fn function_(
        &mut self,
        arity: i32,
        params: &[Ident],
        body: Lam,
        attr: FunctionAttribute,
        loc: LamLoc,
    ) -> Lam {
        let params = self.add_idents(params);
        let info = self.add_func(arity, params, attr, loc);
        self.push(Node::Function { body, info })
    }

    /// A function with the header of `info` and a new body.
    pub fn function_with(&mut self, info: FuncId, body: Lam) -> Lam {
        self.push(Node::Function { body, info })
    }

    /// A `let` binding.
    pub fn let_(&mut self, kind: LetKind, id: Ident, value: Lam, body: Lam) -> Lam {
        let id = self.add_ident(id);
        self.push(Node::Let {
            kind,
            id,
            value,
            body,
        })
    }

    /// A `let` binding whose binder is already in the identifier table.
    pub fn let_with(&mut self, kind: LetKind, id: IdentId, value: Lam, body: Lam) -> Lam {
        self.push(Node::Let {
            kind,
            id,
            value,
            body,
        })
    }

    /// A `let rec` group.
    pub fn letrec(&mut self, bindings: &[(Ident, Lam)], body: Lam) -> Lam {
        let ids = self.add_idents_iter(bindings.iter().map(|(id, _)| *id));
        let values = self.add_list_iter(bindings.iter().map(|(_, v)| *v));
        self.push(Node::LetRec {
            ids: IdentId(ids.start),
            values,
            body,
        })
    }

    /// A `let rec` group from an existing binder run and value list.
    pub fn letrec_with(&mut self, ids: IdentId, values: LamList, body: Lam) -> Lam {
        self.push(Node::LetRec { ids, values, body })
    }

    /// `Lprim` without constant folding.
    pub fn prim_raw(&mut self, primitive: Primitive, args: &[Lam], loc: LamLoc) -> Lam {
        let info = self.add_prim(primitive, loc);
        let args = self.add_list(args);
        self.push(Node::Prim { args, info })
    }

    /// `Lprim` reusing an existing primitive payload, without constant folding.
    pub fn prim_raw_with(&mut self, info: PrimId, args: LamList) -> Lam {
        self.push(Node::Prim { args, info })
    }

    /// `Lapply` without the simplifications of [`Self::apply`].
    pub fn apply_raw(&mut self, func: Lam, args: &[Lam], info: ApInfo, jsx: bool) -> Lam {
        let info = self.add_apply(info, jsx);
        let args = self.add_list(args);
        self.push(Node::Apply { func, args, info })
    }

    /// `Lapply` reusing existing arguments and application payload.
    pub fn apply_raw_with(&mut self, func: Lam, args: LamList, info: ApplyId) -> Lam {
        self.push(Node::Apply { func, args, info })
    }

    /// A switch node from existing actions and payload.
    pub fn switch_raw(&mut self, scrut: Lam, actions: LamList, info: SwitchId) -> Lam {
        self.push(Node::Switch {
            scrut,
            actions,
            info,
        })
    }

    /// A string-switch node from existing actions and payload.
    pub fn string_switch_raw(&mut self, scrut: Lam, actions: LamList, info: StrSwitchId) -> Lam {
        self.push(Node::StringSwitch {
            scrut,
            actions,
            info,
        })
    }

    /// A static raise to `label`.
    pub fn static_raise(&mut self, label: i32, args: &[Lam]) -> Lam {
        let args = self.add_list(args);
        self.push(Node::StaticRaise { label, args })
    }

    /// A static raise to `label` with an existing argument list.
    pub fn static_raise_with(&mut self, label: i32, args: LamList) -> Lam {
        self.push(Node::StaticRaise { label, args })
    }

    /// A static catch of `label` around `body`.
    pub fn static_catch(&mut self, body: Lam, label: i32, params: &[Ident], handler: Lam) -> Lam {
        let params = self.add_idents(params);
        let info = self.add_catch(label, params);
        self.push(Node::StaticCatch {
            body,
            handler,
            info,
        })
    }

    /// A static catch reusing an existing header.
    pub fn static_catch_with(&mut self, body: Lam, info: CatchId, handler: Lam) -> Lam {
        self.push(Node::StaticCatch {
            body,
            handler,
            info,
        })
    }

    /// A `try` around `body`, binding the exception to `exn` in `handler`.
    pub fn try_(&mut self, body: Lam, exn: Ident, handler: Lam) -> Lam {
        let id = self.add_ident(exn);
        self.push(Node::TryWith { body, id, handler })
    }

    /// A `try` whose exception binder is already in the identifier table.
    pub fn try_with(&mut self, body: Lam, id: IdentId, handler: Lam) -> Lam {
        self.push(Node::TryWith { body, id, handler })
    }

    /// An `if` without the simplifications of [`Self::if_`].
    pub fn if_raw(&mut self, cond: Lam, then_: Lam, else_: Lam) -> Lam {
        self.push(Node::If { cond, then_, else_ })
    }

    /// A sequence without the simplifications of [`Self::seq`].
    pub fn seq_raw(&mut self, first: Lam, second: Lam) -> Lam {
        self.push(Node::Sequence(first, second))
    }

    /// A `break`.
    pub fn break_(&mut self) -> Lam {
        self.push(Node::Break)
    }

    /// A `continue`.
    pub fn continue_(&mut self) -> Lam {
        self.push(Node::Continue)
    }

    /// A `while` loop.
    pub fn while_(&mut self, cond: Lam, body: Lam) -> Lam {
        self.push(Node::While(cond, body))
    }

    /// A counted `for` loop.
    pub fn for_(
        &mut self,
        var: Ident,
        start: Lam,
        finish: Lam,
        dir: DirectionFlag,
        body: Lam,
    ) -> Lam {
        let id = self.add_ident(var);
        self.for_with(id, start, finish, dir, body)
    }

    /// A counted `for` loop whose variable is already in the identifier table.
    pub fn for_with(
        &mut self,
        id: IdentId,
        start: Lam,
        finish: Lam,
        dir: DirectionFlag,
        body: Lam,
    ) -> Lam {
        let kids = self.add_list(&[start, finish, body]);
        self.push(Node::For { dir, id, kids })
    }

    /// A `for...of` loop.
    pub fn for_of(&mut self, var: Ident, iter: Lam, body: Lam) -> Lam {
        let id = self.add_ident(var);
        self.push(Node::ForOf { id, iter, body })
    }

    /// A `for await...of` loop.
    pub fn for_await_of(&mut self, var: Ident, iter: Lam, body: Lam) -> Lam {
        let id = self.add_ident(var);
        self.push(Node::ForAwaitOf { id, iter, body })
    }

    /// An assignment to a mutable variable.
    pub fn assign(&mut self, var: Ident, value: Lam) -> Lam {
        let id = self.add_ident(var);
        self.push(Node::Assign { id, value })
    }

    /// An assignment whose variable is already in the identifier table.
    pub fn assign_with(&mut self, id: IdentId, value: Lam) -> Lam {
        self.push(Node::Assign { id, value })
    }

    /// New switch from owned keys and actions, through `Lam.switch`.
    pub fn switch(&mut self, scrut: Lam, spec: SwitchSpec) -> Lam {
        let SwitchSpec {
            consts_full,
            consts,
            blocks_full,
            blocks,
            fail,
            dispatch,
        } = spec;
        let actions = self.add_list_iter(
            consts
                .iter()
                .map(|(_, a)| *a)
                .chain(blocks.iter().map(|(_, a)| *a))
                .chain(fail),
        );
        let info = self.add_switch(
            consts_full,
            consts.into_iter().map(|(k, _)| k),
            blocks_full,
            blocks.into_iter().map(|(k, _)| k),
            fail.is_some(),
            dispatch,
        );
        self.switch_with(scrut, actions, info)
    }

    /// New string switch, through `Lam.stringswitch`.
    pub fn string_switch(
        &mut self,
        scrut: Lam,
        cases: &[(&str, Lam)],
        default: Option<Lam>,
    ) -> Lam {
        let actions = self.add_list_iter(cases.iter().map(|(_, a)| *a).chain(default));
        let info = self.add_str_switch(cases.iter().map(|(k, _)| *k), default.is_some());
        self.string_switch_with(scrut, actions, info)
    }

    // ------------------------------------------------- smart constructors

    /// `Lam.prim` (compiler/core/lam.ml:478-582), including its constant
    /// folds and the `Blk_module` alias collapse.
    pub fn prim(&mut self, primitive: Primitive, args: &[Lam], loc: LamLoc) -> Lam {
        match self.fold_prim(&primitive, args) {
            Some(Folded::Const(c)) => self.const_(c),
            Some(Folded::Node(lam)) => lam,
            None => self.prim_raw(primitive, args, loc),
        }
    }

    /// [`Self::prim`] reusing an existing primitive payload.
    pub fn prim_with(&mut self, info: PrimId, args: LamList) -> Lam {
        let folded = {
            let primitive = &self.prims[info.index()].primitive;
            self.fold_prim(primitive, self.list(args))
        };
        match folded {
            Some(Folded::Const(c)) => self.const_(c),
            Some(Folded::Node(lam)) => lam,
            None => self.prim_raw_with(info, args),
        }
    }

    /// [`Self::prim`] reusing an existing primitive payload, with new
    /// arguments.
    pub fn prim_with_id(&mut self, info: PrimId, args: &[Lam]) -> Lam {
        let args = self.add_list(args);
        self.prim_with(info, args)
    }

    fn fold_prim(&self, primitive: &Primitive, args: &[Lam]) -> Option<Folded> {
        let c = |c| Some(Folded::Const(c));
        let b = |v: bool| {
            Some(Folded::Const(if v {
                Constant::JsTrue
            } else {
                Constant::JsFalse
            }))
        };
        match args {
            // lam.ml:482-498 — single-arg constant folds.
            [a] if self.is_const(*a) => {
                let a = self.as_const(*a).expect("checked constant");
                match (primitive, a) {
                    (Primitive::Pnegint, Constant::Int { i, .. }) => {
                        c(Constant::int(i.wrapping_neg()))
                    }
                    (Primitive::Pintoffloat, Constant::Float(s)) => match s.parse::<f64>() {
                        Ok(f) => c(Constant::int(f as i32)),
                        Err(_) => None,
                    },
                    (Primitive::Pstringlength, Constant::String(s)) => c(Constant::int(
                        crate::string_literal::utf16_length(s)
                            .expect("String_literal.utf16_length: Invalid_utf8")
                            as i32,
                    )),
                    (Primitive::Pnot, Constant::JsTrue) => c(Constant::JsFalse),
                    (Primitive::Pnot, Constant::JsFalse) => c(Constant::JsTrue),
                    _ => None,
                }
            }
            // lam.ml:499-548 — two-arg constant folds.
            [a, bb] if self.is_const(*a) && self.is_const(*bb) => {
                let a = self.as_const(*a).expect("checked constant");
                let bv = self.as_const(*bb).expect("checked constant");
                match (primitive, a, bv) {
                    (
                        Primitive::Pintcomp(cmp),
                        Constant::Int { i: ai, .. },
                        Constant::Int { i: bi, .. },
                    ) => b(cmp.cmp_int32(*ai, *bi)),
                    (Primitive::Pfloatcomp(cmp), Constant::Float(af), Constant::Float(bf)) => {
                        match (af.parse::<f64>(), bf.parse::<f64>()) {
                            (Ok(av), Ok(bv)) => b(cmp.cmp_float(av, bv)),
                            _ => None,
                        }
                    }
                    (
                        Primitive::Pintcomp(op @ (Comparison::Eq | Comparison::Neq)),
                        Constant::Pointer(ai),
                        Constant::Pointer(bi),
                    ) => {
                        let eq = ai == bi;
                        b(match op {
                            Comparison::Eq => eq,
                            _ => !eq,
                        })
                    }
                    (
                        Primitive::Paddint
                        | Primitive::Psubint
                        | Primitive::Pmulint
                        | Primitive::Pdivint
                        | Primitive::Pmodint
                        | Primitive::Pandint
                        | Primitive::Porint
                        | Primitive::Pxorint
                        | Primitive::Plslint
                        | Primitive::Plsrint
                        | Primitive::Pasrint,
                        Constant::Int { i: aa, .. },
                        Constant::Int { i: bb, .. },
                    ) => match primitive {
                        Primitive::Paddint => c(Constant::int(aa.wrapping_add(*bb))),
                        Primitive::Psubint => c(Constant::int(aa.wrapping_sub(*bb))),
                        Primitive::Pmulint => c(Constant::int(aa.wrapping_mul(*bb))),
                        Primitive::Pdivint => {
                            if *bb == 0 {
                                None
                            } else {
                                c(Constant::int(aa.wrapping_div(*bb)))
                            }
                        }
                        Primitive::Pmodint => {
                            if *bb == 0 {
                                None
                            } else {
                                c(Constant::int(aa.wrapping_rem(*bb)))
                            }
                        }
                        Primitive::Pandint => c(Constant::int(aa & bb)),
                        Primitive::Porint => c(Constant::int(aa | bb)),
                        Primitive::Pxorint => c(Constant::int(aa ^ bb)),
                        Primitive::Plslint => c(Constant::int(aa.wrapping_shl(*bb as u32))),
                        Primitive::Plsrint => {
                            c(Constant::int((*aa as u32).wrapping_shr(*bb as u32) as i32))
                        }
                        Primitive::Pasrint => c(Constant::int(aa.wrapping_shr(*bb as u32))),
                        _ => unreachable!(),
                    },
                    (
                        Primitive::Psequand,
                        Constant::JsFalse,
                        Constant::JsTrue | Constant::JsFalse,
                    ) => b(false),
                    (Primitive::Psequand, Constant::JsTrue, Constant::JsTrue) => b(true),
                    (Primitive::Psequand, Constant::JsTrue, Constant::JsFalse) => b(false),
                    (
                        Primitive::Psequor,
                        Constant::JsTrue,
                        Constant::JsTrue | Constant::JsFalse,
                    ) => b(true),
                    (Primitive::Psequor, Constant::JsFalse, Constant::JsTrue) => b(true),
                    (Primitive::Psequor, Constant::JsFalse, Constant::JsFalse) => b(false),
                    (Primitive::Pstringadd, Constant::String(a_s), Constant::String(b_s)) => {
                        c(Constant::String(format!("{}{}", a_s, b_s)))
                    }
                    (
                        Primitive::Pstringrefs | Primitive::Pstringrefu,
                        Constant::String(s),
                        Constant::Int { i: idx, .. },
                    ) => match crate::string_literal::code_point_at_utf16_index(s, *idx as i64) {
                        Ok(Some(codepoint)) => c(Constant::Char(codepoint as i32)),
                        _ => None,
                    },
                    _ => None,
                }
            }
            // lam.ml:549-582 — `Pmakeblock (Blk_module fields)` alias collapse.
            _ => self
                .fold_makeblock_module_alias(primitive, args)
                .map(Folded::Node),
        }
    }

    /// Port of OCaml's `Lam.prim` `Blk_module` collapse arm (lam.ml:551-575).
    fn fold_makeblock_module_alias(&self, primitive: &Primitive, args: &[Lam]) -> Option<Lam> {
        let Primitive::Pmakeblock(TagInfo::Module(fields), _) = primitive else {
            return None;
        };
        if fields.len() != args.len() || fields.is_empty() {
            return None;
        }
        let module_field = |arg: Lam| -> Option<(i32, &str, Lam)> {
            let (Primitive::Pfield(pos, lam_compat::FieldDbgInfo::Module { name }), inner, _) =
                self.as_prim(arg)?
            else {
                return None;
            };
            let [src] = inner else {
                return None;
            };
            Some((*pos, name.as_str(), *src))
        };
        let (pos, f1, source_lam) = module_field(args[0])?;
        if pos != 0 || f1 != fields[0] {
            return None;
        }
        let source_ident = match self.node(source_lam) {
            Node::GlobalModule(v) | Node::Var(v) => self.ident(v),
            _ => return None,
        };
        for (i, (arg, expected_name)) in args.iter().zip(fields.iter()).enumerate().skip(1) {
            let (pos, name, src) = module_field(*arg)?;
            if pos as usize != i || name != expected_name {
                return None;
            }
            let same = match self.node(src) {
                Node::GlobalModule(v) | Node::Var(v) => self.ident(v).same(&source_ident),
                _ => false,
            };
            if !same {
                return None;
            }
        }
        Some(source_lam)
    }

    /// `Lam.switch` for an existing payload: a constant scrutinee picks its
    /// action at construction time.
    pub fn switch_with(&mut self, scrut: Lam, actions: LamList, info: SwitchId) -> Lam {
        match self.decide_switch(scrut, actions, info) {
            Some(action) => action,
            None => self.switch_raw(scrut, actions, info),
        }
    }

    /// The action `Lam.switch` selects for a constant scrutinee, if any.
    pub(crate) fn decide_switch(
        &self,
        scrut: Lam,
        actions: LamList,
        info: SwitchId,
    ) -> Option<Lam> {
        let cst = self.as_const(scrut)?;
        let payload = &self.switches[info.index()];
        let acts = self.switch_actions(info, actions);
        let const_keys = self.switch_const_keys(info);
        let block_keys = self.switch_block_keys(info);
        // lambda.ml `switch`: an untagged variant is dispatched on the value.
        if let SwitchDispatch::Variant(facts) = &payload.dispatch
            && !facts.block_types.is_empty()
        {
            return match crate::lambda::untagged_action_index(facts, cst, const_keys, block_keys) {
                crate::lambda::UntaggedChoice::Const(i) => Some(acts.consts[i]),
                crate::lambda::UntaggedChoice::Block(i) => Some(acts.blocks[i]),
                crate::lambda::UntaggedChoice::NoCase => acts.fail,
                crate::lambda::UntaggedChoice::Undecided => None,
            };
        }
        match cst {
            Constant::Constructor(tag) => const_keys
                .iter()
                .position(|key| {
                    matches!(
                        key,
                        SwitchKey::Constructor(crate::types::VariantConstructorCase::Constant(
                            candidate
                        )) if candidate == tag
                    )
                })
                .map(|i| acts.consts[i])
                .or(acts.fail),
            Constant::Int { i, .. } => const_keys
                .iter()
                .position(|key| matches!(key, SwitchKey::Int(value) if value == i))
                .map(|i| acts.consts[i])
                .or(acts.fail),
            Constant::Block { tag_info, .. } => {
                let runtime = match &**tag_info {
                    TagInfo::Constructor(c) => {
                        Some(crate::types::VariantBlock::Tagged((*c.runtime).clone()))
                    }
                    TagInfo::RecordInlined(r) => Some((*r.runtime).clone()),
                    _ => None,
                };
                block_keys
                    .iter()
                    .position(|key| {
                        matches!(
                            (key, runtime.as_ref()),
                            (
                                SwitchKey::Constructor(crate::types::VariantConstructorCase::Block(candidate)),
                                Some(runtime)
                            ) if candidate == runtime
                        )
                    })
                    .map(|i| acts.blocks[i])
                    .or(acts.fail)
            }
            _ => None,
        }
    }

    /// `Lam.stringswitch` for an existing payload.
    pub fn string_switch_with(&mut self, scrut: Lam, actions: LamList, info: StrSwitchId) -> Lam {
        let decided = match self.as_const(scrut) {
            Some(Constant::String(s) | Constant::ImmString(s)) => {
                let p = self.str_switches[info.index()];
                let all = self.list(actions);
                (0..p.n_cases())
                    .find(|&i| self.str_switch_key(info, i) == s.as_str())
                    .map(|i| all[i])
                    .or_else(|| p.has_default.then(|| all[p.n_cases()]))
            }
            _ => None,
        };
        match decided {
            Some(action) => action,
            None => self.string_switch_raw(scrut, actions, info),
        }
    }

    /// `Lam.apply`.
    pub fn apply(&mut self, func: Lam, args: &[Lam], info: ApInfo, jsx: bool) -> Lam {
        match self.node(func) {
            Node::Function { body, info: f } => {
                if let Some(reduced) = self.eta_reduce_function_apply(f, body, args, &info) {
                    return reduced;
                }
                self.apply_raw(func, args, info, jsx)
            }
            Node::Let {
                kind,
                id,
                value,
                body,
            } if matches!(self.node(body), Node::Function { .. }) => {
                let inner = self.apply(body, args, info, jsx);
                self.let_with(kind, id, value, inner)
            }
            _ => self.apply_raw(func, args, info, jsx),
        }
    }

    /// [`Self::apply`] reusing an existing application payload.
    pub fn apply_with(&mut self, func: Lam, args: LamList, info: ApplyId) -> Lam {
        match self.node(func) {
            Node::Function { .. } | Node::Let { .. } => {
                let ApplyPayload {
                    info: ap_info,
                    transformed_jsx,
                } = self.applies[info.index()].clone();
                let args = self.list_vec(args);
                self.apply(func, &args, ap_info, transformed_jsx)
            }
            _ => self.apply_raw_with(func, args, info),
        }
    }

    fn eta_reduce_function_apply(
        &mut self,
        function: FuncId,
        body: Lam,
        args: &[Lam],
        ap_info: &ApInfo,
    ) -> Option<Lam> {
        let params = self.funcs[function.index()].params;
        match self.node(body) {
            Node::Prim {
                args: wrap_args,
                info: wrap,
            } if matches!(
                self.prims[wrap.index()].primitive,
                Primitive::PnullToOpt
                    | Primitive::PnullUndefinedToOpt
                    | Primitive::PisNull
                    | Primitive::PisNullUndefined
                    | Primitive::Ptypeof
            ) =>
            {
                let [inner_call] = self.list(wrap_args) else {
                    return None;
                };
                let inner_call = *inner_call;
                let Node::Prim {
                    args: inner_args,
                    info: inner_info,
                } = self.node(inner_call)
                else {
                    return None;
                };
                let eta_args = self.eta_conversion_args(params, inner_args, args)?;
                let wrap_prim = self.prims[wrap.index()].primitive.clone();
                let inner_prim = self.prims[inner_info.index()].primitive.clone();
                let inner = self.prim(inner_prim, &eta_args, ap_info.loc);
                Some(self.prim(wrap_prim, &[inner], ap_info.loc))
            }
            Node::Prim {
                args: inner_args,
                info: inner_info,
            } => {
                let eta_args = self.eta_conversion_args(params, inner_args, args)?;
                let inner_prim = self.prims[inner_info.index()].primitive.clone();
                Some(self.prim(inner_prim, &eta_args, ap_info.loc))
            }
            Node::Sequence(first, second) => {
                let Node::Prim {
                    args: inner_args,
                    info: inner_info,
                } = self.node(first)
                else {
                    return None;
                };
                if !self.is_const(second) {
                    return None;
                }
                let eta_args = self.eta_conversion_args(params, inner_args, args)?;
                let inner_prim = self.prims[inner_info.index()].primitive.clone();
                let inner = self.prim(inner_prim, &eta_args, ap_info.loc);
                Some(self.seq(inner, second))
            }
            _ => None,
        }
    }

    fn eta_conversion_args(
        &self,
        params: IdentSpan,
        inner_args: LamList,
        outer_args: &[Lam],
    ) -> Option<smallvec::SmallVec<[Lam; 8]>> {
        let params = self.idents(params);
        let inner_args = self.list(inner_args);
        if params.len() != inner_args.len() || params.len() != outer_args.len() {
            return None;
        }
        params
            .iter()
            .zip(inner_args.iter())
            .zip(outer_args.iter())
            .map(
                |((param, inner_arg), outer_arg)| match self.as_var(*inner_arg) {
                    Some(id) if param.same(&id) => Some(*outer_arg),
                    _ => None,
                },
            )
            .collect()
    }

    /// `Lam.seq`.
    pub fn seq(&mut self, first: Lam, second: Lam) -> Lam {
        if let Node::Prim { args, info } = self.node(first) {
            match &self.prims[info.index()].primitive {
                Primitive::Pmakeblock(_, _) => {
                    let args = self.list_vec(args);
                    let Some((&first_arg, rest)) = args.split_first() else {
                        return self.seq_raw(first, second);
                    };
                    let mut acc = first_arg;
                    for &arg in rest {
                        acc = self.seq(acc, arg);
                    }
                    return self.seq(acc, second);
                }
                Primitive::PnullToOpt | Primitive::PnullUndefinedToOpt
                    if self.list_len(args) == 1 =>
                {
                    let arg = self.list(args)[0];
                    return self.seq(arg, second);
                }
                _ => {}
            }
        }
        self.seq_raw(first, second)
    }

    fn is_assertfalse(&self, lam: Lam) -> bool {
        matches!(
            self.as_const(lam),
            Some(Constant::Int { comment: Some(info), .. })
                if matches!(**info, lam_constant::PointerInfo::AssertFalse)
        )
    }

    fn has_boolean_type(&self, lam: Lam) -> Option<LamLoc> {
        let (primitive, _, loc) = self.as_prim(lam)?;
        matches!(
            primitive,
            Primitive::Pnot
                | Primitive::Psequand
                | Primitive::Psequor
                | Primitive::PisNotNone
                | Primitive::Pobjcomp(_)
                | Primitive::Pboolcomp(_)
                | Primitive::Pintcomp(_)
                | Primitive::Pfloatcomp(_)
                | Primitive::Pbigintcomp(_)
                | Primitive::Pstringcomp(_)
        )
        .then_some(loc)
    }

    fn lambda_not(&mut self, loc: LamLoc, lam: Lam) -> Lam {
        if let Node::Prim { args, info } = self.node(lam)
            && matches!(
                self.prims[info.index()].primitive,
                Primitive::Pintcomp(Comparison::Neq)
            )
        {
            let ploc = self.prims[info.index()].loc;
            let info = self.add_prim(Primitive::Pintcomp(Comparison::Eq), ploc);
            return self.prim_raw_with(info, args);
        }
        self.prim(Primitive::Pnot, &[lam], loc)
    }

    /// `[Lvar j; Lconst _]` with `j == i`: the comparison operands of the
    /// `Pisint` rewrites in `Lam.if_`.
    fn is_var_const_cmp(&self, args: &[Lam], i: &Ident) -> bool {
        matches!(args, [v, c] if self.is_const(*c) && self.as_var(*v).is_some_and(|j| i.same(&j)))
    }

    /// `Lam.if_`.
    pub fn if_(&mut self, cond: Lam, then_: Lam, else_: Lam) -> Lam {
        if let Some(constant) = self.as_const(cond) {
            return if constant.eval_as_bool() {
                then_
            } else {
                else_
            };
        }
        if self.is_assertfalse(else_) {
            return self.seq(cond, then_);
        }
        if self.is_assertfalse(then_) {
            return self.seq(cond, else_);
        }
        let then_c = self.as_const(then_);
        let else_c = self.as_const(else_);
        if matches!(
            (then_c, else_c),
            (Some(Constant::JsTrue), Some(Constant::JsFalse))
        ) {
            return if self.has_boolean_type(cond).is_some() {
                cond
            } else {
                self.if_raw(cond, then_, else_)
            };
        }
        if matches!(
            (then_c, else_c),
            (Some(Constant::JsFalse), Some(Constant::JsTrue))
        ) {
            return match self.has_boolean_type(cond) {
                Some(loc) => self.lambda_not(loc, cond),
                None => self.if_raw(cond, then_, else_),
            };
        }
        if let Some((Primitive::Pisint, pargs, _)) = self.as_prim(cond)
            && let [v] = pargs
            && let Some(i) = self.as_var(*v)
        {
            if let Some(r) = self.if_pisint(&i, then_, else_) {
                return r;
            }
        }
        self.if_raw(cond, then_, else_)
    }

    fn if_pisint(&mut self, i: &Ident, then_: Lam, else_: Lam) -> Option<Lam> {
        // if (Pisint i) then (if (i == c) then _ else e) else e
        if let Node::If {
            cond: pred,
            else_: branch_false,
            ..
        } = self.node(then_)
            && let Some((Primitive::Pintcomp(Comparison::Eq), pred_args, _)) = self.as_prim(pred)
            && self.is_var_const_cmp(pred_args, i)
            && self.eq_approx(branch_false, else_)
        {
            return Some(then_);
        }
        // if (Pisint i) then (i == c) else false
        if let Some((Primitive::Pintcomp(Comparison::Eq), pred_args, _)) = self.as_prim(then_)
            && self.is_var_const_cmp(pred_args, i)
            && matches!(self.as_const(else_), Some(Constant::JsFalse))
        {
            return Some(then_);
        }
        // if (Pisint i) then (if (i != c) then t else f) else t
        if let Node::If {
            cond: pred,
            then_: branch_true,
            else_: branch_false,
        } = self.node(then_)
            && let Node::Prim {
                args: pred_args,
                info,
            } = self.node(pred)
            && matches!(
                self.prims[info.index()].primitive,
                Primitive::Pintcomp(Comparison::Neq)
            )
            && self.is_var_const_cmp(self.list(pred_args), i)
            && self.eq_approx(branch_true, else_)
        {
            let loc = self.prims[info.index()].loc;
            let info = self.add_prim(Primitive::Pintcomp(Comparison::Eq), loc);
            let cmp = self.prim_raw_with(info, pred_args);
            return Some(self.if_raw(cmp, branch_false, branch_true));
        }
        match self.as_prim(then_) {
            Some((Primitive::Pintcomp(Comparison::Neq), pred_args, _)) => {
                if self.is_var_const_cmp(pred_args, i)
                    && matches!(self.as_const(else_), Some(Constant::JsTrue))
                {
                    let Node::Prim { args, .. } = self.node(then_) else {
                        unreachable!()
                    };
                    let (_, _, loc) = self.as_prim(then_).expect("checked primitive");
                    let info = self.add_prim(Primitive::Pintcomp(Comparison::Neq), loc);
                    return Some(self.prim_raw_with(info, args));
                }
            }
            Some((Primitive::Pnot, [inner], _)) => {
                let inner = *inner;
                if let Node::Prim { args, info } = self.node(inner)
                    && matches!(
                        self.prims[info.index()].primitive,
                        Primitive::Pintcomp(Comparison::Eq)
                    )
                    && self.is_var_const_cmp(self.list(args), i)
                    && matches!(self.as_const(else_), Some(Constant::JsTrue))
                {
                    let loc = self.prims[info.index()].loc;
                    let info = self.add_prim(Primitive::Pintcomp(Comparison::Neq), loc);
                    return Some(self.prim_raw_with(info, args));
                }
            }
            _ => {}
        }
        None
    }

    /// `Lam.eq_approx`.
    pub fn eq_approx(&self, lhs: Lam, rhs: Lam) -> bool {
        match (self.node(lhs), self.node(rhs)) {
            (Node::GlobalModule(i1), Node::GlobalModule(i2)) | (Node::Var(i1), Node::Var(i2)) => {
                self.ident(i1).same(&self.ident(i2))
            }
            (Node::Const(c1), Node::Const(c2)) => self.constant(c1).eq_approx(self.constant(c2)),
            (
                Node::Apply {
                    func: f1, args: a1, ..
                },
                Node::Apply {
                    func: f2, args: a2, ..
                },
            ) => self.eq_approx(f1, f2) && self.list_eq_approx(a1, a2),
            (
                Node::If {
                    cond: a1,
                    then_: b1,
                    else_: c1,
                },
                Node::If {
                    cond: a2,
                    then_: b2,
                    else_: c2,
                },
            ) => self.eq_approx(a1, a2) && self.eq_approx(b1, b2) && self.eq_approx(c1, c2),
            (Node::Sequence(a1, b1), Node::Sequence(a2, b2))
            | (Node::While(a1, b1), Node::While(a2, b2)) => {
                self.eq_approx(a1, a2) && self.eq_approx(b1, b2)
            }
            (Node::Break, Node::Break) | (Node::Continue, Node::Continue) => true,
            (Node::Assign { id: v1, value: l1 }, Node::Assign { id: v2, value: l2 }) => {
                self.ident(v1).same(&self.ident(v2)) && self.eq_approx(l1, l2)
            }
            (
                Node::StaticRaise {
                    label: id1,
                    args: a1,
                },
                Node::StaticRaise {
                    label: id2,
                    args: a2,
                },
            ) => id1 == id2 && self.list_eq_approx(a1, a2),
            (Node::Prim { args: a1, info: p1 }, Node::Prim { args: a2, info: p2 }) => {
                self.prims[p1.index()]
                    .primitive
                    .eq_approx(&self.prims[p2.index()].primitive)
                    && self.list_eq_approx(a1, a2)
            }
            (
                Node::StringSwitch {
                    scrut: s1,
                    actions: a1,
                    info: i1,
                },
                Node::StringSwitch {
                    scrut: s2,
                    actions: a2,
                    info: i2,
                },
            ) => {
                let p1 = self.str_switch_payload(i1);
                let p2 = self.str_switch_payload(i2);
                let (l1, l2) = (self.list(a1), self.list(a2));
                self.eq_approx(s1, s2)
                    && p1.has_default == p2.has_default
                    && (!p1.has_default || self.eq_approx(l1[p1.n_cases()], l2[p2.n_cases()]))
                    && p1.n_cases() == p2.n_cases()
                    && (0..p1.n_cases()).all(|i| {
                        self.str_switch_key(i1, i) == self.str_switch_key(i2, i)
                            && self.eq_approx(l1[i], l2[i])
                    })
            }
            _ => false,
        }
    }

    fn list_eq_approx(&self, a: LamList, b: LamList) -> bool {
        let (a, b) = (self.list(a), self.list(b));
        a.len() == b.len() && a.iter().zip(b).all(|(x, y)| self.eq_approx(*x, *y))
    }

    // ---------------------------------------------------- generic rebuild

    /// Applies `f` to each direct child of `lam` and rebuilds the node if any
    /// child changed, through the same smart constructors as
    /// `Lambda_traverse.shallow_map_sharing` (applications, primitives and
    /// switches) and plain construction otherwise. Unchanged nodes keep
    /// their handle.
    pub fn shallow_map(&mut self, lam: Lam, f: &mut impl FnMut(&mut Self, Lam) -> Lam) -> Lam {
        self.shallow_map_impl(lam, f, true)
    }

    /// [`Self::shallow_map`] rebuilding every changed node with its plain
    /// constructor, without folding.
    pub fn shallow_map_plain(
        &mut self,
        lam: Lam,
        f: &mut impl FnMut(&mut Self, Lam) -> Lam,
    ) -> Lam {
        self.shallow_map_impl(lam, f, false)
    }

    fn shallow_map_impl(
        &mut self,
        lam: Lam,
        f: &mut impl FnMut(&mut Self, Lam) -> Lam,
        smart: bool,
    ) -> Lam {
        match self.node(lam) {
            Node::Var(_)
            | Node::GlobalModule(_)
            | Node::Const(_)
            | Node::Break
            | Node::Continue => lam,
            Node::Apply { func, args, info } => {
                let nf = f(self, func);
                let (nargs, changed) = self.map_list(args, f);
                if nf == func && !changed {
                    return lam;
                }
                if smart {
                    self.apply_with(nf, nargs, info)
                } else {
                    self.apply_raw_with(nf, nargs, info)
                }
            }
            Node::Function { body, info } => {
                let nb = f(self, body);
                if nb == body {
                    lam
                } else {
                    self.function_with(info, nb)
                }
            }
            Node::Let {
                kind,
                id,
                value,
                body,
            } => {
                let nv = f(self, value);
                let nb = f(self, body);
                if nv == value && nb == body {
                    lam
                } else {
                    self.let_with(kind, id, nv, nb)
                }
            }
            Node::LetRec { ids, values, body } => {
                let (nvalues, changed) = self.map_list(values, f);
                let nb = f(self, body);
                if !changed && nb == body {
                    lam
                } else {
                    self.letrec_with(ids, nvalues, nb)
                }
            }
            Node::Prim { args, info } => {
                let (nargs, changed) = self.map_list(args, f);
                if !changed {
                    return lam;
                }
                if smart {
                    self.prim_with(info, nargs)
                } else {
                    self.prim_raw_with(info, nargs)
                }
            }
            Node::Switch {
                scrut,
                actions,
                info,
            } => {
                let ns = f(self, scrut);
                let (nactions, changed) = self.map_list(actions, f);
                if ns == scrut && !changed {
                    return lam;
                }
                if smart {
                    self.switch_with(ns, nactions, info)
                } else {
                    self.switch_raw(ns, nactions, info)
                }
            }
            Node::StringSwitch {
                scrut,
                actions,
                info,
            } => {
                let ns = f(self, scrut);
                let (nactions, changed) = self.map_list(actions, f);
                if ns == scrut && !changed {
                    return lam;
                }
                if smart {
                    self.string_switch_with(ns, nactions, info)
                } else {
                    self.string_switch_raw(ns, nactions, info)
                }
            }
            Node::StaticRaise { label, args } => {
                let (nargs, changed) = self.map_list(args, f);
                if changed {
                    self.static_raise_with(label, nargs)
                } else {
                    lam
                }
            }
            Node::StaticCatch {
                body,
                handler,
                info,
            } => {
                let nb = f(self, body);
                let nh = f(self, handler);
                if nb == body && nh == handler {
                    lam
                } else {
                    self.static_catch_with(nb, info, nh)
                }
            }
            Node::TryWith { body, id, handler } => {
                let nb = f(self, body);
                let nh = f(self, handler);
                if nb == body && nh == handler {
                    lam
                } else {
                    self.try_with(nb, id, nh)
                }
            }
            Node::If { cond, then_, else_ } => {
                let nc = f(self, cond);
                let nt = f(self, then_);
                let ne = f(self, else_);
                if nc == cond && nt == then_ && ne == else_ {
                    lam
                } else if smart {
                    self.if_(nc, nt, ne)
                } else {
                    self.if_raw(nc, nt, ne)
                }
            }
            Node::Sequence(a, b) => {
                let na = f(self, a);
                let nb = f(self, b);
                if na == a && nb == b {
                    lam
                } else if smart {
                    self.seq(na, nb)
                } else {
                    self.seq_raw(na, nb)
                }
            }
            Node::While(a, b) => {
                let na = f(self, a);
                let nb = f(self, b);
                if na == a && nb == b {
                    lam
                } else {
                    self.while_(na, nb)
                }
            }
            Node::For { dir, id, kids } => {
                let (nkids, changed) = self.map_list(kids, f);
                if changed {
                    self.push(Node::For {
                        dir,
                        id,
                        kids: nkids,
                    })
                } else {
                    lam
                }
            }
            Node::ForOf { id, iter, body } => {
                let ni = f(self, iter);
                let nb = f(self, body);
                if ni == iter && nb == body {
                    lam
                } else {
                    self.push(Node::ForOf {
                        id,
                        iter: ni,
                        body: nb,
                    })
                }
            }
            Node::ForAwaitOf { id, iter, body } => {
                let ni = f(self, iter);
                let nb = f(self, body);
                if ni == iter && nb == body {
                    lam
                } else {
                    self.push(Node::ForAwaitOf {
                        id,
                        iter: ni,
                        body: nb,
                    })
                }
            }
            Node::Assign { id, value } => {
                let nv = f(self, value);
                if nv == value {
                    lam
                } else {
                    self.assign_with(id, nv)
                }
            }
        }
    }

    /// Maps every element of `list` in order. Returns the original handle
    /// when nothing changed, otherwise a new list.
    pub fn map_list(
        &mut self,
        list: LamList,
        f: &mut impl FnMut(&mut Self, Lam) -> Lam,
    ) -> (LamList, bool) {
        let len = self.list_len(list);
        let base = list.index() + 1;
        let mut i = 0;
        while i < len {
            let old = self.pool[base + i];
            let new = f(self, old);
            if new != old {
                // Copy the unchanged prefix, then map the rest into a buffer.
                let mut out: smallvec::SmallVec<[Lam; 8]> = smallvec::SmallVec::with_capacity(len);
                out.extend_from_slice(&self.pool[base..base + i]);
                out.push(new);
                for j in i + 1..len {
                    let old = self.pool[base + j];
                    out.push(f(self, old));
                }
                return (self.add_list(&out), true);
            }
            i += 1;
        }
        (list, false)
    }

    /// Calls `f` on each direct child of `lam`, in the order of
    /// `Lambda_traverse.shallow_iter`.
    pub fn iter_children(&self, lam: Lam, mut f: impl FnMut(Lam)) {
        match self.node(lam) {
            Node::Var(_)
            | Node::GlobalModule(_)
            | Node::Const(_)
            | Node::Break
            | Node::Continue => {}
            Node::Apply { func, args, .. } => {
                f(func);
                self.list(args).iter().copied().for_each(f);
            }
            Node::Function { body, .. } => f(body),
            Node::Let { value, body, .. } => {
                f(value);
                f(body);
            }
            Node::LetRec { values, body, .. } => {
                self.list(values).iter().copied().for_each(&mut f);
                f(body);
            }
            Node::Prim { args, .. } | Node::StaticRaise { args, .. } => {
                self.list(args).iter().copied().for_each(f)
            }
            Node::Switch { scrut, actions, .. } | Node::StringSwitch { scrut, actions, .. } => {
                f(scrut);
                self.list(actions).iter().copied().for_each(f);
            }
            Node::StaticCatch { body, handler, .. } | Node::TryWith { body, handler, .. } => {
                f(body);
                f(handler);
            }
            Node::If { cond, then_, else_ } => {
                f(cond);
                f(then_);
                f(else_);
            }
            Node::Sequence(a, b) | Node::While(a, b) => {
                f(a);
                f(b);
            }
            Node::For { kids, .. } => self.list(kids).iter().copied().for_each(f),
            Node::ForOf { iter, body, .. } | Node::ForAwaitOf { iter, body, .. } => {
                f(iter);
                f(body);
            }
            Node::Assign { value, .. } => f(value),
        }
    }

    // ------------------------------------------------------ tree boundary

    /// Copies a recursive Lambda into the arena without re-running smart
    /// constructors (the tree is already in constructor-normal form).
    pub fn import(&mut self, lam: &Lambda) -> Lam {
        match lam {
            Lambda::Lvar(id) => self.var(*id),
            Lambda::LglobalModule(id) => self.global_module(*id),
            Lambda::Lconst(c) => self.const_(c.clone()),
            Lambda::Lapply(ap) => {
                let func = self.import(&ap.ap_func);
                let args = self.import_list(&ap.ap_args);
                let info = self.add_apply(ap.ap_info.clone(), ap.ap_transformed_jsx);
                self.apply_raw_with(func, args, info)
            }
            Lambda::Lfunction(func) => {
                let body = self.import(&func.body);
                let params = self.add_idents(&func.params);
                let info = self.add_func(func.arity, params, func.attr.clone(), func.loc);
                self.function_with(info, body)
            }
            Lambda::Llet(kind, id, value, body) => {
                let value = self.import(value);
                let body = self.import(body);
                self.let_(*kind, *id, value, body)
            }
            Lambda::Lletrec(bindings, body) => {
                let values: smallvec::SmallVec<[Lam; 8]> =
                    bindings.iter().map(|(_, v)| self.import(v)).collect();
                let body = self.import(body);
                let ids = self.add_idents_iter(bindings.iter().map(|(id, _)| *id));
                let values = self.add_list(&values);
                self.letrec_with(IdentId(ids.start), values, body)
            }
            Lambda::Lprim(info) => {
                let args = self.import_list(&info.args);
                let p = self.add_prim(info.primitive.clone(), info.loc);
                self.prim_raw_with(p, args)
            }
            Lambda::Lswitch(scrut, sw) => {
                let scrut = self.import(scrut);
                let actions: smallvec::SmallVec<[Lam; 8]> = sw
                    .sw_consts
                    .iter()
                    .map(|(_, a)| a)
                    .chain(sw.sw_blocks.iter().map(|(_, a)| a))
                    .chain(sw.sw_failaction.as_deref())
                    .map(|a| self.import(a))
                    .collect();
                let actions = self.add_list(&actions);
                let info = self.add_switch(
                    sw.sw_consts_full,
                    sw.sw_consts.iter().map(|(k, _)| k.clone()),
                    sw.sw_blocks_full,
                    sw.sw_blocks.iter().map(|(k, _)| k.clone()),
                    sw.sw_failaction.is_some(),
                    sw.sw_dispatch.clone(),
                );
                self.switch_raw(scrut, actions, info)
            }
            Lambda::LstringSwitch(scrut, cases, default) => {
                let scrut = self.import(scrut);
                let actions: smallvec::SmallVec<[Lam; 8]> = cases
                    .iter()
                    .map(|(_, a)| a)
                    .chain(default.as_deref())
                    .map(|a| self.import(a))
                    .collect();
                let actions = self.add_list(&actions);
                let info =
                    self.add_str_switch(cases.iter().map(|(k, _)| k.as_str()), default.is_some());
                self.string_switch_raw(scrut, actions, info)
            }
            Lambda::LstaticRaise(label, args) => {
                let args = self.import_list(args);
                self.static_raise_with(*label, args)
            }
            Lambda::LstaticCatch(body, (label, params), handler) => {
                let body = self.import(body);
                let handler = self.import(handler);
                self.static_catch(body, *label, params, handler)
            }
            Lambda::LtryWith(body, id, handler) => {
                let body = self.import(body);
                let handler = self.import(handler);
                self.try_(body, *id, handler)
            }
            Lambda::LifThenElse(c, t, e) => {
                let c = self.import(c);
                let t = self.import(t);
                let e = self.import(e);
                self.if_raw(c, t, e)
            }
            Lambda::Lsequence(a, b) => {
                let a = self.import(a);
                let b = self.import(b);
                self.seq_raw(a, b)
            }
            Lambda::Lbreak => self.break_(),
            Lambda::Lcontinue => self.continue_(),
            Lambda::Lwhile(c, b) => {
                let c = self.import(c);
                let b = self.import(b);
                self.while_(c, b)
            }
            Lambda::Lfor(id, start, finish, dir, body) => {
                let start = self.import(start);
                let finish = self.import(finish);
                let body = self.import(body);
                self.for_(*id, start, finish, *dir, body)
            }
            Lambda::LforOf(id, iter, body) => {
                let iter = self.import(iter);
                let body = self.import(body);
                self.for_of(*id, iter, body)
            }
            Lambda::LforAwaitOf(id, iter, body) => {
                let iter = self.import(iter);
                let body = self.import(body);
                self.for_await_of(*id, iter, body)
            }
            Lambda::Lassign(id, value) => {
                let value = self.import(value);
                self.assign(*id, value)
            }
        }
    }

    fn import_list(&mut self, items: &[Lambda]) -> LamList {
        let lams: smallvec::SmallVec<[Lam; 8]> = items.iter().map(|x| self.import(x)).collect();
        self.add_list(&lams)
    }

    /// Copies the subtree at `lam` of `other` into this arena.
    pub fn copy_from(&mut self, other: &LamArena, lam: Lam) -> Lam {
        // Through the tree form: only used at the CMJ boundary for small
        // inline bodies.
        let tree = other.export(lam);
        self.import(&tree)
    }

    /// Materializes `lam` as a recursive Lambda (debug printers, CMJ
    /// payloads and tests).
    pub fn export(&self, lam: Lam) -> Lambda {
        match self.node(lam) {
            Node::Var(id) => Lambda::Lvar(self.ident(id)),
            Node::GlobalModule(id) => Lambda::LglobalModule(self.ident(id)),
            Node::Const(c) => Lambda::Lconst(self.constant(c).clone()),
            Node::Apply { func, args, info } => {
                let p = &self.applies[info.index()];
                Lambda::Lapply(Box::new(Apply {
                    ap_func: Box::new(self.export(func)),
                    ap_args: self.export_list(args),
                    ap_info: p.info.clone(),
                    ap_transformed_jsx: p.transformed_jsx,
                }))
            }
            Node::Function { body, info } => {
                let p = &self.funcs[info.index()];
                Lambda::Lfunction(Box::new(LFunction {
                    arity: p.arity,
                    params: self.idents(p.params).to_vec(),
                    body: Box::new(self.export(body)),
                    attr: p.attr.clone(),
                    loc: p.loc,
                }))
            }
            Node::Let {
                kind,
                id,
                value,
                body,
            } => Lambda::Llet(
                kind,
                self.ident(id),
                Box::new(self.export(value)),
                Box::new(self.export(body)),
            ),
            Node::LetRec { ids, values, body } => {
                let values = self.list(values);
                Lambda::Lletrec(
                    self.ident_run(ids, values.len())
                        .iter()
                        .zip(values)
                        .map(|(id, v)| (*id, self.export(*v)))
                        .collect(),
                    Box::new(self.export(body)),
                )
            }
            Node::Prim { args, info } => {
                let p = &self.prims[info.index()];
                Lambda::Lprim(Box::new(PrimInfo {
                    primitive: p.primitive.clone(),
                    args: self.export_list(args),
                    loc: p.loc,
                }))
            }
            Node::Switch {
                scrut,
                actions,
                info,
            } => {
                let p = &self.switches[info.index()];
                let acts = self.switch_actions(info, actions);
                Lambda::Lswitch(
                    Box::new(self.export(scrut)),
                    Box::new(LambdaSwitch {
                        sw_consts_full: p.consts_full,
                        sw_consts: self
                            .switch_const_keys(info)
                            .iter()
                            .zip(acts.consts)
                            .map(|(k, a)| (k.clone(), self.export(*a)))
                            .collect(),
                        sw_blocks_full: p.blocks_full,
                        sw_blocks: self
                            .switch_block_keys(info)
                            .iter()
                            .zip(acts.blocks)
                            .map(|(k, a)| (k.clone(), self.export(*a)))
                            .collect(),
                        sw_failaction: acts.fail.map(|a| Box::new(self.export(a))),
                        sw_dispatch: p.dispatch.clone(),
                    }),
                )
            }
            Node::StringSwitch {
                scrut,
                actions,
                info,
            } => {
                let (cases, default) = self.str_switch_cases(info, actions);
                Lambda::LstringSwitch(
                    Box::new(self.export(scrut)),
                    cases
                        .map(|(k, a)| (k.to_string(), self.export(a)))
                        .collect(),
                    default.map(|d| Box::new(self.export(d))),
                )
            }
            Node::StaticRaise { label, args } => {
                Lambda::LstaticRaise(label, self.export_list(args))
            }
            Node::StaticCatch {
                body,
                handler,
                info,
            } => {
                let p = self.catch_payload(info);
                Lambda::LstaticCatch(
                    Box::new(self.export(body)),
                    (p.label, self.idents(p.params).to_vec()),
                    Box::new(self.export(handler)),
                )
            }
            Node::TryWith { body, id, handler } => Lambda::LtryWith(
                Box::new(self.export(body)),
                self.ident(id),
                Box::new(self.export(handler)),
            ),
            Node::If { cond, then_, else_ } => Lambda::LifThenElse(
                Box::new(self.export(cond)),
                Box::new(self.export(then_)),
                Box::new(self.export(else_)),
            ),
            Node::Sequence(a, b) => {
                Lambda::Lsequence(Box::new(self.export(a)), Box::new(self.export(b)))
            }
            Node::Break => Lambda::Lbreak,
            Node::Continue => Lambda::Lcontinue,
            Node::While(a, b) => Lambda::Lwhile(Box::new(self.export(a)), Box::new(self.export(b))),
            Node::For { dir, id, kids } => {
                let [s, e, b] = self.list(kids) else {
                    unreachable!("for node has three children")
                };
                Lambda::Lfor(
                    self.ident(id),
                    Box::new(self.export(*s)),
                    Box::new(self.export(*e)),
                    dir,
                    Box::new(self.export(*b)),
                )
            }
            Node::ForOf { id, iter, body } => Lambda::LforOf(
                self.ident(id),
                Box::new(self.export(iter)),
                Box::new(self.export(body)),
            ),
            Node::ForAwaitOf { id, iter, body } => Lambda::LforAwaitOf(
                self.ident(id),
                Box::new(self.export(iter)),
                Box::new(self.export(body)),
            ),
            Node::Assign { id, value } => {
                Lambda::Lassign(self.ident(id), Box::new(self.export(value)))
            }
        }
    }

    fn export_list(&self, list: LamList) -> Vec<Lambda> {
        self.list(list).iter().map(|x| self.export(*x)).collect()
    }

    /// `[start; finish; body]` of a `For` node.
    pub fn for_parts(&self, kids: LamList) -> (Lam, Lam, Lam) {
        let [s, e, b] = self.list(kids) else {
            unreachable!("for node has three children")
        };
        (*s, *e, *b)
    }
}

enum Folded {
    Const(Constant),
    Node(Lam),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ident::IdentFlags;

    fn id(name: &str, stamp: i32) -> Ident {
        Ident::new(name, stamp, IdentFlags::NONE)
    }

    fn sample() -> Lambda {
        let x = id("x", 1);
        let f = id("f", 2);
        let e = id("e", 3);
        Lambda::let_(
            LetKind::Strict,
            x,
            Lambda::const_(Constant::int(1)),
            Lambda::letrec(
                vec![(
                    f,
                    Lambda::function_(
                        1,
                        vec![x],
                        Lambda::LstaticCatch(
                            Box::new(Lambda::LstaticRaise(1, vec![Lambda::var(x)])),
                            (1, vec![e]),
                            Box::new(Lambda::LstringSwitch(
                                Box::new(Lambda::var(e)),
                                vec![
                                    ("a".into(), Lambda::true_()),
                                    ("b".into(), Lambda::false_()),
                                ],
                                Some(Box::new(Lambda::unit())),
                            )),
                        ),
                        FunctionAttribute::default(),
                        LamLoc::NONE,
                    ),
                )],
                Lambda::Lsequence(
                    Box::new(Lambda::Lfor(
                        e,
                        Box::new(Lambda::const_(Constant::int(0))),
                        Box::new(Lambda::var(x)),
                        DirectionFlag::Upto,
                        Box::new(Lambda::Lassign(x, Box::new(Lambda::var(e)))),
                    )),
                    Box::new(Lambda::Lprim(Box::new(PrimInfo {
                        primitive: Primitive::Paddint,
                        args: vec![Lambda::var(x), Lambda::var(f)],
                        loc: LamLoc::NONE,
                    }))),
                ),
            ),
        )
    }

    fn print(lam: &Lambda) -> String {
        let mut buf = Vec::new();
        crate::lambda::printlambda::print_lambda(lam, &mut buf);
        String::from_utf8(buf).unwrap()
    }

    #[test]
    fn stamp_bound_includes_all_identifier_insertion_paths() {
        let mut a = LamArena::new();
        assert_eq!(a.ident_stamp_bound(), 0);
        let root = a.import(&sample());
        assert_eq!(a.ident_stamp_bound(), 3);
        assert_eq!(
            crate::lambda::lam_beta_reduce::max_ident_stamp_in_lambda(&a, root),
            3,
        );
        a.add_ident(id("unused", 10));
        a.add_idents(&[id("param", 20)]);
        a.add_idents_iter([id("catch", 30)]);
        assert_eq!(a.ident_stamp_bound(), 30);
        // Unreachable identifiers still reserve their stamps.
        assert_eq!(
            crate::lambda::lam_beta_reduce::max_ident_stamp_in_lambda(&a, root),
            3,
        );
    }

    #[test]
    fn import_export_round_trips() {
        let lam = sample();
        let mut a = LamArena::new();
        let root = a.import(&lam);
        assert_eq!(print(&a.export(root)), print(&lam));
    }

    #[test]
    fn shallow_map_identity_keeps_handles() {
        let lam = sample();
        let mut a = LamArena::new();
        let root = a.import(&lam);
        let before = a.node_count();
        let mapped = a.shallow_map(root, &mut |_, x| x);
        assert_eq!(mapped, root);
        assert_eq!(a.node_count(), before);
    }

    #[test]
    fn prim_folds_constants() {
        let mut a = LamArena::new();
        let one = a.const_(Constant::int(1));
        let two = a.const_(Constant::int(2));
        let sum = a.prim(Primitive::Paddint, &[one, two], LamLoc::NONE);
        assert!(matches!(a.as_const(sum), Some(Constant::Int { i: 3, .. })));
    }

    #[test]
    fn smart_constructors_match_tree() {
        let x = id("x", 1);
        let cond_tree = Lambda::prim(
            Primitive::Pintcomp(Comparison::Neq),
            vec![Lambda::var(x), Lambda::const_(Constant::int(0))],
            LamLoc::NONE,
        );
        let tree = Lambda::if_(cond_tree.clone(), Lambda::false_(), Lambda::true_());
        let mut a = LamArena::new();
        let cond = a.import(&cond_tree);
        let f = a.false_();
        let t = a.true_();
        let r = a.if_(cond, f, t);
        assert_eq!(print(&a.export(r)), print(&tree));
    }

    #[test]
    fn node_is_sixteen_bytes() {
        assert_eq!(std::mem::size_of::<Node>(), 16);
    }
}
