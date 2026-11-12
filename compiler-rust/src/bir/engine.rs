//! The rewrite engine (BACKEND_REDESIGN.md C.1, C.5): rounds, subtree
//! summaries, the normalising worklist and per-round snapshots.
//!
//! Contract, with the cost of every operation:
//!
//! - A **normalising rule** (`bir/l/norm.rs`) sees a node in three places and
//!   nowhere else: when the node is built through [`Engine::build`]; when a
//!   rule asks for it with [`Engine::push`] (the node it rewrote, or a node it
//!   created); and, during a round, when the sweep returns to an ancestor of a
//!   rewrite whose opcode is in the round's `renorm` mask. No normalising rule
//!   reads a use count, so a count change never triggers one.
//! - The **worklist** is a stack of nodes waiting for their normalising rule.
//!   [`Engine::push`] is one vector push. Rules never call each other: a rule
//!   edits, pushes what must be looked at next and returns, so no rewrite
//!   recurses however deep the term is. Entries pop in reverse push order,
//!   pushes happen in rule code order, and nothing iterates a hash table, so
//!   the result is a function of the tree alone. A rule pushes only the node
//!   it was given or nodes it created below it, parent before child; an entry
//!   is therefore never released before it is popped.
//! - A **rule attempt** reads the node and a bounded number of levels below
//!   it (`norm.rs` states the pattern of each row); it never walks a subtree,
//!   with one documented exception (row N11).
//! - An **edit** ([`Engine::promote`], [`Engine::put`]) costs the nodes it
//!   removes, plus a recount of the kept content only when that content
//!   changes use weight (`Bir::replace_local`).
//! - A **round** is one sweep of the tree in a fixed order. A subtree whose
//!   summary does not intersect the round's mask is not entered. The sweep
//!   uses an explicit stack. Total cost: the nodes entered plus the rewrites.
//! - A **summary** is a 16-bit set of opcode classes per node, a superset of
//!   the classes in its subtree. It is set when the engine creates a node and
//!   widened on the way back up a sweep; it is recomputed in one walk only
//!   when an edit was made outside a sweep.
//! - A **snapshot** is a detached copy of a subtree taken before the first
//!   edit inside it in a round, so that rules can read the subtree as it was
//!   when the round started. Cost: the size of the subtree, once per round,
//!   and only if something below it is edited.
use super::*;
use crate::fast_hash::AHashMap;
use smallvec::SmallVec;

/// A set of opcode classes. Sixteen classes; level J shares one.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct OpMask(pub u16);
impl OpMask {
    /// No class.
    pub const NONE: Self = Self(0);
    /// Every class.
    pub const ALL: Self = Self(u16::MAX);
    /// Variable uses.
    pub const VAR: Self = Self(1);
    /// Constants, module references, `break` and `continue`.
    pub const LEAF: Self = Self(1 << 1);
    /// Applications.
    pub const APPLY: Self = Self(1 << 2);
    /// Functions.
    pub const FUN: Self = Self(1 << 3);
    /// `let`.
    pub const LET: Self = Self(1 << 4);
    /// `let rec`.
    pub const LETREC: Self = Self(1 << 5);
    /// Primitive applications.
    pub const PRIM: Self = Self(1 << 6);
    /// Integer and constructor switches.
    pub const SWITCH: Self = Self(1 << 7);
    /// String switches.
    pub const STR_SWITCH: Self = Self(1 << 8);
    /// Static exits.
    pub const EXIT: Self = Self(1 << 9);
    /// Static catches.
    pub const CATCH: Self = Self(1 << 10);
    /// `try` and `try`/`finally`.
    pub const TRY: Self = Self(1 << 11);
    /// Conditionals.
    pub const IF: Self = Self(1 << 12);
    /// Sequences.
    pub const SEQ: Self = Self(1 << 13);
    /// Loops and assignments.
    pub const LOOP: Self = Self(1 << 14);
    /// Every level J opcode.
    pub const J: Self = Self(1 << 15);
    /// What `LamArena::shallow_map` rebuilds through a smart constructor.
    pub const SHALLOW_MAP: Self =
        Self(Self::APPLY.0 | Self::PRIM.0 | Self::SWITCH.0 | Self::STR_SWITCH.0);

    /// The class of one opcode.
    pub fn of(op: Op) -> Self {
        match op {
            Op::Var => Self::VAR,
            Op::Global | Op::Const | Op::Break | Op::Continue => Self::LEAF,
            Op::Apply => Self::APPLY,
            Op::Fun => Self::FUN,
            Op::Let => Self::LET,
            Op::LetRec => Self::LETREC,
            Op::Prim => Self::PRIM,
            Op::Switch => Self::SWITCH,
            Op::StrSwitch => Self::STR_SWITCH,
            Op::Exit => Self::EXIT,
            Op::Catch => Self::CATCH,
            Op::Try | Op::TryFinally => Self::TRY,
            Op::If => Self::IF,
            Op::Seq => Self::SEQ,
            Op::While | Op::For | Op::ForOf | Op::ForAwaitOf | Op::Assign => Self::LOOP,
            _ => Self::J,
        }
    }
    /// Union.
    pub const fn or(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }
    /// Whether the sets share a class.
    pub const fn intersects(self, other: Self) -> bool {
        self.0 & other.0 != 0
    }
}

/// Whether a rule rewrote the node it was offered.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Changed {
    /// The node is as it was.
    No,
    /// The node, or something below it, was rewritten.
    Yes,
}

/// When a round's rule runs relative to the node's children.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Order {
    /// The rule runs first; the sweep then enters the children the node has
    /// after the rule.
    Pre,
    /// The children are swept first.
    Post,
}

/// Which binding facts the rules of a round read.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Facts {
    /// The arena's facts, current after every edit.
    Current,
    /// A copy of the fact column taken when the round starts (today's
    /// `collect_info` before a pass), read with [`Engine::fact`].
    Frozen,
}

/// One sweep of the tree with one rule.
pub struct Round {
    /// Name for reports.
    pub name: &'static str,
    /// Opcode classes the rule can match. Other nodes are not offered and
    /// subtrees without these classes are not entered.
    pub mask: OpMask,
    /// Traversal order.
    pub order: Order,
    /// Opcode classes re-normalised when the sweep returns to a node with a
    /// rewrite below it: [`OpMask::SHALLOW_MAP`] for a pass that rebuilds
    /// through `shallow_map`, [`OpMask::NONE`] for one that rebuilds plainly.
    pub renorm: OpMask,
    /// Facts the rule reads.
    pub facts: Facts,
    /// Nodes to snapshot before the first edit inside them (C.2 row 1).
    pub guard: Option<fn(&Engine<'_>, NodeId) -> bool>,
    /// The rule. It may edit the offered node and below it, nothing else.
    pub rule: fn(&mut Engine<'_>, NodeId) -> Changed,
}

/// Counters for reports and step-count tests.
#[derive(Debug, Default, Clone)]
pub struct Stats {
    /// Worklist pushes.
    pub pushes: u64,
    /// Normalising rule attempts.
    pub attempts: u64,
    /// Rewrites by normalising rules, per row of the table in `norm.rs`.
    pub fired: [u32; crate::bir::l::norm::ROWS],
    /// Nodes entered by sweeps.
    pub entered: u64,
    /// Subtrees a sweep did not enter because of their summary.
    pub pruned: u64,
    /// Snapshots taken.
    pub snapshots: u64,
    /// Nodes compared by row N11's structural equality.
    pub compared: u64,
}

struct Guard {
    node: NodeId,
    taken: bool,
}

struct Frame {
    node: NodeId,
    children: SmallVec<[NodeId; 4]>,
    next: usize,
    changed: bool,
    guarded: bool,
}

/// Drives rules over one unit. Deaths of unused bindings are deferred while
/// an engine exists (C.2 row 5); [`Engine::resume_deaths`] ends that.
pub struct Engine<'a> {
    bir: &'a mut Bir,
    worklist: Vec<NodeId>,
    summary: Vec<OpMask>,
    summaries_valid: bool,
    in_sweep: bool,
    facts: Vec<Fact>,
    frozen: bool,
    guards: Vec<Guard>,
    snapshots: AHashMap<NodeId, NodeId>,
    snapshot_roots: Vec<NodeId>,
    /// Counters.
    pub stats: Stats,
}

impl<'a> Engine<'a> {
    /// An engine over `bir`. Constant time.
    pub fn new(bir: &'a mut Bir) -> Self {
        bir.defer_deaths();
        Self {
            bir,
            worklist: Vec::new(),
            summary: Vec::new(),
            summaries_valid: false,
            in_sweep: false,
            facts: Vec::new(),
            frozen: false,
            guards: Vec::new(),
            snapshots: AHashMap::default(),
            snapshot_roots: Vec::new(),
            stats: Stats::default(),
        }
    }

    /// The arena, read-only: every edit goes through the engine.
    pub fn bir(&self) -> &Bir {
        self.bir
    }

    /// Intern text for a constant a rule creates.
    pub fn intern_text(&mut self, text: &str) -> StrId {
        self.bir.intern_text(text)
    }

    /// Intern a constant a rule creates.
    pub fn intern_const(&mut self, value: Constant) -> ConstId {
        self.bir.intern_const(value)
    }

    /// Intern a primitive with its location.
    pub fn intern_prim(
        &mut self,
        primitive: crate::lambda::lam_primitive::Primitive,
        loc: crate::lambda::LamLoc,
    ) -> PrimId {
        self.bir.intern_prim(PrimPayload { primitive, loc })
    }

    /// Mark unused pure bindings dead and keep doing so (the start of the
    /// round that ports `simplify_lets`). One scan of the variable table.
    pub fn resume_deaths(&mut self) {
        self.bir.resume_deaths();
    }

    #[cfg(test)]
    pub(crate) fn steps(&self) -> u64 {
        self.bir.steps.get() + self.stats.pushes
    }

    // ------------------------------------------------------------ summaries

    fn set_summary(&mut self, node: NodeId) {
        let mut mask = OpMask::of(self.bir.node(node).op());
        for child in self.bir.view(node).children() {
            mask = mask.or(self
                .summary
                .get(child.index())
                .copied()
                .unwrap_or(OpMask::ALL));
        }
        if self.summary.len() <= node.index() {
            // An unknown slot reads as "anything": a visit, never a miss.
            self.summary.resize(node.index() + 1, OpMask::ALL);
        }
        self.summary[node.index()] = mask;
    }

    /// The classes that may occur at or below `node`.
    pub fn summary(&self, node: NodeId) -> OpMask {
        if self.summaries_valid {
            self.summary
                .get(node.index())
                .copied()
                .unwrap_or(OpMask::ALL)
        } else {
            OpMask::ALL
        }
    }

    fn summarise(&mut self, root: NodeId) {
        let mut stack = vec![(root, false)];
        while let Some((node, done)) = stack.pop() {
            if done {
                self.set_summary(node);
            } else {
                stack.push((node, true));
                stack.extend(
                    self.bir
                        .view(node)
                        .children()
                        .into_iter()
                        .map(|c| (c, false)),
                );
            }
        }
        self.summaries_valid = true;
    }

    // ---------------------------------------------------------------- edits

    fn before_write(&mut self, target: NodeId) {
        if !self.in_sweep && self.bir.parents[target.index()].is_some() {
            // An edit outside a sweep has no path on which to widen the
            // summaries of the ancestors: recompute before the next round.
            self.summaries_valid = false;
        }
        for i in 0..self.guards.len() {
            if !self.guards[i].taken {
                self.guards[i].taken = true;
                let node = self.guards[i].node;
                self.take_snapshot(node);
            }
        }
    }

    /// The use weight of a slot, for [`Engine::node`].
    pub fn weight(&mut self, slot: NodeId) -> u32 {
        self.bir.weight_of(slot)
    }

    /// A new node whose children are detached. `weight` is the weight of the
    /// slot the rewrite fills ([`Engine::weight`]). Constant time for children
    /// that came from that slot.
    pub fn node(&mut self, view: View<'_>, aux: u16, weight: u32) -> NodeId {
        let id = self.bir.new_node_in(view, aux, weight);
        self.set_summary(id);
        id
    }

    /// Detach a node below the node being rewritten, to reuse it in the
    /// replacement. Constant time.
    pub fn detach(&mut self, node: NodeId) {
        self.before_write(node);
        self.bir.detach(node);
    }

    /// Replace `target`'s content by its descendant `kept`; everything else
    /// below `target` is released.
    pub fn promote(&mut self, target: NodeId, kept: NodeId) {
        self.before_write(target);
        self.bir.replace_local(target, kept);
        self.set_summary(target);
    }

    /// Replace `target`'s content by a new node built from nodes detached
    /// from below `target` and from new nodes. What was not detached is
    /// released. The rewrite must not move a variable use under a function
    /// or loop; a rule that does uses [`Engine::replace`].
    pub fn put(&mut self, target: NodeId, view: View<'_>, aux: u16) {
        self.before_write(target);
        let weight = self.bir.weight_of(target);
        let new = self.bir.new_node_in(view, aux, weight);
        self.bir.replace_local(target, new);
        self.set_summary(target);
    }

    /// [`Engine::put`] with a replacement already built by [`Engine::node`].
    /// The replacement's handle is invalid afterwards; handles below it stay.
    pub fn fill(&mut self, target: NodeId, replacement: NodeId) {
        self.before_write(target);
        self.bir.replace_local(target, replacement);
        self.set_summary(target);
    }

    /// Replace `target` by a detached tree that may hold uses moved under a
    /// function or loop (inlining). Costs a walk of the replacement.
    pub fn replace(&mut self, target: NodeId, replacement: NodeId) {
        self.before_write(target);
        self.bir.replace(target, replacement);
        self.set_summary(target);
    }

    /// Release a detached subtree.
    pub fn release(&mut self, node: NodeId) {
        self.bir.release(node);
    }

    // ------------------------------------------------------------- worklist

    /// Queue a node for its normalising rule. One vector push.
    pub fn push(&mut self, node: NodeId) {
        self.stats.pushes += 1;
        self.worklist.push(node);
    }

    fn drain(&mut self) -> Changed {
        let mut changed = Changed::No;
        while let Some(node) = self.worklist.pop() {
            debug_assert_ne!(
                self.bir.nodes[node.index()].op(),
                Op::Free,
                "stale worklist entry"
            );
            self.stats.attempts += 1;
            if crate::bir::l::norm::step(self, node) == Changed::Yes {
                changed = Changed::Yes;
            }
        }
        changed
    }

    /// Run the normalising rules on `node` until none applies to it or to
    /// what they produced. The node keeps its handle.
    pub fn normalise(&mut self, node: NodeId) -> Changed {
        self.push(node);
        self.drain()
    }

    /// Build a node through the normalising rules: what a `LamArena` smart
    /// constructor does when it is called. The children are detached roots.
    pub fn build(&mut self, view: View<'_>, aux: u16) -> NodeId {
        let id = self.node(view, aux, 1);
        self.normalise(id);
        id
    }

    /// One bottom-up normalising pass over a whole tree: every node is
    /// offered once, after its children. Linear in the nodes plus the
    /// rewrites.
    pub fn normalise_tree(&mut self, root: NodeId) -> Changed {
        self.run(&NORMALISE, root)
    }

    // --------------------------------------------------------------- rounds

    /// Run one round from `root`.
    pub fn run(&mut self, round: &Round, root: NodeId) -> Changed {
        if !self.summaries_valid {
            self.summarise(root);
        }
        if !self.summary(root).intersects(round.mask) {
            self.stats.pruned += 1;
            return Changed::No;
        }
        self.frozen = round.facts == Facts::Frozen;
        if self.frozen {
            self.facts.clear();
            self.facts.extend_from_slice(&self.bir.vars.fact);
        }
        self.in_sweep = true;
        let mut stack: Vec<Frame> = Vec::new();
        let mut result = Changed::No;
        let mut enter = Some(root);
        loop {
            if let Some(node) = enter.take() {
                self.stats.entered += 1;
                let guarded = round.guard.is_some_and(|guard| guard(self, node));
                if guarded {
                    self.guards.push(Guard { node, taken: false });
                }
                let mut changed = false;
                if round.order == Order::Pre
                    && round.mask.intersects(OpMask::of(self.bir.node(node).op()))
                {
                    changed = (round.rule)(self, node) == Changed::Yes;
                }
                stack.push(Frame {
                    node,
                    children: self.bir.view(node).children(),
                    next: 0,
                    changed,
                    guarded,
                });
            }
            let frame = stack.last_mut().expect("sweep frame");
            if frame.next < frame.children.len() {
                let child = frame.children[frame.next];
                frame.next += 1;
                if self.summary(child).intersects(round.mask) {
                    enter = Some(child);
                } else {
                    self.stats.pruned += 1;
                }
                continue;
            }
            let Frame {
                node,
                mut changed,
                guarded,
                ..
            } = stack.pop().expect("sweep frame");
            // The way back up: what a pass's rebuild of a changed spine does.
            if changed
                && round
                    .renorm
                    .intersects(OpMask::of(self.bir.node(node).op()))
            {
                self.normalise(node);
            }
            if round.order == Order::Post
                && round.mask.intersects(OpMask::of(self.bir.node(node).op()))
            {
                changed |= (round.rule)(self, node) == Changed::Yes;
            }
            if changed {
                self.set_summary(node);
            }
            if guarded {
                self.guards.pop();
            }
            match stack.last_mut() {
                Some(parent) => parent.changed |= changed,
                None => {
                    if changed {
                        result = Changed::Yes;
                    }
                    break;
                }
            }
        }
        self.in_sweep = false;
        self.frozen = false;
        self.end_round();
        result
    }

    // ------------------------------------------------- facts and snapshots

    /// The binding fact of `var` as the round's rules see it: frozen at the
    /// start of a [`Facts::Frozen`] round, current otherwise. A node in a
    /// frozen fact is read through [`Engine::as_of_round_start`]. A variable
    /// created during a frozen round has no fact until [`Engine::set_fact`].
    pub fn fact(&self, var: VarId) -> Fact {
        if self.frozen {
            self.facts
                .get(var.index())
                .copied()
                .unwrap_or(Fact::Unknown)
        } else {
            self.bir.vars().fact(var)
        }
    }

    /// Record a fact in the frozen table (today's passes add to `ident_tbl`
    /// as they create bindings).
    pub fn set_fact(&mut self, var: VarId, fact: Fact) {
        if self.frozen {
            if self.facts.len() <= var.index() {
                self.facts.resize(var.index() + 1, Fact::Unknown);
            }
            self.facts[var.index()] = fact;
        }
    }

    fn take_snapshot(&mut self, node: NodeId) {
        if self.snapshots.contains_key(&node) {
            return;
        }
        self.stats.snapshots += 1;
        let copy = self.bir.copy_subtree(node, &[]);
        self.snapshots.insert(node, copy);
        self.snapshot_roots.push(copy);
    }

    /// Snapshot `node` now. A rule calls this before it replaces a guarded
    /// node from outside (for example a binding's value while the binding
    /// stays); edits inside a guarded node are covered by the round's guard.
    pub fn preserve(&mut self, node: NodeId) {
        self.take_snapshot(node);
    }

    /// `node` as it was when the round started: its snapshot if something
    /// inside it was edited this round, the node itself otherwise. The
    /// snapshot is a detached copy with its own binders; copy from it, do not
    /// attach it.
    pub fn as_of_round_start(&self, node: NodeId) -> NodeId {
        self.snapshots.get(&node).copied().unwrap_or(node)
    }

    fn end_round(&mut self) {
        // Release in the order taken: no hash iteration.
        for copy in std::mem::take(&mut self.snapshot_roots) {
            self.bir.release(copy);
        }
        self.snapshots.clear();
        self.guards.clear();
    }
}

/// The round behind [`Engine::normalise_tree`].
pub static NORMALISE: Round = Round {
    name: "normalise",
    mask: OpMask(
        OpMask::PRIM.0
            | OpMask::IF.0
            | OpMask::SEQ.0
            | OpMask::SWITCH.0
            | OpMask::STR_SWITCH.0
            | OpMask::APPLY.0,
    ),
    order: Order::Post,
    renorm: OpMask::NONE,
    facts: Facts::Current,
    guard: None,
    rule: |engine, node| engine.normalise(node),
};

#[cfg(test)]
pub(crate) mod testing {
    //! Trees for engine and rule tests, built in the legacy arena and imported.
    use crate::bir::bridge::{Imported, import_lambda};
    use crate::ident::{Ident, IdentFlags};
    use crate::lambda::arena::{Lam, LamArena};
    use crate::lambda::lam_primitive::Primitive;
    use crate::lambda::{ApInfo, ApplyStatus, LamLoc};

    pub fn id(name: &str, stamp: i32) -> Ident {
        Ident::new(name, stamp, IdentFlags::NONE)
    }
    pub fn prim(a: &mut LamArena, p: Primitive, args: &[Lam]) -> Lam {
        a.prim_raw(p, args, LamLoc::NONE)
    }
    /// `f()`, a node no rule folds.
    pub fn call(a: &mut LamArena, name: &str, stamp: i32) -> Lam {
        let f = a.var(id(name, stamp));
        let unit = a.unit();
        a.apply_raw(
            f,
            &[unit],
            ApInfo {
                loc: LamLoc::NONE,
                status: ApplyStatus::Uncurry,
            },
        )
    }
    /// Import with the step counter reset.
    pub fn import(a: &LamArena, root: Lam) -> Imported {
        let imported = import_lambda(a, root).unwrap();
        imported.arena.steps.set(0);
        imported
    }
}

#[cfg(test)]
mod tests {
    use super::testing::*;
    use super::*;
    use crate::lambda::arena::LamArena;
    use crate::lambda::lam_compat::LetKind;
    use crate::lambda::lam_constant::Constant as C;
    use crate::lambda::lam_primitive::Primitive;
    use crate::lambda::{FunctionAttribute, LamLoc, SwitchDispatch, SwitchKey};

    fn identity_arg(e: &Engine<'_>, node: NodeId) -> Option<NodeId> {
        match e.bir().view(node) {
            View::Prim {
                args: [arg],
                primitive,
            } if matches!(e.bir().primitive(primitive).primitive, Primitive::Pidentity) => {
                Some(*arg)
            }
            _ => None,
        }
    }
    /// A pass rule for the tests: `identity(x)` becomes `x`.
    fn drop_identity(e: &mut Engine<'_>, node: NodeId) -> Changed {
        match identity_arg(e, node) {
            Some(arg) => {
                e.promote(node, arg);
                Changed::Yes
            }
            None => Changed::No,
        }
    }
    fn round(rule: fn(&mut Engine<'_>, NodeId) -> Changed) -> Round {
        Round {
            name: "test",
            mask: OpMask::PRIM,
            order: Order::Post,
            renorm: OpMask::NONE,
            facts: Facts::Current,
            guard: None,
            rule,
        }
    }

    #[test]
    fn pushing_is_one_step_and_an_attempt_on_a_leaf_is_one_read() {
        let mut a = LamArena::new();
        let root = a.unit();
        let mut unit = import(&a, root);
        let mut e = Engine::new(&mut unit.arena);
        for _ in 0..10_000 {
            e.push(unit.root);
        }
        assert_eq!(e.steps(), 10_000);
        e.drain();
        println!("COST 10000 pushes and attempts: {} steps", e.steps());
        assert_eq!(e.steps(), 20_000);
        assert_eq!(e.stats.attempts, 10_000);
    }

    #[test]
    fn a_round_enters_only_subtrees_that_can_hold_a_candidate() {
        // 2,000 statements, one of them `identity(f())` in the middle.
        let mut a = LamArena::new();
        let mut root = a.unit();
        for i in 0..2_000 {
            let mut statement = call(&mut a, "f", 1);
            if i == 1_000 {
                statement = prim(&mut a, Primitive::Pidentity, &[statement]);
            }
            let cond = a.var(id("c", 2));
            let unit = a.unit();
            let guarded = a.if_raw(cond, statement, unit);
            root = a.seq_raw(guarded, root);
        }
        let mut unit = import(&a, root);
        let mut e = Engine::new(&mut unit.arena);
        let switches = Round {
            mask: OpMask::SWITCH,
            ..round(drop_identity)
        };
        assert_eq!(e.run(&switches, unit.root), Changed::No);
        assert_eq!((e.stats.entered, e.stats.pruned), (0, 1));
        assert_eq!(e.run(&round(drop_identity), unit.root), Changed::Yes);
        // The spine above the candidate, the `if` and the primitive.
        println!(
            "COST sweep of 12001 nodes with one candidate: {} entered",
            e.stats.entered
        );
        assert!(e.stats.entered <= 1_003, "{}", e.stats.entered);
        // The summary was narrowed on the way back: nothing left to visit.
        let before = e.stats.entered;
        assert_eq!(e.run(&round(drop_identity), unit.root), Changed::No);
        assert_eq!(e.stats.entered, before);
        unit.arena.validate(Some(unit.root), false).unwrap();
    }

    #[test]
    fn a_round_is_linear_in_a_deep_chain_and_in_a_wide_node() {
        let mut a = LamArena::new();
        let mut deep = a.unit();
        for _ in 0..10_000 {
            let inner = call(&mut a, "f", 1);
            let statement = prim(&mut a, Primitive::Pidentity, &[inner]);
            deep = a.seq_raw(statement, deep);
        }
        // Pure children: a rewrite of one must not rescan its 10,000 siblings.
        let wide: Vec<_> = (0..10_000)
            .map(|_| {
                let inner = a.var(id("y", 2));
                prim(&mut a, Primitive::Pidentity, &[inner])
            })
            .collect();
        let wide = prim(
            &mut a,
            Primitive::Pmakeblock(
                crate::lambda::lam_tag_info::TagInfo::Tuple,
                crate::lambda::lam_primitive::Mutable::Immutable,
            ),
            &wide,
        );
        let root = a.seq_raw(wide, deep);
        let mut unit = import(&a, root);
        let mut e = Engine::new(&mut unit.arena);
        assert_eq!(e.run(&round(drop_identity), unit.root), Changed::Yes);
        let nodes = 10_000 * 5 + 10_000 * 2 + 3;
        println!(
            "COST round over {nodes} nodes, 20000 rewrites: {} steps, {} entered",
            e.steps(),
            e.stats.entered
        );
        assert!(e.steps() <= 24 * nodes, "{}", e.steps());
        unit.arena.validate(Some(unit.root), false).unwrap();
    }

    #[test]
    fn an_edit_keeps_counts_in_a_doubled_default_without_a_walk() {
        // switch c { | 0 => () | _ => (BIG; x) } with a default counted twice.
        let mut a = LamArena::new();
        let x = id("x", 1);
        let mut big = a.var(x);
        for _ in 0..5_000 {
            let use_ = a.var(x);
            big = a.seq_raw(use_, big);
        }
        let last = a.var(x);
        let default = a.seq_raw(big, last);
        let case = a.unit();
        let actions = a.add_list(&[case, default]);
        let info = a.add_switch(
            false,
            [SwitchKey::Int(0)],
            false,
            std::iter::empty(),
            true,
            SwitchDispatch::Direct,
        );
        let scrut = a.var(id("c", 2));
        let switch = a.switch_raw(scrut, actions, info);
        let value = a.unit();
        let root = a.let_(LetKind::Strict, x, value, switch);
        let mut unit = import(&a, root);
        let var = unit
            .arena
            .vars()
            .binder
            .iter()
            .position(|b| b.is_some())
            .unwrap();
        let var = VarId(var as u32);
        assert_eq!(unit.arena.vars().uses(var), 2 * 5_002);
        let View::Let { body, .. } = unit.arena.view(unit.root) else {
            panic!()
        };
        let View::Switch { actions, .. } = unit.arena.view(body) else {
            panic!()
        };
        let default = actions[1];
        let View::Seq { first, second } = unit.arena.view(default) else {
            panic!()
        };
        let mut e = Engine::new(&mut unit.arena);
        // Swap the two halves of the default: both keep their weight.
        e.detach(first);
        e.detach(second);
        e.put(
            default,
            View::Seq {
                first: second,
                second: first,
            },
            0,
        );
        println!(
            "COST swap of two subtrees in a doubled default: {} steps",
            e.steps()
        );
        assert!(e.steps() <= 128, "{}", e.steps());
        assert_eq!(unit.arena.vars().uses(var), 2 * 5_002);
        unit.arena.validate(Some(unit.root), false).unwrap();
    }

    fn function_with_identity(a: &mut LamArena, param: i32) -> crate::lambda::arena::Lam {
        let x = id("x", param);
        let vx = a.var(x);
        let body = prim(a, Primitive::Pidentity, &[vx]);
        a.function_(1, &[x], body, FunctionAttribute::default(), LamLoc::NONE)
    }

    fn check_snapshots(e: &mut Engine<'_>, node: NodeId) -> Changed {
        if let View::Let { var, .. } = e.bir().view(node) {
            if let Fact::Function { node: function, .. } = e.fact(var) {
                let old = e.as_of_round_start(function);
                let View::Fun { body, .. } = e.bir().view(old) else {
                    panic!()
                };
                let rewritten = e.bir().vars().name(var).as_str() == "f";
                // `f` is read as it was; `g` was never copied.
                assert_eq!(old != function, rewritten);
                assert_eq!(
                    e.bir().node(body).op(),
                    if rewritten { Op::Prim } else { Op::Var }
                );
            }
            return Changed::No;
        }
        drop_identity(e, node)
    }

    #[test]
    fn a_guarded_function_is_copied_before_the_first_edit_inside_it_only() {
        // let f = x => identity(x) in let g = y => y in f
        let mut a = LamArena::new();
        let (f, g) = (id("f", 1), id("g", 2));
        let fun_f = function_with_identity(&mut a, 3);
        let y = id("y", 4);
        let vy = a.var(y);
        let fun_g = a.function_(1, &[y], vy, FunctionAttribute::default(), LamLoc::NONE);
        let body = a.var(f);
        let inner = a.let_(LetKind::Strict, g, fun_g, body);
        let root = a.let_(LetKind::Strict, f, fun_f, inner);
        let mut unit = import(&a, root);
        let uses: Vec<u32> = (0..4).map(|v| unit.arena.vars().uses(VarId(v))).collect();
        let nodes = unit.arena.nodes.len();
        let mut e = Engine::new(&mut unit.arena);
        let inlining = Round {
            mask: OpMask::PRIM.or(OpMask::LET),
            facts: Facts::Frozen,
            guard: Some(|e, node| e.bir().node(node).op() == Op::Fun),
            ..round(check_snapshots)
        };
        assert_eq!(e.run(&inlining, unit.root), Changed::Yes);
        assert_eq!(e.stats.snapshots, 1);
        // Snapshots are released with the round: counts and slots are back.
        let after: Vec<u32> = (0..4).map(|v| unit.arena.vars().uses(VarId(v))).collect();
        assert_eq!(uses, after);
        assert!(unit.arena.nodes.len() <= nodes + 3);
        unit.arena.validate(Some(unit.root), false).unwrap();
    }

    fn check_frozen(e: &mut Engine<'_>, node: NodeId) -> Changed {
        if let View::Let { var, .. } = e.bir().view(node) {
            // The binding's value was rewritten below: the arena's fact
            // follows, the round's does not.
            assert!(matches!(e.bir().vars().fact(var), Fact::Const(_)));
            assert_eq!(e.fact(var), Fact::Unknown);
            return Changed::No;
        }
        drop_identity(e, node)
    }

    #[test]
    fn a_frozen_round_reads_facts_as_they_were_at_its_start() {
        let mut a = LamArena::new();
        let x = id("x", 1);
        let one = a.const_(C::int(1));
        let value = prim(&mut a, Primitive::Pidentity, &[one]);
        let body = a.var(x);
        let root = a.let_(LetKind::Strict, x, value, body);
        let mut unit = import(&a, root);
        let mut e = Engine::new(&mut unit.arena);
        let frozen = Round {
            mask: OpMask::PRIM.or(OpMask::LET),
            facts: Facts::Frozen,
            ..round(check_frozen)
        };
        assert_eq!(e.run(&frozen, unit.root), Changed::Yes);
        unit.arena.validate(Some(unit.root), false).unwrap();
    }

    #[test]
    fn an_unused_binding_stays_until_deaths_resume() {
        // let x = 1 in (x; ()): drop the use; the binding keeps its value.
        let mut a = LamArena::new();
        let x = id("x", 1);
        let one = a.const_(C::int(1));
        let use_ = a.var(x);
        let unit_ = a.unit();
        let body = a.seq_raw(use_, unit_);
        let root = a.let_(LetKind::Strict, x, one, body);
        let mut unit = import(&a, root);
        let View::Let { var, body, .. } = unit.arena.view(unit.root) else {
            panic!()
        };
        let View::Seq { second, .. } = unit.arena.view(body) else {
            panic!()
        };
        let mut e = Engine::new(&mut unit.arena);
        e.promote(body, second);
        assert_eq!(e.bir().vars().uses(var), 0);
        assert!(matches!(
            e.bir().view(unit.root),
            View::Let { value: Some(_), .. }
        ));
        e.resume_deaths();
        assert!(matches!(
            e.bir().view(unit.root),
            View::Let { value: None, .. }
        ));
        unit.arena.validate(Some(unit.root), false).unwrap();
    }
}
