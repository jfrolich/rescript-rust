//! R3 skeleton: unification on the new graph. Bodies are built by slices
//! R3a, R3c and R3e to R3h (CHECKER_REWRITE.md, "R3 as designed"); every
//! signature, size and stated cost here is fixed.
//!
//! The order of work is OCaml's (compiler/ml/ctype.ml:2227-2440): a link is
//! written before the children are unified, in the direction OCaml writes
//! it. Recursion is an explicit stack of [`Frame`]s, popped in the order the
//! recursive calls would run.

use super::expand::{ExpandMode, Memo, TypeTable, link_node};
use super::graph::{
    ARROW, CONSTR, Change, GENERIC, Graph, LINK, Mode, NONE, Node, Speculation, TUPLE, Ty, VAR,
};
use super::rows::Extras;
use super::segment::{EXTENDED, ExtraDescriptor};

/// The three kinds of a binding-walk stack entry, in the two bits above a
/// local handle (local handles stay below bit 30, `Graph::push`):
/// - [`LOWERS`]: occurrence test, and lowering allowed. The root, and the
///   children of a node this walk lowered: `update_level` reaches them
///   (compiler/ml/ctype.ml:586).
/// - no flag: occurrence test only. The children of a node that was not
///   lowered: `update_level` does not look below it.
/// - [`LEVEL_ONLY`]: lowering only. Below an object or a variant row, which
///   `occur_rec` does not enter (ctype.ml:1403) and `update_level` does,
///   and below a node lowered after it was already tested.
const LEVEL_ONLY: u32 = 1 << 30;
/// See [`LEVEL_ONLY`].
const LOWERS: u32 = 1 << 31;

/// A failed unification. It carries nothing: in `Mode::Explain` the trace is
/// [`Checker::trace`]; in `Mode::Success` there is none.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Clash;

/// `umode` (compiler/ml/ctype.ml:252).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum UnifyMode {
    Expression,
    Pattern,
}

/// What a [`Frame`] asks for when it is popped.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum FrameKind {
    /// Unify `left` with `right`.
    Pair,
    /// The children of a linked structure pair were all unified: nothing to
    /// undo. `Mode::Explain` only. `left` and `right` are the pair of the
    /// enclosing `unify` call, before expansion and in its order: the trace
    /// entry (compiler/ml/ctype.ml:2272). `extra` indexes
    /// [`Checker::saved`]: the descriptor `d1` to put back if a later frame
    /// above this one fails (`t1'.desc <- d1`, ctype.ml:2437), then a link
    /// node naming the expanded head `t1'` it goes back into; bit 31 of
    /// `extra` (`SWAPPED`) says unify2 chose the right side
    /// (ctype.ml:2299-2303), whose trace entries come out swapped.
    Linked,
    /// Leave the universal-variable scope `extra` (R3g).
    LeavePoly,
    /// After the children: the `create_recursion` repair of
    /// compiler/ml/ctype.ml:2428-2436 for the pair (R3c).
    Recursion,
}

/// Bit 31 of a [`FrameKind::Linked`] frame's `extra`: `unify2` ran `unify3`
/// on the swapped pair (compiler/ml/ctype.ml:2301-2303), so every trace entry
/// made below the frame is reversed.
const SWAPPED: u32 = 1 << 31;

/// One entry of the explicit stack: 16 bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct Frame {
    pub left: Ty,
    pub right: Ty,
    pub kind: FrameKind,
    pub extra: u32,
}

/// The pairs assumed equal in pattern mode (`unify_eq_set`,
/// compiler/ml/ctype.ml:2102-2214). Keys are ordered pairs of node indices.
/// It is a hash set because no dense index of pairs exists; it is read and
/// written in `UnifyMode::Pattern` only.
#[derive(Default)]
pub struct PairSet {
    pub keys: crate::fast_hash::AHashSet<u64>,
}

/// One checker context: the graph and everything unification reads.
/// A worker owns one and resets it between units.
pub struct Checker {
    pub g: Graph,
    pub types: TypeTable,
    pub memo: Memo,
    pub extras: Extras,
    pub umode: UnifyMode,
    /// `generate_equations` and `assume_injective`
    /// (compiler/ml/ctype.ml:253).
    pub generate_equations: bool,
    pub assume_injective: bool,
    /// Set by a top-level unification that failed in `Mode::Success` outside
    /// a speculation: the unit must be checked again in `Mode::Explain`
    /// (`note_unexplained_unify_failure`, types/context.rs).
    pub unexplained_failure: bool,
    /// Depth of [`Checker::unify`] calls in progress; the top-level one opens
    /// the speculation of `Mode::Explain`.
    pub depth: u32,
    /// The explicit stack of [`Checker::unify`].
    pub frames: Vec<Frame>,
    /// Descriptors to restore on failure, `Mode::Explain` only.
    pub saved: Vec<Node>,
    /// The failing pairs, outermost first, `Mode::Explain` only
    /// (`Unify trace`, compiler/ml/ctype.ml:2272).
    pub trace: Vec<[Ty; 2]>,
    /// Visit marks of the binding walk, indexed by node; a mark is set when
    /// it equals `mark_generation`.
    pub marks: Vec<u32>,
    pub mark_generation: u32,
    pub pairs: PairSet,
    /// `univar_pairs` (compiler/ml/ctype.ml:1681), innermost last (R3g).
    pub univars: Vec<[Ty; 2]>,
}

impl Checker {
    /// O(1): a context over a graph and its declaration facts, in the
    /// graph's mode. Allocates nothing.
    pub fn new(g: Graph, types: TypeTable) -> Checker {
        Checker {
            g,
            types,
            memo: Memo::default(),
            extras: Extras::default(),
            umode: UnifyMode::Expression,
            generate_equations: false,
            assume_injective: false,
            unexplained_failure: false,
            depth: 0,
            frames: Vec::new(),
            saved: Vec::new(),
            trace: Vec::new(),
            marks: Vec::new(),
            mark_generation: 0,
            pairs: PairSet::default(),
            univars: Vec::new(),
        }
    }

    /// Unify two types. Inline: two `repr` and a compare; one node on both
    /// sides costs nothing more (compiler/ml/ctype.ml:2229-2233). Otherwise
    /// [`Checker::unify_distinct`]. (R3a)
    #[inline]
    pub fn unify(&mut self, left: Ty, right: Ty) -> Result<(), Clash> {
        let left = self.g.repr(left);
        let right = self.g.repr(right);
        if left == right {
            return Ok(());
        }
        self.unify_distinct(left, right)
    }

    /// The outer `unify` (compiler/ml/ctype.ml:2732-2737) and the loop over
    /// the explicit stack. At depth 0 in `Mode::Explain` it opens a
    /// speculation and, on failure, [`Checker::undo_compress`]es it; in
    /// `Mode::Success` it opens none and, on failure outside a speculation,
    /// sets `unexplained_failure`. Cost: O(pairs popped), each pair one
    /// [`Checker::unify_pair`]. (R3a)
    pub fn unify_distinct(&mut self, left: Ty, right: Ty) -> Result<(), Clash> {
        let top = self.depth == 0;
        let explain = self.g.mode == Mode::Explain;
        // `unify_takes_snapshot` (types/context.rs:1609), as decision 5 of
        // "R3 as designed" restricts it: only the explaining mode opens one.
        let token = if top && explain {
            self.trace.clear();
            Some(self.g.speculate())
        } else {
            None
        };
        let base = self.frames.len();
        let saved_base = self.saved.len();
        let trace_base = self.trace.len();
        self.depth += 1;
        self.push_pair(left, right);
        let result = self.run_frames(base);
        self.depth -= 1;
        match result {
            Ok(()) => {
                if let Some(token) = token {
                    self.g.keep(token);
                }
                Ok(())
            }
            Err([left, right]) => {
                if explain {
                    self.explain_failure(base, trace_base, left, right);
                }
                self.frames.truncate(base);
                self.saved.truncate(saved_base);
                match token {
                    Some(token) => self.undo_compress(token),
                    None if top && self.g.speculation_depth == 0 => {
                        self.unexplained_failure = true;
                    }
                    None => {}
                }
                Err(Clash)
            }
        }
    }

    /// One pair of distinct representatives: the first step of `unify`
    /// (compiler/ml/ctype.ml:2239-2268). A variable goes to
    /// [`Checker::bind`]; two nullary constructors of one type with no
    /// memorized expansion are lowered and linked, left to right
    /// (ctype.ml:2248-2257); everything else goes to
    /// [`Checker::unify_expanded`]. O(1) plus the callee. (R3a)
    pub fn unify_pair(&mut self, left: Ty, right: Ty) -> Result<(), Clash> {
        #[cfg(test)]
        super::steps::tick();
        let l = self.g.nodes[left.0 as usize];
        let r = self.g.nodes[right.0 as usize];
        // `Tvar _, _` before `_, Tvar _`: of two variables the left one is
        // bound (ctype.ml:2242-2243). A variable that occurs in a
        // constructor goes to `unify2` with the pair as it is
        // (ctype.ml:2240-2241); the binding walk finds that occurrence.
        if l.tag() == VAR {
            let route = r.tag() == CONSTR;
            return self.bind_routed(left, right, route.then_some([left, right]));
        }
        if r.tag() == VAR {
            let route = l.tag() == CONSTR;
            return self.bind_routed(right, left, route.then_some([left, right]));
        }
        // Two universal variables (ctype.ml:2244) are extended nodes: R3g.
        // Two locally abstract types (ctype.ml:2258) need equations: R3h.
        //
        // `has_cached_expansion p1 !a1` reads the node's own memo
        // (ctype.ml:2251), which `proper_abbrevs` never writes for a
        // nullary constructor: its expansion goes to `simple_abbrevs`
        // (ctype.ml:200-202). Slot 0 of a nullary node stays empty here too
        // (expand.rs), so the test is always false. With GADT instance
        // tracing the node's own memo is used (R3h).
        if l.tag() == CONSTR && r.tag() == CONSTR && l.a == r.a && l.arity() == 0 && r.arity() == 0
        {
            // `update_level !env t1.level t2; link_type t1 t2`.
            self.lower_to(right, l.level)?;
            self.g.link(left, right);
            return Ok(());
        }
        self.unify_expanded(left, right)
    }

    /// `unify1_var` (compiler/ml/ctype.ml:2216-2225): the occurrence check,
    /// the universal-variable check, the link `var -> ty`, then the level
    /// update of `ty` to the variable's level, undone to the variable's
    /// descriptor on a clash. One walk of `ty` ([`Checker::binding_walk`])
    /// when no type has a scope; with scoped types the level update is a
    /// separate [`Checker::lower`]. (R3a)
    pub fn bind(&mut self, var: Ty, ty: Ty) -> Result<(), Clash> {
        self.bind_routed(var, ty, None)
    }

    /// [`Checker::bind`], or, when `route` holds the pair of a variable and
    /// a constructor and the variable occurs in the constructor, `unify2` of
    /// that pair ([`Checker::unify_expanded`]; `deep_occur`,
    /// compiler/ml/ctype.ml:2240-2241). The occurrence found by the binding
    /// walk is the `deep_occur` test: a generated node of R3c has no object
    /// or variant row, below which the two differ (R3e adds the rows). The
    /// cost is [`Checker::bind`]'s, or one walk and the callee.
    fn bind_routed(&mut self, var: Ty, ty: Ty, route: Option<[Ty; 2]>) -> Result<(), Clash> {
        let before = self.g.nodes[var.0 as usize];
        let target_is_var = self.g.nodes[ty.0 as usize].tag() == VAR;
        // Of two variables, `link_type` picks the surviving name by the
        // levels before `update_level` (compiler/ml/btype.ml:727,
        // ctype.ml:2221-2222): link first, then lower the one node. A
        // variable cannot hold another, so the occurrence walk is skipped.
        //
        // Decision 6 of "R3 as designed": in `Mode::Explain`, outside a
        // speculation whose owner restores, a failed binding must leave the
        // levels as they were, because a failed top-level unification there
        // undoes path compression only. So the occurrence check runs before
        // any level is written (`occur`, `link_type`, `update_level`:
        // ctype.ml:2216-2225), in two walks. The speculation this
        // unification opened in `Mode::Explain` is not an owner's.
        let occur_first = self.occur_first();
        if !target_is_var && self.binding_occurrence(var, ty, occur_first, route.is_some())? {
            let [left, right] = route.expect("routed occurrence");
            return self.unify_expanded(left, right);
        }
        self.g.link(var, ty);
        if (target_is_var || occur_first || self.types.scoped != 0)
            && let Err(clash) = self.lower_to(ty, before.level)
        {
            // `t1.desc <- d1` (ctype.ml:2224).
            self.g.write(var, before);
            return Err(clash);
        }
        Ok(())
    }

    /// O(1): whether a binding tests occurrence in a walk of its own before
    /// it writes a level (decision 6 of "R3 as designed"): in
    /// `Mode::Explain` outside a speculation whose owner restores.
    #[inline]
    fn occur_first(&self) -> bool {
        let own = usize::from(self.g.mode == Mode::Explain && self.depth > 0);
        self.g.mode == Mode::Explain && self.g.speculation_depth <= own
    }

    /// The occurrence part of a binding of `var` to `ty` (not a variable):
    /// `Ok(true)` when `routed` and `var` occurs in `ty` (the caller runs
    /// `unify2`), `Ok(false)` when the binding may be linked, a clash when
    /// `var` occurs even after the expansions `occur_rec` makes
    /// (compiler/ml/ctype.ml:1396-1402). With `occur_first`, one
    /// [`Checker::occur`]-style walk that writes nothing; otherwise the
    /// combined [`Checker::binding_walk`] (or its scan alone when `routed`),
    /// which lowers. Cost: one walk of
    /// `ty`; when `var` is found, one [`Checker::occur_expanding`] more.
    fn binding_occurrence(
        &mut self,
        var: Ty,
        ty: Ty,
        occur_first: bool,
        routed: bool,
    ) -> Result<bool, Clash> {
        if !occur_first {
            if routed {
                return Ok(self.binding_scan(var, ty));
            }
            self.binding_walk(var, ty)?;
            return Ok(false);
        }
        if !self.reaches(var, ty, false) {
            return Ok(false);
        }
        if routed {
            return Ok(true);
        }
        self.occur_expanding(var, ty)?;
        Ok(false)
    }

    /// The walk a binding makes over `ty`: every node reachable without
    /// crossing an object or a variant row is visited once (marks), tested
    /// against `var` (`occur_rec`, compiler/ml/ctype.ml:1384), tested for a
    /// free universal variable (`occur_univar`, ctype.ml:1563; R3g fills the
    /// test), and lowered to the variable's level exactly when `update_level`
    /// would lower it: when it is above that level and is the root of the
    /// walk or a child of a node this walk lowered. `update_level` does not
    /// look below a node that is not above the target
    /// (`if ty.level > level`, compiler/ml/ctype.ml:586), so a node above the
    /// target that is reached only through such a node keeps its level. A
    /// node first met on a path that does not lower and met again on one
    /// that does is lowered at the second meeting. At most 2 steps a node.
    /// The occurrence test has no level cut: a node below the variable's
    /// level can hold the variable (ctype.ml:2217 has none). The levels this
    /// walk leaves are those the two walks of `Mode::Explain` leave.
    /// A constructor node that holds the variable is expanded before the
    /// walk gives up (ctype.ml:1396-1402). Explicit stack. (R3a; the
    /// expansion retry R3c)
    pub fn binding_walk(&mut self, var: Ty, ty: Ty) -> Result<(), Clash> {
        if self.binding_scan(var, ty) {
            // The walk went on to the end, so every level `update_level`
            // writes is written; what is left is `occur_rec`'s retry.
            return self.occur_expanding(var, ty);
        }
        Ok(())
    }

    /// The walk of [`Checker::binding_walk`] without the expansion retry:
    /// whether `var` was reached. It does not stop at `var`: it lowers
    /// everything `update_level` lowers either way, so that a retry that
    /// finds no occurrence leaves the levels of a successful binding. At
    /// most 2 steps a node, explicit stack, marks.
    fn binding_scan(&mut self, var: Ty, ty: Ty) -> bool {
        let level = self.g.nodes[var.0 as usize].level;
        // With scoped types the level update is `bind`'s Checker::lower.
        let lower = self.types.scoped == 0;
        let generation = self.fresh_marks();
        self.g.work.clear();
        self.g.work.push(Ty(ty.0 | LOWERS));
        let mut found = false;
        while let Some(entry) = self.g.work.pop() {
            let ty = self.g.repr(Ty(entry.0 & !(LEVEL_ONLY | LOWERS)));
            let node = self.g.nodes[ty.0 as usize];
            let above = lower && node.level > level;
            let marked = self.marks[ty.0 as usize] == generation;
            // A level-only entry, or a lowering entry on a node already
            // tested on a path that did not lower it: lower only, pruning
            // at a node that is not above, as `update_level` does.
            if entry.0 & LEVEL_ONLY != 0 || (marked && entry.0 & LOWERS != 0) {
                if above {
                    #[cfg(test)]
                    super::steps::tick();
                    self.g.write(ty, Node { level, ..node });
                    self.push_flagged(node, LEVEL_ONLY);
                }
                continue;
            }
            if marked {
                continue;
            }
            #[cfg(test)]
            super::steps::tick();
            self.marks[ty.0 as usize] = generation;
            if ty == var {
                // A variable has no child and is not above its own level.
                found = true;
                continue;
            }
            let lowered = above && entry.0 & LOWERS != 0;
            if lowered {
                self.g.write(ty, Node { level, ..node });
            }
            if self.stops_occurrence(node) {
                if lowered {
                    self.push_flagged(node, LEVEL_ONLY);
                }
            } else {
                self.push_flagged(node, if lowered { LOWERS } else { 0 });
            }
        }
        found
    }

    /// `occur` of one structure node in another (compiler/ml/ctype.ml:1488),
    /// run before a structure pair is linked (ctype.ml:2330): a walk of
    /// `ty`, one step a node, giving up on nothing. This is one walk per
    /// structure pair, as in OCaml; see "R3 as designed", decision 6. (R3a)
    pub fn occur(&mut self, node: Ty, ty: Ty) -> Result<(), Clash> {
        if self.reaches(node, ty, false) {
            // `occur_cannot_fail` could not decide (ctype.ml:1496-1499):
            // `occur_full`, whose `occur_rec` expands before it gives up.
            self.occur_expanding(node, ty)
        } else {
            Ok(())
        }
    }

    /// `occur_rec` (compiler/ml/ctype.ml:1384-1408) in expression mode, run
    /// once [`Checker::reaches`] found `node` in `ty`: a clash when `node`
    /// occurs. A constructor one of whose arguments holds `node` is expanded
    /// (`try_expand_head try_expand_once`, [`ExpandMode::Unif`]) and the
    /// expansion is tested in its place; a constructor that does not expand
    /// holds it. Children are tested in `iter_type_expr`'s order and a node
    /// stops at its first child that holds `node`, so the expansions made
    /// are OCaml's. Each node is decided once (marks: free, holding, on the
    /// path; OCaml re-walks a shared node and finds the same answer, the
    /// expansions it would make again being memorized). An object or a
    /// variant row is not entered (ctype.ml:1403). A node met again on the
    /// path (a cycle, which expression mode does not build) holds `node`
    /// when it is a constructor and not otherwise, as `visited` decides.
    /// Cost: one step and one frame per node, plus one
    /// [`Checker::expand_head`] per constructor that holds `node`, on
    /// [`Checker::frames`] above the length it finds.
    fn occur_expanding(&mut self, node: Ty, ty: Ty) -> Result<(), Clash> {
        let free = self.fresh_marks();
        let holds = self.fresh_marks();
        let busy = self.fresh_marks();
        let base = self.frames.len();
        let mut result = self.occur_visit(node, ty, [free, holds, busy]);
        let outcome = loop {
            if self.frames.len() == base {
                break result;
            }
            let top = self.frames.len() - 1;
            let frame = self.frames[top];
            let parent = frame.left;
            match result.take() {
                // The expansion of `parent` decided it.
                Some(holds_node) if frame.right.0 != NONE => {
                    result = Some(self.occur_finish(parent, holds_node, [free, holds]));
                }
                Some(false) => {}
                Some(true) => {
                    let descriptor = self.g.nodes[parent.0 as usize];
                    if descriptor.tag() != CONSTR {
                        result = Some(self.occur_finish(parent, true, [free, holds]));
                        continue;
                    }
                    let expansion = match self.expand_head(parent, ExpandMode::Unif) {
                        Ok(expansion) => self.g.repr(expansion),
                        Err(Clash) => {
                            self.frames.truncate(base);
                            return Err(Clash);
                        }
                    };
                    if expansion == parent {
                        // `Cannot_expand`: the constructor holds it.
                        result = Some(self.occur_finish(parent, true, [free, holds]));
                        continue;
                    }
                    self.frames[top].right = expansion;
                    result = self.occur_visit(node, expansion, [free, holds, busy]);
                }
                None => {
                    let descriptor = self.g.nodes[parent.0 as usize];
                    let index = frame.extra;
                    match self.child(descriptor, index) {
                        Some(child) => {
                            self.frames[top].extra = index + 1;
                            result = self.occur_visit(node, child, [free, holds, busy]);
                        }
                        None => {
                            result = Some(self.occur_finish(parent, false, [free, holds]));
                        }
                    }
                }
            }
        };
        self.frames.truncate(base);
        if outcome == Some(true) {
            Err(Clash)
        } else {
            Ok(())
        }
    }

    /// O(1): one node of [`Checker::occur_expanding`]: decided at once
    /// (`node` itself, a node already decided or on the path, a node with no
    /// child, an object or a variant row), or pushed as a frame whose `extra`
    /// is the next child and whose `right` is the expansion it waits for.
    /// The marks grow, amortized, to nodes an expansion made.
    fn occur_visit(&mut self, node: Ty, ty: Ty, [free, holds, busy]: [u32; 3]) -> Option<bool> {
        #[cfg(test)]
        super::steps::tick();
        let ty = self.g.repr(ty);
        if ty == node {
            return Some(true);
        }
        let descriptor = self.g.nodes[ty.0 as usize];
        // An expansion made during the walk adds nodes past the marks.
        if ty.0 as usize >= self.marks.len() {
            self.marks.resize(self.g.nodes.len(), 0);
        }
        let mark = self.marks[ty.0 as usize];
        if mark == free {
            return Some(false);
        }
        if mark == holds {
            return Some(true);
        }
        if mark == busy {
            return Some(descriptor.tag() == CONSTR);
        }
        if self.stops_occurrence(descriptor) || self.child(descriptor, 0).is_none() {
            self.marks[ty.0 as usize] = free;
            return Some(false);
        }
        self.marks[ty.0 as usize] = busy;
        self.frames.push(Frame {
            left: ty,
            right: Ty(NONE),
            kind: FrameKind::Pair,
            extra: 0,
        });
        None
    }

    /// O(1): pop the frame of `ty` in [`Checker::occur_expanding`], record
    /// whether it holds the node, and return that.
    fn occur_finish(&mut self, ty: Ty, holds_node: bool, [free, holds]: [u32; 2]) -> bool {
        self.frames.pop();
        self.marks[ty.0 as usize] = if holds_node { holds } else { free };
        holds_node
    }

    /// O(1): child `index` of a representative descriptor in
    /// `iter_type_expr`'s order (compiler/ml/btype.ml:250-257: an arrow's
    /// parameters, then its result), or `None` past the last.
    #[inline]
    fn child(&self, node: Node, index: u32) -> Option<Ty> {
        let arity = node.arity();
        match node.tag() {
            ARROW if index < arity => Some(self.g.params[(node.b + index) as usize].ty),
            ARROW if index == arity => Some(Ty(node.a)),
            CONSTR if index < arity => Some(self.g.lists[(node.b + 1 + index) as usize]),
            TUPLE if index < arity => Some(self.g.lists[(node.b + index) as usize]),
            _ => None,
        }
    }

    /// `deep_occur` (compiler/ml/ctype.ml:1775): whether `node` is reachable
    /// from `ty`, crossing rows and objects too. O(nodes of `ty`), marks,
    /// explicit stack. (R3a)
    pub fn deep_occur(&mut self, node: Ty, ty: Ty) -> bool {
        self.reaches(node, ty, true)
    }

    /// `unify2` and `unify3` (compiler/ml/ctype.ml:2276-2438): expand both
    /// heads ([`super::expand::ExpandMode::Unif`]), lower both originals to
    /// the lower of the two expanded levels, pick the side to link by
    /// ctype.ml:2299, then: a variable head is linked to the *original*
    /// other side; otherwise the expanded head `left'` is linked to the
    /// original `right` and the children of the two expanded descriptors are
    /// pushed. In R3a the expansion is absent (both heads are their own
    /// expansion); R3c adds it. O(1) plus one [`Checker::occur`], two
    /// [`Checker::lower`] and one push per child. (R3a, R3c)
    pub fn unify_expanded(&mut self, left: Ty, right: Ty) -> Result<(), Clash> {
        // `ignore (expand_head_unif !env t1); ignore (expand_head_unif !env
        // t2)`, then both again: an expansion may change the representative
        // of the other side (ctype.ml:2278-2283). When neither side expanded
        // the second pair would read the same graph and return the same
        // nodes, so it is made only after an expansion.
        let mut expanded_left = self.expand_head(left, ExpandMode::Unif)?;
        let mut expanded_right = self.expand_head(right, ExpandMode::Unif)?;
        if expanded_left != self.g.repr(left) || expanded_right != self.g.repr(right) {
            expanded_left = self.expand_head(left, ExpandMode::Unif)?;
            expanded_right = self.expand_head(right, ExpandMode::Unif)?;
        }
        let level = self.g.nodes[expanded_left.0 as usize]
            .level
            .min(self.g.nodes[expanded_right.0 as usize].level);
        self.lower_to(right, level)?;
        self.lower_to(left, level)?;
        // `unify_eq t1' t2'` (ctype.ml:2286). The heads are taken again as
        // representatives: only a scoped lowering links a node, and then
        // OCaml would read a link's descriptor in unify3.
        let expanded_left = self.g.repr(expanded_left);
        let expanded_right = self.g.repr(expanded_right);
        if expanded_left == expanded_right {
            return Ok(());
        }
        let t1 = self.g.repr(left);
        let t2 = self.g.repr(right);
        // `if unify_eq t1 t1' || not (unify_eq t2 t2') then unify3 env t1
        // t1' t2 t2' else unify3 env t2 t2' t1 t1'` (ctype.ml:2299-2303).
        if t1 == expanded_left || t2 != expanded_right {
            self.unify3(
                [t1, expanded_left, t2, expanded_right],
                [left, right],
                false,
            )
        } else {
            self.unify3([t2, expanded_right, t1, expanded_left], [left, right], true)
        }
    }

    /// `unify3 env t1 t1' t2 t2'` (compiler/ml/ctype.ml:2305-2438) on
    /// `[t1, t1', t2, t2']`, all representatives; `pair` is the pair of the
    /// enclosing `unify`, in its order, and `swapped` says unify2 chose the
    /// right side. A variable head is linked to the *original* other side;
    /// otherwise `occur t1' t2'`, the link `t1' -> t2` before the children,
    /// then the children are pushed. When `t2` was expanded and `t1'` occurs
    /// in it (`create_recursion`, one [`Checker::deep_occur`]), a
    /// [`FrameKind::Recursion`] frame runs the repair after the children.
    /// O(1) plus one [`Checker::occur`], at most one `deep_occur` and one
    /// push per child.
    fn unify3(
        &mut self,
        [t1, t1x, t2, t2x]: [Ty; 4],
        pair: [Ty; 2],
        swapped: bool,
    ) -> Result<(), Clash> {
        let d1 = self.g.nodes[t1x.0 as usize];
        let d2 = self.g.nodes[t2x.0 as usize];
        // `occur_univar` of these two cases is R3g's.
        if d1.tag() == VAR {
            self.occur(t1x, t2)?;
            self.g.link(t1x, t2);
            return Ok(());
        }
        if d2.tag() == VAR {
            self.occur(t2x, t1)?;
            self.g.link(t2x, t1);
            return Ok(());
        }
        // `create_recursion` is computed before anything is linked
        // (ctype.ml:2308); the variable cases above do not read it.
        let create_recursion = t2 != t2x && self.deep_occur(t1x, t2);
        if d1.head & d2.head & EXTENDED != 0 {
            self.extended_pair(d1, d2);
        }
        if self.umode == UnifyMode::Pattern {
            // `add_type_equality` in place of the link (ctype.ml:2329).
            todo!("R3h")
        }
        // `occur !env t1' t2'; link_type t1' t2` (ctype.ml:2330-2331),
        // before the children.
        self.occur(t1x, t2x)?;
        self.g.link(t1x, t2);
        let explain = self.g.mode == Mode::Explain;
        if explain {
            // Popped after the children: the descriptor to put back if
            // one of them fails (`t1'.desc <- d1`, ctype.ml:2437), and the
            // node it goes back into.
            let extra = self.saved.len() as u32;
            self.saved.push(d1);
            self.saved.push(link_node(d1, t1x));
            let [left, right] = pair;
            self.frames.push(Frame {
                left,
                right,
                kind: FrameKind::Linked,
                extra: if swapped { extra | SWAPPED } else { extra },
            });
        }
        if create_recursion {
            self.frames.push(Frame {
                left: t2,
                right: t2x,
                kind: FrameKind::Recursion,
                extra: 0,
            });
        }
        let pushed = self.push_children(d1, d2);
        if pushed.is_err() {
            // `push_children` pushes nothing when it fails.
            if create_recursion {
                self.frames.pop();
            }
            if explain {
                self.frames.pop();
                self.saved.truncate(self.saved.len() - 2);
                self.g.write(t1x, d1);
            }
        }
        pushed
    }

    /// The `create_recursion` repair (compiler/ml/ctype.ml:2428-2436), after
    /// the children of a pair whose right side `t2` was expanded to `t2x`:
    /// when `t2` is still a constructor, forget its memo, expand it again,
    /// and when the new expansion is not closed over `t2`'s arguments link
    /// `t2` to `t2x`. One [`Checker::forget_abbrev`], one
    /// [`Checker::expand_head`] and one walk of the arguments and of the
    /// expansion ([`Checker::closed_over`]).
    fn repair_recursion(&mut self, t2: Ty, t2x: Ty) -> Result<(), Clash> {
        // `match t2.desc with Tconstr ...`: the node as it is, not its
        // representative (`| _ -> ()`, ctype.ml:2436).
        let node = self.g.nodes[t2.0 as usize];
        if node.tag() != CONSTR {
            return Ok(());
        }
        self.forget_abbrev(t2);
        let expansion = self.expand_head(t2, ExpandMode::Unif)?;
        if !self.closed_over(node, expansion) {
            let from = self.g.repr(t2);
            let to = self.g.repr(t2x);
            self.g.link(from, to);
        }
        Ok(())
    }

    /// `closed_parameterized_type tl ty` (compiler/ml/ctype.ml:441-451) for
    /// the arguments of constructor descriptor `constr`: whether every
    /// variable reachable from `ty` is reachable from an argument. One mark
    /// generation: the nodes reachable from the arguments are marked, then
    /// the walk of `ty` stops at a marked node. One step a node, explicit
    /// stack.
    fn closed_over(&mut self, constr: Node, ty: Ty) -> bool {
        let generation = self.fresh_marks();
        self.g.work.clear();
        for index in 0..constr.arity() {
            self.g
                .work
                .push(self.g.lists[(constr.b + 1 + index) as usize]);
        }
        while let Some(ty) = self.g.work.pop() {
            let ty = self.g.repr(ty);
            if self.marks[ty.0 as usize] == generation {
                continue;
            }
            #[cfg(test)]
            super::steps::tick();
            self.marks[ty.0 as usize] = generation;
            let node = self.g.nodes[ty.0 as usize];
            self.g.children(node, false);
        }
        self.g.work.push(ty);
        while let Some(ty) = self.g.work.pop() {
            let ty = self.g.repr(ty);
            if self.marks[ty.0 as usize] == generation {
                continue;
            }
            #[cfg(test)]
            super::steps::tick();
            self.marks[ty.0 as usize] = generation;
            let node = self.g.nodes[ty.0 as usize];
            if node.tag() == VAR {
                self.g.work.clear();
                return false;
            }
            self.g.children(node, false);
        }
        true
    }

    /// Push the child pairs of two structure nodes of the same shape, last
    /// child first: arrows with equal parameter counts and compatible labels
    /// (compiler/ml/ctype.ml:2335-2347), tuples of equal length, constructors
    /// of one type (ctype.ml:2348-2351, expression mode). Anything else is a
    /// clash or belongs to R3e-R3h. O(children). (R3a)
    pub fn push_children(&mut self, left: Node, right: Node) -> Result<(), Clash> {
        if (left.head | right.head) & EXTENDED != 0 {
            // An extended descriptor against another kind of node
            // (`_, _ -> raise (Unify [])`, ctype.ml:2424).
            return Err(Clash);
        }
        let arity = left.arity();
        if arity != right.arity() {
            return Err(Clash);
        }
        match (left.tag(), right.tag()) {
            (ARROW, ARROW) => {
                for i in 0..arity {
                    let l = self.g.params[(left.b + i) as usize].label;
                    let r = self.g.params[(right.b + i) as usize].label;
                    if !self.labels_match(l, r) {
                        return Err(Clash);
                    }
                }
                // The parameters in order, then the result.
                self.push_pair(Ty(left.a), Ty(right.a));
                for i in (0..arity).rev() {
                    let l = self.g.params[(left.b + i) as usize].ty;
                    let r = self.g.params[(right.b + i) as usize].ty;
                    self.push_pair(l, r);
                }
            }
            (TUPLE, TUPLE) => self.push_lists(left.b, right.b, arity),
            // Expression mode (ctype.ml:2350); pattern mode is R3h's.
            (CONSTR, CONSTR) if left.a == right.a => {
                self.push_lists(left.b + 1, right.b + 1, arity)
            }
            _ => return Err(Clash),
        }
        Ok(())
    }

    /// `Btype.undo_compress` (compiler/ml/btype.ml:792): walk the trail back
    /// to the speculation's mark and put back only the entries that
    /// rewrote one link into another, then close the speculation without
    /// restoring anything else. O(writes since the mark). (R3a)
    pub fn undo_compress(&mut self, token: Speculation) {
        // Newest first, as OCaml's `List.iter` over the reversed log. A link
        // is written only on a representative (`Graph::link`), so an entry
        // whose old descriptor is a link was written by path compression;
        // it is put back only while the node is still a link, the
        // `ty.desc == d` test of btype.ml:800 (a link a failure later
        // overwrote with a restored descriptor stays as it is).
        let nested = self.g.speculation_depth > 1;
        for index in (token.mark..self.g.trail.len()).rev() {
            let change = self.g.trail[index];
            let now = self.g.nodes[change.ty.0 as usize];
            if change.before.tag() == LINK && now.tag() == LINK {
                #[cfg(test)]
                super::steps::tick();
                if nested {
                    // An enclosing owner may still restore past this point.
                    self.g.trail.push(Change {
                        ty: change.ty,
                        before: now,
                    });
                }
                self.g.nodes[change.ty.0 as usize] = change.before;
            }
        }
        self.g.keep(token);
    }

    /// Restore a speculation and run the cleanup OCaml's `backtrack` runs
    /// (compiler/ml/btype.ml:773-781). O(writes since the mark) plus
    /// [`Checker::cleanup_abbrev`]. (R3b)
    pub fn restore(&mut self, token: Speculation) {
        let written = self.g.trail.len();
        self.g.restore(token);
        // `backtrack` cleans the memos only when something was logged since
        // the snapshot (`Change _`, compiler/ml/btype.ml:776-779).
        if self.g.trail.len() != written {
            self.cleanup_abbrev();
        }
    }

    /// `unify_var` (compiler/ml/ctype.ml:2752-2771): unify a variable that
    /// must stay a variable-free binding of expansion, with the trace of
    /// `Mode::Explain`. O(1) plus [`Checker::bind`] or [`Checker::unify`].
    /// (R3c)
    pub fn unify_var(&mut self, var: Ty, ty: Ty) -> Result<(), Clash> {
        let var = self.g.repr(var);
        let ty = self.g.repr(ty);
        if var == ty {
            return Ok(());
        }
        // `| _ -> unify (ref env) t1 t2`.
        if self.g.nodes[var.0 as usize].tag() != VAR {
            return self.unify(var, ty);
        }
        let before = self.g.nodes[var.0 as usize];
        let target = self.g.nodes[ty.0 as usize];
        let occur_first = self.occur_first();
        // `occur env t1 t2; update_level env t1.level t2; link_type t1 t2`:
        // here the level is written before the link, so of two variables the
        // name is chosen by the levels after it (btype.ml:727).
        let mut result = Ok(());
        if target.tag() != VAR {
            match self.binding_occurrence(var, ty, occur_first, target.tag() == CONSTR) {
                // `Tvar _, Tconstr _ when deep_occur t1 t2 -> unify (ref env)
                // t1 t2` (ctype.ml:2755).
                Ok(true) => return self.unify(var, ty),
                Ok(false) => {}
                Err(clash) => result = Err(clash),
            }
        }
        if result.is_ok() && (target.tag() == VAR || occur_first || self.types.scoped != 0) {
            result = self.lower_to(ty, before.level);
        }
        if result.is_ok() {
            self.g.link(var, ty);
            return Ok(());
        }
        // `raise (Unify ((t1, t2) :: trace))` (ctype.ml:2766-2768): the
        // failure of a unification that is not nested in another.
        if self.depth == 0 {
            if self.g.mode == Mode::Explain {
                self.trace.clear();
                self.trace.push([var, ty]);
            } else if self.g.speculation_depth == 0 {
                self.unexplained_failure = true;
            }
        }
        result
    }

    /// `unify_gadt` (compiler/ml/ctype.ml:2739-2750): one unification in
    /// pattern mode with equations, at `newtype_level`; clears the pair set
    /// before and after. (R3h)
    pub fn unify_gadt(&mut self, newtype_level: u32, left: Ty, right: Ty) -> Result<(), Clash> {
        todo!("R3h")
    }

    /// The failure path of the explaining mode: the trace, outermost pair
    /// first (each enclosing `unify` adds its pair, ctype.ml:2272), and the
    /// descriptors of the linked structure nodes enclosing the failure put
    /// back, innermost first (`t1'.desc <- d1`, ctype.ml:2437). The
    /// enclosing pairs are the `Linked` frames above `base`; the entries a
    /// nested unification already wrote stay after this one's. O(frames
    /// above `base` + trace entries since `trace_base`).
    /// Below a swapped `unify3` every entry is reversed
    /// (`List.map (fun (x, y) -> (y, x))`, ctype.ml:2303), twice swapped is
    /// as made. A clash of a recursion repair has no pair of its own (`NONE`).
    #[cold]
    fn explain_failure(&mut self, base: usize, trace_base: usize, left: Ty, right: Ty) {
        let inner = self.trace.len() - trace_base;
        let mut swapped = false;
        for index in base..self.frames.len() {
            let frame = self.frames[index];
            if frame.kind == FrameKind::Linked {
                let entry = [frame.left, frame.right];
                self.trace
                    .push(if swapped { [entry[1], entry[0]] } else { entry });
                swapped ^= frame.extra & SWAPPED != 0;
            }
        }
        if left.0 != NONE {
            self.trace.push(if swapped {
                [right, left]
            } else {
                [left, right]
            });
        }
        self.trace[trace_base..].rotate_left(inner);
        for index in (base..self.frames.len()).rev() {
            let frame = self.frames[index];
            if frame.kind == FrameKind::Linked {
                let slot = (frame.extra & !SWAPPED) as usize;
                let descriptor = self.saved[slot];
                let target = Ty(self.saved[slot + 1].a);
                self.g.write(target, descriptor);
            }
        }
    }

    /// O(1): push one pair.
    #[inline]
    fn push_pair(&mut self, left: Ty, right: Ty) {
        self.frames.push(Frame {
            left,
            right,
            kind: FrameKind::Pair,
            extra: 0,
        });
    }

    /// O(len): push the pairs of two list ranges, last first.
    fn push_lists(&mut self, left: u32, right: u32, len: u32) {
        for i in (0..len).rev() {
            let l = self.g.lists[(left + i) as usize];
            let r = self.g.lists[(right + i) as usize];
            self.push_pair(l, r);
        }
    }

    /// O(1): `Asttypes.same_arg_label`, or in pattern mode any two labels
    /// that are not optional (compiler/ml/ctype.ml:2338-2342). A label is
    /// an interned name with the low bit set when optional, or `NONE`.
    #[inline]
    fn labels_match(&self, left: u32, right: u32) -> bool {
        let optional = |label: u32| label != NONE && label & 1 != 0;
        left == right || (self.umode == UnifyMode::Pattern && !optional(left) && !optional(right))
    }

    /// Two extended descriptors of one kind: the cases of unify3 that the
    /// row slices build (compiler/ml/ctype.ml:2316-2328, 2400-2421). Two of
    /// different kinds fall through to the clash of `push_children`. O(1).
    fn extended_pair(&self, left: Node, right: Node) {
        let kind = |node: Node| std::mem::discriminant(&self.extras.descriptors[node.a as usize]);
        if kind(left) != kind(right) {
            return;
        }
        match self.extras.descriptors[left.a as usize] {
            ExtraDescriptor::Object | ExtraDescriptor::Field { .. } | ExtraDescriptor::Nil => {
                todo!("R3e")
            }
            ExtraDescriptor::Variant(_) => todo!("R3f"),
            ExtraDescriptor::Univar(_) | ExtraDescriptor::Poly | ExtraDescriptor::Package(_) => {
                todo!("R3g")
            }
            ExtraDescriptor::Substitution => unreachable!("Tsubst outside a copy"),
        }
    }

    /// O(1) frame pops each plus the callee: the loop of
    /// [`Checker::unify_distinct`] over the frames above `base`. A pair whose
    /// two sides are one node is skipped (`unify_eq`, ctype.ml:2233). On a
    /// clash returns the failing pair, as it stood, and leaves the frames.
    fn run_frames(&mut self, base: usize) -> Result<(), [Ty; 2]> {
        while self.frames.len() > base {
            let Some(frame) = self.frames.pop() else {
                break;
            };
            match frame.kind {
                FrameKind::Pair => {
                    let left = self.g.repr(frame.left);
                    let right = self.g.repr(frame.right);
                    if left != right && self.unify_pair(left, right).is_err() {
                        return Err([left, right]);
                    }
                }
                FrameKind::Linked => self.saved.truncate((frame.extra & !SWAPPED) as usize),
                FrameKind::LeavePoly => todo!("R3g"),
                FrameKind::Recursion => {
                    // A clash here is the enclosing pair's: it adds no
                    // pair of its own to the trace (`Unify []`).
                    if self.repair_recursion(frame.left, frame.right).is_err() {
                        return Err([Ty(NONE), Ty(NONE)]);
                    }
                }
            }
        }
        Ok(())
    }

    /// `update_level` of `ty` to `level`: [`Checker::lower`]. O(1) for the
    /// generic level, which nothing is above; otherwise the callee's cost.
    #[inline]
    fn lower_to(&mut self, ty: Ty, level: u32) -> Result<(), Clash> {
        if level == GENERIC {
            return Ok(());
        }
        self.lower(ty, level)
    }

    /// O(1): an object or a polymorphic variant row, which `occur_rec`
    /// does not enter (compiler/ml/ctype.ml:1403).
    #[inline]
    fn stops_occurrence(&self, node: Node) -> bool {
        node.head & EXTENDED != 0
            && matches!(
                self.extras.descriptors[node.a as usize],
                ExtraDescriptor::Object | ExtraDescriptor::Variant(_)
            )
    }

    /// O(arity): push the children of `node` on the walk's stack, each
    /// entry carrying `flag` ([`LEVEL_ONLY`], [`LOWERS`] or none).
    ///
    /// The flags use bits 30 and 31 of a handle. Bit 31 is reserved for a
    /// frozen node (CHECKER_REWRITE 3.2), which no local graph holds yet:
    /// the slice that puts frozen handles into child lists must keep them
    /// off this stack (a frozen node holds no local variable and has no
    /// level to lower) or widen the entry. The assertion pins that.
    fn push_flagged(&mut self, node: Node, flag: u32) {
        let start = self.g.work.len();
        self.g.children(node, false);
        debug_assert!(
            self.g.work[start..]
                .iter()
                .all(|entry| entry.0 & (LEVEL_ONLY | LOWERS) == 0),
            "a handle with bit 30 or 31 set on the binding walk's stack"
        );
        if flag != 0 {
            for entry in &mut self.g.work[start..] {
                entry.0 |= flag;
            }
        }
    }

    /// Amortized O(1): a fresh generation of `marks`, which grows to the
    /// graph's length; a wrap of the counter clears the marks once.
    pub(super) fn fresh_marks(&mut self) -> u32 {
        if self.marks.len() < self.g.nodes.len() {
            self.marks.resize(self.g.nodes.len(), 0);
        }
        if self.mark_generation == u32::MAX {
            self.marks.fill(0);
            self.mark_generation = 0;
        }
        self.mark_generation += 1;
        self.mark_generation
    }

    /// Whether `node` is reachable from `ty`: one step a node, each node
    /// once (marks), explicit stack. With `deep` objects and variant rows
    /// are crossed (`deep_occur`, ctype.ml:1775), otherwise not
    /// (`occur_rec`, ctype.ml:1403). No level cut.
    fn reaches(&mut self, node: Ty, ty: Ty, deep: bool) -> bool {
        let generation = self.fresh_marks();
        self.g.work.clear();
        self.g.work.push(ty);
        while let Some(ty) = self.g.work.pop() {
            let ty = self.g.repr(ty);
            if self.marks[ty.0 as usize] == generation {
                continue;
            }
            #[cfg(test)]
            super::steps::tick();
            if ty == node {
                self.g.work.clear();
                return true;
            }
            self.marks[ty.0 as usize] = generation;
            let descriptor = self.g.nodes[ty.0 as usize];
            if deep || !self.stops_occurrence(descriptor) {
                self.g.children(descriptor, false);
            }
        }
        false
    }

    /// O(1): the checking mode, fixed for the unit (CHECKER_REWRITE 3.4).
    #[inline]
    pub fn mode(&self) -> Mode {
        self.g.mode
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sizes() {
        assert_eq!(std::mem::size_of::<Clash>(), 0);
        assert_eq!(std::mem::size_of::<Result<(), Clash>>(), 1);
        assert_eq!(std::mem::size_of::<UnifyMode>(), 1);
        assert_eq!(std::mem::size_of::<Frame>(), 16);
        assert_eq!(std::mem::size_of::<FrameKind>(), 4);
    }
}
