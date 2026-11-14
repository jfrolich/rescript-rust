//! R3 skeleton: unification on the new graph. Bodies are built by slices
//! R3a, R3c and R3e to R3h (CHECKER_REWRITE.md, "R3 as designed"); every
//! signature, size and stated cost here is fixed.
//!
//! The order of work is OCaml's (compiler/ml/ctype.ml:2227-2440): a link is
//! written before the children are unified, in the direction OCaml writes
//! it. Recursion is an explicit stack of [`Frame`]s, popped in the order the
//! recursive calls would run.

use super::expand::{Memo, TypeTable};
use super::graph::{CONSTR, GENERIC, Graph, Mode, NONE, Node, Speculation, Ty, VAR};
use super::rows::Extras;
use super::segment::{EXTENDED, ExtraDescriptor};

/// Flag of a binding-walk stack entry reached through an object or a
/// variant row: `occur_rec` does not enter those (compiler/ml/ctype.ml:1403)
/// and `update_level` does, so below them the walk only lowers. Local
/// handles stay below bit 30 (`Graph::push`).
const LEVEL_ONLY: u32 = 1 << 30;

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
    /// The children of the node `left` were all unified: nothing to undo.
    /// In `Mode::Explain`, `extra` indexes [`Checker::saved`], the
    /// descriptor to put back into `left` if a later frame above this one
    /// fails (`t1'.desc <- d1`, compiler/ml/ctype.ml:2437).
    Linked,
    /// Leave the universal-variable scope `extra` (R3g).
    LeavePoly,
    /// After the children: the `create_recursion` repair of
    /// compiler/ml/ctype.ml:2428-2436 for the pair (R3c).
    Recursion,
}

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
        let base = self.frames.len();
        self.depth += 1;
        self.frames.push(Frame {
            left,
            right,
            kind: FrameKind::Pair,
            extra: 0,
        });
        let result = self.run_frames(base);
        self.depth -= 1;
        if result.is_err() {
            self.frames.truncate(base);
            if top && self.g.speculation_depth == 0 {
                self.unexplained_failure = true;
            }
        }
        result.map_err(|_| Clash)
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
        // bound (ctype.ml:2242-2243). A variable in a constructor goes to
        // the binding walk, whose expansion retry (R3c) stands for the
        // `deep_occur` cases of ctype.ml:2240-2241.
        if l.tag() == VAR {
            return self.bind(left, right);
        }
        if r.tag() == VAR {
            return self.bind(right, left);
        }
        // Two universal variables (ctype.ml:2244) are extended nodes: R3g.
        // Two locally abstract types (ctype.ml:2258) need equations: R3h.
        if l.tag() == CONSTR
            && r.tag() == CONSTR
            && l.a == r.a
            && l.arity() == 0
            && r.arity() == 0
            && !self.has_cached_expansion(left)
            && !self.has_cached_expansion(right)
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
        let before = self.g.nodes[var.0 as usize];
        let target_is_var = self.g.nodes[ty.0 as usize].tag() == VAR;
        // Of two variables, `link_type` picks the surviving name by the
        // levels before `update_level` (compiler/ml/btype.ml:727,
        // ctype.ml:2221-2222): link first, then lower the one node. A
        // variable cannot hold another, so the occurrence walk is skipped.
        if !target_is_var {
            self.binding_walk(var, ty)?;
        }
        self.g.link(var, ty);
        if (target_is_var || self.types.scoped != 0)
            && let Err(clash) = self.lower_to(ty, before.level)
        {
            // `t1.desc <- d1` (ctype.ml:2224).
            self.g.write(var, before);
            return Err(clash);
        }
        Ok(())
    }

    /// The walk a binding makes over `ty`: every node reachable without
    /// crossing an object or a variant row is visited once (marks), tested
    /// against `var` (`occur_rec`, compiler/ml/ctype.ml:1384), tested for a
    /// free universal variable (`occur_univar`, ctype.ml:1563; R3g fills the
    /// test), and lowered to the variable's level when above it. At most 2
    /// steps a node. The occurrence test has no level cut: a node below the
    /// variable's level can hold the variable (ctype.ml:2217 has none).
    /// A constructor node that holds the variable is expanded before the
    /// walk gives up (ctype.ml:1396-1402). Explicit stack. (R3a; the
    /// expansion retry R3c)
    pub fn binding_walk(&mut self, var: Ty, ty: Ty) -> Result<(), Clash> {
        let level = self.g.nodes[var.0 as usize].level;
        // With scoped types the level update is `bind`'s Checker::lower.
        let lower = self.types.scoped == 0;
        let generation = self.fresh_marks();
        self.g.work.clear();
        self.g.work.push(ty);
        while let Some(entry) = self.g.work.pop() {
            let ty = self.g.repr(Ty(entry.0 & !LEVEL_ONLY));
            let node = self.g.nodes[ty.0 as usize];
            let above = lower && node.level > level;
            if entry.0 & LEVEL_ONLY != 0 {
                if above {
                    #[cfg(test)]
                    super::steps::tick();
                    self.g.write(ty, Node { level, ..node });
                    self.push_level_only(node);
                }
                continue;
            }
            if self.marks[ty.0 as usize] == generation {
                continue;
            }
            #[cfg(test)]
            super::steps::tick();
            if ty == var {
                self.g.work.clear();
                return Err(Clash);
            }
            self.marks[ty.0 as usize] = generation;
            if above {
                self.g.write(ty, Node { level, ..node });
            }
            if self.stops_occurrence(node) {
                if above {
                    self.push_level_only(node);
                }
            } else {
                self.g.children(node, false);
            }
        }
        Ok(())
    }

    /// `occur` of one structure node in another (compiler/ml/ctype.ml:1488),
    /// run before a structure pair is linked (ctype.ml:2330): a walk of
    /// `ty`, one step a node, giving up on nothing. This is one walk per
    /// structure pair, as in OCaml; see "R3 as designed", decision 6. (R3a)
    pub fn occur(&mut self, node: Ty, ty: Ty) -> Result<(), Clash> {
        if self.reaches(node, ty, false) {
            Err(Clash)
        } else {
            Ok(())
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
        todo!("R3a")
    }

    /// Push the child pairs of two structure nodes of the same shape, last
    /// child first: arrows with equal parameter counts and compatible labels
    /// (compiler/ml/ctype.ml:2335-2347), tuples of equal length, constructors
    /// of one type (ctype.ml:2348-2351, expression mode). Anything else is a
    /// clash or belongs to R3e-R3h. O(children). (R3a)
    pub fn push_children(&mut self, left: Node, right: Node) -> Result<(), Clash> {
        todo!("R3a")
    }

    /// `Btype.undo_compress` (compiler/ml/btype.ml:792): walk the trail back
    /// to the speculation's mark and put back only the entries that
    /// rewrote one link into another, then close the speculation without
    /// restoring anything else. O(writes since the mark). (R3a)
    pub fn undo_compress(&mut self, token: Speculation) {
        todo!("R3a")
    }

    /// Restore a speculation and run the cleanup OCaml's `backtrack` runs
    /// (compiler/ml/btype.ml:773-781). O(writes since the mark) plus
    /// [`Checker::cleanup_abbrev`]. (R3b)
    pub fn restore(&mut self, token: Speculation) {
        todo!("R3b")
    }

    /// `unify_var` (compiler/ml/ctype.ml:2752-2771): unify a variable that
    /// must stay a variable-free binding of expansion, with the trace of
    /// `Mode::Explain`. O(1) plus [`Checker::bind`] or [`Checker::unify`].
    /// (R3c)
    pub fn unify_var(&mut self, var: Ty, ty: Ty) -> Result<(), Clash> {
        todo!("R3c")
    }

    /// `unify_gadt` (compiler/ml/ctype.ml:2739-2750): one unification in
    /// pattern mode with equations, at `newtype_level`; clears the pair set
    /// before and after. (R3h)
    pub fn unify_gadt(&mut self, newtype_level: u32, left: Ty, right: Ty) -> Result<(), Clash> {
        todo!("R3h")
    }

    /// O(1) frame pops each plus the callee: the loop of
    /// [`Checker::unify_distinct`] over the frames above `base`. A pair whose
    /// two sides are one node is skipped (`unify_eq`, ctype.ml:2233). On a
    /// clash returns the failing pair, as it stood, and leaves the frames.
    fn run_frames(&mut self, base: usize) -> Result<(), [Ty; 2]> {
        while self.frames.len() > base {
            let Some(frame) = self.frames.pop() else { break };
            match frame.kind {
                FrameKind::Pair => {
                    let left = self.g.repr(frame.left);
                    let right = self.g.repr(frame.right);
                    if left != right && self.unify_pair(left, right).is_err() {
                        return Err([left, right]);
                    }
                }
                FrameKind::Linked => self.saved.truncate(frame.extra as usize),
                FrameKind::LeavePoly => todo!("R3g"),
                FrameKind::Recursion => todo!("R3c"),
            }
        }
        Ok(())
    }

    /// O(1) when no nullary memo row is live; otherwise one
    /// [`Checker::find_expansion`]. Whether a nullary constructor node has a
    /// memorized expansion, public or private (`has_cached_expansion`,
    /// compiler/ml/ctype.ml:2251).
    #[inline]
    fn has_cached_expansion(&self, ty: Ty) -> bool {
        self.memo.live != 0 && self.find_expansion(ty, true).0 != NONE
    }

    /// `update_level` of `ty` to `level`: [`Graph::lower`] when no type has a
    /// scope (what [`Checker::lower`] reduces to then), else
    /// [`Checker::lower`]. O(1) for the generic level, which nothing is
    /// above; otherwise the callee's cost.
    #[inline]
    fn lower_to(&mut self, ty: Ty, level: u32) -> Result<(), Clash> {
        if level == GENERIC {
            return Ok(());
        }
        if self.types.scoped == 0 {
            self.g.lower(ty, level);
            Ok(())
        } else {
            self.lower(ty, level)
        }
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

    /// O(arity): push the children of `node` on the walk's stack, flagged
    /// [`LEVEL_ONLY`].
    fn push_level_only(&mut self, node: Node) {
        let start = self.g.work.len();
        self.g.children(node, false);
        for entry in &mut self.g.work[start..] {
            entry.0 |= LEVEL_ONLY;
        }
    }

    /// Amortized O(1): a fresh generation of `marks`, which grows to the
    /// graph's length; a wrap of the counter clears the marks once.
    fn fresh_marks(&mut self) -> u32 {
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
