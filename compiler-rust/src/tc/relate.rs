//! R3 skeleton: the relations that do not unify for good: `moregeneral`,
//! `equal`, `matches` (slice R3i) and subtyping (slice R3j). See
//! CHECKER_REWRITE.md, "R3 as designed", section 8.12.
//!
//! `moregen` and `eqtype` are one loop over [`Checker::frames`]
//! (`Checker::relate_frames`) with a [`Relation`] passed down: the
//! frames are the ones unification has ([`FrameKind::Pair`],
//! [`FrameKind::LeavePoly`], [`FrameKind::PackageEnd`],
//! [`FrameKind::Field`], [`FrameKind::RowField`]), so that
//! [`Checker::enter_poly`], [`Checker::unify_univar`],
//! [`Checker::unify_package`] and [`Checker::push_children`] are called
//! as they are. No relation keeps a trace: every caller reads a boolean
//! (compiler/ml/includecore.ml:47, 92; typedecl.ml:815; typecore.ml:879).

use std::cmp::Ordering;

use super::expand::ExpandMode;
use super::graph::{ARROW, CONSTR, GENERIC, LINK, NONE, Node, Ty, VAR};
use super::rows::{RES_ABSENT, RES_PRESENT, cell_mutable, cell_repr, each_field_types, either_flags, field_repr};
use super::segment::{EXTENDED, ExtraDescriptor, RowFieldKind, VariantRow};
use super::unify::{Checker, Clash, Frame, FrameKind};

/// One delayed constraint of subtyping (`(trace, t1, t2,
/// !(current_univar_pairs ()), None) :: cstrs`,
/// compiler/ml/ctype.ml:3655): 16 bytes. (Changed in the eleventh
/// skeleton turn from 12 bytes with a trace length: CHECKER_REWRITE 8.6,
/// decision 120.)
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct Constraint {
    pub left: Ty,
    pub right: Ty,
    /// The trace of the pair the constraint was made at: an index of
    /// [`Coercion::links`], or `NONE` in `Mode::Success`.
    pub trace: u32,
    /// The scopes of universal variables open where it was made: an
    /// index of [`Coercion::scopes`], or `NONE`.
    pub scopes: u32,
}

/// Which relation `Checker::relate_frames` decides for a pair: 2 bytes,
/// passed down the walk by value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Relation {
    /// `moregen inst_nongen` (compiler/ml/ctype.ml:2925-2991).
    Moregen { inst_nongen: bool },
    /// `eqtype rename` (compiler/ml/ctype.ml:3200-3274).
    Equal { rename: bool },
}

/// One row of [`Checker::renaming`], indexed by a node: 12 bytes. The
/// substitution of `eqtype` (`subst`, a list of pairs searched with
/// `List.assq` and `List.exists`, compiler/ml/ctype.ml:3209-3215) as a
/// dense table: `partner` is what the node is renamed to when `left` is
/// the live generation; `right` is the live generation when some node is
/// renamed to this one.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
#[repr(C)]
pub struct Renamed {
    pub left: u32,
    pub partner: u32,
    pub right: u32,
}

/// `may_instantiate inst_nongen t1` (compiler/ml/ctype.ml:2921-2923):
///
/// ```text
/// let may_instantiate inst_nongen t1 =
///   if inst_nongen then t1.level <> generic_level - 1
///   else t1.level = generic_level
/// ```
///
/// O(1).
#[inline]
pub fn may_instantiate(inst_nongen: bool, level: u32) -> bool {
    if inst_nongen { level != GENERIC - 1 } else { level == GENERIC }
}

/// O(1): the ordered key of a pair in [`Checker::related`]
/// (`Type_pairs` hashes and compares the pair as it is given,
/// compiler/ml/ctype.ml:2941, 3225).
#[inline]
fn ordered(left: Ty, right: Ty) -> u64 {
    u64::from(left.0) << 32 | u64::from(right.0)
}

impl Checker {
    /// `moregeneral env inst_nongen pat_sch subj_sch`
    /// (compiler/ml/ctype.ml:3104-3124): whether the scheme `pattern` is at
    /// least as general as the scheme `subject`, both nodes of the graph.
    ///
    /// 1. The level is saved. At level `GENERIC - 1`: [`Checker::copy`] of
    ///    `subject` (`instance env subj_sch`), then
    ///    [`Checker::duplicate_type`] of that copy.
    /// 2. At level `GENERIC`: [`Checker::copy`] of `pattern`.
    /// 3. [`Checker::moregen`] of the two; the level is put back.
    ///
    /// NO speculation: OCaml takes no snapshot here (ctype.ml:3104-3124
    /// has none), and with `inst_nongen` the links `moregen` writes into
    /// the nodes of `pattern` that are not generic are the caller's to
    /// keep (a weak variable of an implementation is instantiated by its
    /// interface, includecore.ml:47). Everything else it writes is in the
    /// two copies, which nothing holds afterwards; the memo of
    /// constructors without arguments keeps what the expansions put there
    /// until the next cleanup, as in OCaml (CHECKER_REWRITE 8.6, decision
    /// 114). Cost: two copies of the subject and one of the pattern, then
    /// the walk. (R3i)
    pub fn moregeneral(&mut self, inst_nongen: bool, pattern: Ty, subject: Ty) -> bool {
        let level = std::mem::replace(&mut self.g.level, GENERIC - 1);
        let subject = self.copy(subject);
        let subject = self.duplicate_type(subject);
        self.g.level = GENERIC;
        let pattern = self.copy(pattern);
        let result = self.moregen(inst_nongen, pattern, subject);
        self.g.level = level;
        result
    }

    /// `duplicate_type ty` (compiler/ml/ctype.ml:496, `Subst.type_expr
    /// Subst.identity`): a copy of every node of `ty` that is not a
    /// variable, at the generic level, around the variables themselves.
    ///
    /// ```text
    /// (* compiler/ml/subst.ml:132-143, typexp_rec *)
    ///   match ty.desc with
    ///   | (Tvar _ | Tunivar _) as desc ->
    ///     if s.for_saving || ty.id < 0 then (...)
    ///     else ty
    /// (* compiler/ml/subst.ml:191-207, the row variable of a variant *)
    ///             let dup =
    ///               s.for_saving || more.level = generic_level || static_row row
    ///               || match more.desc with Tconstr _ -> true | _ -> false
    ///             ...
    ///               | Tunivar _ | Tvar _ ->
    ///                 save_desc more more.desc;
    ///                 if s.for_saving then newpersty (norm more.desc)
    ///                 else if dup && is_Tvar more then newgenty more.desc
    ///                 else more
    /// ```
    ///
    /// NOT [`Checker::duplicate`], which copies variables too (the
    /// destination of an equation has none; 8.9, decision 67). The same
    /// three passes: under a speculation, one generation of
    /// [`Checker::marks`] (held across `Graph::children`,
    /// [`Checker::row_children`] and `Graph::write` only) and a walk that
    /// writes generic the level of every node that is not a variable or
    /// a universal variable, and of the row variable of a static row
    /// (`dup`: a new generic variable; the inner nodes of a chain of
    /// variant nodes are walked in line with the node that leads to
    /// them, so that `static_row` is asked of a whole row); `Graph::copy` at the generic
    /// level, which shares what is not generic: the variables, and with
    /// a row variable the references of its row (`copy_row ... (not
    /// dup)`), followed by the pass of [`Checker::copy`] over the new
    /// nodes for the cells of fields (`Checker::dup_cell`) and the
    /// references of rows ([`Checker::copy_refs`]) but WITHOUT its
    /// lookup of the memo: `Subst` makes a constructor node with an
    /// empty memo and asks no memo (`Tconstr (type_path s p, List.map
    /// (typexp s) tl, ref Mnil)`, subst.ml:172), so a copy of a
    /// constructor without arguments is a new node and never a link to
    /// a memorized one. `Graph::restore`, which puts the levels of `ty`
    /// back, runs BETWEEN the copy and that pass: the pass opens a
    /// source row whose row variable the copy shares, so that the two
    /// have one reference a `Reither` field (`let e = if keep then e
    /// else ref None`, btype.ml:374), and that opening must outlive the
    /// function (corrected in the tenth turn: with the restore last, the
    /// source was unopened again and `set_row_field e1 (Reither (c2,
    /// [], m2, e2))` of `moregen_row_field` wrote a reference the
    /// subject did not hold; 8.6, decision 117). The pass reads handles
    /// (`first`), not levels. The
    /// caller, `moregeneral`, passes a type none of whose nodes is
    /// generic (an instance made at `GENERIC - 1`). Cost: one step a
    /// node visited and one trail entry a level written, one step a node
    /// copied, one step a level restored. (R3i)
    fn duplicate_type(&mut self, ty: Ty) -> Ty {
        let token = self.g.speculate();
        let generation = self.fresh_marks();
        let base = self.g.work.len();
        self.g.work.push(ty);
        while self.g.work.len() > base {
            let Some(next) = self.g.work.pop() else {
                break;
            };
            let next = self.g.repr(next);
            let mark = &mut self.marks[next.0 as usize];
            if *mark == generation {
                continue;
            }
            *mark = generation;
            #[cfg(test)]
            super::steps::tick();
            let node = self.g.nodes[next.0 as usize];
            // `Tvar _ | Tunivar _ -> ty` (subst.ml:135-143): shared, and an
            // unresolved reference is a variable too.
            if node.tag() == VAR || self.is_univar(next) {
                continue;
            }
            if node.level != GENERIC {
                self.g.write(next, Node { level: GENERIC, ..node });
            }
            if self.is_variant(node) {
                let (static_row, home, _, more) = self.row_children(next, node);
                // The inner nodes of the chain, in line: an inner node is
                // not a row of its own (`row_repr`), so `static_row` is
                // never asked of it alone.
                let (mut at, mut current) = (next, node);
                while at != home {
                    let ExtraDescriptor::Variant(index) = self.extras.descriptors[current.a as usize] else {
                        unreachable!("a variant node");
                    };
                    let slot = current.b + self.extras.variants[index as usize].more;
                    at = self.g.repr(self.g.lists[slot as usize]);
                    current = self.g.nodes[at.0 as usize];
                    self.marks[at.0 as usize] = generation;
                    if current.level != GENERIC {
                        self.g.write(at, Node { level: GENERIC, ..current });
                    }
                    self.g.children(current, true);
                }
                // `dup && is_Tvar more` (subst.ml:191-203): the row
                // variable of a static row is copied.
                let rest = self.g.nodes[more.0 as usize];
                if static_row && rest.tag() == VAR {
                    self.marks[more.0 as usize] = generation;
                    if rest.level != GENERIC {
                        self.g.write(more, Node { level: GENERIC, ..rest });
                    }
                }
            }
            self.g.children(node, true);
        }
        let level = std::mem::replace(&mut self.g.level, GENERIC);
        let first = self.g.nodes.len();
        let copy = self.g.copy(ty);
        self.g.level = level;
        // The levels go back BEFORE the pass: `copy_refs` opens a source
        // row whose row variable the copy shares, and that must stay
        // (decision 117).
        self.g.restore(token);
        if !self.extras.descriptors.is_empty() {
            // The pass of `Checker::copy` without its lookup of the memo.
            self.extras.copying = true;
            let end = self.g.nodes.len();
            self.begin_cell_session();
            for index in first..end {
                #[cfg(test)]
                super::steps::tick();
                let node = self.g.nodes[index];
                if node.head & EXTENDED == 0 {
                    continue;
                }
                match self.extras.descriptors[node.a as usize] {
                    ExtraDescriptor::Field { .. } => self.dup_cell(Ty(index as u32), node, first as u32),
                    ExtraDescriptor::Variant(_) => self.copy_refs(Ty(index as u32), node, first as u32),
                    _ => {}
                }
            }
            self.end_cell_session();
            self.extras.copying = false;
        }
        copy
    }

    /// The outer `moregen` (compiler/ml/ctype.ml:3091-3094: `Must empty
    /// univar_pairs first`) with the pair table of `moregeneral`
    /// (`Type_pairs.create 13`, ctype.ml:3119) and its `try ... with Unify
    /// _ -> false`: whether the instance `pattern` can be instantiated to
    /// `subject`, linking the variables [`may_instantiate`] allows. For a
    /// caller that made the two instances itself (from two templates).
    /// The scopes of universal variables are EMPTIED first
    /// ([`Checker::empty_scopes`]: `current_univar_pairs () := []`,
    /// ctype.ml:3089) and nothing puts them back when the relation
    /// returns: a relation the inclusion check of two packages runs
    /// inside a polymorphic type leaves the rest of that type without
    /// scopes, as OCaml does (CHECKER_REWRITE 8.6, decision 127). The
    /// relation has a table of pairs of its own
    /// ([`Checker::enter_relation`], decision 128), cleared; the pair
    /// goes on [`Checker::frames`] and [`Checker::relate_frames`] runs;
    /// on a failure the frames, `saved`, the scopes entered inside
    /// (with the floor the lowest of them found) and the trace are cut
    /// back to what they were at the entry. What
    /// was linked stays, on either answer. Cost: O(pairs visited), each
    /// one [`Checker::moregen_pair`]; one hash insertion a pair that is
    /// not decided at its first test. (R3i)
    pub fn moregen(&mut self, inst_nongen: bool, pattern: Ty, subject: Ty) -> bool {
        self.empty_scopes();
        self.enter_relation();
        self.related.keys.clear();
        let base = self.frames.len();
        self.push_pair(pattern, subject);
        let result = self.relate_run(Relation::Moregen { inst_nongen }, base);
        self.leave_relation();
        result
    }

    /// `equal env rename tyl1 tyl2` (compiler/ml/ctype.ml:3372-3376) with
    /// the outer `eqtype_list` (3361-3369): structural equality of two
    /// lists of types, up to a bijective renaming of variables when
    /// `rename`.
    ///
    /// ```text
    /// let eqtype_list rename type_pairs subst env tl1 tl2 =
    ///   current_univar_pairs () := [];
    ///   let snap = Btype.snapshot () in
    ///   try
    ///     eqtype_list rename type_pairs subst env tl1 tl2;
    ///     backtrack snap
    ///   with exn ->
    ///     backtrack snap;
    ///     raise exn
    /// ```
    ///
    /// Lists of different lengths: `false`, nothing opened
    /// (`if List.length tl1 <> List.length tl2 then raise (Unify [])`,
    /// ctype.ml:3277, inside the snapshot, which then has nothing to
    /// undo). The scopes of universal variables are emptied at the entry,
    /// before that test ([`Checker::empty_scopes`]; OCaml at
    /// ctype.ml:3358), and stay emptied when `equal` returns
    /// (CHECKER_REWRITE 8.6, decision 127).
    /// Otherwise one speculation, a table of pairs of its own
    /// ([`Checker::enter_relation`], left after the restore), cleared,
    /// with `rename` a new generation of [`Checker::renaming`], the pairs
    /// pushed last first, [`Checker::relate_frames`], and
    /// [`Checker::restore`] on either answer: nothing `equal` wrote stays
    /// (an expansion, a compressed path, an opened row), and the memos
    /// are cleaned when something was written, as `backtrack` cleans
    /// them. Cost: O(pairs visited), each one [`Checker::eqtype_pair`],
    /// one hash insertion a pair not decided at its first test, plus the
    /// restore (one step a write). (R3i)
    pub fn equal(&mut self, rename: bool, left: &[Ty], right: &[Ty]) -> bool {
        self.empty_scopes();
        if left.len() != right.len() {
            return false;
        }
        let token = self.g.speculate();
        self.enter_relation();
        self.related.keys.clear();
        if rename {
            self.renamed.clear();
            self.renaming_trail = self.g.trail.len();
            self.next_renaming_generation();
        }
        let base = self.frames.len();
        for (&l, &r) in left.iter().zip(right).rev() {
            self.push_pair(l, r);
        }
        let result = self.relate_run(Relation::Equal { rename }, base);
        self.restore(token);
        self.leave_relation();
        result
    }

    /// `matches env ty ty'` (compiler/ml/ctype.ml:3167-3179): whether `ty`
    /// unifies with `pattern` without instantiating a variable of `ty`.
    ///
    /// ```text
    /// let matches env ty ty' =
    ///   let snap = snapshot () in
    ///   let vars = rigidify ty in
    ///   cleanup_abbrev ();
    ///   let ok =
    ///     try
    ///       unify env ty ty';
    ///       all_distinct_vars env vars
    ///     with Unify _ -> false
    ///   in
    ///   backtrack snap;
    ///   ok
    /// ```
    ///
    /// One speculation opened BEFORE [`Checker::rigidify`] (it links row
    /// variables), [`Checker::cleanup_abbrev`], the scopes of universal
    /// variables emptied ([`Checker::empty_scopes`]: the `unify` this
    /// function calls in OCaml is the typer's, which starts with
    /// `univar_pairs := []`, compiler/ml/ctype.ml:2770 by 2773),
    /// [`Checker::unify`],
    /// [`Checker::all_distinct_vars`], the trace cut back to its length
    /// at the entry, [`Checker::restore`] on either answer. The
    /// unification runs inside the speculation, so a failure in
    /// `Mode::Success` does not set `unexplained_failure`. Cost: the
    /// walk of `ty`, one unification, one expansion a variable, the
    /// restore. (R3i)
    pub fn matches(&mut self, ty: Ty, pattern: Ty) -> bool {
        let token = self.g.speculate();
        let trace = self.trace.len();
        self.rigid_vars.clear();
        self.rigidify(ty);
        self.cleanup_abbrev();
        self.empty_scopes();
        let result = self.unify(ty, pattern).is_ok() && self.all_distinct_vars();
        self.rigid_vars.clear();
        self.trace.truncate(trace);
        self.restore(token);
        result
    }

    /// Run [`Checker::relate_frames`] above `base` and, on a clash, cut
    /// [`Checker::frames`] back to `base`. On either answer `saved`, the
    /// scopes of universal variables (`univar_pairs := old_univars`,
    /// compiler/ml/ctype.ml:1677-1679) and the trace (a callee that
    /// clashed in `Mode::Explain` pushed its pair; 8.6, decision 25) go
    /// back to their lengths at the entry. O(1) plus the walk. (R3i)
    fn relate_run(&mut self, relation: Relation, base: usize) -> bool {
        let (saved, scopes, trace) = (self.saved.len(), self.scopes.len(), self.trace.len());
        let result = self.relate_frames(relation, base).is_ok();
        if !result && self.scopes.len() != scopes {
            // `univar_pairs := old_univars; raise exn` (ctype.ml:
            // 1677-1679): the floor of the lowest scope entered too.
            self.leave_scopes(base);
        }
        self.frames.truncate(base);
        self.saved.truncate(saved);
        self.scopes.truncate(scopes);
        self.trace.truncate(trace);
        result
    }

    /// The loop of `moregen` and `eqtype`: pop the frames above `base`
    /// until none is left or one clashes (the frames then stay; the
    /// caller cuts them).
    ///
    /// - A [`FrameKind::Pair`] frame: the two representatives; nothing when they
    ///   are one node (`if t1 == t2 then ()`, compiler/ml/ctype.ml:2926,
    ///   2930, 3201, 3205), otherwise [`Checker::moregen_pair`] or
    ///   [`Checker::eqtype_pair`].
    /// - A [`FrameKind::LeavePoly`] frame: [`Checker::leave_poly`]: `scopes` is
    ///   cut to the frame's `extra` and the floor is the frame's `left`
    ///   (`univar_pairs := old_univars`, ctype.ml:1675).
    /// - A [`FrameKind::PackageEnd`] frame: [`Checker::package_end`]; a clash is
    ///   the relation's (`with Not_found -> raise (Unify [])`,
    ///   ctype.ml:2974, 3257).
    /// - A [`FrameKind::Field`] frame: [`Checker::relate_field`].
    /// - A [`FrameKind::RowField`] frame: [`Checker::moregen_row_field`]
    ///   (`eqtype` pushes none).
    ///
    /// One step a frame popped. No recursion: a type 10,000 deep costs
    /// 16 bytes of frame a level. (R3i)
    fn relate_frames(&mut self, relation: Relation, base: usize) -> Result<(), Clash> {
        while self.frames.len() > base {
            let Some(frame) = self.frames.pop() else {
                break;
            };
            #[cfg(test)]
            super::steps::tick();
            match frame.kind {
                FrameKind::Pair => {
                    let (left, right) = (self.g.repr(frame.left), self.g.repr(frame.right));
                    if left == right {
                        continue;
                    }
                    match relation {
                        Relation::Moregen { inst_nongen } => self.moregen_pair(inst_nongen, left, right)?,
                        Relation::Equal { rename } => self.eqtype_pair(rename, left, right)?,
                    }
                }
                FrameKind::LeavePoly => self.leave_poly(frame),
                FrameKind::PackageEnd => self.package_end(frame)?,
                FrameKind::Field => self.relate_field(frame)?,
                FrameKind::RowField => {
                    debug_assert!(matches!(relation, Relation::Moregen { .. }), "eqtype pushes no row field");
                    self.moregen_row_field(frame)?
                }
                _ => unreachable!("a frame of unification in a relation"),
            }
        }
        Ok(())
    }

    /// One pair of `moregen` (compiler/ml/ctype.ml:2925-2991), `t1` and
    /// `t2` two distinct representatives, in OCaml's order of tests:
    ///
    /// 1. `Tvar _, _ when may_instantiate inst_nongen t1` (2934-2937):
    ///    [`Checker::moregen_occur`]`(t1.level, t2)`, [`Checker::occur`]
    ///    `(t1, t2)`, `Graph::link(t1, t2)`.
    /// 2. Two constructors without arguments of one type (2938): nothing.
    /// 3. Both heads expanded in [`ExpandMode::Safe`] (`expand_head`,
    ///    2940-2941), their representatives `t1x`, `t2x`; one node:
    ///    nothing. The ordered pair looked up in [`Checker::related`]:
    ///    found, nothing; otherwise added (2946-2948).
    /// 4. `Tvar _, _ when may_instantiate inst_nongen t1'` (2950-2952):
    ///    `moregen_occur(t1x.level, t2)` with the UNEXPANDED `t2`, then
    ///    `Graph::link(t1x, t2)`; no `occur`.
    /// 5. [`Checker::relate_children`].
    ///
    /// O(1) plus the callees; one hash lookup and at most one insertion.
    /// (R3i)
    fn moregen_pair(&mut self, inst_nongen: bool, t1: Ty, t2: Ty) -> Result<(), Clash> {
        let (l, r) = (self.g.nodes[t1.0 as usize], self.g.nodes[t2.0 as usize]);
        if l.tag() == VAR && may_instantiate(inst_nongen, l.level) {
            self.moregen_occur(l.level, t2)?;
            self.occur(t1, t2)?;
            self.g.link(t1, t2);
            return Ok(());
        }
        if l.tag() == CONSTR && r.tag() == CONSTR && l.arity() == 0 && r.arity() == 0 && l.a == r.a {
            return Ok(());
        }
        let t1x = self.expand_head(t1, ExpandMode::Safe)?;
        let t2x = self.expand_head(t2, ExpandMode::Safe)?;
        let (t1x, t2x) = (self.g.repr(t1x), self.g.repr(t2x));
        if t1x == t2x || !self.related.keys.insert(ordered(t1x, t2x)) {
            return Ok(());
        }
        let (l, r) = (self.g.nodes[t1x.0 as usize], self.g.nodes[t2x.0 as usize]);
        if l.tag() == VAR && may_instantiate(inst_nongen, l.level) {
            self.moregen_occur(l.level, t2)?;
            self.g.link(t1x, t2);
            return Ok(());
        }
        self.relate_children(Relation::Moregen { inst_nongen }, [t1x, t2x], l, r)
    }

    /// One pair of `eqtype` (compiler/ml/ctype.ml:3200-3274), `t1` and
    /// `t2` two distinct representatives:
    ///
    /// 1. `Tvar _, Tvar _ when rename` (3209-3215):
    ///    [`Checker::rename_pair`].
    /// 2. Two constructors without arguments of one type (3216): nothing.
    /// 3. Both heads expanded in [`ExpandMode::Rigid`]
    ///    (`expand_head_rigid`, 3218-3219); one node: nothing; the
    ///    ordered pair found in [`Checker::related`]: nothing; otherwise
    ///    added (3224-3226).
    /// 4. `Tvar _, Tvar _ when rename` of the two heads (3228-3236):
    ///    [`Checker::rename_pair`].
    /// 5. [`Checker::relate_children`]; two variables without `rename`
    ///    clash there (`_, _ -> raise (Unify [])`, 3273).
    ///
    /// O(1) plus the callees; one hash lookup and at most one insertion.
    /// (R3i)
    fn eqtype_pair(&mut self, rename: bool, t1: Ty, t2: Ty) -> Result<(), Clash> {
        let (l, r) = (self.g.nodes[t1.0 as usize], self.g.nodes[t2.0 as usize]);
        if rename && l.tag() == VAR && r.tag() == VAR {
            return self.rename_pair(t1, t2);
        }
        if l.tag() == CONSTR && r.tag() == CONSTR && l.arity() == 0 && r.arity() == 0 && l.a == r.a {
            return Ok(());
        }
        let t1x = self.expand_head(t1, ExpandMode::Rigid)?;
        let t2x = self.expand_head(t2, ExpandMode::Rigid)?;
        let (t1x, t2x) = (self.g.repr(t1x), self.g.repr(t2x));
        if t1x == t2x || !self.related.keys.insert(ordered(t1x, t2x)) {
            return Ok(());
        }
        let (l, r) = (self.g.nodes[t1x.0 as usize], self.g.nodes[t2x.0 as usize]);
        if rename && l.tag() == VAR && r.tag() == VAR {
            return self.rename_pair(t1x, t2x);
        }
        self.relate_children(Relation::Equal { rename }, [t1x, t2x], l, r)
    }

    /// The structure arms the two relations share
    /// (compiler/ml/ctype.ml:2953-2990 and 3236-3273), for two expanded
    /// heads `t1x`, `t2x` with descriptors `l` and `r`:
    ///
    /// - neither extended: [`Checker::push_children`] (two arrows of one
    ///   arity whose labels are the same, two tuples, two constructors of
    ///   one type; anything else, a variable included, clashes);
    /// - one extended: a clash;
    /// - two objects: [`Checker::relate_fields`] of their slots 0; two
    ///   fields ("Actually unused"): of the two nodes;
    /// - two `Tnil`: nothing;
    /// - two polymorphic types without variables: the pair of the bodies;
    ///   otherwise [`Checker::enter_poly`];
    /// - two universal variables: [`Checker::unify_univar`];
    /// - two variants: [`Checker::moregen_row`] or
    ///   [`Checker::eqtype_row`];
    /// - two packages: [`Checker::unify_package`], whose pairs this
    ///   relation's loop pops and whose [`FrameKind::PackageEnd`] it
    ///   runs; without a supplier ([`Checker::packages`] is `None`) a
    ///   clash, as in unification.
    ///
    /// O(1) plus the callee; pushes nothing when it fails. (R3i)
    fn relate_children(&mut self, relation: Relation, [t1x, t2x]: [Ty; 2], l: Node, r: Node) -> Result<(), Clash> {
        if (l.head | r.head) & EXTENDED == 0 {
            return self.push_children(l, r);
        }
        if l.head & r.head & EXTENDED == 0 {
            return Err(Clash);
        }
        match (self.extras.descriptors[l.a as usize], self.extras.descriptors[r.a as usize]) {
            (ExtraDescriptor::Object, ExtraDescriptor::Object) => {
                let (fields1, fields2) = (self.g.lists[l.b as usize], self.g.lists[r.b as usize]);
                self.relate_fields(relation, fields1, fields2)
            }
            // "Actually unused" (ctype.ml:2978, 3261).
            (ExtraDescriptor::Field { .. }, ExtraDescriptor::Field { .. }) => self.relate_fields(relation, t1x, t2x),
            (ExtraDescriptor::Nil, ExtraDescriptor::Nil) => Ok(()),
            (ExtraDescriptor::Poly, ExtraDescriptor::Poly) if l.arity() == 1 && r.arity() == 1 => {
                let (body1, body2) = (self.g.lists[l.b as usize], self.g.lists[r.b as usize]);
                self.push_pair(body1, body2);
                Ok(())
            }
            (ExtraDescriptor::Poly, ExtraDescriptor::Poly) => self.enter_poly(l, r),
            (ExtraDescriptor::Univar(_), ExtraDescriptor::Univar(_)) => self.unify_univar(t1x, t2x),
            (ExtraDescriptor::Variant(_), ExtraDescriptor::Variant(_)) => match relation {
                Relation::Moregen { inst_nongen } => self.moregen_row(inst_nongen, [t1x, t2x]),
                Relation::Equal { .. } => self.eqtype_row([t1x, t2x]),
            },
            (ExtraDescriptor::Package(_), ExtraDescriptor::Package(_)) => self.unify_package([t1x, t2x], l, r),
            _ => Err(Clash),
        }
    }

    /// `moregen_occur env level ty` (compiler/ml/ctype.ml:2901-2919):
    ///
    /// ```text
    /// let moregen_occur env level ty =
    ///   let rec occur ty =
    ///     let ty = repr ty in
    ///     if ty.level > level then (
    ///       if is_Tvar ty && ty.level >= generic_level - 1 then raise Occur;
    ///       ty.level <- pivot_level - ty.level;
    ///       match ty.desc with
    ///       | Tvariant row when static_row row -> iter_row occur row
    ///       | _ -> iter_type_expr occur ty)
    ///   in
    ///   (try occur ty; unmark_type ty with Occur -> unmark_type ty; raise (Unify []));
    ///   (* also check for free univars *)
    ///   occur_univar env ty;
    ///   update_level env level ty
    /// ```
    ///
    /// A walk of the nodes of `ty` above `level`, each once: OCaml marks
    /// by negating the level and unmarks after the walk, a mark that
    /// STAYS for the walk (not a list of the path); here one generation
    /// of [`Checker::marks`], taken by this function and held across no
    /// call that takes one (the walk calls `Graph::children` and
    /// [`Checker::row_children`] only). A variable at `GENERIC - 1` or
    /// above is a clash. A variant node's children are what
    /// [`Checker::row_children`] pushes, and its row variable only when
    /// the row is not static. With `level == GENERIC` nothing is above
    /// it and the walk is skipped (one compare). Then
    /// [`Checker::occur_univar`] behind one load of `Extras::univars`,
    /// then [`Checker::lower`] unless `level` is generic. Cost: one step
    /// a node above `level`, explicit stack on `Graph::work` above the
    /// length it finds, no allocation; plus the lowering. (R3i)
    fn moregen_occur(&mut self, level: u32, ty: Ty) -> Result<(), Clash> {
        if level < GENERIC {
            let generation = self.fresh_marks();
            let base = self.g.work.len();
            self.g.work.push(ty);
            while self.g.work.len() > base {
                let Some(next) = self.g.work.pop() else {
                    break;
                };
                let next = self.g.repr(next);
                let node = self.g.nodes[next.0 as usize];
                if node.level <= level {
                    continue;
                }
                let mark = &mut self.marks[next.0 as usize];
                if *mark == generation {
                    continue;
                }
                *mark = generation;
                #[cfg(test)]
                super::steps::tick();
                if node.tag() == VAR && node.level >= GENERIC - 1 {
                    self.g.work.truncate(base);
                    return Err(Clash);
                }
                if self.is_variant(node) {
                    let (static_row, _, _, more) = self.row_children(next, node);
                    if !static_row {
                        self.g.work.push(more);
                    }
                } else {
                    self.g.children(node, false);
                }
            }
        }
        if self.extras.univars != 0 {
            self.occur_univar(ty)?;
        }
        if level != GENERIC {
            self.lower(ty, level)?;
        }
        Ok(())
    }

    /// O(1): whether `node` (a descriptor) is a variant node.
    #[inline]
    fn is_variant(&self, node: Node) -> bool {
        node.head & EXTENDED != 0 && matches!(self.extras.descriptors[node.a as usize], ExtraDescriptor::Variant(_))
    }

    /// O(1): whether `node` (a descriptor) is `Tnil`.
    #[inline]
    fn is_nil(&self, node: Node) -> bool {
        node.head & EXTENDED != 0 && self.extras.descriptors[node.a as usize] == ExtraDescriptor::Nil
    }

    /// O(1): the `VariantRow` of a flattened row (`row_repr`,
    /// compiler/ml/btype.ml:126-135: the flags and the name are the last
    /// node's), from what [`Checker::flatten_row`] returned for `top`:
    /// `last` is that node, or `NONE` for `top` itself. Two loads.
    #[inline]
    fn last_row(&self, last: Ty, top: Node) -> VariantRow {
        let node = if last.0 == NONE { top } else { self.g.nodes[last.0 as usize] };
        let ExtraDescriptor::Variant(row) = self.extras.descriptors[node.a as usize] else {
            unreachable!("a variant node");
        };
        self.extras.variants[row as usize]
    }

    /// Amortized O(1): a new live generation of [`Checker::renaming`],
    /// returned; a wrap of the counter clears the table once.
    fn next_renaming_generation(&mut self) -> u32 {
        if self.renaming_generation == u32::MAX {
            self.renaming.fill(Renamed::default());
            self.renaming_generation = 0;
        }
        self.renaming_generation += 1;
        self.renaming_generation
    }

    /// Amortized O(1): [`Checker::renaming`] has a row for node `index`;
    /// it grows to the graph's length when it has not.
    #[inline]
    fn renaming_covers(&mut self, index: u32) {
        let needed = index as usize + 1;
        if self.renaming.len() < needed {
            self.renaming.resize(self.g.nodes.len().max(needed), Renamed::default());
        }
    }

    /// `iter_row f row` (compiler/ml/btype.ml:229-241) for the variant
    /// node `ty` with descriptor `node`: push on `Graph::work` what
    /// `iter_row` visits: for each field of each node of the chain (the
    /// row and the rows its `more` leads to), a present field's type and
    /// every type of a field that is still `Reither` ([`field_repr`],
    /// [`each_field_types`]: the chain of references is read, never
    /// pushed, so a reference node is not a child); then the arguments
    /// of the name of the LAST row of the chain. They are pushed so that
    /// they are popped in `iter_row`'s order. Returns `static_row row`
    /// (btype.ml:162-170: the last row is closed and no field of the
    /// chain is `Reither`), the last variant node of the chain (`ty`
    /// when the chain is one node), its `VariantRow`, and the
    /// representative of its `more`, which is NOT pushed. Rows are not
    /// opened. O(fields + chain), one step a field, no allocation.
    /// (R3i; the loop is `Checker::reify_row`'s)
    fn row_children(&mut self, ty: Ty, node: Node) -> (bool, Ty, VariantRow, Ty) {
        let start = self.g.work.len();
        let mut work = std::mem::take(&mut self.g.work);
        let (mut home, mut current, mut static_fields) = (ty, node, true);
        let (row, more) = loop {
            let ExtraDescriptor::Variant(index) = self.extras.descriptors[current.a as usize] else {
                unreachable!("a variant node");
            };
            let row = self.extras.variants[index as usize];
            for at in row.fields.start..row.fields.start + row.fields.len {
                #[cfg(test)]
                super::steps::tick();
                let field = self.extras.row_fields[at as usize];
                let read = field_repr(&self.g, current.b, current.arity(), field);
                match read.kind {
                    RowFieldKind::Present if read.first.0 != NONE => work.push(read.first),
                    RowFieldKind::Either { .. } => {
                        static_fields = false;
                        each_field_types(&self.g, current.b, current.arity(), field, |types| {
                            work.extend_from_slice(types)
                        });
                    }
                    _ => {}
                }
            }
            let more = self.g.repr(self.g.lists[(current.b + row.more) as usize]);
            let next = self.g.nodes[more.0 as usize];
            if !self.is_variant(next) {
                break (row, more);
            }
            (home, current) = (more, next);
        };
        if row.name != NONE {
            let from = (current.b + row.name_arguments.start) as usize;
            work.extend_from_slice(&self.g.lists[from..from + row.name_arguments.len as usize]);
        }
        // Popped in `iter_row`'s order.
        work[start..].reverse();
        self.g.work = work;
        (row.closed && static_fields, home, row, more)
    }

    /// `rigidify ty` (compiler/ml/ctype.ml:3130-3154): append to
    /// [`Checker::rigid_vars`] every variable of `ty`, and make every row
    /// that is not fixed and ends in a variable a fixed one.
    ///
    /// ```text
    /// let rec rigidify_rec vars ty =
    ///   let ty = repr ty in
    ///   if ty.level >= lowest_level then (
    ///     ty.level <- pivot_level - ty.level;
    ///     match ty.desc with
    ///     | Tvar _ -> if not (List.memq ty !vars) then vars := ty :: !vars
    ///     | Tvariant row ->
    ///       let row = row_repr row in
    ///       let more = repr row.row_more in
    ///       (if is_Tvar more && not (row_fixed row) then
    ///          let more' = newty2 more.level more.desc in
    ///          let row' =
    ///            {row with row_fixed = true; row_fields = []; row_more = more'}
    ///          in
    ///          link_type more (newty2 ty.level (Tvariant row')));
    ///       iter_row (rigidify_rec vars) row;
    ///       (* only consider the row variable if the variant is not static *)
    ///       if not (static_row row) then rigidify_rec vars (row_more row)
    ///     | _ -> iter_type_expr (rigidify_rec vars) ty)
    /// ```
    ///
    /// Each node once: OCaml marks by negating the level, a mark that
    /// stays until `unmark_type`; here one generation of
    /// [`Checker::marks`], held across no call that takes one (the walk
    /// calls `Graph::children`, [`Checker::row_children`],
    /// `Checker::build_variant`, `Graph::link` and
    /// `Checker::forget_name_children`). The marks grow with the nodes
    /// the walk makes. `List.memq ty !vars` is always false for a node
    /// met for the first time, so the list is not searched.
    ///
    /// A variant node: [`Checker::row_children`]; when the `more` is a
    /// variable and the row is not fixed ([`Checker::row_is_fixed`]), a
    /// new variable `more'` with the descriptor of `more` (its level and
    /// name), a new variant node without fields, fixed, closed as the
    /// row is and with the row's name, at the level of the visited node,
    /// whose `more` is `more'`; `more` is linked to it (logged: the
    /// caller's speculation undoes it) and the name's arguments stop
    /// being children of the row's home (`Checker::forget_name_children`;
    /// 8.6, decision 60, as `Checker::reify_row` does). OCaml's new node
    /// carries the MARKED level of the visited node (`newty2 ty.level`
    /// after `ty.level <- pivot_level - ty.level`), below every level,
    /// and `unmark_type` does not reach it (`iter_row` goes through an
    /// inner row without visiting its node); nothing compares that level
    /// for equality, and the node is gone at the backtrack of `matches`.
    /// Then, unless the row is static, the row variable is visited: the
    /// new `more'` after a link.
    ///
    /// Cost: one step a node, explicit stack on `Graph::work`; a row
    /// made fixed costs two nodes, one `VariantRow` and one descriptor
    /// row. (R3i)
    fn rigidify(&mut self, ty: Ty) {
        let generation = self.fresh_marks();
        let base = self.g.work.len();
        self.g.work.push(ty);
        while self.g.work.len() > base {
            let Some(next) = self.g.work.pop() else {
                break;
            };
            let next = self.g.repr(next);
            // A node the walk made is beyond the marks.
            if self.marks.len() <= next.0 as usize {
                self.marks.resize(self.g.nodes.len(), 0);
            }
            let mark = &mut self.marks[next.0 as usize];
            if *mark == generation {
                continue;
            }
            *mark = generation;
            #[cfg(test)]
            super::steps::tick();
            let node = self.g.nodes[next.0 as usize];
            let start = self.g.work.len();
            if node.tag() == VAR {
                self.rigid_vars.push(next);
            } else if self.is_variant(node) {
                let (static_row, home, row, more) = self.row_children(next, node);
                let variable = self.g.nodes[more.0 as usize];
                let mut rest = more;
                if variable.tag() == VAR && !self.row_is_fixed(row, more) {
                    let fresh = self.g.push(variable);
                    let scratch = self.extras.row_scratch.len();
                    let b = self.g.nodes[home.0 as usize].b;
                    let tail = self.build_variant(scratch..scratch, fresh, row.closed, true, (row, b));
                    // `newty2 ty.level`: a node made now, stored unlogged.
                    self.g.nodes[tail.0 as usize].level = node.level;
                    self.g.link(more, tail);
                    if row.name != NONE && row.name_arguments.len != 0 {
                        self.forget_name_children(home, row);
                    }
                    rest = fresh;
                }
                if !static_row {
                    // `rigidify_rec vars (row_more row)` after `iter_row`:
                    // below the row's children, so popped after them.
                    self.g.work.push(rest);
                    self.g.work[start..].rotate_right(1);
                }
            } else {
                // Popped in `iter_type_expr`'s order (btype.ml:251-271):
                // `Graph::children` pushes an arrow's result first.
                self.g.children(node, false);
                let from = if node.tag() == ARROW { start + 1 } else { start };
                self.g.work[from..].reverse();
            }
        }
    }

    /// `all_distinct_vars env vars` (compiler/ml/ctype.ml:3156-3165) of
    /// [`Checker::rigid_vars`]:
    ///
    /// ```text
    /// let all_distinct_vars env vars =
    ///   let tyl = ref [] in
    ///   List.for_all
    ///     (fun ty ->
    ///       let ty = expand_head env ty in
    ///       if List.memq ty !tyl then false
    ///       else (
    ///         tyl := ty :: !tyl;
    ///         is_Tvar ty))
    ///     vars
    /// ```
    ///
    /// OCaml searches a list a variable: quadratic. Here two passes:
    /// first every entry is replaced by its head ([`Checker::expand_head`]
    /// in [`ExpandMode::Safe`]); then one generation of
    /// [`Checker::marks`] and one scan: a head that is not a variable, or
    /// one that is marked already, is `false`. The answer is OCaml's:
    /// `false` exactly when two entries have one head or a head is not a
    /// variable. OCaml stops expanding at the first `false`; the
    /// expansions made after it are undone with the rest by the restore
    /// of [`Checker::matches`], the one caller. The two passes are apart
    /// so that the generation is held across no expansion (an expansion
    /// of a type with a constrained parameter unifies, and unification
    /// takes generations). Cost: one expansion and two steps a variable.
    /// (R3i)
    fn all_distinct_vars(&mut self) -> bool {
        for at in 0..self.rigid_vars.len() {
            #[cfg(test)]
            super::steps::tick();
            let var = self.rigid_vars[at];
            // A safe expansion turns a clash into no expansion
            // (`try_expand_safe`, ctype.ml:1251-1256); were one to escape,
            // `matches` would answer `false` (`with Unify _ -> false`).
            match self.expand_head(var, ExpandMode::Safe) {
                Ok(head) => self.rigid_vars[at] = head,
                Err(Clash) => return false,
            }
        }
        let generation = self.fresh_marks();
        for at in 0..self.rigid_vars.len() {
            #[cfg(test)]
            super::steps::tick();
            let head = self.rigid_vars[at];
            let mark = &mut self.marks[head.0 as usize];
            if *mark == generation || self.g.nodes[head.0 as usize].tag() != VAR {
                return false;
            }
            *mark = generation;
        }
        true
    }

    /// `Tvar _, Tvar _ when rename` of `eqtype`
    /// (compiler/ml/ctype.ml:3209-3215, 3228-3236), for two variables
    /// that are representatives:
    ///
    /// ```text
    ///           try
    ///             normalize_subst subst;
    ///             if List.assq t1 !subst != t2 then raise (Unify [])
    ///           with Not_found ->
    ///             if List.exists (fun (_, t) -> t == t2) !subst then raise (Unify []);
    ///             subst := (t1, t2) :: !subst)
    /// ```
    ///
    /// [`Checker::normalize_renaming`] first. Then the row of `t1` in
    /// [`Checker::renaming`]: live on the left, `Ok` when its partner is
    /// `t2` and a clash otherwise; not live, a clash when the row of
    /// `t2` is live on the right, else both rows are written and the
    /// pair is appended to [`Checker::renamed`]. The table grows to the
    /// graph's length when a node is beyond it. OCaml's two list
    /// searches are O(variables) a pair; this is O(1): two row loads.
    /// The answer is the same because the table holds exactly the pairs
    /// of the list: a key has one entry (a second `t1` is compared, not
    /// added) and so does a value. The table is not on the trail: the
    /// one reader is this function, inside one `equal`. (R3i)
    fn rename_pair(&mut self, t1: Ty, t2: Ty) -> Result<(), Clash> {
        self.normalize_renaming();
        let generation = self.renaming_generation;
        self.renaming_covers(t1.0.max(t2.0));
        let row = self.renaming[t1.0 as usize];
        if row.left == generation {
            return if row.partner == t2.0 { Ok(()) } else { Err(Clash) };
        }
        if self.renaming[t2.0 as usize].right == generation {
            return Err(Clash);
        }
        let row = &mut self.renaming[t1.0 as usize];
        (row.left, row.partner) = (generation, t2.0);
        self.renaming[t2.0 as usize].right = generation;
        self.renamed.push([t1, t2]);
        Ok(())
    }

    /// `normalize_subst subst` (compiler/ml/ctype.ml:3191-3198):
    ///
    /// ```text
    /// let normalize_subst subst =
    ///   if
    ///     List.exists
    ///       (function
    ///         | {desc = Tlink _}, _ | _, {desc = Tlink _} -> true
    ///         | _ -> false)
    ///       !subst
    ///   then subst := List.map (fun (t1, t2) -> (repr t1, repr t2)) !subst
    /// ```
    ///
    /// A variable of the renaming becomes a link only when an expansion
    /// unifies a constrained parameter with it, and inside `equal` every
    /// write is on the trail: when the trail has the length it had at
    /// the last call, nothing (one compare). Otherwise one scan of
    /// [`Checker::renamed`]; when an entry is a link, a new generation of
    /// the table and every pair written again under its two
    /// representatives, oldest first, so that of two pairs with one key
    /// the newest is found, as `List.assq` finds it. OCaml scans the
    /// list at every pair of variables; this scans it once a pair that
    /// follows a write. (R3i)
    fn normalize_renaming(&mut self) {
        if self.g.trail.len() == self.renaming_trail {
            return;
        }
        self.renaming_trail = self.g.trail.len();
        let mut stale = false;
        for at in 0..self.renamed.len() {
            #[cfg(test)]
            super::steps::tick();
            let [a, b] = self.renamed[at];
            stale |= self.g.nodes[a.0 as usize].head == LINK || self.g.nodes[b.0 as usize].head == LINK;
        }
        if !stale {
            return;
        }
        let generation = self.next_renaming_generation();
        for at in 0..self.renamed.len() {
            let [a, b] = self.renamed[at];
            let (a, b) = (self.g.repr(a), self.g.repr(b));
            self.renamed[at] = [a, b];
            self.renaming_covers(a.0.max(b.0));
            let row = &mut self.renaming[a.0 as usize];
            (row.left, row.partner) = (generation, b.0);
            self.renaming[b.0 as usize].right = generation;
        }
    }

    /// `moregen_fields` (compiler/ml/ctype.ml:2997-3029) and
    /// `eqtype_fields` (3280-3323) of two field lists.
    ///
    /// Both: [`Checker::flatten_fields`] of the two into `Extras::fields`
    /// (taken and put back), `associate_fields` by one merge from the
    /// last names (two indices may spell one name: differing indices
    /// compare their texts once, decision 32), one [`FrameKind::Field`]
    /// frame a common name pushed last name first, so that they are
    /// popped in name order.
    ///
    /// `moregen`: a name only the left has is a clash (`if miss1 <> []
    /// then raise (Unify [])`); the pair of `rest1` and `build_fields
    /// (repr ty2).level miss2 rest2` ([`Checker::build_field`] from the
    /// last name) is pushed above the field frames, so it is popped
    /// first (3002-3003).
    ///
    /// `eqtype`: first `same_row` (3283-3288): `rest1 == rest2`, or the
    /// pair is in [`Checker::related`], or with `rename` the renaming
    /// holds it: nothing. Otherwise `rest2` is expanded in
    /// [`ExpandMode::Rigid`]; an object: the whole call again with its
    /// field list (3292-3293; a loop, not a recursion). Otherwise a name
    /// one side lacks is a clash, and the pair of the two rests is
    /// pushed above the field frames.
    ///
    /// Cost: O(fields) plus the sort of `flatten_fields`; 16 bytes of
    /// frame a common name; one node a field `moregen` builds. (R3i)
    fn relate_fields(&mut self, relation: Relation, ty1: Ty, ty2: Ty) -> Result<(), Clash> {
        let mut ty2 = ty2;
        let mut fields = std::mem::take(&mut self.extras.fields);
        debug_assert!(fields.is_empty());
        let (rest1, n1, rest2) = loop {
            fields.clear();
            let rest1 = self.flatten_fields(ty1, &mut fields);
            let n1 = fields.len();
            let rest2 = self.flatten_fields(ty2, &mut fields);
            let Relation::Equal { rename } = relation else {
                break (rest1, n1, rest2);
            };
            // `same_row` (ctype.ml:3279-3284).
            let renamed = rename
                && self
                    .renaming
                    .get(rest1.0 as usize)
                    .is_some_and(|row| row.left == self.renaming_generation && row.partner == rest2.0);
            if rest1 == rest2 || self.related.keys.contains(&ordered(rest1, rest2)) || renamed {
                fields.clear();
                self.extras.fields = fields;
                return Ok(());
            }
            let Ok(head) = self.expand_head(rest2, ExpandMode::Rigid) else {
                fields.clear();
                self.extras.fields = fields;
                return Err(Clash);
            };
            let node = self.g.nodes[head.0 as usize];
            if node.head & EXTENDED != 0 && self.extras.descriptors[node.a as usize] == ExtraDescriptor::Object {
                ty2 = self.g.lists[node.b as usize];
                continue;
            }
            break (rest1, n1, rest2);
        };
        let frames = self.frames.len();
        let (mut i, mut j) = (n1, fields.len());
        let (mut missing, mut built) = (false, rest2);
        let repr2 = self.g.repr(ty2);
        let level2 = self.g.nodes[repr2.0 as usize].level;
        while i > 0 || j > n1 {
            #[cfg(test)]
            super::steps::tick();
            let order = if i == 0 {
                Ordering::Less
            } else if j == n1 {
                Ordering::Greater
            } else {
                let (f1, f2) = (fields[i - 1], fields[j - 1]);
                if f1.name == f2.name {
                    Ordering::Equal
                } else {
                    let names = &self.extras.names;
                    names.text(f1.name).cmp(names.text(f2.name))
                }
            };
            match order {
                Ordering::Equal => {
                    let (f1, f2) = (fields[i - 1], fields[j - 1]);
                    self.frames.push(Frame { left: Ty(f1.at), right: Ty(f2.at), kind: FrameKind::Field, extra: 0 });
                    i -= 1;
                    j -= 1;
                }
                // A name only the left has: `miss1`.
                Ordering::Greater => {
                    missing = true;
                    i -= 1;
                }
                // A name only the right has: `miss2`, built into the rest
                // by `moregen`, a clash of `eqtype`.
                Ordering::Less => {
                    match relation {
                        Relation::Moregen { .. } => built = self.build_field(level2, Ty(fields[j - 1].at), built),
                        Relation::Equal { .. } => missing = true,
                    }
                    j -= 1;
                }
            }
        }
        fields.clear();
        self.extras.fields = fields;
        if missing {
            self.frames.truncate(frames);
            return Err(Clash);
        }
        self.push_pair(rest1, built);
        Ok(())
    }

    /// The pop of a [`FrameKind::Field`] frame in a relation
    /// (compiler/ml/ctype.ml:3006-3007, 3300-3301): `left` and `right`
    /// are the two field nodes of one name.
    ///
    /// ```text
    ///       if mutability_repr f1.f_mut <> mutability_repr f2.f_mut then
    ///         raise (Unify []);
    ///       try moregen inst_nongen type_pairs env f1.f_typ f2.f_typ
    /// ```
    ///
    /// The two cells are read ([`cell_repr`], [`cell_mutable`]) and
    /// never written or merged: a relation promotes no cell. Then the
    /// pair of the two types is pushed. O(links of the two cells). (R3i)
    fn relate_field(&mut self, frame: Frame) -> Result<(), Clash> {
        let c1 = cell_repr(&self.g, self.cell_of(frame.left));
        let c2 = cell_repr(&self.g, self.cell_of(frame.right));
        if cell_mutable(&self.g, c1) != cell_mutable(&self.g, c2) {
            return Err(Clash);
        }
        let (n1, n2) = (self.g.nodes[frame.left.0 as usize], self.g.nodes[frame.right.0 as usize]);
        let (t1, t2) = (self.g.lists[n1.b as usize], self.g.lists[n2.b as usize]);
        self.push_pair(t1, t2);
        Ok(())
    }

    /// `moregen_row` (compiler/ml/ctype.ml:3031-3089) for the two variant
    /// nodes `t1x`, `t2x`.
    ///
    /// 1. Both nodes are opened ([`Checker::open_row`]) and flattened
    ///    ([`Checker::flatten_row`]) into `Extras::row_scratch`; `rm1 ==
    ///    rm2`: nothing (3034).
    /// 2. `may_inst` (3036-3038): `rm1` is a variable that
    ///    [`may_instantiate`], or `Tnil`.
    /// 3. [`Checker::merge_rows`]. When row 2 is closed,
    ///    `filter_row_fields may_inst r1` and `filter_row_fields false
    ///    r2` (3040-3043; ctype.ml:388-397), each from its last field: an
    ///    absent field is dropped, and with `may_inst` a field of `r1`
    ///    that is `Reither` and not matched is made absent
    ///    (`Checker::resolve`, `Checker::settle`) and dropped.
    /// 4. A clash when `r1` is not empty, or row 1 is closed and row 2
    ///    is not or `r2` is not empty (3045-3046).
    /// 5. By the two rests (3047-3058): two universal variables,
    ///    [`Checker::unify_univar`]; one, a clash; `static_row row1`
    ///    (row 1 closed and none of its fields `Reither` NOW, after step
    ///    3), nothing; `may_inst`: a new generic variant node of `r2`
    ///    with row 2's `more`, closedness and `fixed` and no name
    ///    (`Checker::build_variant`), [`Checker::moregen_occur`]`
    ///    (rm1.level, it)`, `rm1` linked to it, and the arguments of row
    ///    1's name stop being children of its home
    ///    (`Checker::drop_name_children`, decision 60); two
    ///    constructors: the pair `rm1`, `rm2`, popped before the fields;
    ///    anything else a clash.
    /// 6. One [`FrameKind::RowField`] frame a common tag, pushed so that
    ///    they are popped in the order of the pairs; `left` and `right`
    ///    are the two `FieldRef::ty`, `extra` the index in `saved` of
    ///    one record: `head` the left row-field index, `level` the right
    ///    one, `a` 1 with `may_inst`.
    ///
    /// On a clash the frames and records this call pushed are taken off.
    /// Cost: the two flattenings and the merge, one step a field of `r1`
    /// and `r2`, 16 bytes of frame and 16 of record a common tag; with
    /// `may_inst` one node, one `VariantRow`, one descriptor row and a
    /// `RowFieldRow` a field of `r2`. (R3i)
    fn moregen_row(&mut self, inst_nongen: bool, [t1x, t2x]: [Ty; 2]) -> Result<(), Clash> {
        let (left, right) = (self.open_row(t1x), self.open_row(t2x));
        let base = self.extras.row_scratch.len();
        let (last1, rm1) = self.flatten_row(left);
        let n1 = self.extras.row_scratch.len() - base;
        let (last2, rm2) = self.flatten_row(right);
        let n2 = self.extras.row_scratch.len() - base - n1;
        if rm1 == rm2 {
            self.extras.row_scratch.truncate(base);
            return Ok(());
        }
        let (row1, row2) = (self.last_row(last1, left), self.last_row(last2, right));
        let (more1, more2) = (self.g.nodes[rm1.0 as usize], self.g.nodes[rm2.0 as usize]);
        let may_inst = (more1.tag() == VAR && may_instantiate(inst_nongen, more1.level)) || self.is_nil(more1);
        let pairs = self.merge_rows(base, n1);
        let (mut r1, mut r2) = (base..base + n1 - pairs, base + n1 - pairs..base + n1 + n2 - 2 * pairs);
        let paired = r2.end..r2.end + 2 * pairs;
        let fields1 = r1.clone();
        if row2.closed {
            r1 = self.filter_fields(r1, may_inst);
            r2 = self.filter_fields(r2, false);
        }
        // The arms of the two rests (ctype.ml:3043-3054); nothing is pushed
        // before the last of them, so a clash takes nothing off.
        let mut rests = false;
        let arms = 'arms: {
            if !r1.is_empty() || (row1.closed && (!row2.closed || !r2.is_empty())) {
                break 'arms Err(Clash);
            }
            let (univar1, univar2) = (self.is_univar(rm1), self.is_univar(rm2));
            if univar1 && univar2 {
                break 'arms self.unify_univar(rm1, rm2);
            }
            if univar1 || univar2 {
                break 'arms Err(Clash);
            }
            // `static_row row1`, read after the filter: a field it erased
            // is absent now. The range of `r1` before the filter still
            // holds every field it had or one it kept twice.
            let either = |c: &Checker, at: usize| matches!(c.field_now_at(at).kind, RowFieldKind::Either { .. });
            if row1.closed && !fields1.chain(paired.clone().step_by(2)).any(|at| either(self, at)) {
                break 'arms Ok(());
            }
            if may_inst {
                let unnamed = VariantRow { name: NONE, ..row2 };
                let ext = self.build_variant(r2.clone(), rm2, row2.closed, row2.fixed, (unnamed, 0));
                if let Err(clash) = self.moregen_occur(more1.level, ext) {
                    break 'arms Err(clash);
                }
                self.g.link(rm1, ext);
                // The link stays on a clash (no backtrack in `moregen`), so
                // nothing is to be put back: the write without its frame.
                if row1.name != NONE && row1.name_arguments.len != 0 {
                    let home1 = if last1.0 == NONE { t1x } else { last1 };
                    self.forget_name_children(home1, row1);
                }
                break 'arms Ok(());
            }
            if more1.tag() == CONSTR && more2.tag() == CONSTR {
                rests = true;
                break 'arms Ok(());
            }
            Err(Clash)
        };
        if arms.is_err() {
            self.extras.row_scratch.truncate(base);
            return arms;
        }
        for k in (0..pairs).rev() {
            let at = paired.start + 2 * k;
            let (f1, f2) = (self.extras.row_scratch[at], self.extras.row_scratch[at + 1]);
            let extra = self.saved.len() as u32;
            self.saved.push(Node { head: f1.at, level: f2.at, a: u32::from(may_inst), b: 0 });
            self.frames.push(Frame { left: f1.ty, right: f2.ty, kind: FrameKind::RowField, extra });
        }
        if rests {
            self.push_pair(rm1, rm2);
        }
        self.extras.row_scratch.truncate(base);
        Ok(())
    }

    /// `filter_row_fields erase` (compiler/ml/ctype.ml:388-397) of
    /// `Extras::row_scratch[fields]`, from the last field to the first:
    ///
    /// ```text
    /// let rec filter_row_fields erase = function
    ///   | [] -> []
    ///   | ((_l, f) as p) :: fi -> (
    ///     let fi = filter_row_fields erase fi in
    ///     match row_field_repr f with
    ///     | Rabsent -> fi
    ///     | Reither (_, _, false, e) when erase ->
    ///       set_row_field e Rabsent;
    ///       fi
    ///     | _ -> p :: fi)
    /// ```
    ///
    /// The kept fields move up to the end of the range, in order; the
    /// range of them is returned. One step a field; a field made absent
    /// costs `Checker::resolve` and `Checker::settle`. (R3i)
    fn filter_fields(&mut self, fields: std::ops::Range<usize>, erase: bool) -> std::ops::Range<usize> {
        let mut kept = fields.end;
        for at in fields.clone().rev() {
            #[cfg(test)]
            super::steps::tick();
            let field = self.field_now_at(at);
            let dropped = match field.kind {
                RowFieldKind::Absent => true,
                RowFieldKind::Either { matched: false, .. } if erase => {
                    let holders = self.resolve(field.end, RES_ABSENT, Ty(NONE));
                    self.settle(holders, RES_ABSENT);
                    true
                }
                _ => false,
            };
            if !dropped {
                kept -= 1;
                self.extras.row_scratch[kept] = self.extras.row_scratch[at];
            }
        }
        kept..fields.end
    }

    /// The pop of a [`FrameKind::RowField`] frame of `moregen_row`
    /// (compiler/ml/ctype.ml:3059-3089), one common tag; `f1` and `f2`
    /// are the two fields read now ([`field_repr`]) and `may_inst` is
    /// the record's `a`:
    ///
    /// ```text
    ///         if f1 == f2 then ()
    ///         else
    ///           match (f1, f2) with
    ///           | Rpresent (Some t1), Rpresent (Some t2) ->
    ///             moregen inst_nongen type_pairs env t1 t2
    ///           | Rpresent None, Rpresent None -> ()
    ///           | Reither (false, tl1, _, e1), Rpresent (Some t2) when may_inst ->
    ///             set_row_field e1 f2;
    ///             List.iter (fun t1 -> moregen inst_nongen type_pairs env t1 t2) tl1
    ///           | Reither (c1, tl1, _, e1), Reither (c2, tl2, m2, e2) ->
    ///             if e1 != e2 then (
    ///               if c1 && not c2 then raise (Unify []);
    ///               set_row_field e1 (Reither (c2, [], m2, e2));
    ///               if List.length tl1 = List.length tl2 then
    ///                 List.iter2 (moregen inst_nongen type_pairs env) tl1 tl2
    ///               else
    ///                 match tl2 with
    ///                 | t2 :: _ ->
    ///                   List.iter
    ///                     (fun t1 -> moregen inst_nongen type_pairs env t1 t2)
    ///                     tl1
    ///                 | [] -> if tl1 <> [] then raise (Unify []))
    ///           | Reither (true, [], _, e1), Rpresent None when may_inst ->
    ///             set_row_field e1 f2
    ///           | Reither (_, _, _, e1), Rabsent when may_inst -> set_row_field e1 f2
    ///           | Rabsent, Rabsent -> ()
    ///           | _ -> raise (Unify [])
    /// ```
    ///
    /// `f1 == f2` is two `Reither` with one reference; every other
    /// identical pair passes its arm below. The types of a field are
    /// read into `Extras::row_scratch` BEFORE its reference is written
    /// (`Checker::read_types`), the reference is written with
    /// `Checker::resolve` and its holders settled at once
    /// (`Checker::settle`), or with `Checker::resolve_either` and no
    /// types for the `Reither` arm; then the pairs are pushed last
    /// first. O(types of the two fields + holders). (R3i)
    fn moregen_row_field(&mut self, frame: Frame) -> Result<(), Clash> {
        let record = self.saved[frame.extra as usize];
        let may_inst = record.a != 0;
        let (row1, row2) =
            (self.extras.row_fields[record.head as usize], self.extras.row_fields[record.level as usize]);
        let f1 = field_repr(&self.g, frame.left.0, u32::MAX, row1);
        let f2 = field_repr(&self.g, frame.right.0, u32::MAX, row2);
        let base = self.extras.row_scratch.len();
        let result = match (f1.kind, f2.kind) {
            (RowFieldKind::Present, RowFieldKind::Present) => match (f1.first.0 == NONE, f2.first.0 == NONE) {
                (false, false) => {
                    self.push_pair(f1.first, f2.first);
                    Ok(())
                }
                (true, true) => Ok(()),
                _ => Err(Clash),
            },
            (RowFieldKind::Either { constant: false, .. }, RowFieldKind::Present) if f2.first.0 != NONE && may_inst => {
                self.read_types(frame.left.0, row1);
                let holders = self.resolve(f1.end, RES_PRESENT, f2.first);
                self.settle(holders, RES_PRESENT);
                for at in (base..self.extras.row_scratch.len()).rev() {
                    let t1 = self.extras.row_scratch[at].ty;
                    self.push_pair(t1, f2.first);
                }
                Ok(())
            }
            (RowFieldKind::Either { constant: c1, .. }, RowFieldKind::Either { constant: c2, matched: m2 }) => {
                if f1.end == f2.end {
                    // `f1 == f2`, or `e1 == e2`.
                    Ok(())
                } else if c1 && !c2 {
                    Err(Clash)
                } else {
                    self.read_types(frame.left.0, row1);
                    let n = self.extras.row_scratch.len() - base;
                    self.read_types(frame.right.0, row2);
                    let m = self.extras.row_scratch.len() - base - n;
                    self.resolve_either(f1.end, either_flags(c2, m2), base..base, f2.end);
                    if n == m {
                        for k in (0..n).rev() {
                            let (t1, t2) =
                                (self.extras.row_scratch[base + k].ty, self.extras.row_scratch[base + n + k].ty);
                            self.push_pair(t1, t2);
                        }
                        Ok(())
                    } else if m != 0 {
                        let t2 = self.extras.row_scratch[base + n].ty;
                        for k in (0..n).rev() {
                            let t1 = self.extras.row_scratch[base + k].ty;
                            self.push_pair(t1, t2);
                        }
                        Ok(())
                    } else {
                        // `[] -> if tl1 <> [] then raise (Unify [])`, n > 0.
                        Err(Clash)
                    }
                }
            }
            (RowFieldKind::Either { constant: true, .. }, RowFieldKind::Present)
                if f1.types == 0 && f2.first.0 == NONE && may_inst =>
            {
                let holders = self.resolve(f1.end, RES_PRESENT, Ty(NONE));
                self.settle(holders, RES_PRESENT);
                Ok(())
            }
            (RowFieldKind::Either { .. }, RowFieldKind::Absent) if may_inst => {
                let holders = self.resolve(f1.end, RES_ABSENT, Ty(NONE));
                self.settle(holders, RES_ABSENT);
                Ok(())
            }
            (RowFieldKind::Absent, RowFieldKind::Absent) => Ok(()),
            _ => Err(Clash),
        };
        self.extras.row_scratch.truncate(base);
        result
    }

    /// `eqtype_row` (compiler/ml/ctype.ml:3325-3358) for the two variant
    /// nodes `t1x`, `t2x`. Nothing is written but the rows that are
    /// opened ([`Checker::open_row`], [`Checker::flatten_row`]), which
    /// the restore of `equal` undoes.
    ///
    /// 1. Row 2 is flattened; its `more` is expanded in
    ///    [`ExpandMode::Rigid`], and while the head is a variant node the
    ///    row is that node's (`match expand_head_rigid env (row_more
    ///    row2) with {desc = Tvariant row2} -> eqtype_row ... row1
    ///    row2`, 3327-3328; a loop).
    /// 2. Row 1 is flattened, the two are merged
    ///    ([`Checker::merge_rows`]).
    /// 3. A clash (3332-3336) when the two rows differ in `closed`, or
    ///    they are open and one has a tag the other lacks, or a tag only
    ///    one has is not absent (`filter_row_fields false (r1 @ r2) <>
    ///    []`).
    /// 4. Unless row 1 is static, the pair of the two rests (3337-3338),
    ///    popped first.
    /// 5. Each common tag (3339-3358), in the order of the pairs: two
    ///    present fields with a type, the pair; two `Reither` with one
    ///    `c`: both without types, nothing; both with types, the pair of
    ///    the first two, then with as many types on each side the other
    ///    types pairwise, otherwise `t1` against every other type of the
    ///    right and every other type of the left against `t2`; two
    ///    present fields without a type, two absent fields: nothing;
    ///    anything else a clash.
    ///
    /// The pairs are pushed so that they are popped in OCaml's order.
    /// Cost: the flattenings and the merge, one step a field of `r1` and
    /// `r2`, 16 bytes of frame a pair. (R3i)
    fn eqtype_row(&mut self, [t1x, t2x]: [Ty; 2]) -> Result<(), Clash> {
        let base = self.extras.row_scratch.len();
        let (left, mut right) = (self.open_row(t1x), self.open_row(t2x));
        // `expand_head_rigid env (row_more row2)` while it is a variant
        // (ctype.ml:3323-3324).
        let (last2, rm2) = loop {
            self.extras.row_scratch.truncate(base);
            let (last2, rm2) = self.flatten_row(right);
            let Ok(head) = self.expand_head(rm2, ExpandMode::Rigid) else {
                self.extras.row_scratch.truncate(base);
                return Err(Clash);
            };
            if !self.is_variant(self.g.nodes[head.0 as usize]) {
                break (last2, rm2);
            }
            right = self.open_row(head);
        };
        // Row 2 moves above row 1: `merge_rows` wants the left one first.
        let n2 = self.extras.row_scratch.len() - base;
        let (last1, rm1) = self.flatten_row(left);
        let n1 = self.extras.row_scratch.len() - base - n2;
        self.extras.row_scratch[base..].rotate_left(n2);
        let (row1, row2) = (self.last_row(last1, left), self.last_row(last2, right));
        let pairs = self.merge_rows(base, n1);
        let (r1, r2) = (base..base + n1 - pairs, base + n1 - pairs..base + n1 + n2 - 2 * pairs);
        let paired = r2.end..r2.end + 2 * pairs;
        let frames = self.frames.len();
        let mut absent = true;
        for at in r1.start..r2.end {
            #[cfg(test)]
            super::steps::tick();
            absent &= self.field_now_at(at).kind == RowFieldKind::Absent;
        }
        let mut clash = row1.closed != row2.closed || (!row1.closed && r1.start != r2.end) || !absent;
        let either = |c: &Checker, at: usize| matches!(c.field_now_at(at).kind, RowFieldKind::Either { .. });
        let static_row = row1.closed && !r1.clone().chain(paired.clone().step_by(2)).any(|at| either(self, at));
        let mut k = pairs;
        while !clash && k > 0 {
            k -= 1;
            let at = paired.start + 2 * k;
            let (s1, s2) = (self.extras.row_scratch[at], self.extras.row_scratch[at + 1]);
            let (f1, f2) = (self.field_now_at(at), self.field_now_at(at + 1));
            match (f1.kind, f2.kind) {
                (RowFieldKind::Present, RowFieldKind::Present) => match (f1.first.0 == NONE, f2.first.0 == NONE) {
                    (false, false) => self.push_pair(f1.first, f2.first),
                    (true, true) => {}
                    _ => clash = true,
                },
                (RowFieldKind::Either { constant: c1, .. }, RowFieldKind::Either { constant: c2, .. })
                    if c1 == c2 && (f1.types == 0) == (f2.types == 0) =>
                {
                    if f1.types == 0 {
                        continue;
                    }
                    let scratch = self.extras.row_scratch.len();
                    self.read_types(s1.ty.0, self.extras.row_fields[s1.at as usize]);
                    let n = self.extras.row_scratch.len() - scratch;
                    self.read_types(s2.ty.0, self.extras.row_fields[s2.at as usize]);
                    let m = self.extras.row_scratch.len() - scratch - n;
                    let ty = |c: &Checker, at: usize| c.extras.row_scratch[at].ty;
                    let (t1, t2) = (ty(self, scratch), ty(self, scratch + n));
                    // Pushed last first: `t1, t2`, then the rest of
                    // ctype.ml:3343-3350 in order.
                    if n == m {
                        for i in (1..n).rev() {
                            let (a, b) = (ty(self, scratch + i), ty(self, scratch + n + i));
                            self.push_pair(a, b);
                        }
                    } else {
                        for i in (1..n).rev() {
                            let a = ty(self, scratch + i);
                            self.push_pair(a, t2);
                        }
                        for i in (1..m).rev() {
                            let b = ty(self, scratch + n + i);
                            self.push_pair(t1, b);
                        }
                    }
                    self.push_pair(t1, t2);
                    self.extras.row_scratch.truncate(scratch);
                }
                (RowFieldKind::Absent, RowFieldKind::Absent) => {}
                _ => clash = true,
            }
        }
        self.extras.row_scratch.truncate(base);
        if clash {
            self.frames.truncate(frames);
            return Err(Clash);
        }
        // `if not (static_row row1)`, before the tags: popped first.
        if !static_row {
            self.push_pair(rm1, rm2);
        }
        Ok(())
    }

    /// `subtype env ty1 ty2` up to the closure it returns
    /// (compiler/ml/ctype.ml:4212-4217), without the arms that read a
    /// declaration's labels or constructors (R6e; CHECKER_REWRITE 8.13,
    /// the table of arms):
    ///
    /// ```text
    /// let subtype env ty1 ty2 =
    ///   Type_pairs.clear (subtypes ());
    ///   current_univar_pairs () := [];
    ///   (* Build constraint set. *)
    ///   let cstrs = subtype_rec env [(ty1, ty2)] ty1 ty2 [] in
    ///   Type_pairs.clear (subtypes ());
    /// ```
    ///
    /// `out` is emptied, then filled with the constraints of `left :>
    /// right` in the order [`Checker::force_subtype`] unifies them
    /// (OCaml conses and reverses, 4231). Nothing is unified here.
    ///
    /// The scopes of universal variables are emptied at the entry
    /// ([`Checker::empty_scopes`]; OCaml empties its list, 4214): what
    /// was open stays below [`Checker::scope_floor`], and at the end
    /// `scopes` has the length it had. [`Checker::subtyped`] is cleared
    /// at the entry and at the end, as OCaml clears twice (4213, 4217).
    /// It is the table of subtyping ALONE (`subtypes ()`, one global of
    /// OCaml): the relations a supplier runs inside the walk have
    /// [`Checker::related`] (`Type_pairs.create`, 3115, 3370) and do
    /// not see or clear this one (CHECKER_REWRITE 8.6, decision 128). [`Checker::subtype_trace`]
    /// is cleared. The root pair goes on [`Checker::subtyping`] with the
    /// first link of the trace (`[(ty1, ty2)]`) and
    /// `Checker::subtype_frames` runs.
    ///
    /// NO speculation (OCaml takes none): what the walk writes stays.
    /// It writes expansions with their memos (`expand_abbrev`,
    /// 3675, 3678, 3706), opened rows, compressed paths, the nodes of the
    /// constraints it builds (3693-3695, 4119-4131, 4152-4170), the
    /// instance of a polymorphic type (4065) and partner nodes of the
    /// scopes it enters; it links no variable. The trial of two packages
    /// of different paths is the one place that unifies, under a
    /// speculation of its own that is restored (4089-4098).
    ///
    /// `Err`: two tuples of different lengths (`subtype_list`,
    /// 4104: `subtype_error env trace`). The frames, the scopes and
    /// `out` are cut back to empty; in `Mode::Explain`
    /// [`Checker::subtype_trace`] holds the pairs down to the two
    /// tuples and [`Checker::trace`] is empty (`Subtype (expand_trace
    /// env (List.rev trace), [], None)`, 3614-3615); in `Mode::Success`
    /// outside a speculation `unexplained_failure` is set.
    ///
    /// Cost: O(pairs visited): one step and one hash insertion a pair
    /// that is not one node, plus the callees; 16 bytes of frame a
    /// pending pair, 16 a constraint, and in `Mode::Explain` 12 a pair
    /// pushed. No recursion. (R3j)
    pub fn subtype(&mut self, left: Ty, right: Ty, out: &mut Coercion) -> Result<(), Clash> {
        todo!("R3j")
    }

    /// The closure `subtype` returns (compiler/ml/ctype.ml:4219-4231):
    ///
    /// ```text
    ///   function
    ///   | () ->
    ///     List.iter
    ///       (function
    ///         | trace0, t1, t2, pairs, ctx -> (
    ///           try unify_pairs (ref env) t1 t2 pairs
    ///           with Unify trace ->
    ///             raise
    ///               (Subtype
    ///                  ( expand_trace env (List.rev trace0),
    ///                    List.tl (List.tl trace),
    ///                    ctx ))))
    ///       (List.rev cstrs)
    /// ```
    ///
    /// Each constraint of `coercion`, in order: when its `scopes` is not
    /// what the constraint before it had, `Checker::open_scopes` makes
    /// [`Checker::scopes`] the chain of its [`HeldScope`]s, outermost
    /// first (`unify_pairs`: `univar_pairs := pairs`,
    /// ctype.ml:2769-2771); then [`Checker::unify`]. The chain is pushed
    /// ABOVE the length `scopes` has at the entry, which is
    /// [`Checker::scope_floor`] for every constraint: the floor is
    /// written before each unification (one store a constraint),
    /// because a unification may raise it (a package whose inclusion
    /// check runs a relation) and OCaml assigns the list again for the
    /// next constraint. A unification leaves the length of `scopes` as
    /// it found it on both answers. After the last constraint, and
    /// after a clash, `scopes` is cut to the length of the entry and
    /// the floor is that length: OCaml leaves the last constraint's
    /// list in place, and every later `unify` of the typer starts by
    /// emptying it (`let unify env ty1 ty2 = unify_pairs (ref env) ty1
    /// ty2 []`, 2773).
    ///
    /// NO speculation: the links stay, also those of the constraints
    /// before a clash and of the one that clashed (in `Mode::Explain`
    /// the top-level unification undoes its path compressions only,
    /// `Checker::undo_compress`).
    ///
    /// A clash ends the call (the constraints after it are not
    /// unified). In `Mode::Explain` [`Checker::subtype_trace`] holds
    /// the constraint's pairs outermost first, and [`Checker::trace`]
    /// the unification's trace without its first pair (`List.tl
    /// (List.tl trace)`: OCaml's trace has two entries a pair, a type
    /// and its expansion, and the kernel's one). Neither is expanded:
    /// the expansion of a trace is the printer's (8.13). In
    /// `Mode::Success` the unification has set `unexplained_failure`.
    ///
    /// A scope open at the entry is not read (the first `unify_pairs`
    /// replaces the list). A
    /// caller that never forces drops `coercion`: nothing of it is held
    /// by the checker. Cost: O(constraints), one step each, plus the
    /// unifications; one step a scope closed or opened between two
    /// constraints, which over a whole coercion is at most twice the
    /// scopes entered plus the scopes open at the last constraint (the
    /// constraints are in the order of the walk); on a clash one step a
    /// pair of the trace. (R3j)
    pub fn force_subtype(&mut self, coercion: &Coercion) -> Result<(), Clash> {
        todo!("R3j")
    }

    /// Make [`Checker::scopes`], which holds the chain of `from` (an
    /// index of `coercion.scopes` or `NONE`), hold the chain of `to`,
    /// outermost first, and return `to`. A row's parent has a lower
    /// index than the row, so the two chains are walked back from their
    /// ends, the one with the higher index first, until they meet: a
    /// scope left on the `from` side is popped, one left on the `to`
    /// side is counted; then the counted scopes are pushed from `to`
    /// upwards and that tail of `scopes` is reversed. OCaml assigns a
    /// list (`univar_pairs := pairs`, O(1)); this is O(scopes that
    /// differ), one step each, no allocation. (R3j)
    fn open_scopes(&mut self, coercion: &Coercion, from: u32, to: u32) -> u32 {
        todo!("R3j")
    }

    /// `enlarge_type env ty` (compiler/ml/ctype.ml:3589-3593):
    ///
    /// ```text
    /// let enlarge_type env ty =
    ///   warn () := false;
    ///   (* [level = 4] allows 2 expansions involving objects/variants *)
    ///   let ty', _ = build_subtype env [] [] true 4 ty in
    ///   (ty', !(warn ()))
    /// ```
    ///
    /// The supertype a coercion without a source annotation is first
    /// tried against (typecore.ml:3594-3604; the snapshot and the
    /// unification are the caller's), and `warn`: whether a double
    /// coercion might do better, which no caller of this compiler reads
    /// (`let ty, _b = enlarge_type env ty'`, typecore.ml:3597) and which
    /// is returned because OCaml returns it.
    ///
    /// `build_subtype` (3427-3587) is a recursion that returns a type
    /// and a `change`; here one loop over [`Checker::enlarging`], a
    /// frame a node entered ([`EnlargeFrame`]), with the results of the
    /// nodes left on [`Checker::enlarged`]. The frame of the root is
    /// pushed with `posi` and level 4 and `Checker::enlarge_visit` /
    /// `Checker::enlarge_leave` run until the stack is back to its
    /// length at the entry. `loops` is `[]` at this one entry and
    /// nothing adds to it (3430-3437), so a variable is itself.
    ///
    /// `visited` is a list of the PATH (`let visited = t :: visited`,
    /// passed down, gone on return; 3441, 3458, 3479), which an object
    /// or a variant cuts (3506-3508, 3543-3544), searched with
    /// `List.memq` (`memq_warn`, 3409-3413). Here
    /// [`Checker::path_entries`] with an [`EnlargePath`]:
    /// `Checker::on_path` is two loads and a compare (8.13, "The
    /// visited list").
    ///
    /// What it writes: the new nodes, at the current level (`newty`,
    /// `newvar`, `newconstr`); expansions with their memos
    /// (`expand_abbrev` under `safe_abbrev`, 3466-3468, 3483); opened
    /// rows. It links nothing and takes no speculation.
    ///
    /// Cost: one step a frame popped, at most three frames a node
    /// entered and one a child; one node made for a node with a changed
    /// child, a variant, or a closed end of a field list in a positive
    /// position; no allocation outside the pools. A unit that never
    /// calls it pays nothing: `path_entries` is empty until the first
    /// call, then four bytes a node. (R3j)
    pub fn enlarge_type(&mut self, ty: Ty) -> (Ty, bool) {
        todo!("R3j")
    }

    /// The loop of `subtype_rec` (compiler/ml/ctype.ml:3643-4101): pop
    /// the frames of [`Checker::subtyping`] above `base` until none is
    /// left. A loop of its own and not a third `Relation` of
    /// `relate_frames`: a pair here carries its trace, collects where the
    /// two relations clash, and has continuations the frames of
    /// unification do not have (CHECKER_REWRITE 8.6, decision 119).
    ///
    /// - A [`SubKind::Pair`] frame: `Checker::subtype_pair`.
    /// - A [`SubKind::Constrain`] frame: `Checker::constrain` of the frame's
    ///   two types under its link: a constraint OCaml makes after a walk
    ///   that is still on the stack (`subtype_fields`, 4126-4133).
    /// - A [`SubKind::Leave`] frame: the innermost scope of
    ///   [`Checker::scopes`] is popped, `out.held` is the frame's
    ///   `left` again and [`Checker::scope_floor`] its `right`
    ///   (`univar_pairs := old_univars`, ctype.ml:1675): what the entry
    ///   found, also when the body emptied the scopes (a trial of two
    ///   packages).
    /// - A [`SubKind::Invariant`] frame (an argument that may occur both ways,
    ///   3687-3691): a [`SubKind::Back`] frame of the same pair with the
    ///   `dirty` of `out`; `out.quiet` one more and `out.dirty` false;
    ///   the pair `left`, `right` under a new link.
    /// - A [`SubKind::Back`] frame: when `out.dirty` (the first direction made a
    ///   constraint: `subtype_rec ... t1 t2 [] = []` is false and `&&`
    ///   does not run the second), `Checker::subtype_close`; otherwise
    ///   a [`SubKind::Close`] frame of the same pair and the pair
    ///   `right`, `left` under a new link.
    /// - A [`SubKind::Close`] frame: `Checker::subtype_close`.
    ///
    /// `Err` is the link of two tuples of different lengths; the frames
    /// stay for the caller to cut. One step a frame popped. No
    /// recursion: a type 10,000 deep costs 16 bytes of frame a level.
    /// (R3j)
    fn subtype_frames(&mut self, out: &mut Coercion, base: usize) -> Result<(), u32> {
        todo!("R3j")
    }

    /// A new entry of the trace: `(left, right) :: trace` for the trace
    /// that ends in `parent` (`NONE`: the empty trace). In
    /// `Mode::Explain` one [`TraceLink`] appended to `out.links`, whose
    /// index is returned; in `Mode::Success` nothing, and `NONE`. Made
    /// inside a quiet region too: `subtype_error` reports the trace of a
    /// pair of tuples met there. O(1). (R3j)
    #[inline]
    fn subtype_link(&mut self, out: &mut Coercion, parent: u32, left: Ty, right: Ty) -> u32 {
        todo!("R3j")
    }

    /// `subtype_rec env ((left, right) :: trace) left right cstrs` as a
    /// pending call: one [`SubKind::Pair`] frame under a new link whose
    /// parent is `parent`. O(1). (R3j)
    #[inline]
    fn push_subtype(&mut self, out: &mut Coercion, parent: u32, left: Ty, right: Ty) {
        todo!("R3j")
    }

    /// `(trace, left, right, !(current_univar_pairs ()), None) :: cstrs`
    /// (compiler/ml/ctype.ml:3655 and every arm that collects): inside a
    /// quiet region (`out.quiet != 0`) only `out.dirty` is set, since
    /// the list the constraint goes to is dropped (3689-3690: `= []`);
    /// otherwise one [`Constraint`] appended with `link` and `out.held`.
    /// O(1). (R3j)
    #[inline]
    fn constrain(&mut self, out: &mut Coercion, link: u32, left: Ty, right: Ty) {
        todo!("R3j")
    }

    /// The end of a quiet region: `out.quiet` one less, `out.dirty` what
    /// the frame kept. For an invariant argument (the frame's `left` is
    /// not `NONE`) of which a direction made a constraint
    /// (compiler/ml/ctype.ml:3692-3698):
    ///
    /// ```text
    ///                     ( trace,
    ///                       newty2 t1.level (Ttuple [t1]),
    ///                       newty2 t2.level (Ttuple [t2]),
    ///                       !(current_univar_pairs ()),
    ///                       None )
    ///                     :: cstrs
    /// ```
    ///
    /// `Checker::constrain` under the frame's link (the constructor
    /// pair's) of two new tuples of one element, each at the level its
    /// element's node has, read without `repr` as OCaml reads it. The
    /// tuples are not made inside an enclosing quiet region. For the
    /// region of a row that ended in `Exit` (`left` is `NONE`) nothing
    /// more: the frame below is the row's [`SubKind::Constrain`]. O(1);
    /// two nodes and two list slots. (R3j)
    fn subtype_close(&mut self, out: &mut Coercion, frame: SubFrame) {
        todo!("R3j")
    }

    /// One pair of `subtype_rec` (compiler/ml/ctype.ml:3643-4101), in
    /// OCaml's order of arms; `link` is the frame's (`trace`).
    ///
    /// 1. The two representatives; one node: nothing (3644-3646). The
    ///    ordered pair in [`Checker::subtyped`]: nothing; otherwise
    ///    added (3648-3652).
    /// 2. A variable on either side: `Checker::constrain` (3654-3655).
    /// 3. Two arrows of one arity whose labels are the same
    ///    (`Asttypes.same_arg_label`: the two label words are equal;
    ///    3656-3668): for each parameter in order the pair of the RIGHT
    ///    parameter's type and the left one's (`subtype_rec env
    ///    ((a2.typ, a1.typ) :: trace) a2.typ a1.typ`), then the pair of
    ///    the two results; pushed last first.
    /// 4. Two tuples (3669-3671, `subtype_list` 4103-4107): different
    ///    lengths, `Err(link)`; otherwise the pairs of the elements.
    /// 5. Two constructors without arguments of one type: nothing
    ///    (3672).
    /// 6. A constructor on the left whose type expands publicly
    ///    (`Checker::expands`: `generic_abbrev`, 1353-1357) and whose
    ///    [`Checker::expand_once`] in [`ExpandMode::Safe`] gives a node
    ///    (`safe_abbrev`, 1240-1247): the pair of that node and `t2`
    ///    under the SAME link (3673-3675). Then the same on the right
    ///    (3676-3678).
    /// 7. Two constructors of one type (3679-3704):
    ///    `Checker::subtype_constr`.
    /// 8. A constructor on the left whose type is a private
    ///    abbreviation (`generic_private_abbrev`, 1359-1369) and whose
    ///    `expand_once` in [`ExpandMode::Opt`] gives a node: the pair of
    ///    that node and `t2` under the same link (3705-3706).
    /// 9. R6e's arms go HERE (3707-4028: a private record or variant on
    ///    the right, `int` to `float`, a primitive and an unboxed
    ///    variant, two variants, two records): not built; such a pair
    ///    goes on and ends in step 13.
    /// 10. Two objects (4030-4034): when both field lists end in a
    ///     variable (`Checker::object_row`), `constrain`; otherwise
    ///     `Checker::subtype_fields`.
    /// 11. Two variants (4035-4038): `Checker::subtype_row`. R6e's two
    ///     arms of a variant against another type (4039-4062) go after
    ///     it.
    /// 12. Two polymorphic types (4063-4072): `Checker::subtype_poly`.
    ///     Two packages (4073-4100): `Checker::subtype_package`.
    /// 13. Anything else: `constrain` (4101).
    ///
    /// O(1) plus the callee; one hash insertion. (R3j)
    fn subtype_pair(&mut self, out: &mut Coercion, frame: SubFrame) -> Result<(), u32> {
        todo!("R3j")
    }

    /// `generic_abbrev env p` with `flag` [`super::expand::ABBREV`]
    /// (compiler/ml/ctype.ml:1353-1357) and `generic_private_abbrev env
    /// p` with [`super::expand::PRIVATE`] (1359-1369) for type index
    /// `type_index`: whether the row has the flag, or is another
    /// spelling ([`super::expand::ALIAS`]) of a type that has it
    /// (`Env.find_type_expansion` and `Env.find_type` find the
    /// declaration through a module alias); the chain of spellings is
    /// followed. The test `(repr body).level = generic_level` holds for
    /// every manifest the table has: a manifest is a template, and the
    /// destination of an equation is a generic copy (8.13). O(spellings
    /// on the way), one row load each. (R3j)
    #[inline]
    fn expands(&self, type_index: u32, flag: u8) -> bool {
        todo!("R3j")
    }

    /// `object_row ty` (compiler/ml/ctype.ml:346-351): the
    /// representative that ends the field list `fields`, through fields
    /// and objects. O(fields), one step a node; no write but path
    /// compression. (R3j)
    fn object_row(&mut self, fields: Ty) -> Ty {
        todo!("R3j")
    }

    /// Two constructors of one type with arguments
    /// (compiler/ml/ctype.ml:3679-3704), `d1` and `d2` their
    /// descriptors:
    ///
    /// ```text
    ///           List.fold_left2
    ///             (fun cstrs v (t1, t2) ->
    ///               let co, cn = Variance.get_upper v in
    ///               if co then
    ///                 if cn then
    ///                   (* Invariant type argument: check both ways *)
    ///                   if
    ///                     subtype_rec env ((t1, t2) :: trace) t1 t2 [] = []
    ///                     && subtype_rec env ((t2, t1) :: trace) t2 t1 [] = []
    ///                   then cstrs
    ///                   else (...) :: cstrs
    ///                 else subtype_rec env ((t1, t2) :: trace) t1 t2 cstrs
    ///               else if cn then subtype_rec env ((t2, t1) :: trace) t2 t1 cstrs
    ///               else cstrs)
    ///             cstrs decl.type_variance (List.combine tl1 tl2)
    ///         with Not_found ->
    ///           (trace, t1, t2, !(current_univar_pairs ()), None) :: cstrs)
    /// ```
    ///
    /// A type whose declaration the table does not have
    /// ([`super::expand::TypeTable::upper`] is `None`): `constrain` of
    /// the two nodes. Otherwise one frame an argument, pushed last
    /// argument first: both ways, [`SubKind::Invariant`] of the two
    /// arguments under `link`; positively only, the pair; negatively
    /// only, the pair swapped; neither, nothing. O(arguments), one step
    /// each. (R3j)
    fn subtype_constr(&mut self, out: &mut Coercion, [t1, t2]: [Ty; 2], d1: Node, d2: Node, link: u32) {
        todo!("R3j")
    }

    /// `subtype_fields env trace ty1 ty2 cstrs`
    /// (compiler/ml/ctype.ml:4109-4173) for two field lists, `link` the
    /// trace of the two objects:
    ///
    /// ```text
    ///   let fields1, rest1 = flatten_fields ty1 in
    ///   let fields2, rest2 = flatten_fields ty2 in
    ///   let pairs, miss1, miss2 = associate_fields fields1 fields2 in
    ///   let cstrs =
    ///     if rest2.desc = Tnil then cstrs
    ///     else if miss1 = [] then
    ///       subtype_rec env ((rest1, rest2) :: trace) rest1 rest2 cstrs
    ///     else
    ///       ( trace, build_fields (repr ty1).level miss1 rest1, rest2, ... ) :: cstrs
    ///   in
    ///   let cstrs =
    ///     if miss2 = [] then cstrs
    ///     else
    ///       ( trace, rest1, build_fields (repr ty2).level miss2 (newvar ()), ... ) :: cstrs
    ///   in
    ///   List.fold_left (fun cstrs (f1, f2) -> ...) cstrs pairs
    /// ```
    ///
    /// Both lists are flattened into `Extras::fields` (taken and put
    /// back, cut to the length found) and merged from the last names to
    /// the first (`associate_fields`, 330-342; two indices may spell one
    /// name: differing indices compare their texts once, decision 32).
    /// In that one pass:
    /// - a common name pushes its frame, so that the common names are
    ///   popped in name order: when the RIGHT field is immutable
    ///   (`mutability_repr f2.f_mut`; [`cell_repr`], [`cell_mutable`] of
    ///   `Checker::cell_of`), the pair of the two types under a new
    ///   link; when it is mutable, a [`SubKind::Constrain`] under `link`
    ///   of two new fields at the current level
    ///   ([`Checker::build_field`], which shares the name and the CELL
    ///   of the field it copies: 4152-4170), the left one over `rest1`
    ///   and the right one over a new variable;
    /// - a name only the left has is built on the chain that starts at
    ///   `rest1` (`build_fields`, 325-328, at the level of the
    ///   representative of `ty1`), unless `rest2` is `Tnil`;
    /// - a name only the right has is built on a chain that starts at a
    ///   new variable, at the level of the representative of `ty2`.
    ///
    /// Then, above the common names and so popped before them: a
    /// `Constrain` of `rest1` and the right chain when the right has a
    /// name the left lacks; and above it, unless `rest2` is `Tnil`, the
    /// pair of the two rests under a new link when the left has no name
    /// the right lacks, else a `Constrain` of the left chain and
    /// `rest2`. Inside a quiet region no node is built and the two
    /// `Constrain` frames carry `NONE`.
    ///
    /// Cost: the two flattenings (their sort included) and one step a
    /// merge step; 16 bytes of frame a common name; one node a field
    /// built. (R3j)
    fn subtype_fields(&mut self, out: &mut Coercion, ty1: Ty, ty2: Ty, link: u32) {
        todo!("R3j")
    }

    /// A new variable at the current level, without a name (`newvar
    /// ()`). O(1); one node. (R3j)
    #[inline]
    fn fresh_var(&mut self) -> Ty {
        todo!("R3j")
    }

    /// Two variants (compiler/ml/ctype.ml:4035-4038 with `subtype_row`,
    /// 4175-4210), `t1` and `t2` the two nodes:
    ///
    /// ```text
    ///       | Tvariant row1, Tvariant row2 -> (
    ///         try subtype_row env trace row1 row2 cstrs
    ///         with Exit ->
    ///           (trace, t1, t2, !(current_univar_pairs ()), None) :: cstrs)
    /// ```
    ///
    /// Both nodes are opened and flattened ([`Checker::open_row`],
    /// [`Checker::flatten_row`]) into `Extras::row_scratch` above the
    /// length found, and merged ([`Checker::merge_rows`]). By the two
    /// rests `more1`, `more2`:
    ///
    /// 1. Two constructors of one type (4180-4181): the pair of the two
    ///    rests under a new link, and nothing else.
    /// 2. Each a variable, a constructor or `Tnil`, row 1 closed and
    ///    with no tag row 2 lacks (4182-4194): each common tag, in the
    ///    order of the pairs, read now ([`Checker::field_now_at`]): a
    ///    present tag without a type or an `Either` tag with `c`,
    ///    against a present tag without a type: nothing; two present
    ///    tags with a type: the pair of the types; `Either` without `c`
    ///    and with a type against a present tag with a type: the pair of
    ///    its FIRST type and the type; an absent tag on the left:
    ///    nothing; anything else is `Exit`.
    /// 3. Two universal variables, rows closed alike and neither with a
    ///    tag the other lacks (4195-4209): the pair of the two rests,
    ///    popped first; then each common tag: two present tags without
    ///    a type, two `Either` tags with `c` and no type, two absent
    ///    tags: nothing; two present tags with a type, two `Either`
    ///    tags without `c` and with ONE type each: the pair; anything
    ///    else is `Exit`.
    /// 4. Anything else: `Exit` (4210).
    ///
    /// The common tags are classified in one pass before a pair is
    /// walked; the pairs to walk are kept above the merged rows in the
    /// scratch and pushed last first. `Exit` with no pair before it:
    /// `constrain` of the two nodes. `Exit` at a later tag: OCaml has
    /// walked the pairs before it and drops what they collected (the
    /// handler has the list of before), while the pairs they visited
    /// stay in the table. So: a `Constrain` frame of the two nodes; above
    /// it a [`SubKind::Close`] frame with `left` `NONE` and the `dirty`
    /// of `out`; `out.quiet` one more and `out.dirty` false; then the
    /// pairs before the `Exit` (CHECKER_REWRITE 8.6, decision 122). The
    /// scratch is cut back to the length found.
    ///
    /// Cost: the two flattenings and the merge, one step a common tag
    /// classified, 16 bytes of frame a pair. (R3j)
    fn subtype_row(&mut self, out: &mut Coercion, [t1, t2]: [Ty; 2], link: u32) {
        todo!("R3j")
    }

    /// Two polymorphic types (compiler/ml/ctype.ml:4063-4072), `d1` and
    /// `d2` their descriptors (slot 0 the body, then the bound
    /// variables):
    ///
    /// ```text
    ///       | Tpoly (u1, []), Tpoly (u2, []) -> subtype_rec env trace u1 u2 cstrs
    ///       | Tpoly (u1, tl1), Tpoly (u2, []) ->
    ///         let _, u1' = instance_poly ~fixed:false tl1 u1 in
    ///         subtype_rec env trace u1' u2 cstrs
    ///       | Tpoly (u1, tl1), Tpoly (u2, tl2) -> (
    ///         try
    ///           enter_poly env (current_univar_pairs ()) u1 tl1 u2 tl2 (fun t1 t2 ->
    ///               subtype_rec env trace t1 t2 cstrs)
    ///         with Unify _ ->
    ///           (trace, t1, t2, !(current_univar_pairs ()), None) :: cstrs)
    /// ```
    ///
    /// Neither binds: the pair of the bodies under the SAME link. Only
    /// the left binds: [`Checker::instance_poly`] of `t1` (not fixed, no
    /// names; its variables go to `Extras::fields`' sibling scratch
    /// [`Checker::rigid_vars`], taken and put back empty) and the pair
    /// of the instance and the right body. Otherwise
    /// [`Checker::enter_poly`]: a clash is `constrain` of the two
    /// nodes; on success the two frames it pushed on
    /// [`Checker::frames`] are taken off again, the scope it pushed is
    /// appended to `out.scopes` as a [`HeldScope`] whose parent is
    /// `out.held`, a [`SubKind::Leave`] frame keeps the old `out.held`
    /// in its `left` and in its `right` the floor `enter_poly` found
    /// (the `left` of its `LeavePoly` frame), `out.held` is the new row, and the pair of the
    /// bodies goes above the `Leave` frame under the same link. So a
    /// constraint made below it records the scopes that are open where
    /// it is made, and [`Checker::force_subtype`] opens them again
    /// (CHECKER_REWRITE 8.6, decision 120). O(1) plus the callee; 24
    /// bytes a scope entered. (R3j)
    fn subtype_poly(&mut self, out: &mut Coercion, [t1, t2]: [Ty; 2], d1: Node, d2: Node, link: u32) {
        todo!("R3j")
    }

    /// Two packages (compiler/ml/ctype.ml:4073-4100), `d1` and `d2`
    /// their descriptors:
    ///
    /// ```text
    ///         try
    ///           let ntl1 = complete_type_list env nl2 t1.level (Mty_ident p1) nl1 tl1
    ///           and ntl2 =
    ///             complete_type_list env nl1 t2.level (Mty_ident p2) nl2 tl2
    ///               ~allow_absent:true
    ///           in
    ///           let cstrs' =
    ///             List.map
    ///               (fun (n2, t2) ->
    ///                 (trace, List.assoc n2 ntl1, t2, !(current_univar_pairs ()), None))
    ///               ntl2
    ///           in
    ///           if eq_package_path env p1 p2 then cstrs' @ cstrs
    ///           else
    ///             (* need to check module subtyping *)
    ///             let snap = Btype.snapshot () in
    ///             try
    ///               List.iter (fun (_, t1, t2, _, _) -> unify env t1 t2) cstrs';
    ///               if !package_subtype env p1 nl1 tl1 p2 nl2 tl2 then (
    ///                 Btype.backtrack snap;
    ///                 cstrs' @ cstrs)
    ///               else raise (Unify [])
    ///             with Unify _ ->
    ///               Btype.backtrack snap;
    ///               raise Not_found
    ///         with Not_found ->
    ///           (trace, t1, t2, !(current_univar_pairs ()), None) :: cstrs)
    /// ```
    ///
    /// No supplier ([`Checker::packages`] is `None`): `constrain` of
    /// the two nodes, which unification then refuses. Otherwise one
    /// merge of the two name lists
    /// ([`super::rows::PackageDecls::compare`]), one
    /// [`SubKind::Constrain`] frame a name of `ntl2`, in name order
    /// (they are scratch above the length found: this body takes them
    /// off again before it returns), so that they are constrained, and
    /// so forced, last name first (`cstrs' @ cstrs`, reversed with the
    /// rest at 4231):
    /// - a name both list: the two arguments;
    /// - a name only the RIGHT lists: the left module type's answer at
    ///   the left node's level
    ///   ([`super::rows::PackageDecls::complete`]) and the right
    ///   argument; an answer that is no type ends the arm;
    /// - a name only the LEFT lists (`~allow_absent:true`): the left
    ///   argument and the right module type's answer at the right
    ///   node's level; [`super::rows::Completion::Abstract`] and
    ///   [`super::rows::Completion::Missing`] skip the name,
    ///   [`super::rows::Completion::Other`] ends the arm.
    ///
    /// Then, unless the two paths are one index or
    /// [`super::rows::PackageDecls::same_path`]: one speculation, each
    /// pair of the frames unified in name order,
    /// [`super::rows::PackageDecls::subtype`], and
    /// [`Checker::restore`] on either answer. The supplier is taken out
    /// of `Checker::packages` for the calls and put back.
    ///
    /// The scopes (CHECKER_REWRITE 8.6, decision 127). The `unify` of
    /// the trial is the typer's, which empties the list of scopes
    /// (`unify_pairs (ref env) ty1 ty2 []`, 2773), and the inclusion
    /// check runs `moregen` and `eqtype_list`, which empty it too
    /// (3089, 3358); nothing puts it back before the enclosing
    /// `enter_poly` ends (1675). So: [`Checker::empty_scopes`] before
    /// the first pair of the trial is unified (with no pair, only what
    /// the supplier's relations do); the supplier says nothing about
    /// what it ran. After the trial the frames are taken off: when the
    /// arm goes on, each is `constrain`ed, last name first, under the
    /// `out.held` the arm FOUND (`cstrs'` reads the list at 4083,
    /// before the trial). Then, when [`Checker::scope_floor`] is the
    /// length of [`Checker::scopes`] (no scope is read any more),
    /// `out.held` is `NONE`: every constraint made from here to the
    /// `Leave` frame of the enclosing polymorphic type records no
    /// scope, and a pair of universal variables among them clashes when
    /// it is forced (1559). The arm that ends (also on a clash of the
    /// trial or a `false`) then `constrain`s the two nodes, under no
    /// scope if the trial emptied them (4100 reads the list after the
    /// trial).
    ///
    /// Cost: O(names of both), one step a merge step, 16 bytes of frame
    /// a name, plus the supplier; for two paths the unifications and
    /// the restore. Cold. (R3j)
    #[cold]
    #[inline(never)]
    fn subtype_package(&mut self, out: &mut Coercion, [t1, t2]: [Ty; 2], d1: Node, d2: Node, link: u32) {
        todo!("R3j")
    }

    /// Fill [`Checker::subtype_trace`] with the pairs of the trace that
    /// ends in `link`, outermost first (`List.rev trace0`,
    /// compiler/ml/ctype.ml:4228): the chain of [`TraceLink`]s is
    /// followed to its root and the vector reversed. Nothing in
    /// `Mode::Success` (`link` is `NONE`). O(pairs of the trace), one
    /// step each. (R3j)
    #[cold]
    fn read_subtype_trace(&mut self, coercion: &Coercion, link: u32) {
        todo!("R3j")
    }

    /// `memq_warn t visited` (compiler/ml/ctype.ml:3409-3413) for the
    /// representative `ty`:
    ///
    /// ```text
    /// let memq_warn t visited =
    ///   if List.memq t visited then (
    ///     warn () := true;
    ///     true)
    ///   else false
    /// ```
    ///
    /// The entry of `ty` in [`Checker::path_entries`] (0 past its end):
    /// an object or a variant (`row`) is in `visited` when its entry is
    /// at or above `path.floor`, any other node when it is above
    /// `path.base` (CHECKER_REWRITE 8.13, "The visited list"). Sets
    /// `path.warn` when it answers true. O(1): one bounds test, one
    /// load, one compare; OCaml scans the list. (R3j)
    #[inline]
    fn on_path(&self, path: &mut EnlargePath, ty: Ty, row: bool) -> bool {
        todo!("R3j")
    }

    /// `let visited = t :: visited` for a node that is not an object or
    /// a variant (compiler/ml/ctype.ml:3441, 3458, 3479): `path_clock`
    /// one more, and that number as the entry of `ty`; the table grows
    /// to the graph's length when `ty` is past its end. Returns the
    /// entry `ty` had, which the node's leave frame puts back (an entry
    /// an enclosing cut has hidden is in `visited` again when the walk
    /// is back above the cut). O(1) amortized. (R3j)
    fn enter_path(&mut self, ty: Ty) -> u32 {
        todo!("R3j")
    }

    /// `t :: (if level' < level then [] else filter_visited visited)`
    /// for an object or a variant `ty` (compiler/ml/ctype.ml:3506-3508,
    /// 3543-3544; `filter_visited`, 3404-3407, drops the entries down to
    /// the nearest object or variant): `Checker::enter_path`, then
    /// `path.base` is the new entry, so that the nodes entered before
    /// it that are not rows are out of `visited`; with `cut` (`level' <
    /// level`) a frame `ENLARGE_FLOOR` that keeps `path.floor` is
    /// pushed and `path.floor` is the new entry too, so that the rows
    /// entered before it are out as well. Returns the entry `ty` had and
    /// the `path.base` there was, for the leave frame, which the caller
    /// pushes ABOVE the floor frame. O(1). (R3j)
    fn enter_row(&mut self, path: &mut EnlargePath, ty: Ty, cut: bool) -> (u32, u32) {
        todo!("R3j")
    }

    /// `has_constr_row' env t` after the expansion
    /// (compiler/ml/ctype.ml:3425; btype.ml:212: `(not (is_Tconstr t))
    /// && is_Tconstr (row_of_type t)`) for the representative
    /// `expansion`: whether it is an object whose field list ends in a
    /// constructor (`Checker::object_row`) or a variant whose row
    /// ([`Checker::flatten_row`] of the opened node, the scratch cut
    /// back) ends in one. O(fields) for an object or a variant, O(1)
    /// otherwise. (R3j)
    fn has_constr_row(&mut self, expansion: Ty) -> bool {
        todo!("R3j")
    }

    /// One node of `build_subtype env visited loops posi level t`
    /// (compiler/ml/ctype.ml:3427-3587) on the way down; `frame.state`
    /// holds `posi` and `level`. Either the node's result is pushed on
    /// [`Checker::enlarged`] at once, or a leave frame (`ENLARGE_LEAVE`,
    /// with `a` the entry the node had and `b` the `path.base` there
    /// was) and above it one frame a child, so that the children are
    /// popped in OCaml's order and leave one result each: a visit, or
    /// `ENLARGE_KEEP` for a child returned as it is, or
    /// `ENLARGE_FRESH` for a new variable with `Changed`.
    ///
    /// - A variable (3430-3437): itself, `Unchanged` (`loops` is
    ///   empty).
    /// - An arrow (3438-3454), a tuple (3455-3464): on the path
    ///   (`Checker::on_path`): itself. Otherwise
    ///   `Checker::enter_path`; an arrow's parameters with `posi`
    ///   turned, then its result.
    /// - A constructor whose type expands publicly, with `level > 0`,
    ///   whose [`Checker::expand_once`] in [`ExpandMode::Safe`] gives a
    ///   node that is not `Checker::has_constr_row` (3465-3471): a
    ///   leave frame with `a` 0 and no entry (the node is not added to
    ///   `visited`), and the visit of the expansion at `pred_expand
    ///   level`.
    /// - Any other constructor (3472-3500): on the path, itself.
    ///   Otherwise `enter_path`; with `level == 0`, `path.warn` when the
    ///   type expands publicly to a node that is not `has_constr_row`
    ///   (3482-3485: the expansion is made and memorized). A type
    ///   whose declaration the table does not have, or without
    ///   arguments: itself, the entry put back. Otherwise per argument
    ///   by [`super::expand::TypeTable::upper`]: both ways, kept;
    ///   negatively only, a visit with `posi` turned; positively only, a
    ///   visit; neither, a new variable.
    /// - A variant (3501-3537): on the path, or not static: itself.
    ///   Otherwise `Checker::enter_row` with `pred_enlarge level`, and
    ///   a visit at that level of the type of each present tag that
    ///   has one, in the order of the row.
    /// - An object (3538-3547): on the path, or its field list ends in
    ///   a variable, a universal variable or a constructor: itself.
    ///   Otherwise `enter_row` and the visit of the field list.
    /// - A field (3548-3575): its type kept when its cell is mutable,
    ///   visited otherwise; then the rest. No entry.
    /// - `Tnil` (3576-3582): with `posi` a new variable, `Changed`;
    ///   otherwise itself and `path.warn`.
    /// - A polymorphic type (3584-3586): the visit of the body.
    /// - A universal variable, a package (3587): itself.
    ///
    /// O(children) frames; one step a field of a variant read. (R3j)
    fn enlarge_visit(&mut self, frame: EnlargeFrame, path: &mut EnlargePath) {
        todo!("R3j")
    }

    /// One node of `build_subtype` on the way up: the results of its
    /// children are the last entries of [`Checker::enlarged`], in the
    /// order they were visited; they are replaced by the node's own.
    /// `c` is the greatest `change` of the children (`collect`,
    /// ctype.ml:3402).
    ///
    /// - An arrow, a tuple, a constructor with arguments, an object, a
    ///   polymorphic type: with `c > Unchanged` a new node of the same
    ///   kind at the current level over the children's results (an
    ///   arrow keeps each parameter's label and location; a constructor
    ///   gets an empty memo slot, `newconstr`; a polymorphic type its
    ///   bound variables), with `c`; otherwise the node, `Unchanged`.
    /// - An expanded constructor: the expansion's result when it is
    ///   above `Unchanged`, otherwise the constructor, `Unchanged`
    ///   (3470-3471).
    /// - A field (3560-3574): with `c > Unchanged` a new field node
    ///   with the name, the two results and a NEW cell holding the
    ///   value the field's cell has now (`ref (Mutability_value
    ///   (mutability_repr f.mutability))`: one cell node and one
    ///   descriptor row).
    /// - A variant: `Checker::enlarge_variant`, always `Changed`.
    ///
    /// Then the node's entry in [`Checker::path_entries`] is what the
    /// frame's `a` holds and `path.base` its `b` (an expanded
    /// constructor, a field and a polymorphic type made no entry and
    /// write the base they found). O(children); one node. (R3j)
    fn enlarge_leave(&mut self, frame: EnlargeFrame, path: &mut EnlargePath) {
        todo!("R3j")
    }

    /// The public expansion of constructor node `ty` when
    /// `build_subtype` may go through it (`safe_abbrev env t && not
    /// (has_constr_row' env t)`, compiler/ml/ctype.ml:3466-3468,
    /// 3483-3484): [`Checker::expand_once`] in [`ExpandMode::Safe`]; the
    /// representative of what it gives unless that is
    /// `Checker::has_constr_row`; otherwise `NONE`. The cost of the
    /// expansion (a memo hit the second time). (R3j)
    fn enlarge_expansion(&mut self, ty: Ty) -> Ty {
        todo!("R3j")
    }

    /// The leave of a static variant (compiler/ml/ctype.ml:3510-3537);
    /// `frame.state` holds `posi` and the `level` the node was entered
    /// with:
    ///
    /// ```text
    ///       let fields = filter_row_fields false row.row_fields in
    ///       let fields =
    ///         List.map
    ///           (fun ((l, f) as orig) ->
    ///             match row_field_repr f with
    ///             | Rpresent None ->
    ///               if posi then ((l, Reither (true, [], false, ref None)), Unchanged)
    ///               else (orig, Unchanged)
    ///             | Rpresent (Some t) ->
    ///               let t', c = build_subtype env visited loops posi level' t in
    ///               let f =
    ///                 if posi && level > 0 then Reither (false, [t'], false, ref None)
    ///                 else Rpresent (Some t')
    ///               in
    ///               ((l, f), c)
    ///             | _ -> assert false)
    ///           fields
    ///       in
    ///       let c = collect fields in
    ///       let row =
    ///         {
    ///           row_fields = List.map fst fields;
    ///           row_more = newvar ();
    ///           row_closed = posi;
    ///           row_fixed = false;
    ///           row_name = (if c > Unchanged then None else row.row_name);
    ///         }
    ///       in
    ///       (newty (Tvariant row), Changed)
    /// ```
    ///
    /// The row is flattened again; the results of its typed tags are
    /// the last entries of [`Checker::enlarged`], in the order of the
    /// row. One new UNOPENED variant node at the current level (each of
    /// its `Either` fields stands for a reference of its own, `ref
    /// None`; "The reference of a variant field", rows.rs): one
    /// `RowFieldRow` a tag that is not absent, the slots of the typed
    /// tags' results in order, a new variable as `more`, and the
    /// arguments of the row's name when the name is kept (those of the
    /// LAST node of the chain). Its result is always `Changed`. Cost:
    /// the flattening and two steps a tag; one node, one variable, one
    /// descriptor row, one `VariantRow`. (R3j)
    fn enlarge_variant(&mut self, frame: EnlargeFrame) {
        todo!("R3j")
    }

    /// The table of pairs and the renaming of a relation that starts
    /// (`Type_pairs.create`, compiler/ml/ctype.ml:3115 for `moregeneral`
    /// and 3370 for `equal`, and `ref []` for the renaming of `equal`,
    /// 3370: a table and a list a call). `moregen` and `equal` call it
    /// before they clear [`Checker::related`], and
    /// [`Checker::leave_relation`] on every way out. The first relation
    /// (no other is running) moves nothing: one load, one branch, one
    /// store. A relation entered while another runs (the inclusion
    /// check of two packages, from `package_end`: the supplier is
    /// handed this checker) puts the running one's table, its list
    /// [`Checker::renamed`] and its `renaming_trail` on
    /// [`Checker::related_shelf`] and takes emptied ones from
    /// [`Checker::related_spare`], or new ones that have allocated
    /// nothing. Subtyping has [`Checker::subtyped`] and unification no
    /// table, so only a relation inside a relation moves one.
    /// (CHECKER_REWRITE 8.6, decision 128)
    #[inline]
    pub fn enter_relation(&mut self) {
        if self.relating != 0 {
            self.shelve_related();
        }
        self.relating += 1;
    }

    /// The end of a relation [`Checker::enter_relation`] started; call
    /// it after the relation's speculation is restored. When it ran
    /// inside another, its table and list are emptied and kept for the
    /// next one, and the outer relation has its own again, its renaming
    /// written under a new generation. O(1) for the first relation; for
    /// a nested one the clear of its table and one step a pair of the
    /// outer renaming.
    #[inline]
    pub fn leave_relation(&mut self) {
        self.relating -= 1;
        if self.relating != 0 {
            self.unshelve_related();
        }
    }

    /// O(1): the nested case of [`Checker::enter_relation`].
    #[cold]
    #[inline(never)]
    fn shelve_related(&mut self) {
        let inner = self.related_spare.pop().unwrap_or_default();
        self.related_shelf.push(Shelved {
            related: std::mem::replace(&mut self.related, inner.related),
            renamed: std::mem::replace(&mut self.renamed, inner.renamed),
            trail: self.renaming_trail,
        });
    }

    /// The nested case of [`Checker::leave_relation`]. The rows of
    /// [`Checker::renaming`] are live by generation and the inner
    /// relation may have taken generations and written rows of nodes
    /// the outer one had renamed: the outer list is put back and every
    /// pair of it is written again under a NEW generation, as it stands
    /// (not normalized: `renaming_trail` is the outer one's again, so
    /// `normalize_renaming` still sees what the outer relation has not
    /// seen). O(capacity of the inner table + pairs of the outer
    /// renaming), one step a pair.
    #[cold]
    #[inline(never)]
    fn unshelve_related(&mut self) {
        let outer = self.related_shelf.pop().expect("the state of the outer relation");
        let mut inner = Shelved {
            related: std::mem::replace(&mut self.related, outer.related),
            renamed: std::mem::replace(&mut self.renamed, outer.renamed),
            trail: 0,
        };
        inner.related.keys.clear();
        inner.renamed.clear();
        self.related_spare.push(inner);
        self.renaming_trail = outer.trail;
        let generation = self.next_renaming_generation();
        for at in 0..self.renamed.len() {
            #[cfg(test)]
            super::steps::tick();
            let [a, b] = self.renamed[at];
            self.renaming_covers(a.0.max(b.0));
            let row = &mut self.renaming[a.0 as usize];
            (row.left, row.partner) = (generation, b.0);
            self.renaming[b.0 as usize].right = generation;
        }
    }
}

/// What a relation that waits for a relation entered inside it has put
/// aside (`Checker::related_shelf`): its table of pairs, the pairs of
/// its renaming in the order they were added, and the length of the
/// trail when they were last normalized. (CHECKER_REWRITE 8.6, decision
/// 128)
#[derive(Default)]
pub struct Shelved {
    pub related: super::unify::PairSet,
    pub renamed: Vec<[Ty; 2]>,
    pub trail: usize,
}

/// The end of a row in `Checker::subtype_row`, beside the tags `VAR`
/// and `CONSTR`: `Tnil`, a universal variable, anything else.
const NIL_END: u32 = 16;
const UNIVAR_END: u32 = 17;
const OTHER_END: u32 = 18;

/// What one [`Checker::subtype`] collects and [`Checker::force_subtype`]
/// unifies (the closure of compiler/ml/ctype.ml:4219-4231 as data). The
/// caller owns it and may use it again: `subtype` empties it first. A
/// caller that never forces drops it or passes it again; the checker
/// holds nothing of it. (R3j; CHECKER_REWRITE 8.13)
pub struct Coercion {
    /// The constraints in the order they are unified (`List.rev cstrs`).
    pub constraints: Vec<Constraint>,
    /// The traces of the pairs walked, `Mode::Explain` only: OCaml's
    /// `trace` is a list whose tail every deeper pair shares; here the
    /// tail is the `parent` of a row.
    pub links: Vec<TraceLink>,
    /// The scopes of universal variables entered, each with the one
    /// around it (`!(current_univar_pairs ())` as a constraint keeps
    /// it).
    pub scopes: Vec<HeldScope>,
    /// Walk state, all three as below between calls. How many quiet
    /// regions are open: an invariant argument's two directions, whose
    /// constraints are counted and dropped (`subtype_rec ... [] = []`,
    /// ctype.ml:3689-3690), or the tags of a row before its `Exit`.
    pub quiet: u32,
    /// The innermost scope open: an index of `scopes`, or `NONE`, which
    /// also stands for "emptied" (the floor of the checker's scopes is
    /// their length: an entry that empties OCaml's list ran inside the
    /// polymorphic type the walk is in).
    pub held: u32,
    /// Whether the innermost quiet region has made a constraint.
    pub dirty: bool,
}

impl Default for Coercion {
    /// O(1): nothing collected; allocates nothing.
    fn default() -> Self {
        Coercion { constraints: Vec::new(), links: Vec::new(), scopes: Vec::new(), quiet: 0, held: NONE, dirty: false }
    }
}

/// One pair of a trace of `subtype_rec` (`(t1, t2) :: trace`): 12 bytes,
/// one a pair pushed in `Mode::Explain`. `parent` is the rest of the
/// trace, an index of [`Coercion::links`] or `NONE`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct TraceLink {
    pub left: Ty,
    pub right: Ty,
    pub parent: u32,
}

/// One scope of universal variables a constraint was made under: 24
/// bytes, one a scope `subtype_rec` enters (ctype.ml:4067-4070).
/// `parent` is the scope around it, an index of [`Coercion::scopes`] or
/// `NONE`. The partner nodes of `scope` are nodes of the graph, so every
/// constraint that holds the scope sees the pairings the ones before it
/// made, as OCaml's constraints share the `ref`s of one list.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct HeldScope {
    pub scope: super::rows::PolyScope,
    pub parent: u32,
}

/// What a [`SubFrame`] asks for when it is popped
/// (`Checker::subtype_frames`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum SubKind {
    /// `subtype_rec env trace left right cstrs`; `link` is `trace`.
    Pair,
    /// `(trace, left, right, ...) :: cstrs`, put off until the frames
    /// above it are popped.
    Constrain,
    /// Leave the innermost scope of universal variables; `left` is the
    /// `Coercion::held` to put back and `right` the floor of the scopes
    /// to put back ([`Checker::scope_floor`] as `enter_poly` found it).
    Leave,
    /// An invariant argument, before its first direction.
    Invariant,
    /// An invariant argument, after its first direction.
    Back,
    /// The end of a quiet region; `dirty` is the `Coercion::dirty` to
    /// put back. `left` is `NONE` for the region of a row.
    Close,
}

/// One entry of [`Checker::subtyping`]: 16 bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct SubFrame {
    pub left: Ty,
    pub right: Ty,
    /// The trace: an index of [`Coercion::links`], or `NONE`.
    pub link: u32,
    pub kind: SubKind,
    pub dirty: bool,
}

/// `change` of `build_subtype` (compiler/ml/ctype.ml:3398), ordered as
/// OCaml orders it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u32)]
pub enum Change {
    Unchanged,
    Equiv,
    Changed,
}

/// The result of one node of `build_subtype`: 8 bytes, on
/// [`Checker::enlarged`] until the node above it is left.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct Enlarged {
    pub ty: Ty,
    pub change: Change,
}

/// One entry of [`Checker::enlarging`]: 16 bytes. `state` is one of the
/// five kinds below in its low three bits, [`ENLARGE_POSI`], the level
/// (the expansion budget, 0 to 4) from bit [`ENLARGE_LEVEL`], and for a
/// leave frame [`ENLARGE_EXPANDED`] and [`ENLARGE_ENTERED`]. For a
/// leave frame `a` is the entry the node had in
/// [`Checker::path_entries`] and `b` the `EnlargePath::base` to put
/// back; for a floor frame `a` is the `EnlargePath::floor` to put back.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct EnlargeFrame {
    pub ty: Ty,
    pub a: u32,
    pub b: u32,
    pub state: u32,
}

/// `build_subtype env visited loops posi level ty`, pending.
pub const ENLARGE_VISIT: u32 = 0;
/// The children of `ty` are done.
pub const ENLARGE_LEAVE: u32 = 1;
/// Put `EnlargePath::floor` back.
pub const ENLARGE_FLOOR: u32 = 2;
/// The result is `ty` itself, `Unchanged`.
pub const ENLARGE_KEEP: u32 = 3;
/// The result is a new variable, `Changed` (ctype.ml:3494).
pub const ENLARGE_FRESH: u32 = 4;
/// The three bits of the kind.
pub const ENLARGE_KIND: u32 = 7;
/// `posi`.
pub const ENLARGE_POSI: u32 = 8;
/// The shift of the level.
pub const ENLARGE_LEVEL: u32 = 4;
/// A leave frame of a constructor that was expanded (ctype.ml:3470-3471).
pub const ENLARGE_EXPANDED: u32 = 1 << 7;
/// A leave frame of a node that made an entry on the path.
pub const ENLARGE_ENTERED: u32 = 1 << 8;

/// O(1): the `state` of a frame of kind `kind` with `posi` and `level`.
#[inline]
pub fn enlarge_state(kind: u32, posi: bool, level: u32) -> u32 {
    kind | if posi { ENLARGE_POSI } else { 0 } | level << ENLARGE_LEVEL
}

/// `visited` and `warn` of one `build_subtype` walk
/// (compiler/ml/ctype.ml:3427, 3394), held by `Checker::enlarge_type`:
/// 12 bytes. A node that is not an object or a variant is in `visited`
/// when its entry is above `base`; an object or a variant when its
/// entry is at or above `floor` (CHECKER_REWRITE 8.13, "The visited
/// list").
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct EnlargePath {
    pub base: u32,
    pub floor: u32,
    pub warn: bool,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sizes() {
        // R3j: 8.13.
        assert_eq!(std::mem::size_of::<Constraint>(), 16);
        assert_eq!(std::mem::size_of::<TraceLink>(), 12);
        assert_eq!(std::mem::size_of::<HeldScope>(), 24);
        assert_eq!(std::mem::size_of::<SubKind>(), 1);
        assert_eq!(std::mem::size_of::<SubFrame>(), 16);
        assert_eq!(std::mem::size_of::<Change>(), 4);
        assert_eq!(std::mem::size_of::<Enlarged>(), 8);
        assert_eq!(std::mem::size_of::<EnlargeFrame>(), 16);
        assert_eq!(std::mem::size_of::<EnlargePath>(), 12);
        assert_eq!(std::mem::size_of::<Relation>(), 2);
        assert_eq!(std::mem::size_of::<Renamed>(), 12);
    }
}
