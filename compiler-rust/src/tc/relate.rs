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
use super::graph::{CONSTR, GENERIC, LINK, NONE, Node, Ty, VAR};
use super::rows::{RES_ABSENT, RES_PRESENT, cell_mutable, cell_repr, each_field_types, either_flags, field_repr};
use super::segment::{EXTENDED, ExtraDescriptor, RowFieldKind, VariantRow};
use super::unify::{Checker, Clash, Frame, FrameKind};

/// One delayed constraint of subtyping (`cstrs`,
/// compiler/ml/ctype.ml:3647): 12 bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct Constraint {
    pub left: Ty,
    pub right: Ty,
    /// Length of the trace when the constraint was made, `Mode::Explain`.
    pub trace: u32,
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
        todo!("R3i")
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
        todo!("R3i")
    }

    /// The outer `moregen` (compiler/ml/ctype.ml:3091-3094: `Must empty
    /// univar_pairs first`) with the pair table of `moregeneral`
    /// (`Type_pairs.create 13`, ctype.ml:3119) and its `try ... with Unify
    /// _ -> false`: whether the instance `pattern` can be instantiated to
    /// `subject`, linking the variables [`may_instantiate`] allows. For a
    /// caller that made the two instances itself (from two templates).
    /// [`Checker::related`] is cleared; the pair goes on
    /// [`Checker::frames`] and [`Checker::relate_frames`] runs; on a
    /// failure the frames, `saved`, the scopes of universal variables
    /// and the trace are cut back to what they were at the entry. OCaml
    /// EMPTIES its list of scopes at this entry (`current_univar_pairs ()
    /// := []`, ctype.ml:3093) and does not put the old value back, which
    /// is the same only when no scope is open: the body asserts it in
    /// debug builds, and no caller may enter with one open. What
    /// was linked stays, on either answer. Cost: O(pairs visited), each
    /// one [`Checker::moregen_pair`]; one hash insertion a pair that is
    /// not decided at its first test. (R3i)
    pub fn moregen(&mut self, inst_nongen: bool, pattern: Ty, subject: Ty) -> bool {
        todo!("R3i")
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
    /// undo). No scope of universal variables is open at the entry
    /// (asserted in debug builds: OCaml empties its list there, 3363, and
    /// the kernel only cuts `scopes` back to its length at the entry).
    /// Otherwise one speculation, [`Checker::related`] cleared,
    /// with `rename` a new generation of [`Checker::renaming`], the pairs
    /// pushed last first, [`Checker::relate_frames`], and
    /// [`Checker::restore`] on either answer: nothing `equal` wrote stays
    /// (an expansion, a compressed path, an opened row), and the memos
    /// are cleaned when something was written, as `backtrack` cleans
    /// them. Cost: O(pairs visited), each one [`Checker::eqtype_pair`],
    /// one hash insertion a pair not decided at its first test, plus the
    /// restore (one step a write). (R3i)
    pub fn equal(&mut self, rename: bool, left: &[Ty], right: &[Ty]) -> bool {
        todo!("R3i")
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
    /// variables), [`Checker::cleanup_abbrev`], [`Checker::unify`],
    /// [`Checker::all_distinct_vars`], the trace cut back to its length
    /// at the entry, [`Checker::restore`] on either answer. The
    /// unification runs inside the speculation, so a failure in
    /// `Mode::Success` does not set `unexplained_failure`. Cost: the
    /// walk of `ty`, one unification, one expansion a variable, the
    /// restore. (R3i)
    pub fn matches(&mut self, ty: Ty, pattern: Ty) -> bool {
        todo!("R3i")
    }

    /// Run [`Checker::relate_frames`] above `base` and, on a clash, cut
    /// [`Checker::frames`] back to `base`. On either answer `saved`, the
    /// scopes of universal variables (`univar_pairs := old_univars`,
    /// compiler/ml/ctype.ml:1677-1679) and the trace (a callee that
    /// clashed in `Mode::Explain` pushed its pair; 8.6, decision 25) go
    /// back to their lengths at the entry. O(1) plus the walk. (R3i)
    fn relate_run(&mut self, relation: Relation, base: usize) -> bool {
        todo!("R3i")
    }

    /// The loop of `moregen` and `eqtype`: pop the frames above `base`
    /// until none is left or one clashes (the frames then stay; the
    /// caller cuts them).
    ///
    /// - A [`FrameKind::Pair`] frame: the two representatives; nothing when they
    ///   are one node (`if t1 == t2 then ()`, compiler/ml/ctype.ml:2926,
    ///   2930, 3201, 3205), otherwise [`Checker::moregen_pair`] or
    ///   [`Checker::eqtype_pair`].
    /// - A [`FrameKind::LeavePoly`] frame: `scopes` is cut to the frame's `extra`
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
        todo!("R3i")
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
        todo!("R3i")
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
        todo!("R3i")
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
        todo!("R3i")
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
        todo!("R3i")
    }

    /// O(1): whether `node` (a descriptor) is a variant node.
    #[inline]
    fn is_variant(&self, node: Node) -> bool {
        todo!("R3i")
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
        todo!("R3i")
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
        todo!("R3i")
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
        todo!("R3i")
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
        todo!("R3i")
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
        todo!("R3i")
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
        todo!("R3i")
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
        todo!("R3i")
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
        todo!("R3i")
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
        todo!("R3i")
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
        todo!("R3i")
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
        todo!("R3i")
    }

    /// `subtype` (compiler/ml/ctype.ml:4216-4225) without the checks that
    /// read a declaration's labels or constructors (those belong to R6e,
    /// see "R3 as designed", decision 6): collect the constraints of
    /// `left :> right` into `out` (`subtype_rec`, ctype.ml:3647). O(pairs),
    /// pair set, explicit stack. (R3j)
    pub fn subtype(&mut self, left: Ty, right: Ty, out: &mut Vec<Constraint>) -> Result<(), Clash> {
        todo!("R3j")
    }

    /// Unify the delayed constraints, in order (the closure `subtype`
    /// returns, compiler/ml/ctype.ml:4221-4225). O(constraints) plus the
    /// unifications. (R3j)
    pub fn force_subtype(&mut self, constraints: &[Constraint]) -> Result<(), Clash> {
        todo!("R3j")
    }

    /// `enlarge_type` (compiler/ml/ctype.ml:3593-3613): the supertype a
    /// coercion without a source annotation goes to, and whether it is the
    /// type itself (`build_subtype`, ctype.ml:3431). O(nodes), marks. (R3j)
    pub fn enlarge_type(&mut self, ty: Ty) -> (Ty, bool) {
        todo!("R3j")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sizes() {
        assert_eq!(std::mem::size_of::<Constraint>(), 12);
        assert_eq!(std::mem::size_of::<Relation>(), 2);
        assert_eq!(std::mem::size_of::<Renamed>(), 12);
    }
}
