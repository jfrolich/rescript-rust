//! R3 skeleton: unification on the new graph. Bodies are built by slices
//! R3a, R3c and R3e to R3h (CHECKER_REWRITE.md, "R3 as designed"); every
//! signature, size and stated cost here is fixed.
//!
//! The order of work is OCaml's (compiler/ml/ctype.ml:2227-2440): a link is
//! written before the children are unified, in the direction OCaml writes
//! it. Recursion is an explicit stack of [`Frame`]s, popped in the order the
//! recursive calls would run.

use super::expand::{
    ABBREV, ALIAS, DATATYPE, ExpandMode, INHERITS, LOCAL, Memo, NEWTYPE, PRIVATE, TypeTable, link_node,
};
use super::graph::{
    ARROW, CONSTR, Change, GENERIC, Graph, LINK, Mode, NONE, Node, Speculation, TUPLE, Ty, VAR,
};
use super::rows::{Extras, PolyScope};
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

/// The node budget of [`Checker::unreached_within_budget`]: `walk_budget`
/// (compiler/ml/ctype.ml:1424).
const PROBE_BUDGET: u32 = 256;

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
    /// Leave a scope of universal variables: [`Checker::scopes`] is cut
    /// back to `extra` entries (`univar_pairs := old_univars`,
    /// compiler/ml/ctype.ml:1675). Pushed by [`Checker::enter_poly`] below
    /// the pair of the two bodies; `left` and `right` are `NONE`. It
    /// carries no trace pair and no swap: the pair of the two polymorphic
    /// types is the [`FrameKind::Linked`] frame below it, which is what
    /// reverses the entries of a failure in the bodies. When a frame above
    /// it fails, [`Checker::unify_distinct`] cuts the scopes back
    /// (`Checker::leave_scopes`). (R3g)
    LeavePoly,
    /// After the children: the `create_recursion` repair of
    /// compiler/ml/ctype.ml:2428-2436 for the pair (R3c).
    Recursion,
    /// Below everything one [`Checker::unify_fields`] pushed,
    /// `Mode::Explain` only: `left` and `right` are the two rests and
    /// `extra` indexes [`Checker::saved`]: their two descriptors, put back
    /// when a frame above fails (`rest1.desc <- d1; rest2.desc <- d2`,
    /// compiler/ml/ctype.ml:2513-2517). Popped: nothing to undo. (R3e)
    Fields,
    /// One common field of two rows: `left` and `right` are the two field
    /// nodes, `extra` bit 0 is `open1` and bit 1 `open2`
    /// ([`Checker::unify_field`]). (R3e)
    Field,
    /// Below the frames of a common field's types, `Mode::Explain` only:
    /// `left` and `right` are the two field nodes, whose pair goes into the
    /// trace when a frame above fails (compiler/ml/ctype.ml:2493-2510).
    /// Popped: nothing. (R3e)
    FieldEnd,
    /// One common tag of two variant rows: `left` and `right` are the list
    /// indices of slot 0 of the two homes, `extra` indexes
    /// [`Checker::saved`]: one record ([`Checker::unify_row`], step 9).
    /// Popped: [`Checker::unify_row_field`]. (R3f)
    RowField,
    /// Below the frames of a common tag, in every mode: popped,
    /// [`Checker::row_field_end`]; when a frame above fails in
    /// `Mode::Explain`, the pair of the two fields goes into the trace
    /// (compiler/ml/ctype.ml:2622-2628). (R3f)
    RowFieldEnd,
    /// Below the common tags of a closed row 1: `left` is the right node
    /// of the pair. Popped: [`Checker::row_end`]. (R3f)
    RowEnd,
    /// Below the pairs of the completed type lists of two packages:
    /// `left` and `right` are the two package nodes, `extra` indexes
    /// [`Checker::saved`]: the descriptor the left node had. Popped:
    /// [`Checker::package_end`]. (R3p)
    PackageEnd,
    /// Pattern mode, below the pairs of the arguments of two
    /// constructors of one type: `extra` holds the two flags as they
    /// were (bit 0 `generate_equations`, bit 1 `assume_injective`).
    /// Popped: the flags are put back (`set_mode_pattern`,
    /// compiler/ml/ctype.ml:256-273). (R3h; CHECKER_REWRITE 8.9,
    /// decision 64)
    Flags,
    /// Pattern mode, `Mode::Explain` only, below the children of a
    /// structure pair that was assumed equal and not linked: `left` and
    /// `right` are the pair of the enclosing `unify` call, in its order,
    /// for the trace (compiler/ml/ctype.ml:2274); bit 31 of `extra`
    /// (`SWAPPED`) as for [`FrameKind::Linked`]. It holds no descriptor:
    /// nothing of the pair's nodes was written. Popped: nothing. (R3h;
    /// CHECKER_REWRITE 8.9, decision 64)
    Assumed,
    /// Pattern mode, one attempt that falls back: `left` and `right` are
    /// the two types to reify when it fails. The frame is pushed
    /// PENDING, with [`TRY_ARGUMENT`] or [`TRY_ROWS`] as its `extra`, and
    /// is popped twice (`Checker::try_frame`): the first pop STARTS the
    /// attempt (the snapshot is taken when the attempt is reached, after
    /// everything pushed above the frame has run) and pushes the frame
    /// again with the index of its [`Try`] record as `extra`, below what
    /// is tried; the second pop means the attempt succeeded.
    /// [`Checker::recover`] says what a clash above a started frame
    /// does. (R3r; CHECKER_REWRITE 8.9, decision 68)
    Try,
    /// Pattern mode: the pair popped just above this frame turned the
    /// tracing of GADT instances on (`check_trace_gadt_instances` at the
    /// top of `unify`, compiler/ml/ctype.ml:2235), and everything that
    /// pair pushed has run. Popped: tracing is off again
    /// (`reset_trace_gadt_instances reset_tracing`, ctype.ml:2269).
    /// `left`, `right` and `extra` hold nothing. Pushed by
    /// `Checker::late_pair` only. (R3s; CHECKER_REWRITE 8.11, decision
    /// 105)
    Untrace,
}

/// One STARTED attempt of pattern mode that falls back on a clash (`let
/// snap = snapshot () in try ... with Unify _ -> backtrack snap; reify
/// ...`, compiler/ml/ctype.ml:2364-2375 for an argument that is not
/// injective, 2402-2411 for two variants). 40 bytes; one per attempt
/// that is started and not yet finished. (R3r; CHECKER_REWRITE 8.9,
/// decision 68)
#[derive(Debug)]
pub struct Try {
    /// What the graph is restored to.
    pub speculation: super::graph::Speculation,
    /// Index of the started [`FrameKind::Try`] frame in `frames`.
    pub frame: u32,
    /// The lengths of `trace`, `saved` and `scopes` when it was started.
    pub trace: u32,
    pub saved: u32,
    pub scopes: u32,
    /// Bit 0 `generate_equations`, bit 1 `assume_injective`, as they
    /// were; bit 2: `mcomp` follows the reification when
    /// `generate_equations` is on after the flags are put back; bit 3:
    /// GADT instances were traced ([`GADT_TRACING`]; R3s).
    pub flags: u8,
}

/// `extra` of a pending [`FrameKind::Try`] frame: the attempt of an
/// argument whose parameter is not injective (compiler/ml/ctype.ml:
/// 2364-2375). Started, both flags are off (`set_mode_pattern
/// ~generate:false ~injective:false`) and the pair of the two arguments
/// is what is tried; the fallback is `reify` of both.
pub const TRY_ARGUMENT: u32 = 1 << 31;
/// `extra` of a pending [`FrameKind::Try`] frame: the attempt of two
/// variants (compiler/ml/ctype.ml:2402-2411). Started, the flags are as
/// they are, both rows are opened and `unify_row` is what is tried; the
/// fallback is `reify` of both and, with `generate_equations` on,
/// `mcomp`. A record index stays below both bits.
pub const TRY_ROWS: u32 = 1 << 30;

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

impl PairSet {
    /// O(1): the key of the pair of two nodes whatever their order, the
    /// smaller index in the high half (`order_type_pair`,
    /// compiler/ml/ctype.ml:2105: `if t1.id <= t2.id then (t1, t2) else
    /// (t2, t1)`; the kernel's index is OCaml's `id` for this purpose, a
    /// total order on nodes).
    #[inline]
    pub fn key(left: Ty, right: Ty) -> u64 {
        let (low, high) = if left.0 <= right.0 {
            (left.0, right.0)
        } else {
            (right.0, left.0)
        };
        u64::from(low) << 32 | u64::from(high)
    }
}

/// [`Checker::gadt`]: the environment has a local constraint
/// (`Env.has_local_constraints`, compiler/ml/env.ml:1047): an equation, a
/// type `reify` made or an existential type of a constructor pattern.
pub const GADT_LOCAL: u8 = 1;
/// [`Checker::gadt`]: GADT instances are traced (`trace_gadt_instances`,
/// compiler/ml/ctype.ml:176-177).
pub const GADT_TRACING: u8 = 2;
/// [`Checker::gadt`]: a member was pushed on an instance set in this
/// unit. Never cleared: an addition that was undone leaves it set.
pub const GADT_MEMBER: u8 = 4;
/// [`Checker::gadt`]: `umode` is [`UnifyMode::Pattern`]. Kept by
/// [`Checker::unify_pattern`], the one writer of `umode`.
pub const GADT_PATTERN: u8 = 8;

/// One scope of GADT instances (`Env.add_gadt_instance_level`,
/// compiler/ml/env.ml:1307-1308: `(lv, ref Type_set.empty) ::
/// env.gadt_instances`). 12 bytes; one per scope entered in the unit.
/// (R3s; CHECKER_REWRITE 8.11, decision 98)
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct InstanceScope {
    pub level: u32,
    /// The scope around this one, or `NONE`.
    pub parent: u32,
    /// A variable node of the graph whose `b` is the index of the
    /// scope's newest [`InstanceMember`], or `NONE`: written with
    /// `Graph::write`, so that a restore undoes an addition.
    pub head: Ty,
}

/// One member of a set of instances. 8 bytes; one per addition, also
/// one a restore undid (its row is not reached again).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct InstanceMember {
    pub ty: Ty,
    /// The member added before this one, or `NONE`.
    pub next: u32,
}

/// What [`Checker::leave_case`] puts back: the environment of a case as
/// it was. 12 bytes, held by the walk on its own stack, one a case.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct CaseMark {
    pub equations: u32,
    pub scope: u32,
    /// `Checker::gadt & GADT_LOCAL` as it was.
    pub local: u8,
}

/// One checker context: the graph and everything unification reads.
/// A worker owns one and resets it between units.
pub struct Checker {
    pub g: Graph,
    pub types: TypeTable,
    pub memo: Memo,
    pub extras: Extras,
    pub umode: UnifyMode,
    /// [`GADT_LOCAL`], [`GADT_TRACING`], [`GADT_MEMBER`],
    /// [`GADT_PATTERN`]: 0 for a unit that never had a local constraint
    /// outside a pattern unification. The one byte every site of GADT
    /// instances reads (CHECKER_REWRITE 8.11, the table of sites). (R3s)
    pub gadt: u8,
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
    /// Membership marks of an instance set, indexed by node; a mark is
    /// set when it equals `instance_mark_generation`. Read and written
    /// by `Checker::add_instance_chain` and [`Checker::copy_in`] only.
    /// Not `marks`: `non_recursive_abbrev`, `occur_expanding`,
    /// `occur_pattern` and `lower_args_walk` hold a generation of
    /// `marks` across an expansion that can add a chain to a set, and
    /// OCaml's walks keep theirs apart from its `Type_set`s
    /// (compiler/ml/ctype.ml:1393-1394, 1505, 1511; typecore.ml:2505).
    /// Empty until a unit adds a chain or copies with a member. (R3s)
    pub instance_marks: Vec<u32>,
    pub instance_mark_generation: u32,
    pub pairs: PairSet,
    /// `univar_pairs` (compiler/ml/ctype.ml:1681): the open scopes of
    /// universal variables, innermost last. Empty between top-level
    /// unifications: [`FrameKind::LeavePoly`] pops a scope, a failure cuts
    /// back to the scopes it found (`Checker::leave_scopes`). (R3g)
    pub scopes: Vec<PolyScope>,
    /// Where `univar_pairs` starts in [`Checker::scopes`]: the scopes
    /// below this index are those OCaml's list no longer holds, because
    /// an entry that starts with `univar_pairs := []` ran inside a
    /// polymorphic body (compiler/ml/ctype.ml:2737, 2770 with 2773,
    /// 3089, 3358, 4214; [`Checker::empty_scopes`]). They stay in the
    /// vector because `enter_poly` puts its `old_univars` back at its
    /// exit (1675, 1678): each [`FrameKind::LeavePoly`] frame holds the
    /// floor its entry found, in `left`, and puts it back
    /// ([`Checker::leave_poly`]). `unify_univar`, `enter_poly` and
    /// `univars_escape` read the scopes from this index on. 0 in a unit
    /// that never empties inside a polymorphic body. (CHECKER_REWRITE
    /// 8.6, decision 127)
    pub scope_floor: u32,
    /// What [`Checker::unify_package`] asks about module types; `None`
    /// until a caller that has declarations sets it (R5a). (R3p)
    pub packages: Option<Box<dyn super::rows::PackageDecls>>,
    /// `current_newtype_level` (compiler/ml/ctype.ml:1802-1808): the level
    /// of the pattern being typed, or 0 outside
    /// [`Checker::unify_pattern`] (`None`; no node is at level 0). (R3h)
    pub newtype_level: u32,
    /// The equations in force, oldest first (the local constraints of
    /// `Env`, compiler/ml/ctype.ml:2093-2100). Empty for a unit that
    /// never typed a pattern with an equation; `equations.len()` is what
    /// a caller keeps to cut back to ([`Checker::cut_equations`]). (R3h)
    pub equations: Vec<super::rows::Equation>,
    /// What `reify` and `mcomp` ask about declarations; `None` until a
    /// caller that has declarations sets it (R5a). (R3h)
    pub locals: Option<Box<dyn super::rows::LocalDecls>>,
    /// The open attempts of pattern mode, innermost last; empty outside
    /// a pattern unification. (R3r)
    pub tries: Vec<Try>,
    /// The pairs `mcomp` assumes compatible, ordered (left, right) in
    /// one `u64` each; empty outside a call of it. (R3r)
    pub compatible: PairSet,
    /// The scopes of GADT instances entered in this unit
    /// (`env.gadt_instances`, innermost first through `parent`). (R3s)
    pub instance_scopes: Vec<InstanceScope>,
    /// The innermost scope of the environment the caller is in: an index
    /// of `instance_scopes`, or `NONE`. (R3s)
    pub instance_scope: u32,
    /// The pool of members; a scope's list starts at its head node. (R3s)
    pub instance_members: Vec<InstanceMember>,
    /// The pairs a relation of `relate.rs` has visited (`type_pairs` of
    /// `moregen`, `eqtype` and `subtype_rec`, compiler/ml/ctype.ml:2925,
    /// 3200, 3647): ordered pairs, the left node in the high half of the
    /// key. A hash set because no dense index of pairs exists. Cleared
    /// at the entry of each relation (`Type_pairs.create`,
    /// ctype.ml:3119, 3374; `TypePairs.clear subtypes`, 4217); not
    /// `pairs` or `compatible`, which pattern mode owns. (R3i, R3j)
    pub related: PairSet,
    /// How many relations are running: 0 outside
    /// [`Checker::enter_relation`] and [`Checker::leave_relation`].
    /// (CHECKER_REWRITE 8.6, decision 128)
    pub relating: u32,
    /// The tables and renamings of the relations that are waiting for a
    /// relation entered inside them (through the inclusion check of two
    /// packages), outermost first; empty unless a relation runs inside
    /// a relation.
    pub related_shelf: Vec<super::relate::Shelved>,
    /// What nested relations used, emptied, for the next ones: at most
    /// as many as relations were ever nested.
    pub related_spare: Vec<super::relate::Shelved>,
    /// The renaming of `equal` with `rename` (`subst`, compiler/ml/
    /// ctype.ml:3200-3215): one row a node, live by
    /// `renaming_generation`. Empty until a unit calls `equal` with
    /// `rename`; then it grows to the graph's length. (R3i)
    pub renaming: Vec<super::relate::Renamed>,
    pub renaming_generation: u32,
    /// The pairs of the renaming in the order they were added, for
    /// `normalize_subst` (ctype.ml:3191-3198), and the length of the
    /// trail when they were last normalized. (R3i)
    pub renamed: Vec<[Ty; 2]>,
    pub renaming_trail: usize,
    /// Scratch of `matches`: the variables `rigidify` collected
    /// (`vars`, ctype.ml:3150-3154). Empty between calls. (R3i)
    pub rigid_vars: Vec<Ty>,
    /// The explicit stack of `subtype_rec` (compiler/ml/ctype.ml:
    /// 3643-4101): not `frames`, whose kinds are unification's. Empty
    /// between calls of [`Checker::subtype`]. (R3j; CHECKER_REWRITE 8.13)
    pub subtyping: Vec<super::relate::SubFrame>,
    /// `subtypes ()` (compiler/ml/ctype.ml:3641, cleared at 4213 and
    /// 4217): the pairs [`Checker::subtype`] has met, ordered keys. A
    /// table of its own and not [`Checker::related`]: the inclusion
    /// check of two packages runs `equal` and `moregeneral` on this
    /// checker INSIDE the walk, and those clear and fill `related` (in
    /// OCaml a table of their own a call, 3115, 3370). Empty between
    /// calls of `subtype`; a unit that never coerces never allocates it.
    /// (R3j; CHECKER_REWRITE 8.6, decision 128)
    pub subtyped: PairSet,
    /// After a failed [`Checker::subtype`] or
    /// [`Checker::force_subtype`] in `Mode::Explain`: the pairs
    /// `subtype_rec` went through down to the constraint that failed,
    /// outermost first (`List.rev trace0`, compiler/ml/ctype.ml:4228; the
    /// first component of the exception `Subtype`, ctype.ml:96), not
    /// expanded. Cleared at the entry of both. (R3j)
    pub subtype_trace: Vec<[Ty; 2]>,
    /// The explicit stack of `build_subtype` (compiler/ml/ctype.ml:
    /// 3427-3587) and the results of the nodes it has left, innermost
    /// last. Empty between calls of [`Checker::enlarge_type`]. (R3j)
    pub enlarging: Vec<super::relate::EnlargeFrame>,
    pub enlarged: Vec<super::relate::Enlarged>,
    /// `visited` of `build_subtype` (ctype.ml:3427) as a dense table:
    /// per node the number of its entry on the path, a value of
    /// `path_clock`, or 0. Not `marks`: the walk holds its entries
    /// across an expansion, and an expansion of a type with a
    /// constrained parameter unifies and takes generations of `marks`.
    /// Empty until a unit calls [`Checker::enlarge_type`]; then it grows
    /// to the graph's length: four bytes a node. (R3j)
    pub path_entries: Vec<u32>,
    pub path_clock: u32,
}

/// `Frame::extra` of the frame [`Checker::occur_pattern`] pushes for a
/// constructor it meets again on the way; no constructor has as many
/// arguments.
const AGAIN: u32 = u32::MAX;

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
            gadt: 0,
            generate_equations: false,
            assume_injective: false,
            unexplained_failure: false,
            depth: 0,
            frames: Vec::new(),
            saved: Vec::new(),
            trace: Vec::new(),
            marks: Vec::new(),
            mark_generation: 0,
            instance_marks: Vec::new(),
            instance_mark_generation: 0,
            pairs: PairSet::default(),
            scopes: Vec::new(),
            scope_floor: 0,
            packages: None,
            newtype_level: 0,
            equations: Vec::new(),
            locals: None,
            tries: Vec::new(),
            compatible: PairSet::default(),
            instance_scopes: Vec::new(),
            instance_scope: NONE,
            instance_members: Vec::new(),
            related: PairSet::default(),
            relating: 0,
            related_shelf: Vec::new(),
            related_spare: Vec::new(),
            renaming: Vec::new(),
            renaming_generation: 0,
            renamed: Vec::new(),
            renaming_trail: 0,
            rigid_vars: Vec::new(),
            subtyping: Vec::new(),
            subtyped: PairSet::default(),
            subtype_trace: Vec::new(),
            enlarging: Vec::new(),
            enlarged: Vec::new(),
            path_entries: Vec::new(),
            path_clock: 0,
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
    /// sets `unexplained_failure`. `left` and `right` are two distinct
    /// representatives ([`Checker::unify`] makes them so). The root pair goes
    /// to [`Checker::unify_pair`] without a frame; the loop runs only when
    /// that call left frames. Cost: one [`Checker::unify_pair`], then
    /// O(pairs popped), each pair one [`Checker::unify_pair`]. (R3a)
    ///
    /// GADT instances (R3s; CHECKER_REWRITE 8.11): one load of
    /// [`Checker::gadt`] and one branch; with [`GADT_LOCAL`] or
    /// [`GADT_PATTERN`] the call is [`Checker::unify_distinct_gadt`].
    pub fn unify_distinct(&mut self, left: Ty, right: Ty) -> Result<(), Clash> {
        if self.gadt & (GADT_LOCAL | GADT_PATTERN) != 0 {
            return self.unify_distinct_gadt(left, right);
        }
        self.unify_distinct_from(left, right, false)
    }

    /// The body of [`Checker::unify_distinct`], whose cost it has. With
    /// `late` (pattern mode entered without a local constraint) the
    /// frames are run by [`Checker::late_pair`] and
    /// [`Checker::resume_frames`], which look at each pair for a local
    /// constraint added since; without, by `run_frames`. Always inline:
    /// `late` is a constant at the call of `unify_distinct`, the hot one;
    /// `unify_distinct_gadt`, out of line, gives it a value.
    #[inline(always)]
    fn unify_distinct_from(&mut self, left: Ty, right: Ty, late: bool) -> Result<(), Clash> {
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
        let mut result = if late {
            self.late_pair(left, right).and_then(|()| self.resume_frames(base))
        } else {
            self.run_frames(base, left, right)
        };
        // A clash above a started attempt of pattern mode is the
        // attempt's (8.9, decision 68): one load of `tries.len()`, on
        // the failure path only.
        if let Err(pair) = result
            && !self.tries.is_empty()
        {
            result = self.recover_frames(base, pair);
        }
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
                // `univar_pairs := old_univars; raise exn` (ctype.ml:
                // 1677-1679): one load when no scope is open.
                if !self.scopes.is_empty() {
                    self.leave_scopes(base);
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

    /// [`Checker::unify_distinct`] for a unit that has a local constraint
    /// or is in pattern mode (`let reset_tracing =
    /// check_trace_gadt_instances !env`, compiler/ml/ctype.ml:2235, and
    /// `reset_trace_gadt_instances reset_tracing` on both ways out,
    /// 2269-2271). With [`GADT_LOCAL`]: [`Checker::trace_on`], the body,
    /// and tracing off again if this call turned it on. Without (pattern
    /// mode before its first local constraint): the body with `late`,
    /// since OCaml makes the test at EVERY `unify`, and a pair that is
    /// unified after an equation or a reified type was added traces;
    /// then [`GADT_TRACING`] is put back as it was (a clash leaves
    /// [`FrameKind::Untrace`] frames unpopped). Cold: O(1) plus the
    /// body. (R3s; CHECKER_REWRITE 8.11, decisions 97 and 105)
    #[cold]
    #[inline(never)]
    fn unify_distinct_gadt(&mut self, left: Ty, right: Ty) -> Result<(), Clash> {
        let before = self.gadt & GADT_TRACING;
        let late = self.gadt & GADT_LOCAL == 0;
        if !late {
            self.trace_on();
        }
        let result = self.unify_distinct_from(left, right, late);
        self.gadt = self.gadt & !GADT_TRACING | before;
        result
    }

    /// `check_trace_gadt_instances env` (compiler/ml/ctype.ml:178-184):
    /// when tracing is off and the environment has a local constraint,
    /// tracing is on, the memorized expansions are forgotten
    /// ([`Checker::cleanup_abbrev`]) and the answer is `true`: the
    /// caller turns it off again with [`Checker::trace_off`]. A caller
    /// on a path every unit runs reads `gadt & GADT_LOCAL` itself first
    /// and calls this only when it is set. O(1) plus the cleanup. (R3s)
    #[cold]
    #[inline(never)]
    pub fn trace_on(&mut self) -> bool {
        if self.gadt & (GADT_LOCAL | GADT_TRACING) != GADT_LOCAL {
            return false;
        }
        self.gadt |= GADT_TRACING;
        self.cleanup_abbrev();
        true
    }

    /// `reset_trace_gadt_instances b` (compiler/ml/ctype.ml:186). O(1).
    #[inline]
    pub fn trace_off(&mut self, turned_on: bool) {
        if turned_on {
            self.gadt &= !GADT_TRACING;
        }
    }

    /// `wrap_trace_gadt_instances env f x` (compiler/ml/ctype.ml:188-192)
    /// for the walk: `expand_head_trace` is `c.traced(|c|
    /// c.expand_head(ty, ExpandMode::Unif))` (ctype.ml:2781-2785). One
    /// load of [`Checker::gadt`] and one branch when no local constraint
    /// exists. (R3s; CHECKER_REWRITE 8.11, decision 101)
    #[inline]
    pub fn traced<T>(&mut self, f: impl FnOnce(&mut Checker) -> T) -> T {
        let turned_on = self.gadt & GADT_LOCAL != 0 && self.trace_on();
        let result = f(self);
        self.trace_off(turned_on);
        result
    }

    /// One pair of two distinct representatives of a pattern unification
    /// that was entered without a local constraint (`late`), as OCaml's
    /// `unify` treats it (compiler/ml/ctype.ml:2235): when a local
    /// constraint exists now and tracing is off, a
    /// [`FrameKind::Untrace`] frame is pushed, tracing is turned on
    /// ([`Checker::trace_on`]) and the pair with everything it pushes is
    /// run by `run_frames` above that frame, which the caller's loop
    /// pops next; otherwise the pair alone is run (`run_frames` with a
    /// base no stack reaches, so that it returns after its one
    /// `unify_pair`). `run_frames` keeps its one call site of
    /// `unify_pair`. A clash leaves the frames as `run_frames` leaves
    /// them. O(1) plus the callee. (R3s; decision 105)
    #[cold]
    #[inline(never)]
    fn late_pair(&mut self, left: Ty, right: Ty) -> Result<(), [Ty; 2]> {
        if self.gadt & (GADT_LOCAL | GADT_TRACING) != GADT_LOCAL {
            return self.run_frames(usize::MAX, left, right);
        }
        let untrace = Frame {
            left: Ty(NONE),
            right: Ty(NONE),
            kind: FrameKind::Untrace,
            extra: 0,
        };
        self.frames.push(untrace);
        self.trace_on();
        let base = self.frames.len();
        self.run_frames(base, left, right)
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
        let bound = if l.tag() == VAR {
            Some((left, l, right, r))
        } else if r.tag() == VAR {
            Some((right, r, left, l))
        } else {
            None
        };
        if let Some((var, before, ty, target)) = bound {
            if self.binds_leaf(target) {
                self.bind_leaf(var, before, ty);
                return Ok(());
            }
            let route = target.tag() == CONSTR;
            return self.bind_routed(var, ty, route.then_some([left, right]));
        }
        // `has_cached_expansion p1 !a1` reads the node's own memo
        // (ctype.ml:2254), which `proper_abbrevs` never writes for a
        // nullary constructor: its expansion goes to `simple_abbrevs`
        // (ctype.ml:200-202). Slot 0 of a nullary node stays empty here too
        // (expand.rs), so the test is always false. With GADT instance
        // tracing the node's own memo is used (R3h).
        if l.tag() == CONSTR && r.tag() == CONSTR && l.arity() == 0 && r.arity() == 0 {
            // `not (has_cached_expansion p1 !a1 || has_cached_expansion p2
            // !a2)` (ctype.ml:2254): a constructor without arguments has
            // an expansion of its own only from a traced one (R3s): one
            // load of `own_live` on this arm.
            if l.a == r.a && (self.memo.own_live == 0 || !self.has_own_expansion(left, right)) {
                // `update_level !env t1.level t2; link_type t1 t2`. `right`
                // is a representative and `r` its descriptor: the outer test
                // of `update_level` (`if ty.level > level`, ctype.ml:635)
                // reads `r` with no second `repr`. Nothing is above the
                // generic level, so a generic `l` never lowers.
                if r.level > l.level {
                    self.lower(right, l.level)?;
                }
                self.g.link(left, right);
                return Ok(());
            }
            // Two locally abstract types under equations (ctype.ml:
            // 2258-2269; 8.9, decision 65): for two nullary constructors of
            // different types, one load; nothing for any other pair.
            if l.a != r.a
                && !self.equations.is_empty()
                && let Some(result) = self.unify_newtypes([left, right], l, r)
            {
                return result;
            }
        }
        // `Tunivar _, Tunivar _` (ctype.ml:2244-2247). Both heads are in
        // registers: one `and` and one untaken branch for any other pair,
        // no load.
        if l.head & r.head & EXTENDED != 0 && self.both_univars(l, r) {
            return self.unify_univars([left, right], l, r);
        }
        self.unify_expanded(left, right)
    }

    /// The first step of `unify` for two universal variables
    /// (`unify_univar t1 t2 !univar_pairs; update_level !env t1.level t2;
    /// link_type t1 t2`, compiler/ml/ctype.ml:2244-2247): `left` and
    /// `right` are distinct representatives with descriptors `l` and `r`.
    /// A universal variable has no child and no scope, so the level
    /// update is one write when `right` is above `left`. Out of line: a
    /// rare arm of [`Checker::unify_pair`]. O(1) plus
    /// [`Checker::unify_univar`].
    #[inline(never)]
    fn unify_univars(&mut self, [left, right]: [Ty; 2], l: Node, r: Node) -> Result<(), Clash> {
        self.unify_univar(left, right)?;
        if r.level > l.level {
            self.g.write(
                right,
                Node {
                    level: l.level,
                    ..r
                },
            );
        }
        self.g.link(left, right);
        Ok(())
    }

    /// `univar_pairs := old_univars` on a failure (compiler/ml/ctype.ml:
    /// 1677-1679): cut [`Checker::scopes`] back to what it held before the
    /// first scope entered above frame index `base`, which the lowest
    /// [`FrameKind::LeavePoly`] frame there records, with the floor that
    /// frame found ([`Checker::scope_floor`]). With no such frame nothing
    /// changes: a floor an entry raised outside every scope entered
    /// above `base` stays raised, as no handler of OCaml puts the list
    /// back there. Failure path only: O(frames above `base`), no step.
    #[cold]
    pub(super) fn leave_scopes(&mut self, base: usize) {
        let lowest = self.frames[base..]
            .iter()
            .find(|frame| frame.kind == FrameKind::LeavePoly)
            .copied();
        if let Some(frame) = lowest {
            self.leave_poly(frame);
        }
    }

    /// `occur_univar !env ty` where OCaml runs it before a variable is
    /// linked (compiler/ml/ctype.ml:2219, 2318, 2322): nothing, on one
    /// load of [`Extras::univars`], when the graph has no universal
    /// variable; otherwise [`Checker::occur_univar`]. `swapped` says the
    /// caller is `unify3` on the swapped pair: the pair a failure pushed
    /// is then reversed, as every entry made below it is
    /// (`List.map (fun (x, y) -> (y, x)) trace`, ctype.ml:2301-2303).
    #[inline]
    fn free_of_univars(&mut self, ty: Ty, swapped: bool) -> Result<(), Clash> {
        if self.extras.univars == 0 {
            return Ok(());
        }
        let mark = self.trace.len();
        let result = self.occur_univar(ty);
        if result.is_err() && swapped {
            for entry in &mut self.trace[mark..] {
                entry.swap(0, 1);
            }
        }
        result
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
    /// walk is the `deep_occur` test: on this route it crosses objects and
    /// variant rows, which `occur_rec` does not enter. The cost is [`Checker::bind`]'s, or one walk and the callee.
    fn bind_routed(&mut self, var: Ty, ty: Ty, route: Option<[Ty; 2]>) -> Result<(), Clash> {
        let before = self.g.nodes[var.0 as usize];
        let target = self.g.nodes[ty.0 as usize];
        if self.binds_leaf(target) {
            self.bind_leaf(var, before, ty);
            return Ok(());
        }
        // Decision 6 of "R3 as designed": in `Mode::Explain`, outside a
        // speculation whose owner restores, a failed binding must leave the
        // levels as they were, because a failed top-level unification there
        // undoes path compression only. So the occurrence check runs before
        // any level is written (`occur`, `link_type`, `update_level`:
        // ctype.ml:2216-2225), in two walks. The speculation this
        // unification opened in `Mode::Explain` is not an owner's.
        let occur_first = self.occur_first();
        // A node without a child holds nothing: no occurrence walk. With
        // scoped types its one level is `Checker::lower`'s, below.
        if !childless(target) && self.binding_occurrence(var, ty, occur_first, route.is_some())? {
            let [left, right] = route.expect("routed occurrence");
            return self.unify_expanded(left, right);
        }
        // `occur_univar env t2` (ctype.ml:2219), after `occur` and before
        // the link. A target without a child is not a universal variable
        // (an extended node is never `childless`) and holds none.
        self.free_of_univars(ty, false)?;
        self.g.link(var, ty);
        if (occur_first || self.types.scoped != 0)
            && let Err(clash) = self.lower_to(ty, before.level)
        {
            // `t1.desc <- d1` (ctype.ml:2224).
            self.g.write(var, before);
            return Err(clash);
        }
        Ok(())
    }

    /// O(1): whether a binding to a representative whose descriptor is
    /// `target` is [`Checker::bind_leaf`]'s: `target` is a variable, or has
    /// no child ([`childless`]) and no type has a scope.
    #[inline(always)]
    fn binds_leaf(&self, target: Node) -> bool {
        target.tag() == VAR || (childless(target) && self.types.scoped == 0)
    }

    /// O(1): the binding of variable `var`, whose descriptor is `before`, to
    /// the distinct representative `ty`, a variable or (with no scoped
    /// types) a node without a child ([`Checker::binds_leaf`]). `ty` holds
    /// nothing, so there is no occurrence walk: a variable cannot hold
    /// another, and a node without a child is a walk of one node that finds
    /// nothing (`occur`, compiler/ml/ctype.ml:2217; nor is it
    /// `deep_occur`'s, ctype.ml:2240). What remains is the link and
    /// `update_level` of the one node (ctype.ml:586, 2221-2222): no child,
    /// and no scope test (a variable has no scope; with no scoped types
    /// there is none), so one write when `ty` is above the variable, which
    /// cannot fail. Of two variables, `link_type` picks the surviving name by
    /// the levels before `update_level` (compiler/ml/btype.ml:727), so the
    /// link comes first and the node is read after it, its name rule having
    /// possibly named it; the rule leaves a target that is not a variable
    /// alone. Always inline (out of line, saving registers costs more than
    /// the body): one link, one node load, one compare and at most one
    /// write.
    #[inline(always)]
    fn bind_leaf(&mut self, var: Ty, before: Node, ty: Ty) {
        self.g.link(var, ty);
        let target = self.g.nodes[ty.0 as usize];
        if target.level > before.level {
            self.g.write(
                ty,
                Node {
                    level: before.level,
                    ..target
                },
            );
        }
    }

    /// O(1): whether a binding tests occurrence in a walk of its own before
    /// it writes a level (decision 6 of "R3 as designed"): in
    /// `Mode::Explain` outside a speculation whose owner restores.
    #[inline]
    pub(super) fn occur_first(&self) -> bool {
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
                return Ok(self.binding_scan(var, ty, true));
            }
            self.binding_walk(var, ty)?;
            return Ok(false);
        }
        if !self.reaches(var, ty, routed) {
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
    /// against `var` (`occur_rec`, compiler/ml/ctype.ml:1384) and lowered
    /// to the variable's level exactly when `update_level`
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
        if self.binding_scan(var, ty, false) {
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
    /// most 2 steps a node, explicit stack, marks. With `deep` (the route
    /// of a variable against a constructor, `deep_occur`,
    /// compiler/ml/ctype.ml:1735, 2240) the occurrence test crosses objects
    /// and variant rows too.
    fn binding_scan(&mut self, var: Ty, ty: Ty, deep: bool) -> bool {
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
            if !deep && self.stops_occurrence(node) {
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
        // `let allow_recursive = !(umode ()) = Pattern` (ctype.ml:1468):
        // one load, made only after a walk found `node` in `ty`, which in
        // expression mode is a clash or the retry of one constructor.
        if self.umode == UnifyMode::Pattern {
            return self.occur_pattern(node, ty);
        }
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

    /// `occur_rec` with `allow_recursive` (compiler/ml/ctype.ml:1384-1408;
    /// `occur_full` sets it in pattern mode, 1468), run once a walk found
    /// `node` in `ty`: a clash when `node` occurs where pattern mode
    /// looks. Per representative:
    ///
    /// - `node` itself: it occurs (`if ty == ty0 then raise Occur`, 1387);
    /// - a constructor whose type is [`TypeTable::contractive`]: free, and
    ///   not entered (`if allow_recursive && is_contractive env p then
    ///   ()`, 1390);
    /// - any other constructor: its arguments, in order; when one holds
    ///   `node`, or the constructor is met again on the way from `ty`,
    ///   the constructor is expanded ([`Checker::expand_head`] in
    ///   [`ExpandMode::Unif`]: `try_expand_head try_expand_once`, 1398)
    ///   and its expansion is tested in its place; one that does not
    ///   expand holds `node` (1392-1402);
    /// - anything else (a tuple, an arrow, an object, a variant, a
    ///   polymorphic type, a package): free, and not entered (`| _ -> if
    ///   allow_recursive || Type_set.mem ty visited then ()`, 1403-1405).
    ///
    /// So a variable is bound to a type that holds it below a structure
    /// that is not a constructor or below a contractive constructor, and
    /// the graph has a cycle through that node afterwards (every walk of
    /// the kernel marks or cuts by level; `Checker::reaches` gives up at
    /// its budget and marks). The walk of [`Checker::occur_expanding`]
    /// with these two rules, one frame a constructor entered on
    /// [`Checker::frames`] above the length it finds.
    ///
    /// OCaml's `visited` is the set of the PATH (`if Type_set.mem ty
    /// visited then raise Occur; let visited = Type_set.add ty visited`,
    /// 1393-1394), and what a constructor answers depends on it: one on
    /// the way answers what its expansion does, one met elsewhere
    /// answers that only when an argument holds `node`. The kernel
    /// remembers an answer across paths (marks: free, holding) only for
    /// a constructor whose visit met no constructor that was on the
    /// way, itself included: such a visit is the same from every path.
    /// While a constructor that was met again is on the way (`met`, a
    /// count; its mark says "on the way, met"), a constructor that is
    /// left is not remembered and is walked once per path, as in OCaml.
    /// Witness: `the_occurrence_test_of_pattern_mode_keeps_its_set_per_
    /// path` (tc/r3_tests.rs), where an answer remembered from a path
    /// that held `c` is wrong on a path that does not.
    ///
    /// Cost: one step and one `TypeInfo` load a constructor reached
    /// through constructors that are not contractive, one expansion a
    /// constructor that holds `node`; for a type that reaches itself
    /// through constructors that are not contractive (made by a binding
    /// through a constructor whose expansion drops the argument), the
    /// constructors below one that was met again are walked once per
    /// path. (R3h; the set per path in the eighth skeleton turn;
    /// CHECKER_REWRITE 8.9, decision 69)
    #[cold]
    #[inline(never)]
    fn occur_pattern(&mut self, node: Ty, ty: Ty) -> Result<(), Clash> {
        let marks = [self.fresh_marks(), self.fresh_marks(), self.fresh_marks(), self.fresh_marks()];
        // How many constructors on the way were met again.
        let mut met = 0u32;
        let base = self.frames.len();
        let mut result = self.occur_pattern_visit(node, ty, marks, &mut met);
        while self.frames.len() > base {
            let top = self.frames.len() - 1;
            let frame = self.frames[top];
            let parent = frame.left;
            match result.take() {
                // The expansion of `parent` decided it.
                Some(holds_node) if frame.right.0 != NONE => {
                    result = Some(self.occur_pattern_finish(frame, holds_node, marks, &mut met));
                }
                Some(false) => {}
                Some(true) => {
                    let expansion = match self.expand_head(parent, ExpandMode::Unif) {
                        Ok(expansion) => self.g.repr(expansion),
                        Err(Clash) => {
                            self.frames.truncate(base);
                            return Err(Clash);
                        }
                    };
                    if expansion == parent {
                        // `Cannot_expand`: the constructor holds it.
                        result = Some(self.occur_pattern_finish(frame, true, marks, &mut met));
                    } else {
                        self.frames[top].right = expansion;
                        result = self.occur_pattern_visit(node, expansion, marks, &mut met);
                    }
                }
                None => {
                    let descriptor = self.g.nodes[parent.0 as usize];
                    if frame.extra < descriptor.arity() {
                        self.frames[top].extra += 1;
                        let argument = self.g.lists[(descriptor.b + 1 + frame.extra) as usize];
                        result = self.occur_pattern_visit(node, argument, marks, &mut met);
                    } else {
                        result = Some(self.occur_pattern_finish(frame, false, marks, &mut met));
                    }
                }
            }
        }
        if result == Some(true) { Err(Clash) } else { Ok(()) }
    }

    /// O(1): one node of [`Checker::occur_pattern`]: decided at once
    /// (`node` itself; a node that is not a constructor, or of a
    /// contractive type, which is not entered; a constructor remembered
    /// from a visit that met none on the way; one without arguments), or
    /// pushed as a frame whose `extra` is the next argument and whose
    /// `right` is the expansion it waits for. A constructor met again on
    /// the way (`Type_set.mem ty visited`, compiler/ml/ctype.ml:1393)
    /// holds `node` in a frame of its own ([`AGAIN`] in `extra`), so
    /// that it is expanded and its expansion tested in its place; its
    /// mark becomes "on the way, met" and `met` counts it once. One
    /// step; the marks grow, amortized, to nodes an expansion made.
    fn occur_pattern_visit(&mut self, node: Ty, ty: Ty, [free, holds, busy, busy_met]: [u32; 4], met: &mut u32) -> Option<bool> {
        #[cfg(test)]
        super::steps::tick();
        let ty = self.g.repr(ty);
        if ty == node {
            return Some(true);
        }
        let descriptor = self.g.nodes[ty.0 as usize];
        if descriptor.tag() != CONSTR || TypeTable::contractive(self.types.info(descriptor.a)) {
            return Some(false);
        }
        if ty.0 as usize >= self.marks.len() {
            self.marks.resize(self.g.nodes.len(), 0);
        }
        let mark = self.marks[ty.0 as usize];
        if mark == free || mark == holds {
            return Some(mark == holds);
        }
        if mark == busy || mark == busy_met {
            if mark == busy {
                self.marks[ty.0 as usize] = busy_met;
                *met += 1;
            }
            self.frames.push(Frame { left: ty, right: Ty(NONE), kind: FrameKind::Pair, extra: AGAIN });
            return Some(true);
        }
        if descriptor.arity() == 0 {
            self.marks[ty.0 as usize] = free;
            return Some(false);
        }
        self.marks[ty.0 as usize] = busy;
        self.frames.push(Frame { left: ty, right: Ty(NONE), kind: FrameKind::Pair, extra: 0 });
        None
    }

    /// O(1): pop `frame` in [`Checker::occur_pattern`] and return
    /// `holds_node`. The frame of a constructor met again ([`AGAIN`])
    /// leaves the mark as it is: the constructor is still on the way.
    /// Any other frame takes its constructor off the way; the answer is
    /// remembered only when neither it nor a constructor still on the
    /// way was met again.
    fn occur_pattern_finish(&mut self, frame: Frame, holds_node: bool, [free, holds, _, busy_met]: [u32; 4], met: &mut u32) -> bool {
        self.frames.pop();
        if frame.extra == AGAIN {
            return holds_node;
        }
        let slot = frame.left.0 as usize;
        let was_met = self.marks[slot] == busy_met;
        if was_met {
            *met -= 1;
        }
        self.marks[slot] = match (was_met || *met != 0, holds_node) {
            (true, _) => 0,
            (false, true) => holds,
            (false, false) => free,
        };
        holds_node
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
    /// parameters, then its result), or `None` past the last. An extended
    /// node's children are its slots in order.
    #[inline]
    pub(super) fn child(&self, node: Node, index: u32) -> Option<Ty> {
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
        // `umode` is loaded once a call and handed to unify3, which read
        // it before (8.9, decision 64): the loads of a unification in
        // expression mode are what they were.
        let pattern = self.umode == UnifyMode::Pattern;
        let left_head = self.g.repr(left);
        // `if unify_eq t1 t2 then ()` of `unify` (ctype.ml:2233), which
        // in pattern mode reads the table of assumed pairs.
        if pattern && self.assumed_equal(left_head, right) {
            return Ok(());
        }
        let mut expanded_left = if self.never_expands(left_head) {
            left_head
        } else {
            self.expand_head_unif(left_head)?
        };
        let right_head = self.g.repr(right);
        let mut expanded_right = if self.never_expands(right_head) {
            right_head
        } else {
            self.expand_head_unif(right_head)?
        };
        let unexpanded = expanded_left == self.g.repr(left) && expanded_right == self.g.repr(right);
        if !unexpanded {
            expanded_left = self.expand_head_unif(left)?;
            expanded_right = self.expand_head_unif(right)?;
            // `try_expand_head` adds the chain of a type whose head is
            // in a set (ctype.ml:1271-1276): one load of `gadt` a pair
            // of which a head expanded. (R3s)
            if self.gadt & GADT_MEMBER != 0 {
                self.expanded_instances([left, right], [expanded_left, expanded_right]);
            }
        }
        let left_level = self.g.nodes[expanded_left.0 as usize].level;
        let right_level = self.g.nodes[expanded_right.0 as usize].level;
        let level = left_level.min(right_level);
        let (t1, t2) = if unexpanded && self.types.scoped == 0 {
            // The heads are the representatives of `left` and `right`, whose
            // levels were just read: the outer test of `update_level`
            // (`if ty.level > level`, ctype.ml:635) reads them with no
            // second `repr`. `level` is the lower of the two, so at most one
            // is above it. Without scoped types `Graph::lower` links nothing,
            // so lowering one side does not raise the other and every head
            // stays its side's representative: `t1 = t1'`, `t2 = t2'`.
            if right_level > level {
                self.lower(expanded_right, level)?;
            } else if left_level > level {
                self.lower(expanded_left, level)?;
            }
            if expanded_left == expanded_right {
                return Ok(());
            }
            (expanded_left, expanded_right)
        } else {
            self.lower_to(right, level)?;
            self.lower_to(left, level)?;
            // `unify_eq t1' t2'` (ctype.ml:2286). The heads are taken again
            // as representatives: only a scoped lowering links a node, and
            // then OCaml would read a link's descriptor in unify3.
            expanded_left = self.g.repr(expanded_left);
            expanded_right = self.g.repr(expanded_right);
            if expanded_left == expanded_right {
                return Ok(());
            }
            (self.g.repr(left), self.g.repr(right))
        };
        // `if unify_eq t1' t2' then ()` (ctype.ml:2286) for a pair that
        // pattern mode assumed.
        if pattern && self.assumed_equal(expanded_left, expanded_right) {
            return Ok(());
        }
        // `if !(trace_gadt_instances ()) then ...` (ctype.ml:2289-2298):
        // one load a call that comes here. (R3s)
        if self.gadt & GADT_TRACING != 0 {
            self.join_instance_levels(t1, t2);
        }
        // `if unify_eq t1 t1' || not (unify_eq t2 t2') then unify3 env t1
        // t1' t2 t2' else unify3 env t2 t2' t1 t1'` (ctype.ml:2299-2303).
        // These two stay tests of identity in pattern mode: a pair in the
        // table is two heads, and a node and its own expanded head are
        // never both that (8.9, decision 64).
        if t1 == expanded_left || t2 != expanded_right {
            self.unify3(
                [t1, expanded_left, t2, expanded_right],
                [left, right],
                false,
                pattern,
            )
        } else {
            self.unify3(
                [t2, expanded_right, t1, expanded_left],
                [left, right],
                true,
                pattern,
            )
        }
    }

    /// `unify_eq` for two nodes that are not one node, in pattern mode
    /// (compiler/ml/ctype.ml:2205-2214): whether the pair is in the table
    /// of assumed equalities, in either order. Both are taken as their
    /// representatives. One hash lookup; never called in expression
    /// mode. (R3h)
    #[cold]
    #[inline(never)]
    fn assumed_equal(&mut self, left: Ty, right: Ty) -> bool {
        let (left, right) = (self.g.repr(left), self.g.repr(right));
        self.pairs.keys.contains(&PairSet::key(left, right))
    }

    /// `expand_head_unif` of `ty` (compiler/ml/ctype.ml:1279) as unify2 asks
    /// for it (ctype.ml:2278-2282): [`Checker::expand_head`] in
    /// [`ExpandMode::Unif`], except that the answer "does not expand" is
    /// given here, without the call, when the first [`Checker::expand_once`]
    /// would return it on a test without a side effect: the representative
    /// is not a constructor (its first return), or its type's row, read now
    /// with one `TypeInfo` load, has none of [`ABBREV`], [`ALIAS`],
    /// [`INHERITS`]. Such a type has no public memo entry: slot 0 or the
    /// nullary row gets one only from `memorize` in `subst` of a public
    /// expansion (which needs [`ABBREV`]) or in `expand_alias` (which needs
    /// [`ALIAS`]), and the chain lookup runs only for [`INHERITS`]; so
    /// `expand_once` finds no memo, skips the alias and the chain and
    /// returns `NONE` at its `!expands` test. The row is the one at the time
    /// of the call, nothing is cached: a pattern-mode equation that gives a
    /// locally abstract type a manifest (R3h) sets its row's flags before a
    /// later unification reads them, and one that takes it away cleans the
    /// memos as `check_abbrev_env` does (ctype.ml:1163, `Checker::set_env`),
    /// which `expand_once` relies on as well. Cost: one `repr`, one node
    /// load and at most one row load; otherwise `expand_head`'s.
    #[inline(always)]
    fn never_expands(&self, head: Ty) -> bool {
        let node = self.g.nodes[head.0 as usize];
        node.tag() != CONSTR || self.types.info(node.a).flags & (ABBREV | ALIAS | INHERITS) == 0
    }

    /// `unify3 env t1 t1' t2 t2'` (compiler/ml/ctype.ml:2305-2438) on
    /// `[t1, t1', t2, t2']`, all representatives; `pair` is the pair of the
    /// enclosing `unify`, in its order, and `swapped` says unify2 chose the
    /// right side; `pattern` is `umode`, which
    /// [`Checker::unify_expanded`] loaded. A variable head is linked to
    /// the *original* other side; otherwise, in expression mode, `occur
    /// t1' t2'`, the link `t1' -> t2` before the children, then the
    /// children are pushed; in pattern mode [`Checker::unify3_pattern`]. When `t2` was expanded and `t1'` occurs
    /// in it (`create_recursion`, one [`Checker::deep_occur`]), a
    /// [`FrameKind::Recursion`] frame runs the repair after the children.
    /// O(1) plus one [`Checker::occur`], at most one `deep_occur` and one
    /// push per child. In `Mode::Explain` a clash met while the children
    /// are pushed leaves its entries reversed when `swapped`, as unify2's
    /// handler does (`List.map (fun (x, y) -> (y, x)) trace`, ctype.ml:
    /// 2301-2303): one swap per entry, on the failure path only.
    fn unify3(
        &mut self,
        [t1, t1x, t2, t2x]: [Ty; 4],
        pair: [Ty; 2],
        swapped: bool,
        pattern: bool,
    ) -> Result<(), Clash> {
        let d1 = self.g.nodes[t1x.0 as usize];
        let d2 = self.g.nodes[t2x.0 as usize];
        // `occur !env t1' t2; occur_univar !env t2; link_type t1' t2`
        // (ctype.ml:2316-2319) and its mirror (ctype.ml:2320-2323).
        if d1.tag() == VAR {
            self.occur(t1x, t2)?;
            self.free_of_univars(t2, swapped)?;
            self.g.link(t1x, t2);
            return Ok(());
        }
        if d2.tag() == VAR {
            self.occur(t2x, t1)?;
            self.free_of_univars(t1, swapped)?;
            self.g.link(t2x, t1);
            return Ok(());
        }
        let extended = d1.head & d2.head & EXTENDED != 0;
        // `Tunivar _, Tunivar _ -> unify_univar t1' t2' !univar_pairs;
        // link_type t1' t2'` (ctype.ml:2313-2315): the first arm of unify3,
        // reached when a head expands to a universal variable. The link
        // goes to the EXPANDED other side, there is no occurrence test,
        // no `Linked` frame and no child.
        if extended && self.both_univars(d1, d2) {
            self.unify_univar(t1x, t2x)?;
            self.g.link(t1x, t2x);
            return Ok(());
        }
        // `create_recursion` is computed before anything is linked
        // (ctype.ml:2308); the cases above do not read it.
        let create_recursion = t2 != t2x && self.deep_occur(t1x, t2);
        // `Tfield _, Tfield _ -> unify_fields env t1' t2'` (ctype.ml:
        // 2322-2324): an arm of its own, before the link and without the
        // recursion repair. In `Mode::Explain` the pair is recorded as a
        // `Linked` frame whose descriptor is the one the node still has.
        if extended && self.both_fields(d1, d2) {
            if self.g.mode == Mode::Explain {
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
            return self.unify_fields(t1x, t2x);
        }
        if pattern {
            // `add_type_equality` in place of the link (ctype.ml:2332):
            // CHECKER_REWRITE 8.9, decision 64.
            return self.unify3_pattern([t1, t1x, t2, t2x], pair, swapped, create_recursion);
        }
        // Two variant nodes get the slots of their references while both
        // are nodes (`Checker::open_row`): the left one is a link after
        // this, and what `unify_row` resolves in it must be in the
        // descriptor a failure puts back (`t1'.desc <- d1`).
        let (d1, d2) = if extended && self.both_variants(d1, d2) {
            (self.open_row(t1x), self.open_row(t2x))
        } else {
            (d1, d2)
        };
        // `occur !env t1' t2'; link_type t1' t2` (ctype.ml:2330-2331),
        // before the children. A `t2'` without a child is not `t1'` (they
        // are distinct representatives) and holds nothing: no walk.
        if !childless(d2) {
            self.occur(t1x, t2x)?;
        }
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
        let mark = self.trace.len();
        let pushed = if extended {
            self.extended_children([t1x, t2x], d1, d2)
        } else {
            self.push_children(d1, d2)
        };
        if pushed.is_err() {
            // `push_children` pushes nothing when it fails.
            if create_recursion {
                self.frames.pop();
            }
            if explain {
                self.frames.pop();
                self.saved.truncate(self.saved.len() - 2);
                self.g.write(t1x, d1);
                // The entries of a clash below this swapped pair are
                // reversed (ctype.ml:2301-2303).
                if swapped {
                    for entry in &mut self.trace[mark..] {
                        entry.swap(0, 1);
                    }
                }
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
    /// clash or belongs to R3e-R3h. O(children). Always inline: its two
    /// callers are unify3 and the pattern arm, and out of line it costs
    /// expression mode a call a structure pair. (R3a)
    #[inline(always)]
    pub fn push_children(&mut self, left: Node, right: Node) -> Result<(), Clash> {
        if (left.head | right.head) & EXTENDED != 0 {
            // An extended descriptor against another kind of node
            // (`_, _ -> raise (Unify [])`, ctype.ml:2425).
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

    /// `has_cached_expansion p1 !a1 || has_cached_expansion p2 !a2`
    /// (compiler/ml/ctype.ml:2254) for two constructor nodes without
    /// arguments: whether one of them has a live row of `Memo::own`.
    /// Called when `Memo::own_live` is not 0. Two row loads. (R3s;
    /// CHECKER_REWRITE 8.11, decision 100)
    #[cold]
    #[inline(never)]
    fn has_own_expansion(&self, left: Ty, right: Ty) -> bool {
        self.own_expansion(left).0 != NONE || self.own_expansion(right).0 != NONE
    }

    /// The chains of the two sides of unify2 after `expand_head_unif`
    /// (compiler/ml/ctype.ml:1271-1276, 2278-2281), for the two sides and
    /// the heads they expanded to: each side whose representative is not
    /// its head goes to `Checker::expanded_instance`. OCaml adds the
    /// chain at each of the four expansions; a set holds a node once,
    /// so once a side after the last is the same set. Called behind
    /// [`GADT_MEMBER`]. Cold. (R3s; decision 111)
    #[cold]
    #[inline(never)]
    fn expanded_instances(&mut self, sides: [Ty; 2], heads: [Ty; 2]) {
        for (side, head) in sides.into_iter().zip(heads) {
            let side = self.g.repr(side);
            if side != head {
                self.expanded_instance(side, head);
            }
        }
    }

    /// unify2 under tracing (compiler/ml/ctype.ml:2289-2298), for `t1`
    /// and `t2` as unify2 has them after the two lowerings
    /// (representatives): `lv1 = ilevel t1`, `lv2 = ilevel t2`, 0 for a
    /// node in no set; `if lv1 > lv2 then add_gadt_instance_chain lv1 t2
    /// else if lv2 > lv1 then add_gadt_instance_chain lv2 t1`. Nothing,
    /// on one more load of [`Checker::gadt`], when no member exists (both
    /// levels are 0 then). Two [`Checker::instance_level`] and at most
    /// one [`Checker::add_instance_chain`]. Cold. (R3s)
    #[cold]
    #[inline(never)]
    fn join_instance_levels(&mut self, t1: Ty, t2: Ty) {
        if self.gadt & GADT_MEMBER == 0 {
            return;
        }
        let (lv1, lv2) = (self.instance_level(t1), self.instance_level(t2));
        if lv1 > lv2 {
            self.add_instance_chain(lv1, t2);
        } else if lv2 > lv1 {
            self.add_instance_chain(lv2, t1);
        }
    }

    /// `Env.add_gadt_instance_level lv env` (compiler/ml/env.ml:
    /// 1307-1308) where the walk calls `init_env` (CHECKER_REWRITE 8.11,
    /// the contract of R5b): a new scope at `level` inside the current
    /// one becomes the current one; the mark is what the environment was
    /// ([`Checker::case_mark`]). Amortized O(1): one node (the head, a
    /// variable at level 0 with `b = NONE`) and one 12-byte row. (R3s)
    pub fn enter_instance_scope(&mut self, level: u32) -> CaseMark {
        let mark = self.case_mark();
        let head = self.g.push(Node {
            head: VAR,
            level: 0,
            a: NONE,
            b: NONE,
        });
        let parent = self.instance_scope;
        self.instance_scope = self.instance_scopes.len() as u32;
        self.instance_scopes.push(InstanceScope {
            level,
            parent,
            head,
        });
        mark
    }

    /// O(1): the environment as it is: the number of equations, the
    /// current scope and whether a local constraint exists. What a
    /// caller keeps before a pattern is typed (`save_state`,
    /// compiler/ml/typecore.ml:1299-1305) and before a case. (R3s)
    #[inline]
    pub fn case_mark(&self) -> CaseMark {
        CaseMark {
            equations: self.equations.len() as u32,
            scope: self.instance_scope,
            local: self.gadt & GADT_LOCAL,
        }
    }

    /// Drop the environment of a case, or of a pattern unification that
    /// failed (`set_state`, compiler/ml/typecore.ml:1303-1305):
    /// [`Checker::cut_equations`] to the mark, the current scope and
    /// [`GADT_LOCAL`] as the mark has them. The members of a scope that
    /// was left are not reached again; [`GADT_MEMBER`] stays. One call,
    /// so that none of the three is forgotten. O(equations cut). (R3s;
    /// decision 101)
    pub fn leave_case(&mut self, mark: CaseMark) {
        self.cut_equations(mark.equations as usize);
        self.instance_scope = mark.scope;
        self.gadt = self.gadt & !GADT_LOCAL | mark.local;
    }

    /// `Env.add_local_type path decl env` (compiler/ml/env.ml:1802-1803)
    /// as far as the kernel keeps it: the environment has a local
    /// constraint from here to the `leave_case` of a mark taken before.
    /// The walk calls it for each existential type of a constructor
    /// pattern (ctype.ml:970); `reify` and `add_gadt_equation` set the
    /// bit themselves. O(1). (R3s; decisions 85 and 97)
    #[inline]
    pub fn add_local_type(&mut self) {
        self.gadt |= GADT_LOCAL;
    }

    /// `Env.gadt_instance_level env t` (compiler/ml/env.ml:1314-1323)
    /// for a representative: the level of the innermost scope, from
    /// [`Checker::instance_scope`] outwards, one of whose members has
    /// `ty` as its representative; 0 when none has (a scope's level is
    /// at least 1). One step a scope visited and one step and one `repr`
    /// a member read: linear in the additions of the scopes visited, as
    /// OCaml's is in their members (`Type_set.exists is_Tlink` a scope).
    /// A caller reads [`GADT_MEMBER`] first. (R3s; decision 106)
    pub fn instance_level(&mut self, ty: Ty) -> u32 {
        let mut scope = self.instance_scope;
        while scope != NONE {
            #[cfg(test)]
            super::steps::tick();
            let row = self.instance_scopes[scope as usize];
            let mut member = self.g.nodes[row.head.0 as usize].b;
            while member != NONE {
                #[cfg(test)]
                super::steps::tick();
                let entry = self.instance_members[member as usize];
                if self.g.repr(entry.ty) == ty {
                    return row.level;
                }
                member = entry.next;
            }
            scope = row.parent;
        }
        0
    }

    /// O(scopes visited): the first scope of level `level` from the
    /// current one outwards (`List.assoc lv env.gadt_instances`,
    /// compiler/ml/env.ml:1326-1328), or `NONE`: OCaml asserts that it
    /// exists; an equation whose level has no scope adds nothing
    /// (CHECKER_REWRITE 8.11, (v)). One step a scope.
    fn instance_scope_at(&self, level: u32) -> u32 {
        let mut scope = self.instance_scope;
        while scope != NONE {
            #[cfg(test)]
            super::steps::tick();
            let row = self.instance_scopes[scope as usize];
            if row.level == level {
                return scope;
            }
            scope = row.parent;
        }
        NONE
    }

    /// O(1) amortized: `ty` joins the set of scope `scope` (an index of
    /// `instance_scopes`): one 8-byte row, and one `Graph::write` of the
    /// scope's head node, which a restore undoes (`set_typeset`,
    /// compiler/ml/btype.ml:749-751, logs `Ctypeset`). The first
    /// addition of a unit sets [`GADT_MEMBER`] and counts one scoped
    /// type (`TypeTable::scoped`), so that every lowering of the unit is
    /// the scoped one from here on. No test that `ty` is already a
    /// member. (R3s; decision 98)
    fn push_instance(&mut self, scope: u32, ty: Ty) {
        if self.gadt & GADT_MEMBER == 0 {
            self.gadt |= GADT_MEMBER;
            self.types.scoped += 1;
        }
        let head = self.instance_scopes[scope as usize].head;
        let node = self.g.nodes[head.0 as usize];
        let member = self.instance_members.len() as u32;
        self.instance_members
            .push(InstanceMember { ty, next: node.b });
        self.g.write(head, Node { b: member, ..node });
    }

    /// `Env.add_gadt_instances env lv tl` (compiler/ml/env.ml:1325-1329)
    /// for the representatives `tys`: each joins the set of the first
    /// scope of level `level`; nothing when no scope has that level.
    /// O(scopes visited + tys). (R3s)
    pub fn add_instances(&mut self, level: u32, tys: &[Ty]) {
        let scope = self.instance_scope_at(level);
        if scope == NONE {
            return;
        }
        for &ty in tys {
            let ty = self.g.repr(ty);
            self.push_instance(scope, ty);
        }
    }

    /// `Env.add_gadt_instance_chain env lv t` (compiler/ml/env.ml:
    /// 1332-1345): `t` joins the set of the first scope of level `level`
    /// unless it is a member of THAT set, and then, when it is a
    /// constructor whose own memo holds an expansion of either kind
    /// (`find_expans Private p !memo`: slot 0 and the entries it inherits
    /// for one with arguments, the row of `Memo::own` for one without;
    /// never the memo all nullary constructors of a type share), the
    /// same for that expansion. Nothing when no scope has the level.
    /// Membership in the set is one generation of
    /// `Checker::instance_marks`: the set's members
    /// are marked once (one step each), then each node of the chain is
    /// one step, one mark and one memo lookup. O(members of the set +
    /// chain), not their product. (R3s; decision 106)
    pub fn add_instance_chain(&mut self, level: u32, ty: Ty) {
        let scope = self.instance_scope_at(level);
        if scope == NONE {
            return;
        }
        // The set's members, marked once.
        let generation = self.fresh_instance_marks();
        let mut member = self.g.nodes[self.instance_scopes[scope as usize].head.0 as usize].b;
        while member != NONE {
            #[cfg(test)]
            super::steps::tick();
            let entry = self.instance_members[member as usize];
            let node = self.g.repr(entry.ty);
            self.instance_marks[node.0 as usize] = generation;
            member = entry.next;
        }
        // `add_instance`, a loop: each node of the chain once.
        let mut ty = self.g.repr(ty);
        loop {
            #[cfg(test)]
            super::steps::tick();
            if self.instance_marks[ty.0 as usize] == generation {
                return;
            }
            self.instance_marks[ty.0 as usize] = generation;
            self.push_instance(scope, ty);
            let node = self.g.nodes[ty.0 as usize];
            if node.tag() != CONSTR {
                return;
            }
            // `find_expans Private p !memo` on the node's own memo.
            let expansion = if node.arity() == 0 {
                self.own_expansion(ty)
            } else {
                let slot = self.g.lists[node.b as usize];
                if slot.0 != NONE || self.types.info(node.a).flags & INHERITS == 0 {
                    slot
                } else {
                    self.inherited_expansion(node, true)
                }
            };
            if expansion.0 == NONE {
                return;
            }
            ty = self.g.repr(expansion);
        }
    }

    /// The copy WITH an environment (`copy ?env`, compiler/ml/ctype.ml:
    /// 770-774; `instance env`, 846-851): [`Checker::copy`], and when a
    /// member exists and the environment has a local constraint
    /// ([`GADT_MEMBER`] and [`GADT_LOCAL`]: `Some env when
    /// Env.has_local_constraints env`, ctype.ml:771; one load and one
    /// branch otherwise) the copy of every member that was copied joins
    /// the member's set
    /// (`Some lv -> Env.add_gadt_instances env lv [t]`). The members of
    /// the scopes from the current one outwards are read once, innermost
    /// scope first; a member whose representative has a forwarding row
    /// of this copy (`Graph::forward`, the copy's generation) gets its
    /// copy added to the innermost scope that holds it. Cost: the copy,
    /// then one step a scope and one a member read, instead of one
    /// lookup a copied node. (R3s; decisions 101 and 107)
    pub fn copy_in(&mut self, root: Ty) -> Ty {
        let copied = self.copy(root);
        // `Some env when Env.has_local_constraints env` (ctype.ml:771).
        if self.gadt & (GADT_MEMBER | GADT_LOCAL) != GADT_MEMBER | GADT_LOCAL {
            return copied;
        }
        // A source whose copy was added is marked: an outer scope that
        // holds it too adds nothing (`gadt_instance_level` answers the
        // innermost scope).
        let generation = self.fresh_instance_marks();
        let mut scope = self.instance_scope;
        while scope != NONE {
            #[cfg(test)]
            super::steps::tick();
            let row = self.instance_scopes[scope as usize];
            let mut member = self.g.nodes[row.head.0 as usize].b;
            while member != NONE {
                #[cfg(test)]
                super::steps::tick();
                let entry = self.instance_members[member as usize];
                member = entry.next;
                let source = self.g.repr(entry.ty);
                let Some(&forward) = self.g.forward.get(source.0 as usize) else {
                    continue;
                };
                if forward.generation != self.g.copy_generation
                    || self.instance_marks[source.0 as usize] == generation
                {
                    continue;
                }
                self.instance_marks[source.0 as usize] = generation;
                let target = self.g.repr(Ty(forward.target));
                self.push_instance(scope, target);
            }
            scope = row.parent;
        }
        copied
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
        // `Tvar _, Tconstr _ when deep_occur t1 t2 -> unify (ref env) t1
        // t2` comes before the arm that traces (ctype.ml:2757): with a
        // local constraint the test is made here, ahead of
        // `check_trace_gadt_instances` (ctype.ml:2759). One load of
        // `gadt` and one branch a call. (R3s)
        let mut turned_on = false;
        if self.gadt & GADT_LOCAL != 0 {
            if target.tag() == CONSTR && self.deep_occur(var, ty) {
                return self.unify(var, ty);
            }
            turned_on = self.trace_on();
        }
        let occur_first = self.occur_first();
        // `occur env t1 t2; update_level env t1.level t2; link_type t1 t2`:
        // here the level is written before the link, so of two variables the
        // name is chosen by the levels after it (btype.ml:727).
        let mut result = Ok(());
        // A node without a child holds nothing: no occurrence walk; its one
        // level is written below.
        if target.tag() != VAR && !childless(target) {
            match self.binding_occurrence(var, ty, occur_first, target.tag() == CONSTR) {
                // `Tvar _, Tconstr _ when deep_occur t1 t2 -> unify (ref env)
                // t1 t2` (ctype.ml:2755).
                Ok(true) => {
                    self.trace_off(turned_on);
                    return self.unify(var, ty);
                }
                Ok(false) => {}
                Err(clash) => result = Err(clash),
            }
        }
        if result.is_ok()
            && (target.tag() == VAR || childless(target) || occur_first || self.types.scoped != 0)
        {
            result = self.lower_to(ty, before.level);
        }
        self.trace_off(turned_on);
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
    /// pattern mode with equations and injectivity assumed, at
    /// `newtype_level`: [`Checker::unify_pattern`]. (R3h)
    pub fn unify_gadt(&mut self, newtype_level: u32, left: Ty, right: Ty) -> Result<(), Clash> {
        self.unify_pattern(newtype_level, true, true, left, right)
    }

    /// One top-level unification in pattern mode (`unify_gadt`,
    /// compiler/ml/ctype.ml:2739-2750, with the two flags of
    /// `set_mode_pattern`, ctype.ml:256-273, as arguments so that a test
    /// can ask for each mode `unify3` installs, ctype.ml:2352, 2368):
    /// 1. [`Checker::empty_scopes`] (`current_univar_pairs () := []`,
    ///    ctype.ml:2737: one load and one store); the
    ///    previous `umode`, `generate_equations`, `assume_injective` are
    ///    kept; `umode = Pattern`, the two flags as given, `newtype_level`
    ///    as given;
    /// 2. [`Checker::unify`] of the pair;
    /// 3. on either result: the three settings go back, `newtype_level`
    ///    is 0, and the table of assumed equalities is emptied
    ///    (`Type_pairs.clear (unify_eq_set ())`; O(capacity) when it held
    ///    a pair, one load when it did not).
    ///
    /// The equations it added stay in [`Checker::equations`]: the caller
    /// cuts them back when the case they belong to ends or when it
    /// restores a speculation ([`Checker::cut_equations`]). O(1) plus the
    /// unification. (R3h; CHECKER_REWRITE 8.9)
    pub fn unify_pattern(
        &mut self,
        newtype_level: u32,
        generate: bool,
        injective: bool,
        left: Ty,
        right: Ty,
    ) -> Result<(), Clash> {
        self.empty_scopes();
        let before = (self.umode, self.generate_equations, self.assume_injective);
        self.umode = UnifyMode::Pattern;
        let pattern = self.gadt & GADT_PATTERN;
        self.gadt |= GADT_PATTERN;
        self.generate_equations = generate;
        self.assume_injective = injective;
        self.newtype_level = newtype_level;
        let result = self.unify(left, right);
        (self.umode, self.generate_equations, self.assume_injective) = before;
        self.gadt = self.gadt & !GADT_PATTERN | pattern;
        self.newtype_level = 0;
        if !self.pairs.keys.is_empty() {
            self.pairs.keys.clear();
        }
        result
    }

    /// Cut the equations back to the first `len` (a length of
    /// [`Checker::equations`] the caller kept), last first: the
    /// `TypeTable` row of each popped entry is its `previous` again;
    /// then [`Checker::cleanup_abbrev`] when one was popped. What a
    /// caller does where OCaml drops the environment of a case
    /// (`set_state`, compiler/ml/typecore.ml:1303-1305). The `Manifest`
    /// and `Newtype` rows an equation made are not reclaimed. O(entries
    /// popped), one step each, plus the cleanup. (R3h; CHECKER_REWRITE
    /// 8.9, decision 67)
    pub fn cut_equations(&mut self, len: usize) {
        if self.equations.len() <= len {
            return;
        }
        while self.equations.len() > len {
            #[cfg(test)]
            super::steps::tick();
            let equation = self.equations.pop().expect("an equation above the length");
            self.types.rows[equation.type_index as usize] = equation.previous;
        }
        self.cleanup_abbrev();
    }

    /// The arm of `unify` for two locally abstract types under local
    /// constraints (compiler/ml/ctype.ml:2258-2269): `left` and `right`
    /// are distinct representatives, constructors WITHOUT arguments of
    /// two types, with descriptors `l` and `r`; the caller has seen that
    /// [`Checker::equations`] is not empty (`Env.has_local_constraints`).
    /// `None` when one of the two types is not a locally abstract type
    /// (`is_newtype`, ctype.ml:1862-1868: `flags & (NEWTYPE | DATATYPE |
    /// PRIVATE) == NEWTYPE`) or when the one to expand does not expand
    /// (`with Cannot_expand -> unify2 env t1 t2`): the caller goes on to
    /// [`Checker::unify_expanded`]. Otherwise, in pattern mode, `Ok` at
    /// once for a pair in the table of assumed equalities (`unify_eq`,
    /// ctype.ml:2233, which comes first); then
    /// [`Checker::expand_once`] in [`ExpandMode::Unif`] of `right` when
    /// [`Checker::find_newtype_level`] of the left type is lower (as
    /// pairs), otherwise of `left`: only the NEWER one is expanded, and
    /// once ("do not use local constraints more than necessary"). The
    /// pair of the side that was not expanded and the expansion, in the
    /// order of the two sides, is pushed as a [`FrameKind::Pair`] frame:
    /// the nested `unify` of OCaml. In `Mode::Explain` an
    /// [`FrameKind::Assumed`] frame with `left` and `right` goes below
    /// it, so that the pair is in the trace of a clash below (`raise
    /// (Unify ((t1, t2) :: trace))`, ctype.ml:2274). A clash of the
    /// expansion is the pair's clash. O(1) plus the expansion: two row
    /// loads, at most two `Newtype` loads. (R3h; CHECKER_REWRITE 8.9,
    /// decision 65)
    #[cold]
    #[inline(never)]
    fn unify_newtypes(
        &mut self,
        [left, right]: [Ty; 2],
        l: Node,
        r: Node,
    ) -> Option<Result<(), Clash>> {
        let newtype = |c: &Checker, ty: u32| c.types.info(ty).flags & (NEWTYPE | DATATYPE | PRIVATE) == NEWTYPE;
        if !newtype(self, l.a) || !newtype(self, r.a) {
            return None;
        }
        // `unify_eq t1 t2` comes first (ctype.ml:2233): in pattern mode
        // the table of assumed pairs.
        if self.umode == UnifyMode::Pattern && self.assumed_equal(left, right) {
            return Some(Ok(()));
        }
        let older = self.find_newtype_level(l.a) < self.find_newtype_level(r.a);
        let expansion = match self.expand_once(if older { right } else { left }, ExpandMode::Unif) {
            Ok(expansion) => expansion,
            Err(clash) => return Some(Err(clash)),
        };
        if expansion.0 == NONE {
            return None;
        }
        if self.g.mode == Mode::Explain {
            self.frames.push(Frame { left, right, kind: FrameKind::Assumed, extra: 0 });
        }
        if older {
            self.push_pair(left, expansion);
        } else {
            self.push_pair(expansion, right);
        }
        Some(Ok(()))
    }

    /// unify3 in pattern mode, after its first arms (a variable on either
    /// side, two universal variables, two fields: compiler/ml/ctype.ml:
    /// 2313-2326), for `[t1, t1', t2, t2']` as [`Checker::unify3`] has
    /// them; `create_recursion` is what it computed (ctype.ml:2309).
    ///
    /// 1. the pair `(t1', t2')` goes into the table of assumed equalities
    ///    (`add_type_equality`, ctype.ml:2332, 2107-2108). No occurrence
    ///    test, no link;
    /// 2. in `Mode::Explain` a [`FrameKind::Assumed`] frame with `pair`
    ///    and `swapped`; with `create_recursion` a
    ///    [`FrameKind::Recursion`] frame above it, as in expression mode
    ///    (ctype.ml:2428-2435: the repair is outside the match on
    ///    `umode`);
    /// 3. the arm, by the two heads: the table of CHECKER_REWRITE 8.9,
    ///    decision 64, first row that applies.
    ///
    /// An arm that clashes has pushed nothing; then the frames of step 2
    /// are taken off and, when `swapped`, the trace entries made since
    /// the call are reversed (ctype.ml:2301-2303). Nothing of `t1'` is
    /// put back: it was not written (`t1'.desc <- d1`, ctype.ml:2437,
    /// writes what is there). Out of line: [`Checker::unify3`] keeps the
    /// size it has. O(1) plus the arm. (R3h; the three arms marked 2 in
    /// decision 64 are R3r's)
    #[inline(never)]
    fn unify3_pattern(
        &mut self,
        [t1, t1x, t2, t2x]: [Ty; 4],
        pair: [Ty; 2],
        swapped: bool,
        create_recursion: bool,
    ) -> Result<(), Clash> {
        let (d1, d2) = (self.g.nodes[t1x.0 as usize], self.g.nodes[t2x.0 as usize]);
        self.pairs.keys.insert(PairSet::key(t1x, t2x));
        let (frames, mark) = (self.frames.len(), self.trace.len());
        if self.g.mode == Mode::Explain {
            let [left, right] = pair;
            let extra = if swapped { SWAPPED } else { 0 };
            self.frames.push(Frame { left, right, kind: FrameKind::Assumed, extra });
        }
        if create_recursion {
            self.frames.push(Frame { left: t2, right: t2x, kind: FrameKind::Recursion, extra: 0 });
        }
        let result = self.pattern_arm([t1x, t2x], d1, d2);
        if result.is_err() {
            self.frames.truncate(frames);
            if swapped {
                for entry in &mut self.trace[mark..] {
                    entry.swap(0, 1);
                }
            }
        }
        result
    }

    /// The arm of [`Checker::unify3_pattern`] for the two expanded heads
    /// `[t1x, t2x]` with descriptors `d1` and `d2`: the table of
    /// CHECKER_REWRITE 8.9, decision 64, first row that applies
    /// (compiler/ml/ctype.ml:2333-2425). It pushes nothing when it
    /// clashes. O(1) plus a push per child, or one of the callees.
    fn pattern_arm(&mut self, [t1x, t2x]: [Ty; 2], d1: Node, d2: Node) -> Result<(), Clash> {
        let plain = (d1.head | d2.head) & EXTENDED == 0;
        let generate = self.generate_equations;
        match (d1.tag(), d2.tag()) {
            (ARROW, ARROW) | (TUPLE, TUPLE) if plain => return self.push_children(d1, d2),
            (CONSTR, CONSTR) if d1.a == d2.a => {
                let arity = d1.arity();
                if arity != d2.arity() {
                    return Err(Clash);
                }
                if generate && self.assume_injective {
                    // `set_mode_pattern ~generate:true ~injective:false`
                    // (ctype.ml:2352-2354), undone by the frame.
                    let extra = 1 | 2;
                    self.frames.push(Frame { left: Ty(NONE), right: Ty(NONE), kind: FrameKind::Flags, extra });
                    self.assume_injective = false;
                } else if generate && self.types.info(d1.a).flags & (LOCAL | DATATYPE) == 0 {
                    // Per argument by injectivity, falling back (ctype.ml:
                    // 2358-2375; 8.9, decision 68), last first so that
                    // the first is taken first (`List.iter2`).
                    for i in (0..arity).rev() {
                        let (l, r) = (self.g.lists[(d1.b + 1 + i) as usize], self.g.lists[(d2.b + 1 + i) as usize]);
                        if self.types.injective(d1.a, i) {
                            self.push_pair(l, r);
                        } else {
                            self.frames.push(Frame { left: l, right: r, kind: FrameKind::Try, extra: TRY_ARGUMENT });
                        }
                    }
                    return Ok(());
                }
                self.push_lists(d1.b + 1, d2.b + 1, arity);
                return Ok(());
            }
            _ => {}
        }
        let instantiable = |c: &Checker, d: Node| d.tag() == CONSTR && d.arity() == 0 && c.types.instantiable(d.a);
        let (left, right) = (instantiable(self, d1), instantiable(self, d2));
        if generate && left && right {
            // The newer type gets the equation (ctype.ml:2376-2387).
            if self.find_newtype_level(d1.a) > self.find_newtype_level(d2.a) {
                return self.add_gadt_equation(d1.a, t2x);
            }
            return self.add_gadt_equation(d2.a, t1x);
        }
        if generate && left {
            self.reify(t2x)?;
            return self.add_gadt_equation(d1.a, t2x);
        }
        if generate && right {
            self.reify(t1x)?;
            return self.add_gadt_equation(d2.a, t1x);
        }
        if d1.tag() == CONSTR || d2.tag() == CONSTR {
            self.reify(t1x)?;
            self.reify(t2x)?;
            return if generate { self.mcomp(t1x, t2x) } else { Ok(()) };
        }
        if d1.head & d2.head & EXTENDED == 0 {
            return Err(Clash);
        }
        let (l, r) = (self.extras.descriptors[d1.a as usize], self.extras.descriptors[d2.a as usize]);
        match (l, r) {
            (ExtraDescriptor::Object, ExtraDescriptor::Object) => {
                let (fields1, fields2) = (self.g.lists[d1.b as usize], self.g.lists[d2.b as usize]);
                self.unify_fields(fields1, fields2)
            }
            // A snapshot, `unify_row`, and on a clash `reify` and `mcomp`
            // (ctype.ml:2402-2411; 8.9, decision 68).
            (ExtraDescriptor::Variant(_), ExtraDescriptor::Variant(_)) => {
                self.frames.push(Frame { left: t1x, right: t2x, kind: FrameKind::Try, extra: TRY_ROWS });
                Ok(())
            }
            (ExtraDescriptor::Nil, ExtraDescriptor::Nil) => Ok(()),
            (ExtraDescriptor::Poly, ExtraDescriptor::Poly) if d1.arity() == 1 && d2.arity() == 1 => {
                let (body1, body2) = (self.g.lists[d1.b as usize], self.g.lists[d2.b as usize]);
                self.push_pair(body1, body2);
                Ok(())
            }
            (ExtraDescriptor::Poly, ExtraDescriptor::Poly) => self.enter_poly(d1, d2),
            (ExtraDescriptor::Package(_), ExtraDescriptor::Package(_)) => {
                match self.unify_package([t1x, t2x], d1, d2) {
                    Ok(()) => Ok(()),
                    // `Not_found`: the lists reified (ctype.ml:2416-2424;
                    // 8.9, decision 63).
                    Err(Clash) => self.package_fallback(t1x, t2x),
                }
            }
            _ => Err(Clash),
        }
    }


    /// O(1): the pop of a [`FrameKind::Flags`] frame: bit 0 of `extra`
    /// is `generate_equations` and bit 1 `assume_injective`, as they
    /// were before the arguments of a constructor were entered
    /// (`set_mode_pattern`, compiler/ml/ctype.ml:256-273). Two stores.
    /// (R3h)
    #[inline]
    fn put_flags(&mut self, extra: u32) {
        self.generate_equations = extra & 1 != 0;
        self.assume_injective = extra & 2 != 0;
    }

    /// The pop of a [`FrameKind::Try`] frame (CHECKER_REWRITE 8.9,
    /// decision 68).
    ///
    /// PENDING (`extra` is [`TRY_ARGUMENT`] or [`TRY_ROWS`]): the attempt
    /// starts. A [`Try`] record is pushed: `g.speculate()`, the index the
    /// frame is about to have, the lengths of `trace`, `saved` and
    /// `scopes`, the two flags as they are, and bit 2 for [`TRY_ROWS`];
    /// the frame is pushed again with the record's index as `extra`.
    /// Then, for an argument: both flags off and the pair of `left` and
    /// `right` pushed above the frame; for two variants:
    /// [`Checker::open_row`] of both representatives and
    /// [`Checker::unify_row`] of them, whose clash is this function's
    /// (with no pair: `Unify []` is the row's own trace), to be recovered
    /// by the caller.
    ///
    /// STARTED (`extra` is a record index, the last record): the attempt
    /// succeeded: the record is popped, `g.keep` of its speculation, the
    /// two flags put back.
    ///
    /// Cold: only pattern mode pushes the frame. O(1) plus `unify_row`.
    /// (R3r)
    #[cold]
    #[inline(never)]
    fn try_frame(&mut self, frame: Frame) -> Result<(), [Ty; 2]> {
        if frame.extra & (TRY_ARGUMENT | TRY_ROWS) == 0 {
            let record = self.tries.pop().expect("the record of a started attempt");
            debug_assert_eq!(self.tries.len() as u32, frame.extra);
            self.g.keep(record.speculation);
            self.put_flags(u32::from(record.flags));
            return Ok(());
        }
        let rows = frame.extra & TRY_ROWS != 0;
        let index = self.tries.len() as u32;
        let record = Try {
            speculation: self.g.speculate(),
            frame: self.frames.len() as u32,
            trace: self.trace.len() as u32,
            saved: self.saved.len() as u32,
            scopes: self.scopes.len() as u32,
            flags: u8::from(self.generate_equations)
                | u8::from(self.assume_injective) << 1
                | u8::from(rows) << 2
                | (self.gadt & GADT_TRACING) << 2,
        };
        self.tries.push(record);
        self.frames.push(Frame { extra: index, ..frame });
        if !rows {
            // `set_mode_pattern ~generate:false ~injective:false`.
            self.generate_equations = false;
            self.assume_injective = false;
            self.push_pair(frame.left, frame.right);
            return Ok(());
        }
        let (left, right) = (self.g.repr(frame.left), self.g.repr(frame.right));
        let (d1, d2) = (self.open_row(left), self.open_row(right));
        self.unify_row([left, right], d1, d2).map_err(|Clash| [Ty(NONE), Ty(NONE)])
    }

    /// A clash reached [`Checker::unify_distinct`] whose frames start at
    /// `base`: `None` when no [`Try`] record has its frame at or above
    /// `base` (the clash is the caller's). Otherwise the LAST record is
    /// taken off: `frames` is cut to its frame (the frame itself goes),
    /// [`Checker::restore`] of its speculation (`backtrack snap`, which
    /// cleans the memos when something was written), `scopes`, `trace`
    /// and `saved` cut to its lengths, the two flags put back; then
    /// `reify(left)`, `reify(right)` and, with bit 2 of the record and
    /// `generate_equations` on, `mcomp(left, right)`: `Some` of their
    /// result. The equations and the fresh types made inside the attempt
    /// stay (`env` is not part of OCaml's snapshot,
    /// compiler/ml/btype.ml:753-784). It reads the last record and
    /// nothing else of `tries` or `frames`: O(writes restored) plus the
    /// three callees, one step a record taken. (R3r; CHECKER_REWRITE 8.9,
    /// decision 68)
    pub fn recover(&mut self, base: usize) -> Option<Result<(), Clash>> {
        if (self.tries.last()?.frame as usize) < base {
            return None;
        }
        #[cfg(test)]
        super::steps::tick();
        let record = self.tries.pop().expect("the last record");
        let frame = self.frames[record.frame as usize];
        // The scopes entered inside the attempt are left as a clash
        // leaves them (ctype.ml:1677-1679): the floor too.
        if self.scopes.len() != record.scopes as usize {
            self.leave_scopes(record.frame as usize);
        }
        self.frames.truncate(record.frame as usize);
        self.restore(record.speculation);
        self.scopes.truncate(record.scopes as usize);
        self.trace.truncate(record.trace as usize);
        self.saved.truncate(record.saved as usize);
        self.put_flags(u32::from(record.flags));
        // Tracing is what it was where the attempt started: every
        // `unify` between the clash and the handler put its own back
        // (`reset_trace_gadt_instances`, ctype.ml:2270). (R3s)
        self.gadt = self.gadt & !GADT_TRACING | (record.flags >> 2 & GADT_TRACING);
        // `backtrack snap; reify env t1; reify env t2` and, for two
        // variants, `if generate_equations then mcomp` (ctype.ml:
        // 2370-2374, 2407-2411).
        let fallback = self.reify(frame.left).and_then(|()| self.reify(frame.right));
        Some(fallback.and_then(|()| {
            if record.flags & 4 != 0 && self.generate_equations {
                self.mcomp(frame.left, frame.right)
            } else {
                Ok(())
            }
        }))
    }

    /// The failure path of [`Checker::unify_distinct`] while an attempt
    /// of pattern mode is open: `pair` is the clash `run_frames`
    /// returned. A loop of [`Checker::recover`]: `None`: `Err` of the
    /// pair in hand; `Some(Ok(()))`: [`Checker::resume_frames`], whose
    /// `Ok` is this function's and whose clash is the pair in hand for
    /// the next turn; `Some(Err(_))`: the fallback clashed, the pair in
    /// hand is none (`Unify []`, or the pair `reify` put on the trace)
    /// and the next record is asked. Cold. O(records taken) plus the
    /// callees. (R3r)
    #[cold]
    #[inline(never)]
    fn recover_frames(&mut self, base: usize, pair: [Ty; 2]) -> Result<(), [Ty; 2]> {
        let mut pair = pair;
        loop {
            match self.recover(base) {
                None => return Err(pair),
                Some(Ok(())) => match self.resume_frames(base) {
                    Ok(()) => return Ok(()),
                    Err(next) => pair = next,
                },
                Some(Err(Clash)) => pair = [Ty(NONE), Ty(NONE)],
            }
        }
    }

    /// Go on with the frames above `base` after an attempt was recovered:
    /// frames are popped as `run_frames` pops them, arm for arm, until a
    /// [`FrameKind::Pair`] whose two representatives differ, which goes
    /// to `run_frames` as its root pair, or until none is left. The hot
    /// loop of `run_frames` is not changed for it: this is its cold
    /// second entry, and a `match` on every [`FrameKind`] keeps the two
    /// in step. O(frames popped). (R3r)
    #[cold]
    #[inline(never)]
    fn resume_frames(&mut self, base: usize) -> Result<(), [Ty; 2]> {
        while self.frames.len() > base {
            let frame = self.frames.pop().expect("a frame above the base");
            match frame.kind {
                FrameKind::Pair => {
                    let (left, right) = (self.g.repr(frame.left), self.g.repr(frame.right));
                    if left != right {
                        self.late_pair(left, right)?;
                    }
                }
                FrameKind::Untrace => self.gadt &= !GADT_TRACING,
                FrameKind::Linked => self.saved.truncate((frame.extra & !SWAPPED) as usize),
                FrameKind::LeavePoly => self.leave_poly(frame),
                FrameKind::Fields => self.saved.truncate(frame.extra as usize),
                FrameKind::Field => self.unify_field(frame)?,
                FrameKind::FieldEnd | FrameKind::Assumed => {}
                FrameKind::RowField => self.unify_row_field(frame)?,
                FrameKind::RowFieldEnd => self.row_field_end(frame)?,
                FrameKind::RowEnd => self.row_end(frame),
                FrameKind::Flags => self.put_flags(frame.extra),
                FrameKind::Try => self.try_frame(frame)?,
                FrameKind::PackageEnd => {
                    if self.package_end(frame).is_err() && self.package_fallback(frame.left, frame.right).is_err() {
                        return Err([Ty(NONE), Ty(NONE)]);
                    }
                }
                FrameKind::Recursion => {
                    if self.repair_recursion(frame.left, frame.right).is_err() {
                        return Err([Ty(NONE), Ty(NONE)]);
                    }
                }
            }
        }
        Ok(())
    }

    /// The failure path of the explaining mode: the trace, outermost pair
    /// first (each enclosing `unify` adds its pair, ctype.ml:2272), and the
    /// descriptors of the linked structure nodes enclosing the failure put
    /// back, innermost first (`t1'.desc <- d1`, ctype.ml:2437). The
    /// enclosing pairs are the `Linked` frames above `base` and, in
    /// pattern mode, the `Assumed` ones, which have a pair and no
    /// descriptor; the entries a
    /// nested unification already wrote stay after this one's. O(frames
    /// above `base` + trace entries since `trace_base`).
    /// Below a swapped `unify3` every entry is reversed
    /// (`List.map (fun (x, y) -> (y, x))`, ctype.ml:2303), twice swapped is
    /// as made. A clash of a recursion repair has no pair of its own (`NONE`).
    /// The entries already in the trace (`inner`: a `set_more` pair, a
    /// failed lowering's) were made below every frame, so they are reversed
    /// when the frames' parity is swapped (ctype.ml:2303), one step each.
    #[cold]
    fn explain_failure(&mut self, base: usize, trace_base: usize, left: Ty, right: Ty) {
        let inner = self.trace.len() - trace_base;
        let mut swapped = false;
        for index in base..self.frames.len() {
            let frame = self.frames[index];
            if frame.kind == FrameKind::Linked || frame.kind == FrameKind::Assumed {
                let entry = [frame.left, frame.right];
                self.trace
                    .push(if swapped { [entry[1], entry[0]] } else { entry });
                swapped ^= frame.extra & SWAPPED != 0;
            } else if frame.kind == FrameKind::FieldEnd {
                // `(Tfield f1, Tfield f2) :: trace` (ctype.ml:2493-2510).
                let entry = self.field_trace_pair(frame.left, frame.right);
                self.trace
                    .push(if swapped { [entry[1], entry[0]] } else { entry });
            } else if frame.kind == FrameKind::RowFieldEnd {
                // `(mkvariant [(l, f1)] true, mkvariant [(l, f2)] true) ::
                // trace` (ctype.ml:2624-2628).
                let entry = self.row_trace_pair(frame);
                self.trace
                    .push(if swapped { [entry[1], entry[0]] } else { entry });
            }
        }
        if left.0 != NONE {
            self.trace.push(if swapped {
                [right, left]
            } else {
                [left, right]
            });
        }
        if swapped {
            for entry in &mut self.trace[trace_base..trace_base + inner] {
                #[cfg(test)]
                super::steps::tick();
                entry.swap(0, 1);
            }
        }
        self.trace[trace_base..].rotate_left(inner);
        for index in (base..self.frames.len()).rev() {
            let frame = self.frames[index];
            if frame.kind == FrameKind::Linked {
                let slot = (frame.extra & !SWAPPED) as usize;
                let descriptor = self.saved[slot];
                let target = Ty(self.saved[slot + 1].a);
                self.g.write(target, descriptor);
            } else if frame.kind == FrameKind::Fields {
                // `rest1.desc <- d1; rest2.desc <- d2` (ctype.ml:2513-2517):
                // the descriptor only. A rest lowered before the clash (by
                // unify2's `update_level`, ctype.ml:2283-2285) keeps its level.
                let slot = frame.extra as usize;
                for (rest, saved) in [(frame.left, slot), (frame.right, slot + 1)] {
                    let level = self.g.nodes[rest.0 as usize].level;
                    let descriptor = Node {
                        level,
                        ..self.saved[saved]
                    };
                    self.g.write(rest, descriptor);
                }
            }
        }
    }

    /// O(1): push one pair.
    #[inline]
    pub(super) fn push_pair(&mut self, left: Ty, right: Ty) {
        self.frames.push(Frame {
            left,
            right,
            kind: FrameKind::Pair,
            extra: 0,
        });
    }

    /// O(len): push the pairs of two list ranges, last first.
    pub(super) fn push_lists(&mut self, left: u32, right: u32, len: u32) {
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

    /// O(1): whether two extended descriptors are both fields.
    #[inline]
    fn both_fields(&self, left: Node, right: Node) -> bool {
        let field = |node: Node| {
            matches!(self.extras.descriptors[node.a as usize], ExtraDescriptor::Field { .. })
        };
        field(left) && field(right)
    }

    /// O(1): whether two extended descriptors are both universal
    /// variables.
    #[inline]
    fn both_univars(&self, left: Node, right: Node) -> bool {
        let univar = |node: Node| {
            matches!(
                self.extras.descriptors[node.a as usize],
                ExtraDescriptor::Univar(_)
            )
        };
        univar(left) && univar(right)
    }

    /// O(1): whether two extended descriptors are both variant rows.
    #[inline]
    fn both_variants(&self, left: Node, right: Node) -> bool {
        let variant = |node: Node| {
            matches!(self.extras.descriptors[node.a as usize], ExtraDescriptor::Variant(_))
        };
        variant(left) && variant(right)
    }

    /// The children of two extended descriptors, after the link of unify3
    /// (compiler/ml/ctype.ml:2400-2424): `[t1x, t2x]` are the two nodes,
    /// `left` and `right` the descriptors they had. Two objects:
    /// [`Checker::unify_fields`] of their slot 0 (ctype.ml:2400). Two
    /// `Tnil`: nothing (ctype.ml:2412). Two polymorphic types without
    /// variables (arity 1): the pair of their bodies (ctype.ml:2413;
    /// decision 22 of 8.6). Two variants: [`Checker::unify_row`]. Two
    /// polymorphic types with variables: [`Checker::enter_poly`]
    /// (ctype.ml:2414-2415; R3g). Two packages:
    /// [`Checker::unify_package`] (ctype.ml:2416-2423; R3p). Anything else,
    /// a universal variable against another extended node included, is a
    /// clash (`_, _ -> raise (Unify [])`, ctype.ml:2425; two universal
    /// variables never come here: `unify3` takes them first). Like
    /// [`Checker::push_children`], it pushes nothing when it fails. O(1)
    /// plus the callee.
    fn extended_children(&mut self, [t1x, t2x]: [Ty; 2], left: Node, right: Node) -> Result<(), Clash> {
        let (l, r) = (
            self.extras.descriptors[left.a as usize],
            self.extras.descriptors[right.a as usize],
        );
        match (l, r) {
            (ExtraDescriptor::Object, ExtraDescriptor::Object) => {
                let (fields1, fields2) = (self.g.lists[left.b as usize], self.g.lists[right.b as usize]);
                self.unify_fields(fields1, fields2)
            }
            (ExtraDescriptor::Nil, ExtraDescriptor::Nil) => Ok(()),
            // `Tpoly (t1, []), Tpoly (t2, []) -> unify env t1 t2`: push the
            // pair of the two slots 0 and return `Ok(())`.
            (ExtraDescriptor::Poly, ExtraDescriptor::Poly) if left.arity() == 1 && right.arity() == 1 => {
                let body1 = self.g.lists[left.b as usize];
                let body2 = self.g.lists[right.b as usize];
                self.push_pair(body1, body2);
                Ok(())
            }
            (ExtraDescriptor::Poly, ExtraDescriptor::Poly) => self.enter_poly(left, right),
            (ExtraDescriptor::Variant(_), ExtraDescriptor::Variant(_)) => {
                self.unify_row([t1x, t2x], left, right)
            }
            (ExtraDescriptor::Package(_), ExtraDescriptor::Package(_)) => {
                self.unify_package([t1x, t2x], left, right)
            }
            _ => Err(Clash),
        }
    }

    /// The loop of [`Checker::unify_distinct`]: the root pair `left`,
    /// `right` (two distinct representatives) goes to
    /// [`Checker::unify_pair`] without a frame, then the frames that call
    /// left above `base` are popped, O(1) each plus the callee. A popped
    /// pair whose two sides are one node is skipped (`unify_eq`,
    /// ctype.ml:2233). One call site of `unify_pair`, so that it stays
    /// inline. On a clash returns the failing pair, as it stood, and leaves
    /// the frames: for the root pair, the frames its call left, as when the
    /// root was a popped frame.
    fn run_frames(&mut self, base: usize, left: Ty, right: Ty) -> Result<(), [Ty; 2]> {
        let [mut left, mut right] = [left, right];
        loop {
            if self.unify_pair(left, right).is_err() {
                return Err([left, right]);
            }
            // The next pair whose sides differ, running the other frames.
            loop {
                if self.frames.len() <= base {
                    return Ok(());
                }
                let Some(frame) = self.frames.pop() else {
                    return Ok(());
                };
                match frame.kind {
                    FrameKind::Pair => {
                        left = self.g.repr(frame.left);
                        right = self.g.repr(frame.right);
                        if left != right {
                            break;
                        }
                    }
                    FrameKind::Linked => self.saved.truncate((frame.extra & !SWAPPED) as usize),
                    FrameKind::LeavePoly => self.leave_poly(frame),
                    FrameKind::Fields => self.saved.truncate(frame.extra as usize),
                    FrameKind::Field => self.unify_field(frame)?,
                    FrameKind::FieldEnd => {}
                    FrameKind::RowField => self.unify_row_field(frame)?,
                    FrameKind::RowFieldEnd => self.row_field_end(frame)?,
                    FrameKind::RowEnd => self.row_end(frame),
                    // The two flags go back (8.9, decision 64).
                    FrameKind::Flags => self.put_flags(frame.extra),
                    FrameKind::Assumed => {}
                    // Never above the base of this loop: `late_pair`
                    // runs it above the frame. (R3s)
                    FrameKind::Untrace => self.gadt &= !GADT_TRACING,
                    // The attempt starts, or it succeeded (8.9, decision
                    // 68). A clash of this loop is offered to the open
                    // attempts by the caller (`Checker::recover_frames`).
                    FrameKind::Try => self.try_frame(frame)?,
                    FrameKind::PackageEnd => {
                        // A clash here is the enclosing pair's (`Unify []`);
                        // in pattern mode the two lists are reified instead
                        // (`Not_found`, ctype.ml:2420-2422; decision 63).
                        if self.package_end(frame).is_err()
                            && self.package_fallback(frame.left, frame.right).is_err()
                        {
                            return Err([Ty(NONE), Ty(NONE)]);
                        }
                    }
                    FrameKind::Recursion => {
                        // A clash here is the enclosing pair's: it adds no
                        // pair of its own to the trace (`Unify []`).
                        if self.repair_recursion(frame.left, frame.right).is_err() {
                            return Err([Ty(NONE), Ty(NONE)]);
                        }
                    }
                }
            }
        }
    }

    /// `update_level` of `ty` to `level`: [`Checker::lower`]. O(1) for the
    /// generic level, which nothing is above, and for a representative that
    /// is not above `level`, which the outer `update_level` leaves alone
    /// (`if ty.level > level`, compiler/ml/ctype.ml:635; `Checker::lower`
    /// makes the same test before its scoped walk): one `repr`, one load and
    /// one compare. Otherwise the callee's cost.
    #[inline]
    fn lower_to(&mut self, ty: Ty, level: u32) -> Result<(), Clash> {
        if level == GENERIC {
            return Ok(());
        }
        let root = self.g.repr(ty);
        if self.g.nodes[root.0 as usize].level <= level {
            return Ok(());
        }
        self.lower(root, level)
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

    /// Amortized O(1): a fresh generation of `instance_marks`, which
    /// grows to the graph's length; a wrap of the counter clears the
    /// marks once. The array is grown the first time a unit adds a chain
    /// or copies with a member: four bytes a node in a unit that has a
    /// member, nothing in any other. (R3s)
    pub(super) fn fresh_instance_marks(&mut self) -> u32 {
        if self.instance_marks.len() < self.g.nodes.len() {
            self.instance_marks.resize(self.g.nodes.len(), 0);
        }
        if self.instance_mark_generation == u32::MAX {
            self.instance_marks.fill(0);
            self.instance_mark_generation = 0;
        }
        self.instance_mark_generation += 1;
        self.instance_mark_generation
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

    /// Whether `node` is reachable from `ty`: first
    /// [`Checker::unreached_within_budget`]; when that does not decide, one
    /// step a node, each node once (marks), explicit stack. With `deep`
    /// objects and variant rows are crossed (`deep_occur`, ctype.ml:1775),
    /// otherwise not (`occur_rec`, ctype.ml:1403). No level cut. Cost: at
    /// most [`PROBE_BUDGET`] + 1 steps of the probe, then, when it did not
    /// decide, the marked walk's O(nodes of `ty`).
    fn reaches(&mut self, node: Ty, ty: Ty, deep: bool) -> bool {
        if self.unreached_within_budget(node, ty, deep) {
            return false;
        }
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

    /// The probe of [`Checker::reaches`], `occur_reaches_budget`
    /// (compiler/ml/ctype.ml:1432-1465): the same edges as the marked walk
    /// in the same mode (objects and variant rows crossed only with `deep`,
    /// [`Checker::stops_occurrence`]), explicit stack on `g.work`, no marks,
    /// at most [`PROBE_BUDGET`] nodes. `true` only when the walk finished
    /// within the budget without meeting `node`: then no path from `ty`
    /// reaches it. `false` when it met `node` or the budget ran out (a large
    /// type, a cycle or heavy sharing, which a walk without marks visits
    /// once per path); the caller then decides with the marked walk. One
    /// step a node visited, at most [`PROBE_BUDGET`] + 1; allocates nothing
    /// beyond `g.work`'s growth.
    fn unreached_within_budget(&mut self, node: Ty, ty: Ty, deep: bool) -> bool {
        self.g.work.clear();
        self.g.work.push(ty);
        let mut budget = PROBE_BUDGET;
        while let Some(ty) = self.g.work.pop() {
            let ty = self.g.repr(ty);
            #[cfg(test)]
            super::steps::tick();
            if ty == node || budget == 0 {
                self.g.work.clear();
                return false;
            }
            budget -= 1;
            let descriptor = self.g.nodes[ty.0 as usize];
            if deep || !self.stops_occurrence(descriptor) {
                self.g.children(descriptor, false);
            }
        }
        true
    }

    /// O(1): the checking mode, fixed for the unit (CHECKER_REWRITE 3.4).
    #[inline]
    pub fn mode(&self) -> Mode {
        self.g.mode
    }
}

/// O(1): whether a descriptor has no child: a constructor or a tuple of
/// arity 0 with no flag bit (`TUPLE` is `CONSTR | 1`, so one mask and one
/// compare). A variable, a link, an arrow (its result is a child), an
/// extended node and any node with arguments are not. It tests the whole
/// head, so a node that is not a representative (head `LINK`) is never
/// childless.
#[inline(always)]
fn childless(node: Node) -> bool {
    const { assert!(TUPLE == CONSTR | 1) };
    node.head & !1 == CONSTR
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
        // One per started attempt of pattern mode (CHECKER_REWRITE 8.9,
        // decision 68).
        assert_eq!(std::mem::size_of::<Try>(), 40);
        // One per scope entered, per addition to a set and per case
        // (CHECKER_REWRITE 8.11; 8.6, decision 98).
        assert_eq!(std::mem::size_of::<InstanceScope>(), 12);
        assert_eq!(std::mem::size_of::<InstanceMember>(), 8);
        assert_eq!(std::mem::size_of::<CaseMark>(), 12);
    }
}
