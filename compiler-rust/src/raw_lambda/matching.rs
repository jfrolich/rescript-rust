//! Pattern matching compilation — Layer 1: Core types and infrastructure.
//!
//! This is a 1:1 port of OCaml's `matching.ml` lines 1-374.
//! It defines the core data structures (matrix, context, jumps, pattern_matching)
//! and the operations on them used by the pattern matching compiler.

use super::key_encode::{KeyEncode, KeyOut};
use crate::fast_hash::AHashMap as HashMap;
use crate::raw_lambda::builder::{RawLambdaBuilder, RawLambdaRead};
use crate::types::path::PathView;
use std::borrow::{Borrow, Cow};
use std::collections::BTreeSet;
use std::collections::VecDeque;
use std::fmt::Write as _;
use std::ops::Deref;
use std::sync::{Arc, OnceLock};

use crate::ident::{Ident, IdentFlags};
use crate::lambda::LamLoc;
use crate::lambda::LetKind;
use crate::lambda::arena::{LamArena, Node, View};
use crate::lambda::lam_constant::PointerInfo;
use crate::lambda::lam_primitive::Mutable;
use crate::lambda::{Comparison, FieldDbgInfo, Primitive, TagInfo};
use crate::location::Location;
use crate::parse_arena::LocIdx;
use crate::raw_lambda::loc::LocArena;
use crate::raw_lambda::switch::Shared;
use crate::raw_lambda::typeopt::{
    constructor_has_optional_shape, constructor_payload_is_unboxed, type_cannot_contain_undefined,
    type_cannot_contain_undefined_no_env,
};
use crate::raw_lambda::{RawLambda, RawLambdaSwitch};
use crate::types::asttypes::MutableFlag;
use crate::types::btype;
use crate::types::context::TypeContext;
use crate::types::decl::{ConstructorDescription, LabelDescription, RecordRepresentation};
use crate::types::parmatch::{int_range, make_int_range};
use crate::types::type_expr::TypeExprRef;
use crate::types::type_expr::{RowDesc, RowField};
use crate::types::typedtree::Partial;
use crate::types::typedtree::{
    Constant, EnvRef, Pattern, PatternDesc, TPatIdx, TPatList, TypedArena,
};
use std::cell::RefCell;

/// Shared action carried by the pattern-matching compiler.
///
/// OCaml `compiler/ml/matching.ml:29-34,659-1090` keeps actions as immutable
/// lambda values in lists, so copying case matrices shares those actions by
/// pointer. Raw Lambda terms are arena handles, so an action is shared the
/// same way; the action itself is shared so its `make_key` result is
/// computed once.
#[derive(Clone)]
struct MatchAction(Arc<MatchActionData>);

struct MatchActionData {
    kind: MatchActionKind,
    normalized_key: OnceLock<Option<String>>,
}

/// A case's right-hand side as translation hands it to matching
/// (`compiler/ml/matching.ml:348-360`): the guard stays data until the
/// fallthrough it needs is known.
pub struct CaseAction {
    /// The guard, if the case has one.
    pub guard: Option<RawLambda>,
    /// The case body.
    pub body: RawLambda,
}

impl CaseAction {
    /// `Matching.unguarded`.
    pub fn unguarded(body: RawLambda) -> Self {
        Self { guard: None, body }
    }

    /// `Matching.guarded`.
    pub fn guarded(guard: RawLambda, body: RawLambda) -> Self {
        Self {
            guard: Some(guard),
            body,
        }
    }
}

impl From<RawLambda> for CaseAction {
    fn from(body: RawLambda) -> Self {
        Self::unguarded(body)
    }
}

/// The stand-in fallthrough when actions are compared by key
/// (`compiler/ml/matching.ml:381-386`). OCaml makes a fresh variable per
/// comparison so no real action can mention it; a negative stamp is never
/// allocated, which gives the same guarantee and lets keys be cached.
fn fallthrough_stand_in<B: RawLambdaBuilder>(b: &B) -> RawLambda {
    b.var(Ident::new(
        "fallthrough",
        -1,
        crate::ident::IdentFlags::NONE,
    ))
}

enum MatchActionKind {
    /// A case's guard and body.
    Case {
        guard: Option<RawLambda>,
        body: RawLambda,
    },
    Bind {
        kind: LetKind,
        id: Ident,
        arg: RawLambda,
        action: MatchAction,
    },
}

impl MatchAction {
    fn new(action: RawLambda) -> Self {
        Self::from_case(CaseAction::unguarded(action))
    }

    fn from_case(action: CaseAction) -> Self {
        Self::from_kind(MatchActionKind::Case {
            guard: action.guard,
            body: action.body,
        })
    }

    fn from_kind(kind: MatchActionKind) -> Self {
        Self(Arc::new(MatchActionData {
            kind,
            normalized_key: OnceLock::new(),
        }))
    }

    fn bind<B: RawLambdaBuilder>(self, b: &B, kind: LetKind, id: Ident, arg: RawLambda) -> Self {
        // OCaml `compiler/ml/matching.ml:556-566` calls
        // `Lambda.bind Alias id arg action`, and `compiler/ml/lambda.ml:560-565`
        // shares the immutable action below the new `Llet`. The `Llet` is
        // built when the action is placed (`body_with`), since a guarded
        // action's fallthrough is only known then.
        match b.as_var(arg) {
            Some(v) if v.same(&id) => self,
            _ => Self::from_kind(MatchActionKind::Bind {
                kind,
                id,
                arg,
                action: self,
            }),
        }
    }

    /// `Matching.action_body_with ~fail` (`compiler/ml/matching.ml:370-376`):
    /// the guard falls through to `fail`, under the action's bindings.
    fn body_with<B: RawLambdaBuilder>(&self, b: &B, fail: RawLambda) -> RawLambda {
        match &self.0.kind {
            MatchActionKind::Case { guard: None, body } => *body,
            MatchActionKind::Case {
                guard: Some(guard),
                body,
            } => b.if_(*guard, *body, fail),
            MatchActionKind::Bind {
                kind,
                id,
                arg,
                action,
            } => {
                let body = action.body_with(b, fail);
                b.let_(*kind, *id, *arg, body)
            }
        }
    }

    /// An unguarded action's term (`action_body_with ~fail:lambda_unit`).
    fn to_raw<B: RawLambdaBuilder>(&self, b: &B) -> RawLambda {
        if let MatchActionKind::Case { guard: None, body } = &self.0.kind {
            return *body;
        }
        let unit = lambda_unit(b);
        self.body_with(b, unit)
    }

    fn normalized_key<B: RawLambdaBuilder>(&self, b: &B) -> Option<&str> {
        // OCaml `compiler/ml/lambda.ml:432-466` computes `Lambda.make_key`, and
        // `compiler/ml/matching.ml:489-500,708-846` compares those pure keys while
        // shuffling the same immutable actions through match matrices. Cache the
        // key beside the shared action so Rust preserves the same result without
        // materializing delayed `Llet` wrappers.
        self.0
            .normalized_key
            .get_or_init(|| make_key_string_action(b, self))
            .as_deref()
    }

    fn is_guarded(&self) -> bool {
        match &self.0.kind {
            MatchActionKind::Case { guard, .. } => guard.is_some(),
            MatchActionKind::Bind { action, .. } => action.is_guarded(),
        }
    }

    /// `Matching.action_free_variables` (`compiler/ml/matching.ml:388-397`).
    fn free_variables(&self, a: &impl RawLambdaRead) -> IdentSet {
        match &self.0.kind {
            MatchActionKind::Case { guard, body } => {
                let mut fv = raw_lambda_free_variables(a, *body);
                if let Some(guard) = guard {
                    fv.extend(raw_lambda_free_variables(a, *guard));
                }
                fv
            }
            MatchActionKind::Bind {
                id, arg, action, ..
            } => {
                let mut fv = raw_lambda_free_variables(a, *arg);
                fv.extend(action.free_variables(a));
                fv.remove(id);
                fv
            }
        }
    }
}

type Clause<'p> = (Vec<&'p Pattern>, MatchAction);

/// An or-pattern handler: the matrix of its rows, its exit label, the
/// variables it passes to the handler, and the matching of its rows.
type OrHandler<'p> = (Matrix<'p>, i32, Vec<Ident>, PatternMatching<'p>);

/// A constructor case and its action.
type ConstrCase = (std::sync::Arc<ConstructorDescription>, RawLambda);

/// Match arguments being collected before they become a [`MatchArgs`].
type ArgsBuf = smallvec::SmallVec<[(RawLambda, LetKind); 8]>;

/// Shared match arguments used while compiling pattern matrices.
///
/// OCaml `compiler/ml/matching.ml:814-1090` passes immutable `args` lists
/// through `split_or`, `precompile_var`, and `precompile_or`; constructing a
/// `Pm`/`PmOr` node shares that list. Rust used `Vec<(RawLambda, LetKind)>`
/// directly, so every `args.to_vec()` recursively cloned raw-lambda scrutinees.
/// Store the backing vector once and represent OCaml tail lists with a start
/// offset to preserve the same functional sharing.
#[derive(Clone)]
pub struct MatchArgs {
    values: Arc<[(RawLambda, LetKind)]>,
    start: usize,
}

impl MatchArgs {
    /// Builds the shared list in one allocation: the items are gathered
    /// inline first, since most argument lists are short.
    fn new(values: impl IntoIterator<Item = (RawLambda, LetKind)>) -> Self {
        let items: ArgsBuf = values.into_iter().collect();
        Self {
            values: Arc::from(items.as_slice()),
            start: 0,
        }
    }

    /// `head :: tail`.
    fn cons(head: (RawLambda, LetKind), tail: &[(RawLambda, LetKind)]) -> Self {
        Self::new(std::iter::once(head).chain(tail.iter().copied()))
    }

    fn tail(&self, count: usize) -> Self {
        assert!(
            self.start + count <= self.values.len(),
            "MatchArgs::tail past end"
        );
        Self {
            values: Arc::clone(&self.values),
            start: self.start + count,
        }
    }

    fn as_slice(&self) -> &[(RawLambda, LetKind)] {
        &self.values[self.start..]
    }
}

impl Deref for MatchArgs {
    type Target = [(RawLambda, LetKind)];

    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

// ============================================================================
// Omega (wildcard) helpers — ported from parmatch.ml
// ============================================================================

/// Backing storage of a [`PatArena`] overlay.
#[derive(Default)]
pub struct PatStore {
    pats: typed_arena::Arena<Pattern>,
    lists: typed_arena::Arena<TPatIdx>,
}

/// The patterns a match is compiled from: the typed tree's, plus an overlay
/// of patterns synthesized while compiling it. Matrices, contexts and
/// default environments hold `&'p Pattern` rows that borrow either, the way
/// OCaml's immutable pattern lists share their elements
/// (`compiler/ml/matching.ml`). Sub-patterns are handles; overlay handles
/// carry a flag bit, so every lookup goes through this type.
pub struct PatArena<'p> {
    ta: &'p TypedArena,
    store: &'p PatStore,
    overlay: RefCell<Vec<&'p Pattern>>,
    overlay_lists: RefCell<Vec<&'p [TPatIdx]>>,
    /// Overlay handle of each overlay pattern (and the shared wildcard), by
    /// address, for [`PatArena::handle`].
    overlay_by_addr: RefCell<ahash::AHashMap<usize, TPatIdx>>,
}

impl<'p> PatArena<'p> {
    pub(crate) fn new(ta: &'p TypedArena, store: &'p PatStore) -> Self {
        let pa = PatArena {
            ta,
            store,
            overlay: RefCell::new(Vec::new()),
            overlay_lists: RefCell::new(Vec::new()),
            overlay_by_addr: RefCell::new(ahash::AHashMap::new()),
        };
        let omega_idx = pa.push(omega_owned());
        pa.overlay_by_addr
            .borrow_mut()
            .insert(omega() as *const Pattern as usize, omega_idx);
        pa
    }

    fn store_overlay(&self, p: Pattern) -> (TPatIdx, &'p Pattern) {
        let r: &'p Pattern = self.store.pats.alloc(p);
        let mut overlay = self.overlay.borrow_mut();
        let idx = TPatIdx::overlay(overlay.len());
        overlay.push(r);
        self.overlay_by_addr
            .borrow_mut()
            .insert(r as *const Pattern as usize, idx);
        (idx, r)
    }

    /// Store a synthesized pattern.
    pub(crate) fn alloc(&self, p: Pattern) -> &'p Pattern {
        self.store_overlay(p).1
    }

    /// Store a synthesized pattern, for use as a sub-pattern.
    pub(crate) fn push(&self, p: Pattern) -> TPatIdx {
        self.store_overlay(p).0
    }

    /// A pattern by handle.
    pub(crate) fn pat(&self, idx: TPatIdx) -> &'p Pattern {
        match idx.overlay_index() {
            Some(i) => self.overlay.borrow()[i],
            None => self.ta.pattern(idx),
        }
    }

    /// The handles of a pattern list.
    pub(crate) fn list(&self, list: TPatList) -> &'p [TPatIdx] {
        match crate::types::tast_arena::overlay_pattern_list_index(list) {
            Some(i) => self.overlay_lists.borrow()[i],
            None => self.ta.pattern_list(list),
        }
    }

    /// The patterns of a list.
    pub(crate) fn pats(&self, list: TPatList) -> impl ExactSizeIterator<Item = &'p Pattern> + '_ {
        self.list(list).iter().map(move |&idx| self.pat(idx))
    }

    /// Store a list of handles.
    pub(crate) fn push_list(&self, items: impl IntoIterator<Item = TPatIdx>) -> TPatList {
        let items: &'p [TPatIdx] = self.store.lists.alloc_extend(items);
        if items.is_empty() {
            return TPatList::EMPTY;
        }
        let mut lists = self.overlay_lists.borrow_mut();
        let list = crate::types::tast_arena::overlay_pattern_list(lists.len(), items.len());
        lists.push(items);
        list
    }

    /// The handle of a pattern reference, for use as a sub-pattern: its own
    /// handle when it is stored here or in the typed tree, otherwise a
    /// stored copy.
    pub(crate) fn handle(&self, p: &Pattern) -> TPatIdx {
        if let Some(idx) = self.ta.pattern_handle(p) {
            return idx;
        }
        if let Some(&idx) = self
            .overlay_by_addr
            .borrow()
            .get(&(p as *const Pattern as usize))
        {
            return idx;
        }
        self.push(p.clone())
    }

    /// The shared wildcard, as a sub-pattern.
    pub(crate) fn omega_idx(&self) -> TPatIdx {
        self.handle(omega())
    }

    /// `n` wildcards, as the sub-patterns of a new pattern (OCaml
    /// `omega_list`).
    pub(crate) fn omegas(&self, n: usize) -> TPatList {
        let omega = self.omega_idx();
        self.push_list(std::iter::repeat_n(omega, n))
    }

    /// Row patterns as the sub-patterns of a new pattern.
    pub(crate) fn refs_list(&self, ps: &[&Pattern]) -> TPatList {
        let handles: Vec<TPatIdx> = ps.iter().map(|p| self.handle(p)).collect();
        self.push_list(handles)
    }

    /// The handle of a pattern that is either a reference or newly built.
    pub(crate) fn intern(&self, p: Cow<'_, Pattern>) -> TPatIdx {
        match p {
            Cow::Borrowed(p) => self.handle(p),
            Cow::Owned(p) => self.push(p),
        }
    }
}

/// OCaml `omega = make_pat Tpat_any Ctype.none Env.empty`: one shared value.
static OMEGA: std::sync::LazyLock<Pattern> = std::sync::LazyLock::new(|| {
    Pattern::new(
        PatternDesc::Tpat_any,
        LocIdx::none(),
        TypeExprRef(0),
        EnvRef(0),
    )
});

/// The wildcard pattern (`_`).
/// Equivalent to OCaml's `omega = make_pat Tpat_any Ctype.none Env.empty`.
fn omega() -> &'static Pattern {
    &OMEGA
}

/// An owned wildcard, for building sub-pattern lists of a new pattern.
fn omega_owned() -> Pattern {
    OMEGA.clone()
}

/// Create a list of n wildcard patterns.
/// Equivalent to OCaml's `omegas n`.
fn omegas(n: usize) -> Vec<&'static Pattern> {
    (0..n).map(|_| omega()).collect()
}

fn bump_raise_count(next_raise_count: &mut i32) -> i32 {
    *next_raise_count += 1;
    *next_raise_count
}

// ============================================================================
// Pattern helper functions — ported from parmatch.ml
// ============================================================================

/// Make a pattern with given desc, type, and env.
fn make_pat(desc: PatternDesc, ty: TypeExprRef, env: EnvRef) -> Pattern {
    Pattern::new(desc, LocIdx::none(), ty, env)
}

/// Compare two typed constants.
/// Equivalent to OCaml's `const_compare`.
fn const_compare(c1: &Constant, c2: &Constant) -> std::cmp::Ordering {
    use std::cmp::Ordering;
    fn normalize_bigint_digits(digits: &str) -> &str {
        let trimmed = digits.trim_start_matches('0');
        if trimmed.is_empty() { "0" } else { trimmed }
    }

    fn compare_bigint(positive1: bool, digits1: &str, positive2: bool, digits2: &str) -> Ordering {
        if positive1 != positive2 {
            return if positive1 {
                Ordering::Greater
            } else {
                Ordering::Less
            };
        }

        let digits1 = normalize_bigint_digits(digits1);
        let digits2 = normalize_bigint_digits(digits2);
        let abs_cmp = digits1
            .len()
            .cmp(&digits2.len())
            .then_with(|| digits1.cmp(digits2));
        if positive1 {
            abs_cmp
        } else {
            abs_cmp.reverse()
        }
    }

    match (c1, c2) {
        (Constant::Float(f1), Constant::Float(f2)) => {
            let v1: f64 = f1.parse().unwrap_or(0.0);
            let v2: f64 = f2.parse().unwrap_or(0.0);
            v1.partial_cmp(&v2).unwrap_or(Ordering::Equal)
        }
        (Constant::BigInt(s1, b1), Constant::BigInt(s2, b2)) => compare_bigint(*s1, b1, *s2, b2),
        (Constant::String(s1), Constant::String(s2)) => s1.cmp(s2),
        (Constant::Int(i1), Constant::Int(i2)) => i1.cmp(i2),
        (Constant::Char(c1), Constant::Char(c2)) => c1.cmp(c2),
        _ => {
            // Fall back to debug-based comparison for mixed types.
            let d1 = format!("{:?}", c1);
            let d2 = format!("{:?}", c2);
            d1.cmp(&d2)
        }
    }
}

fn same_constructor(c1: &ConstructorDescription, c2: &ConstructorDescription) -> bool {
    crate::types::same_constructor(c1, c2)
}

type RecordPatternField = (
    crate::parse_arena::Located<crate::parse_arena::LidentIdx>,
    std::sync::Arc<crate::types::LabelDescription>,
    TPatIdx,
    bool,
);

/// Record sub-patterns aligned for a comparison; small enough to stay inline.
type PatRefs<'p> = smallvec::SmallVec<[&'p Pattern; 8]>;

fn records_args_for_le_pats<'p>(
    pa: &PatArena<'p>,
    l1: &[RecordPatternField],
    l2: &[RecordPatternField],
    omega: &'p Pattern,
) -> (PatRefs<'p>, PatRefs<'p>) {
    let pat = |idx: &TPatIdx| pa.pat(*idx);
    let mut ps = PatRefs::new();
    let mut qs = PatRefs::new();
    let mut i = 0;
    let mut j = 0;

    // OCaml `Parmatch.records_args` aligns already-sorted record fields by
    // `lbl_pos`, filling absent fields with omega (compiler/ml/parmatch.ml:267-283).
    while i < l1.len() || j < l2.len() {
        match (l1.get(i), l2.get(j)) {
            (Some((_, lbl1, p1, _)), Some((_, lbl2, p2, _))) => {
                if lbl1.lbl_pos < lbl2.lbl_pos {
                    ps.push(pat(p1));
                    qs.push(omega);
                    i += 1;
                } else if lbl1.lbl_pos > lbl2.lbl_pos {
                    ps.push(omega);
                    qs.push(pat(p2));
                    j += 1;
                } else {
                    ps.push(pat(p1));
                    qs.push(pat(p2));
                    i += 1;
                    j += 1;
                }
            }
            (Some((_, _, p1, _)), None) => {
                ps.push(pat(p1));
                qs.push(omega);
                i += 1;
            }
            (None, Some((_, _, p2, _))) => {
                ps.push(omega);
                qs.push(pat(p2));
                j += 1;
            }
            (None, None) => break,
        }
    }

    (ps, qs)
}

/// Check if one pattern is less specific than another (le_pat p q means
/// everything matched by q is also matched by p).
/// Equivalent to OCaml's `le_pat`.
fn le_pat<'p>(pa: &PatArena<'p>, p: &Pattern, q: &Pattern) -> bool {
    match (&p.pat_desc, &q.pat_desc) {
        (PatternDesc::Tpat_var(..) | PatternDesc::Tpat_any, _) => true,
        (PatternDesc::Tpat_alias(p, _, _), _) => le_pat(pa, pa.pat(*p), q),
        (_, PatternDesc::Tpat_alias(q, _, _)) => le_pat(pa, p, pa.pat(*q)),
        // OCaml reaches or-pattern implication through the `satisfiable`
        // fallback in `Parmatch.le_pat` (compiler/ml/parmatch.ml:1772-1791).
        (PatternDesc::Tpat_or(_, _, _), PatternDesc::Tpat_or(q1, q2, _)) => {
            le_pat(pa, p, pa.pat(*q1)) && le_pat(pa, p, pa.pat(*q2))
        }
        (PatternDesc::Tpat_or(p1, p2, _), _) => {
            le_pat(pa, pa.pat(*p1), q) || le_pat(pa, pa.pat(*p2), q)
        }
        (_, PatternDesc::Tpat_or(q1, q2, _)) => {
            le_pat(pa, p, pa.pat(*q1)) && le_pat(pa, p, pa.pat(*q2))
        }
        (PatternDesc::Tpat_constant(c1), PatternDesc::Tpat_constant(c2)) => {
            const_compare(c1, c2) == std::cmp::Ordering::Equal
        }
        (
            PatternDesc::Tpat_constant(_) | PatternDesc::Tpat_interval(..),
            PatternDesc::Tpat_constant(_) | PatternDesc::Tpat_interval(..),
        ) => match (int_range(p), int_range(q)) {
            (Some((lo1, hi1)), Some((lo2, hi2))) => lo1 <= lo2 && hi2 <= hi1,
            _ => false,
        },
        (PatternDesc::Tpat_construct(_, c1, ps), PatternDesc::Tpat_construct(_, c2, qs)) => {
            same_constructor(c1, c2) && le_pat_lists(pa, *ps, *qs)
        }
        (
            PatternDesc::Tpat_variant(l1, Some(p1), _),
            PatternDesc::Tpat_variant(l2, Some(p2), _),
        ) => l1 == l2 && le_pat(pa, pa.pat(*p1), pa.pat(*p2)),
        (PatternDesc::Tpat_variant(l1, None, _), PatternDesc::Tpat_variant(l2, None, _)) => {
            l1 == l2
        }
        (PatternDesc::Tpat_variant(..), PatternDesc::Tpat_variant(..)) => false,
        (PatternDesc::Tpat_tuple(ps), PatternDesc::Tpat_tuple(qs)) => le_pat_lists(pa, *ps, *qs),
        (PatternDesc::Tpat_record(l1, _, _), PatternDesc::Tpat_record(l2, _, _)) => {
            let omega = omega();
            let (ps, qs) = records_args_for_le_pats(pa, l1, l2, omega);
            ps.iter().zip(&qs).all(|(p, q)| le_pat(pa, p, q))
        }
        (PatternDesc::Tpat_array(ps), PatternDesc::Tpat_array(qs)) => {
            ps.len() == qs.len() && le_pat_lists(pa, *ps, *qs)
        }
        // OCaml falls back to `not (satisfiable [[p]] [q])` here
        // (compiler/ml/parmatch.ml:1772-1791). Keep the remaining fallback
        // conservative until that enumeration path is ported.
        _ => false,
    }
}

/// [`le_pats`] over the sub-pattern lists of two patterns.
fn le_pat_lists(pa: &PatArena<'_>, ps: TPatList, qs: TPatList) -> bool {
    pa.pats(ps).zip(pa.pats(qs)).all(|(p, q)| le_pat(pa, p, q))
}

/// Check if patterns ps are pairwise le_pat to qs.
fn le_pats<A: Borrow<Pattern>, B: Borrow<Pattern>>(pa: &PatArena<'_>, ps: &[A], qs: &[B]) -> bool {
    ps.iter()
        .zip(qs)
        .all(|(p, q)| le_pat(pa, p.borrow(), q.borrow()))
}

/// Indices of the minimal elements of `ps` under a partial order `le`,
/// ascending. OCaml `select_rec` keeps `p` unless a later element is below
/// it and conses kept elements onto the accumulator, so each pass returns
/// the kept elements in reverse order and two passes restore input order.
fn get_mins_indices<T>(le: impl Fn(&T, &T) -> bool, ps: &[T]) -> MinIndices {
    fn select_rec<T>(le: &impl Fn(&T, &T) -> bool, ps: &[T], order: &[usize]) -> MinIndices {
        let mut kept: MinIndices = order
            .iter()
            .enumerate()
            .filter(|(i, p)| !order[i + 1..].iter().any(|p0| le(&ps[*p0], &ps[**p])))
            .map(|(_, p)| *p)
            .collect();
        kept.reverse();
        kept
    }
    let all: MinIndices = (0..ps.len()).collect();
    let first_pass = select_rec(&le, ps, &all);
    let kept = select_rec(&le, ps, &first_pass);
    debug_assert!(kept.windows(2).all(|w| w[0] < w[1]));
    kept
}

type MinIndices = smallvec::SmallVec<[usize; 16]>;

/// Get minimal elements under a partial order `le`, keeping the survivors
/// in place. Equivalent to OCaml's `get_mins`.
fn get_mins<T>(le: impl Fn(&T, &T) -> bool, mut ps: Vec<T>) -> Vec<T> {
    let kept = get_mins_indices(le, &ps);
    let mut next = kept.iter().copied().peekable();
    let mut index = 0;
    ps.retain(|_| {
        let keep = next.next_if_eq(&index).is_some();
        index += 1;
        keep
    });
    ps
}

/// Raised when patterns are incompatible in lub.
struct Empty;

/// Least upper bound of two patterns (the most specific pattern that
/// matches everything matched by either p or q).
/// Returns Err(Empty) when p and q are incompatible.
fn lub<'p>(pa: &'p PatArena<'p>, p: &'p Pattern, q: &'p Pattern) -> Result<&'p Pattern, Empty> {
    Ok(alloc_cow(pa, lub_cow(pa, p, q)?))
}

/// Store a pattern that is either one of the inputs or newly built.
fn alloc_cow<'p>(pa: &'p PatArena<'p>, p: Cow<'p, Pattern>) -> &'p Pattern {
    match p {
        Cow::Borrowed(p) => p,
        Cow::Owned(p) => pa.alloc(p),
    }
}

/// `lub` returning one of its inputs when the result is that input (OCaml
/// returns `p` or `q` physically), and a new pattern otherwise.
fn lub_cow<'p>(
    pa: &PatArena<'p>,
    p: &'p Pattern,
    q: &'p Pattern,
) -> Result<Cow<'p, Pattern>, Empty> {
    match (&p.pat_desc, &q.pat_desc) {
        (PatternDesc::Tpat_alias(p, _, _), _) => lub_cow(pa, pa.pat(*p), q),
        (_, PatternDesc::Tpat_alias(q, _, _)) => lub_cow(pa, p, pa.pat(*q)),
        (PatternDesc::Tpat_any | PatternDesc::Tpat_var(..), _) => Ok(Cow::Borrowed(q)),
        (_, PatternDesc::Tpat_any | PatternDesc::Tpat_var(..)) => Ok(Cow::Borrowed(p)),
        (PatternDesc::Tpat_or(p1, p2, _), _) => orlub(pa, pa.pat(*p1), pa.pat(*p2), q),
        (_, PatternDesc::Tpat_or(q1, q2, _)) => orlub(pa, pa.pat(*q1), pa.pat(*q2), p),
        (PatternDesc::Tpat_constant(c1), PatternDesc::Tpat_constant(c2))
            if const_compare(c1, c2) == std::cmp::Ordering::Equal =>
        {
            Ok(Cow::Borrowed(p))
        }
        (
            PatternDesc::Tpat_constant(_) | PatternDesc::Tpat_interval(..),
            PatternDesc::Tpat_constant(_) | PatternDesc::Tpat_interval(..),
        ) => match (int_range(p), int_range(q)) {
            (Some((lo1, hi1)), Some((lo2, hi2))) if lo1.max(lo2) <= hi1.min(hi2) => {
                Ok(Cow::Owned(make_int_range(p, lo1.max(lo2), hi1.min(hi2))))
            }
            _ => Err(Empty),
        },
        (PatternDesc::Tpat_tuple(ps), PatternDesc::Tpat_tuple(qs)) => {
            let rs = lubs_owned(pa, pa.list(*ps), pa.list(*qs))?;
            Ok(Cow::Owned(make_pat(
                PatternDesc::Tpat_tuple(pa.push_list(rs)),
                p.pat_type,
                p.pat_env,
            )))
        }
        (PatternDesc::Tpat_construct(lid, c1, ps1), PatternDesc::Tpat_construct(_, c2, ps2))
            if same_constructor(c1, c2) =>
        {
            let rs = lubs_owned(pa, pa.list(*ps1), pa.list(*ps2))?;
            Ok(Cow::Owned(make_pat(
                PatternDesc::Tpat_construct(*lid, c1.clone(), pa.push_list(rs)),
                p.pat_type,
                p.pat_env,
            )))
        }
        (
            PatternDesc::Tpat_variant(l1, Some(p1), row),
            PatternDesc::Tpat_variant(l2, Some(p2), _),
        ) if l1 == l2 => {
            let r = pa.intern(lub_cow(pa, pa.pat(*p1), pa.pat(*p2))?);
            Ok(Cow::Owned(make_pat(
                PatternDesc::Tpat_variant(l1.clone(), Some(r), *row),
                p.pat_type,
                p.pat_env,
            )))
        }
        (PatternDesc::Tpat_variant(l1, None, _), PatternDesc::Tpat_variant(l2, None, _))
            if l1 == l2 =>
        {
            Ok(Cow::Borrowed(p))
        }
        (PatternDesc::Tpat_record(l1, closed, _), PatternDesc::Tpat_record(l2, _, _)) => {
            let rs = record_lubs(pa, l1, l2)?;
            Ok(Cow::Owned(make_pat(
                PatternDesc::Tpat_record(rs, *closed, None),
                p.pat_type,
                p.pat_env,
            )))
        }
        (PatternDesc::Tpat_array(ps), PatternDesc::Tpat_array(qs)) if ps.len() == qs.len() => {
            let rs = lubs_owned(pa, pa.list(*ps), pa.list(*qs))?;
            Ok(Cow::Owned(make_pat(
                PatternDesc::Tpat_array(pa.push_list(rs)),
                p.pat_type,
                p.pat_env,
            )))
        }
        _ => Err(Empty),
    }
}

/// `q` with a new descriptor (OCaml `{q with pat_desc = ...}`).
fn with_desc(q: &Pattern, pat_desc: PatternDesc) -> Pattern {
    Pattern {
        pat_desc,
        pat_loc: q.pat_loc,
        pat_cold: q.pat_cold,
        pat_type: q.pat_type,
        pat_env: q.pat_env,
    }
}

fn orlub<'p>(
    pa: &PatArena<'p>,
    p1: &'p Pattern,
    p2: &'p Pattern,
    q: &'p Pattern,
) -> Result<Cow<'p, Pattern>, Empty> {
    match lub_cow(pa, p1, q) {
        Ok(r1) => match lub_cow(pa, p2, q) {
            Ok(r2) => Ok(Cow::Owned(with_desc(
                q,
                PatternDesc::Tpat_or(pa.intern(r1), pa.intern(r2), None),
            ))),
            Err(Empty) => Ok(r1),
        },
        Err(Empty) => lub_cow(pa, p2, q),
    }
}

/// Record field lub.
fn record_lubs<'p>(
    pa: &PatArena<'p>,
    l1: &[RecordPatternField],
    l2: &[RecordPatternField],
) -> Result<Vec<RecordPatternField>, Empty> {
    let mut out = Vec::with_capacity(l1.len().max(l2.len()));
    let (mut i, mut j) = (0, 0);
    loop {
        match (l1.get(i), l2.get(j)) {
            (None, _) => {
                out.extend_from_slice(&l2[j..]);
                return Ok(out);
            }
            (_, None) => {
                out.extend_from_slice(&l1[i..]);
                return Ok(out);
            }
            (Some((lid1, lbl1, p1, o1)), Some((lid2, lbl2, p2, o2))) => {
                if lbl1.lbl_pos < lbl2.lbl_pos {
                    out.push((*lid1, lbl1.clone(), *p1, *o1));
                    i += 1;
                } else if lbl2.lbl_pos < lbl1.lbl_pos {
                    out.push((*lid2, lbl2.clone(), *p2, *o2));
                    j += 1;
                } else {
                    if o1 != o2 {
                        return Err(Empty);
                    }
                    let p = pa.intern(lub_cow(pa, pa.pat(*p1), pa.pat(*p2))?);
                    out.push((*lid1, lbl1.clone(), p, *o1));
                    i += 1;
                    j += 1;
                }
            }
        }
    }
}

/// `lubs` over sub-patterns of new patterns.
fn lubs_owned(pa: &PatArena<'_>, ps: &[TPatIdx], qs: &[TPatIdx]) -> Result<Vec<TPatIdx>, Empty> {
    ps.iter()
        .zip(qs)
        .map(|(p, q)| lub_cow(pa, pa.pat(*p), pa.pat(*q)).map(|r| pa.intern(r)))
        .collect()
}

/// `lubs` over borrowed rows.
fn lubs<'p>(
    pa: &'p PatArena<'p>,
    ps: &[&'p Pattern],
    qs: &[&'p Pattern],
) -> Result<Vec<&'p Pattern>, Empty> {
    ps.iter().zip(qs).map(|(p, q)| lub(pa, p, q)).collect()
}

/// Normalize a pattern: replace all sub-pattern arguments with omega.
/// Equivalent to OCaml's `normalize_pat`.
fn normalize_pat<'p>(pa: &'p PatArena<'p>, q: &'p Pattern) -> &'p Pattern {
    match &q.pat_desc {
        PatternDesc::Tpat_any | PatternDesc::Tpat_constant(_) | PatternDesc::Tpat_interval(..) => q,
        PatternDesc::Tpat_alias(p, _, _) => normalize_pat(pa, pa.pat(*p)),
        _ => pa.alloc(normalize_pat_owned(pa, q)),
    }
}

fn normalize_pat_owned(pa: &PatArena<'_>, q: &Pattern) -> Pattern {
    match &q.pat_desc {
        PatternDesc::Tpat_any | PatternDesc::Tpat_constant(_) | PatternDesc::Tpat_interval(..) => {
            q.clone()
        }
        PatternDesc::Tpat_var(..) => make_pat(PatternDesc::Tpat_any, q.pat_type, q.pat_env),
        PatternDesc::Tpat_alias(p, _, _) => normalize_pat_owned(pa, pa.pat(*p)),
        PatternDesc::Tpat_tuple(args) => make_pat(
            PatternDesc::Tpat_tuple(pa.omegas(args.len())),
            q.pat_type,
            q.pat_env,
        ),
        PatternDesc::Tpat_construct(lid, c, args) => make_pat(
            PatternDesc::Tpat_construct(*lid, c.clone(), pa.omegas(args.len())),
            q.pat_type,
            q.pat_env,
        ),
        PatternDesc::Tpat_variant(l, arg, row) => make_pat(
            PatternDesc::Tpat_variant(l.clone(), arg.map(|_| pa.omega_idx()), *row),
            q.pat_type,
            q.pat_env,
        ),
        PatternDesc::Tpat_array(args) => make_pat(
            PatternDesc::Tpat_array(pa.omegas(args.len())),
            q.pat_type,
            q.pat_env,
        ),
        PatternDesc::Tpat_record(largs, closed, _) => make_pat(
            PatternDesc::Tpat_record(
                largs
                    .iter()
                    .map(|(lid, lbl, _, opt)| (*lid, lbl.clone(), pa.omega_idx(), *opt))
                    .collect(),
                *closed,
                None,
            ),
            q.pat_type,
            q.pat_env,
        ),
        PatternDesc::Tpat_or(..) => crate::misc::fatal_error("Parmatch.normalize_pat"),
        PatternDesc::Tpat_dict(_) => {
            crate::misc::fatal_error("Parmatch.normalize_pat: dict pattern")
        }
    }
}

/// Read n arguments from `r`, returning (args, rest).
fn read_args<'r, 'p>(n: usize, r: &'r [&'p Pattern]) -> (&'r [&'p Pattern], &'r [&'p Pattern]) {
    assert!(r.len() >= n, "Parmatch.read_args: not enough arguments");
    r.split_at(n)
}

/// Set the arguments of a normalized pattern, optionally erasing mutable fields.
/// Equivalent to OCaml's `do_set_args`.
fn do_set_args<'p>(
    pa: &'p PatArena<'p>,
    erase_mutable: bool,
    q: &'p Pattern,
    r: &[&'p Pattern],
) -> Vec<&'p Pattern> {
    let (head, rest): (Pattern, &[&'p Pattern]) = match &q.pat_desc {
        PatternDesc::Tpat_tuple(pats) => {
            let (args, rest) = read_args(pats.len(), r);
            (
                make_pat(
                    PatternDesc::Tpat_tuple(pa.refs_list(args)),
                    q.pat_type,
                    q.pat_env,
                ),
                rest,
            )
        }
        PatternDesc::Tpat_record(fields, closed, _) => {
            let (args, rest) = read_args(fields.len(), r);
            let new_fields: Vec<_> = fields
                .iter()
                .zip(args.iter())
                .map(|((lid, lbl, _, opt), arg)| {
                    if erase_mutable && matches!(lbl.lbl_mut, MutableFlag::Mutable) {
                        (*lid, lbl.clone(), pa.omega_idx(), *opt)
                    } else {
                        (*lid, lbl.clone(), pa.handle(arg), *opt)
                    }
                })
                .collect();
            (
                make_pat(
                    PatternDesc::Tpat_record(new_fields, *closed, None),
                    q.pat_type,
                    q.pat_env,
                ),
                rest,
            )
        }
        PatternDesc::Tpat_construct(lid, c, pats) => {
            let (args, rest) = read_args(pats.len(), r);
            (
                make_pat(
                    PatternDesc::Tpat_construct(*lid, c.clone(), pa.refs_list(args)),
                    q.pat_type,
                    q.pat_env,
                ),
                rest,
            )
        }
        PatternDesc::Tpat_variant(l, opt_omega, row) => {
            let (arg, rest) = match (opt_omega, r) {
                (Some(_), [a, rest @ ..]) => (Some(pa.handle(a)), rest),
                (None, _) => (None, r),
                _ => panic!("Parmatch.set_args: variant"),
            };
            (
                make_pat(
                    PatternDesc::Tpat_variant(l.clone(), arg, *row),
                    q.pat_type,
                    q.pat_env,
                ),
                rest,
            )
        }
        PatternDesc::Tpat_array(pats) => {
            let (args, rest) = read_args(pats.len(), r);
            (
                make_pat(
                    PatternDesc::Tpat_array(pa.refs_list(args)),
                    q.pat_type,
                    q.pat_env,
                ),
                rest,
            )
        }
        PatternDesc::Tpat_constant(_) | PatternDesc::Tpat_interval(..) | PatternDesc::Tpat_any => {
            let mut result = Vec::with_capacity(r.len() + 1);
            result.push(q);
            result.extend_from_slice(r);
            return result;
        }
        _ => crate::misc::fatal_error("Parmatch.set_args"),
    };
    let mut result = Vec::with_capacity(rest.len() + 1);
    result.push(pa.alloc(head));
    result.extend_from_slice(rest);
    result
}

/// `set_args_erase_mutable q r` — like set_args but replaces mutable fields with omega.
fn set_args_erase_mutable<'p>(
    pa: &'p PatArena<'p>,
    q: &'p Pattern,
    r: &[&'p Pattern],
) -> Vec<&'p Pattern> {
    do_set_args(pa, true, q, r)
}

/// The complete label array of a record pattern: `lbl_all` of its first
/// label (compiler/ml/matching.ml:218-224, 540-563); see `all_record_args`.
fn record_all_labels(
    ctx_ref: Option<&TypeContext>,
    lbls: &[RecordPatternField],
) -> Option<Vec<LabelDescription>> {
    let first_lbl = &lbls[0].1;
    ctx_ref.map(|ctx| pattern_label_family(ctx, first_lbl))
}

/// `lbl.lbl_all`: every pattern label carries the array its record's labels
/// were described with.
fn pattern_label_family(ctx: &TypeContext, lbl: &LabelDescription) -> Vec<LabelDescription> {
    ctx.label_all(lbl.lbl_all).unwrap_or_else(|| {
        panic!(
            "record pattern label `{}` carries no lbl_all array ({:?})",
            lbl.lbl_name, lbl.lbl_all
        )
    })
}

fn all_record_args(
    pa: &PatArena<'_>,
    ctx_ref: Option<&TypeContext>,
    lbls: &[RecordPatternField],
) -> Vec<RecordPatternField> {
    if lbls.is_empty() {
        return Vec::new();
    }
    let first_opt = lbls[0].3;
    match record_all_labels(ctx_ref, lbls) {
        Some(all_labels) => {
            // Build a full array with omega for missing fields
            let dummy_loc = crate::parse_arena::Located {
                txt: crate::parse_arena::LidentIdx(0),
                loc: LocIdx::none(),
            };
            let mut result: Vec<_> = all_labels
                .iter()
                .map(|lbl| {
                    (
                        dummy_loc,
                        std::sync::Arc::new(lbl.clone()),
                        pa.omega_idx(),
                        first_opt,
                    )
                })
                .collect();
            // Fill in the actual patterns from the provided fields
            for (id, lbl, pat, opt) in lbls {
                if (lbl.lbl_pos as usize) < result.len() {
                    result[lbl.lbl_pos as usize] = (*id, lbl.clone(), *pat, *opt);
                }
            }
            result
        }
        None => {
            // Fallback: return fields as-is (old behavior)
            lbls.to_vec()
        }
    }
}

/// The field patterns `all_record_args` would produce, borrowed: the columns
/// a record head expands to.
fn all_record_arg_pats<'p>(
    pa: &PatArena<'p>,
    ctx_ref: Option<&TypeContext>,
    lbls: &'p [RecordPatternField],
) -> Vec<&'p Pattern> {
    if lbls.is_empty() {
        return Vec::new();
    }
    match record_all_labels(ctx_ref, lbls) {
        Some(all_labels) => {
            let mut result: Vec<&'p Pattern> = vec![omega(); all_labels.len()];
            for (_, lbl, pat, _) in lbls {
                if (lbl.lbl_pos as usize) < result.len() {
                    result[lbl.lbl_pos as usize] = pa.pat(*pat);
                }
            }
            result
        }
        None => lbls.iter().map(|(_, _, p, _)| pa.pat(*p)).collect(),
    }
}

/// Check if two constructors may be equal (considering extension types).
fn may_equal_constr(
    c1: &crate::types::ConstructorDescription,
    c2: &crate::types::ConstructorDescription,
) -> bool {
    crate::types::may_equal_constructor(c1, c2)
}

/// Compatibility predicate: may_compat p q returns false when p and q
/// never admit a common instance.
fn may_compat(pa: &PatArena<'_>, p: &Pattern, q: &Pattern) -> bool {
    match (&p.pat_desc, &q.pat_desc) {
        (PatternDesc::Tpat_any | PatternDesc::Tpat_var(..), _)
        | (_, PatternDesc::Tpat_any | PatternDesc::Tpat_var(..)) => true,
        (PatternDesc::Tpat_alias(p, _, _), _) => may_compat(pa, pa.pat(*p), q),
        (_, PatternDesc::Tpat_alias(q, _, _)) => may_compat(pa, p, pa.pat(*q)),
        (PatternDesc::Tpat_or(p1, p2, _), _) => {
            may_compat(pa, pa.pat(*p1), q) || may_compat(pa, pa.pat(*p2), q)
        }
        (_, PatternDesc::Tpat_or(q1, q2, _)) => {
            may_compat(pa, p, pa.pat(*q1)) || may_compat(pa, p, pa.pat(*q2))
        }
        (PatternDesc::Tpat_construct(_, c1, ps1), PatternDesc::Tpat_construct(_, c2, ps2)) => {
            may_equal_constr(c1, c2) && may_compat_lists(pa, *ps1, *ps2)
        }
        (PatternDesc::Tpat_constant(c1), PatternDesc::Tpat_constant(c2)) => {
            const_compare(c1, c2) == std::cmp::Ordering::Equal
        }
        (
            PatternDesc::Tpat_constant(_) | PatternDesc::Tpat_interval(..),
            PatternDesc::Tpat_constant(_) | PatternDesc::Tpat_interval(..),
        ) => match (int_range(p), int_range(q)) {
            (Some((lo1, hi1)), Some((lo2, hi2))) => lo1 <= hi2 && lo2 <= hi1,
            _ => false,
        },
        (PatternDesc::Tpat_variant(l1, op1, _), PatternDesc::Tpat_variant(l2, op2, _)) => {
            l1 == l2
                && match (op1, op2) {
                    (Some(p1), Some(p2)) => may_compat(pa, pa.pat(*p1), pa.pat(*p2)),
                    (None, None) => true,
                    _ => false,
                }
        }
        (PatternDesc::Tpat_tuple(ps), PatternDesc::Tpat_tuple(qs)) => {
            may_compat_lists(pa, *ps, *qs)
        }
        (PatternDesc::Tpat_array(ps), PatternDesc::Tpat_array(qs)) => {
            ps.len() == qs.len() && may_compat_lists(pa, *ps, *qs)
        }
        (PatternDesc::Tpat_record(l1, _, _), PatternDesc::Tpat_record(l2, _, _)) => {
            // Check compatible fields only
            may_compats_record(pa, l1, l2)
        }
        // OCaml's Parmatch.Compat.compat rejects cross-shape pairs here.
        _ => false,
    }
}

/// [`may_compats`] over the sub-pattern lists of two patterns.
fn may_compat_lists(pa: &PatArena<'_>, ps: TPatList, qs: TPatList) -> bool {
    pa.pats(ps)
        .zip(pa.pats(qs))
        .all(|(p, q)| may_compat(pa, p, q))
}

fn may_compats<A: Borrow<Pattern>, B: Borrow<Pattern>>(
    pa: &PatArena<'_>,
    ps: &[A],
    qs: &[B],
) -> bool {
    ps.iter()
        .zip(qs.iter())
        .all(|(p, q)| may_compat(pa, p.borrow(), q.borrow()))
}

fn may_compats_record(
    pa: &PatArena<'_>,
    l1: &[(
        crate::parse_arena::Located<crate::parse_arena::LidentIdx>,
        std::sync::Arc<crate::types::LabelDescription>,
        TPatIdx,
        bool,
    )],
    l2: &[(
        crate::parse_arena::Located<crate::parse_arena::LidentIdx>,
        std::sync::Arc<crate::types::LabelDescription>,
        TPatIdx,
        bool,
    )],
) -> bool {
    // For each field present in both, check compatibility
    for (_, lbl1, p1, _) in l1 {
        for (_, lbl2, p2, _) in l2 {
            if lbl1.lbl_pos == lbl2.lbl_pos && !may_compat(pa, pa.pat(*p1), pa.pat(*p2)) {
                return false;
            }
        }
    }
    true
}

// ============================================================================
// Matrix type — pattern list list
// ============================================================================

/// A pattern matrix: each row is a list of patterns.
pub type Matrix<'p> = Vec<Vec<&'p Pattern>>;

/// Prepend an omega (wildcard) column to each row of a matrix.
pub fn add_omega_column<'p>(pss: &Matrix<'p>) -> Matrix<'p> {
    pss.iter()
        .map(|ps| {
            let mut row = vec![omega()];
            row.extend(ps.iter().cloned());
            row
        })
        .collect()
}

// ============================================================================
// Context type
// ============================================================================

/// A context: a pair of pattern lists (left, right) where columns are
/// partitioned into left and right parts.
#[derive(Debug, Clone)]
pub struct Ctx<'p> {
    /// Patterns of the left columns.
    pub left: Vec<&'p Pattern>,
    /// Patterns of the right columns.
    pub right: Vec<&'p Pattern>,
}

/// Check if context c1 is less-or-equal to c2.
pub fn le_ctx<'p>(pa: &PatArena<'p>, c1: &Ctx<'_>, c2: &Ctx<'_>) -> bool {
    le_pats(pa, &c1.left, &c2.left) && le_pats(pa, &c1.right, &c2.right)
}

/// Shift the first element of `right` to the front of `left`.
pub fn lshift<'p>(ctx: &Ctx<'p>) -> Ctx<'p> {
    match ctx.right.split_first() {
        Some((x, xs)) => Ctx {
            left: {
                let mut l = vec![*x];
                l.extend(ctx.left.iter().cloned());
                l
            },
            right: xs.to_vec(),
        },
        None => panic!("lshift: empty right"),
    }
}

/// Shift an omega to the front of `left`, dropping the first element of `right`.
pub fn lforget<'p>(ctx: &Ctx<'p>) -> Ctx<'p> {
    match ctx.right.split_first() {
        Some((_, xs)) => Ctx {
            left: {
                let mut l = vec![omega()];
                l.extend(ctx.left.iter().cloned());
                l
            },
            right: xs.to_vec(),
        },
        None => panic!("lforget: empty right"),
    }
}

/// Check if a slice is small enough (length <= n).
fn small_enough(n: usize, slice: &[Ctx<'_>]) -> bool {
    slice.len() <= n
}

/// Shift left for a list of contexts, with pruning when too large.
pub fn ctx_lshift<'p>(pa: &PatArena<'p>, ctx: &[Ctx<'p>]) -> Vec<Ctx<'p>> {
    if small_enough(31, ctx) {
        ctx.iter().map(lshift).collect()
    } else {
        // Context pruning
        let forgotten: Vec<Ctx<'_>> = ctx.iter().map(lforget).collect();
        get_mins(|c1, c2| le_ctx(pa, c1, c2), forgotten)
    }
}

/// Shift the first element of `left` to the front of `right`.
pub fn rshift<'p>(ctx: &Ctx<'p>) -> Ctx<'p> {
    match ctx.left.split_first() {
        Some((p, ps)) => Ctx {
            left: ps.to_vec(),
            right: {
                let mut r = vec![*p];
                r.extend(ctx.right.iter().cloned());
                r
            },
        },
        None => panic!("rshift: empty left"),
    }
}

/// Right-shift all contexts.
pub fn ctx_rshift<'p>(ctx: &[Ctx<'p>]) -> Vec<Ctx<'p>> {
    ctx.iter().map(rshift).collect()
}

/// Forget what the contexts know about the first column
/// (`ctx_erase_first_col`, matching.ml:106-113).
fn ctx_erase_first_col<'p>(ctx: Vec<Ctx<'p>>) -> Vec<Ctx<'p>> {
    ctx.into_iter()
        .map(|Ctx { left, mut right }| {
            match right.first_mut() {
                Some(first) => *first = omega(),
                None => panic!("Matching.ctx_erase_first_col"),
            }
            Ctx { left, right }
        })
        .collect()
}

/// Split off the first n elements from a pattern list.
/// Returns (first_n, rest).
fn nchars<'p>(n: usize, ps: &[&'p Pattern]) -> (Vec<&'p Pattern>, Vec<&'p Pattern>) {
    if n == 0 {
        return (Vec::new(), ps.to_vec());
    }
    match ps.split_first() {
        Some((p, rem)) => {
            let (mut chars, cdrs) = nchars(n - 1, rem);
            chars.insert(0, *p);
            (chars, cdrs)
        }
        None => panic!("nchars: not enough patterns"),
    }
}

/// Right-shift n elements from left to right.
pub fn rshift_num<'p>(n: usize, ctx: &Ctx<'p>) -> Ctx<'p> {
    let (shifted, left) = nchars(n, &ctx.left);
    let mut right = shifted;
    right.extend(ctx.right.iter().cloned());
    Ctx { left, right }
}

/// Right-shift n elements for all contexts.
pub fn ctx_rshift_num<'p>(n: usize, ctx: &[Ctx<'p>]) -> Vec<Ctx<'p>> {
    ctx.iter().map(|c| rshift_num(n, c)).collect()
}

/// Recombination of contexts: take the first element from left,
/// and set its arguments from right, erasing mutable fields.
/// e.g. `(_,_)::p1::p2::rem -> (p1,p2)::rem`
pub fn combine<'p>(pa: &'p PatArena<'p>, ctx: &Ctx<'p>) -> Ctx<'p> {
    match ctx.left.split_first() {
        Some((p, ps)) => {
            let result = set_args_erase_mutable(pa, p, &ctx.right);
            // The first element of result is the combined pattern;
            // the rest is the remaining right.
            Ctx {
                left: ps.to_vec(),
                right: result,
            }
        }
        None => panic!("combine: empty left"),
    }
}

/// Combine all contexts.
pub fn ctx_combine<'p>(pa: &'p PatArena<'p>, ctx: &[Ctx<'p>]) -> Vec<Ctx<'p>> {
    ctx.iter().map(|c| combine(pa, c)).collect()
}

/// Number of columns in a matrix (length of first row, or 0 if empty).
pub fn ncols<'p>(pss: &Matrix<'p>) -> usize {
    match pss.first() {
        Some(ps) => ps.len(),
        None => 0,
    }
}

// ============================================================================
// NoMatch / OrPat exceptions (represented as Result/enum in Rust)
// ============================================================================

/// Matcher used by `filter_matrix` and `make_default`: given a row's head
/// pattern and the rest of the row, the row's replacement.
type RowMatcher<'p, 'a> =
    dyn Fn(&'p Pattern, &[&'p Pattern]) -> Result<Vec<&'p Pattern>, MatchError> + 'a;

/// Errors that can occur during pattern matching filtering.
enum MatchError {
    /// Pattern doesn't match.
    NoMatch,
    /// Pattern is an or-pattern that needs expansion.
    OrPat,
}

// ============================================================================
// filter_matrix — filter a matrix according to a matcher function
// ============================================================================

/// Filter a pattern matrix using a matcher function.
/// The matcher takes a pattern and the rest of the row, and returns
/// the filtered row or an error.
///
/// Equivalent to OCaml's `filter_matrix`. OCaml re-conses `p::ps` onto the
/// remaining rows when it peels an alias, a variable or an or-pattern; each
/// row's results come before the remaining rows' results, so filtering one
/// row at a time gives the same matrix.
fn filter_matrix<'p>(
    pa: &PatArena<'p>,
    matcher: &RowMatcher<'p, '_>,
    pss: &Matrix<'p>,
) -> Matrix<'p> {
    fn filter_row<'p>(
        pa: &PatArena<'p>,
        matcher: &RowMatcher<'p, '_>,
        p: &'p Pattern,
        ps: &[&'p Pattern],
        out: &mut Matrix<'p>,
    ) {
        match &p.pat_desc {
            PatternDesc::Tpat_alias(p_inner, _, _) => {
                filter_row(pa, matcher, pa.pat(*p_inner), ps, out)
            }
            PatternDesc::Tpat_var(..) => filter_row(pa, matcher, omega(), ps, out),
            _ => match matcher(p, ps) {
                Ok(filtered_row) => out.push(filtered_row),
                Err(MatchError::NoMatch) => {}
                Err(MatchError::OrPat) => match &p.pat_desc {
                    PatternDesc::Tpat_or(p1, p2, _) => {
                        filter_row(pa, matcher, pa.pat(*p1), ps, out);
                        filter_row(pa, matcher, pa.pat(*p2), ps, out);
                    }
                    _ => panic!("filter_matrix: OrPat on non-or pattern"),
                },
            },
        }
    }
    let mut out = Vec::new();
    for row in pss {
        match row.split_first() {
            Some((p, ps)) => filter_row(pa, matcher, p, ps, &mut out),
            // Empty rows shouldn't appear here — fatal error in OCaml.
            None => crate::misc::fatal_error("Matching.filter_matrix"),
        }
    }
    out
}

// ============================================================================
// make_default — build default environment by filtering
// ============================================================================

/// Default environment entry: (matrix, exit_number).
pub type DefaultEnv<'p> = Vec<(Matrix<'p>, i32)>;

/// Build default environment by filtering each matrix with the given matcher.
/// Equivalent to OCaml's `make_default`.
fn make_default<'p>(
    pa: &PatArena<'p>,
    matcher: &RowMatcher<'p, '_>,
    env: &DefaultEnv<'p>,
) -> DefaultEnv<'p> {
    fn make_rec<'p>(
        pa: &PatArena<'p>,
        matcher: &RowMatcher<'p, '_>,
        env: &[(Matrix<'p>, i32)],
    ) -> DefaultEnv<'p> {
        match env.split_first() {
            None => Vec::new(),
            Some(((pss, i), rem)) => {
                // Check for terminal: [[]] case
                if pss.len() == 1 && pss[0].is_empty() {
                    return vec![(vec![Vec::new()], *i)];
                }
                let rest = make_rec(pa, matcher, rem);
                let filtered = filter_matrix(pa, matcher, pss);
                if filtered.is_empty() {
                    rest
                } else if !filtered.is_empty() && filtered.iter().any(|row| row.is_empty()) {
                    let mut result = vec![(vec![Vec::new()], *i)];
                    result.extend(rest);
                    result
                } else {
                    let mut result = vec![(filtered, *i)];
                    result.extend(rest);
                    result
                }
            }
        }
    }
    make_rec(pa, matcher, env)
}

// ============================================================================
// ctx_matcher — build a context matcher from a pattern
// ============================================================================

/// Matcher built by `ctx_matcher`: given a context column head `q` and the
/// rest of the column list, the normalized pattern to move left and the
/// expanded right list.
type CtxMatcher<'p, 'a> = Box<CtxMatcherFn<'p, 'a>>;

/// The function behind a [`CtxMatcher`].
type CtxMatcherFn<'p, 'a> =
    dyn Fn(&'p Pattern, &[&'p Pattern]) -> Result<(&'p Pattern, Vec<&'p Pattern>), MatchError> + 'a;

/// `args @ rem` as a fresh row.
fn prepend_row<'p>(
    args: impl IntoIterator<Item = &'p Pattern>,
    rem: &[&'p Pattern],
) -> Vec<&'p Pattern> {
    let mut row: Vec<&'p Pattern> = args.into_iter().collect();
    row.extend_from_slice(rem);
    row
}

/// Build a matcher function from a pattern, for use with filter_ctx.
/// Returns a closure that, given a pattern q and remaining patterns,
/// returns (to_left_pattern, expanded_right) or Err(NoMatch).
///
/// Equivalent to OCaml's `ctx_matcher`.
fn ctx_matcher<'p, 'a>(
    ctx_ref: Option<&'a TypeContext>,
    pa: &'p PatArena<'p>,
    p: &'p Pattern,
) -> CtxMatcher<'p, 'a>
where
    'p: 'a,
{
    let p = normalize_pat(pa, p);
    match &p.pat_desc {
        PatternDesc::Tpat_construct(_, cstr, pats) => Box::new(
            move |q: &'p Pattern, rem: &[&'p Pattern]| match &q.pat_desc {
                PatternDesc::Tpat_construct(_, cstr2, args) if may_equal_constr(cstr, cstr2) => {
                    Ok((p, prepend_row(pa.pats(*args), rem)))
                }
                PatternDesc::Tpat_any => Ok((p, prepend_row(pa.pats(*pats), rem))),
                _ => Err(MatchError::NoMatch),
            },
        ),
        // `p` is a piece of a split column; values matched by a context
        // range that overlaps it may reach it.
        PatternDesc::Tpat_constant(_) | PatternDesc::Tpat_interval(..)
            if int_range(p).is_some() =>
        {
            Box::new(
                move |q: &'p Pattern, rem: &[&'p Pattern]| match &q.pat_desc {
                    PatternDesc::Tpat_constant(_) | PatternDesc::Tpat_interval(..)
                        if may_compat(pa, p, q) =>
                    {
                        Ok((p, rem.to_vec()))
                    }
                    PatternDesc::Tpat_any => Ok((p, rem.to_vec())),
                    _ => Err(MatchError::NoMatch),
                },
            )
        }
        PatternDesc::Tpat_constant(cst) => {
            Box::new(
                move |q: &'p Pattern, rem: &[&'p Pattern]| match &q.pat_desc {
                    PatternDesc::Tpat_constant(cst2)
                        if const_compare(cst, cst2) == std::cmp::Ordering::Equal =>
                    {
                        Ok((p, rem.to_vec()))
                    }
                    PatternDesc::Tpat_any => Ok((p, rem.to_vec())),
                    _ => Err(MatchError::NoMatch),
                },
            )
        }
        PatternDesc::Tpat_variant(lab, Some(omega_pat), _) => Box::new(
            move |q: &'p Pattern, rem: &[&'p Pattern]| match &q.pat_desc {
                PatternDesc::Tpat_variant(lab2, Some(arg), _) if lab == lab2 => {
                    Ok((p, prepend_row([pa.pat(*arg)], rem)))
                }
                PatternDesc::Tpat_any => Ok((p, prepend_row([pa.pat(*omega_pat)], rem))),
                _ => Err(MatchError::NoMatch),
            },
        ),
        PatternDesc::Tpat_variant(lab, None, _) => Box::new(
            move |q: &'p Pattern, rem: &[&'p Pattern]| match &q.pat_desc {
                PatternDesc::Tpat_variant(lab2, None, _) if lab == lab2 => Ok((p, rem.to_vec())),
                PatternDesc::Tpat_any => Ok((p, rem.to_vec())),
                _ => Err(MatchError::NoMatch),
            },
        ),
        PatternDesc::Tpat_array(pats) => {
            let len = pats.len();
            Box::new(
                move |q: &'p Pattern, rem: &[&'p Pattern]| match &q.pat_desc {
                    PatternDesc::Tpat_array(args) if args.len() == len => {
                        Ok((p, prepend_row(pa.pats(*args), rem)))
                    }
                    PatternDesc::Tpat_any => Ok((p, prepend_row(pa.pats(*pats), rem))),
                    _ => Err(MatchError::NoMatch),
                },
            )
        }
        PatternDesc::Tpat_tuple(pats) => {
            let len = pats.len();
            Box::new(
                move |q: &'p Pattern, rem: &[&'p Pattern]| match &q.pat_desc {
                    PatternDesc::Tpat_tuple(args) if args.len() == len => {
                        Ok((p, prepend_row(pa.pats(*args), rem)))
                    }
                    PatternDesc::Tpat_any => Ok((p, prepend_row(pa.pats(*pats), rem))),
                    _ => Err(MatchError::NoMatch),
                },
            )
        }
        PatternDesc::Tpat_record(fields, _, _) if !fields.is_empty() => Box::new(
            move |q: &'p Pattern, rem: &[&'p Pattern]| match &q.pat_desc {
                PatternDesc::Tpat_record(fields2, _, _) if !fields2.is_empty() => {
                    let expanded = all_record_arg_pats(pa, ctx_ref, fields2);
                    Ok((p, prepend_row(expanded, rem)))
                }
                PatternDesc::Tpat_any => Ok((
                    p,
                    prepend_row(fields.iter().map(|(_, _, f, _)| pa.pat(*f)), rem),
                )),
                _ => Err(MatchError::NoMatch),
            },
        ),
        _ => crate::misc::fatal_error("Matching.ctx_matcher"),
    }
}

// ============================================================================
// filter_ctx — filter a context list using a ctx_matcher
// ============================================================================

/// Filter contexts using a matcher built from pattern q.
/// Equivalent to OCaml's `filter_ctx`; as in `filter_matrix`, each context's
/// results precede the remaining contexts' results.
pub fn filter_ctx<'p>(
    ctx_ref: Option<&TypeContext>,
    pa: &'p PatArena<'p>,
    q: &'p Pattern,
    ctx: &[Ctx<'p>],
) -> Vec<Ctx<'p>> {
    let matcher = ctx_matcher(ctx_ref, pa, q);

    fn filter_one<'p>(
        pa: &PatArena<'p>,
        matcher: &CtxMatcherFn<'p, '_>,
        left: &[&'p Pattern],
        p: &'p Pattern,
        ps: &[&'p Pattern],
        out: &mut Vec<Ctx<'p>>,
    ) {
        match &p.pat_desc {
            PatternDesc::Tpat_or(p1, p2, _) => {
                filter_one(pa, matcher, left, pa.pat(*p1), ps, out);
                filter_one(pa, matcher, left, pa.pat(*p2), ps, out);
            }
            PatternDesc::Tpat_alias(p_inner, _, _) => {
                filter_one(pa, matcher, left, pa.pat(*p_inner), ps, out)
            }
            PatternDesc::Tpat_var(..) => filter_one(pa, matcher, left, omega(), ps, out),
            _ => {
                if let Ok((to_left, right)) = matcher(p, ps) {
                    let mut new_left = Vec::with_capacity(left.len() + 1);
                    new_left.push(to_left);
                    new_left.extend_from_slice(left);
                    out.push(Ctx {
                        left: new_left,
                        right,
                    });
                }
            }
        }
    }

    let mut out = Vec::new();
    for l in ctx {
        match l.right.split_first() {
            Some((p, ps)) => filter_one(pa, &*matcher, &l.left, p, ps, &mut out),
            None => crate::misc::fatal_error("Matching.filter_ctx"),
        }
    }
    out
}

// ============================================================================
// select_columns, ctx_lub, ctx_match
// ============================================================================

/// Select columns from pattern rows and combine with context.
/// Equivalent to OCaml's `select_columns`.
pub fn select_columns<'p>(pa: &'p PatArena<'p>, pss: &Matrix<'p>, ctx: &[Ctx<'p>]) -> Vec<Ctx<'p>> {
    let n = ncols(pss);
    let mut result = Vec::new();
    for ps in pss.iter() {
        for c in ctx.iter() {
            let (transfert, right) = c.right.split_at(n);
            if let Ok(lub_result) = lubs(pa, transfert, ps) {
                let mut left = lub_result;
                left.extend(c.left.iter().copied());
                result.push(Ctx {
                    left,
                    right: right.to_vec(),
                });
            }
        }
    }
    result
}

/// Least upper bound of a pattern with contexts.
/// Equivalent to OCaml's `ctx_lub`.
pub fn ctx_lub<'p>(pa: &'p PatArena<'p>, p: &'p Pattern, ctx: &[Ctx<'p>]) -> Vec<Ctx<'p>> {
    let mut result = Vec::new();
    for c in ctx.iter() {
        match c.right.split_first() {
            Some((q, rem)) => {
                if let Ok(r) = lub(pa, p, q) {
                    let mut right = Vec::with_capacity(rem.len() + 1);
                    right.push(r);
                    right.extend_from_slice(rem);
                    result.push(Ctx {
                        left: c.left.clone(),
                        right,
                    });
                }
            }
            None => crate::misc::fatal_error("Matching.ctx_lub"),
        }
    }
    result
}

/// Check if any context's right side may be compatible with any row in pss.
/// Equivalent to OCaml's `ctx_match`.
pub fn ctx_match(pa: &PatArena<'_>, ctx: &[Ctx<'_>], pss: &Matrix<'_>) -> bool {
    ctx.iter()
        .any(|c| pss.iter().any(|ps| may_compats(pa, &c.right, ps)))
}

// ============================================================================
// Jumps — mapping from exit numbers to context lists
// ============================================================================

/// Jump table: sorted list of (exit_number, context_list) pairs,
/// sorted in descending order by exit number.
pub type Jumps<'p> = Vec<(i32, Vec<Ctx<'p>>)>;

/// Position of the entry for exit number `i` in the descending table, if
/// present. Like OCaml's `Jumps.extract`, the scan stops at the first entry
/// whose exit number is not greater than `i`.
fn jumps_position(i: i32, jumps: &Jumps<'_>) -> Option<usize> {
    jumps
        .iter()
        .position(|(j, _)| *j <= i)
        .filter(|&p| jumps[p].0 == i)
}

/// Extract the contexts for exit number i, returning (extracted, remaining).
pub fn jumps_extract<'p>(i: i32, mut jumps: Jumps<'p>) -> (Vec<Ctx<'p>>, Jumps<'p>) {
    match jumps_position(i, &jumps) {
        Some(p) => (jumps.remove(p).1, jumps),
        None => (Vec::new(), jumps),
    }
}

/// Remove the (first) entry for exit number i.
pub fn jumps_remove<'p>(i: i32, mut jumps: Jumps<'p>) -> Jumps<'p> {
    if let Some(p) = jumps.iter().position(|(j, _)| *j == i) {
        jumps.remove(p);
    }
    jumps
}

/// Empty jump table.
pub fn jumps_empty<'p>() -> Jumps<'p> {
    Vec::new()
}

/// Check if a jump table is empty.
pub fn jumps_is_empty(jumps: &Jumps<'_>) -> bool {
    jumps.is_empty()
}

/// Create a singleton jump table (or empty if ctx is empty).
pub fn jumps_singleton<'p>(i: i32, ctx: Vec<Ctx<'p>>) -> Jumps<'p> {
    if ctx.is_empty() {
        Vec::new()
    } else {
        vec![(i, ctx)]
    }
}

/// Add contexts for exit number i to the jump table.
/// Maintains descending sort order and merges with get_mins when
/// the exit number already exists.
pub fn jumps_add<'p>(
    pa: &PatArena<'p>,
    i: i32,
    pss: Vec<Ctx<'p>>,
    mut jumps: Jumps<'p>,
) -> Jumps<'p> {
    if pss.is_empty() {
        return jumps;
    }
    match jumps.iter().position(|(j, _)| *j <= i) {
        None => jumps.push((i, pss)),
        Some(p) if jumps[p].0 < i => jumps.insert(p, (i, pss)),
        Some(p) => {
            // Same exit number: merge with get_mins.
            let qss = std::mem::take(&mut jumps[p].1);
            let mut combined = pss;
            combined.extend(qss);
            jumps[p].1 = get_mins(|c1, c2| le_ctx(pa, c1, c2), combined);
        }
    }
    jumps
}

/// Union of two jump tables.
/// Maintains descending sort order and merges contexts with get_mins.
pub fn jumps_union<'p>(pa: &PatArena<'p>, env1: Jumps<'p>, env2: Jumps<'p>) -> Jumps<'p> {
    let mut result = Vec::with_capacity(env1.len() + env2.len());
    let mut env1 = env1.into_iter().peekable();
    let mut env2 = env2.into_iter().peekable();
    loop {
        let (i1, i2) = match (env1.peek(), env2.peek()) {
            (None, _) => {
                result.extend(env2);
                break;
            }
            (_, None) => {
                result.extend(env1);
                break;
            }
            (Some((i1, _)), Some((i2, _))) => (*i1, *i2),
        };
        if i1 == i2 {
            let (_, mut combined) = env1.next().expect("peeked");
            let (_, pss2) = env2.next().expect("peeked");
            combined.extend(pss2);
            result.push((i1, get_mins(|c1, c2| le_ctx(pa, c1, c2), combined)));
        } else if i1 > i2 {
            result.extend(env1.next());
        } else {
            result.extend(env2.next());
        }
    }
    result
}

/// Merge adjacent pairs of jump tables (used by jumps_unions).
fn merge<'p>(pa: &PatArena<'p>, envs: Vec<Jumps<'p>>) -> Vec<Jumps<'p>> {
    if envs.len() < 2 {
        return envs;
    }
    let mut result = Vec::new();
    let mut iter = envs.into_iter();
    loop {
        match (iter.next(), iter.next()) {
            (Some(e1), Some(e2)) => result.push(jumps_union(pa, e1, e2)),
            (Some(e1), None) => {
                result.push(e1);
                break;
            }
            (None, _) => break,
        }
    }
    result
}

/// Union of a list of jump tables (using balanced merge).
pub fn jumps_unions<'p>(pa: &PatArena<'p>, envs: Vec<Jumps<'p>>) -> Jumps<'p> {
    match envs.len() {
        0 => Vec::new(),
        1 => envs.into_iter().next().unwrap(),
        _ => jumps_unions(pa, merge(pa, envs)),
    }
}

/// Map a function over the context lists in a jump table.
pub fn jumps_map<'p>(f: impl Fn(Vec<Ctx<'p>>) -> Vec<Ctx<'p>>, env: Jumps<'p>) -> Jumps<'p> {
    env.into_iter().map(|(i, pss)| (i, f(pss))).collect()
}

// ============================================================================
// Pattern matching before compilation
// ============================================================================

/// Pattern matching before any compilation.
/// Equivalent to OCaml's `pattern_matching`.
#[derive(Clone)]
pub struct PatternMatching<'p> {
    /// Cases: list of (pattern_row, action).
    cases: Vec<Clause<'p>>,
    /// Arguments to match against: (expression, let_kind).
    pub args: MatchArgs,
    /// Default: mapping from matrices to exit numbers.
    pub default: DefaultEnv<'p>,
}

// ============================================================================
// Pattern matching after or-pat and mixture rule application
// ============================================================================

/// Pattern matching after application of both the or-pat rule and the
/// mixture rule.
#[derive(Clone)]
pub struct PmOrCompiled<'p> {
    /// The body pattern matching.
    pub body: PatternMatching<'p>,
    /// Handlers for or-patterns: (matrix, exit_number, idents, pattern_matching).
    pub handlers: Vec<OrHandler<'p>>,
    /// The or-pattern matrix.
    pub or_matrix: Matrix<'p>,
}

/// Half-compiled pattern matching.
#[derive(Clone)]
pub enum PmHalfCompiled<'p> {
    /// Or-pattern compiled.
    PmOr(PmOrCompiled<'p>),
    /// Variable case.
    PmVar(PmVarCompiled<'p>),
    /// Simple pattern matching.
    Pm(PatternMatching<'p>),
}

/// Variable case in half-compiled pattern matching.
#[derive(Clone)]
pub struct PmVarCompiled<'p> {
    /// The inner half-compiled pattern matching.
    pub inside: Box<PmHalfCompiled<'p>>,
    /// The variable argument.
    pub var_arg: RawLambda,
}

/// Half-compiled pattern matching with associated info.
pub struct PmHalfCompiledInfo<'p> {
    /// The half-compiled pattern matching.
    pub me: PmHalfCompiled<'p>,
    /// The associated matrix.
    pub matrix: Matrix<'p>,
    /// The top-level default environment.
    pub top_default: DefaultEnv<'p>,
}

// ============================================================================
// Layer 2: Catch/exit and action sharing
// ============================================================================
// Ported from OCaml's matching.ml lines 442-587.

// ============================================================================
// Lambda.make_key — normalize a RawLambda for structural comparison
// ============================================================================

/// Maximum size for make_key normalization (matches OCaml's max_raw = 32).
const MAX_RAW: i32 = 32;

fn charge_logical_record_fields(
    count: &mut i32,
    primitive: &Primitive,
    actual_arg_count: usize,
) -> Option<()> {
    let Primitive::Pmakeblock(
        tag_info @ (TagInfo::Record { .. } | TagInfo::RecordInlined { .. }),
        _,
    ) = primitive
    else {
        return Some(());
    };

    let logical_count = tag_info.logical_field_count();
    if logical_count > actual_arg_count {
        *count += (logical_count - actual_arg_count) as i32;
        if *count > MAX_RAW {
            return None;
        }
    }
    Some(())
}

/// Normalize a RawLambda for structural comparison.
/// - Alias lets are substituted (variable replaced by its definition)
/// - Other let-bound variables get sequential normalized names
/// - Locations are cleared
///
/// Returns None if the lambda is too complex (functions, letrec, loops, etc.)
///
/// Equivalent to OCaml's `Lambda.make_key`.
fn make_key<B: RawLambdaBuilder>(b: &B, e: RawLambda) -> Option<RawLambda> {
    type KeyEnv = Vec<(Ident, RawLambda)>;
    fn tr_rec<B: RawLambdaBuilder>(
        b: &B,
        env: &mut KeyEnv,
        e: RawLambda,
        count: &mut i32,
        next_id: &mut i32,
    ) -> Option<RawLambda> {
        *count += 1;
        if *count > MAX_RAW {
            return None; // Too big
        }
        match b.node(e) {
            Node::Var(id) => {
                let id = b.get().ident(id);
                match env.iter().rev().find(|(key, _)| key.same(&id)) {
                    Some((_, replacement)) => Some(*replacement),
                    None => Some(e),
                }
            }
            Node::Const(_) | Node::GlobalModule(_) => Some(e),
            Node::Apply { func, args, info } => {
                let func = tr_rec(b, env, func, count, next_id)?;
                let args = tr_recs(b, env, &b.list(args), count, next_id)?;
                let payload = b.get().apply_payload(info).clone();
                Some(b.apply(
                    func,
                    &args,
                    crate::lambda::ApInfo {
                        loc: LamLoc::NONE,
                        ..payload.info
                    },
                ))
            }
            Node::Let {
                kind,
                id,
                value,
                body,
            } => {
                let x = b.get().ident(id);
                if kind == LetKind::Alias {
                    // Ignore aliases -> substitute
                    let ex = tr_rec(b, env, value, count, next_id)?;
                    env.push((x, ex));
                    let result = tr_rec(b, env, body, count, next_id);
                    env.pop();
                    return result;
                }
                if matches!(kind, LetKind::Strict | LetKind::StrictOpt)
                    && matches!(b.as_var(body), Some(v) if v.same(&x))
                {
                    // Llet (Strict|StrictOpt, x, ex, Lvar v) when v same x -> tr_rec ex
                    return tr_rec(b, env, value, count, next_id);
                }
                // Because of side effects, keep other lets with normalized names
                let ex_norm = tr_rec(b, env, value, count, next_id)?;
                let y = Ident::new(x.name(), *next_id, IdentFlags::NONE);
                *next_id += 1;
                let y_var = b.var(y);
                env.push((x, y_var));
                let body_norm = tr_rec(b, env, body, count, next_id);
                env.pop();
                Some(b.let_(kind, y, ex_norm, body_norm?))
            }
            Node::Prim { args, info } => {
                let primitive = b.get().prim_payload(info).primitive.clone();
                let args = b.list(args);
                charge_logical_record_fields(count, &primitive, args.len())?;
                let args = tr_recs(b, env, &args, count, next_id)?;
                Some(b.prim(primitive, &args, LamLoc::NONE))
            }
            Node::Switch { scrut, .. } => {
                let (_, sw) = b.switch_parts(e).expect("switch node");
                let scrut_norm = tr_rec(b, env, scrut, count, next_id)?;
                let mut consts = Vec::with_capacity(sw.sw_consts.len());
                for (tag, act) in sw.sw_consts {
                    consts.push((tag, tr_rec(b, env, act, count, next_id)?));
                }
                let mut blocks = Vec::with_capacity(sw.sw_blocks.len());
                for (tag, act) in sw.sw_blocks {
                    blocks.push((tag, tr_rec(b, env, act, count, next_id)?));
                }
                let fail = match sw.sw_failaction {
                    None => None,
                    Some(fail) => Some(tr_rec(b, env, fail, count, next_id)?),
                };
                Some(b.switch(
                    scrut_norm,
                    RawLambdaSwitch {
                        sw_consts_full: sw.sw_consts_full,
                        sw_consts: consts,
                        sw_blocks_full: sw.sw_blocks_full,
                        sw_blocks: blocks,
                        sw_failaction: fail,
                        sw_dispatch: sw.sw_dispatch,
                    },
                ))
            }
            Node::StringSwitch { .. } => {
                let (scrut, cases, default) = b.string_switch_parts(e).expect("string switch");
                let scrut_norm = tr_rec(b, env, scrut, count, next_id)?;
                let mut norm_cases = Vec::with_capacity(cases.len());
                for (s, act) in cases {
                    norm_cases.push((s, tr_rec(b, env, act, count, next_id)?));
                }
                let default = match default {
                    None => None,
                    Some(default) => Some(tr_rec(b, env, default, count, next_id)?),
                };
                Some(b.string_switch(scrut_norm, &norm_cases, default))
            }
            Node::StaticRaise { label, args } => {
                let args = tr_recs(b, env, &b.list(args), count, next_id)?;
                Some(b.static_raise(label, &args))
            }
            Node::StaticCatch {
                body,
                handler,
                info,
            } => {
                let body = tr_rec(b, env, body, count, next_id)?;
                let handler = tr_rec(b, env, handler, count, next_id)?;
                Some(b.push(Node::StaticCatch {
                    body,
                    handler,
                    info,
                }))
            }
            Node::TryWith { body, id, handler } => {
                let body = tr_rec(b, env, body, count, next_id)?;
                let handler = tr_rec(b, env, handler, count, next_id)?;
                Some(b.push(Node::TryWith { body, id, handler }))
            }
            Node::TryFinally { body, finally } => {
                let body = tr_rec(b, env, body, count, next_id)?;
                let finally = tr_rec(b, env, finally, count, next_id)?;
                Some(b.try_finally(body, finally))
            }
            Node::If { cond, then_, else_ } => {
                let cond = tr_rec(b, env, cond, count, next_id)?;
                let then_ = tr_rec(b, env, then_, count, next_id)?;
                let else_ = tr_rec(b, env, else_, count, next_id)?;
                Some(b.if_raw(cond, then_, else_))
            }
            Node::Sequence(e1, e2) => {
                let e1 = tr_rec(b, env, e1, count, next_id)?;
                let e2 = tr_rec(b, env, e2, count, next_id)?;
                Some(b.seq(e1, e2))
            }
            Node::Assign { id, value } => {
                let value = tr_rec(b, env, value, count, next_id)?;
                Some(b.push(Node::Assign { id, value }))
            }
            // OCaml `Lambda.make_key` after #8348:
            // `Lbreak -> Lbreak | Lcontinue -> Lcontinue`.
            Node::Break | Node::Continue => Some(e),
            // Functions, letrec, loops are not simple
            Node::LetRec { .. }
            | Node::Function { .. }
            | Node::For { .. }
            | Node::ForOf { .. }
            | Node::ForAwaitOf { .. }
            | Node::While(..) => None,
        }
    }

    fn tr_recs<B: RawLambdaBuilder>(
        b: &B,
        env: &mut KeyEnv,
        es: &[RawLambda],
        count: &mut i32,
        next_id: &mut i32,
    ) -> Option<Vec<RawLambda>> {
        es.iter()
            .map(|e| tr_rec(b, env, *e, count, next_id))
            .collect()
    }

    // OCaml's `Lambda.make_key` extends a tiny identifier environment with
    // `Ident.add` while capped by `max_raw = 32`
    // (`compiler/ml/lambda.ml:432-466`). Use a stack of bindings here instead
    // of cloning a hash table for every normalized `let`.
    tr_rec(b, &mut Vec::new(), e, &mut 0, &mut 0)
}

/// Convert a RawLambda to a string key for comparison purposes.
/// Returns None if the lambda cannot be normalized.
fn make_key_string<B: RawLambdaBuilder>(b: &B, e: RawLambda) -> Option<String> {
    let mut writer = MakeKeyWriter::new(b);
    let mut out = KeyOut::new(128);
    writer.write_raw(&*b.get(), e, &mut out)?;
    Some(out.buf)
}

/// Convert a delayed match action to the same structural key as
/// `Lambda.make_key` without first expanding the delayed `Llet` chain.
///
/// OCaml actions are immutable lambda values, so `matching.ml:489-500` can pass
/// them directly to `Lambda.make_key` (`lambda.ml:432-466`). Rust stores some
/// action lets as `MatchActionKind::Bind` to preserve that sharing; this
/// traverses those wrappers as if they were `Llet` nodes while keeping the
/// `max_raw = 32` cutoff from `lambda.ml:434,438-440`.
fn make_key_string_action<B: RawLambdaBuilder>(b: &B, action: &MatchAction) -> Option<String> {
    let mut writer = MakeKeyWriter::new(b);
    let mut out = KeyOut::new(128);
    writer.write_action(action, &mut out)?;
    Some(out.buf)
}

/// Whether `e`'s `Lambda.make_key` exists and equals `key`. Writes the key
/// against `key` and stops at the first byte that differs, so unequal
/// actions are rejected without normalizing them in full.
fn make_key_equals<B: RawLambdaBuilder>(b: &B, e: RawLambda, key: &str) -> bool {
    let mut writer = MakeKeyWriter::new(b);
    let mut out = KeyOut::expecting(key);
    writer.write_raw(&*b.get(), e, &mut out).is_some() && out.matches_all()
}

enum KeyBody<'a> {
    Raw(RawLambda),
    Action(&'a MatchAction),
}

/// Writes `Lambda.make_key`. Reads hold the arena only inside
/// [`MakeKeyWriter::write_raw_after_count`], which never reaches an action;
/// a guarded action's key term is built in [`MakeKeyWriter::write_action`].
struct MakeKeyWriter<'b, B: RawLambdaBuilder> {
    b: &'b B,
    count: i32,
    next_id: i32,
    env: Vec<(Ident, String)>,
}

impl<'b, B: RawLambdaBuilder> MakeKeyWriter<'b, B> {
    fn new(b: &'b B) -> Self {
        Self {
            b,
            count: 0,
            next_id: 0,
            env: Vec::new(),
        }
    }

    fn write_raw(&mut self, a: &B::Reader, e: RawLambda, out: &mut KeyOut<'_>) -> Option<()> {
        self.count += 1;
        if self.count > MAX_RAW || out.diverged {
            return None;
        }
        self.write_raw_after_count(a, e, out)
    }

    fn write_action(&mut self, action: &MatchAction, out: &mut KeyOut<'_>) -> Option<()> {
        self.count += 1;
        if self.count > MAX_RAW {
            return None;
        }
        match &action.0.kind {
            MatchActionKind::Case { guard: None, body } => {
                self.write_raw_after_count(&*self.b.get(), *body, out)
            }
            // `Matching.action_key_term` (`compiler/ml/matching.ml:381-386`).
            MatchActionKind::Case { guard: Some(_), .. } => {
                let fallthrough = fallthrough_stand_in(self.b);
                let term = action.body_with(self.b, fallthrough);
                self.write_raw_after_count(&*self.b.get(), term, out)
            }
            MatchActionKind::Bind {
                kind,
                id,
                arg,
                action,
            } => self.write_let(None, *kind, id, *arg, KeyBody::Action(action), out),
        }
    }

    fn write_body(
        &mut self,
        a: Option<&B::Reader>,
        body: KeyBody<'_>,
        out: &mut KeyOut<'_>,
    ) -> Option<()> {
        match body {
            KeyBody::Raw(raw) => match a {
                Some(a) => self.write_raw(a, raw, out),
                None => self.write_raw(&*self.b.get(), raw, out),
            },
            KeyBody::Action(action) => self.write_action(action, out),
        }
    }

    fn write_raw_after_count(
        &mut self,
        a: &B::Reader,
        e: RawLambda,
        out: &mut KeyOut<'_>,
    ) -> Option<()> {
        match a.view(e) {
            View::Var(id) => {
                if let Some((_, replacement)) = self.env.iter().rev().find(|(key, _)| key.same(&id))
                {
                    out.push_str(replacement);
                } else {
                    out.push_str("Lvar(");
                    write_ident_key(out, &id);
                    out.push(')');
                }
                Some(())
            }
            View::Const(c) => {
                out.push_str("Lconst(");
                c.encode(out);
                out.push(')');
                Some(())
            }
            View::GlobalModule(id) => {
                out.push_str("LglobalModule(");
                write_ident_key(out, &id);
                out.push(')');
                Some(())
            }
            View::Apply { func, args, info } => {
                out.push_str("Lapply(");
                self.write_raw(a, func, out)?;
                out.push_str(",[");
                self.write_raw_list(a, args, out)?;
                out.push_str("],");
                info.status.encode(out);
                out.push(')');
                Some(())
            }
            View::Let(kind, x, ex, body) => {
                self.write_let(Some(a), kind, &x, ex, KeyBody::Raw(body), out)
            }
            View::Prim(primitive, args, _) => {
                charge_logical_record_fields(&mut self.count, primitive, args.len())?;
                out.push_str("Lprim(");
                primitive.encode(out);
                out.push_str(",[");
                self.write_raw_list(a, args, out)?;
                out.push_str("])");
                Some(())
            }
            View::Switch(scrut, sw) => {
                out.push_str("Lswitch(");
                self.write_raw(a, scrut, out)?;
                write!(out, ",fullc={},consts=[", sw.payload.consts_full).ok()?;
                for (idx, (tag, act)) in sw.consts().enumerate() {
                    if idx > 0 {
                        out.push(',');
                    }
                    write!(out, "{tag}:").ok()?;
                    self.write_raw(a, act, out)?;
                }
                write!(out, "],fullb={},blocks=[", sw.payload.blocks_full).ok()?;
                for (idx, (tag, act)) in sw.blocks().enumerate() {
                    if idx > 0 {
                        out.push(',');
                    }
                    write!(out, "{tag}:").ok()?;
                    self.write_raw(a, act, out)?;
                }
                out.push_str("],fail=");
                self.write_raw_opt(a, sw.actions.fail, out)?;
                out.push_str(",names=");
                sw.payload.dispatch.encode(out);
                out.push(')');
                Some(())
            }
            View::StringSwitch(scrut, sw) => {
                out.push_str("LstringSwitch(");
                self.write_raw(a, scrut, out)?;
                out.push_str(",[");
                for (idx, (label, act)) in sw.cases().enumerate() {
                    if idx > 0 {
                        out.push(',');
                    }
                    label.encode(out);
                    out.push(':');
                    self.write_raw(a, act, out)?;
                }
                out.push_str("],");
                self.write_raw_opt(a, sw.default, out)?;
                out.push(')');
                Some(())
            }
            View::StaticRaise(i, args) => {
                write!(out, "LstaticRaise({i},[").ok()?;
                self.write_raw_list(a, args, out)?;
                out.push_str("])");
                Some(())
            }
            View::StaticCatch(e1, i, vars, e2) => {
                write!(out, "LstaticCatch(").ok()?;
                self.write_raw(a, e1, out)?;
                write!(out, ",({i},[").ok()?;
                for (idx, var) in vars.iter().enumerate() {
                    if idx > 0 {
                        out.push(',');
                    }
                    write_ident_key(out, var);
                }
                out.push_str("]),");
                self.write_raw(a, e2, out)?;
                out.push(')');
                Some(())
            }
            View::TryFinally(e1, e2) => {
                out.push_str("LtryFinally(");
                self.write_raw(a, e1, out)?;
                out.push(',');
                self.write_raw(a, e2, out)?;
                out.push(')');
                Some(())
            }
            View::TryWith(e1, x, e2) => {
                out.push_str("LtryWith(");
                self.write_raw(a, e1, out)?;
                out.push(',');
                write_ident_key(out, &x);
                out.push(',');
                self.write_raw(a, e2, out)?;
                out.push(')');
                Some(())
            }
            View::If(cond, ifso, ifnot) => {
                out.push_str("LifThenElse(");
                self.write_raw(a, cond, out)?;
                out.push(',');
                self.write_raw(a, ifso, out)?;
                out.push(',');
                self.write_raw(a, ifnot, out)?;
                out.push(')');
                Some(())
            }
            View::Sequence(e1, e2) => {
                out.push_str("Lsequence(");
                self.write_raw(a, e1, out)?;
                out.push(',');
                self.write_raw(a, e2, out)?;
                out.push(')');
                Some(())
            }
            View::Assign(x, e) => {
                out.push_str("Lassign(");
                write_ident_key(out, &x);
                out.push(',');
                self.write_raw(a, e, out)?;
                out.push(')');
                Some(())
            }
            View::Break => {
                out.push_str("Lbreak");
                Some(())
            }
            View::Continue => {
                out.push_str("Lcontinue");
                Some(())
            }
            View::LetRec(..)
            | View::Function { .. }
            | View::For(..)
            | View::ForOf(..)
            | View::ForAwaitOf(..)
            | View::While(..) => None,
        }
    }

    /// `a` is the held arena when the let is a raw node, `None` when it is
    /// an action's binding (whose body may need building).
    fn write_let(
        &mut self,
        a: Option<&B::Reader>,
        kind: LetKind,
        x: &Ident,
        ex: RawLambda,
        body: KeyBody<'_>,
        out: &mut KeyOut<'_>,
    ) -> Option<()> {
        if kind == LetKind::Alias {
            let ex_key = match a {
                Some(a) => self.raw_to_string(a, ex)?,
                None => self.raw_to_string(&*self.b.get(), ex)?,
            };
            self.env.push((*x, ex_key));
            let result = self.write_body(a, body, out);
            self.env.pop();
            return result;
        }

        let same_var = match a {
            Some(a) => same_var_body(a, &body, x),
            None => same_var_body(&*self.b.get(), &body, x),
        };
        if matches!(kind, LetKind::Strict | LetKind::StrictOpt) && same_var {
            return match a {
                Some(a) => self.write_raw(a, ex, out),
                None => self.write_raw(&*self.b.get(), ex, out),
            };
        }

        out.push_str("Llet(");
        kind.encode(out);
        out.push(',');
        let synthetic_stamp = self.next_id;
        self.next_id += 1;
        write_synthetic_ident_key(out, x.name(), synthetic_stamp);
        out.push(',');
        match a {
            Some(a) => self.write_raw(a, ex, out)?,
            None => self.write_raw(&*self.b.get(), ex, out)?,
        }
        out.push(',');
        let mut replacement = KeyOut::new(x.name().len() + 16);
        replacement.push_str("Lvar(");
        write_synthetic_ident_key(&mut replacement, x.name(), synthetic_stamp);
        replacement.push(')');
        self.env.push((*x, replacement.buf));
        let result = self.write_body(a, body, out);
        self.env.pop();
        result?;
        out.push(')');
        Some(())
    }

    fn raw_to_string(&mut self, a: &B::Reader, e: RawLambda) -> Option<String> {
        let mut out = KeyOut::new(64);
        self.write_raw(a, e, &mut out)?;
        Some(out.buf)
    }

    fn write_raw_list(
        &mut self,
        a: &B::Reader,
        items: &[RawLambda],
        out: &mut KeyOut<'_>,
    ) -> Option<()> {
        for (idx, item) in items.iter().enumerate() {
            if idx > 0 {
                out.push(',');
            }
            self.write_raw(a, *item, out)?;
        }
        Some(())
    }

    fn write_raw_opt(
        &mut self,
        a: &B::Reader,
        item: Option<RawLambda>,
        out: &mut KeyOut<'_>,
    ) -> Option<()> {
        match item {
            None => out.push_str("None"),
            Some(item) => {
                out.push_str("Some(");
                self.write_raw(a, item, out)?;
                out.push(')');
            }
        }
        Some(())
    }
}

fn same_var_body(a: &impl RawLambdaRead, body: &KeyBody<'_>, id: &Ident) -> bool {
    match body {
        KeyBody::Raw(raw) => matches!(a.as_var(*raw), Some(v) if v.same(id)),
        KeyBody::Action(action) => matches!(
            &action.0.kind,
            MatchActionKind::Case { guard: None, body } if matches!(a.as_var(*body), Some(v) if v.same(id))
        ),
    }
}

fn write_ident_key(out: &mut KeyOut<'_>, id: &Ident) {
    match id.stamp() {
        0 => {
            out.push_str(id.name());
            out.push('!');
        }
        -1 => {
            out.push_str(id.name());
            out.push('#');
        }
        stamp => write_synthetic_ident_key_with_global(out, id.name(), stamp, id.is_global()),
    }
}

fn write_synthetic_ident_key(out: &mut KeyOut<'_>, name: &str, stamp: i32) {
    write_synthetic_ident_key_with_global(out, name, stamp, false);
}

fn write_synthetic_ident_key_with_global(
    out: &mut KeyOut<'_>,
    name: &str,
    stamp: i32,
    is_global: bool,
) {
    if stamp == 0 {
        out.push_str(name);
        out.push('!');
    } else if stamp == -1 {
        out.push_str(name);
        out.push('#');
    } else {
        out.push_str(name);
        // Fails only when a comparing sink has already diverged.
        if write!(out, "/{stamp}").is_ok() && is_global {
            out.push('g');
        }
    }
}

// ============================================================================
// StoreExp — Action deduplication using make_key
// ============================================================================
// Ported from OCaml's Switch.Store, specialized for lambda/RawLambda.

/// Action store for deduplicating lambda actions.
/// Equivalent to OCaml's `StoreExp` (Switch.Store specialized for lambda).
///
/// Uses string keys (from `make_key` normalization) for comparison,
/// since RawLambda doesn't implement PartialEq/Ord.
pub struct StoreExp<'b, B: RawLambdaBuilder> {
    b: &'b B,
    /// Map from normalized key string -> action index.
    ///
    /// OCaml uses `AMap` for lookup in `Switch.Store.store`
    /// (`compiler/ml/switch.ml:55-65`) and iterates it only to mark shared
    /// action slots (`compiler/ml/switch.ml:67-76`). That iteration order does
    /// not feed the generated lambda, so Rust records the shared flag directly
    /// on the action slot when a key hits and keeps the map for lookup only.
    map: HashMap<String, usize>,
    /// Accumulated actions in index order: (shared, action).
    acts: Vec<(bool, RawLambda)>,
}

impl<'b, B: RawLambdaBuilder> StoreExp<'b, B> {
    /// Create a new empty store.
    /// Equivalent to OCaml's `mk_store`.
    pub fn mk_store(b: &'b B) -> Self {
        StoreExp {
            b,
            map: HashMap::new(),
            acts: Vec::new(),
        }
    }

    /// Internal: add an action unconditionally (no dedup).
    fn add(&mut self, must_share: bool, act: RawLambda) -> usize {
        self.acts.push((must_share, act));
        self.acts.len() - 1
    }

    /// Internal: store an action, deduplicating if possible.
    fn store(&mut self, must_share: bool, act: RawLambda) -> usize {
        match make_key_string(self.b, act) {
            Some(key) => {
                if let Some(&i) = self.map.get(&key) {
                    self.acts[i].0 = true;
                    i
                } else {
                    let i = self.add(must_share, act);
                    self.map.insert(key, i);
                    i
                }
            }
            None => self.add(must_share, act),
        }
    }

    /// Store an action (not forced shared).
    /// Equivalent to OCaml's `act_store`.
    pub fn act_store(&mut self, act: RawLambda) -> usize {
        self.store(false, act)
    }

    /// Store an action that must be shared.
    /// Equivalent to OCaml's `act_store_shared`.
    pub fn act_store_shared(&mut self, act: RawLambda) -> usize {
        self.store(true, act)
    }

    /// Get the actions array with sharing info.
    /// Actions that were stored multiple times or marked as must-share
    /// are wrapped in `Shared`; others are `Single`.
    /// Equivalent to OCaml's `act_get_shared`.
    pub fn act_get_shared(self) -> Vec<Shared<RawLambda>> {
        // OCaml's store closes over the action list and returns those actions
        // directly when `act_get_shared` is called (compiler/ml/switch.ml:55-67).
        // Rust callers consume the store at the same point, so move the raw
        // lambda actions into the result instead of recursively cloning them.
        self.acts
            .into_iter()
            .map(|(shared, act)| {
                if shared {
                    Shared::Shared(act)
                } else {
                    Shared::Single(act)
                }
            })
            .collect()
    }
}

// ============================================================================
// make_exit — Lstaticraise(i, [])
// ============================================================================

/// Create a static raise with no arguments.
/// Equivalent to OCaml's `make_exit`.
pub fn make_exit<B: RawLambdaBuilder>(b: &B, i: i32) -> RawLambda {
    b.static_raise(i, &[])
}

// ============================================================================
// make_catch — Introduce catch if worth it
// ============================================================================

/// Introduce a catch around `k(d)`, if `d` is not already a simple exit.
/// If `d` is already `Lstaticraise(_, [])`, just returns `k(d)`.
/// Otherwise, allocates a new exit number, returns `Lstaticcatch(k(exit(e)), (e,[]), d)`.
///
/// Equivalent to OCaml's `make_catch`.
pub fn make_catch<B: RawLambdaBuilder>(
    b: &B,
    d: RawLambda,
    next_raise_count: &mut i32,
    k: impl FnOnce(RawLambda) -> RawLambda,
) -> RawLambda {
    match b.node(d) {
        Node::StaticRaise { args, .. } if args == LamArena::EMPTY => k(d),
        _ => {
            let e = bump_raise_count(next_raise_count);
            let exit = make_exit(b, e);
            let body = k(exit);
            b.static_catch(body, e, &[], d)
        }
    }
}

// ============================================================================
// as_simple_exit — Check if lambda is just an exit
// ============================================================================

/// Check if a lambda is just a static raise (possibly wrapped in alias lets).
/// Returns the exit number if so.
///
/// Equivalent to OCaml's `as_simple_exit`.
pub fn as_simple_exit(a: &impl RawLambdaRead, lam: RawLambda) -> Option<i32> {
    match a.view(lam) {
        View::StaticRaise(i, []) => Some(i),
        View::Let(LetKind::Alias, _, _, e) => as_simple_exit(a, e),
        _ => None,
    }
}

// ============================================================================
// make_catch_delayed — Delayed catch with next_raise_count
// ============================================================================

/// Create a delayed catch: returns the exit number and the handler to wrap
/// with, if any (see `apply_catch_delayed`). If the handler is already a
/// simple exit, there is nothing to wrap.
///
/// Equivalent to OCaml's `make_catch_delayed`.
pub fn make_catch_delayed<B: RawLambdaBuilder>(
    b: &B,
    handler: RawLambda,
    next_raise_count: &mut i32,
) -> (i32, Option<RawLambda>) {
    let simple = as_simple_exit(&*b.get(), handler);
    match simple {
        Some(i) => (i, None),
        None => (bump_raise_count(next_raise_count), Some(handler)),
    }
}

/// The wrapper `make_catch_delayed` returns: the identity without a handler,
/// else `Lstaticcatch(body, (i,[]), handler)`, or just `handler` when `body`
/// is `Lstaticraise(i, _)`.
fn apply_catch_delayed<B: RawLambdaBuilder>(
    b: &B,
    i: i32,
    handler: Option<RawLambda>,
    body: RawLambda,
) -> RawLambda {
    let Some(handler) = handler else {
        return body;
    };
    match b.node(body) {
        Node::StaticRaise { label, .. } if label == i => handler,
        _ => b.static_catch(body, i, &[], handler),
    }
}

// ============================================================================
// raw_static_raise — The raw action's static-raise shape
// ============================================================================

/// `raw_action r` (`compiler/ml/matching.ml:479-482`) when it is a static
/// raise: `make_key r`, or `r` itself when `make_key` fails.
fn raw_static_raise<B: RawLambdaBuilder>(b: &B, l: RawLambda) -> Option<(i32, Vec<RawLambda>)> {
    let raw = make_key(b, l).unwrap_or(l);
    match b.node(raw) {
        Node::StaticRaise { label, args } => Some((label, b.list(args))),
        _ => None,
    }
}

// ============================================================================
// up_ok_action — Check if swapping two actions is safe
// ============================================================================

/// Check if two actions are equivalent (safe to swap).
/// Returns true if both can be normalized and their normalized forms are equal.
///
/// Equivalent to OCaml's `up_ok_action`.
fn up_ok_action<B: RawLambdaBuilder>(
    b: &B,
    ctx_ref: Option<&TypeContext>,
    act1: &MatchAction,
    act2: &MatchAction,
) -> bool {
    // `let fail = Lambda.var (Ident.create "fallthrough")`
    // (compiler/ml/matching.ml:522-525): every comparison takes a fresh
    // identifier, shared by both keys. The cached keys use a stand-in that is
    // never allocated, equally shared; take the stamp OCaml takes here.
    if let Some(ctx) = ctx_ref {
        let _fail = ctx.create_ident("fallthrough");
    }
    match (act1.normalized_key(b), act2.normalized_key(b)) {
        (Some(raw1), Some(raw2)) => raw1 == raw2,
        _ => false,
    }
}

// ============================================================================
// up_ok — Check if swapping two clauses is safe
// ============================================================================

/// Check if a clause `(ps, act_p)` can be moved past all clauses in `l`.
/// Safe to swap if either the actions are equivalent or the patterns
/// are incompatible.
///
/// Equivalent to OCaml's `up_ok`.
fn up_ok<'p, B: RawLambdaBuilder>(
    b: &B,
    pa: &PatArena<'p>,
    ctx_ref: Option<&TypeContext>,
    ps: &[&'p Pattern],
    act_p: &MatchAction,
    l: &[Clause<'p>],
) -> bool {
    up_ok_iter(b, pa, ctx_ref, ps, act_p, l.iter())
}

fn up_ok_iter<'p: 'a, 'a, B: RawLambdaBuilder>(
    b: &B,
    pa: &PatArena<'p>,
    ctx_ref: Option<&TypeContext>,
    ps: &[&'p Pattern],
    act_p: &MatchAction,
    mut clauses: impl Iterator<Item = &'a Clause<'p>>,
) -> bool {
    clauses.all(|(qs, act_q)| up_ok_action(b, ctx_ref, act_p, act_q) || !may_compats(pa, ps, qs))
}

// ============================================================================
// simplify_or — Simplify or-patterns
// ============================================================================

/// Simplify an or-pattern:
/// - `_|p` becomes `_` (propagated as Var)
/// - Records are expanded to all fields
/// - Aliases are preserved around or-patterns
///
/// Equivalent to OCaml's `simplify_or`.
fn simplify_or<'p>(
    ctx_ref: Option<&TypeContext>,
    pa: &'p PatArena<'p>,
    p: &'p Pattern,
) -> &'p Pattern {
    /// `Err` is OCaml's `Var` exception: the pattern matches anything.
    fn simpl_rec<'x>(
        pa: &PatArena<'x>,
        ctx_ref: Option<&TypeContext>,
        p: &'x Pattern,
    ) -> Result<Cow<'x, Pattern>, Cow<'x, Pattern>> {
        match &p.pat_desc {
            PatternDesc::Tpat_any | PatternDesc::Tpat_var(..) => Err(Cow::Borrowed(p)),
            PatternDesc::Tpat_alias(q, id, s) => {
                let alias = |q: Cow<'x, Pattern>| {
                    Cow::Owned(with_desc(
                        p,
                        PatternDesc::Tpat_alias(pa.push(q.into_owned()), *id, s.clone()),
                    ))
                };
                match simpl_rec(pa, ctx_ref, pa.pat(*q)) {
                    Ok(q) => Ok(alias(q)),
                    Err(q) => Err(alias(q)),
                }
            }
            PatternDesc::Tpat_or(p1, p2, o) => {
                let q1 = simpl_rec(pa, ctx_ref, pa.pat(*p1))?; // propagates Var if p1 is variable
                let or = |q2: Cow<'x, Pattern>| {
                    Cow::Owned(with_desc(
                        p,
                        PatternDesc::Tpat_or(pa.intern(q1.clone()), pa.intern(q2), o.clone()),
                    ))
                };
                match simpl_rec(pa, ctx_ref, pa.pat(*p2)) {
                    Ok(q2) => Ok(or(q2)),
                    Err(q2) => Err(or(q2)),
                }
            }
            PatternDesc::Tpat_record(lbls, closed, rest) => {
                let all_lbls = all_record_args(pa, ctx_ref, lbls);
                Ok(Cow::Owned(with_desc(
                    p,
                    PatternDesc::Tpat_record(all_lbls, *closed, rest.clone()),
                )))
            }
            _ => Ok(Cow::Borrowed(p)),
        }
    }

    match simpl_rec(pa, ctx_ref, p) {
        Ok(p) | Err(p) => alloc_cow(pa, p),
    }
}

// ============================================================================
// simplify_cases — Simplify all cases (swap optimization)
// ============================================================================

/// Bind a variable to an argument in an action.
/// Equivalent to OCaml's `Lambda.bind Alias id arg action`.
fn bind<B: RawLambdaBuilder>(
    b: &B,
    kind: LetKind,
    id: &Ident,
    arg: &RawLambda,
    action: RawLambda,
) -> RawLambda {
    match b.as_var(*arg) {
        Some(v) if v.same(id) => action,
        _ => b.let_(kind, *id, *arg, action),
    }
}

/// Simplify the first column of a match:
/// - Variables are replaced with omega and bound in the action
/// - Aliases are removed and replaced by bindings in actions
/// - Records are expanded to all fields
/// - Or-patterns are simplified (but not removed)
///
/// Equivalent to OCaml's `simplify_cases`.
fn simplify_cases<'p, B: RawLambdaBuilder>(
    ctx_ref: Option<&TypeContext>,
    pa: &'p PatArena<'p>,
    arena: &LocArena<'_, B>,
    args: &[(RawLambda, LetKind)],
    cls: Vec<Clause<'p>>,
) -> Vec<Clause<'p>> {
    assert!(!args.is_empty(), "simplify_cases: empty args");

    let (ref arg, _) = args[0];

    fn simplify<'p, B: RawLambdaBuilder>(
        ctx_ref: Option<&TypeContext>,
        pa: &'p PatArena<'p>,
        arena: &LocArena<'_, B>,
        arg: &RawLambda,
        cls: Vec<Clause<'p>>,
    ) -> Vec<Clause<'p>> {
        let b = arena.b;
        let mut pending: VecDeque<Clause<'p>> = cls.into();
        let mut result = Vec::with_capacity(pending.len());
        while let Some((pats, action)) = pending.pop_front() {
            assert!(!pats.is_empty(), "simplify_cases: empty pattern row");

            let pat: &'p Pattern = pats[0];
            let patl = &pats[1..];

            match &pat.pat_desc {
                PatternDesc::Tpat_var(id, _) => {
                    let new_action = action.bind(b, LetKind::Alias, *id, *arg);
                    let mut row = vec![omega()];
                    row.extend(patl.iter().cloned());
                    result.push((row, new_action));
                }
                PatternDesc::Tpat_any => {
                    result.push((pats, action));
                }
                PatternDesc::Tpat_alias(p, id, _) => {
                    let new_action = action.bind(b, LetKind::Alias, *id, *arg);
                    let mut new_pats = vec![pa.pat(*p)];
                    new_pats.extend(patl.iter().cloned());
                    // OCaml `compiler/ml/matching.ml:565-566` immediately
                    // reprocesses the peeled alias row by recursing on
                    // `(p :: patl, bind Alias id arg action) :: rem`. A deque
                    // keeps that same order without shifting the whole Rust Vec.
                    pending.push_front((new_pats, new_action));
                }
                PatternDesc::Tpat_record(lbls, _, rest) if lbls.is_empty() => {
                    let action = match rest {
                        Some(rest) => action.bind(
                            b,
                            LetKind::Strict,
                            rest.rest_ident,
                            b.prim(
                                Primitive::PrecordRest(rest.excluded_runtime_labels.clone()),
                                &[*arg], // matching.ml:585/596 `bind_record_rest pat.pat_loc`.
                                arena.lam_loc(pat.pat_loc),
                            ),
                        ),
                        None => action,
                    };
                    let mut row = vec![omega()];
                    row.extend(patl.iter().cloned());
                    result.push((row, action));
                }
                PatternDesc::Tpat_record(lbls, closed, rest) => {
                    let action = match rest {
                        Some(rest) => action.bind(
                            b,
                            LetKind::Strict,
                            rest.rest_ident,
                            b.prim(
                                Primitive::PrecordRest(rest.excluded_runtime_labels.clone()),
                                &[*arg], // matching.ml:585/596 `bind_record_rest pat.pat_loc`.
                                arena.lam_loc(pat.pat_loc),
                            ),
                        ),
                        None => action,
                    };
                    let all_lbls = all_record_args(pa, ctx_ref, lbls);
                    let full_pat: &'p Pattern = pa.alloc(with_desc(
                        pat,
                        PatternDesc::Tpat_record(all_lbls, *closed, None),
                    ));
                    let mut row = vec![full_pat];
                    row.extend(patl.iter().cloned());
                    result.push((row, action));
                }
                PatternDesc::Tpat_or(..) => {
                    let pat_simple = simplify_or(ctx_ref, pa, pat);
                    match &pat_simple.pat_desc {
                        PatternDesc::Tpat_or(..) => {
                            let mut row = vec![pat_simple];
                            row.extend(patl.iter().cloned());
                            result.push((row, action));
                        }
                        _ => {
                            // OCaml `compiler/ml/matching.ml:577-580` also
                            // reprocesses an or-pattern that simplified away.
                            let mut new_pats = vec![pat_simple];
                            new_pats.extend(patl.iter().cloned());
                            pending.push_front((new_pats, action));
                        }
                    }
                }
                _ => {
                    result.push((pats, action));
                }
            }
        }
        result
    }

    simplify(ctx_ref, pa, arena, arg, cls)
}

// ============================================================================
// what_is_cases — Determine what kind of patterns are in cases
// ============================================================================

/// Determine what kind of pattern the first non-wildcard case has.
/// Returns the first non-wildcard pattern, or omega if all are wildcards.
///
/// Equivalent to OCaml's `what_is_cases`.
fn what_is_cases<'p>(cases: &[Clause<'p>]) -> &'p Pattern {
    match cases.split_first() {
        None => omega(),
        Some(((pats, _), rem)) => {
            assert!(!pats.is_empty(), "what_is_cases: empty pattern row");
            match &pats[0].pat_desc {
                PatternDesc::Tpat_any => what_is_cases(rem),
                PatternDesc::Tpat_var(..)
                | PatternDesc::Tpat_or(..)
                | PatternDesc::Tpat_alias(..) => {
                    panic!("what_is_cases: applies to simplified matchings only")
                }
                _ => pats[0],
            }
        }
    }
}

// ============================================================================
// as_matrix, cons_default, default_compat — Default environment helpers
// ============================================================================
// Ported from OCaml's matching.ml lines 588-607.

/// Convert cases to a pattern matrix (taking the minimal rows under le_pats).
/// Equivalent to OCaml's `as_matrix`.
fn as_matrix<'p>(pa: &PatArena<'p>, cases: &[Clause<'p>]) -> Matrix<'p> {
    get_mins_indices(
        |a: &Clause<'p>, b: &Clause<'p>| le_pats(pa, &a.0, &b.0),
        cases,
    )
    .iter()
    .map(|&i| cases[i].0.clone())
    .collect()
}

/// Prepend a matrix entry to the default environment, skipping empty matrices.
/// Equivalent to OCaml's `cons_default`.
pub fn cons_default<'p>(
    matrix: Matrix<'p>,
    raise_num: i32,
    default: DefaultEnv<'p>,
) -> DefaultEnv<'p> {
    if matrix.is_empty() {
        default
    } else {
        let mut result = vec![(matrix, raise_num)];
        result.extend(default);
        result
    }
}

/// Filter a default environment for entries compatible with pattern p.
/// For each entry (pss, i), keep only rows whose first pattern is compatible
/// with p, and drop the first column.
///
/// Equivalent to OCaml's `default_compat`.
pub fn default_compat<'p>(pa: &PatArena<'p>, p: &Pattern, def: &DefaultEnv<'p>) -> DefaultEnv<'p> {
    def.iter().rev().fold(Vec::new(), |r, (pss, i)| {
        let qss: Vec<Vec<&'p Pattern>> = pss
            .iter()
            .filter_map(|qs| match qs.split_first() {
                Some((q, rem)) if may_compat(pa, p, q) => Some(rem.to_vec()),
                _ => None,
            })
            .collect();
        if qss.is_empty() {
            r
        } else {
            let mut result = vec![(qss, *i)];
            result.extend(r);
            result
        }
    })
}

// ============================================================================
// Layer 3: Default environments and or-patterns
// Ported from OCaml's matching.ml lines 612-657
// ============================================================================

/// Type alias for the set of identifiers (equivalent to OCaml's IdentSet).
type IdentSet = BTreeSet<Ident>;

/// Recursively extract all variables bound in a pattern.
/// Equivalent to OCaml's `extract_vars`.
pub fn extract_vars(pa: &PatArena<'_>, r: IdentSet, p: &Pattern) -> IdentSet {
    match &p.pat_desc {
        PatternDesc::Tpat_var(id, _) => {
            let mut r = r;
            r.insert(*id);
            r
        }
        PatternDesc::Tpat_alias(p, id, _) => {
            let mut r = r;
            r.insert(*id);
            extract_vars(pa, r, pa.pat(*p))
        }
        PatternDesc::Tpat_tuple(pats) => pa.pats(*pats).fold(r, |r, p| extract_vars(pa, r, p)),
        PatternDesc::Tpat_record(lpats, _, rest) => {
            let mut r = r;
            if let Some(rest) = rest {
                r.insert(rest.rest_ident);
            }
            lpats
                .iter()
                .fold(r, |r, (_, _, p, _)| extract_vars(pa, r, pa.pat(*p)))
        }
        PatternDesc::Tpat_construct(_, _, pats) => {
            pa.pats(*pats).fold(r, |r, p| extract_vars(pa, r, p))
        }
        PatternDesc::Tpat_dict(entries) => entries
            .iter()
            .fold(r, |r, entry| extract_vars(pa, r, pa.pat(entry.tdp_pattern))),
        PatternDesc::Tpat_array(pats) => pa.pats(*pats).fold(r, |r, p| extract_vars(pa, r, p)),
        PatternDesc::Tpat_variant(_, Some(p), _) => extract_vars(pa, r, pa.pat(*p)),
        PatternDesc::Tpat_or(p, _, _) => extract_vars(pa, r, pa.pat(*p)),
        PatternDesc::Tpat_constant(_)
        | PatternDesc::Tpat_interval(..)
        | PatternDesc::Tpat_any
        | PatternDesc::Tpat_variant(_, None, _) => r,
    }
}

/// Boolean form of `extract_vars IdentSet.empty p |> IdentSet.is_empty`.
/// Mirrors OCaml's `extract_vars` branches (compiler/ml/matching.ml:613-624)
/// but avoids allocating an IdentSet for the hot no-variable test in
/// `insert_or_append` (compiler/ml/matching.ml:738-740).
fn pattern_binds_vars(pa: &PatArena<'_>, p: &Pattern) -> bool {
    match &p.pat_desc {
        PatternDesc::Tpat_var(_, _) | PatternDesc::Tpat_alias(_, _, _) => true,
        PatternDesc::Tpat_tuple(pats)
        | PatternDesc::Tpat_construct(_, _, pats)
        | PatternDesc::Tpat_array(pats) => pa.pats(*pats).any(|p| pattern_binds_vars(pa, p)),
        PatternDesc::Tpat_record(lpats, _, rest) => {
            rest.is_some()
                || lpats
                    .iter()
                    .any(|(_, _, pat, _)| pattern_binds_vars(pa, pa.pat(*pat)))
        }
        PatternDesc::Tpat_dict(entries) => entries
            .iter()
            .any(|entry| pattern_binds_vars(pa, pa.pat(entry.tdp_pattern))),
        PatternDesc::Tpat_variant(_, Some(p), _) | PatternDesc::Tpat_or(p, _, _) => {
            pattern_binds_vars(pa, pa.pat(*p))
        }
        PatternDesc::Tpat_constant(_)
        | PatternDesc::Tpat_interval(..)
        | PatternDesc::Tpat_any
        | PatternDesc::Tpat_variant(_, None, _) => false,
    }
}

/// Error raised when an or-pattern cannot be flattened because
/// an aliased variable needs a binding but no argument is available.
/// Equivalent to OCaml's `Cannot_flatten` exception.
#[derive(Debug)]
pub struct CannotFlatten;

/// Create an alpha-renaming environment mapping each id in `ids` to either
/// the match argument (if id is in aliases) or a fresh ident with the same name.
/// Raises `CannotFlatten` if an alias id has no argument.
/// Equivalent to OCaml's `mk_alpha_env`.
pub fn mk_alpha_env(
    ctx_ref: Option<&TypeContext>,
    arg: &Option<Ident>,
    aliases: &[Ident],
    ids: &IdentSet,
) -> Result<Vec<(Ident, Ident)>, CannotFlatten> {
    ids.iter()
        .map(|id| {
            let new_id = if aliases.contains(id) {
                match arg {
                    Some(v) => *v,
                    None => return Err(CannotFlatten),
                }
            } else {
                ctx_ref
                    .map(|ctx_ref| ctx_ref.create_ident(id.name()))
                    .unwrap_or_else(|| Ident::create_local(id.name()))
            };
            Ok((*id, new_id))
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Alpha-renaming for patterns (local copy, mirrors Typedtree.alpha_pat)
// ---------------------------------------------------------------------------

/// Look up an identifier in the alpha-renaming environment.
fn alpha_pat_id<'a>(env: &'a [(Ident, Ident)], id: &Ident) -> Option<&'a Ident> {
    env.iter()
        .find_map(|(from, to)| if from.same(id) { Some(to) } else { None })
}

fn alpha_pat_list(pa: &PatArena<'_>, env: &[(Ident, Ident)], items: TPatList) -> TPatList {
    let renamed: Vec<TPatIdx> = pa
        .pats(items)
        .map(|item| pa.push(alpha_pat(pa, env, item)))
        .collect();
    pa.push_list(renamed)
}

/// Apply an alpha-renaming environment to a pattern.
/// Equivalent to OCaml's `Typedtree.alpha_pat`.
fn alpha_pat(pa: &PatArena<'_>, env: &[(Ident, Ident)], pat: &Pattern) -> Pattern {
    match &pat.pat_desc {
        PatternDesc::Tpat_var(id, name) => {
            let pat_desc = alpha_pat_id(env, id)
                .map(|new_id| PatternDesc::Tpat_var(*new_id, name.clone()))
                .unwrap_or(PatternDesc::Tpat_any);
            with_desc(pat, pat_desc)
        }
        PatternDesc::Tpat_alias(inner, id, name) => {
            let new_inner = alpha_pat(pa, env, pa.pat(*inner));
            if let Some(new_id) = alpha_pat_id(env, id) {
                with_desc(
                    pat,
                    PatternDesc::Tpat_alias(pa.push(new_inner), *new_id, name.clone()),
                )
            } else {
                new_inner
            }
        }
        PatternDesc::Tpat_tuple(items) => with_desc(
            pat,
            PatternDesc::Tpat_tuple(alpha_pat_list(pa, env, *items)),
        ),
        PatternDesc::Tpat_construct(lid, cstr, args) => with_desc(
            pat,
            PatternDesc::Tpat_construct(*lid, cstr.clone(), alpha_pat_list(pa, env, *args)),
        ),
        PatternDesc::Tpat_variant(label, arg, row) => with_desc(
            pat,
            PatternDesc::Tpat_variant(
                label.clone(),
                arg.map(|arg| pa.push(alpha_pat(pa, env, pa.pat(arg)))),
                *row,
            ),
        ),
        PatternDesc::Tpat_record(fields, closed, rest) => with_desc(
            pat,
            PatternDesc::Tpat_record(
                fields
                    .iter()
                    .map(|(lid, lbl, field_pat, opt)| {
                        (
                            *lid,
                            lbl.clone(),
                            pa.push(alpha_pat(pa, env, pa.pat(*field_pat))),
                            *opt,
                        )
                    })
                    .collect(),
                *closed,
                rest.as_ref().map(|rest| {
                    let mut rest = rest.clone();
                    if let Some(new_id) = alpha_pat_id(env, &rest.rest_ident) {
                        rest.rest_ident = *new_id;
                    }
                    rest
                }),
            ),
        ),
        PatternDesc::Tpat_array(items) => with_desc(
            pat,
            PatternDesc::Tpat_array(alpha_pat_list(pa, env, *items)),
        ),
        PatternDesc::Tpat_or(left, right, row) => with_desc(
            pat,
            PatternDesc::Tpat_or(
                pa.push(alpha_pat(pa, env, pa.pat(*left))),
                pa.push(alpha_pat(pa, env, pa.pat(*right))),
                row.clone(),
            ),
        ),
        _ => pat.clone(),
    }
}

impl<'p, B: RawLambdaBuilder> Split<'p, '_, B> {
    /// Expand an or-pattern into separate cases with alpha-renamed variables.
    ///
    /// `patl`: surrounding pattern context
    /// `mk_action`: closure that builds an action given a list of fresh idents
    /// `rem`: accumulator of already-expanded cases
    /// `vars`: set of variables that need alpha-renaming
    /// `aliases`: accumulated alias identifiers from Tpat_alias wrappers
    /// `pat`: the pattern being exploded
    ///
    /// Equivalent to OCaml's `explode_or_pat`; the optional binding for alias
    /// variables is the split's `argo`.
    fn explode_or_pat<F>(
        &self,
        patl: &[&'p Pattern],
        mk_action: &F,
        rem: Vec<Clause<'p>>,
        vars: &IdentSet,
        aliases: &[Ident],
        pat: &'p Pattern,
    ) -> Result<Vec<Clause<'p>>, CannotFlatten>
    where
        F: Fn(&[Ident]) -> RawLambda,
    {
        // OCaml conses each expanded row onto `rem`. Keep the list reversed so a
        // cons is a push: prepending to a vector made an or-pattern of many
        // alternatives (an expanded character range) quadratic.
        let mut acc = rem;
        acc.reverse();
        self.explode_or_pat_rev(patl, mk_action, &mut acc, vars, aliases, pat)?;
        acc.reverse();
        Ok(acc)
    }

    /// `explode_or_pat` onto `acc`, which holds the result list reversed.
    fn explode_or_pat_rev<F>(
        &self,
        patl: &[&'p Pattern],
        mk_action: &F,
        acc: &mut Vec<Clause<'p>>,
        vars: &IdentSet,
        aliases: &[Ident],
        pat: &'p Pattern,
    ) -> Result<(), CannotFlatten>
    where
        F: Fn(&[Ident]) -> RawLambda,
    {
        let Split {
            ctx_ref,
            pa,
            argo: arg,
            ..
        } = *self;
        match &pat.pat_desc {
            PatternDesc::Tpat_or(p1, p2, _) => {
                self.explode_or_pat_rev(patl, mk_action, acc, vars, aliases, pa.pat(*p2))?;
                self.explode_or_pat_rev(patl, mk_action, acc, vars, aliases, pa.pat(*p1))
            }
            PatternDesc::Tpat_alias(p, id, _) => {
                let mut new_aliases = vec![*id];
                new_aliases.extend_from_slice(aliases);
                self.explode_or_pat_rev(patl, mk_action, acc, vars, &new_aliases, pa.pat(*p))
            }
            PatternDesc::Tpat_var(x, _) => {
                let mut x_aliases = vec![*x];
                x_aliases.extend_from_slice(aliases);
                let env = mk_alpha_env(ctx_ref, arg, &x_aliases, vars)?;
                let new_ids: Vec<Ident> = env.iter().map(|(_, id)| *id).collect();
                let mut row = vec![omega()];
                row.extend_from_slice(patl);
                acc.push((row, MatchAction::new(mk_action(&new_ids))));
                Ok(())
            }
            _ => {
                let env = mk_alpha_env(ctx_ref, arg, aliases, vars)?;
                let new_ids: Vec<Ident> = env.iter().map(|(_, id)| *id).collect();
                let mut row: Vec<&'p Pattern> = vec![pa.alloc(alpha_pat(pa, &env, pat))];
                row.extend_from_slice(patl);
                acc.push((row, MatchAction::new(mk_action(&new_ids))));
                Ok(())
            }
        }
    }
}

/// Compute the free variables of a pattern matching's actions.
/// Equivalent to OCaml's `pm_free_variables`.
pub fn pm_free_variables<'p, B: RawLambdaBuilder>(b: &B, pm: &PatternMatching<'p>) -> IdentSet {
    let a = b.get();
    // OCaml uses IdentSet.union (free_variables act) r folded right over cases.
    pm.cases
        .iter()
        .rev()
        .fold(BTreeSet::new(), |mut r, (_, act)| {
            let fv = act.free_variables(&*a);
            r.extend(fv);
            r
        })
}

/// Free variables of a RawLambda expression (`Lambda.free_variables`).
fn raw_lambda_free_variables(a: &impl RawLambdaRead, lam: RawLambda) -> IdentSet {
    let mut fv = IdentSet::new();
    crate::raw_lambda::collect_free_variables(a, lam, &mut fv);
    fv
}

// ============================================================================
// Layer 4: Grouping and splitting
// ============================================================================
// Ported from OCaml's matching.ml lines 659-1090.
// This layer implements the pattern grouping predicates, or-pattern
// operations, and the split/precompile functions that prepare pattern
// matchings for compilation.

// ============================================================================
// Group predicates (lines 659-700)
// ============================================================================

/// Extract the constructor description from a construct pattern.
/// Equivalent to OCaml's `pat_as_constr`.
fn pat_as_constr(p: &Pattern) -> &crate::types::ConstructorDescription {
    match &p.pat_desc {
        PatternDesc::Tpat_construct(_, cstr, _) => cstr,
        _ => crate::misc::fatal_error("Matching.pat_as_constr"),
    }
}

/// Group predicate for constant patterns.
/// Equivalent to OCaml's `group_constant`.
fn group_constant(p: &Pattern) -> bool {
    matches!(
        &p.pat_desc,
        PatternDesc::Tpat_constant(_) | PatternDesc::Tpat_interval(..)
    )
}

/// Group predicate for constructor patterns.
/// Equivalent to OCaml's `group_constructor`.
fn group_constructor(p: &Pattern) -> bool {
    matches!(&p.pat_desc, PatternDesc::Tpat_construct(_, _, _))
}

/// Group predicate for variant patterns.
/// Equivalent to OCaml's `group_variant`.
fn group_variant(p: &Pattern) -> bool {
    matches!(&p.pat_desc, PatternDesc::Tpat_variant(_, _, _))
}

/// Group predicate for variable/wildcard patterns.
/// Equivalent to OCaml's `group_var`.
fn group_var(p: &Pattern) -> bool {
    matches!(&p.pat_desc, PatternDesc::Tpat_any)
}

/// Group predicate for tuple patterns (including wildcard).
/// Equivalent to OCaml's `group_tuple`.
fn group_tuple(p: &Pattern) -> bool {
    matches!(
        &p.pat_desc,
        PatternDesc::Tpat_tuple(_) | PatternDesc::Tpat_any
    )
}

/// Group predicate for record patterns (including wildcard).
/// Equivalent to OCaml's `group_record`.
fn group_record(p: &Pattern) -> bool {
    matches!(
        &p.pat_desc,
        PatternDesc::Tpat_record(_, _, _) | PatternDesc::Tpat_any
    )
}

/// Group predicate for array patterns.
/// Equivalent to OCaml's `group_array`.
fn group_array(p: &Pattern) -> bool {
    matches!(&p.pat_desc, PatternDesc::Tpat_array(_))
}

/// Get the appropriate group predicate for a pattern.
/// Equivalent to OCaml's `get_group`.
fn get_group(p: &Pattern) -> fn(&Pattern) -> bool {
    match &p.pat_desc {
        PatternDesc::Tpat_any => group_var,
        PatternDesc::Tpat_constant(_) | PatternDesc::Tpat_interval(..) => group_constant,
        PatternDesc::Tpat_construct(_, _, _) => group_constructor,
        PatternDesc::Tpat_tuple(_) => group_tuple,
        PatternDesc::Tpat_record(_, _, _) => group_record,
        PatternDesc::Tpat_array(_) => group_array,
        PatternDesc::Tpat_variant(_, _, _) => group_variant,
        _ => crate::misc::fatal_error("Matching.get_group"),
    }
}

/// Check if a pattern is an or-pattern.
/// Equivalent to OCaml's `is_or`.
/// `is_or p ps`: a row starting with an or-pattern. An interval is
/// precompiled like an or-pattern of its values when the rest of its row
/// tests something: that is then compiled once, in a handler, instead of
/// once per piece of the column.
fn is_or(p: &Pattern, ps: &[&Pattern]) -> bool {
    match &p.pat_desc {
        PatternDesc::Tpat_or(_, _, _) => true,
        PatternDesc::Tpat_interval(..) => ps.iter().any(|q| {
            !matches!(
                q.pat_desc,
                PatternDesc::Tpat_any | PatternDesc::Tpat_var(..)
            )
        }),
        _ => false,
    }
}

// ============================================================================
// Or-pattern operations (lines 708-773)
// ============================================================================

/// Condition (a) for appending to the Or matrix: p and q are incompatible.
/// Equivalent to OCaml's `conda`.
fn conda(pa: &PatArena<'_>, p: &Pattern, q: &Pattern) -> bool {
    !may_compat(pa, p, q)
}

/// Condition (b) for appending: action is not guarded and qs <= ps.
/// Equivalent to OCaml's `condb`.
fn condb<'p>(pa: &PatArena<'p>, act: &MatchAction, ps: &[&Pattern], qs: &[&Pattern]) -> bool {
    !act.is_guarded() && le_pats(pa, qs, ps)
}

fn or_ok_iter<'p: 'a, 'a>(
    pa: &PatArena<'p>,
    p: &'p Pattern,
    ps: &[&'p Pattern],
    mut clauses: impl Iterator<Item = &'a Clause<'p>>,
) -> bool {
    clauses.all(|(row, act)| match row.split_first() {
        Some((q, qs)) if is_or(q, qs) => conda(pa, p, q) || condb(pa, act, ps, qs),
        _ => true,
    })
}

/// Check if two patterns are equivalent (each le the other).
/// Equivalent to OCaml's `equiv_pat`.
fn equiv_pat(pa: &PatArena<'_>, p: &Pattern, q: &Pattern) -> bool {
    le_pat(pa, p, q) && le_pat(pa, q, p)
}

/// Get equivalent or-patterns from the front of the list.
/// Returns (equivalent_clauses, remaining_clauses).
/// Equivalent to OCaml's `get_equiv`.
fn get_equiv<'p>(
    pa: &PatArena<'p>,
    p: &'p Pattern,
    l: &[Clause<'p>],
) -> (Vec<Clause<'p>>, Vec<Clause<'p>>) {
    // OCaml compiler/ml/matching.ml:727-732 recurses through the equivalent
    // prefix and conses each row while returning, preserving source order.
    // Count the prefix first so Rust clones each row once without repeated
    // front insertion.
    let prefix_len = l
        .iter()
        .take_while(|cl| match cl.0.first() {
            Some(q) => equiv_pat(pa, p, q),
            None => false,
        })
        .count();

    if prefix_len == 0 {
        return (Vec::new(), l.to_vec());
    }

    (l[..prefix_len].to_vec(), l[prefix_len..].to_vec())
}

/// Insert or append a pattern in the Or matrix.
/// Returns (updated_ors, updated_no).
/// Equivalent to OCaml's `insert_or_append`.
fn insert_or_append<'p>(
    pa: &PatArena<'p>,
    p: &'p Pattern,
    ps: &[&'p Pattern],
    act: &MatchAction,
    mut ors: VecDeque<Clause<'p>>,
    mut no: VecDeque<Clause<'p>>,
) -> (VecDeque<Clause<'p>>, VecDeque<Clause<'p>>) {
    fn clause_from_head<'p>(p: &'p Pattern, ps: &[&'p Pattern], act: &MatchAction) -> Clause<'p> {
        let mut new_p_row = vec![p];
        new_p_row.extend_from_slice(ps);
        (new_p_row, act.clone())
    }

    let ors_len = ors.len();

    for index in 0..ors_len {
        let cl = ors
            .get(index)
            .expect("insert_or_append: index within deque length");
        let (q_head, qs) = match cl.0.split_first() {
            Some((q, qs)) => (q, qs),
            None => panic!("insert_or_append: empty pattern row"),
        };
        let act_q = &cl.1;

        if is_or(q_head, qs) && may_compat(pa, p, q_head) {
            if !pattern_binds_vars(pa, p)
                && !pattern_binds_vars(pa, q_head)
                && equiv_pat(pa, p, q_head) {
                // OCaml compiler/ml/matching.ml:743-756 checks the tail after
                // the equivalent-prefix group. Keep that as deque iteration so
                // we do not force VecDeque::make_contiguous on a push_front-built
                // accumulator.
                let equivalent_tail_len = ors
                    .iter()
                    .skip(index + 1)
                    .take_while(|cl| match cl.0.first() {
                        Some(q) => equiv_pat(pa, q_head, q),
                        None => false,
                    })
                    .count();
                let not_e_start = index + 1 + equivalent_tail_len;
                if or_ok_iter(pa, p, ps, ors.iter().skip(not_e_start))
                    && ors
                        .iter()
                        .take(index)
                        .all(|seen_cl| match seen_cl.0.first() {
                            Some(q) => !may_compat(pa, p, q),
                            None => panic!("insert_or_append: empty seen row"),
                        })
                {
                    // OCaml compiler/ml/matching.ml:733-756 builds `seen` as a
                    // shared list prefix. Keep the Rust equivalent as a deque
                    // prefix and only clone rows when reconstructing the result.
                    let mut result = VecDeque::with_capacity(ors_len + 1);
                    result.extend(ors.iter().take(index).cloned());
                    result.push_back(clause_from_head(p, ps, act));
                    result.push_back(cl.clone());
                    result.extend(ors.iter().skip(index + 1).cloned());
                    return (result, no);
                }

                no.push_front(clause_from_head(p, ps, act));
                return (ors, no);
            }

            if !condb(pa, act_q, ps, qs) {
                no.push_front(clause_from_head(p, ps, act));
                return (ors, no);
            }
        }

        // OCaml's recursive `attempt (cl :: seen) rem` shares `cl`
        // (compiler/ml/matching.ml:733-734,768). The current index is the
        // logical `seen` prefix for subsequent iterations.
    }

    // OCaml compiler/ml/matching.ml:768-773 returns `((p :: ps, act) :: ors, no)`.
    ors.push_front(clause_from_head(p, ps, act));
    (ors, no)
}

// ============================================================================
// Rebuild functions (lines 777-793)
// ============================================================================

/// Reconstruct a matrix from a half-compiled pattern matching.
/// Equivalent to OCaml's `rebuild_matrix`.
fn rebuild_matrix<'p>(pa: &PatArena<'p>, pmh: &PmHalfCompiled<'p>) -> Matrix<'p> {
    match pmh {
        PmHalfCompiled::Pm(pm) => as_matrix(pa, &pm.cases),
        PmHalfCompiled::PmOr(por) => por.or_matrix.clone(),
        PmHalfCompiled::PmVar(x) => add_omega_column(&rebuild_matrix(pa, &x.inside)),
    }
}

/// Reconstruct default information from half-compiled pm list.
/// Equivalent to OCaml's `rebuild_default`.
fn rebuild_default<'p>(
    pa: &PatArena<'p>,
    nexts: &[(i32, PmHalfCompiled<'p>)],
    def: DefaultEnv<'p>,
) -> DefaultEnv<'p> {
    match nexts.split_first() {
        None => def,
        Some(((e, pmh), rem)) => {
            let mut result = vec![(add_omega_column(&rebuild_matrix(pa, pmh)), *e)];
            result.extend(rebuild_default(pa, rem, def));
            result
        }
    }
}

/// Wrap nexts with PmVar nodes.
/// Equivalent to OCaml's `rebuild_nexts`.
fn rebuild_nexts<'p>(
    arg: &RawLambda,
    nexts: Vec<(i32, PmHalfCompiled<'p>)>,
    k: Vec<(i32, PmHalfCompiled<'p>)>,
) -> Vec<(i32, PmHalfCompiled<'p>)> {
    // OCaml compiler/ml/matching.ml:789-792 uses `List.fold_right` to keep
    // `nexts` order and prepend each wrapped item before `k`.
    let mut result = Vec::with_capacity(nexts.len() + k.len());
    result.extend(nexts.into_iter().map(|(e, pm)| {
        (
            e,
            PmHalfCompiled::PmVar(PmVarCompiled {
                inside: Box::new(pm),
                var_arg: *arg,
            }),
        )
    }));
    result.extend(k);
    result
}

// ============================================================================
// Split functions (lines 814-1090)
// ============================================================================


/// What the split functions share: the compilation's context and exit
/// counter, and the arguments of the `split_or` call being split.
struct Split<'p, 'a, B: RawLambdaBuilder> {
    ctx_ref: Option<&'a TypeContext>,
    pa: &'p PatArena<'p>,
    arena: &'a LocArena<'a, B>,
    /// The variable the first argument is bound to, if any.
    argo: &'a Option<Ident>,
    args: &'a MatchArgs,
    next_raise: &'a mut i32,
}

impl<'p, B: RawLambdaBuilder> Split<'p, '_, B> {
    /// Split a matching, directed first by or-patterns, then by tests/variable transitions.
    /// Equivalent to OCaml's `split_or`.
    fn split_or(
        &mut self,
        cls: Vec<Clause<'p>>,
        def: DefaultEnv<'p>,
    ) -> (PmHalfCompiledInfo<'p>, Vec<(i32, PmHalfCompiled<'p>)>) {
        let Split {
            ctx_ref,
            pa,
            arena,
            args,
            ..
        } = *self;
        let cls = simplify_cases(ctx_ref, pa, arena, args, cls);

        self.do_split_or(cls.into(), &def)
    }

    /// Inner do_split for split_or.
    fn do_split_or(
        &mut self,
        mut rest: VecDeque<Clause<'p>>,
        def: &DefaultEnv<'p>,
    ) -> (PmHalfCompiledInfo<'p>, Vec<(i32, PmHalfCompiled<'p>)>) {
        let Split {
            ctx_ref, pa, arena, ..
        } = *self;
        let b = arena.b;
        let mut before = VecDeque::new();
        let mut ors = VecDeque::new();
        let mut no = VecDeque::new();
        // OCaml `compiler/ml/matching.ml:817-828` is tail-recursive. Rust does not
        // guarantee tail-call elimination, and large generated matches build very
        // deep `do_split_or` stacks. Keep the exact branch order but run it as an
        // explicit loop.
        loop {
            let Some(cl) = rest.pop_front() else {
                let before = rev_deque_to_vec(before);
                let ors = rev_deque_to_vec(ors);
                let no = rev_deque_to_vec(no);
                return self.cons_next_or(before, ors, no, def);
            };

            let push_to_before_or_ors = {
                let (p, ps) = cl.0.split_first().expect("split_or: empty pattern row");
                let act = &cl.1;
                if up_ok_iter(b, pa, ctx_ref, cl.0.as_slice(), act, no.iter()) {
                    if is_or(p, ps) {
                        let (new_ors, new_no) = insert_or_append(pa, p, ps, act, ors, no);
                        ors = new_ors;
                        no = new_no;
                        continue;
                    } else if up_ok_iter(b, pa, ctx_ref, cl.0.as_slice(), act, ors.iter()) {
                        // OCaml `do_split` moves the current row into `before` with
                        // `(cl :: before)` (compiler/ml/matching.ml:820-826).
                        Some(true)
                    } else if or_ok_iter(pa, p, ps, ors.iter()) {
                        Some(false)
                    } else {
                        None
                    }
                } else {
                    None
                }
            };

            match push_to_before_or_ors {
                Some(true) => before.push_front(cl),
                Some(false) => ors.push_front(cl),
                None => no.push_front(cl),
            }
        }
    }

    /// cons_next helper for split_or.
    fn cons_next_or(
        &mut self,
        yes: Vec<Clause<'p>>,
        yesor: Vec<Clause<'p>>,
        no: Vec<Clause<'p>>,
        def: &DefaultEnv<'p>,
    ) -> (PmHalfCompiledInfo<'p>, Vec<(i32, PmHalfCompiled<'p>)>) {
        if no.is_empty() {
            self.precompile_or(yes, yesor, def.clone(), Vec::new())
        } else {
            let (info, nexts) = self.do_split_or(no.into(), def);
            let idef = bump_raise_count(self.next_raise);
            let PmHalfCompiledInfo {
                me: next,
                matrix,
                top_default,
            } = info;
            let new_def = cons_default(matrix, idef, top_default);
            let mut new_nexts = vec![(idef, next)];
            new_nexts.extend(nexts);
            self.precompile_or(yes, yesor, new_def, new_nexts)
        }
    }

    /// Ultra-naive splitting, close to semantics, used for extension constructors.
    /// Equivalent to OCaml's `split_naive`.
    fn split_naive(
        &mut self,
        cls: &[Clause<'p>],
        def: DefaultEnv<'p>,
        k: Vec<(i32, PmHalfCompiled<'p>)>,
    ) -> (PmHalfCompiledInfo<'p>, Vec<(i32, PmHalfCompiled<'p>)>) {
        match cls.split_first() {
            None => panic!("split_naive: empty cases"),
            Some((cl, rem)) => match cl.0.first() {
                Some(p) if group_constructor(p) => {
                    self.split_exc(pat_as_constr(p), vec![cl.clone()], rem, def, k)
                }
                Some(_) => self.split_noexc(vec![cl.clone()], rem, def, k),
                None => panic!("split_naive: empty pattern row"),
            },
        }
    }

    /// Split on extension constructors (naive).
    // `split_exc`, `split_noexc`, `split_ex` and `split_noex` (matching.ml
    // split_or/split_constr) cons rows onto `yes`/`no` and `List.rev` them when
    // done. Rust pushes instead, so the vectors are already in source order; a
    // shifting `insert(0, ..)` per row made a column of many distinct constants
    // (an expanded character range) quadratic.
    fn split_exc(
        &mut self,
        cstr0: &crate::types::ConstructorDescription,
        yes: Vec<Clause<'p>>,
        rest: &[Clause<'p>],
        def: DefaultEnv<'p>,
        k: Vec<(i32, PmHalfCompiled<'p>)>,
    ) -> (PmHalfCompiledInfo<'p>, Vec<(i32, PmHalfCompiled<'p>)>) {
        let Split { pa, args, .. } = *self;
        match rest.split_first() {
            None => (
                PmHalfCompiledInfo {
                    me: PmHalfCompiled::Pm(PatternMatching {
                        cases: yes.clone(),
                        args: args.clone(),
                        default: def.clone(),
                    }),
                    matrix: as_matrix(pa, &yes),
                    top_default: def,
                },
                k,
            ),
            Some((cl, rem)) => match cl.0.first() {
                Some(p) if group_constructor(p) => {
                    let cstr = pat_as_constr(p);
                    if same_constructor(cstr, cstr0) {
                        let mut new_yes = yes;
                        new_yes.push(cl.clone());
                        self.split_exc(cstr0, new_yes, rem, def, k)
                    } else {
                        let (info, nexts) =
                            self.split_exc(cstr, vec![cl.clone()], rem, def.clone(), k);
                        let idef = bump_raise_count(self.next_raise);
                        let PmHalfCompiledInfo {
                            me: next,
                            matrix,
                            top_default,
                        } = info;
                        let new_def = cons_default(matrix, idef, top_default);
                        let mut new_nexts = vec![(idef, next)];
                        new_nexts.extend(nexts);
                        (
                            PmHalfCompiledInfo {
                                me: PmHalfCompiled::Pm(PatternMatching {
                                    cases: yes.clone(),
                                    args: args.clone(),
                                    default: new_def.clone(),
                                }),
                                matrix: as_matrix(pa, &yes),
                                top_default: new_def,
                            },
                            new_nexts,
                        )
                    }
                }
                Some(_) => {
                    let (info, nexts) = self.split_noexc(vec![cl.clone()], rem, def.clone(), k);
                    let idef = bump_raise_count(self.next_raise);
                    let PmHalfCompiledInfo {
                        me: next,
                        matrix,
                        top_default,
                    } = info;
                    let new_def = cons_default(matrix, idef, top_default);
                    let mut new_nexts = vec![(idef, next)];
                    new_nexts.extend(nexts);
                    (
                        PmHalfCompiledInfo {
                            me: PmHalfCompiled::Pm(PatternMatching {
                                cases: yes.clone(),
                                args: args.clone(),
                                default: new_def.clone(),
                            }),
                            matrix: as_matrix(pa, &yes),
                            top_default: new_def,
                        },
                        new_nexts,
                    )
                }
                None => panic!("split_exc: empty pattern row"),
            },
        }
    }

    /// Split on non-extension constructors (naive).
    fn split_noexc(
        &mut self,
        yes: Vec<Clause<'p>>,
        rest: &[Clause<'p>],
        def: DefaultEnv<'p>,
        k: Vec<(i32, PmHalfCompiled<'p>)>,
    ) -> (PmHalfCompiledInfo<'p>, Vec<(i32, PmHalfCompiled<'p>)>) {
        match rest.split_first() {
            None => self.precompile_var(yes, def, k),
            Some((cl, rem)) => match cl.0.first() {
                Some(p) if group_constructor(p) => {
                    let (info, nexts) =
                        self.split_exc(pat_as_constr(p), vec![cl.clone()], rem, def.clone(), k);
                    let idef = bump_raise_count(self.next_raise);
                    let PmHalfCompiledInfo {
                        me: next,
                        matrix,
                        top_default,
                    } = info;
                    self.precompile_var(yes, cons_default(matrix, idef, top_default), {
                        let mut new_nexts = vec![(idef, next)];
                        new_nexts.extend(nexts);
                        new_nexts
                    })
                }
                Some(_) => {
                    let mut new_yes = yes;
                    new_yes.push(cl.clone());
                    self.split_noexc(new_yes, rem, def, k)
                }
                None => panic!("split_noexc: empty pattern row"),
            },
        }
    }

    /// Split on constructors using group predicates.
    /// Equivalent to OCaml's `split_constr`.
    fn split_constr(
        &mut self,
        cls: &[Clause<'p>],
        def: DefaultEnv<'p>,
        k: Vec<(i32, PmHalfCompiled<'p>)>,
    ) -> (PmHalfCompiledInfo<'p>, Vec<(i32, PmHalfCompiled<'p>)>) {
        let ex_pat = what_is_cases(cls);
        match &ex_pat.pat_desc {
            PatternDesc::Tpat_any => self.precompile_var(cls.to_vec(), def, k),
            PatternDesc::Tpat_construct(_, cstr, _)
                if matches!(&cstr.cstr_kind, crate::types::ConstructorKind::Extension(_)) =>
            {
                self.split_naive(cls, def, k)
            }
            _ => {
                let group = get_group(ex_pat);
                match cls.split_first() {
                    Some((cl, rem)) => match cl.0.first() {
                        Some(p) if group(p) => {
                            self.split_ex(group, vec![cl.clone()], Vec::new(), rem, def, k)
                        }
                        _ => self.split_noex(group, vec![cl.clone()], Vec::new(), rem, def, k),
                    },
                    None => panic!("split_constr: empty cases"),
                }
            }
        }
    }

    /// split_ex: raise constructor rows up.
    fn split_ex(
        &mut self,
        group: fn(&'p Pattern) -> bool,
        yes: Vec<Clause<'p>>,
        no: Vec<Clause<'p>>,
        rest: &[Clause<'p>],
        def: DefaultEnv<'p>,
        k: Vec<(i32, PmHalfCompiled<'p>)>,
    ) -> (PmHalfCompiledInfo<'p>, Vec<(i32, PmHalfCompiled<'p>)>) {
        let Split {
            ctx_ref,
            pa,
            arena,
            args,
            ..
        } = *self;
        let b = arena.b;
        match rest.split_first() {
            None => match no.split_first() {
                None => (
                    PmHalfCompiledInfo {
                        me: PmHalfCompiled::Pm(PatternMatching {
                            cases: yes.clone(),
                            args: args.clone(),
                            default: def.clone(),
                        }),
                        matrix: as_matrix(pa, &yes),
                        top_default: def,
                    },
                    k,
                ),
                Some((no_cl, no_rem)) => {
                    if yes.is_empty() {
                        // Could not succeed in raising up a constr matching up
                        self.split_noex(group, vec![no_cl.clone()], Vec::new(), no_rem, def, k)
                    } else {
                        let (info, nexts) = self.split_noex(
                            group,
                            vec![no_cl.clone()],
                            Vec::new(),
                            no_rem,
                            def.clone(),
                            k,
                        );
                        let idef = bump_raise_count(self.next_raise);
                        let PmHalfCompiledInfo {
                            me: next,
                            matrix,
                            top_default,
                        } = info;
                        let new_def = cons_default(matrix, idef, top_default);
                        let mut new_nexts = vec![(idef, next)];
                        new_nexts.extend(nexts);
                        (
                            PmHalfCompiledInfo {
                                me: PmHalfCompiled::Pm(PatternMatching {
                                    cases: yes.clone(),
                                    args: args.clone(),
                                    default: new_def.clone(),
                                }),
                                matrix: as_matrix(pa, &yes),
                                top_default: new_def,
                            },
                            new_nexts,
                        )
                    }
                }
            },
            Some((cl, rem)) => match cl.0.first() {
                Some(p) if group(p) && up_ok(b, pa, ctx_ref, &cl.0, &cl.1, &no) => {
                    let mut new_yes = yes;
                    new_yes.push(cl.clone());
                    self.split_ex(group, new_yes, no, rem, def, k)
                }
                _ => {
                    let mut new_no = no;
                    new_no.push(cl.clone());
                    self.split_ex(group, yes, new_no, rem, def, k)
                }
            },
        }
    }

    /// split_noex: raise non-constructor rows up.
    fn split_noex(
        &mut self,
        group: fn(&'p Pattern) -> bool,
        yes: Vec<Clause<'p>>,
        no: Vec<Clause<'p>>,
        rest: &[Clause<'p>],
        def: DefaultEnv<'p>,
        k: Vec<(i32, PmHalfCompiled<'p>)>,
    ) -> (PmHalfCompiledInfo<'p>, Vec<(i32, PmHalfCompiled<'p>)>) {
        let Split {
            ctx_ref, pa, arena, ..
        } = *self;
        let b = arena.b;
        match rest.split_first() {
            None => match no.split_first() {
                None => self.precompile_var(yes, def, k),
                Some((no_cl, no_rem)) => {
                    let (info, nexts) = self.split_ex(
                        group,
                        vec![no_cl.clone()],
                        Vec::new(),
                        no_rem,
                        def.clone(),
                        k,
                    );
                    let idef = bump_raise_count(self.next_raise);
                    let PmHalfCompiledInfo {
                        me: next,
                        matrix,
                        top_default,
                    } = info;
                    self.precompile_var(yes, cons_default(matrix, idef, top_default), {
                        let mut new_nexts = vec![(idef, next)];
                        new_nexts.extend(nexts);
                        new_nexts
                    })
                }
            },
            Some((_cl, _rem)) if rest.len() == 1 => {
                // Check for the special case: last row is all variables and yes is non-empty
                let cl = &rest[0];
                if cl.0.iter().all(|p| group_var(p)) && !yes.is_empty() {
                    // This enables an extra division in some frequent cases:
                    // last row is made of variables only
                    let mut new_no = no;
                    new_no.push(cl.clone());
                    self.split_noex(group, yes, new_no, &[], def, k)
                } else {
                    // Fall through to normal case
                    let cl = &rest[0];
                    match cl.0.first() {
                        Some(p) if !group(p) && up_ok(b, pa, ctx_ref, &cl.0, &cl.1, &no) => {
                            let mut new_yes = yes;
                            new_yes.push(cl.clone());
                            self.split_noex(group, new_yes, no, &[], def, k)
                        }
                        _ => {
                            let mut new_no = no;
                            new_no.push(cl.clone());
                            self.split_noex(group, yes, new_no, &[], def, k)
                        }
                    }
                }
            }
            Some((cl, rem)) => match cl.0.first() {
                Some(p) if !group(p) && up_ok(b, pa, ctx_ref, &cl.0, &cl.1, &no) => {
                    let mut new_yes = yes;
                    new_yes.push(cl.clone());
                    self.split_noex(group, new_yes, no, rem, def, k)
                }
                _ => {
                    let mut new_no = no;
                    new_no.push(cl.clone());
                    self.split_noex(group, yes, new_no, rem, def, k)
                }
            },
        }
    }

    /// Precompile variable patterns: if the match argument is a variable,
    /// split further on the second column.
    /// Equivalent to OCaml's `precompile_var`.
    fn precompile_var(
        &mut self,
        cls: Vec<Clause<'p>>,
        def: DefaultEnv<'p>,
        k: Vec<(i32, PmHalfCompiled<'p>)>,
    ) -> (PmHalfCompiledInfo<'p>, Vec<(i32, PmHalfCompiled<'p>)>) {
        let Split {
            pa, arena, args, ..
        } = *self;
        let b = arena.b;
        match args.as_slice() {
            [] => panic!("precompile_var: empty args"),
            [_, arg_rest @ ..] if !arg_rest.is_empty() => {
                // Check if second arg is Lvar
                match b.as_var(arg_rest[0].0) {
                    Some(v) => {
                        if cls.len() == 1 {
                            // as split as it can
                            dont_precompile_var(pa, args, cls, def, k)
                        } else {
                            // Precompile: strip first pattern from each case
                            let var_cls: Vec<Clause<'p>> = cls
                                .iter()
                                .map(|(ps, act)| match ps.split_first() {
                                    Some((_, rest)) => (rest.to_vec(), act.clone()),
                                    None => panic!("precompile_var: empty pattern row"),
                                })
                                .collect();
                            let var_def = make_default(
                                pa,
                                &|_p: &'p Pattern, rem: &[&'p Pattern]| Ok(rem.to_vec()),
                                &def,
                            );
                            let av = arg_rest[0].0;
                            let arg_tail = args.tail(1);
                            let argo = Some(v);
                            let (first_info, nexts) = Split {
                                ctx_ref: self.ctx_ref,
                                pa,
                                arena,
                                argo: &argo,
                                args: &arg_tail,
                                next_raise: &mut *self.next_raise,
                            }
                            .split_or(var_cls, var_def);

                            // Compute top information
                            if nexts.is_empty() {
                                // If you need
                                dont_precompile_var(pa, args, cls, def, k)
                            } else {
                                let rfirst = PmHalfCompiledInfo {
                                    me: PmHalfCompiled::PmVar(PmVarCompiled {
                                        inside: Box::new(first_info.me),
                                        var_arg: av,
                                    }),
                                    matrix: add_omega_column(&first_info.matrix),
                                    top_default: rebuild_default(pa, &nexts, def),
                                };
                                let rnexts = rebuild_nexts(&av, nexts, k);
                                (rfirst, rnexts)
                            }
                        }
                    }
                    _ => dont_precompile_var(pa, args, cls, def, k),
                }
            }
            _ => dont_precompile_var(pa, args, cls, def, k),
        }
    }

    /// Precompile or-patterns.
    /// Equivalent to OCaml's `precompile_or`.
    fn precompile_or(
        &mut self,
        cls: Vec<Clause<'p>>,
        ors: Vec<Clause<'p>>,
        def: DefaultEnv<'p>,
        k: Vec<(i32, PmHalfCompiled<'p>)>,
    ) -> (PmHalfCompiledInfo<'p>, Vec<(i32, PmHalfCompiled<'p>)>) {
        let Split { pa, args, .. } = *self;
        if ors.is_empty() {
            return self.split_constr(&cls, def, k);
        }

        // do_cases processes the or-pattern list
        let (end_body, handlers) = self.do_cases_or(&ors, &def);

        let matrix = as_matrix(pa, &[cls.as_slice(), ors.as_slice()].concat());
        let body = PatternMatching {
            cases: [cls, end_body].concat(),
            args: args.clone(),
            default: def.clone(),
        };
        (
            PmHalfCompiledInfo {
                me: PmHalfCompiled::PmOr(PmOrCompiled {
                    body,
                    handlers,
                    or_matrix: matrix.clone(),
                }),
                matrix,
                top_default: def,
            },
            k,
        )
    }

    /// Process or-pattern cases for precompile_or.
    /// Equivalent to the inner `do_cases` in OCaml's `precompile_or`.
    fn do_cases_or(
        &mut self,
        ors: &[Clause<'p>],
        def: &DefaultEnv<'p>,
    ) -> (Vec<Clause<'p>>, Vec<OrHandler<'p>>) {
        let (body, handlers) = self.do_cases_or_deque(ors, def);
        (body.into_iter().collect(), handlers)
    }

    fn do_cases_or_deque(
        &mut self,
        ors: &[Clause<'p>],
        def: &DefaultEnv<'p>,
    ) -> (VecDeque<Clause<'p>>, Vec<OrHandler<'p>>) {
        let Split { pa, args, .. } = *self;
        let b = self.arena.b;
        match ors.split_first() {
            None => (VecDeque::new(), Vec::new()),
            Some((cl, rem)) => {
                match cl.0.first() {
                    Some(orp) if is_or(orp, &cl.0[1..]) => {
                        let patl = &cl.0[1..];
                        let action = &cl.1;

                        let (others, rem) = get_equiv(pa, orp, rem);

                        let orpm_cases = {
                            let mut cases = vec![(patl.to_vec(), action.clone())];
                            cases.extend(others.iter().map(|(ps, act)| match ps.split_first() {
                                Some((_, rest)) => (rest.to_vec(), act.clone()),
                                None => panic!("do_cases_or: empty pattern row"),
                            }));
                            cases
                        };
                        let orpm_args = match args.split_first() {
                            Some(_) => args.tail(1),
                            None => panic!("do_cases_or: empty args"),
                        };
                        let orpm = PatternMatching {
                            cases: orpm_cases,
                            args: orpm_args,
                            default: default_compat(pa, orp, def),
                        };

                        let vars: Vec<Ident> = {
                            let orp_vars = extract_vars(pa, BTreeSet::new(), orp);
                            let pm_fv = pm_free_variables(b, &orpm);
                            orp_vars.intersection(&pm_fv).cloned().collect()
                        };

                        let or_num = bump_raise_count(self.next_raise);
                        let new_patl = omegas(patl.len());

                        let mk_new_action = |vs: &[Ident]| -> RawLambda {
                            let vars: Vec<RawLambda> = vs.iter().map(|v| b.var(*v)).collect();
                            b.static_raise(or_num, &vars)
                        };

                        let (body, handlers) = self.do_cases_or_deque(&rem, def);

                        let exploded = self.explode_or_pat(
                            &new_patl,
                            &mk_new_action,
                            body.into_iter().collect(),
                            &vars.iter().cloned().collect(),
                            &[],
                            orp,
                        );

                        let new_body = match exploded {
                            Ok(b) => b,
                            Err(_) => panic!("do_cases_or: Cannot_flatten"),
                        };

                        let mat = vec![vec![*orp]];
                        let mut new_handlers = vec![(mat, or_num, vars, orpm)];
                        new_handlers.extend(handlers);
                        (new_body.into(), new_handlers)
                    }
                    _ => {
                        // OCaml compiler/ml/matching.ml:846-1090 conses ordinary
                        // rows before the recursively processed tail. Use
                        // `push_front` for the same list shape without shifting a
                        // Rust Vec on every row.
                        let (mut new_ord, new_to_catch) = self.do_cases_or_deque(rem, def);
                        new_ord.push_front(cl.clone());
                        (new_ord, new_to_catch)
                    }
                }
            }
        }
    }
}

/// Don't precompile: just wrap the cases in a PatternMatching.
/// Equivalent to OCaml's `dont_precompile_var`.
fn dont_precompile_var<'p>(
    pa: &PatArena<'p>,
    args: &MatchArgs,
    cls: Vec<Clause<'p>>,
    def: DefaultEnv<'p>,
    k: Vec<(i32, PmHalfCompiled<'p>)>,
) -> (PmHalfCompiledInfo<'p>, Vec<(i32, PmHalfCompiled<'p>)>) {
    (
        PmHalfCompiledInfo {
            me: PmHalfCompiled::Pm(PatternMatching {
                cases: cls.clone(),
                args: args.clone(),
                default: def.clone(),
            }),
            matrix: as_matrix(pa, &cls),
            top_default: def,
        },
        k,
    )
}

/// Top-level split_precompile.
/// Equivalent to OCaml's `split_precompile`.
pub fn split_precompile<'p, B: RawLambdaBuilder>(
    ctx_ref: Option<&TypeContext>,
    pa: &'p PatArena<'p>,
    arena: &LocArena<'_, B>,
    argo: &Option<Ident>,
    pm: &PatternMatching<'p>,
    next_raise: &mut i32,
) -> (PmHalfCompiled<'p>, Vec<(i32, PmHalfCompiled<'p>)>) {
    let (info, nexts) = Split {
        ctx_ref,
        pa,
        arena,
        argo,
        args: &pm.args,
        next_raise,
    }
    .split_or(pm.cases.clone(), pm.default.clone());
    (info.me, nexts)
}

/// OCaml compiler/ml/matching.ml:814-846 accumulates rows with `::` and
/// restores source order with `List.rev`; callers use `VecDeque::push_front`
/// for the same asymptotic behavior.
fn rev_deque_to_vec<T>(v: VecDeque<T>) -> Vec<T> {
    let mut v: Vec<T> = v.into_iter().collect();
    v.reverse();
    v
}

// ============================================================================
// Layer 5: General divide functions (lines 1094-1131)
// ============================================================================

/// A cell: a pattern matching with its context list and pattern.
/// Equivalent to OCaml's `cell`.
struct MatchCell<'p> {
    pm: PatternMatching<'p>,
    ctx: Vec<Ctx<'p>>,
    pat: &'p Pattern,
}

/// Add a case to the appropriate cell in a division, creating a new cell if needed.
/// Equivalent to OCaml's `add`.
fn add<'p, K>(
    make_matching_fun: impl FnOnce(&MatchArgs) -> MatchCell<'p>,
    mut division: Vec<(K, MatchCell<'p>)>,
    eq_key: impl Fn(&K, &K) -> bool,
    key: K,
    patl_action: Clause<'p>,
    args: &MatchArgs,
) -> Vec<(K, MatchCell<'p>)> {
    // Try to find existing entry with matching key
    if let Some(pos) = division.iter().position(|(k, _)| eq_key(&key, k)) {
        division[pos].1.pm.cases.insert(0, patl_action);
        division
    } else {
        let mut cell = make_matching_fun(args);
        cell.pm.cases = vec![patl_action];
        division.insert(0, (key, cell));
        division
    }
}

/// Divide a pattern matching by the first pattern column, grouping by key.
/// OCaml's `compiler/ml/matching.ml:1110-1120` recurses to the tail, then
/// conses the current case with `add` (`compiler/ml/matching.ml:1100-1108`).
/// Iterating from the tail, pushing, and reversing once preserves the same
/// group/case order without Rust `Vec::insert(0, ...)` shifting every element.
fn divide<'p, K>(
    make: impl Fn(&'p Pattern, &DefaultEnv<'p>, &[Ctx<'p>], &MatchArgs) -> MatchCell<'p>,
    eq_key: impl Fn(&K, &K) -> bool,
    get_key: impl Fn(&'p Pattern) -> K,
    get_args: impl Fn(&'p Pattern, &[&'p Pattern]) -> Vec<&'p Pattern>,
    ctx: &[Ctx<'p>],
    pm: &PatternMatching<'p>,
) -> Vec<(K, MatchCell<'p>)> {
    let mut division: Vec<(K, MatchCell<'p>)> = Vec::new();

    for (patl, action) in pm.cases.iter().rev() {
        let Some((p, rest_patl)) = patl.split_first() else {
            division.clear();
            continue;
        };

        let key = get_key(p);
        let patl_action = (get_args(p, rest_patl), action.clone());

        if let Some(pos) = division.iter().position(|(k, _)| eq_key(&key, k)) {
            division[pos].1.pm.cases.push(patl_action);
        } else {
            let mut cell = make(p, &pm.default, ctx, &pm.args);
            cell.pm.cases.push(patl_action);
            division.push((key, cell));
        }
    }

    division.reverse();
    for (_, cell) in &mut division {
        cell.pm.cases.reverse();
    }
    division
}

/// Divide a pattern matching into a single cell (no grouping by key).
/// OCaml's `compiler/ml/matching.ml:1122-1130` uses the same tail-recursive
/// consing shape as `divide`; use push + one suffix reverse to keep that order
/// without shifting the whole Rust vector per case.
fn divide_line<'p>(
    make_ctx: impl Fn(&[Ctx<'p>]) -> Vec<Ctx<'p>>,
    make: impl Fn(&DefaultEnv<'p>, &MatchArgs) -> PatternMatching<'p>,
    get_args: impl Fn(&'p Pattern, &[&'p Pattern]) -> Vec<&'p Pattern>,
    pat: &'p Pattern,
    ctx: &[Ctx<'p>],
    pm: &PatternMatching<'p>,
) -> MatchCell<'p> {
    let mut divided = make(&pm.default, &pm.args);
    let mut base_case_count = divided.cases.len();

    for (patl, action) in pm.cases.iter().rev() {
        match patl.split_first() {
            Some((p, rest_patl)) => {
                divided.cases.push((get_args(p, rest_patl), action.clone()));
            }
            None => {
                divided = make(&pm.default, &pm.args);
                base_case_count = divided.cases.len();
            }
        }
    }

    divided.cases[base_case_count..].reverse();

    MatchCell {
        pm: divided,
        ctx: make_ctx(ctx),
        pat,
    }
}

// ============================================================================
// Layer 6: Per-type pattern matchers (lines 1148-1516)
// ============================================================================

// --- Constants (lines 1148-1177) ---

/// The key of a constant column is a range of constants: `(c, c)` for a
/// constant `c`, and the bounds of a piece of a split interval column.
type ConstantKey = (Constant, Constant);

/// `int_key key`: the bounds of an int or char key.
fn int_key((c1, c2): &ConstantKey) -> Option<(i64, i64)> {
    Some((
        crate::types::parmatch::int_of_constant(c1)?,
        crate::types::parmatch::int_of_constant(c2)?,
    ))
}

/// Matcher for constant patterns.
/// Equivalent to OCaml's `matcher_const`.
fn matcher_const<'p>(
    pa: &PatArena<'p>,
    key: &ConstantKey,
    p: &'p Pattern,
    rem: &[&'p Pattern],
) -> Result<Vec<&'p Pattern>, MatchError> {
    match &p.pat_desc {
        PatternDesc::Tpat_or(p1, p2, _) => match matcher_const(pa, key, pa.pat(*p1), rem) {
            Ok(r) => Ok(r),
            Err(MatchError::NoMatch) => matcher_const(pa, key, pa.pat(*p2), rem),
            Err(e) => Err(e),
        },
        PatternDesc::Tpat_constant(_) | PatternDesc::Tpat_interval(..)
            if int_range(p).is_some() =>
        {
            match (int_key(key), int_range(p)) {
                (Some((lo, hi)), Some((a, b))) => {
                    if a <= lo && hi <= b {
                        Ok(rem.to_vec())
                    } else if b < lo || hi < a {
                        Err(MatchError::NoMatch)
                    } else {
                        crate::misc::fatal_error("Matching.matcher_const: range across a piece")
                    }
                }
                _ => Err(MatchError::NoMatch),
            }
        }
        PatternDesc::Tpat_constant(c)
            if const_compare(c, &key.0) == std::cmp::Ordering::Equal
                && const_compare(c, &key.1) == std::cmp::Ordering::Equal =>
        {
            Ok(rem.to_vec())
        }
        PatternDesc::Tpat_any => Ok(rem.to_vec()),
        _ => Err(MatchError::NoMatch),
    }
}

/// Get the key (a range of constants) from a constant or interval pattern.
/// Equivalent to OCaml's `get_key_constant`.
fn get_key_constant(caller: &str, p: &Pattern) -> ConstantKey {
    match &p.pat_desc {
        PatternDesc::Tpat_constant(cst) => (cst.clone(), cst.clone()),
        PatternDesc::Tpat_interval(lo, hi) => (lo.constant(), hi.constant()),
        _ => {
            panic!("get_key_constant ({caller}): not a constant pattern");
        }
    }
}

/// Get the arguments from a constant pattern (none — just the remainder).
/// Equivalent to OCaml's `get_args_constant`.
fn get_args_constant<'p>(_p: &'p Pattern, rem: &[&'p Pattern]) -> Vec<&'p Pattern> {
    rem.to_vec()
}

/// Make a constant matching cell.
/// Equivalent to OCaml's `make_constant_matching`.
fn make_constant_matching<'p>(
    pa: &'p PatArena<'p>,
    p: &'p Pattern,
    def: &DefaultEnv<'p>,
    ctx: &[Ctx<'p>],
    args: &MatchArgs,
) -> MatchCell<'p> {
    match args.split_first() {
        None => crate::misc::fatal_error("Matching.make_constant_matching"),
        Some(_) => {
            let key = get_key_constant("make", p);
            let def = make_default(pa, &|p2, rem| matcher_const(pa, &key, p2, rem), def);
            let ctx = filter_ctx(None, pa, p, ctx);
            MatchCell {
                pm: PatternMatching {
                    cases: Vec::new(),
                    args: args.tail(1),
                    default: def,
                },
                ctx,
                pat: normalize_pat(pa, p),
            }
        }
    }
}

/// `column_int_ranges m`: the int and char ranges of the first column of
/// the cases and of the default matrices, when one of them is an interval.
fn column_int_ranges(pa: &PatArena<'_>, m: &PatternMatching<'_>) -> Option<Vec<(i64, i64)>> {
    fn heads(
        pa: &PatArena<'_>,
        p: &Pattern,
        has_interval: &mut bool,
        acc: &mut Vec<(i64, i64)>,
    ) {
        match &p.pat_desc {
            PatternDesc::Tpat_alias(p, _, _) => heads(pa, pa.pat(*p), has_interval, acc),
            PatternDesc::Tpat_or(p1, p2, _) => {
                heads(pa, pa.pat(*p2), has_interval, acc);
                heads(pa, pa.pat(*p1), has_interval, acc);
            }
            desc => {
                if matches!(desc, PatternDesc::Tpat_interval(..)) {
                    *has_interval = true;
                }
                if let Some(r) = int_range(p) {
                    acc.push(r);
                }
            }
        }
    }
    let mut has_interval = false;
    let mut ranges = Vec::new();
    let rows = m
        .cases
        .iter()
        .map(|(ps, _)| ps)
        .chain(m.default.iter().flat_map(|(pss, _)| pss.iter()));
    for row in rows {
        if let Some(p) = row.first() {
            heads(pa, p, &mut has_interval, &mut ranges);
        }
    }
    has_interval.then_some(ranges)
}

/// `divide_constant_ranges ranges ctx m`: divides a column with intervals
/// into pieces cut at the bounds of all its ranges, so that each range
/// covers whole pieces. A case goes to every piece its head covers; the
/// number of pieces depends on the number of patterns, not on the width of
/// the ranges.
fn divide_constant_ranges<'p>(
    pa: &'p PatArena<'p>,
    ranges: &[(i64, i64)],
    ctx: &[Ctx<'p>],
    m: &PatternMatching<'p>,
) -> Vec<(ConstantKey, MatchCell<'p>)> {
    let mut cuts: Vec<i64> = ranges.iter().flat_map(|&(lo, hi)| [lo, hi + 1]).collect();
    cuts.sort_unstable();
    cuts.dedup();
    let n = cuts.len() - 1;
    let index = |x: i64| {
        cuts.binary_search(&x)
            .expect("Matching.divide_constant_ranges: a bound is a cut")
    };
    let mut rows: Vec<Vec<Clause<'p>>> = vec![Vec::new(); n];
    let mut heads: Vec<Option<&'p Pattern>> = vec![None; n];
    for (patl, action) in &m.cases {
        let Some((p, patl)) = patl.split_first() else {
            crate::misc::fatal_error("Matching.divide_constant_ranges");
        };
        match int_range(p) {
            Some((lo, hi)) => {
                for i in index(lo)..index(hi + 1) {
                    rows[i].push((get_args_constant(p, patl), action.clone()));
                    heads[i].get_or_insert(*p);
                }
            }
            None => {
                get_key_constant("divide", p);
            }
        }
    }
    let mut cells = Vec::new();
    for i in (0..n).rev() {
        if let Some(head) = heads[i] {
            let p = pa.alloc(make_int_range(head, cuts[i], cuts[i + 1] - 1));
            let mut cell = make_constant_matching(pa, p, &m.default, ctx, &m.args);
            cell.pm.cases = std::mem::take(&mut rows[i]);
            cells.push((get_key_constant("divide", p), cell));
        }
    }
    cells.reverse();
    cells
}

/// Divide a pattern matching by constant values.
/// Equivalent to OCaml's `divide_constant`.
fn divide_constant<'p>(
    pa: &'p PatArena<'p>,
    ctx: &[Ctx<'p>],
    m: &PatternMatching<'p>,
) -> Vec<(ConstantKey, MatchCell<'p>)> {
    match column_int_ranges(pa, m) {
        Some(ranges) => divide_constant_ranges(pa, &ranges, ctx, m),
        None => divide(
            |p, d, c, a| make_constant_matching(pa, p, d, c, a),
            |(c, _), (d, _)| const_compare(c, d) == std::cmp::Ordering::Equal,
            |p| get_key_constant("divide", p),
            get_args_constant,
            ctx,
            m,
        ),
    }
}

// --- Constructors (lines 1180-1289) ---

/// Make field access arguments for a constructor: the fields at `positions`
/// of `arg`, then `argl`.
/// Equivalent to OCaml's `make_field_args`, whose `first_pos` and `last_pos`
/// are the bounds of `positions`.
fn make_field_args<B: RawLambdaBuilder>(
    b: &B,
    fld_info: FieldDbgInfo,
    loc: LamLoc,
    binding_kind: LetKind,
    arg: &RawLambda,
    positions: std::ops::RangeInclusive<i32>,
    argl: &MatchArgs,
) -> MatchArgs {
    MatchArgs::new(
        positions
            .map(|pos| {
                (
                    b.prim(Primitive::Pfield(pos, fld_info), &[*arg], loc),
                    binding_kind,
                )
            })
            .chain(argl.iter().copied()),
    )
}

/// Get the declared constructor from a constructor pattern.
/// Equivalent to OCaml's `get_key_constr`.
fn get_key_constr(p: &Pattern) -> std::sync::Arc<ConstructorDescription> {
    match &p.pat_desc {
        PatternDesc::Tpat_construct(_, cstr, _) => cstr.clone(),
        _ => panic!("get_key_constr: not a construct pattern"),
    }
}

/// Get the arguments from a constructor pattern.
/// Equivalent to OCaml's `get_args_constr`.
fn get_args_constr<'p>(pa: &PatArena<'p>, p: &'p Pattern, rem: &[&'p Pattern]) -> Vec<&'p Pattern> {
    match &p.pat_desc {
        PatternDesc::Tpat_construct(_, _, args) => prepend_row(pa.pats(*args), rem),
        _ => panic!("get_args_constr: not a construct pattern"),
    }
}

/// Matcher for constructor patterns.
/// Equivalent to OCaml's `matcher_constr`.
///
/// NB: matcher_constr applies to default matrices.
/// In that context, matching by constructors of extensible
/// types degrades to arity checking, due to potential rebinding.
/// This comparison is performed by Types.may_equal_constr.
fn matcher_constr<'p>(
    pa: &'p PatArena<'p>,
    cstr: &ConstructorDescription,
    p: &'p Pattern,
    rem: &[&'p Pattern],
) -> Result<Vec<&'p Pattern>, MatchError> {
    match cstr.cstr_arity {
        0 => matcher_constr_arity0(pa, cstr, p, rem),
        1 => matcher_constr_arity1(pa, cstr, p, rem),
        _ => matcher_constr_arity_n(pa, cstr, p, rem),
    }
}

/// Matcher for 0-arity constructor.
fn matcher_constr_arity0<'p>(
    pa: &PatArena<'p>,
    cstr: &ConstructorDescription,
    q: &'p Pattern,
    rem: &[&'p Pattern],
) -> Result<Vec<&'p Pattern>, MatchError> {
    match &q.pat_desc {
        PatternDesc::Tpat_or(p1, p2, _) => {
            match matcher_constr_arity0(pa, cstr, pa.pat(*p1), rem) {
                Ok(r) => Ok(r),
                Err(MatchError::NoMatch) => matcher_constr_arity0(pa, cstr, pa.pat(*p2), rem),
                Err(e) => Err(e),
            }
        }
        PatternDesc::Tpat_construct(_, cstr2, args)
            if args.is_empty() && may_equal_constr(cstr, cstr2) =>
        {
            Ok(rem.to_vec())
        }
        PatternDesc::Tpat_any => Ok(rem.to_vec()),
        _ => Err(MatchError::NoMatch),
    }
}

/// Matcher for 1-arity constructor.
fn matcher_constr_arity1<'p>(
    pa: &'p PatArena<'p>,
    cstr: &ConstructorDescription,
    q: &'p Pattern,
    rem: &[&'p Pattern],
) -> Result<Vec<&'p Pattern>, MatchError> {
    match &q.pat_desc {
        PatternDesc::Tpat_or(p1, p2, _) => {
            let r1 = matcher_constr_arity1(pa, cstr, pa.pat(*p1), rem).ok();
            let r2 = matcher_constr_arity1(pa, cstr, pa.pat(*p2), rem).ok();
            match (r1, r2) {
                (None, None) => Err(MatchError::NoMatch),
                (Some(r1), None) => Ok(r1),
                (None, Some(r2)) => Ok(r2),
                (Some(r1), Some(r2)) => match (r1.first(), r2.first()) {
                    (Some(a1), Some(a2)) => {
                        let or_pat = Pattern {
                            pat_desc: PatternDesc::Tpat_or(pa.handle(a1), pa.handle(a2), None),
                            pat_loc: LocIdx::none(),
                            pat_cold: None,
                            pat_type: a1.pat_type,
                            pat_env: a1.pat_env,
                        };
                        let mut result = vec![pa.alloc(or_pat)];
                        result.extend(rem.iter().cloned());
                        Ok(result)
                    }
                    _ => panic!("matcher_constr_arity1: unexpected empty result"),
                },
            }
        }
        PatternDesc::Tpat_construct(_, cstr2, args)
            if args.len() == 1 && may_equal_constr(cstr, cstr2) =>
        {
            let mut result = vec![pa.pat(pa.list(*args)[0])];
            result.extend(rem.iter().cloned());
            Ok(result)
        }
        PatternDesc::Tpat_any => {
            let mut result = vec![omega()];
            result.extend(rem.iter().cloned());
            Ok(result)
        }
        _ => Err(MatchError::NoMatch),
    }
}

/// Matcher for N-arity constructor (N >= 2).
fn matcher_constr_arity_n<'p>(
    pa: &PatArena<'p>,
    cstr: &ConstructorDescription,
    q: &'p Pattern,
    rem: &[&'p Pattern],
) -> Result<Vec<&'p Pattern>, MatchError> {
    match &q.pat_desc {
        PatternDesc::Tpat_or(_, _, _) => Err(MatchError::OrPat),
        PatternDesc::Tpat_construct(_, cstr2, args) if may_equal_constr(cstr, cstr2) => {
            let result = prepend_row(pa.pats(*args), rem);
            Ok(result)
        }
        PatternDesc::Tpat_any => {
            let mut result = omegas(cstr.cstr_arity as usize);
            result.extend(rem.iter().cloned());
            Ok(result)
        }
        _ => Err(MatchError::NoMatch),
    }
}

/// The label's runtime name (OCaml `lbl.lbl_runtime_name`).
fn label_runtime_name_matching(lbl: &LabelDescription) -> crate::name::Name {
    lbl.lbl_runtime_name
}

/// Create field debug info for a record label (equivalent to OCaml's Lambda.fld_record).
fn fld_record(lbl: &LabelDescription) -> FieldDbgInfo {
    FieldDbgInfo::Record {
        name: label_runtime_name_matching(lbl),
    }
}

/// Create field debug info for an inlined record label (equivalent to OCaml's Lambda.fld_record_inline).
fn fld_record_inline(lbl: &LabelDescription) -> FieldDbgInfo {
    FieldDbgInfo::RecordInline {
        name: label_runtime_name_matching(lbl),
    }
}

/// Create field debug info for a record extension label (equivalent to OCaml's Lambda.fld_record_extension).
fn fld_record_extension(lbl: &LabelDescription) -> FieldDbgInfo {
    FieldDbgInfo::RecordExtension {
        name: label_runtime_name_matching(lbl),
    }
}

/// Make a constructor matching cell.
/// Equivalent to OCaml's `make_constr_matching`.
fn make_constr_matching<'p, B: RawLambdaBuilder>(
    ctx_ref: &TypeContext,
    pa: &'p PatArena<'p>,
    arena: &LocArena<'_, B>,
    p: &'p Pattern,
    def: &DefaultEnv<'p>,
    ctx: &[Ctx<'p>],
    args: &MatchArgs,
) -> MatchCell<'p> {
    let b = arena.b;
    match args.split_first() {
        None => crate::misc::fatal_error("Matching.make_constr_matching"),
        Some(((arg, _mut), _)) => {
            let argl = args.tail(1);
            let cstr = pat_as_constr(p);
            // matching.ml: `Datarepr.constructor_payload_is_unboxed cstr`, read
            // from the variant's layout.
            let payload_is_unboxed = constructor_payload_is_unboxed(ctx_ref, cstr);
            let newargs = if cstr.cstr_inlined.is_some()
                || (payload_is_unboxed && !cstr.cstr_args.is_empty())
            {
                MatchArgs::cons((*arg, LetKind::Alias), &argl)
            } else {
                match &cstr.cstr_kind {
                    // OCaml compiler/ml/matching.ml only unwraps option-shaped
                    // ordinary constructors marked with internal.optional.
                    crate::types::ConstructorKind::Ordinary(_)
                        if !cstr.cstr_args.is_empty() && constructor_has_optional_shape(cstr) =>
                    {
                        // The payload is unwrapped unless its type rules out
                        // the object that represents `Some` of undefined. The
                        // patterns can't rule it out: a switch on the payload
                        // gets a case for each constructor, from the default
                        // rows of the match for those the patterns don't name,
                        // and takes its last case without a test, so the
                        // object can reach any arm (compiler/ml/matching.ml
                        // `make_constr_matching`).
                        let from_option = match &p.pat_desc {
                            PatternDesc::Tpat_construct(_, _, args_inner)
                                if args_inner.len() == 1 =>
                            {
                                let pat = pa.pat(pa.list(*args_inner)[0]);
                                // First try env-based check
                                let env_opt = ctx_ref.get_typed_env(pat.pat_env);
                                let can_skip = env_opt
                                    .map(|env| {
                                        type_cannot_contain_undefined(
                                            ctx_ref,
                                            env.as_ref(),
                                            pat.pat_type,
                                        )
                                    })
                                    .unwrap_or_else(|| {
                                        // Fast path: check type descriptor directly
                                        // (works for Ttuple, Tarrow, Tvariant, Tpackage
                                        // which always return true)
                                        type_cannot_contain_undefined_no_env(ctx_ref, pat.pat_type)
                                    });
                                if can_skip {
                                    Primitive::PvalFromOptionNotNest
                                } else {
                                    Primitive::PvalFromOption
                                }
                            }
                            _ => Primitive::PvalFromOption,
                        };
                        MatchArgs::cons(
                            (
                                b.prim(from_option, &[*arg], arena.lam_loc(p.pat_loc)),
                                LetKind::Alias,
                            ),
                            &argl,
                        )
                    }
                    crate::types::ConstructorKind::Ordinary(_) => {
                        let fld_info = if cstr.cstr_name == "::" {
                            FieldDbgInfo::Cons
                        } else {
                            FieldDbgInfo::Variant
                        };
                        make_field_args(
                            b,
                            fld_info,
                            // matching.ml:1309-1313 `make_field_args p.pat_loc`.
                            arena.lam_loc(p.pat_loc),
                            LetKind::Alias,
                            arg,
                            0..=cstr.cstr_arity - 1,
                            &argl,
                        )
                    }
                    crate::types::ConstructorKind::Extension(_) => make_field_args(
                        b,
                        FieldDbgInfo::Extension,
                        arena.lam_loc(p.pat_loc),
                        LetKind::Alias,
                        arg,
                        1..=cstr.cstr_arity,
                        &argl,
                    ),
                }
            };
            let cstr_clone = cstr.clone();
            MatchCell {
                pm: PatternMatching {
                    cases: Vec::new(),
                    args: newargs,
                    default: make_default(
                        pa,
                        &|p2, rem| matcher_constr(pa, &cstr_clone, p2, rem),
                        def,
                    ),
                },
                ctx: filter_ctx(Some(ctx_ref), pa, p, ctx),
                pat: normalize_pat(pa, p),
            }
        }
    }
}

/// Divide a pattern matching by constructor.
/// Equivalent to OCaml's `divide_constructor`.
fn divide_constructor<'p, B: RawLambdaBuilder>(
    ctx_ref: &TypeContext,
    pa: &'p PatArena<'p>,
    arena: &LocArena<'_, B>,
    ctx: &[Ctx<'p>],
    pm: &PatternMatching<'p>,
) -> Vec<(std::sync::Arc<ConstructorDescription>, MatchCell<'p>)> {
    divide(
        |p, def, ctx_inner, args| make_constr_matching(ctx_ref, pa, arena, p, def, ctx_inner, args),
        |left, right| same_constructor(left, right),
        get_key_constr,
        |p, rem| get_args_constr(pa, p, rem),
        ctx,
        pm,
    )
}

// --- Variants (lines 1293-1362) ---

/// Matcher for constant variant patterns.
/// Equivalent to OCaml's `matcher_variant_const`.
fn matcher_variant_const<'p>(
    pa: &PatArena<'p>,
    lab: &str,
    p: &'p Pattern,
    rem: &[&'p Pattern],
) -> Result<Vec<&'p Pattern>, MatchError> {
    match &p.pat_desc {
        PatternDesc::Tpat_or(p1, p2, _) => match matcher_variant_const(pa, lab, pa.pat(*p1), rem) {
            Ok(r) => Ok(r),
            Err(MatchError::NoMatch) => matcher_variant_const(pa, lab, pa.pat(*p2), rem),
            Err(e) => Err(e),
        },
        PatternDesc::Tpat_variant(lab1, _, _) if lab1 == lab => Ok(rem.to_vec()),
        PatternDesc::Tpat_any => Ok(rem.to_vec()),
        _ => Err(MatchError::NoMatch),
    }
}

/// Make a variant matching cell for constant variants.
/// Equivalent to OCaml's `make_variant_matching_constant`.
fn make_variant_matching_constant<'p>(
    pa: &'p PatArena<'p>,
    p: &'p Pattern,
    lab: &str,
    def: &DefaultEnv<'p>,
    ctx: &[Ctx<'p>],
    args: &MatchArgs,
) -> MatchCell<'p> {
    match args.split_first() {
        None => crate::misc::fatal_error("Matching.make_variant_matching_constant"),
        Some(_) => {
            let lab_owned = lab.to_string();
            let def = make_default(
                pa,
                &|p2, rem| matcher_variant_const(pa, &lab_owned, p2, rem),
                def,
            );
            let ctx = filter_ctx(None, pa, p, ctx);
            MatchCell {
                pm: PatternMatching {
                    cases: Vec::new(),
                    args: args.tail(1),
                    default: def,
                },
                ctx,
                pat: normalize_pat(pa, p),
            }
        }
    }
}

/// Matcher for non-constant variant patterns.
/// Equivalent to OCaml's `matcher_variant_nonconst`.
fn matcher_variant_nonconst<'p>(
    pa: &PatArena<'p>,
    lab: &str,
    p: &'p Pattern,
    rem: &[&'p Pattern],
) -> Result<Vec<&'p Pattern>, MatchError> {
    match &p.pat_desc {
        PatternDesc::Tpat_or(_, _, _) => Err(MatchError::OrPat),
        PatternDesc::Tpat_variant(lab1, Some(arg), _) if lab1 == lab => {
            let mut result = vec![pa.pat(*arg)];
            result.extend(rem.iter().cloned());
            Ok(result)
        }
        PatternDesc::Tpat_any => {
            let mut result = vec![omega()];
            result.extend(rem.iter().cloned());
            Ok(result)
        }
        _ => Err(MatchError::NoMatch),
    }
}

/// Make a variant matching cell for non-constant variants.
/// Equivalent to OCaml's `make_variant_matching_nonconst`.
fn make_variant_matching_nonconst<'p, B: RawLambdaBuilder>(
    pa: &'p PatArena<'p>,
    arena: &LocArena<'_, B>,
    p: &'p Pattern,
    lab: &str,
    def: &DefaultEnv<'p>,
    ctx: &[Ctx<'p>],
    args: &MatchArgs,
) -> MatchCell<'p> {
    let b = arena.b;
    match args.split_first() {
        None => crate::misc::fatal_error("Matching.make_variant_matching_nonconst"),
        Some(((arg, _mut), _)) => {
            let argl = args.tail(1);
            let lab_owned = lab.to_string();
            let def = make_default(
                pa,
                &|p2, rem| matcher_variant_nonconst(pa, &lab_owned, p2, rem),
                def,
            );
            let ctx = filter_ctx(None, pa, p, ctx);
            let new_args = MatchArgs::cons(
                (
                    b.prim(
                        Primitive::Pfield(1, FieldDbgInfo::PolyVarContent),
                        &[*arg],
                        arena.lam_loc(p.pat_loc),
                    ),
                    LetKind::Alias,
                ),
                &argl,
            );
            MatchCell {
                pm: PatternMatching {
                    cases: Vec::new(),
                    args: new_args,
                    default: def,
                },
                ctx,
                pat: normalize_pat(pa, p),
            }
        }
    }
}

/// Divide a pattern matching by variant tag.
/// Equivalent to OCaml's `divide_variant`.
fn divide_variant<'p, B: RawLambdaBuilder>(
    ctx_ref: &TypeContext,
    pa: &'p PatArena<'p>,
    arena: &LocArena<'_, B>,
    row: &RowDesc,
    ctx: &[Ctx<'p>],
    pm: &PatternMatching<'p>,
) -> Vec<((String, bool), MatchCell<'p>)> {
    let row = btype::row_repr(ctx_ref, row);

    fn divide_rec<'p, B: RawLambdaBuilder>(
        cx: MatchCx<'p, '_, B>,
        row: &RowDesc,
        cases: &[Clause<'p>],
        def: &DefaultEnv<'p>,
        ctx: &[Ctx<'p>],
        al: &MatchArgs,
    ) -> Vec<((String, bool), MatchCell<'p>)> {
        let MatchCx { ctx_ref, pa, arena } = cx;
        match cases.split_first() {
            Some(((patl, action), rem)) => {
                match patl.split_first() {
                    Some((p, rest_patl)) => {
                        match &p.pat_desc {
                            PatternDesc::Tpat_variant(lab, pato, _) => {
                                let variants = divide_rec(cx, row, rem, def, ctx, al);

                                // Check if this label is absent in the row
                                let is_absent = match row.row_fields.iter().find(|(l, _)| l == lab)
                                {
                                    Some((_, field)) => {
                                        matches!(
                                            btype::row_field_repr(ctx_ref, field),
                                            RowField::Rabsent
                                        )
                                    }
                                    None => true,
                                };

                                if is_absent {
                                    return variants;
                                }

                                let eq_key = |a: &(String, bool), b: &(String, bool)| a == b;

                                match pato {
                                    None => {
                                        let key = (lab.clone(), true);
                                        add(
                                            |a| {
                                                make_variant_matching_constant(
                                                    pa, p, lab, def, ctx, a,
                                                )
                                            },
                                            variants,
                                            eq_key,
                                            key,
                                            (rest_patl.to_vec(), action.clone()),
                                            al,
                                        )
                                    }
                                    Some(pat_inner) => {
                                        let key = (lab.clone(), false);
                                        let mut new_patl = vec![pa.pat(*pat_inner)];
                                        new_patl.extend(rest_patl.iter().cloned());
                                        add(
                                            |a| {
                                                make_variant_matching_nonconst(
                                                    pa, arena, p, lab, def, ctx, a,
                                                )
                                            },
                                            variants,
                                            eq_key,
                                            key,
                                            (new_patl, action.clone()),
                                            al,
                                        )
                                    }
                                }
                            }
                            _ => Vec::new(),
                        }
                    }
                    None => Vec::new(),
                }
            }
            None => Vec::new(),
        }
    }

    divide_rec(
        MatchCx { ctx_ref, pa, arena },
        &row,
        &pm.cases,
        &pm.default,
        ctx,
        &pm.args,
    )
}

// --- Variables (lines 1370-1378) ---

/// Get the arguments from a variable pattern (none — just the remainder).
/// Equivalent to OCaml's `get_args_var`.
fn get_args_var<'p>(_p: &'p Pattern, rem: &[&'p Pattern]) -> Vec<&'p Pattern> {
    rem.to_vec()
}

/// Matcher version of get_args_var for make_default.
fn matcher_get_args_var<'p>(
    _p: &'p Pattern,
    rem: &[&'p Pattern],
) -> Result<Vec<&'p Pattern>, MatchError> {
    Ok(rem.to_vec())
}

/// Make a variable matching.
/// Equivalent to OCaml's `make_var_matching`.
fn make_var_matching<'p>(
    pa: &PatArena<'p>,
    def: &DefaultEnv<'p>,
    args: &MatchArgs,
) -> PatternMatching<'p> {
    match args.split_first() {
        None => crate::misc::fatal_error("Matching.make_var_matching"),
        Some(_) => PatternMatching {
            cases: Vec::new(),
            args: args.tail(1),
            default: make_default(pa, &matcher_get_args_var, def),
        },
    }
}

/// Divide a pattern matching by variable.
/// Equivalent to OCaml's `divide_var`.
fn divide_var<'p>(
    pa: &'p PatArena<'p>,
    ctx: &[Ctx<'p>],
    pm: &PatternMatching<'p>,
) -> MatchCell<'p> {
    divide_line(
        |c| ctx_lshift(pa, c),
        |def, args| make_var_matching(pa, def, args),
        get_args_var,
        omega(),
        ctx,
        pm,
    )
}

// --- Tuples (lines 1382-1413) ---

/// Get the arguments from a tuple pattern.
/// Equivalent to OCaml's `get_args_tuple`.
fn get_args_tuple<'p>(
    pa: &PatArena<'p>,
    arity: usize,
    p: &'p Pattern,
    rem: &[&'p Pattern],
) -> Vec<&'p Pattern> {
    match &p.pat_desc {
        PatternDesc::Tpat_any => {
            let mut result = omegas(arity);
            result.extend(rem.iter().cloned());
            result
        }
        PatternDesc::Tpat_tuple(args) => prepend_row(pa.pats(*args), rem),
        _ => panic!("get_args_tuple: not a tuple or any pattern"),
    }
}

/// Matcher for tuple patterns.
/// Equivalent to OCaml's `matcher_tuple`.
fn matcher_tuple<'p>(
    pa: &PatArena<'p>,
    arity: usize,
    p: &'p Pattern,
    rem: &[&'p Pattern],
) -> Result<Vec<&'p Pattern>, MatchError> {
    match &p.pat_desc {
        PatternDesc::Tpat_or(_, _, _) => Err(MatchError::OrPat),
        PatternDesc::Tpat_any | PatternDesc::Tpat_var(..) => {
            let mut result = omegas(arity);
            result.extend(rem.iter().cloned());
            Ok(result)
        }
        PatternDesc::Tpat_tuple(args) if args.len() == arity => {
            let result = prepend_row(pa.pats(*args), rem);
            Ok(result)
        }
        _ => Err(MatchError::NoMatch),
    }
}

/// Make a tuple matching.
/// Equivalent to OCaml's `make_tuple_matching`.
fn make_tuple_matching<'p, B: RawLambdaBuilder>(
    b: &B,
    pa: &PatArena<'p>,
    loc: LamLoc,
    arity: usize,
    def: &DefaultEnv<'p>,
    args: &MatchArgs,
) -> PatternMatching<'p> {
    match args.split_first() {
        None => crate::misc::fatal_error("Matching.make_tuple_matching"),
        Some(((arg, _mut), _)) => {
            let argl = args.tail(1);
            let mut new_args: ArgsBuf = ArgsBuf::new();
            for pos in 0..arity {
                new_args.push((
                    b.prim(
                        Primitive::Pfield(pos as i32, FieldDbgInfo::Tuple),
                        &[*arg],
                        loc,
                    ),
                    LetKind::Alias,
                ));
            }
            new_args.extend(argl.iter().cloned());
            PatternMatching {
                cases: Vec::new(),
                args: MatchArgs::new(new_args),
                default: make_default(pa, &|p2, rem| matcher_tuple(pa, arity, p2, rem), def),
            }
        }
    }
}

/// Divide a pattern matching by tuple.
/// Equivalent to OCaml's `divide_tuple`.
fn divide_tuple<'p, B: RawLambdaBuilder>(
    pa: &'p PatArena<'p>,
    arena: &LocArena<'_, B>,
    arity: usize,
    p: &'p Pattern,
    ctx: &[Ctx<'p>],
    pm: &PatternMatching<'p>,
) -> MatchCell<'p> {
    let b = arena.b;
    divide_line(
        |c| filter_ctx(None, pa, p, c),
        |def, args| make_tuple_matching(b, pa, arena.lam_loc(p.pat_loc), arity, def, args),
        |pat, rem| get_args_tuple(pa, arity, pat, rem),
        p,
        ctx,
        pm,
    )
}

// --- Records (lines 1417-1476) ---

/// Build a record matching line from a Tpat_record pattern's fields.
/// This version takes the typed record fields directly.
fn record_matching_line_from_fields<'p>(
    pa: &PatArena<'p>,
    num_fields: usize,
    fields: &'p [(
        crate::types::typedtree::Loc<crate::parse_arena::LidentIdx>,
        std::sync::Arc<LabelDescription>,
        TPatIdx,
        bool,
    )],
) -> Vec<&'p Pattern> {
    // Determine the actual size needed: max of num_fields and any label position + 1.
    let max_pos = fields
        .iter()
        .map(|(_, lbl, _, _)| lbl.lbl_pos as usize + 1)
        .max()
        .unwrap_or(0);
    let size = std::cmp::max(num_fields, max_pos);
    let mut patv: Vec<&'p Pattern> = vec![omega(); size];
    for (_, lbl, pat, _) in fields {
        patv[lbl.lbl_pos as usize] = pa.pat(*pat);
    }
    patv
}

/// Get the arguments from a record pattern.
/// Equivalent to OCaml's `get_args_record`.
fn get_args_record<'p>(
    pa: &PatArena<'p>,
    num_fields: usize,
    p: &'p Pattern,
    rem: &[&'p Pattern],
) -> Vec<&'p Pattern> {
    match &p.pat_desc {
        PatternDesc::Tpat_any => {
            let mut result = record_matching_line_from_fields(pa, num_fields, &[]);
            result.extend(rem.iter().cloned());
            result
        }
        PatternDesc::Tpat_record(lbl_pat_list, _, _) => {
            let mut result = record_matching_line_from_fields(pa, num_fields, lbl_pat_list);
            result.extend(rem.iter().cloned());
            result
        }
        _ => panic!("get_args_record: not a record or any pattern"),
    }
}

/// Matcher for record patterns.
/// Equivalent to OCaml's `matcher_record`.
fn matcher_record<'p>(
    pa: &PatArena<'p>,
    num_fields: usize,
    p: &'p Pattern,
    rem: &[&'p Pattern],
) -> Result<Vec<&'p Pattern>, MatchError> {
    match &p.pat_desc {
        PatternDesc::Tpat_or(_, _, _) => Err(MatchError::OrPat),
        PatternDesc::Tpat_any | PatternDesc::Tpat_var(..) => {
            let mut result = record_matching_line_from_fields(pa, num_fields, &[]);
            result.extend(rem.iter().cloned());
            Ok(result)
        }
        PatternDesc::Tpat_record(fields, _, _) if fields.is_empty() && num_fields == 0 => {
            Ok(rem.to_vec())
        }
        PatternDesc::Tpat_record(lbl_pat_list, _, _) => {
            // Check that the first label's lbl_all length matches num_fields.
            // In OCaml: Array.length lbl.lbl_all = num_fields
            // In Rust, lbl_all is a LabelArrayRef placeholder. We check using
            // the all_labels array passed to divide_record instead.
            // For the matcher, we trust the caller's num_fields is correct.
            if !lbl_pat_list.is_empty() {
                let mut result = record_matching_line_from_fields(pa, num_fields, lbl_pat_list);
                result.extend(rem.iter().cloned());
                Ok(result)
            } else {
                Err(MatchError::NoMatch)
            }
        }
        _ => Err(MatchError::NoMatch),
    }
}

/// Make a record matching.
/// Equivalent to OCaml's `make_record_matching`.
fn make_record_matching<'p, B: RawLambdaBuilder>(
    b: &B,
    pa: &PatArena<'p>,
    loc: LamLoc,
    all_labels: &[LabelDescription],
    def: &DefaultEnv<'p>,
    args: &MatchArgs,
) -> PatternMatching<'p> {
    match args.split_first() {
        None => crate::misc::fatal_error("Matching.make_record_matching"),
        Some(((arg, _mut), _)) => {
            let argl = args.tail(1);
            let mut new_args: ArgsBuf = ArgsBuf::new();
            for lbl in all_labels.iter() {
                let access = match &lbl.lbl_repres {
                    RecordRepresentation::RecordRegular | RecordRepresentation::RecordArray => {
                        b.prim(Primitive::Pfield(lbl.lbl_pos, fld_record(lbl)), &[*arg], loc)
                    }
                    RecordRepresentation::RecordInlined { .. } => {
                        b.prim(Primitive::Pfield(lbl.lbl_pos, fld_record_inline(lbl)), &[*arg], loc)
                    }
                    RecordRepresentation::RecordUnboxed(_) => *arg,
                    RecordRepresentation::RecordExtension => b.prim(
                        Primitive::Pfield(lbl.lbl_pos + 1, fld_record_extension(lbl)),
                        &[*arg],
                        loc,
                    ),
                };
                let str_kind = match lbl.lbl_mut {
                    MutableFlag::Immutable => LetKind::Alias,
                    MutableFlag::Mutable => LetKind::StrictOpt,
                };
                new_args.push((access, str_kind));
            }
            new_args.extend(argl.iter().cloned());
            let nfields = all_labels.len();
            let def = make_default(pa, &|p2, rem| matcher_record(pa, nfields, p2, rem), def);
            PatternMatching {
                cases: Vec::new(),
                args: MatchArgs::new(new_args),
                default: def,
            }
        }
    }
}

/// Divide a pattern matching by record fields.
/// Equivalent to OCaml's `divide_record`.
fn divide_record<'p, B: RawLambdaBuilder>(
    ctx_ref: &TypeContext,
    pa: &'p PatArena<'p>,
    arena: &LocArena<'_, B>,
    all_labels: &[LabelDescription],
    p: &'p Pattern,
    ctx: &[Ctx<'p>],
    pm: &PatternMatching<'p>,
) -> MatchCell<'p> {
    let b = arena.b;
    let num_fields = all_labels.len();
    divide_line(
        |c| filter_ctx(Some(ctx_ref), pa, p, c),
        |def, args| make_record_matching(b, pa, arena.lam_loc(p.pat_loc), all_labels, def, args),
        |pat, rem| get_args_record(pa, num_fields, pat, rem),
        p,
        ctx,
        pm,
    )
}

// --- Arrays (lines 1480-1516) ---

/// Get the key (length) from an array pattern.
/// Equivalent to OCaml's `get_key_array`.
fn get_key_array(p: &Pattern) -> usize {
    match &p.pat_desc {
        PatternDesc::Tpat_array(patl) => patl.len(),
        _ => panic!("get_key_array: not an array pattern"),
    }
}

/// Get the arguments from an array pattern.
/// Equivalent to OCaml's `get_args_array`.
fn get_args_array<'p>(pa: &PatArena<'p>, p: &'p Pattern, rem: &[&'p Pattern]) -> Vec<&'p Pattern> {
    match &p.pat_desc {
        PatternDesc::Tpat_array(patl) => prepend_row(pa.pats(*patl), rem),
        _ => panic!("get_args_array: not an array pattern"),
    }
}

/// Matcher for array patterns.
/// Equivalent to OCaml's `matcher_array`.
fn matcher_array<'p>(
    pa: &PatArena<'p>,
    len: usize,
    p: &'p Pattern,
    rem: &[&'p Pattern],
) -> Result<Vec<&'p Pattern>, MatchError> {
    match &p.pat_desc {
        PatternDesc::Tpat_or(_, _, _) => Err(MatchError::OrPat),
        PatternDesc::Tpat_array(args) if args.len() == len => {
            let result = prepend_row(pa.pats(*args), rem);
            Ok(result)
        }
        PatternDesc::Tpat_any => {
            let mut result = omegas(len);
            result.extend(rem.iter().cloned());
            Ok(result)
        }
        _ => Err(MatchError::NoMatch),
    }
}

/// Make an array matching cell.
/// Equivalent to OCaml's `make_array_matching`.
fn make_array_matching<'p, B: RawLambdaBuilder>(
    pa: &'p PatArena<'p>,
    arena: &LocArena<'_, B>,
    p: &'p Pattern,
    def: &DefaultEnv<'p>,
    ctx: &[Ctx<'p>],
    args: &MatchArgs,
) -> MatchCell<'p> {
    let b = arena.b;
    match args.split_first() {
        None => crate::misc::fatal_error("Matching.make_array_matching"),
        Some(((arg, _mut), _)) => {
            let argl = args.tail(1);
            let len = get_key_array(p);
            let mut new_args: ArgsBuf = ArgsBuf::new();
            for pos in 0..len {
                new_args.push((
                    b.prim(
                        Primitive::Parrayrefu,
                        &[
                            *arg,
                            b.const_(crate::lambda::Constant::Int {
                                i: pos as i32,
                                comment: None,
                            }),
                        ],
                        arena.lam_loc(p.pat_loc),
                    ),
                    LetKind::StrictOpt,
                ));
            }
            new_args.extend(argl.iter().cloned());
            let def = make_default(pa, &|p2, rem| matcher_array(pa, len, p2, rem), def);
            let ctx = filter_ctx(None, pa, p, ctx);
            MatchCell {
                pm: PatternMatching {
                    cases: Vec::new(),
                    args: MatchArgs::new(new_args),
                    default: def,
                },
                ctx,
                pat: normalize_pat(pa, p),
            }
        }
    }
}

/// Divide a pattern matching by array length.
/// Equivalent to OCaml's `divide_array`.
fn divide_array<'p, B: RawLambdaBuilder>(
    pa: &'p PatArena<'p>,
    arena: &LocArena<'_, B>,
    ctx: &[Ctx<'p>],
    pm: &PatternMatching<'p>,
) -> Vec<(usize, MatchCell<'p>)> {
    divide(
        |p, d, c, a| make_array_matching(pa, arena, p, d, c, a),
        |a, b| a == b,
        get_key_array,
        |p, rem| get_args_array(pa, p, rem),
        ctx,
        pm,
    )
}

// ============================================================================
// Generic test trees — Sharing (OCaml matching.ml lines 1609-1659)
// ============================================================================

/// What the `share_actions_tree` functions return: the catch handlers by
/// exit label, the cases with shared actions replaced by exits, and the
/// default.
type SharedActions<K, H> = (Vec<(i32, H)>, Vec<(K, RawLambda)>, Option<RawLambda>);

/// Process shared actions for tree-based matching.
/// Returns `(wrapper_fn, processed_sw, processed_d)`.
/// The wrapper_fn wraps the result with catch handlers.
///
/// Equivalent to OCaml's `share_actions_tree`.
fn share_actions_tree<B: RawLambdaBuilder>(
    b: &B,
    sw: Vec<(Constant, RawLambda)>,
    d: Option<RawLambda>,
    next_raise_count: &mut i32,
) -> SharedActions<Constant, RawLambda> {
    let mut store = StoreExp::mk_store(b);

    // Default action is always shared
    let d_idx = d.map(|d| store.act_store_shared(d));

    // Store all other actions
    let sw_indices: Vec<(Constant, usize)> = sw
        .into_iter()
        .map(|(cst, act)| (cst, store.act_store(act)))
        .collect();

    // Retrieve all actions, including potential default
    let acts = store.act_get_shared();

    // Process shared actions — OCaml's handle_shared. Only the actual catch
    // handlers are kept: when the action is already a simple exit there is
    // no handler to reapply.
    let mut handler_pairs: Vec<(i32, RawLambda)> = Vec::new();
    let resolved_acts: Vec<RawLambda> = acts
        .into_iter()
        .map(|act| match act {
            Shared::Single(a) => a,
            Shared::Shared(a) => {
                let (i, h) = make_catch_delayed(b, a, next_raise_count);
                if let Some(h) = h {
                    handler_pairs.push((i, h));
                }
                make_exit(b, i)
            }
        })
        .collect();

    // Reconstruct default and switch list
    let d = d_idx.map(|idx| resolved_acts[idx]);
    let sw: Vec<(Constant, RawLambda)> = sw_indices
        .into_iter()
        .map(|(cst, j)| (cst, resolved_acts[j]))
        .collect();

    (handler_pairs, sw, d)
}

/// Apply handler wrappers to a result lambda.
/// The handlers are applied in forward order (first handler = innermost).
/// Equivalent to OCaml's `!hs result`.
fn apply_handlers<B: RawLambdaBuilder>(
    b: &B,
    mut result: RawLambda,
    handlers: Vec<(i32, RawLambda)>,
) -> RawLambda {
    // OCaml composes: hs := fun act -> h(ohs(act))
    // First handler added is innermost, last is outermost.
    // Each wrapper h wraps the body in LstaticCatch(body, (i,[]), handler_body).
    // So iterating forward: first handler wraps result first (innermost),
    // then each subsequent handler wraps around (outermost).
    for (exit_id, handler) in handlers.into_iter() {
        match b.node(result) {
            Node::StaticRaise { label, args } if label == exit_id && args == LamArena::EMPTY => {
                result = handler;
            }
            _ => {
                result = b.static_catch(result, exit_id, &[], handler);
            }
        }
    }
    result
}

/// Remove duplicate entries from a sorted (constant, lambda) list.
/// Keeps the first occurrence of each constant.
/// Equivalent to OCaml's `uniq_lambda_list`.
fn uniq_lambda_list(sw: Vec<(Constant, RawLambda)>) -> Vec<(Constant, RawLambda)> {
    if sw.len() <= 1 {
        return sw;
    }
    let mut result: Vec<(Constant, RawLambda)> = Vec::new();
    let mut iter = sw.into_iter();
    let first = iter.next().unwrap();
    result.push(first);
    for (c2, lam2) in iter {
        let last_c = &result.last().unwrap().0;
        if const_compare(last_c, &c2) == std::cmp::Ordering::Equal {
            // Duplicate — skip (keep the first, which is already in result)
            // OCaml keeps p1 (first) and drops the second
        } else {
            result.push((c2, lam2));
        }
    }
    result
}

/// Sort a (constant, lambda) list by constant value, then remove duplicates.
/// Equivalent to OCaml's `sort_lambda_list`.
fn sort_lambda_list(mut l: Vec<(Constant, RawLambda)>) -> Vec<(Constant, RawLambda)> {
    l.sort_by(|(x, _), (y, _)| const_compare(x, y));
    uniq_lambda_list(l)
}

// ============================================================================
// Layer 8: Integer/switch matching — OCaml matching.ml lines 1661-1941
// ============================================================================

fn do_tests_fail_owned<B: RawLambdaBuilder>(
    b: &B,
    loc: LamLoc,
    fail: RawLambda,
    tst: Primitive,
    arg: RawLambda,
    cases: Vec<(Constant, RawLambda)>,
) -> RawLambda {
    // OCaml compiler/ml/matching.ml:1761-1833 receives immutable action
    // pointers from `share_actions_tree`. `materialize_resolved_action` above
    // has already converted single-use Rust actions back to owned lambdas, so
    // build the same right-associated test chain while moving those actions
    // into place instead of recursively cloning them.
    cases.into_iter().rev().fold(fail, |acc, (c, act)| {
        b.if_raw(
            b.prim(tst.clone(), &[arg, typed_const_to_lambda_const(b, &c)], loc),
            acc,
            act,
        )
    })
}

fn do_tests_nofail_owned<B: RawLambdaBuilder>(
    b: &B,
    loc: LamLoc,
    tst: Primitive,
    arg: RawLambda,
    mut cases: Vec<(Constant, RawLambda)>,
) -> RawLambda {
    assert!(!cases.is_empty(), "Matching.do_tests_nofail");
    let (_, last_action) = cases
        .pop()
        .expect("checked non-empty constant test sequence");
    // Same branch shape as `do_tests_nofail`: for [c1->a1; c2->a2],
    // emit `if c1 then a2 else a1`. See compiler/ml/matching.ml:1761-1833.
    cases.into_iter().rev().fold(last_action, |acc, (c, act)| {
        b.if_raw(
            b.prim(tst.clone(), &[arg, typed_const_to_lambda_const(b, &c)], loc),
            acc,
            act,
        )
    })
}

/// Convert a typedtree constant to a lambda constant wrapped in Lconst.
/// Equivalent to OCaml's `Lconst(Const_base c)`.
fn typed_const_to_lambda_const<B: RawLambdaBuilder>(b: &B, c: &Constant) -> RawLambda {
    let lc = match c {
        Constant::Int(i) => crate::lambda::Constant::int(*i as i32),
        Constant::Char(c) => crate::lambda::Constant::Char(*c),
        Constant::String(s) => crate::lambda::Constant::String(s.clone()),
        Constant::Float(f) => crate::lambda::Constant::Float(f.clone()),
        Constant::BigInt(positive, v) => crate::lambda::Constant::BigInt {
            negative: !*positive,
            value: v.clone(),
        },
    };
    b.const_(lc)
}

/// Build a test sequence for constant matching.
/// Uses dichotomic splitting when there are enough cases and a less-than test is available.
/// Equivalent to OCaml's `make_test_sequence`; `comparison` builds its `tst`
/// (`Neq`) and `lt_tst` (`Lt`) primitives.
fn make_test_sequence<B: RawLambdaBuilder>(
    b: &B,
    loc: LamLoc,
    fail: Option<RawLambda>,
    comparison: fn(Comparison) -> Primitive,
    arg: RawLambda,
    const_lambda_list: Vec<(Constant, RawLambda)>,
    next_raise_count: &mut i32,
) -> RawLambda {
    let tst = comparison(Comparison::Neq);
    let lt_tst = comparison(Comparison::Lt);
    let const_lambda_list = sort_lambda_list(const_lambda_list);
    let (handlers, const_lambda_list, fail) =
        share_actions_tree(b, const_lambda_list, fail, next_raise_count);

    fn make_test_seq_inner_owned<B: RawLambdaBuilder>(
        b: &B,
        loc: &LamLoc,
        fail: Option<RawLambda>,
        tst: &Primitive,
        lt_tst: &Primitive,
        arg: &RawLambda,
        mut const_lambda_list: Vec<(Constant, RawLambda)>,
    ) -> RawLambda {
        if const_lambda_list.len() >= 4 && !matches!(lt_tst, Primitive::Pignore) {
            let mid = const_lambda_list.len() / 2;
            let list2 = const_lambda_list.split_off(mid);
            let pivot_const = &list2[0].0;
            b.if_raw(
                b.prim(
                    lt_tst.clone(),
                    &[*arg, typed_const_to_lambda_const(b, pivot_const)],
                    *loc,
                ),
                make_test_seq_inner_owned(b, loc, fail, tst, lt_tst, arg, const_lambda_list),
                make_test_seq_inner_owned(b, loc, fail, tst, lt_tst, arg, list2),
            )
        } else {
            match fail {
                None => do_tests_nofail_owned(b, *loc, tst.clone(), *arg, const_lambda_list),
                Some(fail) => {
                    do_tests_fail_owned(b, *loc, fail, tst.clone(), *arg, const_lambda_list)
                }
            }
        }
    }

    let result = make_test_seq_inner_owned(b, &loc, fail, &tst, &lt_tst, &arg, const_lambda_list);
    apply_handlers(b, result, handlers)
}

// ============================================================================
// Action sharing for Lswitch argument (OCaml matching.ml lines 1761-1833)
// ============================================================================

/// Deduplicate switch actions by wrapping shared actions in catch/exit.
/// Equivalent to OCaml's `share_actions_sw`.
pub fn share_actions_sw<B: RawLambdaBuilder>(
    b: &B,
    sw: RawLambdaSwitch,
    next_raise_count: &mut i32,
) -> (Vec<(i32, RawLambda)>, RawLambdaSwitch) {
    let mut store = StoreExp::mk_store(b);

    // Store fail action as shared
    let RawLambdaSwitch {
        sw_consts_full,
        sw_consts,
        sw_blocks_full,
        sw_blocks,
        sw_failaction,
        sw_dispatch,
    } = sw;

    let fail_idx = sw_failaction.map(|fail| store.act_store_shared(fail));

    // Store const and block actions
    let consts: Vec<(crate::lambda::SwitchKey, usize)> = sw_consts
        .into_iter()
        .map(|(i, e)| (i, store.act_store(e)))
        .collect();
    let blocks: Vec<(crate::lambda::SwitchKey, usize)> = sw_blocks
        .into_iter()
        .map(|(i, e)| (i, store.act_store(e)))
        .collect();

    // Get shared actions
    let acts = store.act_get_shared();

    // Process shared actions (handle_shared pattern). An action that is
    // already a simple exit targets an existing handler; no new wrapper.
    let mut handlers: Vec<(i32, RawLambda)> = Vec::new();
    let resolved_acts: Vec<RawLambda> = acts
        .into_iter()
        .map(|act| match act {
            Shared::Single(a) => a,
            Shared::Shared(a) => {
                let (i, h) = make_catch_delayed(b, a, next_raise_count);
                if let Some(h) = h {
                    handlers.push((i, h));
                }
                make_exit(b, i)
            }
        })
        .collect();

    let new_sw = RawLambdaSwitch {
        sw_consts_full,
        sw_consts: consts
            .into_iter()
            .map(|(i, j)| (i, resolved_acts[j]))
            .collect(),
        sw_blocks_full,
        sw_blocks: blocks
            .into_iter()
            .map(|(i, j)| (i, resolved_acts[j]))
            .collect(),
        sw_failaction: fail_idx.map(|idx| resolved_acts[idx]),
        sw_dispatch,
    };

    (handlers, new_sw)
}

/// Reintroduce fail action in switch argument.
/// When a static exit appears >= 3 times in the cases and there's no failaction,
/// extract it as the failaction to reduce switch size.
/// Equivalent to OCaml's `reintroduce_fail`.
pub fn reintroduce_fail<B: RawLambdaBuilder>(b: &B, sw: RawLambdaSwitch) -> RawLambdaSwitch {
    if sw.sw_failaction.is_some() {
        return sw;
    }

    let mut counts: HashMap<i32, i32> = HashMap::new();
    let seen = |counts: &mut HashMap<i32, i32>, lam: &RawLambda| {
        if let Some(i) = as_simple_exit(&*b.get(), *lam) {
            let old = counts.get(&i).copied().unwrap_or(0);
            counts.insert(i, old + 1);
        }
    };

    for (_, l) in &sw.sw_consts {
        seen(&mut counts, l);
    }
    for (_, l) in &sw.sw_blocks {
        seen(&mut counts, l);
    }

    let mut i_max: i32 = -1;
    let mut max: i32 = -1;
    for (&i, &c) in &counts {
        if c > max || (c == max && i > i_max) {
            i_max = i;
            max = c;
        }
    }

    if max >= 3 {
        let default = i_max;
        fn remove<K, B: RawLambdaBuilder>(b: &B, ls: Vec<(K, RawLambda)>, default: i32) -> Vec<(K, RawLambda)> {
            ls.into_iter()
                .filter(|(_, lam)| match as_simple_exit(&*b.get(), *lam) {
                    Some(j) => j != default,
                    None => true,
                })
                .collect()
        }
        let nconsts = sw.sw_consts.len();
        let nblocks = sw.sw_blocks.len();
        let sw_consts = remove(b, sw.sw_consts, default);
        let sw_blocks = remove(b, sw.sw_blocks, default);
        RawLambdaSwitch {
            sw_consts_full: sw.sw_consts_full && sw_consts.len() == nconsts,
            sw_consts,
            sw_blocks_full: sw.sw_blocks_full && sw_blocks.len() == nblocks,
            sw_blocks,
            sw_failaction: Some(make_exit(b, default)),
            sw_dispatch: sw.sw_dispatch,
        }
    } else {
        sw
    }
}

// ============================================================================
// Switcher = Switch.Make(SArg) — uses switch.rs (OCaml matching.ml line 1835)
// ============================================================================

// The Switcher module is already ported in switch.rs.
// The following functions provide the matching.ml-level interface.

/// Get the last key from a sorted list of (int, lambda) pairs.
/// Equivalent to OCaml's `last`.
fn last_key(def: i32, l: &[(i32, i32, RawLambda)]) -> i32 {
    match l.last() {
        None => def,
        Some((_, x, _)) => *x,
    }
}

/// Get the edge values (low, high) from a sorted list of ranges.
/// Equivalent to OCaml's `get_edges`.
fn get_edges(low: i32, high: i32, l: &[(i32, i32, RawLambda)]) -> (i32, i32) {
    match l.first() {
        None => (low, high),
        Some((x, _, _)) => (*x, last_key(high, l)),
    }
}

/// Remaining `(lo, hi, action)` cases, consumed front to back.
type IntCases = std::vec::IntoIter<(i32, i32, RawLambda)>;

/// `do_store _tag i j act` of `as_interval_canfail`: the action of a range
/// `i .. j` is used for each of its values. Storing it as shared emits it
/// once, as an expanded range sharing the action of each value used to;
/// copies would declare its variables twice.
fn store_range_action<B: RawLambdaBuilder>(
    store: &mut StoreExp<'_, B>,
    i: i32,
    j: i32,
    act: RawLambda,
) -> usize {
    if i < j {
        store.act_store_shared(act)
    } else {
        store.act_store(act)
    }
}

/// Convert a sorted range-lambda list with a fail action into intervals.
/// Equivalent to OCaml's `as_interval_canfail`.
///
/// The actions are moved into the store; the recursion mirrors OCaml's
/// list recursion with `rest` as an owning iterator.
fn as_interval_canfail<B: RawLambdaBuilder>(
    b: &B,
    fail: RawLambda,
    low: i32,
    high: i32,
    l: Vec<(i32, i32, RawLambda)>,
) -> (Vec<(i32, i32, usize)>, StoreExp<'_, B>) {
    let mut store = StoreExp::mk_store(b);

    let fail_idx = store_range_action(&mut store, 0, 0, fail);
    assert_eq!(fail_idx, 0); // fail has action index 0

    fn nofail_rec<B: RawLambdaBuilder>(
        cur_low: i32,
        cur_high: i32,
        cur_act: usize,
        rest: &mut IntCases,
        high: i32,
        store: &mut StoreExp<'_, B>,
    ) -> Vec<(i32, i32, usize)> {
        let Some((i, j, act_i)) = rest.next() else {
            return if cur_high == high {
                vec![(cur_low, cur_high, cur_act)]
            } else {
                vec![(cur_low, cur_high, cur_act), (cur_high + 1, high, 0)]
            };
        };
        let act_index = store_range_action(store, i, j, act_i);
        if cur_high + 1 == i {
            if act_index == cur_act {
                nofail_rec(cur_low, j, cur_act, rest, high, store)
            } else if act_index == 0 {
                let mut r = vec![(cur_low, i - 1, cur_act)];
                r.extend(fail_rec(i, j, rest, high, store));
                r
            } else {
                let mut r = vec![(cur_low, i - 1, cur_act)];
                r.extend(nofail_rec(i, j, act_index, rest, high, store));
                r
            }
        } else if act_index == 0 {
            // OCaml recurses with `fail_rec (cur_high + 1) (cur_high + 1) all`,
            // re-storing this case's action. That store hits the fail action
            // again (index 0, already marked shared), so `fail_rec` continues
            // as `fail_rec (cur_high + 1) j rem`.
            let mut r = vec![(cur_low, cur_high, cur_act)];
            r.extend(fail_rec(cur_high + 1, j, rest, high, store));
            r
        } else {
            let mut r = vec![(cur_low, cur_high, cur_act), (cur_high + 1, i - 1, 0)];
            r.extend(nofail_rec(i, j, act_index, rest, high, store));
            r
        }
    }

    fn fail_rec<B: RawLambdaBuilder>(
        cur_low: i32,
        cur_high: i32,
        rest: &mut IntCases,
        high: i32,
        store: &mut StoreExp<'_, B>,
    ) -> Vec<(i32, i32, usize)> {
        let Some((i, j, act_i)) = rest.next() else {
            return vec![(cur_low, cur_high, 0)];
        };
        let index = store_range_action(store, i, j, act_i);
        if index == 0 {
            fail_rec(cur_low, j, rest, high, store)
        } else {
            let mut r = vec![(cur_low, i - 1, 0)];
            r.extend(nofail_rec(i, j, index, rest, high, store));
            r
        }
    }

    let mut rest = l.into_iter();
    let intervals = match rest.next() {
        None => vec![(low, high, 0)],
        Some((i, j, act_i)) => {
            let index = store_range_action(&mut store, i, j, act_i);
            if index == 0 {
                fail_rec(low, j, &mut rest, high, &mut store)
            } else if low < i {
                let mut r = vec![(low, i - 1, 0)];
                r.extend(nofail_rec(i, j, index, &mut rest, high, &mut store));
                r
            } else {
                nofail_rec(i, j, index, &mut rest, high, &mut store)
            }
        }
    };

    (intervals, store)
}

/// Convert a sorted range-lambda list (no fail action) into intervals.
/// Equivalent to OCaml's `as_interval_nofail`.
fn as_interval_nofail<B: RawLambdaBuilder>(
    b: &B,
    l: Vec<(i32, i32, RawLambda)>,
) -> (Vec<(i32, i32, usize)>, StoreExp<'_, B>) {
    let mut store = StoreExp::mk_store(b);

    fn i_rec<B: RawLambdaBuilder>(
        cur_low: i32,
        cur_high: i32,
        cur_act: usize,
        rest: &mut IntCases,
        store: &mut StoreExp<'_, B>,
    ) -> Vec<(i32, i32, usize)> {
        let Some((i, j, act)) = rest.next() else {
            return vec![(cur_low, cur_high, cur_act)];
        };
        let act_index = store_range_action(store, i, j, act);
        if act_index == cur_act {
            i_rec(cur_low, j, cur_act, rest, store)
        } else {
            let mut r = vec![(cur_low, cur_high, cur_act)];
            r.extend(i_rec(i, j, act_index, rest, store));
            r
        }
    }

    assert!(!l.is_empty());
    // OCaml `some_hole` is applied to the tail of the list.
    let has_hole = l[1..].windows(2).any(|w| w[1].0 > w[0].1 + 1);
    let mut rest = l.into_iter();
    let (i, j, act) = rest.next().expect("non-empty");
    // In case there is some hole and that a switch is emitted, action 0 will
    // be used as the action of unreachable cases (cf. switch.ml,
    // make_switch). Hence, this action will be shared.
    let act_index = if has_hole || i < j {
        store.act_store_shared(act)
    } else {
        store.act_store(act)
    };
    assert_eq!(act_index, 0);
    let inters = i_rec(i, j, act_index, &mut rest, &mut store);

    (inters, store)
}

/// Switch intervals `(low, high, action index)` and the action store they
/// index into.
type Intervals<'a, B> = (Vec<(i32, i32, usize)>, StoreExp<'a, B>);

/// `as_interval_ranges fail low high l`: `l` maps disjoint ranges
/// `lo .. hi` to actions.
fn as_interval_ranges<B: RawLambdaBuilder>(
    b: &B,
    fail: Option<RawLambda>,
    low: i32,
    high: i32,
    mut l: Vec<(i32, i32, RawLambda)>,
) -> ((i32, i32), Intervals<'_, B>) {
    l.sort_by_key(|&(i, _, _)| i);
    let edges = get_edges(low, high, &l);
    let result = match fail {
        None => as_interval_nofail(b, l),
        Some(act) => as_interval_canfail(b, act, low, high, l),
    };
    (edges, result)
}

/// Compile an integer switch using the switch module.
/// Equivalent to OCaml's `call_switcher`.
pub fn call_switcher<B: RawLambdaBuilder>(
    b: &B,
    fail: Option<RawLambda>,
    arg: RawLambda,
    low: i32,
    high: i32,
    int_lambda_list: Vec<(i32, RawLambda)>,
    next_raise_count: &mut i32,
) -> RawLambda {
    let range_lambda_list = int_lambda_list
        .into_iter()
        .map(|(i, act)| (i, i, act))
        .collect();
    call_switcher_ranges(b, fail, arg, low, high, range_lambda_list, next_raise_count)
}

/// `call_switcher_ranges fail arg low high range_lambda_list`.
fn call_switcher_ranges<B: RawLambdaBuilder>(
    b: &B,
    fail: Option<RawLambda>,
    arg: RawLambda,
    low: i32,
    high: i32,
    range_lambda_list: Vec<(i32, i32, RawLambda)>,
    next_raise_count: &mut i32,
) -> RawLambda {
    let (edges, (cases, store)) = as_interval_ranges(b, fail, low, high, range_lambda_list);

    // Pass the existing action array through without re-storing it. The cases
    // above already contain indices into this exact array.
    let acts = store.act_get_shared();

    crate::raw_lambda::switch::zyva_with_shared_actions(b, edges, arg, &cases, acts, &mut || {
        bump_raise_count(next_raise_count)
    })
}

// ============================================================================
// Layer 9: Combine functions — OCaml matching.ml lines 1945-2349
// ============================================================================

/// Construct a pattern by or-ing together a list of patterns.
/// Equivalent to OCaml's `list_as_pat`.
fn list_as_pat<'p>(pa: &'p PatArena<'p>, pats: &[&'p Pattern]) -> &'p Pattern {
    match pats {
        [] => crate::misc::fatal_error("Matching.list_as_pat"),
        [pat] => pat,
        [pat, rest @ ..] => {
            let rest = list_as_pat(pa, rest);
            pa.alloc(with_desc(
                pat,
                PatternDesc::Tpat_or(pa.handle(pat), pa.handle(rest), None),
            ))
        }
    }
}

/// Complete the list of constructors not yet seen in the match.
/// Returns patterns for all constructors NOT in `pats`.
/// Equivalent to OCaml's `complete_pats_constrs`.
///
/// This requires environment lookups to get all constructors of a type.
/// We use a simplified approach: extract constructor info from the first pattern.
fn complete_pats_constrs<'p>(
    ctx_ref: &TypeContext,
    pa: &'p PatArena<'p>,
    pats: &[&'p Pattern],
) -> Vec<&'p Pattern> {
    match pats.first() {
        None => panic!("complete_pats_constrs: empty list"),
        Some(p) => {
            let cstr = pat_as_constr(p);

            if matches!(cstr.cstr_kind, crate::types::ConstructorKind::Extension(_)) {
                return Vec::new();
            }
            let seen_constrs: Vec<std::sync::Arc<ConstructorDescription>> =
                pats.iter().map(|p| get_key_constr(p)).collect();

            // Get all constructors of the type from the environment
            let env_opt = ctx_ref.get_typed_env(p.pat_env);
            let all_constrs: Vec<ConstructorDescription> = if let Some(env) = env_opt {
                // Try to find the type declaration and its constructors
                // Try to expand the type and find its constructors
                get_variant_constructors_from_env(ctx_ref, env.as_ref(), cstr.cstr_res)
            } else {
                Vec::new()
            };

            let mut others: Vec<_> = all_constrs
                .into_iter()
                .filter(|cnstr| {
                    !seen_constrs
                        .iter()
                        .any(|seen| same_constructor(cnstr, seen))
                })
                .collect();
            others.sort_by_key(|cnstr| cnstr.cstr_arity != 0);
            others
                .iter()
                .map(|cnstr| pa.alloc(pat_of_constr(pa, p, cnstr)))
                .collect()
        }
    }
}

/// Create a pattern from a constructor description, using the example pattern for type info.
/// Equivalent to OCaml's `pat_of_constr`.
fn pat_of_constr(pa: &PatArena<'_>, ex_pat: &Pattern, cstr: &ConstructorDescription) -> Pattern {
    with_desc(
        ex_pat,
        PatternDesc::Tpat_construct(
            crate::parse_arena::Located {
                txt: crate::parse_arena::LidentIdx(0), // dummy
                loc: LocIdx::none(),
            },
            std::sync::Arc::new(cstr.clone()),
            pa.omegas(cstr.cstr_arity as usize),
        ),
    )
}

/// Get variant constructors from the environment for a given result type.
/// Equivalent to OCaml's `Parmatch.get_variant_constructors`.
fn get_variant_constructors_from_env(
    ctx_ref: &TypeContext,
    env: &crate::types::env::Env,
    result_type: TypeExprRef,
) -> Vec<ConstructorDescription> {
    use crate::types::ctype;
    use crate::types::decl::TypeKind;
    use crate::types::type_expr::TypeDesc;

    // `fst (Env.find_type_descrs path env)` (compiler/ml/parmatch.ml:484-495):
    // the descriptors built by `Datarepr.constructors_of_type`, where an
    // inline record is one argument with its declaration in `cstr_inlined`.
    fn build_descriptions(
        ctx: &TypeContext,
        path: &crate::types::Path,
        decl: &crate::types::TypeDeclaration,
    ) -> Vec<ConstructorDescription> {
        crate::types::env_lazy::constructors_of_type_path(path, decl, ctx)
    }

    let mut ty = ctx_ref.repr(result_type);
    for _ in 0..16 {
        let desc = ctx_ref.get_desc(ty);
        let TypeDesc::Tconstr { path, .. } = &*desc else {
            return Vec::new();
        };
        let exact_lookup = |decl: &crate::types::decl::TypeDeclaration| match path.view() {
            crate::types::path::PathView::Pident(_) => true,
            _ => decl
                .type_path
                .as_ref()
                .is_some_and(|decl_path| decl_path.same(path) || decl_path.name() == path.name()),
        };

        let env_decl = match env.lookup_type(path) {
            Ok(decl) if exact_lookup(decl) => Some(decl),
            _ => None,
        };
        // OCaml `Parmatch.get_variant_constructors` trusts `Env.find_type`
        // for the queried path, even when an alias path returns the target
        // declaration metadata (compiler/ml/parmatch.ml:975-984). The helper
        // below is Rust's Env.find_type-equivalent, so do not require its
        // returned `type_path` to be textually identical to the query.
        let fallback_decl = ctype::lookup_type_decl_for_path(ctx_ref, env, path);

        if let Some(decl) = env_decl {
            match &decl.type_kind {
                TypeKind::TypeVariant(_, _) => {
                    return build_descriptions(ctx_ref, path, decl);
                }
                TypeKind::TypeAbstract => {
                    if let Some(manifest) = decl.type_manifest {
                        let manifest = ctx_ref.repr(manifest);
                        if manifest != ty {
                            ty = manifest;
                            continue;
                        }
                    }
                }
                _ => {}
            }
        } else if let Some(decl) = fallback_decl {
            match &decl.type_kind {
                TypeKind::TypeVariant(_, _) => {
                    return build_descriptions(ctx_ref, path, &decl);
                }
                TypeKind::TypeAbstract => {
                    if let Some(manifest) = decl.type_manifest {
                        let manifest = ctx_ref.repr(manifest);
                        if manifest != ty {
                            ty = manifest;
                            continue;
                        }
                    }
                }
                _ => {}
            }
        }

        // OCaml `Parmatch.get_variant_constructors` asks `Env.find_type` for
        // the path and only expands the type head when that declaration has a
        // manifest (compiler/ml/parmatch.ml:975-984). Do not walk module type
        // aliases here: if normal Env-compatible lookup misses, the caller can
        // synthesize missing constructor tags from the typed constructor counts.

        if let Some(expanded) = ctype::expand_head_once(ctx_ref, env, ty) {
            let expanded = ctx_ref.repr(expanded);
            if expanded != ty {
                ty = expanded;
                continue;
            }
        }
        return Vec::new();
    }

    Vec::new()
}

/// Compute negative fail action (jump to default).
/// Returns (optional fail lambda, jumps).
/// Equivalent to OCaml's `mk_failaction_neg`.
fn mk_failaction_neg<'p, B: RawLambdaBuilder>(
    b: &B,
    partial: &Partial,
    ctx: &[Ctx<'p>],
    def: &DefaultEnv<'p>,
) -> (Option<RawLambda>, Jumps<'p>) {
    match partial {
        Partial::Partial => match def.first() {
            Some((_, idef)) => (
                Some(b.static_raise(*idef, &[])),
                jumps_singleton(*idef, ctx.to_vec()),
            ),
            None => {
                // Act as Total: if no default matrix exists, the switch cannot fail
                (None, jumps_empty())
            }
        },
        Partial::Total => (None, jumps_empty()),
    }
}

/// Compute positive fail action (enumerating missing constructors).
/// Returns (optional fail lambda, additional cases, jumps).
/// Equivalent to OCaml's `mk_failaction_pos`.
fn mk_failaction_pos<'p, B: RawLambdaBuilder>(
    b: &B,
    ctx_ref: &TypeContext,
    pa: &'p PatArena<'p>,
    partial: &Partial,
    seen: &[&'p Pattern],
    ctx: &[Ctx<'p>],
    defs: &DefaultEnv<'p>,
) -> (Option<RawLambda>, Vec<ConstrCase>, Jumps<'p>) {
    let fail_pats = complete_pats_constrs(ctx_ref, pa, seen);
    if fail_pats.len() < 32 {
        let to_test: Vec<(&'p Pattern, Vec<Ctx<'p>>)> = fail_pats
            .iter()
            .map(|pat| (*pat, ctx_lub(pa, pat, ctx)))
            .collect();

        let (fail, jmps) = scan_def(b, pa, ctx, Vec::new(), to_test, defs);
        (None, fail, jmps)
    } else {
        // Too many non-matched constructors -> reduced information
        let (fail, jumps) = mk_failaction_neg(b, partial, ctx, defs);
        (fail, Vec::new(), jumps)
    }
}

/// Scan default environment to build per-constructor fail actions.
/// Returns (key-action list, jumps).
/// Equivalent to OCaml's inner `scan_def` in `mk_failaction_pos`.
fn scan_def<'p, B: RawLambdaBuilder>(
    b: &B,
    pa: &'p PatArena<'p>,
    ctx: &[Ctx<'p>],
    env: Vec<(Vec<&'p Pattern>, i32)>,
    to_test: Vec<(&'p Pattern, Vec<Ctx<'p>>)>,
    defs: &[(Matrix<'p>, i32)],
) -> (Vec<ConstrCase>, Jumps<'p>) {
    if to_test.is_empty() || defs.is_empty() {
        // Fold env to build (klist, jumps)
        let mut klist: Vec<ConstrCase> = Vec::new();
        let mut jumps = jumps_empty();
        for (pats, i) in &env {
            let action = b.static_raise(*i, &[]);
            let mut new_klist: Vec<ConstrCase> = pats
                .iter()
                .map(|pat| (get_key_constr(pat), action))
                .collect();
            new_klist.extend(klist);
            klist = new_klist;
        }
        for (pats, i) in env.iter().rev() {
            if !ctx.is_empty() {
                let jump_ctx = ctx_lub(pa, list_as_pat(pa, pats), ctx);
                jumps = jumps_add(pa, *i, jump_ctx, jumps);
            }
        }
        (klist, jumps)
    } else {
        match defs.split_first() {
            None => scan_def(b, pa, ctx, env, Vec::new(), &[]),
            Some(((pss, idef), rem)) => {
                let (now, later): (Vec<_>, Vec<_>) = to_test
                    .into_iter()
                    .partition(|(_, p_ctx)| ctx_match(pa, p_ctx, pss));
                if now.is_empty() {
                    scan_def(b, pa, ctx, env, later, rem)
                } else {
                    let pats: Vec<&'p Pattern> = now.into_iter().map(|(p, _)| p).collect();
                    let mut new_env = vec![(pats, *idef)];
                    new_env.extend(env);
                    scan_def(b, pa, ctx, new_env, later, rem)
                }
            }
        }
    }
}

/// Overloaded version of `same_actions` for tagged lists (ConstructorTag, lambda).
/// Checks if all actions in a case list are the same.
fn all_actions_same_tagged<K, B: RawLambdaBuilder>(b: &B, cases: &[(K, RawLambda)]) -> bool {
    match cases {
        [] => false,
        [_] => true,
        [(_, act0), rem @ ..] => {
            let Some(raw_act0) = make_key_string(b, *act0) else {
                return false;
            };
            for (_, act) in rem {
                if !make_key_equals(b, *act, &raw_act0) {
                    return false;
                }
            }
            true
        }
    }
}

/// Share actions for tree-based string matching.
/// Like share_actions_tree but for (String, RawLambda) pairs.
fn share_actions_tree_string<B: RawLambdaBuilder>(
    b: &B,
    sw: Vec<(String, RawLambda)>,
    d: Option<RawLambda>,
    next_raise_count: &mut i32,
) -> SharedActions<String, Option<RawLambda>> {
    let mut store = StoreExp::mk_store(b);

    let d_idx = d.map(|d| store.act_store_shared(d));

    let sw_indices: Vec<(String, usize)> = sw
        .into_iter()
        .map(|(s, act)| (s, store.act_store(act)))
        .collect();

    let acts = store.act_get_shared();

    // Process shared actions — handle_shared
    let mut handlers: Vec<(i32, Option<RawLambda>)> = Vec::new();
    let resolved_acts: Vec<RawLambda> = acts
        .into_iter()
        .map(|act| match act {
            Shared::Single(a) => a,
            Shared::Shared(a) => {
                let (i, h) = make_catch_delayed(b, a, next_raise_count);
                handlers.push((i, h));
                make_exit(b, i)
            }
        })
        .collect();

    let d = d_idx.map(|idx| resolved_acts[idx]);
    let sw: Vec<(String, RawLambda)> = sw_indices
        .into_iter()
        .map(|(s, j)| (s, resolved_acts[j]))
        .collect();

    // The composed wrapper `hs` (first handler innermost); see
    // `apply_catch_delayed`.
    (handlers, sw, d)
}

/// The test a `combine_*` function builds: the match compiler's context,
/// the test's location and scrutinee, and the partiality, contexts and
/// default environment of the match it is part of.
struct CombineSite<'p, 'a, B: RawLambdaBuilder> {
    cx: MatchCx<'p, 'a, B>,
    loc: LamLoc,
    arg: RawLambda,
    partial: &'a Partial,
    ctx: &'a [Ctx<'p>],
    def: &'a DefaultEnv<'p>,
}

impl<'p, 'a, B: RawLambdaBuilder> Copy for CombineSite<'p, 'a, B> {}
impl<'p, 'a, B: RawLambdaBuilder> Clone for CombineSite<'p, 'a, B> {
    fn clone(&self) -> Self {
        *self
    }
}

/// Combine constant matching results.
/// Equivalent to OCaml's `combine_constant`.
fn combine_constant<'p, B: RawLambdaBuilder>(
    site: &CombineSite<'p, '_, B>,
    cst: &Constant,
    c_div: (Vec<(ConstantKey, RawLambda)>, Jumps<'p>, Vec<&'p Pattern>),
    next_raise_count: &mut i32,
) -> (RawLambda, Jumps<'p>) {
    let CombineSite {
        cx: MatchCx { pa, arena, .. },
        loc,
        arg,
        partial,
        ctx,
        def,
    } = *site;
    let b = arena.b;
    let (const_lambda_list, total, _pats) = c_div;
    let (fail, local_jumps) = mk_failaction_neg(b, partial, ctx, def);
    let lambda1 = match cst {
        // `char` is an alias of `int`, so a column can mix both. Its keys
        // are ranges. Match intervals use ReScript's int32 bounds.
        Constant::Int(_) | Constant::Char(_) => {
            let range_lambda_list: Vec<(i32, i32, RawLambda)> = const_lambda_list
                .into_iter()
                .map(|(key, l)| match int_key(&key) {
                    Some((lo, hi)) => (lo as i32, hi as i32, l),
                    None => panic!("combine_constant: expected an int range"),
                })
                .collect();
            call_switcher_ranges(
                b,
                fail,
                arg,
                i32::MIN,
                i32::MAX,
                range_lambda_list,
                next_raise_count,
            )
        }
        Constant::String(_) => {
            let const_lambda_list = sort_lambda_list(
                const_lambda_list
                    .into_iter()
                    .map(|((c, _), l)| (c, l))
                    .collect(),
            );
            let sw: Vec<(String, RawLambda)> = const_lambda_list
                .into_iter()
                .map(|(c, act)| match c {
                    Constant::String(s) => (s, act),
                    _ => panic!("combine_constant: expected Const_string"),
                })
                .collect();
            let (hs, sw, fail) = share_actions_tree_string(b, sw, fail, next_raise_count);
            let switch = b.string_switch(arg, &sw, fail);
            hs.into_iter()
                .fold(switch, |act, (i, h)| apply_catch_delayed(b, i, h, act))
        }
        Constant::Float(_) => make_test_sequence(
            b,
            loc,
            fail,
            Primitive::Pfloatcomp,
            arg,
            const_lambda_list
                .into_iter()
                .map(|((c, _), l)| (c, l))
                .collect(),
            next_raise_count,
        ),
        Constant::BigInt(_, _) => make_test_sequence(
            b,
            loc,
            fail,
            Primitive::Pbigintcomp,
            arg,
            const_lambda_list
                .into_iter()
                .map(|((c, _), l)| (c, l))
                .collect(),
            next_raise_count,
        ),
    };
    (lambda1, jumps_union(pa, local_jumps, total))
}

/// Split case list into constant and non-constant constructor cases.
/// Equivalent to OCaml's `split_cases`.
fn split_cases(tag_lambda_list: Vec<ConstrCase>) -> (Vec<ConstrCase>, Vec<ConstrCase>) {
    let (mut consts, mut nonconsts): (Vec<_>, Vec<_>) =
        tag_lambda_list
            .into_iter()
            .partition(|(cstr, _)| match cstr.cstr_kind {
                crate::types::ConstructorKind::Ordinary(_) => cstr.cstr_args.is_empty(),
                crate::types::ConstructorKind::Extension(_) => {
                    unreachable!("extension in split_cases")
                }
            });
    let position = |cstr: &ConstructorDescription| match cstr.cstr_kind {
        crate::types::ConstructorKind::Ordinary(reference) => reference.position,
        crate::types::ConstructorKind::Extension(_) => unreachable!("extension in split_cases"),
    };
    consts.sort_by_key(|(cstr, _)| position(cstr));
    nonconsts.sort_by_key(|(cstr, _)| position(cstr));
    (consts, nonconsts)
}

/// A polymorphic variant case: the tag's hash, its name and its action.
type HashedVariantCase = (i32, (String, RawLambda));

/// Split variant case list into constant and non-constant.
/// Equivalent to OCaml's `split_variant_cases`.
fn split_variant_cases(
    tag_lambda_list: Vec<((String, bool), RawLambda)>,
) -> (Vec<HashedVariantCase>, Vec<HashedVariantCase>) {
    let mut consts = Vec::new();
    let mut nonconsts = Vec::new();
    for ((name, is_const), act) in tag_lambda_list {
        let hash = btype::hash_variant(&name);
        if is_const {
            consts.push((hash, (name, act)));
        } else {
            nonconsts.push((hash, (name, act)));
        }
    }
    consts.sort_by_key(|(i, _)| *i);
    nonconsts.sort_by_key(|(i, _)| *i);
    (consts, nonconsts)
}

/// Get extension constructor cases.
/// Equivalent to OCaml's `get_extension_cases`.
fn get_extension_cases(
    tag_lambda_list: Vec<ConstrCase>,
) -> Vec<(crate::types::path::Path, RawLambda)> {
    tag_lambda_list
        .into_iter()
        .map(|(cstr, act)| match &cstr.cstr_kind {
            crate::types::ConstructorKind::Extension(path) => (*path, act),
            crate::types::ConstructorKind::Ordinary(_) => unreachable!("ordinary extension case"),
        })
        .collect()
}

/// Translate a path to a RawLambda access expression.
/// Equivalent to OCaml's `transl_normal_path`.
fn transl_normal_path<B: RawLambdaBuilder>(b: &B, path: &crate::types::path::Path) -> RawLambda {
    match path.view() {
        PathView::Pident(id) => {
            if id.is_global() {
                b.global_module(*id)
            } else {
                b.var(*id)
            }
        }
        PathView::Pdot(p, s, pos) => b.prim(
            Primitive::Pfield(
                *pos,
                FieldDbgInfo::Module { name: *s },
            ),
            &[transl_normal_path(b, p)],
            LamLoc::NONE,
        ),
        PathView::Papply(_, _) => panic!("transl_normal_path: Papply"),
    }
}

/// Translate an extension path to a RawLambda.
/// Equivalent to OCaml's `transl_extension_path`.
fn transl_extension_path<B: RawLambdaBuilder>(
    b: &B,
    ctx_ref: &TypeContext,
    env: EnvRef,
    path: &crate::types::path::Path,
) -> RawLambda {
    // OCaml: transl_extension_path = transl_value_path = fun env path ->
    //   transl_normal_path (Env.normalize_path_prefix env path)
    if let Some(typed_env) = ctx_ref.get_typed_env(env) {
        let normalized = typed_env.normalize_path_prefix(ctx_ref, path);
        // If normalization didn't resolve (still Pdot chain), try via type context's
        // resolved module sig cache for persistent module aliases
        let normalized = normalize_path_via_ctx(ctx_ref, &normalized);
        transl_normal_path(b, &normalized)
    } else {
        let normalized = normalize_path_via_ctx(ctx_ref, path);
        transl_normal_path(b, &normalized)
    }
}

/// Normalize a value path's prefix through the type context's module sig cache.
/// This handles persistent module aliases that Env::normalize_path can't resolve.
fn normalize_path_via_ctx(
    ctx_ref: &TypeContext,
    path: &crate::types::path::Path,
) -> crate::types::path::Path {
    use crate::types::path::Path;

    match path.view() {
        PathView::Pdot(prefix, name, pos) => {
            // First normalize the prefix recursively
            let norm_prefix = normalize_module_path_via_ctx(ctx_ref, prefix);
            if norm_prefix == *prefix {
                *path
            } else {
                Path::pdot_pos(norm_prefix, *name, *pos)
            }
        }
        _ => *path,
    }
}

/// Normalize a module path through the type context's module sig cache.
fn normalize_module_path_via_ctx(
    ctx_ref: &TypeContext,
    path: &crate::types::path::Path,
) -> crate::types::path::Path {
    use crate::types::decl::{ModuleType, SignatureItem};
    use crate::types::path::Path;

    // First normalize prefix recursively for Pdot
    let path = match path.view() {
        PathView::Pdot(prefix, name, pos) => {
            let norm_prefix = normalize_module_path_via_ctx(ctx_ref, prefix);
            if norm_prefix == *prefix {
                *path
            } else {
                Path::pdot_pos(norm_prefix, *name, *pos)
            }
        }
        _ => *path,
    };

    // Check if this path resolves to a module alias via sig caches
    match path.view() {
        PathView::Pdot(prefix, name, _) => {
            // Strategy 1: check the qualified module components cache.
            // This covers persistent module aliases like Js.Exn → Stdlib_Exn
            // that were resolved during type checking via with_resolved_module_components_for_path.
            if let Some(alias_target) = ctx_ref.find_module_alias_in_components(prefix, name) {
                if !alias_target.same(&path) {
                    return normalize_module_path_via_ctx(ctx_ref, &alias_target);
                }
            }

            // Strategy 2: try to find the parent module's signature from sig caches.
            let prefix_name = prefix.name();
            if let Some((_, sig)) = ctx_ref.find_resolved_module_sig(&prefix_name) {
                for item in sig.iter() {
                    if let SignatureItem::SigModule(id, md, _) = item {
                        if id.name() == name {
                            if let ModuleType::MtyAlias(_, alias_path) = &md.md_type {
                                return normalize_module_path_via_ctx(ctx_ref, alias_path);
                            }
                        }
                    }
                }
            } else {
                let alias_path = {
                    ctx_ref.renamed_module_sig(&prefix_name).and_then(|sig| {
                        sig.iter().find_map(|item| match item {
                            SignatureItem::SigModule(id, md, _) if id.name() == name => {
                                match &md.md_type {
                                    ModuleType::MtyAlias(_, alias_path) => Some(alias_path.clone()),
                                    _ => None,
                                }
                            }
                            _ => None,
                        })
                    })
                };
                if let Some(alias_path) = alias_path {
                    return normalize_module_path_via_ctx(ctx_ref, &alias_path);
                }
            }
            path
        }
        _ => path,
    }
}

/// Combine constructor matching results.
/// Equivalent to OCaml's `combine_constructor`.
fn combine_constructor<'p, B: RawLambdaBuilder>(
    site: &CombineSite<'p, '_, B>,
    ex_pat: &'p Pattern,
    cstr: &ConstructorDescription,
    c_div: CompiledCells<'p, std::sync::Arc<ConstructorDescription>>,
    next_raise_count: &mut i32,
) -> (RawLambda, Jumps<'p>) {
    let CombineSite {
        cx: MatchCx { ctx_ref, pa, arena },
        loc,
        arg,
        partial,
        ctx,
        def,
    } = *site;
    let b = arena.b;
    let (tag_lambda_list, total1, pats) = c_div;

    if matches!(cstr.cstr_kind, crate::types::ConstructorKind::Extension(_)) {
        // Special cases for extensions
        let (fail, local_jumps) = mk_failaction_neg(b, partial, ctx, def);
        let lambda1 = {
            let extension_cases = get_extension_cases(tag_lambda_list);
            // OCaml compiler/ml/matching.ml:2118-2139 uses the first extension
            // action as the default, then fold_rights remaining cases into
            // Pextension_slot_eq tests. Consume the owned action list here so
            // the Rust port preserves that shape without cloning action bodies.
            let (default, extension_cases) = match fail {
                None => {
                    let mut extension_cases = extension_cases.into_iter();
                    let Some((_, default)) = extension_cases.next() else {
                        panic!("combine_constructor: no extension cases");
                    };
                    (default, extension_cases.collect())
                }
                Some(fail) => (fail, extension_cases),
            };
            if extension_cases.is_empty() {
                default
            } else {
                let tag = ctx_ref.create_ident("tag");
                let tests = extension_cases
                    .into_iter()
                    .rev()
                    .fold(default, |rem, (path, act)| {
                        let ext = transl_extension_path(b, ctx_ref, ex_pat.pat_env, &path);
                        b.if_raw(
                            b.prim(Primitive::PextensionSlotEq, &[b.var(tag), ext], loc),
                            act,
                            rem,
                        )
                    });
                b.let_(LetKind::Alias, tag, arg, tests)
            }
        };
        (lambda1, jumps_union(pa, local_jumps, total1))
    } else {
        // Regular concrete type
        let reference = match cstr.cstr_kind {
            crate::types::ConstructorKind::Ordinary(reference) => reference,
            crate::types::ConstructorKind::Extension(_) => unreachable!(),
        };
        let (num_consts, num_nonconsts, sig_complete, matching_facts) = ctx_ref
            .with_variant_layout(reference.variant, |layout| {
                (
                    layout.num_constants(),
                    layout.num_blocks(),
                    tag_lambda_list.len() == layout.constructors.len(),
                    layout.matching_facts.clone(),
                )
            });
        let (fail_opt, fails, local_jumps) = if sig_complete {
            (None, Vec::new(), jumps_empty())
        } else {
            mk_failaction_pos(b, ctx_ref, pa, partial, &pats, ctx, def)
        };

        // OCaml shares the immutable list cells/actions here:
        // compiler/ml/matching.ml:2152-2155 builds `fails @ tag_lambda_list`,
        // then passes the same list to both `split_cases` and `same_actions`.
        // Rust's Vec is moved into `split_cases`, so compute the pure
        // same-action fast path first. When all actions match, move the first
        // owned action instead of cloning it; OCaml returns the original `act0`
        // at compiler/ml/matching.ml:2155-2156.
        let mut actions = fails;
        actions.extend(tag_lambda_list);
        let actions_all_same = fail_opt.is_none() && all_actions_same_tagged(b, &actions);

        let lambda1 = if actions_all_same {
            let (_, act) = actions
                .into_iter()
                .next()
                .expect("non-empty action list after same-action check");
            act // Identical actions, no failure
        } else {
            let (mut consts, mut nonconsts) = split_cases(actions);
            let is_option = constructor_has_optional_shape(cstr);
            if num_consts == 1
                && num_nonconsts == 1
                && consts.len() == 1
                && nonconsts.len() == 1
                && (cstr.cstr_name == "::" || cstr.cstr_name == "[]" || is_option)
            {
                // OCaml compiler/ml/matching.ml:2156-2173 emits a two-way test
                // for lists/options. `consts` and `nonconsts` are owned here, so
                // move the branch actions instead of cloning whole RawLambda
                // bodies out of borrowed slice patterns.
                let (_, act1) = consts.pop().expect("one constant constructor case");
                let (_, act2) = nonconsts.pop().expect("one block constructor case");
                // matching.ml `lower_constructor_matching_plan`: the presence
                // test of an option is redundant when the present action
                // starts with a test of its value that takes the absent
                // action for undefined.
                if is_option && value_test_defaults_on_undefined(b, arg, act1, act2) {
                    return (act2, jumps_union(pa, local_jumps, total1));
                }
                let test_arg = if is_option {
                    b.prim(Primitive::PisNotNone, &[arg], loc)
                } else {
                    b.prim(
                        Primitive::Pjscomp(Comparison::Neq),
                        &[arg, b.const_(crate::lambda::Constant::int(0))],
                        loc,
                    )
                };
                b.if_raw(test_arg, act2, act1)
            } else if num_consts == 2
                && num_nonconsts == 0
                && consts.len() == 2
                && nonconsts.is_empty()
                && (cstr.cstr_name == "true" || cstr.cstr_name == "false")
            {
                let find_action = |name: &str| {
                    consts
                        .iter()
                        .find_map(|(cstr, action)| (cstr.cstr_name == name).then_some(*action))
                        .expect("boolean constructor action")
                };
                b.if_raw(arg, find_action("true"), find_action("false"))
            } else {
                // Emit a switch. OCaml computes `act0` at
                // compiler/ml/matching.ml:2179-2189, but the only arm
                // that can consume it is guarded by `when false` at
                // matching.ml:2190. Skipping that pure computation
                // avoids normalizing/cloning switch actions without
                // changing the emitted lambda.
                let switch_cases = |cases: Vec<ConstrCase>| {
                    cases
                        .into_iter()
                        .map(|(cstr, action)| {
                            let reference = match cstr.cstr_kind {
                                crate::types::ConstructorKind::Ordinary(reference) => reference,
                                crate::types::ConstructorKind::Extension(_) => unreachable!(),
                            };
                            (
                                crate::lambda::SwitchKey::Constructor(
                                    reference.representation(ctx_ref),
                                ),
                                action,
                            )
                        })
                        .collect()
                };
                let sw = RawLambdaSwitch {
                    sw_consts_full: consts.len() >= num_consts,
                    sw_consts: switch_cases(consts),
                    sw_blocks_full: nonconsts.len() >= num_nonconsts,
                    sw_blocks: switch_cases(nonconsts),
                    sw_failaction: fail_opt,
                    sw_dispatch: crate::lambda::SwitchDispatch::Variant(matching_facts),
                };
                let (handlers, sw) = share_actions_sw(b, sw, next_raise_count);
                let sw = reintroduce_fail(b, sw);
                let result = b.switch(arg, sw);
                apply_handlers(b, result, handlers)
            }
        };
        (lambda1, jumps_union(pa, local_jumps, total1))
    }
}



/// `matching.ml value_test_defaults_on_undefined`, over arena handles.
fn value_test_defaults_on_undefined<B: RawLambdaBuilder>(
    b: &B,
    arg: RawLambda,
    absent: RawLambda,
    present: RawLambda,
) -> bool {
    // Drop the read guard before constructing the alias variable.
    if let Node::Let {
        kind: LetKind::Alias,
        id,
        value: def,
        body,
    } = b.node(present)
    {
        let alias = {
            let a = b.get();
            matches!(a.view(def), View::Prim(Primitive::PvalFromOptionNotNest, [payload], _) if a.eq_approx(arg, *payload))
        };
        if alias {
            let id = b.get().ident(id);
            let var = b.var(id);
            return value_test_defaults_on_undefined(b, var, absent, body)
                || value_test_defaults_on_undefined(b, def, absent, body);
        }
    }
    let a = b.get();
    let is_value = |e| match a.view(e) {
        View::Prim(Primitive::PvalFromOptionNotNest, [payload], _) => a.eq_approx(arg, *payload),
        _ => a.eq_approx(arg, e),
    };
    let is_defined_constant = |e| {
        matches!(
            a.view(e),
            View::Const(
                crate::lambda::Constant::Int { .. }
                    | crate::lambda::Constant::Char(_)
                    | crate::lambda::Constant::String { .. }
                    | crate::lambda::Constant::Float(_)
                    | crate::lambda::Constant::BigInt { .. }
                    | crate::lambda::Constant::JsFalse
                    | crate::lambda::Constant::JsTrue
            )
        )
    };
    match a.view(present) {
        View::Switch(scrut, sw) => sw.actions.fail.is_some_and(|fail| {
            is_value(scrut) && a.eq_approx(fail, absent) && switch_defaults_on_undefined(sw)
        }),
        View::StringSwitch(scrut, sw) => sw
            .default
            .is_some_and(|fail| is_value(scrut) && a.eq_approx(fail, absent)),
        View::If(cond, if_true, if_false) => match a.view(cond) {
            View::Prim(prim, [x, y], _)
                if (is_value(*x) && is_defined_constant(*y))
                    || (is_defined_constant(*x) && is_value(*y)) =>
            {
                let comparison = match prim {
                    Primitive::Pboolcomp(c)
                    | Primitive::Pintcomp(c)
                    | Primitive::Pfloatcomp(c)
                    | Primitive::Pbigintcomp(c)
                    | Primitive::Pstringcomp(c)
                    | Primitive::Pjscomp(c) => Some(*c),
                    _ => None,
                };
                match comparison {
                    Some(Comparison::Neq) => a.eq_approx(if_true, absent),
                    Some(Comparison::Eq) => a.eq_approx(if_false, absent),
                    _ => false,
                }
            }
            _ => false,
        },
        _ => false,
    }
}

/// matching.ml `switch_defaults_on_undefined`: whether the switch `sw` on an
/// untagged variant takes its default action for undefined: no case matches
/// undefined, and each side of the switch that undefined can reach has the
/// default action.
fn switch_defaults_on_undefined(sw: crate::lambda::arena::SwitchView<'_>) -> bool {
    use crate::types::variant_runtime::{BlockType, ConstructorCase, LiteralTag};
    match &sw.payload.dispatch {
        crate::lambda::SwitchDispatch::Variant(facts) => {
            !facts.block_types.is_empty()
                && !facts.block_types.contains(&BlockType::Unknown)
                && !sw.payload.blocks_full
                && !(sw.payload.consts_full && !sw.const_keys.is_empty())
                && sw.const_keys.iter().all(|key| match key {
                    crate::lambda::SwitchKey::Constructor(ConstructorCase::Constant(tag)) => {
                        tag.literal != LiteralTag::Undefined
                    }
                    _ => true,
                })
        }
        crate::lambda::SwitchDispatch::Direct => false,
    }
}

/// Convert a polyvar int_lambda_list by grouping entries with the same action.
/// Equivalent to OCaml's `Polyvar_pattern_match.convert`.
///
/// Groups entries that have the same lambda action together, producing a list
/// of `(hash_names, action)` pairs in order of first occurrence.
fn convert_polyvar_list<B: RawLambdaBuilder>(
    b: &B,
    xs: Vec<(i32, (String, RawLambda))>,
) -> Vec<(Vec<(i32, String)>, RawLambda)> {
    // Group by normalized action equality, matching OCaml's make_key-based
    // sharing. Groups are created in first-occurrence order.
    let mut groups: Vec<(Vec<(i32, String)>, RawLambda)> = Vec::new();
    let mut group_of_key: HashMap<String, usize> = HashMap::new();

    for (hash, (name, act)) in xs {
        match make_key_string(b, act) {
            Some(key) => match group_of_key.get(&key) {
                Some(&idx) => groups[idx].0.push((hash, name)),
                None => {
                    group_of_key.insert(key, groups.len());
                    groups.push((vec![(hash, name)], act));
                }
            },
            None => groups.push((vec![(hash, name)], act)),
        }
    }

    for (hash_names, _) in &mut groups {
        // Sort hashes descending within each group to match OCaml's Switcher.test_sequence ordering
        hash_names.sort_by_key(|(hash, _)| std::cmp::Reverse(*hash));
    }
    groups
}

/// Create a disjunction of equality tests for polyvar hash values.
/// Equivalent to OCaml's `Polyvar_pattern_match.or_list`.
fn raw_polyvariant_hash_const<B: RawLambdaBuilder>(b: &B, hash: i32, name: &str) -> RawLambda {
    b.const_(crate::lambda::lam_constant::Constant::Int {
        i: hash,
        comment: Some(Box::new(PointerInfo::PolyVariant(name.to_string()))),
    })
}

fn or_list_polyvar<B: RawLambdaBuilder>(
    b: &B,
    arg: &RawLambda,
    hash_names: &[(i32, String)],
) -> RawLambda {
    let (first_hash, first_name) = &hash_names[0];
    let init = b.prim(
        Primitive::Pintcomp(Comparison::Eq),
        &[*arg, raw_polyvariant_hash_const(b, *first_hash, first_name)],
        LamLoc::NONE,
    );
    hash_names[1..].iter().fold(init, |acc, (hash, name)| {
        b.prim(
            Primitive::Psequor,
            &[
                acc,
                b.prim(
                    Primitive::Pintcomp(Comparison::Eq),
                    &[*arg, raw_polyvariant_hash_const(b, *hash, name)],
                    LamLoc::NONE,
                ),
            ],
            LamLoc::NONE,
        )
    })
}

/// Build an if-chain from converted polyvar list.
/// Used by both make_test_sequence_variant_constant and call_switcher_variant_constant.
fn polyvar_if_chain<B: RawLambdaBuilder>(
    b: &B,
    fail: Option<RawLambda>,
    arg: &RawLambda,
    int_lambda_list: Vec<(i32, (String, RawLambda))>,
) -> RawLambda {
    let mut converted = convert_polyvar_list(b, int_lambda_list).into_iter();
    // Without a fail action the first action is the default and the rest are
    // if-then-else; with one, fail is the default and every entry is tested.
    let default = match fail {
        Some(fail_act) => fail_act,
        None => {
            converted
                .next()
                .expect("polyvar_if_chain: empty list with no fail")
                .1
        }
    };
    converted.rev().fold(default, |acc, (hash_names, act)| {
        let predicate = or_list_polyvar(b, arg, &hash_names);
        b.if_raw(predicate, act, acc)
    })
}

/// Make a test sequence for variant constant matching.
/// Equivalent to OCaml's `Polyvar_pattern_match.make_test_sequence_variant_constant`.
fn make_test_sequence_variant_constant<B: RawLambdaBuilder>(
    b: &B,
    fail: Option<RawLambda>,
    arg: RawLambda,
    int_lambda_list: Vec<(i32, (String, RawLambda))>,
) -> RawLambda {
    polyvar_if_chain(b, fail, &arg, int_lambda_list)
}

/// Call switcher for variant constant matching.
/// Equivalent to OCaml's `Polyvar_pattern_match.call_switcher_variant_constant`.
fn call_switcher_variant_constant<B: RawLambdaBuilder>(
    b: &B,
    fail: Option<RawLambda>,
    arg: RawLambda,
    int_lambda_list: Vec<(i32, (String, RawLambda))>,
) -> RawLambda {
    polyvar_if_chain(b, fail, &arg, int_lambda_list)
}

/// Call switcher for variant non-constant (block) matching.
/// Equivalent to OCaml's `Polyvar_pattern_match.call_switcher_variant_constr`.
fn call_switcher_variant_constr<B: RawLambdaBuilder>(
    b: &B,
    ctx_ref: &TypeContext,
    loc: LamLoc,
    fail: Option<RawLambda>,
    arg: RawLambda,
    int_lambda_list: Vec<(i32, (String, RawLambda))>,
) -> RawLambda {
    let v = ctx_ref.create_ident("variant");
    b.let_(
        LetKind::Alias,
        v,
        b.prim(Primitive::Pfield(0, FieldDbgInfo::PolyVarTag), &[arg], loc),
        call_switcher_variant_constant(b, fail, b.var(v), int_lambda_list),
    )
}

/// Combine variant matching results.
/// Equivalent to OCaml's `combine_variant`.
fn combine_variant<'p, B: RawLambdaBuilder>(
    site: &CombineSite<'p, '_, B>,
    row: &RowDesc,
    c_div: CompiledCells<'p, (String, bool)>,
) -> (RawLambda, Jumps<'p>) {
    let CombineSite {
        cx: MatchCx { ctx_ref, pa, arena },
        loc,
        arg,
        partial,
        ctx,
        def,
    } = *site;
    let b = arena.b;
    let (tag_lambda_list, total1, _pats) = c_div;
    let row = btype::row_repr(ctx_ref, row);
    let mut num_constr: usize = 0;
    if row.row_closed {
        for (_, f) in &row.row_fields {
            match btype::row_field_repr(ctx_ref, f) {
                RowField::Rabsent => {}
                RowField::Reither {
                    constant: true,
                    ref types,
                    ..
                } if !types.is_empty() => {}
                _ => num_constr += 1,
            }
        }
    } else {
        num_constr = usize::MAX;
    }

    let test_int_or_block = |arg: RawLambda, if_int: RawLambda, if_block: RawLambda| -> RawLambda {
        b.if_raw(
            b.prim(Primitive::PisPolyVarBlock, &[arg], loc),
            if_block,
            if_int,
        )
    };

    let sig_complete = tag_lambda_list.len() == num_constr;

    let (fail, local_jumps) = if sig_complete || matches!(partial, Partial::Total) {
        (None, jumps_empty())
    } else {
        mk_failaction_neg(b, partial, ctx, def)
    };

    let actions_all_same = fail.is_none() && all_actions_same_tagged(b, &tag_lambda_list);
    let lambda1 = if actions_all_same {
        // OCaml compiler/ml/matching.ml:2155-2156 returns the original
        // action when all switch branches share the same lambda.
        let (_, act) = tag_lambda_list
            .into_iter()
            .next()
            .expect("non-empty variant action list after same-action check");
        act
    } else {
        let (consts, nonconsts) = split_variant_cases(tag_lambda_list);
        if consts.len() == 1 && nonconsts.len() == 1 && fail.is_none() {
            let (_, (_, act1)) = consts.into_iter().next().expect("one constant case");
            let (_, (_, act2)) = nonconsts.into_iter().next().expect("one block case");
            test_int_or_block(arg, act1, act2)
        } else if nonconsts.is_empty() {
            // One can compare integers and pointers
            make_test_sequence_variant_constant(b, fail, arg, consts)
        } else if consts.is_empty() {
            let lam = call_switcher_variant_constr(b, ctx_ref, loc, fail, arg, nonconsts);
            // One must not dereference integers
            match fail {
                None => lam,
                Some(fail) => test_int_or_block(arg, fail, lam),
            }
        } else {
            let lam_const = call_switcher_variant_constant(b, fail, arg, consts);
            let lam_nonconst = call_switcher_variant_constr(b, ctx_ref, loc, fail, arg, nonconsts);
            test_int_or_block(arg, lam_const, lam_nonconst)
        }
    };
    (lambda1, jumps_union(pa, local_jumps, total1))
}

/// Combine array matching results.
/// Equivalent to OCaml's `combine_array`.
fn combine_array<'p, B: RawLambdaBuilder>(
    site: &CombineSite<'p, '_, B>,
    c_div: (Vec<(usize, RawLambda)>, Jumps<'p>, Vec<&'p Pattern>),
    next_raise_count: &mut i32,
) -> (RawLambda, Jumps<'p>) {
    let CombineSite {
        cx: MatchCx { ctx_ref, pa, arena },
        loc,
        arg,
        partial,
        ctx,
        def,
    } = *site;
    let b = arena.b;
    let (len_lambda_list, total1, _pats) = c_div;
    let (fail, local_jumps) = mk_failaction_neg(b, partial, ctx, def);
    let lambda1 = {
        let newvar = ctx_ref.create_ident("len");
        let int_lambda_list: Vec<(i32, RawLambda)> = len_lambda_list
            .into_iter()
            .map(|(len, act)| (len as i32, act))
            .collect();
        let switch_result = call_switcher(
            b,
            fail,
            b.var(newvar),
            0,
            i32::MAX,
            int_lambda_list,
            next_raise_count,
        );
        bind(
            b,
            LetKind::Alias,
            &newvar,
            &b.prim(Primitive::Parraylength, &[arg], loc),
            switch_result,
        )
    };
    (lambda1, jumps_union(pa, local_jumps, total1))
}

// ============================================================================
// Layer 10: Compile functions — OCaml matching.ml lines 2351-2606
// ============================================================================

/// Exception raised when all cases in a compile are unreachable.
/// Equivalent to OCaml's `Unused` exception.
#[derive(Debug)]
struct Unused;

/// A compiled match: its code and the jumps it may take.
type Compiled<'p> = (RawLambda, Jumps<'p>);

/// What `compile_list` returns: one action per key, the union of their
/// jumps, and the patterns of the compiled cells.
type CompiledCells<'p, K> = (Vec<(K, RawLambda)>, Jumps<'p>, Vec<&'p Pattern>);

/// Compiles one divided cell, given its contexts (`compile_list`).
type CellCompiler<'p, 'f> =
    dyn FnMut(&[Ctx<'p>], PatternMatching<'p>) -> Result<Compiled<'p>, Unused> + 'f;

/// Compiles an or-pattern handler's matching (`compile_orhandlers`).
type OrHandlerCompiler<'p, 'f> =
    dyn FnMut(&[Ctx<'p>], &PatternMatching<'p>) -> Result<Compiled<'p>, Unused> + 'f;

/// Compiles one half-compiled match (`comp_match_handlers`).
type HalfCompiledCompiler<'p, 'f> = dyn FnMut(&Partial, &[Ctx<'p>], &RawLambda, &PmHalfCompiled<'p>) -> Result<Compiled<'p>, Unused>
    + 'f;

/// Divides a matching into cells by key (`compile_test`'s `divide`).
type Divider<'p, 'f, K> = dyn Fn(&[Ctx<'p>], &PatternMatching<'p>) -> Vec<(K, MatchCell<'p>)> + 'f;

/// Combines the compiled cells into one test (`compile_test`'s `combine`).
type Combiner<'p, 'f, K> =
    dyn Fn(&[Ctx<'p>], &DefaultEnv<'p>, CompiledCells<'p, K>, &mut i32) -> Compiled<'p> + 'f;

/// Compile a list of divided cells.
/// Returns (key-action list, total jumps, pattern list).
/// Equivalent to OCaml's `compile_list`.
fn compile_list<'p, K: Clone>(
    pa: &'p PatArena<'p>,
    compile_fun: &mut CellCompiler<'p, '_>,
    division: Vec<(K, MatchCell<'p>)>,
) -> Result<CompiledCells<'p, K>, Unused> {
    let mut compiled = Vec::new();
    let mut totals = Vec::new();
    let mut new_pats = Vec::new();

    for (key, cell) in division {
        if cell.ctx.is_empty() {
            continue;
        }
        if let Ok((lambda1, total1)) = compile_fun(&cell.ctx, cell.pm) {
            // OCaml `compiler/ml/matching.ml:2358-2364` recurses on the
            // tail with `jumps_map ctx_combine total1 :: totals`, then
            // conses `(key, lambda1)` and `cell.pat` onto the returned
            // lists. Rust vectors need the result lists in forward order
            // and the jump totals in reverse-success order, so push
            // results linearly and reverse only the totals once.
            compiled.push((key, lambda1));
            totals.push(jumps_map(|c| ctx_combine(pa, &c), total1));
            new_pats.push(cell.pat);
        }
    }

    totals.reverse();
    Ok((compiled, jumps_unions(pa, totals), new_pats))
}

/// Compile or-pattern handlers.
/// Equivalent to OCaml's `compile_orhandlers`.
fn compile_orhandlers<'p, B: RawLambdaBuilder>(
    b: &B,
    pa: &'p PatArena<'p>,
    compile_fun: &mut OrHandlerCompiler<'p, '_>,
    lambda1: RawLambda,
    total1: Jumps<'p>,
    ctx: &[Ctx<'p>],
    to_catch: &[OrHandler<'p>],
) -> Compiled<'p> {
    /// `add_raised_exits raised lam`: adds the static exits `lam` jumps to.
    /// Exits cannot leave a function, so function bodies are skipped.
    fn add_raised_exits(
        a: &impl RawLambdaRead,
        raised: &mut std::collections::HashSet<i32>,
        lam: RawLambda,
    ) {
        match a.node(lam) {
            Node::Function { .. } => return,
            Node::StaticRaise { label, .. } => {
                raised.insert(label);
            }
            _ => {}
        }
        a.iter_children(lam, |child| add_raised_exits(a, raised, child));
    }

    fn do_rec<'p, B: RawLambdaBuilder>(
        b: &B,
        pa: &'p PatArena<'p>,
        compile_fun: &mut OrHandlerCompiler<'p, '_>,
        raised: &mut std::collections::HashSet<i32>,
        (r, total_r): Compiled<'p>,
        ctx: &[Ctx<'p>],
        to_catch: &[OrHandler<'p>],
    ) -> Compiled<'p> {
        match to_catch.split_first() {
            None => (r, total_r),
            // The or-pattern is unreachable, e.g. after a wildcard. Its
            // handler is not compiled: with a guard and no default, its
            // failure has no exit.
            Some(((_, i, _, _), rem)) if !raised.contains(i) => {
                do_rec(b, pa, compile_fun, raised, (r, total_r), ctx, rem)
            }
            Some(((mat, i, vars, pm), rem)) => {
                let ctx_i = select_columns(pa, mat, ctx);
                match compile_fun(&ctx_i, pm) {
                    Ok((handler_i, total_i)) => {
                        add_raised_exits(&*b.get(), raised, handler_i);
                        match raw_static_raise(b, r) {
                            Some((j, args)) if j == *i => {
                                let body = vars
                                    .iter()
                                    .zip(args.iter())
                                    .rev()
                                    .fold(handler_i, |body, (var, arg)| {
                                        bind(b, LetKind::Alias, var, arg, body)
                                    });
                                do_rec(
                                    b,
                                    pa,
                                    compile_fun,
                                    raised,
                                    (body, jumps_map(|c| ctx_rshift_num(ncols(mat), &c), total_i)),
                                    ctx,
                                    rem,
                                )
                            }
                            Some((_, args)) => {
                                // OCaml `compiler/ml/matching.ml:2375-2388`
                                // skips a handler when `raw_action r` is a
                                // different static raise.
                                drop(args);
                                do_rec(b, pa, compile_fun, raised, (r, total_r), ctx, rem)
                            }
                            None => do_rec(
                                b,
                                pa,
                                compile_fun,
                                raised,
                                (
                                    b.static_catch(r, *i, vars, handler_i),
                                    jumps_union(
                                        pa,
                                        jumps_remove(*i, total_r),
                                        jumps_map(|c| ctx_rshift_num(ncols(mat), &c), total_i),
                                    ),
                                ),
                                ctx,
                                rem,
                            ),
                        }
                    }
                    Err(Unused) => do_rec(
                        b,
                        pa,
                        compile_fun,
                        raised,
                        (b.static_catch(r, *i, vars, lambda_unit(b)), total_r),
                        ctx,
                        rem,
                    ),
                }
            }
        }
    }

    // The exits of the match and of the handlers compiled so far.
    let mut raised = std::collections::HashSet::new();
    add_raised_exits(&*b.get(), &mut raised, lambda1);
    do_rec(
        b,
        pa,
        compile_fun,
        &mut raised,
        (lambda1, total1),
        ctx,
        to_catch,
    )
}

/// Check if v approximately appears in lam.
/// Equivalent to OCaml's `approx_present`.
/// matching.ml `approx_present`: anything but a constant, a static raise,
/// a primitive, an alias let or a variable (including `Lglobal_module`)
/// counts as present.
fn approx_present(a: &impl RawLambdaRead, v: &Ident, lam: RawLambda) -> bool {
    match a.view(lam) {
        View::Const(_) => false,
        View::StaticRaise(_, args) | View::Prim(_, args, _) => {
            args.iter().any(|arg| approx_present(a, v, *arg))
        }
        View::Let(LetKind::Alias, _, l1, l2) => {
            approx_present(a, v, l1) || approx_present(a, v, l2)
        }
        View::Var(vv) => v.same(&vv),
        _ => true,
    }
}

/// Lower a binding into the appropriate branch.
/// Equivalent to OCaml's `lower_bind`.
fn lower_bind<B: RawLambdaBuilder>(b: &B, v: &Ident, arg: &RawLambda, lam: RawLambda) -> RawLambda {
    // OCaml `compiler/ml/matching.ml:2413-2435` rebuilds only the branch that
    // needs the alias binding.
    let present = |l: RawLambda| approx_present(&*b.get(), v, l);
    match b.node(lam) {
        Node::If { cond, then_, else_ } => {
            let pcond = present(cond);
            let pso = present(then_);
            let pnot = present(else_);
            match (pcond, pso, pnot) {
                (false, false, false) => lam,
                (false, true, false) => {
                    let then_ = lower_bind(b, v, arg, then_);
                    b.if_raw(cond, then_, else_)
                }
                (false, false, true) => {
                    let else_ = lower_bind(b, v, arg, else_);
                    b.if_raw(cond, then_, else_)
                }
                _ => bind(b, LetKind::Alias, v, arg, lam),
            }
        }
        Node::Switch { scrut: ls, .. } => {
            let (_, mut sw) = b.switch_parts(lam).expect("switch node");
            if sw.sw_consts.len() == 1 && sw.sw_blocks.is_empty() && !present(ls) {
                let (i, act) = sw.sw_consts.pop().expect("single const switch branch");
                sw.sw_consts.push((i, lower_bind(b, v, arg, act)));
                b.switch(ls, sw)
            } else if sw.sw_consts.is_empty() && sw.sw_blocks.len() == 1 && !present(ls) {
                let (i, act) = sw.sw_blocks.pop().expect("single block switch branch");
                sw.sw_blocks.push((i, lower_bind(b, v, arg, act)));
                b.switch(ls, sw)
            } else {
                bind(b, LetKind::Alias, v, arg, lam)
            }
        }
        Node::Let {
            kind: LetKind::Alias,
            id,
            value: lv,
            body: l,
        } => {
            if present(lv) {
                bind(b, LetKind::Alias, v, arg, lam)
            } else {
                let l = lower_bind(b, v, arg, l);
                b.push(Node::Let {
                    kind: LetKind::Alias,
                    id,
                    value: lv,
                    body: l,
                })
            }
        }
        // matching.ml:2407-2410: eliminate `let v = arg in v`; lower_bind is
        // only used for alias bindings, so `arg` is pure.
        Node::Var(_) if matches!(b.as_var(lam), Some(u) if u.same(v)) => *arg,
        _ => bind(b, LetKind::Alias, v, arg, lam),
    }
}

/// Bind with check — try to lower alias bindings.
/// Equivalent to OCaml's `bind_check`.
fn bind_check<B: RawLambdaBuilder>(
    b: &B,
    str_kind: LetKind,
    v: &Ident,
    arg: &RawLambda,
    lam: RawLambda,
) -> RawLambda {
    match (&str_kind, b.as_var(*arg)) {
        (_, Some(_)) => bind(b, str_kind, v, arg, lam),
        (LetKind::Alias, _) => lower_bind(b, v, arg, lam),
        _ => bind(b, str_kind, v, arg, lam),
    }
}

/// Compile the default/exit case.
/// Equivalent to OCaml's `comp_exit`.
fn comp_exit<'p, B: RawLambdaBuilder>(
    b: &B,
    ctx: &[Ctx<'p>],
    m: &PatternMatching<'p>,
) -> Result<Compiled<'p>, Unused> {
    match m.default.first() {
        Some((_, i)) => Ok((b.static_raise(*i, &[]), jumps_singleton(*i, ctx.to_vec()))),
        None => crate::misc::fatal_error("Matching.comp_exit"),
    }
}

/// Compile a match with multiple handlers (for split results).
/// Equivalent to OCaml's `comp_match_handlers`.
fn comp_match_handlers<'p, B: RawLambdaBuilder>(
    cx: MatchCx<'p, '_, B>,
    comp_fun: &mut HalfCompiledCompiler<'p, '_>,
    partial: &Partial,
    ctx: &[Ctx<'p>],
    arg: &RawLambda,
    first_match: &PmHalfCompiled<'p>,
    next_matchs: &[(i32, PmHalfCompiled<'p>)],
) -> Result<Compiled<'p>, Unused> {
    if next_matchs.is_empty() {
        return comp_fun(partial, ctx, arg, first_match);
    }

    // OCaml `compiler/ml/matching.ml:2448-2482` recurses over `next_matchs`
    // structurally by sharing the tail list. Borrow the Rust slice for the
    // same control flow instead of cloning precompiled match trees.
    match comp_fun(&Partial::Partial, ctx, arg, first_match) {
        Ok((first_lam, total)) => {
            c_rec(cx, comp_fun, partial, arg, (first_lam, total), next_matchs)
        }
        Err(Unused) => match next_matchs.split_first() {
            None => Err(Unused),
            Some(((_, x), xs)) => comp_match_handlers(cx, comp_fun, partial, ctx, arg, x, xs),
        },
    }
}

/// Inner recursive function for comp_match_handlers.
fn c_rec<'p, B: RawLambdaBuilder>(
    cx: MatchCx<'p, '_, B>,
    comp_fun: &mut HalfCompiledCompiler<'p, '_>,
    partial: &Partial,
    arg: &RawLambda,
    (body, total_body): Compiled<'p>,
    rest: &[(i32, PmHalfCompiled<'p>)],
) -> Result<Compiled<'p>, Unused> {
    let MatchCx { pa, arena, .. } = cx;
    let b = arena.b;
    match rest.split_first() {
        None => Ok((body, total_body)),
        Some(((i, pm), rem)) => {
            // OCaml `if ctx_i = [] then c_rec body total_body rem`: keep the
            // original table when nothing (non-empty) is extracted.
            let has_ctx_i =
                jumps_position(*i, &total_body).is_some_and(|p| !total_body[p].1.is_empty());
            if !has_ctx_i {
                c_rec(cx, comp_fun, partial, arg, (body, total_body), rem)
            } else {
                let (ctx_i, total_rem) = jumps_extract(*i, total_body);
                let this_partial = if rem.is_empty() {
                    *partial
                } else {
                    Partial::Partial
                };
                match comp_fun(&this_partial, &ctx_i, arg, pm) {
                    Ok((li, total_i)) => c_rec(
                        cx,
                        comp_fun,
                        partial,
                        arg,
                        (
                            b.static_catch(body, *i, &[], li),
                            jumps_union(pa, total_i, total_rem),
                        ),
                        rem,
                    ),
                    Err(Unused) => c_rec(
                        cx,
                        comp_fun,
                        partial,
                        arg,
                        (b.static_catch(body, *i, &[], lambda_unit(b)), total_rem),
                        rem,
                    ),
                }
            }
        }
    }
}

/// Find a reasonable name for the match variable from the first pattern.
/// Equivalent to OCaml's `name_pattern`.
fn name_pattern<'p>(
    pa: &PatArena<'p>,
    ctx_ref: &TypeContext,
    default: &str,
    cases: &[Clause<'p>],
) -> Ident {
    for (pats, _) in cases {
        if let Some(pat) = pats.first() {
            if let Some(id) = matching_id_of_pattern(pa, ctx_ref, pat) {
                return id;
            }
        }
    }
    ctx_ref.create_ident(default)
}

/// matching.ml `id_of_pattern`: a name for the value `pat` matches, also
/// found under an option's `Some`.
fn matching_id_of_pattern(pa: &PatArena<'_>, ctx_ref: &TypeContext, pat: &Pattern) -> Option<Ident> {
    if let Some(id) = id_of_pattern(pa, ctx_ref, pat) {
        return Some(id);
    }
    match &pat.pat_desc {
        PatternDesc::Tpat_construct(_, cstr, args)
            if args.len() == 1 && constructor_has_optional_shape(cstr) =>
        {
            id_of_pattern(pa, ctx_ref, pa.pat(pa.list(*args)[0]))
        }
        _ => None,
    }
}

/// Extract an identifier from a pattern (for naming purposes).
/// Equivalent to OCaml's `Typecore.id_of_pattern`.
fn id_of_pattern(pa: &PatArena<'_>, ctx_ref: &TypeContext, pat: &Pattern) -> Option<Ident> {
    match &pat.pat_desc {
        PatternDesc::Tpat_var(id, _) => Some(*id),
        PatternDesc::Tpat_alias(_, id, _) => Some(*id),
        PatternDesc::Tpat_construct(_, _, args) if args.len() == 1 => {
            match &pa.pat(pa.list(*args)[0]).pat_desc {
                PatternDesc::Tpat_var(id, _) | PatternDesc::Tpat_alias(_, id, _) => {
                    Some(ctx_ref.rename_ident(id))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// Convert arg to a variable (bind if not already a variable).
/// Equivalent to OCaml's `arg_to_var`.
fn arg_to_var<'p, B: RawLambdaBuilder>(
    b: &B,
    pa: &PatArena<'p>,
    ctx_ref: &TypeContext,
    arg: &RawLambda,
    cls: &[Clause<'p>],
) -> (Ident, RawLambda) {
    match b.as_var(*arg) {
        Some(v) => (v, *arg),
        None => {
            let v = name_pattern(pa, ctx_ref, "match", cls);
            (v, b.var(v))
        }
    }
}

/// Lambda unit value.
/// Equivalent to OCaml's `Lambda.lambda_unit`.
fn lambda_unit<B: RawLambdaBuilder>(b: &B) -> RawLambda {
    b.unit()
}

/// The main compilation function.
/// Input:
///   repr=used for inserting debug events (unused in ReScript)
///   partial=exhaustiveness information
///   ctx=a context
///   m=a pattern matching
/// Output: a lambda term, a jump summary
///
/// Equivalent to OCaml's `compile_match`.
fn compile_match<'p, B: RawLambdaBuilder>(
    cx: MatchCx<'p, '_, B>,
    _repr: Option<()>,
    partial: &Partial,
    ctx: &[Ctx<'p>],
    m: &PatternMatching<'p>,
    next_raise_count: &mut i32,
) -> Result<Compiled<'p>, Unused> {
    compile_match_cow(cx, partial, ctx, Cow::Borrowed(m), next_raise_count)
}

/// [`compile_match`] on a matching the caller gives up, so its cases and
/// default environment move on instead of being copied.
fn compile_match_owned<'p, B: RawLambdaBuilder>(
    cx: MatchCx<'p, '_, B>,
    partial: &Partial,
    ctx: &[Ctx<'p>],
    m: PatternMatching<'p>,
    next_raise_count: &mut i32,
) -> Result<Compiled<'p>, Unused> {
    compile_match_cow(cx, partial, ctx, Cow::Owned(m), next_raise_count)
}

fn compile_match_cow<'p, B: RawLambdaBuilder>(
    cx: MatchCx<'p, '_, B>,
    partial: &Partial,
    ctx: &[Ctx<'p>],
    m: Cow<'_, PatternMatching<'p>>,
    next_raise_count: &mut i32,
) -> Result<Compiled<'p>, Unused> {
    let MatchCx { ctx_ref, pa, arena } = cx;
    let b = arena.b;
    match (m.cases.as_slice(), m.args.as_slice()) {
        ([], []) => comp_exit(b, ctx, &m),
        ([(pats, action), ..], _) if pats.is_empty() => {
            if action.is_guarded() {
                let action = action.clone();
                let remaining = match m {
                    Cow::Borrowed(m) => PatternMatching {
                        cases: m.cases[1..].to_vec(),
                        args: m.args.clone(),
                        default: m.default.clone(),
                    },
                    Cow::Owned(mut m) => {
                        m.cases.remove(0);
                        m
                    }
                };
                let (lambda, total) =
                    compile_match_owned(cx, partial, ctx, remaining, next_raise_count)?;
                Ok((action.body_with(b, lambda), total))
            } else {
                Ok((action.to_raw(b), jumps_empty()))
            }
        }
        (_, [(arg, str_kind), argl @ ..]) => {
            let (arg, str_kind) = (*arg, *str_kind);
            let (v, newarg) = arg_to_var(b, pa, ctx_ref, &arg, &m.cases);
            let new_args = MatchArgs::cons((newarg, LetKind::Alias), argl);
            let (cases, default) = match m {
                Cow::Borrowed(m) => (m.cases.clone(), m.default.clone()),
                Cow::Owned(m) => (m.cases, m.default),
            };
            // `split_precompile` on a matching with the new args, without
            // first copying the cases into that matching.
            let argo = Some(v);
            let (info, rem) = Split {
                ctx_ref: Some(ctx_ref),
                pa,
                arena,
                argo: &argo,
                args: &new_args,
                next_raise: next_raise_count,
            }
            .split_or(cases, default);
            let first_match = info.me;

            let mut comp_fn = |partial: &Partial,
                               ctx: &[Ctx<'p>],
                               arg: &RawLambda,
                               pmh: &PmHalfCompiled<'p>|
             -> Result<Compiled<'p>, Unused> {
                do_compile_matching(cx, partial, ctx, arg, pmh, next_raise_count)
            };

            let (lam, total) =
                comp_match_handlers(cx, &mut comp_fn, partial, ctx, &newarg, &first_match, &rem)?;
            // matching.ml:2800-2808: a mutable field or array element is read
            // once into `v` here. The code that the exits jump to reads it
            // again and may see another value, as a guard may have changed
            // it, so what the tests on `v` found doesn't hold there.
            let total = match str_kind {
                LetKind::StrictOpt => jumps_map(ctx_erase_first_col, total),
                LetKind::Strict | LetKind::Alias | LetKind::Variable => total,
            };
            Ok((bind_check(b, str_kind, &v, &arg, lam), total))
        }
        (cases, []) if !cases.is_empty() => {
            // Cases exist but no args — shouldn't happen normally.
            // Return the first non-guarded action if available.
            for (_, act) in cases {
                if !act.is_guarded() {
                    return Ok((act.to_raw(b), jumps_empty()));
                }
            }
            Err(Unused)
        }
        _ => panic!("Matching.compile_match"),
    }
}

/// Main dispatch for compiling half-compiled pattern matchings.
/// Equivalent to OCaml's `do_compile_matching`.
fn do_compile_matching<'p, B: RawLambdaBuilder>(
    cx: MatchCx<'p, '_, B>,
    partial: &Partial,
    ctx: &[Ctx<'p>],
    arg: &RawLambda,
    pmh: &PmHalfCompiled<'p>,
    next_raise_count: &mut i32,
) -> Result<Compiled<'p>, Unused> {
    let MatchCx { ctx_ref, pa, arena } = cx;
    let b = arena.b;
    match pmh {
        PmHalfCompiled::Pm(pm) => {
            let pat = what_is_cases(&pm.cases);
            match &pat.pat_desc {
                PatternDesc::Tpat_any => compile_no_test(
                    cx,
                    &|ctx, pm| divide_var(pa, ctx, pm),
                    &|ctx| ctx_rshift(ctx),
                    partial,
                    ctx,
                    pm,
                    next_raise_count,
                ),
                PatternDesc::Tpat_tuple(patl) => {
                    let arity = patl.len();
                    let norm_pat = normalize_pat(pa, pat);
                    compile_no_test(
                        cx,
                        &move |ctx, pm| divide_tuple(pa, arena, arity, norm_pat, ctx, pm),
                        &|ctx| ctx_combine(pa, ctx),
                        partial,
                        ctx,
                        pm,
                        next_raise_count,
                    )
                }
                PatternDesc::Tpat_record(fields, _, _) if !fields.is_empty() => {
                    let all_labels = resolve_all_record_labels(ctx_ref, fields);
                    let norm_pat = normalize_pat(pa, pat);
                    compile_no_test(
                        cx,
                        &move |ctx, pm| {
                            divide_record(ctx_ref, pa, arena, &all_labels, norm_pat, ctx, pm)
                        },
                        &|ctx| ctx_combine(pa, ctx),
                        partial,
                        ctx,
                        pm,
                        next_raise_count,
                    )
                }
                PatternDesc::Tpat_constant(_) | PatternDesc::Tpat_interval(_, _) => {
                    let loc = arena.lam_loc(pat.pat_loc);
                    let arg_clone = *arg;
                    let cst_clone = get_key_constant("compile_match", pat).0;
                    compile_test_wrapper(
                        cx,
                        partial,
                        &|ctx, pm| divide_constant(pa, ctx, pm),
                        &|ctx, def, c_div, nrc| {
                            combine_constant(
                                &CombineSite {
                                    cx,
                                    loc,
                                    arg: arg_clone,
                                    partial,
                                    ctx,
                                    def,
                                },
                                &cst_clone,
                                c_div,
                                nrc,
                            )
                        },
                        ctx,
                        pm,
                        next_raise_count,
                    )
                }
                PatternDesc::Tpat_construct(_, cstr, _) => {
                    let loc = arena.lam_loc(pat.pat_loc);
                    let arg_clone = *arg;
                    let ex_pat: &'p Pattern = pat;
                    let cstr_clone = cstr.clone();
                    compile_test_wrapper(
                        cx,
                        partial,
                        &|ctx, pm| divide_constructor(ctx_ref, pa, arena, ctx, pm),
                        &|ctx, def, c_div, nrc| {
                            combine_constructor(
                                &CombineSite {
                                    cx,
                                    loc,
                                    arg: arg_clone,
                                    partial,
                                    ctx,
                                    def,
                                },
                                ex_pat,
                                &cstr_clone,
                                c_div,
                                nrc,
                            )
                        },
                        ctx,
                        pm,
                        next_raise_count,
                    )
                }
                PatternDesc::Tpat_array(_) => {
                    let loc = arena.lam_loc(pat.pat_loc);
                    let arg_clone = *arg;
                    compile_test_wrapper(
                        cx,
                        partial,
                        &|ctx, pm| divide_array(pa, arena, ctx, pm),
                        &|ctx, def, c_div, nrc| {
                            combine_array(
                                &CombineSite {
                                    cx,
                                    loc,
                                    arg: arg_clone,
                                    partial,
                                    ctx,
                                    def,
                                },
                                c_div,
                                nrc,
                            )
                        },
                        ctx,
                        pm,
                        next_raise_count,
                    )
                }
                PatternDesc::Tpat_variant(_, _, _row_ref) => {
                    let loc = arena.lam_loc(pat.pat_loc);
                    let arg_clone = *arg;
                    let row_desc =
                        extract_row_from_type_with_env(ctx_ref, pat.pat_type, pat.pat_env);
                    let row_desc2 = row_desc.clone();
                    compile_test_wrapper(
                        cx,
                        partial,
                        &move |ctx, pm| divide_variant(ctx_ref, pa, arena, &row_desc, ctx, pm),
                        &|ctx, def, c_div, _nrc| {
                            combine_variant(
                                &CombineSite {
                                    cx,
                                    loc,
                                    arg: arg_clone,
                                    partial,
                                    ctx,
                                    def,
                                },
                                &row_desc2,
                                c_div,
                            )
                        },
                        ctx,
                        pm,
                        next_raise_count,
                    )
                }
                _ => panic!("do_compile_matching: unexpected pattern"),
            }
        }
        PmHalfCompiled::PmVar(PmVarCompiled { inside, var_arg }) => {
            let (lam, total) = do_compile_matching(
                cx,
                partial,
                &ctx_lshift(pa, ctx),
                var_arg,
                inside,
                next_raise_count,
            )?;
            Ok((lam, jumps_map(|c| ctx_rshift(&c), total)))
        }
        PmHalfCompiled::PmOr(PmOrCompiled { body, handlers, .. }) => {
            let (lam, total) = compile_match(cx, None, partial, ctx, body, next_raise_count)?;
            let mut compile_fn =
                |ctx: &[Ctx<'p>], pm: &PatternMatching<'p>| -> Result<Compiled<'p>, Unused> {
                    compile_match(cx, None, partial, ctx, pm, next_raise_count)
                };
            Ok(compile_orhandlers(
                b,
                pa,
                &mut compile_fn,
                lam,
                total,
                ctx,
                handlers,
            ))
        }
    }
}

/// Compile without test (divide_line + compile_match).
/// Equivalent to OCaml's `compile_no_test`.
fn compile_no_test<'p, B: RawLambdaBuilder>(
    cx: MatchCx<'p, '_, B>,
    divide_fn: &dyn Fn(&[Ctx<'p>], &PatternMatching<'p>) -> MatchCell<'p>,
    up_ctx: &dyn Fn(&[Ctx<'p>]) -> Vec<Ctx<'p>>,
    partial: &Partial,
    ctx: &[Ctx<'p>],
    to_match: &PatternMatching<'p>,
    next_raise_count: &mut i32,
) -> Result<Compiled<'p>, Unused> {
    let cell = divide_fn(ctx, to_match);
    let (lambda, total) = compile_match_owned(cx, partial, &cell.ctx, cell.pm, next_raise_count)?;
    Ok((lambda, jumps_map(|c| up_ctx(&c), total)))
}

/// Wrapper for compile_test that handles the type-specific divide and combine.
/// This replaces the OCaml pattern of passing `compile_match repr partial` as a function.
///
/// We inline compile_test here to avoid borrow conflicts with next_raise_count
/// being captured by both compile_fn and combine_fn closures.
fn compile_test_wrapper<'p, K: Clone, B: RawLambdaBuilder>(
    cx: MatchCx<'p, '_, B>,
    partial: &Partial,
    divide_fn: &Divider<'p, '_, K>,
    combine_fn: &Combiner<'p, '_, K>,
    ctx: &[Ctx<'p>],
    pm: &PatternMatching<'p>,
    next_raise_count: &mut i32,
) -> Result<Compiled<'p>, Unused> {
    let MatchCx { pa, arena, .. } = cx;
    let b = arena.b;
    let raise_counter = std::cell::Cell::new(*next_raise_count);

    // Step 1: divide
    let division = divide_fn(ctx, pm);

    // Step 2: compile_list
    let c_div = {
        let mut compile_fn =
            |ctx: &[Ctx<'p>], pm: PatternMatching<'p>| -> Result<Compiled<'p>, Unused> {
                let mut next_raise = raise_counter.get();
                let result = compile_match_owned(cx, partial, ctx, pm, &mut next_raise);
                raise_counter.set(next_raise);
                result
            };
        compile_list(pa, &mut compile_fn, division)?
    };

    // Step 3: combine
    let result = match &c_div {
        (list, _, _) if list.is_empty() => match mk_failaction_neg(b, partial, ctx, &pm.default) {
            (None, _) => Err(Unused),
            (Some(l), total) => Ok((l, total)),
        },
        _ => {
            let mut next_raise = raise_counter.get();
            let result = combine_fn(ctx, &pm.default, c_div, &mut next_raise);
            raise_counter.set(next_raise);
            Ok(result)
        }
    };
    *next_raise_count = raise_counter.get();
    result
}

/// `lbl.lbl_all` of a record pattern's first label (compiler/ml/matching.ml:
/// 2564-2568 passes it to `divide_record`).
fn resolve_all_record_labels(
    ctx_ref: &TypeContext,
    fields: &[(
        crate::types::typedtree::Loc<crate::parse_arena::LidentIdx>,
        std::sync::Arc<LabelDescription>,
        TPatIdx,
        bool,
    )],
) -> Vec<LabelDescription> {
    match fields.first() {
        Some((_, first_lbl, _, _)) => pattern_label_family(ctx_ref, first_lbl),
        None => Vec::new(),
    }
}

/// Extract a RowDesc from a type expression (for variant matching).
/// Follows type links to find the Tvariant row.
/// Extract variant row with env-based expansion (preferred).
fn extract_row_from_type_with_env(
    ctx_ref: &TypeContext,
    ty: TypeExprRef,
    env_ref: crate::types::typedtree::EnvRef,
) -> RowDesc {
    use crate::types::btype;
    use crate::types::type_expr::TypeDesc;

    // First try expanding with the environment
    if let Some(env) = ctx_ref.get_typed_env(env_ref) {
        let expanded = crate::types::ctype::expand_head(ctx_ref, env.as_ref(), ty);
        let desc = ctx_ref.get_desc(expanded);
        if let TypeDesc::Tvariant(row) = &*desc {
            return btype::row_repr(ctx_ref, &ctx_ref.row_desc(row));
        }
    }

    extract_row_from_type(ctx_ref, ty)
}

fn extract_row_from_type(ctx_ref: &TypeContext, ty: TypeExprRef) -> RowDesc {
    use crate::types::btype;
    use crate::types::type_expr::TypeDesc;

    if let TypeDesc::Tvariant(row) = &*ctx_ref.get_desc(ctx_ref.repr(ty)) {
        return btype::row_repr(ctx_ref, &ctx_ref.row_desc(*row));
    }

    // Fallback: empty row
    RowDesc {
        row_fields: Vec::new().into(),
        row_more: TypeExprRef(0),
        row_closed: true,
        row_fixed: false,
        row_name: None,
    }
}

// ============================================================================
// Layer 11: Entry points — OCaml matching.ml lines 2631-2978
// ============================================================================

/// Find if a predicate holds for any sub-pattern description.
/// Equivalent to OCaml's `find_in_pat`.
fn find_in_pat(pa: &PatArena<'_>, pred: &dyn Fn(&PatternDesc) -> bool, p: &Pattern) -> bool {
    if pred(&p.pat_desc) {
        return true;
    }
    match &p.pat_desc {
        PatternDesc::Tpat_alias(p, _, _) | PatternDesc::Tpat_variant(_, Some(p), _) => {
            find_in_pat(pa, pred, pa.pat(*p))
        }
        PatternDesc::Tpat_tuple(ps)
        | PatternDesc::Tpat_construct(_, _, ps)
        | PatternDesc::Tpat_array(ps) => pa.pats(*ps).any(|p| find_in_pat(pa, pred, p)),
        PatternDesc::Tpat_record(lpats, _, _) => lpats
            .iter()
            .any(|(_, _, p, _)| find_in_pat(pa, pred, pa.pat(*p))),
        PatternDesc::Tpat_or(p, q, _) => {
            find_in_pat(pa, pred, pa.pat(*p)) || find_in_pat(pa, pred, pa.pat(*q))
        }
        PatternDesc::Tpat_dict(entries) => entries
            .iter()
            .any(|entry| find_in_pat(pa, pred, pa.pat(entry.tdp_pattern))),
        PatternDesc::Tpat_constant(_)
        | PatternDesc::Tpat_interval(..)
        | PatternDesc::Tpat_var(_, _)
        | PatternDesc::Tpat_any
        | PatternDesc::Tpat_variant(_, None, _) => false,
    }
}

/// Check if a pattern description accesses mutable record fields.
/// Equivalent to OCaml's `have_mutable_field`.
fn have_mutable_field(p: &PatternDesc) -> bool {
    match p {
        PatternDesc::Tpat_record(lps, _, _) => lps
            .iter()
            .any(|(_, lbl, _, _)| matches!(lbl.lbl_mut, MutableFlag::Mutable)),
        _ => false,
    }
}

/// Check if a pattern accesses mutable fields anywhere.
/// Equivalent to OCaml's `is_mutable`.
fn is_mutable(pa: &PatArena<'_>, p: &Pattern) -> bool {
    find_in_pat(pa, &have_mutable_field, p)
}

/// Downgrade Total to Partial when needed.
/// Equivalent to OCaml's `check_partial` (single pattern version,
/// matching.ml:2937-2956): when the matching reads some mutable field and has
/// a guard, which may change the field so that the cases after it, reading
/// it again, match none.
fn check_partial_single(
    pa: &PatArena<'_>,
    pat_act_list: &[(&Pattern, CaseAction)],
    partial: Partial,
) -> Partial {
    match partial {
        Partial::Partial => Partial::Partial,
        Partial::Total => {
            if pat_act_list.is_empty()
                || (pat_act_list.iter().any(|(_, act)| act.guard.is_some())
                    && pat_act_list.iter().any(|(pat, _)| is_mutable(pa, pat)))
            {
                Partial::Partial
            } else {
                Partial::Total
            }
        }
    }
}

/// Downgrade Total to Partial when needed (list of patterns version).
/// Equivalent to OCaml's `check_partial_list`.
fn check_partial_list<'p>(
    pa: &PatArena<'p>,
    pat_act_list: &[Clause<'p>],
    partial: Partial,
) -> Partial {
    match partial {
        Partial::Partial => Partial::Partial,
        Partial::Total => {
            if pat_act_list.is_empty()
                || (pat_act_list.iter().any(|(_, lam)| lam.is_guarded())
                    && pat_act_list
                        .iter()
                        .any(|(pats, _)| pats.iter().any(|p| is_mutable(pa, p))))
            {
                Partial::Partial
            } else {
                Partial::Total
            }
        }
    }
}

/// Create a starting context of n wildcards.
/// Equivalent to OCaml's `start_ctx`.
fn start_ctx<'p>(n: usize) -> Vec<Ctx<'p>> {
    vec![Ctx {
        left: Vec::new(),
        right: omegas(n),
    }]
}

/// Check total: add a catch handler if jumps are not empty.
/// Equivalent to OCaml's `check_total`.
fn check_total<'p, B: RawLambdaBuilder>(
    b: &B,
    total: &Jumps<'p>,
    lambda: RawLambda,
    i: i32,
    handler_fun: impl FnOnce() -> RawLambda,
) -> RawLambda {
    if jumps_is_empty(total) {
        lambda
    } else {
        b.static_catch(lambda, i, &[], handler_fun())
    }
}

/// The match compiler's patterns as a store for `Dict_pattern` lowering,
/// which adds the lowered patterns to the overlay.
impl crate::types::dict_pattern::PatternStore for &PatArena<'_> {
    fn pat(&self, idx: TPatIdx) -> &Pattern {
        PatArena::pat(self, idx)
    }
    fn pat_list(&self, list: TPatList) -> &[TPatIdx] {
        PatArena::list(self, list)
    }
    fn push_pat(&mut self, p: Pattern) -> TPatIdx {
        PatArena::push(self, p)
    }
    fn push_pat_list(&mut self, items: &[TPatIdx]) -> TPatList {
        PatArena::push_list(self, items.iter().copied())
    }
}

/// `Matching.lower_dict_patterns`: the cases with the dict patterns of the
/// match lowered to record patterns, see `Dict_pattern`.
fn lower_dict_patterns<'p>(
    ctx_ref: &TypeContext,
    pa: &'p PatArena<'p>,
    pat_act_list: Vec<(&'p Pattern, CaseAction)>,
) -> Vec<(&'p Pattern, CaseAction)> {
    let pats: Vec<&Pattern> = pat_act_list.iter().map(|(pat, _)| *pat).collect();
    let lowering = crate::types::dict_pattern::Lowering::new(ctx_ref, &pa, &pats);
    if lowering.is_identity() {
        return pat_act_list;
    }
    let mut store = pa;
    pat_act_list
        .into_iter()
        .map(|(pat, act)| (pa.pat(lowering.lower(&mut store, pa.handle(pat))), act))
        .collect()
}

/// The type context, pattern arena and location arena the match compiler
/// threads through its compile functions.
struct MatchCx<'p, 'a, B: RawLambdaBuilder> {
    ctx_ref: &'a TypeContext,
    pa: &'p PatArena<'p>,
    arena: &'a LocArena<'a, B>,
}

impl<'p, 'a, B: RawLambdaBuilder> Copy for MatchCx<'p, 'a, B> {}
impl<'p, 'a, B: RawLambdaBuilder> Clone for MatchCx<'p, 'a, B> {
    fn clone(&self) -> Self {
        *self
    }
}

/// The translation state a match is compiled in.
pub struct MatchEnv<'a, B: RawLambdaBuilder> {
    /// The type context the patterns' types live in.
    pub ctx_ref: &'a TypeContext,
    /// The typed tree the patterns live in.
    pub ta: &'a TypedArena,
    /// The arenas the compiled Lambda and its locations are built in.
    pub arena: &'a LocArena<'a, B>,
    /// The static-raise counter, shared with the rest of the translation.
    pub next_raise_count: &'a mut i32,
}

/// `Matching.compile_matching` on the cases of `Matching.for_function`,
/// `for_trywith` or `for_let`, which all lower their dict patterns first
/// (`lower_dict_patterns`).
pub fn compile_matching<B: RawLambdaBuilder>(
    env: MatchEnv<'_, B>,
    handler_fun: impl FnOnce() -> RawLambda,
    arg: RawLambda,
    pat_act_list: Vec<(&Pattern, CaseAction)>,
    partial: Partial,
) -> RawLambda {
    let MatchEnv {
        ctx_ref,
        ta,
        arena,
        next_raise_count,
    } = env;
    let store = PatStore::default();
    let pa = PatArena::new(ta, &store);
    let pat_act_list = lower_dict_patterns(ctx_ref, &pa, pat_act_list);
    compile_matching_unresolved(
        MatchCx {
            ctx_ref,
            pa: &pa,
            arena,
        },
        handler_fun,
        arg,
        pat_act_list,
        partial,
        next_raise_count,
    )
}

fn compile_matching_unresolved<'p, B: RawLambdaBuilder>(
    cx: MatchCx<'p, '_, B>,
    handler_fun: impl FnOnce() -> RawLambda,
    arg: RawLambda,
    pat_act_list: Vec<(&'p Pattern, CaseAction)>,
    partial: Partial,
    next_raise_count: &mut i32,
) -> RawLambda {
    let MatchCx { pa, arena, .. } = cx;
    let b = arena.b;
    let partial = check_partial_single(pa, &pat_act_list, partial);
    match partial {
        Partial::Partial => {
            let raise_num = bump_raise_count(next_raise_count);
            let pm = PatternMatching {
                cases: pat_act_list
                    .into_iter()
                    .map(|(pat, act)| (vec![pat], MatchAction::from_case(act)))
                    .collect(),
                args: MatchArgs::new([(arg, LetKind::Strict)]),
                default: vec![(vec![vec![omega()]], raise_num)],
            };
            match compile_match_owned(cx, &partial, &start_ctx(1), pm, next_raise_count) {
                Ok((lambda, total)) => check_total(b, &total, lambda, raise_num, handler_fun),
                Err(Unused) => panic!("compile_matching: Unused"),
            }
        }
        Partial::Total => {
            let pm = PatternMatching {
                cases: pat_act_list
                    .into_iter()
                    .map(|(pat, act)| (vec![pat], MatchAction::from_case(act)))
                    .collect(),
                args: MatchArgs::new([(arg, LetKind::Strict)]),
                default: Vec::new(),
            };
            match compile_match_owned(cx, &partial, &start_ctx(1), pm, next_raise_count) {
                Ok((lambda, total)) => {
                    assert!(jumps_is_empty(&total));
                    lambda
                }
                Err(Unused) => {
                    // Shouldn't happen for Total matches, but handle gracefully
                    // by returning a unit value as placeholder.
                    lambda_unit(b)
                }
            }
        }
    }
}

/// Build a match failure exception raise.
/// Equivalent to OCaml's `partial_function`.
pub fn partial_function<B: RawLambdaBuilder>(arena: &LocArena<'_, B>, loc: Location) -> RawLambda {
    let b = arena.b;
    // OCaml matching.ml:2688-2691 embeds the source position in the payload.
    arena.require_locations();
    let line = loc.loc_start.line;
    let char_pos = loc.loc_start.column();
    // `Filename.basename fname` (matching.ml:2690-2691).
    let fname = if loc.file_name_idx().0 == 0 {
        String::new()
    } else {
        let file = arena.get_string(loc.file_name_idx());
        std::path::Path::new(file)
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or(file)
            .to_string()
    };

    let node_loc = arena.locs.intern(loc);
    let match_failure_ident = crate::types::predef::ident_match_failure();
    let exn = b.global_module(match_failure_ident);
    let payload = b.const_(crate::lambda::Constant::Block {
        tag_info: Box::new(TagInfo::Tuple),
        elements: vec![
            crate::lambda::Constant::string(fname),
            crate::lambda::Constant::int(line),
            crate::lambda::Constant::int(char_pos),
        ],
    });

    b.prim(
        Primitive::Praise,
        &[b.prim(
            Primitive::Pmakeblock(TagInfo::Extension, Mutable::Immutable),
            &[exn, payload],
            node_loc,
        )],
        node_loc,
    )
}

/// Compile a match for a function body.
/// Equivalent to OCaml's `for_function`.
pub fn for_function<B: RawLambdaBuilder>(
    env: MatchEnv<'_, B>,
    loc: Location,
    param: RawLambda,
    pat_act_list: Vec<(&Pattern, CaseAction)>,
    partial: Partial,
) -> RawLambda {
    let arena = env.arena;
    let loc_clone = loc;
    compile_matching(
        env,
        || partial_function(arena, loc_clone),
        param,
        pat_act_list,
        partial,
    )
}

/// Compile a match for a try-with handler.
/// Equivalent to OCaml's `for_trywith`.
pub fn for_trywith<B: RawLambdaBuilder>(
    env: MatchEnv<'_, B>,
    param: RawLambda,
    pat_act_list: Vec<(&Pattern, CaseAction)>,
) -> RawLambda {
    let b = env.arena.b;
    let param_clone = param;
    compile_matching(
        env,
        || b.prim(Primitive::Praise, &[param_clone], LamLoc::NONE),
        param,
        pat_act_list,
        Partial::Partial,
    )
}

/// Simple let matching.
/// Equivalent to OCaml's `simple_for_let`.
pub fn simple_for_let<B: RawLambdaBuilder>(
    env: MatchEnv<'_, B>,
    loc: Location,
    param: RawLambda,
    pat: &Pattern,
    body: RawLambda,
) -> RawLambda {
    let arena = env.arena;
    let loc_clone = loc;
    compile_matching(
        env,
        || partial_function(arena, loc_clone),
        param,
        vec![(pat, CaseAction::unguarded(body))],
        Partial::Partial,
    )
}

/// Compile a let binding match (with optimization for simple cases).
/// Equivalent to OCaml's `for_let`.
pub fn for_let<B: RawLambdaBuilder>(
    env: MatchEnv<'_, B>,
    loc: Location,
    param: RawLambda,
    pat: &Pattern,
    body: RawLambda,
) -> RawLambda {
    let b = env.arena.b;
    match &pat.pat_desc {
        PatternDesc::Tpat_any => {
            // Eliminates a useless variable
            b.seq(param, body)
        }
        PatternDesc::Tpat_var(id, _) => {
            // Fast path
            b.let_(LetKind::Strict, *id, param, body)
        }
        _ => simple_for_let(env, loc, param, pat, body),
    }
}

/// Compile a tupled function match.
/// Equivalent to OCaml's `for_tupled_function`.
pub fn for_tupled_function<B: RawLambdaBuilder>(
    env: MatchEnv<'_, B>,
    loc: Location,
    paraml: &[Ident],
    pats_act_list: Vec<(Vec<&Pattern>, CaseAction)>,
    partial: Partial,
) -> RawLambda {
    let MatchEnv {
        ctx_ref,
        ta,
        arena,
        next_raise_count,
    } = env;
    let store = PatStore::default();
    let pa = PatArena::new(ta, &store);
    for_tupled_function_unresolved(
        MatchCx {
            ctx_ref,
            pa: &pa,
            arena,
        },
        loc,
        paraml,
        pats_act_list,
        partial,
        next_raise_count,
    )
}

fn for_tupled_function_unresolved<'p, B: RawLambdaBuilder>(
    cx: MatchCx<'p, '_, B>,
    loc: Location,
    paraml: &[Ident],
    pats_act_list: Vec<(Vec<&'p Pattern>, CaseAction)>,
    partial: Partial,
    next_raise_count: &mut i32,
) -> RawLambda {
    let MatchCx { pa, arena, .. } = cx;
    let b = arena.b;
    let pats_act_list: Vec<Clause<'p>> = pats_act_list
        .into_iter()
        .map(|(pats, act)| (pats, MatchAction::from_case(act)))
        .collect();
    let partial = check_partial_list(pa, &pats_act_list, partial);
    let raise_num = bump_raise_count(next_raise_count);
    let omegas_row: Vec<Vec<&'p Pattern>> = vec![omegas(paraml.len())];
    let pm = PatternMatching {
        cases: pats_act_list,
        args: MatchArgs::new(paraml.iter().map(|id| (b.var(*id), LetKind::Strict))),
        default: vec![(omegas_row, raise_num)],
    };
    match compile_match_owned(cx, &partial, &start_ctx(paraml.len()), pm, next_raise_count) {
        Ok((lambda, total)) => {
            let loc_clone = loc;
            check_total(b, &total, lambda, raise_num, || {
                partial_function(arena, loc_clone)
            })
        }
        Err(Unused) => partial_function(arena, loc),
    }
}

/// Cannot_flatten exception — used by flatten_pattern.
struct CannotFlattenExn;

/// Flatten a pattern into its tuple components.
/// Equivalent to OCaml's `flatten_pattern`.
fn flatten_pattern<'p>(
    pa: &PatArena<'p>,
    size: usize,
    p: &'p Pattern,
) -> Result<Vec<&'p Pattern>, CannotFlattenExn> {
    match &p.pat_desc {
        PatternDesc::Tpat_tuple(args) => Ok(pa.pats(*args).collect()),
        PatternDesc::Tpat_any => Ok(omegas(size)),
        _ => Err(CannotFlattenExn),
    }
}

/// Flatten a pattern line (possibly through or-patterns and aliases).
/// Equivalent to OCaml's `flatten_pat_line`.
fn flatten_pat_line<'p>(
    pa: &PatArena<'p>,
    size: usize,
    p: &'p Pattern,
    k: Vec<Vec<&'p Pattern>>,
) -> Result<Vec<Vec<&'p Pattern>>, CannotFlattenExn> {
    match &p.pat_desc {
        PatternDesc::Tpat_any => {
            let mut result = vec![omegas(size)];
            result.extend(k);
            Ok(result)
        }
        PatternDesc::Tpat_tuple(args) => {
            let mut result = vec![pa.pats(*args).collect()];
            result.extend(k);
            Ok(result)
        }
        PatternDesc::Tpat_or(p1, p2, _) => {
            let k = flatten_pat_line(pa, size, pa.pat(*p2), k)?;
            flatten_pat_line(pa, size, pa.pat(*p1), k)
        }
        PatternDesc::Tpat_alias(p, _, _) => flatten_pat_line(pa, size, pa.pat(*p), k),
        _ => Err(CannotFlattenExn),
    }
}

/// Flatten all cases.
/// Equivalent to OCaml's `flatten_cases`.
fn flatten_cases<'p>(
    pa: &PatArena<'p>,
    size: usize,
    cases: &[Clause<'p>],
) -> Result<Vec<Clause<'p>>, CannotFlattenExn> {
    cases
        .iter()
        .map(|(ps, action)| match ps.as_slice() {
            [p] => Ok((flatten_pattern(pa, size, p)?, action.clone())),
            _ => Err(CannotFlattenExn),
        })
        .collect()
}

/// Flatten a matrix.
/// Equivalent to OCaml's `flatten_matrix`.
fn flatten_matrix<'p>(
    pa: &PatArena<'p>,
    size: usize,
    pss: &Matrix<'p>,
) -> Result<Matrix<'p>, CannotFlattenExn> {
    pss.iter()
        .rev()
        .try_fold(Vec::new(), |r, ps| match ps.as_slice() {
            [p] => flatten_pat_line(pa, size, p, r),
            _ => Err(CannotFlattenExn),
        })
}

/// Flatten default environment.
/// Equivalent to OCaml's `flatten_def`.
fn flatten_def<'p>(
    pa: &PatArena<'p>,
    size: usize,
    def: &DefaultEnv<'p>,
) -> Result<DefaultEnv<'p>, CannotFlattenExn> {
    def.iter()
        .map(|(pss, i)| Ok((flatten_matrix(pa, size, pss)?, *i)))
        .collect()
}

/// Flatten a pattern matching.
/// Equivalent to OCaml's `flatten_pm`.
fn flatten_pm<'p>(
    pa: &PatArena<'p>,
    size: usize,
    args: MatchArgs,
    pm: &PatternMatching<'p>,
) -> Result<PatternMatching<'p>, CannotFlattenExn> {
    Ok(PatternMatching {
        args,
        cases: flatten_cases(pa, size, &pm.cases)?,
        default: flatten_def(pa, size, &pm.default)?,
    })
}

/// Flatten a precompiled pattern matching.
/// Equivalent to OCaml's `flatten_precompiled`.
fn flatten_precompiled<'p>(
    pa: &PatArena<'p>,
    size: usize,
    args: &MatchArgs,
    pmh: PmHalfCompiled<'p>,
) -> Result<PmHalfCompiled<'p>, CannotFlattenExn> {
    match pmh {
        PmHalfCompiled::Pm(pm) => Ok(PmHalfCompiled::Pm(flatten_pm(pa, size, args.clone(), &pm)?)),
        PmHalfCompiled::PmOr(PmOrCompiled {
            body,
            handlers,
            or_matrix,
        }) => {
            let flat_body = flatten_pm(pa, size, args.clone(), &body)?;
            let flat_handlers: Vec<_> = handlers
                .into_iter()
                .map(|(mat, i, vars, pm)| {
                    let flat_mat = flatten_matrix(pa, size, &mat)?;
                    Ok((flat_mat, i, vars, pm))
                })
                .collect::<Result<_, CannotFlattenExn>>()?;
            let flat_or_matrix = flatten_matrix(pa, size, &or_matrix)?;
            Ok(PmHalfCompiled::PmOr(PmOrCompiled {
                body: flat_body,
                handlers: flat_handlers,
                or_matrix: flat_or_matrix,
            }))
        }
        PmHalfCompiled::PmVar(_) => panic!("flatten_precompiled: PmVar"),
    }
}

/// Compiled_flattened: a comp_fun argument to comp_match_handlers.
/// Hence it needs a fourth argument (arg), which it ignores.
/// Equivalent to OCaml's `compile_flattened`.
fn compile_flattened<'p, B: RawLambdaBuilder>(
    cx: MatchCx<'p, '_, B>,
    partial: &Partial,
    ctx: &[Ctx<'p>],
    _arg: &RawLambda,
    pmh: &PmHalfCompiled<'p>,
    next_raise_count: &mut i32,
) -> Result<Compiled<'p>, Unused> {
    let MatchCx { pa, arena, .. } = cx;
    let b = arena.b;
    match pmh {
        PmHalfCompiled::Pm(pm) => compile_match(cx, None, partial, ctx, pm, next_raise_count),
        PmHalfCompiled::PmOr(PmOrCompiled { body, handlers, .. }) => {
            let (lam, total) = compile_match(cx, None, partial, ctx, body, next_raise_count)?;
            let mut compile_fn =
                |ctx: &[Ctx<'p>], pm: &PatternMatching<'p>| -> Result<Compiled<'p>, Unused> {
                    compile_match(cx, None, partial, ctx, pm, next_raise_count)
                };
            Ok(compile_orhandlers(
                b,
                pa,
                &mut compile_fn,
                lam,
                total,
                ctx,
                handlers,
            ))
        }
        PmHalfCompiled::PmVar(_) => panic!("compile_flattened: PmVar"),
    }
}

/// Compile a multiple-match expression (tuple patterns on arguments).
/// Equivalent to OCaml's `do_for_multiple_match`.
fn do_for_multiple_match<'p, B: RawLambdaBuilder>(
    cx: MatchCx<'p, '_, B>,
    loc: Location,
    paraml: Vec<RawLambda>,
    pat_act_list: Vec<(&'p Pattern, CaseAction)>,
    partial: Partial,
    next_raise_count: &mut i32,
) -> RawLambda {
    let MatchCx { ctx_ref, pa, arena } = cx;
    let b = arena.b;
    let partial = check_partial_single(pa, &pat_act_list, partial);
    // OCaml `compiler/ml/matching.ml:3846-3852` builds the matrix from the
    // incoming action list directly. Rust owns `pat_act_list` here, so move
    // actions into the shared `MatchAction` wrapper instead of recursively
    // cloning each raw-lambda action before the matrix transformations.
    let cases: Vec<Clause<'p>> = pat_act_list
        .into_iter()
        .map(|(pat, act)| (vec![pat], MatchAction::from_case(act)))
        .collect();
    let tuple_arg = b.prim(
        Primitive::Pmakeblock(TagInfo::Tuple, Mutable::Immutable),
        &paraml.clone(),
        arena.locs.intern(loc),
    );
    let (raise_num, pm1) = match &partial {
        Partial::Partial => {
            let raise_num = bump_raise_count(next_raise_count);
            (
                raise_num,
                PatternMatching {
                    cases,
                    args: MatchArgs::new([(tuple_arg, LetKind::Strict)]),
                    default: vec![(vec![vec![omega()]], raise_num)],
                },
            )
        }
        Partial::Total => (
            -1,
            PatternMatching {
                cases,
                args: MatchArgs::new([(tuple_arg, LetKind::Strict)]),
                default: Vec::new(),
            },
        ),
    };

    // Try flatten optimization first
    let result = (|| -> Result<RawLambda, CannotFlattenExn> {
        let (next, nexts) =
            split_precompile(Some(ctx_ref), pa, arena, &None, &pm1, next_raise_count);

        let size = paraml.len();

        // Debug: print what split_precompile produced
        let idl: Vec<Ident> = paraml
            .iter()
            .map(|_| ctx_ref.create_ident("match"))
            .collect();
        let args = MatchArgs::new(idl.iter().map(|id| (b.var(*id), LetKind::Alias)));

        let flat_next = flatten_precompiled(pa, size, &args, next)?;
        let flat_nexts: Vec<(i32, PmHalfCompiled<'_>)> = nexts
            .into_iter()
            .map(|(e, pm)| {
                let flat = flatten_precompiled(pa, size, &args, pm)?;
                Ok((e, flat))
            })
            .collect::<Result<_, CannotFlattenExn>>()?;

        let mut compile_fn = |partial: &Partial,
                              ctx: &[Ctx<'p>],
                              arg: &RawLambda,
                              pmh: &PmHalfCompiled<'p>|
         -> Result<Compiled<'p>, Unused> {
            compile_flattened(cx, partial, ctx, arg, pmh, next_raise_count)
        };

        let dummy_arg = b.const_(crate::lambda::Constant::int(0));
        let (lam, total) = comp_match_handlers(
            cx,
            &mut compile_fn,
            &partial,
            &start_ctx(size),
            &dummy_arg,
            &flat_next,
            &flat_nexts,
        )
        .map_err(|_| CannotFlattenExn)?;

        let result = idl.iter().zip(paraml.iter()).rev().fold(
            match &partial {
                Partial::Partial => {
                    let loc_clone = loc;
                    check_total(b, &total, lam, raise_num, || {
                        partial_function(arena, loc_clone)
                    })
                }
                Partial::Total => {
                    assert!(jumps_is_empty(&total));
                    lam
                }
            },
            |body, (id, param)| bind(b, LetKind::Strict, id, param, body),
        );
        Ok(result)
    })();

    match result {
        Ok(lam) => lam,
        Err(CannotFlattenExn) => {
            // Fallback: compile without flattening
            match compile_match_owned(cx, &partial, &start_ctx(1), pm1, next_raise_count) {
                Ok((lambda, total)) => match &partial {
                    Partial::Partial => {
                        let loc_clone = loc;
                        check_total(b, &total, lambda, raise_num, || {
                            partial_function(arena, loc_clone)
                        })
                    }
                    Partial::Total => {
                        assert!(jumps_is_empty(&total));
                        lambda
                    }
                },
                Err(Unused) => panic!("do_for_multiple_match: Unused"),
            }
        }
    }
}

/// Extract a variable from a param, binding if needed.
/// Equivalent to OCaml's `param_to_var`.
fn param_to_var<B: RawLambdaBuilder>(
    b: &B,
    ctx_ref: &TypeContext,
    param: &RawLambda,
) -> (Ident, Option<RawLambda>) {
    match b.as_var(*param) {
        Some(v) => (v, None),
        None => (ctx_ref.create_ident("match"), Some(*param)),
    }
}

/// Optionally bind a variable.
/// Equivalent to OCaml's `bind_opt`.
fn bind_opt<B: RawLambdaBuilder>(
    b: &B,
    v_eo: (Ident, Option<RawLambda>),
    k: RawLambda,
) -> RawLambda {
    match v_eo {
        (_, None) => k,
        (v, Some(e)) => bind(b, LetKind::Strict, &v, &e, k),
    }
}

/// Compile a multiple match expression.
/// Equivalent to OCaml's `for_multiple_match`.
pub fn for_multiple_match<B: RawLambdaBuilder>(
    env: MatchEnv<'_, B>,
    loc: Location,
    paraml: Vec<RawLambda>,
    pat_act_list: Vec<(&Pattern, CaseAction)>,
    partial: Partial,
) -> RawLambda {
    let MatchEnv {
        ctx_ref,
        ta,
        arena,
        next_raise_count,
    } = env;
    let b = arena.b;
    let v_paraml: Vec<(Ident, Option<RawLambda>)> = paraml
        .iter()
        .map(|param| param_to_var(b, ctx_ref, param))
        .collect();
    let new_paraml: Vec<RawLambda> = v_paraml.iter().map(|(v, _)| b.var(*v)).collect();
    let store = PatStore::default();
    let pa = PatArena::new(ta, &store);
    let pat_act_list = lower_dict_patterns(ctx_ref, &pa, pat_act_list);
    let inner = do_for_multiple_match(
        MatchCx {
            ctx_ref,
            pa: &pa,
            arena,
        },
        loc,
        new_paraml,
        pat_act_list,
        partial,
        next_raise_count,
    );
    v_paraml
        .into_iter()
        .rev()
        .fold(inner, |body, v_eo| bind_opt(b, v_eo, body))
}

#[cfg(test)]
mod tests {
    use crate::raw_lambda::RawArena;
    fn empty_ctxs<'p>(n: usize) -> Vec<super::Ctx<'p>> {
        (0..n)
            .map(|_| super::Ctx {
                left: Vec::new(),
                right: Vec::new(),
            })
            .collect()
    }

    fn keys(jumps: &super::Jumps<'_>) -> Vec<(i32, usize)> {
        jumps.iter().map(|(i, pss)| (*i, pss.len())).collect()
    }

    #[test]
    fn jumps_tables_stay_sorted_descending_and_merge_equal_exits() {
        use super::*;
        let ta = TypedArena::new();
        let store = PatStore::default();
        let pa = &PatArena::new(&ta, &store);
        let a: Jumps<'_> = vec![(9, empty_ctxs(1)), (5, empty_ctxs(2)), (1, empty_ctxs(1))];
        let b: Jumps<'_> = vec![(7, empty_ctxs(1)), (5, empty_ctxs(1)), (0, empty_ctxs(3))];
        // Equal empty contexts are mutually `le_ctx`, so get_mins keeps one.
        let u = jumps_union(pa, a.clone(), b);
        assert_eq!(keys(&u), vec![(9, 1), (7, 1), (5, 1), (1, 1), (0, 3)]);

        let added = jumps_add(pa, 6, empty_ctxs(2), a.clone());
        assert_eq!(keys(&added), vec![(9, 1), (6, 2), (5, 2), (1, 1)]);
        let added = jumps_add(pa, 5, empty_ctxs(1), a.clone());
        assert_eq!(keys(&added), vec![(9, 1), (5, 1), (1, 1)]);
        let added = jumps_add(pa, -3, empty_ctxs(1), a.clone());
        assert_eq!(keys(&added), vec![(9, 1), (5, 2), (1, 1), (-3, 1)]);
        assert_eq!(keys(&jumps_add(pa, 4, Vec::new(), a.clone())), keys(&a));

        let (ctx, rest) = jumps_extract(5, a.clone());
        assert_eq!(ctx.len(), 2);
        assert_eq!(keys(&rest), vec![(9, 1), (1, 1)]);
        let (ctx, rest) = jumps_extract(4, a.clone());
        assert!(ctx.is_empty());
        assert_eq!(keys(&rest), keys(&a));

        assert_eq!(keys(&jumps_remove(1, a.clone())), vec![(9, 1), (5, 2)]);
        assert_eq!(keys(&jumps_remove(3, a.clone())), keys(&a));
    }

    use super::*;
    use crate::context::IdGenerator;
    use crate::raw_lambda::typeopt::find_type_decl;
    use crate::types::decl::TypeKind;
    use crate::types::env::initial_env;
    use crate::types::predef;
    use crate::types::type_expr::TypeDesc;

    #[test]
    fn constructor_cases_use_pattern_env_layout() {
        let id_gen = IdGenerator::new();
        let ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let env = initial_env(&ctx);
        let env_ref = ctx.store_typed_env(&env);
        let pat_type = ctx.new_generic_constr(
            predef::path_result(),
            vec![ctx.new_var(None), ctx.new_var(None)],
        );
        let pat = make_pat(PatternDesc::Tpat_any, pat_type, env_ref);

        let pat_env = ctx.get_typed_env(pat.pat_env).expect("pattern environment");
        let TypeDesc::Tconstr { path, .. } = &*ctx.get_desc(ctx.repr(pat.pat_type)) else {
            panic!("expected result constructor");
        };
        let decl = find_type_decl(&ctx, pat_env.as_ref(), path).expect("result declaration");
        let TypeKind::TypeVariant(_, layout_ref) = decl.type_kind else {
            panic!("expected result variant layout");
        };
        let layout = ctx.variant_layout(layout_ref);
        let names: Vec<_> = layout
            .constructors
            .iter()
            .map(|case| match case {
                crate::types::VariantConstructorCase::Block(block) => block.tag().name.as_str(),
                crate::types::VariantConstructorCase::Constant(tag) => tag.name.as_str(),
            })
            .collect();

        assert_eq!(names, vec!["Ok", "Error"]);
        assert!(
            layout
                .constructors
                .iter()
                .all(|case| matches!(case, crate::types::VariantConstructorCase::Block(_)))
        );
    }

    #[test]
    fn make_key_equals_compares_while_writing() {
        let b = RawArena::new();
        let x = Ident::create_local("x");
        let y = Ident::create_local("y");
        let one = || {
            b.const_(crate::lambda::lam_constant::Constant::Int {
                i: 1,
                comment: None,
            })
        };
        // A strict let whose body is not its variable is keyed with a
        // synthetic stamp, which a diverged comparison must not fail on.
        let key_term = |id: Ident, v: RawLambda| {
            b.let_(
                LetKind::Strict,
                id,
                v,
                b.prim(Primitive::Paddint, &[b.var(id), b.var(y)], LamLoc::NONE),
            )
        };
        let first = key_term(x, one());
        let key = make_key_string(&b, first).expect("small term has a key");
        // A let of another identifier with the same name keys the same.
        let same_name = Ident::create_local("x");
        assert!(make_key_equals(&b, key_term(same_name, one()), &key));
        assert!(!make_key_equals(&b, key_term(x, b.var(y)), &key));
        assert!(!make_key_equals(&b, one(), &key));
        assert!(!make_key_equals(&b, b.var(y), &key));
    }

    #[test]
    fn or_list_polyvar_keeps_named_hash_metadata() {
        let b = RawArena::new();
        let arg = b.var(Ident::create_local("match"));
        let raw = or_list_polyvar(
            &b,
            &arg,
            &[
                (btype::hash_variant("A"), "A".to_string()),
                (btype::hash_variant("B"), "B".to_string()),
            ],
        );

        let a = b.get();
        let View::Prim(_, [first_eq, second_eq], _) = a.view(raw) else {
            panic!("expected sequor chain over two equality tests");
        };
        for (test, name) in [(*first_eq, "A"), (*second_eq, "B")] {
            let View::Prim(_, [var, hash], _) = a.view(test) else {
                panic!("expected an equality test");
            };
            assert!(a.as_var(*var).is_some());
            assert!(matches!(
                a.as_const(*hash),
                Some(crate::lambda::lam_constant::Constant::Int { i, comment: Some(comment) })
                    if *i == btype::hash_variant(name)
                        && matches!(&**comment, PointerInfo::PolyVariant(n) if n == name)
            ));
        }
    }
}
