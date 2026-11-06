//! `Lam_closure` over the Lambda arena: free variables with usage statistics.

use ahash::{AHashMap as HashMap, AHashSet as HashSet};

use crate::ident::Ident;
use crate::lambda::arena::{Lam, LamArena, Node};
use crate::lambda::lam_analysis::no_side_effects;

/// High penalty for loop usage (variables used in loops can't be safely inlined).
const LOOP_USE: i32 = 100;

/// Variable usage statistics.
///
/// Tracks how a variable is used within an expression, which helps
/// determine if it's safe to inline.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VarStats {
    /// Whether all usages are in "top" position (safe for substitution).
    ///
    /// A variable is in top position if it appears before any side effects.
    /// For example, in `x + (print("hi"); y)`, `x` is in top position but
    /// `y` is not (because `print` has side effects).
    pub top: bool,

    /// Number of times the variable is used.
    pub times: i32,
}

impl VarStats {
    /// Create fresh statistics (unused, top position).
    pub fn fresh() -> Self {
        VarStats {
            top: true,
            times: 0,
        }
    }

    /// Create "sink" statistics for variables in loops.
    pub fn sink() -> Self {
        VarStats {
            top: false,
            times: LOOP_USE,
        }
    }

    /// Check if variable is used zero or one time in top position.
    ///
    /// Variables matching this pattern are safe to inline regardless
    /// of whether they're pure.
    pub fn top_and_used_zero_or_one(&self) -> bool {
        self.top && (self.times == 0 || self.times == 1)
    }

    /// Update statistics based on position.
    pub fn update(&mut self, pos: Position) {
        match pos {
            Position::Begin => {
                self.times += 1;
            }
            Position::NotBegin => {
                self.top = false;
                self.times += 1;
            }
            Position::Sink => {
                self.top = false;
                self.times = LOOP_USE;
            }
        }
    }
}

/// Position within an expression for tracking side effect boundaries.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Position {
    /// At the beginning (before any side effects).
    Begin,
    /// Not at the beginning (after some side effects).
    NotBegin,
    /// In a loop or other sink position (unsafe for substitution).
    Sink,
}

/// Type alias for variable statistics map.
pub type StatsMap = HashMap<Ident, VarStats>;

/// Identifiers bound while walking a closure body: the borrowed export set
/// plus the locals introduced so far. OCaml threads the immutable export set
/// and extends it persistently; borrowing it here avoids cloning the whole
/// export set on every analysis.
pub(crate) struct BoundIdents<'a> {
    exports: &'a HashSet<Ident>,
    local: HashSet<Ident>,
}

impl<'a> BoundIdents<'a> {
    pub(crate) fn new(exports: &'a HashSet<Ident>) -> Self {
        Self {
            exports,
            local: HashSet::new(),
        }
    }

    pub(crate) fn contains(&self, id: &Ident) -> bool {
        self.local.contains(id) || self.exports.contains(id)
    }

    pub(crate) fn insert(&mut self, id: Ident) {
        self.local.insert(id);
    }

    pub(crate) fn extend(&mut self, ids: impl IntoIterator<Item = Ident>) {
        self.local.extend(ids);
    }
}

/// Create a parameter statistics map from a list of identifiers.
pub fn param_map_of_list(params: &[Ident]) -> StatsMap {
    params.iter().map(|p| (*p, VarStats::fresh())).collect()
}

fn after_lam(a: &LamArena, pos: Position, lam: Lam) -> Position {
    if pos != Position::Begin || no_side_effects(a, lam) {
        pos
    } else {
        Position::NotBegin
    }
}

/// `Lam_closure.free_variables`.
pub fn free_variables_with_stats(
    a: &LamArena,
    exports: &HashSet<Ident>,
    params: StatsMap,
    lam: Lam,
) -> StatsMap {
    let mut fv = params;
    let mut local = BoundIdents::new(exports);
    iter(a, lam, Position::Begin, &mut fv, &mut local);
    fv
}

fn use_var(fv: &mut StatsMap, local: &BoundIdents<'_>, v: Ident, pos: Position) {
    if !local.contains(&v) {
        fv.entry(v).or_insert_with(VarStats::fresh).update(pos);
    }
}

fn iter(a: &LamArena, lam: Lam, pos: Position, fv: &mut StatsMap, local: &mut BoundIdents<'_>) {
    match a.node(lam) {
        Node::Var(v) => use_var(fv, local, a.ident(v), pos),
        Node::Const(_) | Node::GlobalModule(_) | Node::Break | Node::Continue => {}
        Node::Apply { func, args, .. } => {
            iter(a, func, pos, fv, local);
            let new_pos = after_lam(a, pos, func);
            for x in a.list(args) {
                iter(a, *x, new_pos, fv, local);
            }
        }
        Node::Prim { args, .. } => {
            for x in a.list(args) {
                iter(a, *x, pos, fv, local);
            }
        }
        Node::Function { body, info } => {
            local.extend(a.params(info).iter().copied());
            iter(a, body, Position::Sink, fv, local);
        }
        Node::Let {
            id, value, body, ..
        } => {
            iter(a, value, pos, fv, local);
            local.insert(a.ident(id));
            iter(a, body, Position::Sink, fv, local);
        }
        Node::LetRec { ids, values, body } => {
            let values = a.list(values);
            local.extend(a.ident_run(ids, values.len()).iter().copied());
            for x in values {
                iter(a, *x, Position::Sink, fv, local);
            }
            iter(a, body, Position::Sink, fv, local);
        }
        Node::Switch {
            scrut,
            actions,
            info,
        } => {
            iter(a, scrut, pos, fv, local);
            let new_pos = after_lam(a, pos, scrut);
            let acts = a.switch_actions(info, actions);
            for x in acts.consts.iter().chain(acts.blocks) {
                iter(a, *x, new_pos, fv, local);
            }
            if let Some(fail) = acts.fail {
                let p = a.switch_payload(info);
                let fail_pos = if p.consts_full || p.blocks_full {
                    new_pos
                } else {
                    Position::Sink
                };
                iter(a, fail, fail_pos, fv, local);
            }
        }
        Node::StringSwitch { scrut, actions, .. } => {
            iter(a, scrut, pos, fv, local);
            let new_pos = after_lam(a, pos, scrut);
            for x in a.list(actions) {
                iter(a, *x, new_pos, fv, local);
            }
        }
        Node::StaticRaise { args, .. } => {
            for x in a.list(args) {
                iter(a, *x, Position::Sink, fv, local);
            }
        }
        Node::StaticCatch {
            body,
            handler,
            info,
        } => {
            iter(a, body, Position::Sink, fv, local);
            local.extend(a.idents(a.catch_payload(info).params).iter().copied());
            iter(a, handler, Position::Sink, fv, local);
        }
        Node::TryWith { body, handler, .. } => {
            iter(a, body, pos, fv, local);
            iter(a, handler, Position::Sink, fv, local);
        }
        Node::If { cond, then_, else_ } => {
            iter(a, cond, pos, fv, local);
            let new_pos = after_lam(a, pos, cond);
            iter(a, then_, new_pos, fv, local);
            iter(a, else_, new_pos, fv, local);
        }
        Node::Sequence(x, y) => {
            iter(a, x, pos, fv, local);
            iter(a, y, Position::Sink, fv, local);
        }
        Node::While(x, y) => {
            iter(a, x, Position::Sink, fv, local);
            iter(a, y, Position::Sink, fv, local);
        }
        Node::For { id, kids, .. } => {
            local.insert(a.ident(id));
            for x in a.list(kids) {
                iter(a, *x, Position::Sink, fv, local);
            }
        }
        Node::ForOf { id, iter: it, body } | Node::ForAwaitOf { id, iter: it, body } => {
            local.insert(a.ident(id));
            iter(a, it, Position::Sink, fv, local);
            iter(a, body, Position::Sink, fv, local);
        }
        Node::Assign { id, value } => {
            use_var(fv, local, a.ident(id), pos);
            iter(a, value, pos, fv, local);
        }
    }
}

/// `Lam_closure.is_closed`: every free variable is global.
pub fn is_closed(a: &LamArena, lam: Lam) -> bool {
    free_variables_with_stats(a, &HashSet::new(), HashMap::new(), lam)
        .keys()
        .all(|k| k.is_global())
}

/// `Lam_closure.is_closed_with_map`.
pub fn is_closed_with_map(
    a: &LamArena,
    exports: &HashSet<Ident>,
    params: &[Ident],
    body: Lam,
) -> (bool, StatsMap) {
    let map = free_variables_with_stats(a, exports, param_map_of_list(params), body);
    (map.len() == params.len(), map)
}
