//! `Lam_pass_count.collect_occurs` and `Lam_pass_lets_dce.simplify_lets`
//! over the Lambda arena.

use ahash::AHashMap as HashMap;

use crate::ident::Ident;
use crate::lambda::arena::{Lam, LamArena, Node};
use crate::lambda::lam_analysis_arena::{lfunction_can_be_inlined, no_side_effects};
use crate::lambda::lam_beta_reduce_arena::no_names_beta_reduce;
use crate::lambda::lam_compat::LetKind;
use crate::lambda::lam_constant::Constant;
use crate::lambda::lam_primitive::Primitive;
use crate::lambda::lam_util_arena::refine_let_original;

/// Equivalent of OCaml's `Lam_pass_count.used_info` (lam_pass_count.ml:15-23).
/// `Default` is OCaml's `dummy_info` (lam_pass_count.ml:30).
#[derive(Debug, Default, Clone, Copy)]
pub struct UsedInfo {
    /// Number of references to the binding.
    pub times: u32,
    /// True when at least one reference appears under a lambda or loop body
    /// (lam_pass_count.ml:17-22).
    pub captured: bool,
}

/// Equivalent of OCaml's `absorb_info` (lam_pass_count.ml:33-37). Adds `y`'s
/// count into `x` and propagates the captured flag.
fn absorb_info(x: &mut UsedInfo, y: UsedInfo) {
    x.times = x.times.saturating_add(y.times);
    if y.captured {
        x.captured = true;
    }
}

/// Occurrence table mirroring OCaml's `Hash_ident.t` of mutable `used_info`
/// records (lam_pass_count.ml:25-26). Each binding owns a slot in `values`;
/// `entries` maps an ident to the slot of its most recent binding, so a
/// rebinding gets a fresh slot while outer scopes keep pointing at theirs.
#[derive(Default)]
pub(crate) struct OccurrenceTable {
    pub(crate) entries: HashMap<Ident, usize>,
    pub(crate) values: Vec<UsedInfo>,
}

impl OccurrenceTable {
    /// The info of the latest binding of `id`, or the default
    /// (lam_pass_count.ml:30).
    pub(crate) fn get(&self, id: &Ident) -> UsedInfo {
        self.entries
            .get(id)
            .map(|index| self.values[*index])
            .unwrap_or_default()
    }

    /// Allocate a fresh slot for `id` (lam_pass_count.ml:69-73).
    pub(crate) fn bind(&mut self, id: &Ident) -> usize {
        let index = self.values.len();
        self.values.push(UsedInfo::default());
        self.entries.insert(*id, index);
        index
    }

    pub(crate) fn used(&self, id: &Ident) -> bool {
        self.get(id).times > 0
    }

    /// `absorb_info` (lam_pass_count.ml:33-37) applied to a slot.
    pub(crate) fn absorb(&mut self, index: usize, other: UsedInfo) {
        absorb_info(&mut self.values[index], other);
    }
}

/// Bindings in scope, pointing at their slots of the occurrence table
/// (`local_tbl = used_info Map_ident.t`, lam_pass_count.ml:28).
type LocalTbl = HashMap<Ident, usize>;

/// `Lam_pass_count.collect_occurs` (lam_pass_count.ml:59-203).
///
/// Needs the arena mutably: applications of inlinable functions are counted
/// on their beta-reduced form, which is built here.
pub(crate) fn collect_occurs(a: &mut LamArena, lam: Lam) -> OccurrenceTable {
    let mut occ = OccurrenceTable::default();
    let mut bv = LocalTbl::new();
    count(a, &mut occ, &mut bv, lam);
    occ
}

/// `bind_var` (lam_pass_count.ml:69-73). Returns the shadowed slot.
fn bind_var(occ: &mut OccurrenceTable, bv: &mut LocalTbl, id: &Ident) -> Option<usize> {
    let index = occ.bind(id);
    bv.insert(*id, index)
}

fn restore_var(bv: &mut LocalTbl, id: &Ident, previous: Option<usize>) {
    match previous {
        Some(previous) => {
            bv.insert(*id, previous);
        }
        None => {
            bv.remove(id);
        }
    }
}

/// `add_one_use` (lam_pass_count.ml:76-89).
fn add_one_use(occ: &mut OccurrenceTable, bv: &LocalTbl, id: &Ident) {
    if let Some(&index) = bv.get(id) {
        occ.values[index].times += 1;
    } else if let Some(&index) = occ.entries.get(id) {
        occ.absorb(
            index,
            UsedInfo {
                times: 1,
                captured: true,
            },
        );
    }
}

/// `inherit_use` (lam_pass_count.ml:91-108).
fn inherit_use(occ: &mut OccurrenceTable, bv: &LocalTbl, id: &Ident, bid: &Ident) {
    let n = occ.get(bid);
    if let Some(&index) = bv.get(id) {
        occ.absorb(index, n);
    } else if let Some(&index) = occ.entries.get(id) {
        occ.absorb(
            index,
            UsedInfo {
                captured: true,
                ..n
            },
        );
    }
}

/// `count` (lam_pass_count.ml:110-201).
fn count(a: &mut LamArena, occ: &mut OccurrenceTable, bv: &mut LocalTbl, lam: Lam) {
    match a.node(lam) {
        Node::Function { body, .. } => count(a, occ, &mut LocalTbl::new(), body),
        Node::For { kids, .. } => {
            let (start, finish, body) = a.for_parts(kids);
            count(a, occ, bv, start);
            count(a, occ, bv, finish);
            count(a, occ, &mut LocalTbl::new(), body);
        }
        Node::ForOf { iter, body, .. } | Node::ForAwaitOf { iter, body, .. } => {
            count(a, occ, bv, iter);
            count(a, occ, &mut LocalTbl::new(), body);
        }
        Node::While(c, b) => {
            let mut empty = LocalTbl::new();
            count(a, occ, &mut empty, c);
            count(a, occ, &mut empty, b);
        }
        Node::Var(v) => add_one_use(occ, bv, &a.ident(v)),
        Node::Let {
            kind,
            id,
            value,
            body,
        } => {
            let v = a.ident(id);
            if let Some(w) = a.as_var(value) {
                // lam_pass_count.ml:126-130
                let previous = bind_var(occ, bv, &v);
                count(a, occ, bv, body);
                restore_var(bv, &v, previous);
                inherit_use(occ, bv, &w, &v);
            } else {
                // lam_pass_count.ml:131-135
                let previous = bind_var(occ, bv, &v);
                count(a, occ, bv, body);
                restore_var(bv, &v, previous);
                if matches!(kind, LetKind::Strict) || occ.used(&v) {
                    count(a, occ, bv, value);
                }
            }
        }
        Node::Assign { value, .. } => count(a, occ, bv, value),
        Node::Apply { func, args, .. } => {
            if let Node::Function { body, info } = a.node(func)
                && a.params(info).len() == a.list_len(args)
                && lfunction_can_be_inlined(a, info)
            {
                // lam_pass_count.ml:146-150
                let params: smallvec::SmallVec<[Ident; 8]> =
                    a.params(info).iter().copied().collect();
                let args = a.list_vec(args);
                let reduced = no_names_beta_reduce(a, &params, body, &args);
                count(a, occ, bv, reduced);
            } else {
                count(a, occ, bv, func);
                for x in a.list_vec(args) {
                    count(a, occ, bv, x);
                }
            }
        }
        // lam_pass_count.ml:159-163, 189-200: the default first, twice when
        // neither table is full.
        Node::Switch {
            scrut,
            actions,
            info,
        } => {
            let p = a.switch_payload(info);
            let (consts_full, blocks_full) = (p.consts_full, p.blocks_full);
            let acts = a.switch_actions(info, actions);
            let fail = acts.fail;
            let cases: smallvec::SmallVec<[Lam; 8]> =
                acts.consts.iter().chain(acts.blocks).copied().collect();
            if let Some(fail) = fail {
                count(a, occ, bv, fail);
                if !consts_full && !blocks_full {
                    count(a, occ, bv, fail);
                }
            }
            count(a, occ, bv, scrut);
            for x in cases {
                count(a, occ, bv, x);
            }
        }
        _ => {
            let mut kids: smallvec::SmallVec<[Lam; 8]> = smallvec::SmallVec::new();
            a.iter_children(lam, |x| kids.push(x));
            for x in kids {
                count(a, occ, bv, x);
            }
        }
    }
}

/// `Lam_pass_lets_dce.simplify_lets` (lam_pass_lets_dce.ml:216-219).
pub fn simplify_lets(a: &mut LamArena, lam: Lam) -> Lam {
    let occ = collect_occurs(a, lam);
    let mut state = LetsState {
        occ: &occ,
        subst: HashMap::with_capacity(32),
        string_table: HashMap::with_capacity(32),
    };
    state.simplif(a, lam)
}

/// `lets_helper`'s substitution and string tables (lam_pass_lets_dce.ml:15-16).
struct LetsState<'a> {
    occ: &'a OccurrenceTable,
    subst: HashMap<Ident, Lam>,
    string_table: HashMap<Ident, String>,
}

impl LetsState<'_> {
    fn used(&self, v: &Ident) -> bool {
        self.occ.get(v).times > 0
    }

    fn string_of(&self, a: &LamArena, lam: Lam) -> Option<String> {
        match a.node(lam) {
            Node::Const(c) => match a.constant(c) {
                Constant::String(s) => Some(s.clone()),
                _ => None,
            },
            Node::Var(i) => self.string_table.get(&a.ident(i)).cloned(),
            _ => None,
        }
    }

    fn const_string(a: &LamArena, lam: Lam) -> Option<String> {
        match a.as_const(lam) {
            Some(Constant::String(s)) => Some(s.clone()),
            _ => None,
        }
    }

    /// `simplif` in `Lam_pass_lets_dce.lets_helper` (lam_pass_lets_dce.ml:14-140).
    fn simplif(&mut self, a: &mut LamArena, lam: Lam) -> Lam {
        match a.node(lam) {
            Node::Var(v) => self.subst.get(&a.ident(v)).copied().unwrap_or(lam),
            Node::Let {
                kind,
                id,
                value,
                body,
            } => {
                let v = a.ident(id);
                if matches!(a.node(value), Node::Var(_))
                    && matches!(kind, LetKind::Strict | LetKind::Alias | LetKind::StrictOpt)
                {
                    let w = self.simplif(a, value);
                    self.subst.insert(v, w);
                    return self.simplif(a, body);
                }
                match kind {
                    LetKind::Alias => self.simplif_alias(a, v, value, body),
                    LetKind::StrictOpt => {
                        if !self.used(&v) {
                            return self.simplif(a, body);
                        }
                        let new_value = self.simplif(a, value);
                        if let Some(s) = Self::const_string(a, new_value) {
                            self.string_table.insert(v, s);
                            let body = self.simplif(a, body);
                            return a.let_(LetKind::Alias, v, new_value, body);
                        }
                        let new_body = self.simplif(a, body);
                        refine_let_original(a, lam, LetKind::StrictOpt, v, new_value, new_body)
                    }
                    LetKind::Strict | LetKind::Variable => {
                        if !self.used(&v) {
                            let new_value = self.simplif(a, value);
                            let new_body = self.simplif(a, body);
                            return if no_side_effects(a, new_value) {
                                new_body
                            } else {
                                a.seq(new_value, new_body)
                            };
                        }
                        let new_value = self.simplif(a, value);
                        if matches!(kind, LetKind::Strict)
                            && let Some(s) = Self::const_string(a, new_value)
                        {
                            self.string_table.insert(v, s);
                            let body = self.simplif(a, body);
                            return a.let_(LetKind::Alias, v, new_value, body);
                        }
                        let new_body = self.simplif(a, body);
                        refine_let_original(a, lam, kind, v, new_value, new_body)
                    }
                }
            }
            Node::Apply { func, args, .. } => {
                if let Node::Function { body, info } = a.node(func)
                    && a.params(info).len() == a.list_len(args)
                    && lfunction_can_be_inlined(a, info)
                {
                    let params: smallvec::SmallVec<[Ident; 8]> =
                        a.params(info).iter().copied().collect();
                    let args = a.list_vec(args);
                    let reduced = no_names_beta_reduce(a, &params, body, &args);
                    return self.simplif(a, reduced);
                }
                a.shallow_map(lam, &mut |a, x| self.simplif(a, x))
            }
            Node::Prim { args, info }
                if matches!(a.prim_payload(info).primitive, Primitive::Pstringadd)
                    && a.list_len(args) == 2 =>
            {
                let [l, r] = *a.list(args) else {
                    unreachable!()
                };
                let l = self.simplif(a, l);
                let r = self.simplif(a, r);
                let folded = self
                    .string_of(a, l)
                    .and_then(|ls| self.string_of(a, r).map(|rs| ls + &rs));
                match folded {
                    Some(s) => a.const_(Constant::String(s)),
                    None => {
                        let args = a.add_list(&[l, r]);
                        a.prim_with(info, args)
                    }
                }
            }
            _ => a.shallow_map(lam, &mut |a, x| self.simplif(a, x)),
        }
    }

    /// The `Llet (Alias, v, l1, l2)` arm (lam_pass_lets_dce.ml:30-69).
    fn simplif_alias(&mut self, a: &mut LamArena, v: Ident, l1: Lam, l2: Lam) -> Lam {
        let info = self.occ.get(&v);
        if info.times == 0 {
            return self.simplif(a, l2);
        }
        let small_const = matches!(
            a.as_const(l1),
            Some(
                Constant::Int { .. }
                    | Constant::Constructor(_)
                    | Constant::NativeInt { .. }
                    | Constant::Char(_)
                    | Constant::Float(_)
                    | Constant::BigInt { .. }
                    | Constant::Pointer(_)
                    | Constant::JsTrue
                    | Constant::JsFalse
                    | Constant::JsUndefined { .. }
            )
        );
        let pfield_from_global = matches!(
            a.as_prim(l1),
            Some((Primitive::Pfield(_, _), [m], _)) if matches!(a.node(*m), Node::GlobalModule(_))
        );
        let atom = matches!(a.node(l1), Node::Const(_) | Node::Var(_));
        let subst_now = (info.times == 1 && !info.captured)
            || (info.times == 1 && info.captured && atom)
            || small_const
            || pfield_from_global;
        if subst_now {
            let simplified = self.simplif(a, l1);
            self.subst.insert(v, simplified);
            return self.simplif(a, l2);
        }
        if let Some(s) = Self::const_string(a, l1) {
            self.string_table.insert(v, s);
            let body = self.simplif(a, l2);
            return a.let_(LetKind::Alias, v, l1, body);
        }
        // The body before the bound expression, as OCaml does.
        let new_l2 = self.simplif(a, l2);
        let new_l1 = self.simplif(a, l1);
        a.let_(LetKind::Alias, v, new_l1, new_l2)
    }
}
