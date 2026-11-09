//! `Lam_pass_count.collect_occurs` and `Lam_pass_lets_dce.simplify_lets`
//! over the Lambda arena.

use ahash::AHashMap as HashMap;

use crate::ident::Ident;
use crate::lambda::arena::{Lam, LamArena, Node};
use crate::lambda::lam_analysis::{lfunction_can_be_inlined, no_side_effects};
use crate::lambda::lam_beta_reduce::no_names_beta_reduce;
use crate::lambda::lam_compat::LetKind;
use crate::lambda::lam_constant::Constant;
use crate::lambda::lam_primitive::Primitive;
use crate::lambda::lam_util::refine_let_original;

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

/// One identifier lookup finds both the latest occurrence slot and the active
/// lexical binding. Slots stay dense even when a binding is shadowed.
#[derive(Default)]
pub(crate) struct OccurrenceTable {
    entries: HashMap<Ident, BindingSlots>,
    pub(crate) values: Vec<UsedInfo>,
}

#[derive(Default)]
struct BindingSlots {
    latest: usize,
    active: Option<(usize, usize)>, // (capture scope depth, occurrence slot)
}

impl OccurrenceTable {
    pub(crate) fn get(&self, id: &Ident) -> UsedInfo {
        self.entries
            .get(id)
            .map(|slots| self.values[slots.latest])
            .unwrap_or_default()
    }

    pub(crate) fn used(&self, id: &Ident) -> bool {
        self.get(id).times > 0
    }

    pub(crate) fn absorb(&mut self, index: usize, other: UsedInfo) {
        absorb_info(&mut self.values[index], other);
    }
}

/// `Lam_pass_count.collect_occurs` (lam_pass_count.ml:59-203).
pub(crate) fn collect_occurs(a: &mut LamArena, lam: Lam) -> OccurrenceTable {
    let mut occ = OccurrenceTable::default();
    count(a, &mut occ, 0, lam);
    occ
}

fn bind_var(occ: &mut OccurrenceTable, scope: usize, id: &Ident) -> Option<(usize, usize)> {
    let index = occ.values.len();
    occ.values.push(UsedInfo::default());
    let slots = occ.entries.entry(*id).or_default();
    slots.latest = index;
    slots.active.replace((scope, index))
}

fn restore_var(occ: &mut OccurrenceTable, id: &Ident, previous: Option<(usize, usize)>) {
    occ.entries.get_mut(id).unwrap().active = previous;
}

/// The OCaml local table is empty across function and loop boundaries
/// (lam_pass_count.ml:110-123). A depth check expresses that without allocating
/// another map. Bindings are restored before leaving each body, so sibling
/// scopes cannot see one another's active slots.
fn use_slot(occ: &OccurrenceTable, scope: usize, id: &Ident) -> Option<(usize, bool)> {
    let slots = occ.entries.get(id)?;
    match slots.active {
        Some((binding_scope, index)) if binding_scope == scope => Some((index, false)),
        _ => Some((slots.latest, true)),
    }
}

fn add_one_use(occ: &mut OccurrenceTable, scope: usize, id: &Ident) {
    if let Some((index, captured)) = use_slot(occ, scope, id) {
        occ.values[index].times += 1;
        occ.values[index].captured |= captured;
    }
}

fn inherit_use(occ: &mut OccurrenceTable, scope: usize, id: &Ident, bid: &Ident) {
    let mut n = occ.get(bid);
    if let Some((index, captured)) = use_slot(occ, scope, id) {
        n.captured |= captured;
        occ.absorb(index, n);
    }
}

/// `count` (lam_pass_count.ml:110-201).
fn count(a: &mut LamArena, occ: &mut OccurrenceTable, scope: usize, lam: Lam) {
    match a.node(lam) {
        Node::Function { body, .. } => count(a, occ, scope + 1, body),
        Node::For { kids, .. } => {
            let (start, finish, body) = a.for_parts(kids);
            count(a, occ, scope, start);
            count(a, occ, scope, finish);
            count(a, occ, scope + 1, body);
        }
        Node::ForOf { iter, body, .. } | Node::ForAwaitOf { iter, body, .. } => {
            count(a, occ, scope, iter);
            count(a, occ, scope + 1, body);
        }
        Node::While(c, b) => {
            let inner_scope = scope + 1;
            count(a, occ, inner_scope, c);
            count(a, occ, inner_scope, b);
        }
        Node::Var(v) => add_one_use(occ, scope, &a.ident(v)),
        Node::Let {
            kind,
            id,
            value,
            body,
        } => {
            let v = a.ident(id);
            if let Some(w) = a.as_var(value) {
                // lam_pass_count.ml:126-130
                let previous = bind_var(occ, scope, &v);
                count(a, occ, scope, body);
                restore_var(occ, &v, previous);
                inherit_use(occ, scope, &w, &v);
            } else {
                // lam_pass_count.ml:131-135
                let previous = bind_var(occ, scope, &v);
                count(a, occ, scope, body);
                restore_var(occ, &v, previous);
                if matches!(kind, LetKind::Strict) || occ.used(&v) {
                    count(a, occ, scope, value);
                }
            }
        }
        Node::Assign { value, .. } => count(a, occ, scope, value),
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
                count(a, occ, scope, reduced);
            } else {
                count(a, occ, scope, func);
                for x in a.list_vec(args) {
                    count(a, occ, scope, x);
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
                count(a, occ, scope, fail);
                if !consts_full && !blocks_full {
                    count(a, occ, scope, fail);
                }
            }
            count(a, occ, scope, scrut);
            for x in cases {
                count(a, occ, scope, x);
            }
        }
        _ => {
            let mut kids: smallvec::SmallVec<[Lam; 8]> = smallvec::SmallVec::new();
            a.iter_children(lam, |x| kids.push(x));
            for x in kids {
                count(a, occ, scope, x);
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

#[cfg(test)]
mod occurrence_scope_tests {
    use super::*;

    #[test]
    fn shadowing_restores_active_slot_but_keeps_latest_occurrence() {
        let id = Ident::create_persistent("x");
        let mut occ = OccurrenceTable::default();
        let outer = bind_var(&mut occ, 0, &id);
        add_one_use(&mut occ, 0, &id);
        let inner = bind_var(&mut occ, 1, &id);
        add_one_use(&mut occ, 1, &id);
        restore_var(&mut occ, &id, inner);
        add_one_use(&mut occ, 0, &id);
        assert_eq!(occ.values[0].times, 2);
        assert!(!occ.values[0].captured);
        // A separate capture scope has an empty local table: it uses the
        // latest binding, rather than the restored outer lexical binding.
        add_one_use(&mut occ, 1, &id);
        assert_eq!(occ.get(&id).times, 2);
        assert!(occ.get(&id).captured);
        restore_var(&mut occ, &id, outer);
        assert!(occ.entries[&id].active.is_none());
    }

    #[test]
    fn captured_alias_use_is_inherited() {
        let x = Ident::create_persistent("x");
        let y = Ident::create_persistent("y");
        let mut occ = OccurrenceTable::default();
        bind_var(&mut occ, 0, &x);
        let previous = bind_var(&mut occ, 0, &y);
        add_one_use(&mut occ, 1, &y);
        restore_var(&mut occ, &y, previous);
        inherit_use(&mut occ, 0, &x, &y);
        assert_eq!(occ.get(&x).times, 1);
        assert!(occ.get(&x).captured);
    }
}
