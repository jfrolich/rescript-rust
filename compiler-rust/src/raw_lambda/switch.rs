//! Port of OCaml's Switch module (compiler/ml/switch.ml).
//!
//! Transforms integer switch constructs into optimal combinations of
//! if-tests and dense switches using the algorithms from:
//!
//! - R.L. Bernstein, "Producing good code for the case statement",
//!   Software Practice and Experience, 15(10) (1985)
//! - D.L. Spuler, "Two-Way Comparison Search Trees" and
//!   "Compiler Code Generation for Multiway Branch Statement",
//!   Technical Reports, James Cook University
//! - S.K. Kannan and T.A. Proebsting, "Correction to Producing Good Code
//!   for the Case Statement", SPE Vol. 24(2) (Feb 1994)

use crate::fast_hash::AHashMap;
use crate::lambda::LamLoc;
use crate::lambda::arena::{LamArena, Node, View};
use crate::lambda::{Comparison, Constant, LetKind, Primitive};
use crate::raw_lambda::{RawArena, RawLambda, RawLambdaSwitch};

// ── Action store (port of Switch.Store) ────────────────────────────────

/// Whether an action is shared (used by multiple cases) or single.
#[derive(Debug, Clone)]
pub enum Shared<A> {
    /// An action used by several cases.
    Shared(A),
    /// An action used by one case.
    Single(A),
}

fn make_const(b: &RawArena, i: i32) -> RawLambda {
    b.const_(Constant::int(i))
}

fn make_prim(b: &RawArena, prim: Primitive, args: &[RawLambda]) -> RawLambda {
    b.prim(prim, args, LamLoc::NONE)
}

/// OCaml `Switch.covers_range` (switch.ml:104-111): `cases` is exactly the
/// contiguous integer keys `start .. finish`, in order.
fn covers_range(keys: &[crate::lambda::SwitchKey], start: i32, finish: i32) -> bool {
    let mut start = start;
    for key in keys {
        match key {
            crate::lambda::SwitchKey::Int(i) if start <= finish && *i == start => start += 1,
            _ => return false,
        }
    }
    finish < start
}

/// OCaml `Switch.out_of_range` (switch.ml:113-118): `arg` is outside
/// `lo .. hi`. A two-value range reads better as a pair of equality tests
/// than as a pair of comparisons.
pub(crate) fn out_of_range(b: &RawArena, arg: RawLambda, lo: i32, hi: i32) -> RawLambda {
    let test = |cmp: Comparison, k: i32| {
        let k = make_const(b, k);
        make_prim(b, Primitive::Pintcomp(cmp), &[arg, k])
    };
    if hi == lo + 1 {
        let (l, h) = (test(Comparison::Eq, lo), test(Comparison::Eq, hi));
        let or = make_prim(b, Primitive::Psequor, &[l, h]);
        make_prim(b, Primitive::Pnot, &[or])
    } else {
        let (h, l) = (test(Comparison::Gt, hi), test(Comparison::Lt, lo));
        make_prim(b, Primitive::Psequor, &[h, l])
    }
}

/// OCaml `Switch.emit_if_out` (switch.ml:120-138). The switcher guards a
/// jump table with a range test; a JS `switch` has a native `default`, so
/// when the table already covers the whole guarded range the guard is
/// dropped and its action becomes the failaction.
fn emit_if_out(
    b: &RawArena,
    offset: i32,
    range: i32,
    arg: RawLambda,
    ifso: RawLambda,
    ifno: RawLambda,
) -> RawLambda {
    let lo = -offset;
    let hi = range - offset;
    let covered = b.with_mut(|a| {
        let Node::Switch {
            scrut,
            actions,
            info,
        } = a.node(ifno)
        else {
            return None;
        };
        let p = a.switch_payload(info);
        let same_var = matches!((a.as_var(arg), a.as_var(scrut)), (Some(x), Some(y)) if x.same(&y));
        if !(same_var
            && p.n_blocks() == 0
            && p.blocks_full
            && !p.has_fail
            && covers_range(a.switch_const_keys(info), lo, hi))
        {
            return None;
        }
        let (blocks_full, dispatch) = (p.blocks_full, p.dispatch.clone());
        let keys = a.switch_const_keys(info).to_vec();
        let mut cases = a.list_small(actions);
        cases.push(ifso);
        let actions = a.add_list(&cases);
        let info = a.add_switch(false, keys, blocks_full, [], true, dispatch);
        Some(a.switch_raw(scrut, actions, info))
    });
    if let Some(switch) = covered {
        return switch;
    }
    let cond = out_of_range(b, arg, lo, hi);
    make_if(b, cond, ifso, ifno)
}

/// OCaml `Switch.emit_if_in` (switch.ml:140-142).
fn emit_if_in(
    b: &RawArena,
    offset: i32,
    range: i32,
    arg: RawLambda,
    ifso: RawLambda,
    ifno: RawLambda,
) -> RawLambda {
    let lo = -offset;
    let hi = range - offset;
    let out = out_of_range(b, arg, lo, hi);
    let cond = make_prim(b, Primitive::Pnot, &[out]);
    make_if(b, cond, ifso, ifno)
}

fn make_if(b: &RawArena, cond: RawLambda, ifso: RawLambda, ifnot: RawLambda) -> RawLambda {
    b.if_raw(cond, ifso, ifnot)
}

/// Build an Lswitch from a mapping table.
fn build_lswitch(
    b: &RawArena,
    arg: RawLambda,
    tbl: &[usize],
    acts: &[RawLambda],
    offset: i32,
) -> RawLambda {
    b.switch(
        arg,
        RawLambdaSwitch {
            sw_consts_full: true,
            sw_consts: tbl
                .iter()
                .enumerate()
                .map(|(i, &act_idx)| {
                    (
                        crate::lambda::SwitchKey::Int(offset + i as i32),
                        acts[act_idx],
                    )
                })
                .collect(),
            sw_blocks_full: true,
            sw_blocks: Vec::new(),
            sw_failaction: None,
            sw_dispatch: crate::lambda::SwitchDispatch::Direct,
        },
    )
}

fn make_exit(b: &RawArena, i: i32) -> RawLambda {
    b.static_raise(i, &[])
}

/// Check if a lambda is a simple static raise.
fn as_simple_exit(a: &LamArena, lam: RawLambda) -> Option<i32> {
    match a.view(lam) {
        View::StaticRaise(i, []) => Some(i),
        View::Let(LetKind::Alias, _, _, body) => as_simple_exit(a, body),
        _ => None,
    }
}

/// OCaml's `make_catch_delayed`.
fn make_catch_delayed(
    b: &RawArena,
    handler: RawLambda,
    next_raise: &mut dyn FnMut() -> i32,
) -> (i32, Option<RawLambda>) {
    // Returns (exit_id, Some(handler)) if wrapping needed, (exit_id, None) if already an exit
    let simple = as_simple_exit(&b.get(), handler);
    if let Some(i) = simple {
        (i, None)
    } else {
        let i = next_raise();
        (i, Some(handler))
    }
}

// ── Main Switch algorithm ─────────────────────────────────────────────

const CUT: usize = 8;
const MORE_CUT: usize = 16;
const THETA: f64 = 0.33333;
const SWITCH_MIN: usize = 3;

#[derive(Clone, Copy, Debug)]
struct CTests {
    n: i32,
    ni: i32,
}

const TOO_MUCH: CTests = CTests {
    n: i32::MAX,
    ni: i32::MAX,
};

fn less_tests(c1: CTests, c2: CTests) -> bool {
    if c1.n < c2.n {
        true
    } else if c1.n == c2.n {
        c1.ni < c2.ni
    } else {
        false
    }
}

fn eq_tests(c1: CTests, c2: CTests) -> bool {
    c1.n == c2.n && c1.ni == c2.ni
}

fn less2tests(p1: (CTests, CTests), p2: (CTests, CTests)) -> bool {
    if eq_tests(p1.0, p2.0) {
        less_tests(p1.1, p2.1)
    } else {
        less_tests(p1.0, p2.0)
    }
}

fn add_test(t1: &mut CTests, t2: CTests) {
    t1.n = t1.n.saturating_add(t2.n);
    t1.ni = t1.ni.saturating_add(t2.ni);
}

#[derive(Clone, Debug)]
enum TRet {
    Inter(i32, i32),
    Sep(usize),
    No,
}

type Cases<'a> = &'a [(i32, i32, usize)];

fn coupe(cases: Cases<'_>, i: usize) -> (i32, Cases<'_>, Cases<'_>) {
    let (l, _, _) = cases[i];
    (l, &cases[..i], &cases[i..])
}

fn case_append(c1: &[(i32, i32, usize)], c2: &[(i32, i32, usize)]) -> Vec<(i32, i32, usize)> {
    let len1 = c1.len();
    let len2 = c2.len();
    if len1 == 0 {
        return c2.to_vec();
    }
    if len2 == 0 {
        return c1.to_vec();
    }
    let (l1, h1, act1) = c1[len1 - 1];
    let (l2, h2, act2) = c2[0];
    if act1 == act2 {
        let mut r = Vec::with_capacity(len1 + len2 - 1);
        r.extend_from_slice(&c1[..len1 - 1]);
        let l = if len1 >= 2 {
            let (_, h, _) = r[len1 - 2];
            if h + 1 < l1 { h + 1 } else { l1 }
        } else {
            l1
        };
        let h = if len2 >= 2 {
            let (l_next, _, _) = c2[1];
            if h2 + 1 < l_next { l_next - 1 } else { h2 }
        } else {
            h2
        };
        r.push((l, h, act1));
        r.extend_from_slice(&c2[1..]);
        r
    } else if h1 > l1 {
        let mut r = Vec::with_capacity(len1 + len2);
        r.extend_from_slice(&c1[..len1 - 1]);
        r.push((l1, l2 - 1, act1));
        r.extend_from_slice(c2);
        r
    } else if h2 > l2 {
        let mut r = Vec::with_capacity(len1 + len2);
        r.extend_from_slice(c1);
        r.push((h1 + 1, h2, act2));
        r.extend_from_slice(&c2[1..]);
        r
    } else {
        let mut r = c1.to_vec();
        r.extend_from_slice(c2);
        r
    }
}

fn coupe_inter(
    i: usize,
    j: usize,
    cases: Cases<'_>,
) -> (i32, i32, Cases<'_>, Vec<(i32, i32, usize)>) {
    let lcases = cases.len();
    let (low, _, _) = cases[i];
    let (_, high, _) = cases[j];
    let inside = &cases[i..=j];
    let outside = case_append(&cases[..i], &cases[j + 1..lcases]);
    (low, high, inside, outside)
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Kind {
    Kvalue(usize),
    Kinter(usize),
    Kempty,
}

fn make_memo_key(cases: &[(i32, i32, usize)]) -> Vec<Kind> {
    let mut seen: Vec<(usize, usize)> = Vec::new();
    let mut count: usize = 0;

    fn got_it(act: usize, seen: &mut Vec<(usize, usize)>, count: &mut usize) -> usize {
        for &(a, idx) in seen.iter() {
            if a == act {
                return idx;
            }
        }
        let r = *count;
        seen.push((act, r));
        *count += 1;
        r
    }

    fn make_one(
        l: i32,
        h: i32,
        act: usize,
        seen: &mut Vec<(usize, usize)>,
        count: &mut usize,
    ) -> Kind {
        if l == h {
            Kind::Kvalue(got_it(act, seen, count))
        } else {
            Kind::Kinter(got_it(act, seen, count))
        }
    }

    let len = cases.len();
    let (l_last, h_last, act_last) = cases[len - 1];
    let mut key = vec![make_one(l_last, h_last, act_last, &mut seen, &mut count)];

    let mut pl = l_last;
    for i in (0..len - 1).rev() {
        let (l, h, act) = cases[i];
        if pl != h + 1 {
            key.push(Kind::Kempty);
        }
        key.push(make_one(l, h, act, &mut seen, &mut count));
        pl = l;
    }
    key
}

fn same_act(cases: &[(i32, i32, usize)]) -> bool {
    if cases.is_empty() {
        return true;
    }
    let a = cases[cases.len() - 1].2;
    cases.iter().all(|&(_, _, act)| act == a)
}

const INTER_LIMIT: i32 = 1 << 16;

/// The main switch compiler. Handles memoization and test optimization.
struct SwitchCompiler<'b> {
    b: &'b RawArena,
    memo: AHashMap<Vec<Kind>, (TRet, (CTests, CTests))>,
    ok_inter: bool,
}

impl<'b> SwitchCompiler<'b> {
    fn new(b: &'b RawArena, ok_inter: bool) -> Self {
        SwitchCompiler {
            b,
            memo: AHashMap::default(),
            ok_inter,
        }
    }

    fn opt_count(&mut self, cases: &[(i32, i32, usize)]) -> (TRet, (CTests, CTests)) {
        let key = make_memo_key(cases);
        if let Some(r) = self.memo.get(&key) {
            return r.clone();
        }

        let lcases = cases.len();
        let r = if lcases == 0 {
            panic!("opt_count: empty cases");
        } else if same_act(cases) {
            (TRet::No, (CTests { n: 0, ni: 0 }, CTests { n: 0, ni: 0 }))
        } else if lcases < CUT {
            self.enum_cases(cases)
        } else if lcases < MORE_CUT {
            self.heuristic(cases)
        } else {
            self.divide(cases)
        };

        self.memo.insert(key, r.clone());
        r
    }

    fn divide(&mut self, cases: &[(i32, i32, usize)]) -> (TRet, (CTests, CTests)) {
        let lcases = cases.len();
        let m = lcases / 2;
        let (_, left, right) = coupe(cases, m);
        let mut ci = CTests { n: 1, ni: 0 };
        let mut cm = CTests { n: 1, ni: 0 };
        let (_, (cml, cleft)) = self.opt_count(left);
        let (_, (cmr, cright)) = self.opt_count(right);
        add_test(&mut ci, cleft);
        add_test(&mut ci, cright);
        if less_tests(cml, cmr) {
            add_test(&mut cm, cmr);
        } else {
            add_test(&mut cm, cml);
        }
        (TRet::Sep(m), (cm, ci))
    }

    fn heuristic(&mut self, cases: &[(i32, i32, usize)]) -> (TRet, (CTests, CTests)) {
        let lcases = cases.len();
        let (sep, csep) = self.divide(cases);
        let (inter, cinter) = if self.ok_inter {
            let (_, _, act0) = cases[0];
            let (_, _, act1) = cases[lcases - 1];
            if act0 == act1 {
                let (low, high, inside, outside) = coupe_inter(1, lcases - 2, cases);
                let (_, (cmi, cinside)) = self.opt_count(inside);
                let (_, (cmo, coutside)) = self.opt_count(&outside);
                let ni = if low == high { 0 } else { 1 };
                let mut cmij = CTests { n: 1, ni };
                let mut cij = CTests { n: 1, ni };
                add_test(&mut cij, cinside);
                add_test(&mut cij, coutside);
                if less_tests(cmi, cmo) {
                    add_test(&mut cmij, cmo);
                } else {
                    add_test(&mut cmij, cmi);
                }
                (TRet::Inter(1, lcases as i32 - 2), (cmij, cij))
            } else {
                (TRet::Inter(-1, -1), (TOO_MUCH, TOO_MUCH))
            }
        } else {
            (TRet::Inter(-1, -1), (TOO_MUCH, TOO_MUCH))
        };
        if less2tests(csep, cinter) {
            (sep, csep)
        } else {
            (inter, cinter)
        }
    }

    fn enum_cases(&mut self, cases: &[(i32, i32, usize)]) -> (TRet, (CTests, CTests)) {
        let lcases = cases.len();

        // Try all separation points
        let mut best_sep: i32 = -1;
        let mut best_sep_cost = (TOO_MUCH, TOO_MUCH);
        for i in 1..lcases {
            let (_, left, right) = coupe(cases, i);
            let mut ci = CTests { n: 1, ni: 0 };
            let mut cm = CTests { n: 1, ni: 0 };
            let (_, (cml, cleft)) = self.opt_count(left);
            let (_, (cmr, cright)) = self.opt_count(right);
            add_test(&mut ci, cleft);
            add_test(&mut ci, cright);
            if less_tests(cml, cmr) {
                add_test(&mut cm, cmr);
            } else {
                add_test(&mut cm, cml);
            }
            if less2tests((cm, ci), best_sep_cost) {
                best_sep = i as i32;
                best_sep_cost = (cm, ci);
            }
        }

        // Try interval tests
        let mut rlow: i32 = -1;
        let mut rhigh: i32 = -1;
        let mut best_inter_cost = (TOO_MUCH, TOO_MUCH);
        if !self.ok_inter {
            for i in 1..lcases.saturating_sub(1) {
                let (low, high, inside, outside) = coupe_inter(i, i, cases);
                if low == high {
                    let (_, (cmi, cinside)) = self.opt_count(inside);
                    let (_, (cmo, coutside)) = self.opt_count(&outside);
                    let mut cmij = CTests { n: 1, ni: 0 };
                    let mut cij = CTests { n: 1, ni: 0 };
                    add_test(&mut cij, cinside);
                    add_test(&mut cij, coutside);
                    if less_tests(cmi, cmo) {
                        add_test(&mut cmij, cmo);
                    } else {
                        add_test(&mut cmij, cmi);
                    }
                    if less2tests((cmij, cij), best_inter_cost) {
                        rlow = i as i32;
                        rhigh = i as i32;
                        best_inter_cost = (cmij, cij);
                    }
                }
            }
        } else {
            for i in 1..lcases.saturating_sub(1) {
                for j in i..lcases.saturating_sub(1) {
                    let (low, high, inside, outside) = coupe_inter(i, j, cases);
                    let (_, (cmi, cinside)) = self.opt_count(inside);
                    let (_, (cmo, coutside)) = self.opt_count(&outside);
                    let ni = if low == high { 0 } else { 1 };
                    let mut cmij = CTests { n: 1, ni };
                    let mut cij = CTests { n: 1, ni };
                    add_test(&mut cij, cinside);
                    add_test(&mut cij, coutside);
                    if less_tests(cmi, cmo) {
                        add_test(&mut cmij, cmo);
                    } else {
                        add_test(&mut cmij, cmi);
                    }
                    if less2tests((cmij, cij), best_inter_cost) {
                        rlow = i as i32;
                        rhigh = j as i32;
                        best_inter_cost = (cmij, cij);
                    }
                }
            }
        }

        let mut r = TRet::Inter(rlow, rhigh);
        let mut rc = best_inter_cost;
        if less2tests(best_sep_cost, rc) {
            r = TRet::Sep(best_sep as usize);
            rc = best_sep_cost;
        }
        (r, rc)
    }

    fn approx_count(&mut self, cases: &[(i32, i32, usize)], i: usize, j: usize) -> i32 {
        let l = j - i + 1;
        if l < CUT {
            let (_, (_, ct)) = self.opt_count(&cases[i..=j]);
            ct.n
        } else {
            l as i32 - 1
        }
    }

    fn particular_case(cases: &[(i32, i32, usize)], i: usize, j: usize) -> bool {
        j - i == 2 && {
            let (l1, _h1, act1) = cases[i];
            let (l2, _h2, _act2) = cases[i + 1];
            let (l3, h3, act3) = cases[i + 2];
            l1 + 1 == l2 && l2 + 1 == l3 && l3 == h3 && act1 != act3
        }
    }

    fn dense(&mut self, cases: &[(i32, i32, usize)], i: usize, j: usize) -> bool {
        if i == j {
            return true;
        }
        let (l, _, _) = cases[i];
        let (_, h, _) = cases[j];
        let ntests = self.approx_count(cases, i, j);
        Self::particular_case(cases, i, j)
            || (ntests >= SWITCH_MIN as i32
                && (ntests as f64 + 1.0) >= THETA * (h as f64 - l as f64 + 1.0))
    }

    fn comp_clusters(&mut self, cases: &[(i32, i32, usize)]) -> (usize, Vec<usize>) {
        let len = cases.len();
        let mut min_clusters = vec![usize::MAX; len];
        let mut k = vec![0usize; len];

        let get_min = |i: i32, min_clusters: &[usize]| -> usize {
            if i < 0 { 0 } else { min_clusters[i as usize] }
        };

        for i in 0..len {
            for j in 0..=i {
                if self.dense(cases, j, i)
                    && get_min(j as i32 - 1, &min_clusters).saturating_add(1) < min_clusters[i]
                {
                    k[i] = j;
                    min_clusters[i] = get_min(j as i32 - 1, &min_clusters).saturating_add(1);
                }
            }
        }
        (min_clusters[len - 1], k)
    }

    /// Generate the comparison/switch tree for a set of cases.
    /// This corresponds to OCaml's c_test.
    fn c_test(
        &mut self,
        off: i32,
        arg: RawLambda,
        cases: &[(i32, i32, usize)],
        actions: &[RawLambda],
    ) -> RawLambda {
        let lcases = cases.len();
        assert!(lcases > 0);
        if lcases == 1 {
            return actions[cases[0].2];
        }

        let (w, _cost) = self.opt_count(cases);
        match w {
            TRet::No => actions[cases[0].2],
            TRet::Inter(i, j) => {
                let (low, high, inside, outside) = coupe_inter(i as usize, j as usize, cases);
                let (_, (cinside, _)) = self.opt_count(inside);
                let (_, (coutside, _)) = self.opt_count(&outside);
                if low == high {
                    if less_tests(coutside, cinside) {
                        let ifso = self.c_test(off, arg, inside, actions);
                        let ifnot = self.c_test(off, arg, &outside, actions);
                        make_if_eq(self.b, arg, low + off, ifso, ifnot)
                    } else {
                        let ifso = self.c_test(off, arg, &outside, actions);
                        let ifnot = self.c_test(off, arg, inside, actions);
                        make_if_ne(self.b, arg, low + off, ifso, ifnot)
                    }
                } else if less_tests(coutside, cinside) {
                    // OCaml `make_if_in ctx (low + ctx.off) (high - low)`
                    // (switch.ml:535-536, 566-569).
                    let ifso = self.c_test(off, arg, inside, actions);
                    let ifno = self.c_test(off, arg, &outside, actions);
                    emit_if_in(self.b, -(low + off), high - low, arg, ifso, ifno)
                } else {
                    let ifso = self.c_test(off, arg, &outside, actions);
                    let ifno = self.c_test(off, arg, inside, actions);
                    emit_if_out(self.b, -(low + off), high - low, arg, ifso, ifno)
                }
            }
            TRet::Sep(i) => {
                let (lim, left, right) = coupe(cases, i);
                let (_, (cleft, _)) = self.opt_count(left);
                let (_, (cright, _)) = self.opt_count(right);

                if i == 1 && lim + off == 1 && cases[0].0 + off == 0 {
                    let ifso = self.c_test(off, arg, right, actions);
                    let ifnot = self.c_test(off, arg, left, actions);
                    make_if_ne(self.b, arg, 0, ifso, ifnot)
                } else if less_tests(cright, cleft) {
                    let ifso = self.c_test(off, arg, left, actions);
                    let ifnot = self.c_test(off, arg, right, actions);
                    make_if_lt(self.b, arg, lim + off, ifso, ifnot)
                } else {
                    let ifso = self.c_test(off, arg, right, actions);
                    let ifnot = self.c_test(off, arg, left, actions);
                    make_if_ge(self.b, arg, lim + off, ifso, ifnot)
                }
            }
        }
    }
}

// ── Comparison helpers ────────────────────────────────────────────────

fn make_if_test(
    b: &RawArena,
    prim: Primitive,
    arg: RawLambda,
    i: i32,
    ifso: RawLambda,
    ifnot: RawLambda,
) -> RawLambda {
    let i = make_const(b, i);
    let cond = make_prim(b, prim, &[arg, i]);
    make_if(b, cond, ifso, ifnot)
}

fn make_if_lt(
    b: &RawArena,
    arg: RawLambda,
    i: i32,
    ifso: RawLambda,
    ifnot: RawLambda,
) -> RawLambda {
    match i {
        1 => make_if_test(b, Primitive::Pintcomp(Comparison::Le), arg, 0, ifso, ifnot),
        _ => make_if_test(b, Primitive::Pintcomp(Comparison::Lt), arg, i, ifso, ifnot),
    }
}

fn make_if_ge(
    b: &RawArena,
    arg: RawLambda,
    i: i32,
    ifso: RawLambda,
    ifnot: RawLambda,
) -> RawLambda {
    match i {
        1 => make_if_test(b, Primitive::Pintcomp(Comparison::Gt), arg, 0, ifso, ifnot),
        _ => make_if_test(b, Primitive::Pintcomp(Comparison::Ge), arg, i, ifso, ifnot),
    }
}

fn make_if_eq(
    b: &RawArena,
    arg: RawLambda,
    i: i32,
    ifso: RawLambda,
    ifnot: RawLambda,
) -> RawLambda {
    make_if_test(b, Primitive::Pintcomp(Comparison::Eq), arg, i, ifso, ifnot)
}

fn make_if_ne(
    b: &RawArena,
    arg: RawLambda,
    i: i32,
    ifso: RawLambda,
    ifnot: RawLambda,
) -> RawLambda {
    make_if_test(b, Primitive::Pintcomp(Comparison::Neq), arg, i, ifso, ifnot)
}

// ── Cluster building (port of make_clusters/make_switch) ──────────────

/// Build clusters and generate the final test tree.
/// This combines comp_clusters, make_clusters, and c_test.
///
/// OCaml `compiler/ml/switch.ml` stores cluster actions as closures over
/// `ctx`; `ctx.off` stays 0 and `ctx.arg` is the original scrutinee for the
/// whole `do_zyva` run, so dense cluster switches are built on `arg` directly.
fn build_clustered_test(
    compiler: &mut SwitchCompiler<'_>,
    cases: &[(i32, i32, usize)],
    actions: &[RawLambda],
    arg: RawLambda,
) -> RawLambda {
    let b = compiler.b;
    let (n_clusters, k) = compiler.comp_clusters(cases);

    let mut cluster_cases = vec![(0i32, 0i32, 0usize); n_clusters];
    let mut cluster_actions: Vec<RawLambda> = Vec::new();
    // Original action index -> cluster action index, for single-case clusters.
    let mut single_act_map: AHashMap<usize, usize> = AHashMap::default();

    // Process clusters from right to left (matching OCaml's recursive zyva).
    let mut j = cases.len() - 1;
    let mut ir = n_clusters - 1;
    loop {
        let i = k[j];
        let (l, _, _) = cases[i];
        let (_, h, _) = cases[j];
        let act_index = if i == j {
            let act = cases[i].2;
            *single_act_map.entry(act).or_insert_with(|| {
                cluster_actions.push(unit_switch_arg_fixup(b, actions[act], arg));
                cluster_actions.len() - 1
            })
        } else {
            // Range [i..j]: build a dense switch.
            let mut tbl = vec![0usize; (h - l + 1) as usize];
            // Original action indices in first-seen order.
            let mut switch_act_ids: Vec<usize> = Vec::new();
            for &(lo, hi, act) in &cases[i..=j] {
                let idx = match switch_act_ids.iter().position(|&a| a == act) {
                    Some(idx) => idx,
                    None => {
                        switch_act_ids.push(act);
                        switch_act_ids.len() - 1
                    }
                };
                tbl[(lo - l) as usize..=(hi - l) as usize].fill(idx);
            }
            let switch_acts: Vec<RawLambda> =
                switch_act_ids.iter().map(|&act| actions[act]).collect();
            cluster_actions.push(build_lswitch(b, arg, &tbl, &switch_acts, l));
            cluster_actions.len() - 1
        };
        cluster_cases[ir] = (l, h, act_index);
        if i == 0 {
            break;
        }
        j = i - 1;
        ir -= 1;
    }

    compiler.c_test(0, arg, &cluster_cases, &cluster_actions)
}

/// Replace the scrutinee of a single-case cluster action that is itself an
/// `Lswitch` on the unit constant with `real_arg`.
///
/// This is a leftover of an earlier placeholder-based construction of dense
/// cluster switches and has no OCaml counterpart (`switch.ml` invokes single
/// actions unchanged). It is kept so output stays byte-identical; it only
/// fires for an action whose own scrutinee is literally `()`.
fn unit_switch_arg_fixup(b: &RawArena, lam: RawLambda, real_arg: RawLambda) -> RawLambda {
    if let Node::Switch {
        scrut,
        actions,
        info,
    } = b.node(lam)
        && b.is_unit(scrut)
    {
        return b.push(Node::Switch {
            scrut: real_arg,
            actions,
            info,
        });
    }
    lam
}

// ── Shared action handling ────────────────────────────────────────────

/// Process shared actions, wrapping in catch/exit.
fn abstract_shared(
    b: &RawArena,
    shared_actions: Vec<Shared<RawLambda>>,
    next_raise: &mut dyn FnMut() -> i32,
) -> (Vec<(i32, RawLambda)>, Vec<RawLambda>) {
    let mut handlers: Vec<(i32, RawLambda)> = Vec::new();
    let mut actions: Vec<RawLambda> = Vec::with_capacity(shared_actions.len());

    for act in shared_actions {
        match act {
            Shared::Single(a) => actions.push(a),
            Shared::Shared(a) => {
                let (exit_id, handler) = make_catch_delayed(b, a, next_raise);
                if let Some(h) = handler {
                    handlers.push((exit_id, h));
                }
                actions.push(make_exit(b, exit_id));
            }
        }
    }
    (handlers, actions)
}

/// Wrap result with catch handlers.
fn wrap_handlers(
    b: &RawArena,
    mut result: RawLambda,
    handlers: Vec<(i32, RawLambda)>,
) -> RawLambda {
    // OCaml composes handlers as h(oh(x)), so first handler is outermost.
    // We reverse to get the first handler as outermost.
    for (exit_id, handler) in handlers.into_iter().rev() {
        if let Node::StaticRaise { label, .. } = b.node(result)
            && label == exit_id
        {
            result = handler;
            continue;
        }
        result = b.static_catch(result, exit_id, &[], handler);
    }
    result
}

// ── Public API ────────────────────────────────────────────────────────

/// Main entry point when the caller already owns the action array.
///
/// This preserves the exact indices embedded in `cases`, matching OCaml's
/// `Switcher.zyva` call where the `StoreExp` action array is passed directly.
pub fn zyva_with_shared_actions(
    b: &RawArena,
    edges: (i32, i32),
    arg: RawLambda,
    cases: &[(i32, i32, usize)],
    shared_actions: Vec<Shared<RawLambda>>,
    next_raise: &mut dyn FnMut() -> i32,
) -> RawLambda {
    assert!(!cases.is_empty());

    let (handlers, actions) = abstract_shared(b, shared_actions, next_raise);

    let (low, high) = edges;
    let ok_inter = low.abs() <= INTER_LIMIT && high.abs() <= INTER_LIMIT;
    let mut compiler = SwitchCompiler::new(b, ok_inter);

    let result = build_clustered_test(&mut compiler, cases, &actions, arg);
    wrap_handlers(b, result, handlers)
}
