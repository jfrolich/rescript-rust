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

use std::collections::HashMap;

use crate::lambda::{Comparison, Constant, LetKind, Primitive};
use crate::location::Location;
use crate::raw_lambda::{RawLambda, RawLambdaSwitch, RawPrimInfo};

// ── Action store (port of Switch.Store) ────────────────────────────────

/// Whether an action is shared (used by multiple cases) or single.
#[derive(Debug, Clone)]
pub enum Shared<A> {
    Shared(A),
    Single(A),
}

/// OCaml `compiler/ml/switch.ml:511-560` stores actions as closures and
/// invokes each leaf action without copying the lambda tree. Rust stores owned
/// `RawLambda` values, so keep single-use actions movable and clone only the
/// action slots that the generated case tree can reach more than once.
enum SwitchAction {
    Shared(RawLambda),
    Single(Option<RawLambda>),
}

impl SwitchAction {
    fn take(&mut self) -> RawLambda {
        match self {
            SwitchAction::Shared(action) => action.clone(),
            SwitchAction::Single(action) => action
                .take()
                .expect("single-use switch action was consumed more than once"),
        }
    }
}

fn action_use_counts(action_count: usize, cases: &[(i32, i32, usize)]) -> Vec<usize> {
    let mut counts = vec![0usize; action_count];
    for &(_, _, action) in cases {
        counts[action] += 1;
    }
    counts
}

fn actions_for_cases(actions: Vec<RawLambda>, cases: &[(i32, i32, usize)]) -> Vec<SwitchAction> {
    let counts = action_use_counts(actions.len(), cases);
    actions
        .into_iter()
        .enumerate()
        .map(|(idx, action)| {
            if counts[idx] == 1 {
                SwitchAction::Single(Some(action))
            } else {
                SwitchAction::Shared(action)
            }
        })
        .collect()
}

/// Action store that deduplicates actions by structural key.
/// Port of OCaml's `Switch.Store`.
pub struct ActionStore {
    /// Maps action key -> (must_share, index)
    map: HashMap<u64, (bool, usize)>,
    /// Stored actions in order: (must_share, action)
    acts: Vec<(bool, RawLambda)>,
    next: usize,
}

impl ActionStore {
    pub fn new() -> Self {
        ActionStore {
            map: HashMap::new(),
            acts: Vec::new(),
            next: 0,
        }
    }

    fn add(&mut self, must_share: bool, act: RawLambda) -> usize {
        let i = self.next;
        self.acts.push((must_share, act));
        self.next += 1;
        i
    }

    fn store(&mut self, must_share: bool, act: RawLambda) -> usize {
        if let Some(key) = make_lambda_key(&act) {
            if let Some(&(shared, i)) = self.map.get(&key) {
                if !shared {
                    self.map.insert(key, (true, i));
                }
                return i;
            }
            let i = self.add(must_share, act);
            self.map.insert(key, (must_share, i));
            i
        } else {
            self.add(must_share, act)
        }
    }

    /// Store an action, returning its index. Actions with the same key
    /// get the same index and become shared.
    pub fn act_store(&mut self, act: RawLambda) -> usize {
        self.store(false, act)
    }

    /// Store an action that will always be shared.
    pub fn act_store_shared(&mut self, act: RawLambda) -> usize {
        self.store(true, act)
    }

    /// Retrieve all stored actions with sharing information.
    pub fn act_get_shared(self) -> Vec<Shared<RawLambda>> {
        let ActionStore { map, acts, .. } = self;
        let mut share_flags: Vec<bool> = acts.iter().map(|(shared, _)| *shared).collect();

        // Mark actions that are shared in the map
        for (_, (shared, i)) in map {
            if shared {
                if let Some(flag) = share_flags.get_mut(i) {
                    *flag = true;
                }
            }
        }
        acts.into_iter()
            .zip(share_flags)
            .map(|((_, act), shared)| {
                if shared {
                    Shared::Shared(act)
                } else {
                    Shared::Single(act)
                }
            })
            .collect()
    }
}

/// Simple structural key for lambda expressions (for deduplication).
fn make_lambda_key(lam: &RawLambda) -> Option<u64> {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    fn hash_lambda(lam: &RawLambda, h: &mut DefaultHasher) -> bool {
        match lam.peel() {
            RawLambda::Lvar(id) => {
                0u8.hash(h);
                id.name().hash(h);
                id.stamp().hash(h);
                true
            }
            RawLambda::Lconst(c) => {
                1u8.hash(h);
                match c {
                    Constant::Int { i, .. } => {
                        0u8.hash(h);
                        i.hash(h);
                    }
                    Constant::Char(c) => {
                        1u8.hash(h);
                        c.hash(h);
                    }
                    Constant::String(s) => {
                        2u8.hash(h);
                        s.hash(h);
                    }
                    Constant::Float(f) => {
                        3u8.hash(h);
                        f.hash(h);
                    }
                    _ => return false,
                }
                true
            }
            RawLambda::LstaticRaise(i, args) if args.is_empty() => {
                2u8.hash(h);
                i.hash(h);
                true
            }
            RawLambda::Lprim(info) => {
                3u8.hash(h);
                std::mem::discriminant(&info.primitive).hash(h);
                for arg in &info.args {
                    if !hash_lambda(arg, h) {
                        return false;
                    }
                }
                true
            }
            RawLambda::LifThenElse(c, t, e) => {
                4u8.hash(h);
                hash_lambda(c, h) && hash_lambda(t, h) && hash_lambda(e, h)
            }
            _ => false,
        }
    }

    let mut hasher = DefaultHasher::new();
    if hash_lambda(lam, &mut hasher) {
        Some(hasher.finish())
    } else {
        None
    }
}

// ── SArg implementation ───────────────────────────────────────────────

fn make_const(i: i32) -> RawLambda {
    RawLambda::Lconst(Constant::int(i))
}

fn make_prim(prim: Primitive, args: Vec<RawLambda>) -> RawLambda {
    RawLambda::Lprim(Box::new(RawPrimInfo {
        primitive: prim,
        args,
        loc: Location::none(),
    }))
}

/// OCaml `Switch.covers_range` (switch.ml:104-111): `cases` is exactly the
/// contiguous integer keys `start .. finish`, in order.
fn covers_range(cases: &[(crate::lambda::SwitchKey, RawLambda)], start: i32, finish: i32) -> bool {
    let mut start = start;
    for (key, _) in cases {
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
pub(crate) fn out_of_range(arg: &RawLambda, lo: i32, hi: i32) -> RawLambda {
    let test = |cmp: Comparison, k: i32| make_prim(Primitive::Pintcomp(cmp), vec![arg.clone(), make_const(k)]);
    if hi == lo + 1 {
        make_prim(
            Primitive::Pnot,
            vec![make_prim(Primitive::Psequor, vec![test(Comparison::Eq, lo), test(Comparison::Eq, hi)])],
        )
    } else {
        make_prim(Primitive::Psequor, vec![test(Comparison::Gt, hi), test(Comparison::Lt, lo)])
    }
}

/// OCaml `Switch.emit_if_out` (switch.ml:120-138). The switcher guards a
/// jump table with a range test; a JS `switch` has a native `default`, so
/// when the table already covers the whole guarded range the guard is
/// dropped and its action becomes the failaction.
fn emit_if_out(offset: i32, range: i32, arg: &RawLambda, ifso: RawLambda, ifno: RawLambda) -> RawLambda {
    let lo = -offset;
    let hi = range - offset;
    if let (RawLambda::Lvar(x), RawLambda::Lswitch(sarg, sw)) = (arg, &ifno)
        && let RawLambda::Lvar(y) = sarg.as_ref()
        && sw.sw_blocks.is_empty()
        && sw.sw_blocks_full
        && sw.sw_failaction.is_none()
        && x.same(y)
        && covers_range(&sw.sw_consts, lo, hi)
    {
        let RawLambda::Lswitch(sarg, mut sw) = ifno else {
            unreachable!()
        };
        sw.sw_failaction = Some(Box::new(ifso));
        sw.sw_consts_full = false;
        return RawLambda::Lswitch(sarg, sw);
    }
    make_if(out_of_range(arg, lo, hi), ifso, ifno)
}

/// OCaml `Switch.emit_if_in` (switch.ml:140-142).
fn emit_if_in(offset: i32, range: i32, arg: &RawLambda, ifso: RawLambda, ifno: RawLambda) -> RawLambda {
    let lo = -offset;
    let hi = range - offset;
    make_if(make_prim(Primitive::Pnot, vec![out_of_range(arg, lo, hi)]), ifso, ifno)
}

fn make_if(cond: RawLambda, ifso: RawLambda, ifnot: RawLambda) -> RawLambda {
    RawLambda::LifThenElse(Box::new(cond), Box::new(ifso), Box::new(ifnot))
}

/// Build an Lswitch from a mapping table.
fn build_lswitch(
    arg: RawLambda,
    tbl: &[usize],
    acts: Vec<RawLambda>,
    offset: i32,
    sw_dispatch: Option<crate::lambda::SwitchDispatch>,
) -> RawLambda {
    let cases_for_counts: Vec<(i32, i32, usize)> = tbl
        .iter()
        .enumerate()
        .map(|(i, &act_idx)| (offset + i as i32, offset + i as i32, act_idx))
        .collect();
    let mut acts = actions_for_cases(acts, &cases_for_counts);
    let mut cases: Vec<(i32, RawLambda)> = Vec::with_capacity(tbl.len());
    for (i, &act_idx) in tbl.iter().enumerate().rev() {
        cases.push((offset + i as i32, acts[act_idx].take()));
    }
    cases.reverse();
    RawLambda::Lswitch(
        Box::new(arg),
        Box::new(RawLambdaSwitch {
            sw_consts_full: true,
            sw_consts: cases
                .into_iter()
                .map(|(key, action)| (crate::lambda::SwitchKey::Int(key), action))
                .collect(),
            sw_blocks_full: true,
            sw_blocks: Vec::new(),
            sw_failaction: None,
            sw_dispatch: crate::lambda::SwitchDispatch::Direct,
        }),
    )
}

fn make_exit(i: i32) -> RawLambda {
    RawLambda::LstaticRaise(i, Vec::new())
}

/// Check if a lambda is a simple static raise.
fn as_simple_exit(lam: &RawLambda) -> Option<i32> {
    match lam.peel() {
        RawLambda::LstaticRaise(i, args) if args.is_empty() => Some(*i),
        RawLambda::Llet(LetKind::Alias, _, _, body) => as_simple_exit(body),
        _ => None,
    }
}

/// OCaml's `make_catch_delayed`.
fn make_catch_delayed(
    handler: RawLambda,
    next_raise: &mut dyn FnMut() -> i32,
) -> (i32, Option<RawLambda>) {
    // Returns (exit_id, Some(handler)) if wrapping needed, (exit_id, None) if already an exit
    if let Some(i) = as_simple_exit(&handler) {
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

fn coupe(
    cases: &[(i32, i32, usize)],
    i: usize,
) -> (i32, Vec<(i32, i32, usize)>, Vec<(i32, i32, usize)>) {
    let (l, _, _) = cases[i];
    (l, cases[..i].to_vec(), cases[i..].to_vec())
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
        for i in 0..len1 - 1 {
            r.push(c1[i]);
        }
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
        for i in 1..len2 {
            r.push(c2[i]);
        }
        r
    } else if h1 > l1 {
        let mut r = Vec::with_capacity(len1 + len2);
        for i in 0..len1 - 1 {
            r.push(c1[i]);
        }
        r.push((l1, l2 - 1, act1));
        for i in 0..len2 {
            r.push(c2[i]);
        }
        r
    } else if h2 > l2 {
        let mut r = Vec::with_capacity(len1 + len2);
        for i in 0..len1 {
            r.push(c1[i]);
        }
        r.push((h1 + 1, h2, act2));
        for i in 1..len2 {
            r.push(c2[i]);
        }
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
    cases: &[(i32, i32, usize)],
) -> (i32, i32, Vec<(i32, i32, usize)>, Vec<(i32, i32, usize)>) {
    let lcases = cases.len();
    let (low, _, _) = cases[i];
    let (_, high, _) = cases[j];
    let inside = cases[i..=j].to_vec();
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
struct SwitchCompiler {
    memo: HashMap<Vec<Kind>, (TRet, (CTests, CTests))>,
    ok_inter: bool,
}

impl SwitchCompiler {
    fn new(ok_inter: bool) -> Self {
        SwitchCompiler {
            memo: HashMap::new(),
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
        let (_, (cml, cleft)) = self.opt_count(&left);
        let (_, (cmr, cright)) = self.opt_count(&right);
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
                let (_, (cmi, cinside)) = self.opt_count(&inside);
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
            let (_, (cml, cleft)) = self.opt_count(&left);
            let (_, (cmr, cright)) = self.opt_count(&right);
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
                    let (_, (cmi, cinside)) = self.opt_count(&inside);
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
                    let (_, (cmi, cinside)) = self.opt_count(&inside);
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
            let sub = cases[i..=j].to_vec();
            let (_, (_, ct)) = self.opt_count(&sub);
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
        arg: &RawLambda,
        cases: &[(i32, i32, usize)],
        actions: &mut [SwitchAction],
    ) -> RawLambda {
        let lcases = cases.len();
        assert!(lcases > 0);
        if lcases == 1 {
            return actions[cases[0].2].take();
        }

        let (w, cost) = self.opt_count(cases);
        match w {
            TRet::No => actions[cases[0].2].take(),
            TRet::Inter(i, j) => {
                let (low, high, inside, outside) = coupe_inter(i as usize, j as usize, cases);
                let (_, (cinside, _)) = self.opt_count(&inside);
                let (_, (coutside, _)) = self.opt_count(&outside);
                if low == high {
                    if less_tests(coutside, cinside) {
                        let ifso = self.c_test(off, arg, &inside, actions);
                        let ifnot = self.c_test(off, arg, &outside, actions);
                        make_if_eq(arg, low + off, ifso, ifnot)
                    } else {
                        let ifso = self.c_test(off, arg, &outside, actions);
                        let ifnot = self.c_test(off, arg, &inside, actions);
                        make_if_ne(arg, low + off, ifso, ifnot)
                    }
                } else if less_tests(coutside, cinside) {
                    // OCaml `make_if_in ctx (low + ctx.off) (high - low)`
                    // (switch.ml:535-536, 566-569).
                    let ifso = self.c_test(off, arg, &inside, actions);
                    let ifno = self.c_test(off, arg, &outside, actions);
                    emit_if_in(-(low + off), high - low, arg, ifso, ifno)
                } else {
                    let ifso = self.c_test(off, arg, &outside, actions);
                    let ifno = self.c_test(off, arg, &inside, actions);
                    emit_if_out(-(low + off), high - low, arg, ifso, ifno)
                }
            }
            TRet::Sep(i) => {
                let (lim, left, right) = coupe(cases, i);
                let (_, (cleft, _)) = self.opt_count(&left);
                let (_, (cright, _)) = self.opt_count(&right);

                if i == 1 && lim + off == 1 && cases[0].0 + off == 0 {
                    let ifso = self.c_test(off, arg, &right, actions);
                    let ifnot = self.c_test(off, arg, &left, actions);
                    make_if_ne(arg, 0, ifso, ifnot)
                } else if less_tests(cright, cleft) {
                    let ifso = self.c_test(off, arg, &left, actions);
                    let ifnot = self.c_test(off, arg, &right, actions);
                    make_if_lt(arg, lim + off, ifso, ifnot)
                } else {
                    let ifso = self.c_test(off, arg, &right, actions);
                    let ifnot = self.c_test(off, arg, &left, actions);
                    make_if_ge(arg, lim + off, ifso, ifnot)
                }
            }
        }
    }
}

// ── Comparison helpers ────────────────────────────────────────────────

fn make_if_test(
    prim: Primitive,
    arg: &RawLambda,
    i: i32,
    ifso: RawLambda,
    ifnot: RawLambda,
) -> RawLambda {
    make_if(
        make_prim(prim, vec![arg.clone(), make_const(i)]),
        ifso,
        ifnot,
    )
}

fn make_if_lt(arg: &RawLambda, i: i32, ifso: RawLambda, ifnot: RawLambda) -> RawLambda {
    match i {
        1 => make_if_test(Primitive::Pintcomp(Comparison::Le), arg, 0, ifso, ifnot),
        _ => make_if_test(Primitive::Pintcomp(Comparison::Lt), arg, i, ifso, ifnot),
    }
}

fn make_if_ge(arg: &RawLambda, i: i32, ifso: RawLambda, ifnot: RawLambda) -> RawLambda {
    match i {
        1 => make_if_test(Primitive::Pintcomp(Comparison::Gt), arg, 0, ifso, ifnot),
        _ => make_if_test(Primitive::Pintcomp(Comparison::Ge), arg, i, ifso, ifnot),
    }
}

fn make_if_eq(arg: &RawLambda, i: i32, ifso: RawLambda, ifnot: RawLambda) -> RawLambda {
    make_if_test(Primitive::Pintcomp(Comparison::Eq), arg, i, ifso, ifnot)
}

fn make_if_ne(arg: &RawLambda, i: i32, ifso: RawLambda, ifnot: RawLambda) -> RawLambda {
    make_if_test(Primitive::Pintcomp(Comparison::Neq), arg, i, ifso, ifnot)
}

// ── Cluster building (port of make_clusters/make_switch) ──────────────

/// Build clusters and generate the final test tree.
/// This combines comp_clusters, make_clusters, and c_test.
fn build_clustered_test(
    compiler: &mut SwitchCompiler,
    cases: &[(i32, i32, usize)],
    actions: &[RawLambda],
    arg: &RawLambda,
    sw_dispatch: &Option<crate::lambda::SwitchDispatch>,
) -> RawLambda {
    let (n_clusters, k) = compiler.comp_clusters(cases);
    let len = cases.len();

    // Build cluster cases and their actions
    let mut cluster_cases = vec![(0i32, 0i32, 0usize); n_clusters];
    let mut cluster_actions: Vec<RawLambda> = Vec::new();

    // Track which original action indices map to which cluster action indices
    let mut single_act_map: HashMap<usize, usize> = HashMap::new();
    let mut next_cluster_act = 0usize;

    // Process clusters from right to left (matching OCaml's recursive zyva)
    fn build_clusters(
        j: usize,
        ir: usize,
        cases: &[(i32, i32, usize)],
        actions: &[RawLambda],
        k: &[usize],
        sw_dispatch: &Option<crate::lambda::SwitchDispatch>,
        cluster_cases: &mut [(i32, i32, usize)],
        cluster_actions: &mut Vec<RawLambda>,
        single_act_map: &mut HashMap<usize, usize>,
        next_cluster_act: &mut usize,
        compiler: &mut SwitchCompiler,
    ) {
        let i = k[j];
        if i == j {
            // Single case - map to original action
            let (l, h, act) = cases[i];
            let act_index = if let Some(&idx) = single_act_map.get(&act) {
                idx
            } else {
                let idx = *next_cluster_act;
                single_act_map.insert(act, idx);
                cluster_actions.push(actions[act].clone());
                *next_cluster_act += 1;
                idx
            };
            cluster_cases[ir] = (l, h, act_index);
        } else {
            // Range [i..j] - build a dense switch
            let (l, _, _) = cases[i];
            let (_, h, _) = cases[j];
            let (ll, _, _) = cases[i];
            let (_, hh, _) = cases[j];
            let size = (hh - ll + 1) as usize;
            let mut tbl = vec![0usize; size];
            let mut act_map_inner: HashMap<usize, usize> = HashMap::new();
            let mut index = 0usize;

            for kk in i..=j {
                let (lo, hi, act) = cases[kk];
                let idx = if let Some(&idx) = act_map_inner.get(&act) {
                    idx
                } else {
                    let idx = index;
                    act_map_inner.insert(act, idx);
                    index += 1;
                    idx
                };
                for slot in (lo - ll) as usize..=(hi - ll) as usize {
                    tbl[slot] = idx;
                }
            }

            let mut acts_ordered: Vec<(usize, usize)> = act_map_inner.into_iter().collect();
            acts_ordered.sort_by_key(|&(_, idx)| idx);
            let switch_acts: Vec<RawLambda> = acts_ordered
                .iter()
                .map(|&(act_idx, _)| actions[act_idx].clone())
                .collect();

            // Build the switch action inline
            let switch_lam = build_lswitch(
                // arg will be filled in during c_test when this action is used
                // We need to use a marker... but c_test just uses actions[idx].clone()
                // Actually c_test passes arg directly. The switch needs the actual arg.
                // In OCaml, cluster actions are closures: fun ctx -> make_switch ...
                // In Rust, we can't do closures easily. Instead, we store the switch template
                // and rebuild with the correct arg during c_test.
                // Hmm, but c_test generates comparison trees that reference actions directly.
                // The simplest approach: just pass arg into actions during c_test.
                //
                // Actually, looking at OCaml more carefully: the actions in c_test are
                // `fun ctx -> ...` closures. For single-case clusters, they ignore ctx and
                // return the action directly. For multi-case clusters, they use ctx.arg to
                // build the switch. Since ctx.arg == arg at the top level, and c_test doesn't
                // change ctx.arg (only ctx.off changes... wait, ctx.off is always 0 in do_zyva).
                //
                // Actually ctx.off stays 0 through the whole computation. And ctx.arg is the
                // original arg. So for cluster switches, we can just use arg directly.
                // But we don't have arg here. Let me restructure.
                RawLambda::unit(), // placeholder
                &tbl,
                switch_acts,
                ll, // offset will be adjusted
                sw_dispatch.clone(),
            );
            // Store as cluster action - but we need arg...
            // We'll store the template info and apply arg later
            let idx = *next_cluster_act;
            // Actually, let's store a special marker and fix up later
            cluster_actions.push(switch_lam);
            *next_cluster_act += 1;
            cluster_cases[ir] = (l, h, idx);
        }

        if i > 0 {
            build_clusters(
                i - 1,
                ir - 1,
                cases,
                actions,
                k,
                sw_dispatch,
                cluster_cases,
                cluster_actions,
                single_act_map,
                next_cluster_act,
                compiler,
            );
        }
    }

    build_clusters(
        len - 1,
        n_clusters - 1,
        cases,
        actions,
        &k,
        sw_dispatch,
        &mut cluster_cases,
        &mut cluster_actions,
        &mut single_act_map,
        &mut next_cluster_act,
        compiler,
    );

    // Now we need c_test to use the arg for switch actions.
    // The issue is that switch cluster actions need the arg, but c_test stores actions
    // as pre-built RawLambda. In OCaml they're closures.
    //
    // Solution: we'll do a post-pass to fix up any switch actions that used a placeholder arg.
    // OR: store the switch templates separately and handle them in c_test.
    //
    // Simplest correct approach: since ctx.off is always 0 and ctx.arg is always the same arg,
    // we can just substitute the real arg into the built switches now.

    // Fix up cluster actions that are switches with placeholder args
    for act in cluster_actions.iter_mut() {
        fix_switch_arg(act, arg);
    }

    let mut cluster_actions = actions_for_cases(cluster_actions, &cluster_cases);
    compiler.c_test(0, arg, &cluster_cases, &mut cluster_actions)
}

/// Fix up any Lswitch nodes that have a unit placeholder as their arg.
fn fix_switch_arg(lam: &mut RawLambda, real_arg: &RawLambda) {
    if matches!(lam, RawLambda::Lshared(_))
        && matches!(lam.peel(), RawLambda::Lswitch(switch_arg, _) if switch_arg.is_unit())
    {
        *lam = std::mem::replace(lam, RawLambda::Lbreak).unshare();
    }
    match lam {
        RawLambda::Lswitch(switch_arg, _) => {
            if switch_arg.is_unit() {
                *switch_arg = Box::new(real_arg.clone());
            }
        }
        _ => {}
    }
}

// ── Shared action handling ────────────────────────────────────────────

/// Process shared actions, wrapping in catch/exit.
fn abstract_shared(
    shared_actions: Vec<Shared<RawLambda>>,
    next_raise: &mut dyn FnMut() -> i32,
) -> (Vec<(i32, RawLambda)>, Vec<RawLambda>) {
    let mut handlers: Vec<(i32, RawLambda)> = Vec::new();
    let mut actions: Vec<RawLambda> = Vec::with_capacity(shared_actions.len());

    for act in shared_actions {
        match act {
            Shared::Single(a) => actions.push(a),
            Shared::Shared(a) => {
                let (exit_id, handler) = make_catch_delayed(a, next_raise);
                if let Some(h) = handler {
                    handlers.push((exit_id, h));
                }
                actions.push(make_exit(exit_id));
            }
        }
    }
    (handlers, actions)
}

/// Wrap result with catch handlers.
fn wrap_handlers(mut result: RawLambda, handlers: Vec<(i32, RawLambda)>) -> RawLambda {
    // OCaml composes handlers as h(oh(x)), so first handler is outermost.
    // We reverse to get the first handler as outermost.
    for (exit_id, handler) in handlers.into_iter().rev() {
        if let RawLambda::LstaticRaise(j, _) = result.peel() {
            if *j == exit_id {
                result = handler;
                continue;
            }
        }
        result =
            RawLambda::LstaticCatch(Box::new(result), (exit_id, Vec::new()), Box::new(handler));
    }
    result
}

// ── Public API ────────────────────────────────────────────────────────

/// Main entry point: compile an integer switch into an optimal comparison tree.
///
/// Port of OCaml's `Switcher.zyva` / `Switch.Make.zyva`.
pub fn zyva(
    edges: (i32, i32),
    arg: RawLambda,
    cases: &[(i32, i32, usize)],
    store: ActionStore,
    sw_dispatch: Option<crate::lambda::SwitchDispatch>,
    next_raise: &mut dyn FnMut() -> i32,
) -> RawLambda {
    assert!(!cases.is_empty());

    let shared_actions = store.act_get_shared();
    zyva_with_shared_actions(
        edges,
        arg,
        cases,
        shared_actions,
        sw_dispatch,
        next_raise,
    )
}

/// Main entry point when the caller already owns the action array.
///
/// This preserves the exact indices embedded in `cases`, matching OCaml's
/// `Switcher.zyva` call where the `StoreExp` action array is passed directly.
pub fn zyva_with_shared_actions(
    edges: (i32, i32),
    arg: RawLambda,
    cases: &[(i32, i32, usize)],
    shared_actions: Vec<Shared<RawLambda>>,
    sw_dispatch: Option<crate::lambda::SwitchDispatch>,
    next_raise: &mut dyn FnMut() -> i32,
) -> RawLambda {
    assert!(!cases.is_empty());

    let (handlers, actions) = abstract_shared(shared_actions, next_raise);

    let (low, high) = edges;
    let ok_inter = low.abs() <= INTER_LIMIT && high.abs() <= INTER_LIMIT;
    let mut compiler = SwitchCompiler::new(ok_inter);

    let result = build_clustered_test(&mut compiler,cases, &actions, &arg, &sw_dispatch);
    wrap_handlers(result, handlers)
}

/// Compile a test sequence (for string switches and variant constants).
/// Port of OCaml's `Switcher.test_sequence`.
pub fn test_sequence(
    arg: RawLambda,
    cases: &[(i32, i32, usize)],
    store: ActionStore,
    next_raise: &mut dyn FnMut() -> i32,
) -> RawLambda {
    assert!(!cases.is_empty());

    let shared_actions = store.act_get_shared();
    let (handlers, actions) = abstract_shared(shared_actions, next_raise);

    let mut compiler = SwitchCompiler::new(false);
    let mut actions = actions_for_cases(actions, cases);
    let result = compiler.c_test(0, &arg, cases, &mut actions);
    wrap_handlers(result, handlers)
}

// ── Interval conversion (port of matching.ml's as_interval) ───────────

/// Convert sorted (int, action) pairs with a fail action into intervals.
pub fn as_interval_canfail(
    fail: RawLambda,
    low: i32,
    high: i32,
    sorted: &[(i32, RawLambda)],
) -> (Vec<(i32, i32, usize)>, ActionStore) {
    let mut store = ActionStore::new();
    let fail_idx = store.act_store(fail);
    assert_eq!(fail_idx, 0);

    fn nofail_rec(
        cur_low: i32,
        cur_high: i32,
        cur_act: usize,
        rest: &[(i32, RawLambda)],
        high: i32,
        store: &mut ActionStore,
    ) -> Vec<(i32, i32, usize)> {
        if rest.is_empty() {
            if cur_high == high {
                vec![(cur_low, cur_high, cur_act)]
            } else {
                vec![(cur_low, cur_high, cur_act), (cur_high + 1, high, 0)]
            }
        } else {
            let (i, ref act_i) = rest[0];
            let act_index = store.act_store(act_i.clone());
            if cur_high + 1 == i {
                if act_index == cur_act {
                    nofail_rec(cur_low, i, cur_act, &rest[1..], high, store)
                } else if act_index == 0 {
                    let mut r = vec![(cur_low, i - 1, cur_act)];
                    r.extend(fail_rec(i, i, &rest[1..], high, store));
                    r
                } else {
                    let mut r = vec![(cur_low, i - 1, cur_act)];
                    r.extend(nofail_rec(i, i, act_index, &rest[1..], high, store));
                    r
                }
            } else if act_index == 0 {
                let mut r = vec![(cur_low, cur_high, cur_act)];
                r.extend(fail_rec(cur_high + 1, cur_high + 1, rest, high, store));
                r
            } else {
                let mut r = vec![(cur_low, cur_high, cur_act), (cur_high + 1, i - 1, 0)];
                r.extend(nofail_rec(i, i, act_index, &rest[1..], high, store));
                r
            }
        }
    }

    fn fail_rec(
        cur_low: i32,
        cur_high: i32,
        rest: &[(i32, RawLambda)],
        high: i32,
        store: &mut ActionStore,
    ) -> Vec<(i32, i32, usize)> {
        if rest.is_empty() {
            vec![(cur_low, cur_high, 0)]
        } else {
            let (i, ref act_i) = rest[0];
            let index = store.act_store(act_i.clone());
            if index == 0 {
                fail_rec(cur_low, i, &rest[1..], high, store)
            } else {
                let mut r = vec![(cur_low, i - 1, 0)];
                r.extend(nofail_rec(i, i, index, &rest[1..], high, store));
                r
            }
        }
    }

    let intervals = if sorted.is_empty() {
        vec![(low, high, 0)]
    } else {
        let (i, ref act_i) = sorted[0];
        let index = store.act_store(act_i.clone());
        if index == 0 {
            fail_rec(low, i, &sorted[1..], high, &mut store)
        } else if low < i {
            let mut r = vec![(low, i - 1, 0)];
            r.extend(nofail_rec(i, i, index, &sorted[1..], high, &mut store));
            r
        } else {
            nofail_rec(i, i, index, &sorted[1..], high, &mut store)
        }
    };

    (intervals, store)
}

/// Convert sorted (int, action) pairs (no fail) into intervals.
pub fn as_interval_nofail(sorted: &[(i32, RawLambda)]) -> (Vec<(i32, i32, usize)>, ActionStore) {
    let mut store = ActionStore::new();

    let has_hole = sorted.windows(2).any(|w| w[1].0 > w[0].0 + 1);

    fn i_rec(
        cur_low: i32,
        cur_high: i32,
        cur_act: usize,
        rest: &[(i32, RawLambda)],
        store: &mut ActionStore,
    ) -> Vec<(i32, i32, usize)> {
        if rest.is_empty() {
            vec![(cur_low, cur_high, cur_act)]
        } else {
            let (i, ref act) = rest[0];
            let act_index = store.act_store(act.clone());
            if act_index == cur_act {
                i_rec(cur_low, i, cur_act, &rest[1..], store)
            } else {
                let mut r = vec![(cur_low, cur_high, cur_act)];
                r.extend(i_rec(i, i, act_index, &rest[1..], store));
                r
            }
        }
    }

    if sorted.is_empty() {
        return (Vec::new(), store);
    }

    let (i, ref act) = sorted[0];
    let act_index = if has_hole {
        store.act_store_shared(act.clone())
    } else {
        store.act_store(act.clone())
    };
    assert_eq!(act_index, 0);
    let intervals = i_rec(i, i, act_index, &sorted[1..], &mut store);
    (intervals, store)
}

/// Build intervals from a sorted int-lambda list.
pub fn as_interval(
    fail: Option<RawLambda>,
    low: i32,
    high: i32,
    sorted: &[(i32, RawLambda)],
) -> ((i32, i32), Vec<(i32, i32, usize)>, ActionStore) {
    let edges = get_edges(low, high, sorted);
    let (intervals, store) = match fail {
        None => as_interval_nofail(sorted),
        Some(fail_act) => as_interval_canfail(fail_act, low, high, sorted),
    };
    (edges, intervals, store)
}

fn get_edges(low: i32, high: i32, sorted: &[(i32, RawLambda)]) -> (i32, i32) {
    if sorted.is_empty() {
        (low, high)
    } else {
        let first = sorted[0].0;
        let last = sorted.last().unwrap().0;
        (first, last)
    }
}

/// High-level entry point matching OCaml's `call_switcher`.
pub fn call_switcher(
    fail: Option<RawLambda>,
    arg: RawLambda,
    low: i32,
    high: i32,
    int_lambda_list: &[(i32, RawLambda)],
    sw_dispatch: Option<crate::lambda::SwitchDispatch>,
    next_raise: &mut dyn FnMut() -> i32,
) -> RawLambda {
    let mut sorted = int_lambda_list.to_vec();
    sorted.sort_by_key(|(i, _)| *i);

    let (edges, cases, store) = as_interval(fail, low, high, &sorted);
    zyva(edges, arg, &cases, store, sw_dispatch, next_raise)
}
