//! Direct port of `compiler/core/lam_pass_count.ml`.
//!
//! Builds an occurrence table mapping each let-bound identifier to its use
//! count plus a `captured` flag. Used downstream by `Lam_pass_lets_dce` to
//! decide which bindings can be inlined.
//!
//! Every match arm and helper here corresponds to a specific line in
//! `lam_pass_count.ml`. Do not add Rust-only logic.

use std::rc::Rc;

use ahash::AHashMap as HashMap;

use crate::ident::Ident;
use crate::lambda::lam_analysis::lfunction_can_be_inlined;
use crate::lambda::lam_beta_reduce::no_names_beta_reduce;
use crate::lambda::lam_compat::LetKind;
use crate::lambda::{LFunction, Lambda, LambdaSwitch};

/// Equivalent of OCaml's `Lam_pass_count.used_info` (lam_pass_count.ml:15-23).
#[derive(Debug, Default, Clone, Copy)]
pub struct UsedInfo {
    /// Number of references to the binding.
    pub times: u32,
    /// True when at least one reference appears under a lambda or loop body
    /// (lam_pass_count.ml:17-22).
    pub captured: bool,
}

/// Mirror of OCaml's `Lam_pass_count.dummy_info` (lam_pass_count.ml:30).
#[inline]
pub fn dummy_info() -> UsedInfo {
    UsedInfo {
        times: 0,
        captured: false,
    }
}

/// Equivalent of OCaml's `absorb_info` (lam_pass_count.ml:33-37). Adds `y`'s
/// count into `x` and propagates the captured flag.
fn absorb_info(x: &mut UsedInfo, y: UsedInfo) {
    x.times = x.times.saturating_add(y.times);
    if y.captured {
        x.captured = true;
    }
}

/// Occurrence table: maps idents to a shared mutable cell so that local-scope
/// bookkeeping mirrors OCaml's `Hash_ident.t` of mutable records
/// (lam_pass_count.ml:25, 26).
pub type OccTbl = HashMap<Ident, Rc<std::cell::RefCell<UsedInfo>>>;

/// Local table tracking the bindings currently in scope. Entries point to the
/// same mutable cells held by [`OccTbl`] so increments stay in sync, matching
/// the OCaml `local_tbl = used_info Map_ident.t` (lam_pass_count.ml:28).
type LocalTbl = HashMap<Ident, Rc<std::cell::RefCell<UsedInfo>>>;

/// Direct port of `collect_occurs` (lam_pass_count.ml:59-203).
///
/// Single-pass traversal that fills an [`OccTbl`] keyed by every let-bound
/// identifier with a `(times, captured)` pair.
pub fn collect_occurs(lam: &Lambda) -> OccTbl {
    let mut occ: OccTbl = HashMap::new();

    // Equivalent of `used` helper (lam_pass_count.ml:62-66).
    fn used(occ: &OccTbl, v: &Ident) -> bool {
        occ.get(v)
            .map(|cell| cell.borrow().times > 0)
            .unwrap_or(false)
    }

    // Equivalent of `bind_var` (lam_pass_count.ml:69-73): create a fresh cell,
    // add it to both `occ` and the local scope. OCaml's `Map_ident.add` returns
    // a persistent map cheaply; Rust mutates the local table and restores the
    // previous binding after the scoped body so we do not clone the whole map at
    // every `Llet`.
    fn bind_var(
        occ: &mut OccTbl,
        bv: &mut LocalTbl,
        ident: &Ident,
    ) -> Option<Rc<std::cell::RefCell<UsedInfo>>> {
        let cell = Rc::new(std::cell::RefCell::new(dummy_info()));
        occ.insert(ident.clone(), Rc::clone(&cell));
        bv.insert(ident.clone(), cell)
    }

    fn restore_var(
        bv: &mut LocalTbl,
        ident: &Ident,
        previous: Option<Rc<std::cell::RefCell<UsedInfo>>>,
    ) {
        match previous {
            Some(previous) => {
                bv.insert(ident.clone(), previous);
            }
            None => {
                bv.remove(ident);
            }
        }
    }

    // Equivalent of `add_one_use` (lam_pass_count.ml:76-89).
    fn add_one_use(occ: &mut OccTbl, bv: &LocalTbl, ident: &Ident) {
        if let Some(cell) = bv.get(ident) {
            cell.borrow_mut().times += 1;
            return;
        }
        // Use under a lambda or loop: mark captured and bump times so single-use
        // optimizations do not apply (lam_pass_count.ml:80-87).
        if let Some(cell) = occ.get(ident) {
            absorb_info(
                &mut cell.borrow_mut(),
                UsedInfo {
                    times: 1,
                    captured: true,
                },
            );
        }
    }

    // Equivalent of `inherit_use` (lam_pass_count.ml:91-108): used when
    // rewriting `let v = w in ...` so each later occurrence of `v` counts as a
    // use of `w` instead.
    fn inherit_use(occ: &mut OccTbl, bv: &LocalTbl, ident: &Ident, bid: &Ident) {
        let n = occ
            .get(bid)
            .map(|cell| *cell.borrow())
            .unwrap_or_else(dummy_info);
        if let Some(cell) = bv.get(ident) {
            absorb_info(&mut cell.borrow_mut(), n);
            return;
        }
        if let Some(cell) = occ.get(ident) {
            let mut copy = n;
            copy.captured = true;
            absorb_info(&mut cell.borrow_mut(), copy);
        }
    }

    // The main traversal. The structure mirrors OCaml's `count` function
    // (lam_pass_count.ml:110-201).
    fn count(occ: &mut OccTbl, bv: &mut LocalTbl, lam: &Lambda) {
        match lam {
            // Lfunction: clear local scope. Closure variables can not be
            // carried over because parameters are never rebound
            // (lam_pass_count.ml:112-117).
            Lambda::Lfunction(__func0) => {
                let LFunction { body, .. } = __func0.as_ref();

                let mut empty = LocalTbl::new();
                count(occ, &mut empty, body);
            }

            // Lfor (lam_pass_count.ml:118-121): bounds counted with `bv`,
            // body counted with empty local scope (loop body re-evaluated).
            Lambda::Lfor(_, l1, l2, _, l3) => {
                count(occ, bv, l1);
                count(occ, bv, l2);
                let mut empty = LocalTbl::new();
                count(occ, &mut empty, l3);
            }

            // Lfor_of / Lfor_await_of (lam_pass_count.ml after #7887):
            // iterable counted with `bv`, body counted with empty local scope.
            Lambda::Lfor_of(_, l1, l2) | Lambda::Lfor_await_of(_, l1, l2) => {
                count(occ, bv, l1);
                let mut empty = LocalTbl::new();
                count(occ, &mut empty, l2);
            }

            // Lwhile (lam_pass_count.ml:122-124): both arms counted with empty
            // local scope.
            Lambda::Lwhile(l1, l2) => {
                let mut empty = LocalTbl::new();
                count(occ, &mut empty, l1);
                count(occ, &mut empty, l2);
            }

            // Lvar (lam_pass_count.ml:125): one use of `v`.
            Lambda::Lvar(v) => add_one_use(occ, bv, v),

            // `Llet (_, v, Lvar w, l2)`: alias-style binding. `v` will be
            // replaced by `w` in `l2`, so each occurrence of `v` increases
            // `w`'s refcount via `inherit_use` (lam_pass_count.ml:126-130).
            Lambda::Llet(_, v, value, l2) if matches!(value.as_ref(), Lambda::Lvar(_)) => {
                let w = match value.as_ref() {
                    Lambda::Lvar(w) => w.clone(),
                    _ => unreachable!(),
                };
                let previous = bind_var(occ, bv, v);
                count(occ, bv, l2);
                restore_var(bv, v, previous);
                inherit_use(occ, bv, &w, v);
            }

            // `Llet (kind, v, l1, l2)` (lam_pass_count.ml:131-135): count body
            // first; only count `l1` if `kind = Strict` or `v` is actually
            // used (otherwise the binding will be dropped and we must not
            // attribute usage to its dead initializer).
            Lambda::Llet(kind, v, l1, l2) => {
                let previous = bind_var(occ, bv, v);
                count(occ, bv, l2);
                restore_var(bv, v, previous);
                if matches!(kind, LetKind::Strict) || used(occ, v) {
                    count(occ, bv, l1);
                }
            }

            // Lassign: only count the rhs; mutated vars are tracked elsewhere
            // (lam_pass_count.ml:136-139).
            Lambda::Lassign(_, l) => count(occ, bv, l),

            // Lglobal_module: nothing to count (lam_pass_count.ml:140).
            Lambda::LglobalModule(_) => {}

            // Lprim: count each arg (lam_pass_count.ml:141).
            Lambda::Lprim(prim) => {
                for arg in &prim.args {
                    count(occ, bv, arg);
                }
            }

            // Lletrec (lam_pass_count.ml:142-144).
            Lambda::Lletrec(bindings, body) => {
                for (_, l) in bindings {
                    count(occ, bv, l);
                }
                count(occ, bv, body);
            }

            // Lapply with inlineable Lfunction: count the beta-reduced body to
            // mirror the inlining that `Lam_pass_lets_dce` will perform later
            // (lam_pass_count.ml:146-150).
            Lambda::Lapply(apply)
                if {
                    matches!(apply.ap_func.as_ref(), Lambda::Lfunction(f)
                        if f.params.len() == apply.ap_args.len()
                            && lfunction_can_be_inlined(f))
                } =>
            {
                let f = match apply.ap_func.as_ref() {
                    Lambda::Lfunction(f) => f,
                    _ => unreachable!(),
                };
                let reduced = no_names_beta_reduce(&f.params, &f.body, &apply.ap_args);
                count(occ, bv, &reduced);
            }

            // Lapply (general): count fn + args (lam_pass_count.ml:155-157).
            Lambda::Lapply(apply) => {
                count(occ, bv, &apply.ap_func);
                for arg in &apply.ap_args {
                    count(occ, bv, arg);
                }
            }

            // Lconst: nothing to count (lam_pass_count.ml:158).
            Lambda::Lconst(_) => {}

            // Lswitch (lam_pass_count.ml:159-163).
            Lambda::Lswitch(scrut, sw) => {
                count_default(occ, bv, sw);
                count(occ, bv, scrut);
                for (_, l) in &sw.sw_consts {
                    count(occ, bv, l);
                }
                for (_, l) in &sw.sw_blocks {
                    count(occ, bv, l);
                }
            }

            // Lstringswitch (lam_pass_count.ml:164-169).
            Lambda::LstringSwitch(scrut, cases, default) => {
                count(occ, bv, scrut);
                for (_, l) in cases {
                    count(occ, bv, l);
                }
                if let Some(d) = default {
                    count(occ, bv, d);
                }
            }

            // Lstaticraise (lam_pass_count.ml:175).
            Lambda::LstaticRaise(_, ls) => {
                for l in ls {
                    count(occ, bv, l);
                }
            }

            // Lstaticcatch (lam_pass_count.ml:176-178).
            Lambda::LstaticCatch(l1, _, l2) => {
                count(occ, bv, l1);
                count(occ, bv, l2);
            }

            // Ltrywith (lam_pass_count.ml:179-181).
            Lambda::LtryWith(l1, _, l2) => {
                count(occ, bv, l1);
                count(occ, bv, l2);
            }

            // Lifthenelse (lam_pass_count.ml:182-185).
            Lambda::LifThenElse(c, t, e) => {
                count(occ, bv, c);
                count(occ, bv, t);
                count(occ, bv, e);
            }

            // Lsequence (lam_pass_count.ml:186-188).
            Lambda::Lsequence(l1, l2) => {
                count(occ, bv, l1);
                count(occ, bv, l2);
            }

            // OCaml `Lam_pass_count.collect_occurs` after #8348:
            // `Lbreak | Lcontinue -> ()`.
            Lambda::Lbreak | Lambda::Lcontinue => {}
        }
    }

    // count_default (lam_pass_count.ml:189-200): the default action runs twice
    // in the native backend when neither the const nor block table is full,
    // so its inner uses are counted twice.
    fn count_default(occ: &mut OccTbl, bv: &mut LocalTbl, sw: &LambdaSwitch) {
        let Some(failaction) = sw.sw_failaction.as_deref() else {
            return;
        };
        if !sw.sw_consts_full && !sw.sw_blocks_full {
            count(occ, bv, failaction);
            count(occ, bv, failaction);
        } else {
            // assert ((not sw.sw_consts_full) || not sw.sw_blocks_full)
            // (lam_pass_count.ml:198-199): either is allowed but not both full.
            count(occ, bv, failaction);
        }
    }

    let mut bv = LocalTbl::new();
    count(&mut occ, &mut bv, lam);
    occ
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ident::{Ident, IdentFlags};
    use crate::lambda::Lambda;
    use crate::lambda::lam_compat::LetKind;
    use crate::lambda::lam_constant::Constant;

    fn ident(name: &str, stamp: i32) -> Ident {
        Ident::new(name, stamp, IdentFlags::NONE)
    }

    fn lookup(occ: &OccTbl, ident: &Ident) -> UsedInfo {
        occ.get(ident)
            .map(|cell| *cell.borrow())
            .unwrap_or_else(dummy_info)
    }

    /// `let v = 1 in v + v` should record times=2, captured=false for v.
    /// Mirrors lam_pass_count.ml:131-135 + the Lvar arm 125.
    #[test]
    fn counts_two_uses_in_let_body() {
        let v = ident("v", 1);
        let body = Lambda::Lsequence(
            Box::new(Lambda::Lvar(v.clone())),
            Box::new(Lambda::Lvar(v.clone())),
        );
        let lam = Lambda::let_(
            LetKind::Strict,
            v.clone(),
            Lambda::Lconst(Constant::int(1)),
            body,
        );
        let occ = collect_occurs(&lam);
        let info = lookup(&occ, &v);
        assert_eq!(info.times, 2);
        assert!(!info.captured);
    }

    /// `let v = 1 in fun _ -> v` should mark v as captured.
    /// Mirrors lam_pass_count.ml:112-117 (Lfunction clears bv).
    #[test]
    fn marks_capture_under_lambda() {
        let v = ident("v", 2);
        let p = ident("p", 3);
        let func = Lambda::function_(
            1,
            vec![p],
            Lambda::Lvar(v.clone()),
            crate::lambda::FunctionAttribute {
                inline: crate::lambda::InlineAttribute::Default,
                is_a_functor: false,
                return_unit: false,
                async_: false,
                directive: None,
                one_unit_arg: false,
            },
            crate::location::Location::none(),
        );
        let lam = Lambda::let_(
            LetKind::Strict,
            v.clone(),
            Lambda::Lconst(Constant::int(1)),
            func,
        );
        let occ = collect_occurs(&lam);
        let info = lookup(&occ, &v);
        assert!(info.captured);
        assert!(info.times >= 1);
    }

    /// `let v = w in v` should add v's uses to w via inherit_use
    /// (lam_pass_count.ml:126-130).
    #[test]
    fn inherit_use_via_alias_let() {
        let w = ident("w", 4);
        let v = ident("v", 5);
        // First bind w so it has an occ entry; otherwise inherit_use does nothing.
        let inner = Lambda::let_(
            LetKind::Alias,
            v.clone(),
            Lambda::Lvar(w.clone()),
            Lambda::Lvar(v.clone()),
        );
        let lam = Lambda::let_(
            LetKind::Strict,
            w.clone(),
            Lambda::Lconst(Constant::int(0)),
            inner,
        );
        let occ = collect_occurs(&lam);
        let w_info = lookup(&occ, &w);
        // v has 1 use; that use inherits to w. w itself appears 0 times in body
        // because the alias-form Llet branch does NOT count `Lvar w` as a use
        // (lam_pass_count.ml:126-130 routes through inherit_use only).
        assert_eq!(w_info.times, 1);
        assert!(!w_info.captured);
    }
}
