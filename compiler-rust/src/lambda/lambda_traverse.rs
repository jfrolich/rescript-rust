//! Port of the generic child walks in `compiler/ml/lambda_traverse.ml`.
//!
//! OCaml's `shallow_map_sharing` returns a node physically unchanged when
//! every child comes back physically unchanged, and otherwise rebuilds it
//! through Lambda's smart constructors. Rust values have no physical
//! identity, so the mapping function reports whether it changed its input
//! and [`shallow_map_sharing`] passes that answer up. An unchanged node is
//! reassembled exactly as it was, and a changed one goes through the same
//! smart constructor OCaml uses.

use crate::lambda::{Apply, Lambda, PrimInfo};

/// A mapped value and whether it differs from the input.
pub type Mapped = (Lambda, bool);

/// `Lambda_traverse.shallow_exists`: does any immediate child satisfy `f`?
/// Children are visited in OCaml's order and the walk short-circuits.
pub fn shallow_exists(lam: &Lambda, f: &mut impl FnMut(&Lambda) -> bool) -> bool {
    match lam {
        Lambda::Lvar(_)
        | Lambda::LglobalModule(_)
        | Lambda::Lconst(_)
        | Lambda::Lbreak
        | Lambda::Lcontinue => false,
        Lambda::Lapply(ap) => f(&ap.ap_func) || ap.ap_args.iter().any(&mut *f),
        Lambda::Lfunction(func) => f(&func.body),
        Lambda::Llet(_, _, arg, body) => f(arg) || f(body),
        Lambda::Lletrec(decl, body) => f(body) || decl.iter().any(|(_, e)| f(e)),
        Lambda::Lprim(prim) => prim.args.iter().any(&mut *f),
        Lambda::Lswitch(arg, sw) => {
            f(arg)
                || sw.sw_consts.iter().any(|(_, e)| f(e))
                || sw.sw_blocks.iter().any(|(_, e)| f(e))
                || sw.sw_failaction.as_deref().is_some_and(&mut *f)
        }
        Lambda::LstringSwitch(arg, cases, default) => {
            f(arg) || cases.iter().any(|(_, e)| f(e)) || default.as_deref().is_some_and(&mut *f)
        }
        Lambda::LstaticRaise(_, args) => args.iter().any(&mut *f),
        Lambda::LstaticCatch(e1, _, e2)
        | Lambda::LtryWith(e1, _, e2)
        | Lambda::LtryFinally(e1, e2) => f(e1) || f(e2),
        Lambda::LifThenElse(e1, e2, e3) => f(e1) || f(e2) || f(e3),
        Lambda::Lsequence(e1, e2) | Lambda::Lwhile(e1, e2) => f(e1) || f(e2),
        Lambda::Lfor(_, e1, e2, _, e3) => f(e1) || f(e2) || f(e3),
        Lambda::Lfor_of(_, e1, e2) | Lambda::Lfor_await_of(_, e1, e2) => f(e1) || f(e2),
        Lambda::Lassign(_, e) => f(e),
    }
}

/// Rewrite one child in place, returning whether it changed.
#[inline]
fn map_in(slot: &mut Lambda, f: &mut impl FnMut(Lambda) -> Mapped) -> bool {
    let (item, changed) = f(std::mem::replace(slot, Lambda::Lbreak));
    *slot = item;
    changed
}

fn map_list(items: &mut [Lambda], f: &mut impl FnMut(Lambda) -> Mapped) -> bool {
    let mut changed = false;
    for item in items {
        changed |= map_in(item, f);
    }
    changed
}

fn map_snd<K>(items: &mut [(K, Lambda)], f: &mut impl FnMut(Lambda) -> Mapped) -> bool {
    let mut changed = false;
    for (_, item) in items {
        changed |= map_in(item, f);
    }
    changed
}

fn map_opt(item: &mut Option<Box<Lambda>>, f: &mut impl FnMut(Lambda) -> Mapped) -> bool {
    item.as_deref_mut().is_some_and(|item| map_in(item, f))
}

/// `Lambda_traverse.shallow_map_sharing`: rewrite the immediate children with
/// `f`, left to right, and rebuild through the smart constructor only when a
/// child changed.
///
/// Children are rewritten in place, so an unchanged node keeps its
/// allocations. Only `apply`, `prim`, `switch`, `string_switch`, `if_` and
/// `seq` fold; the other constructors just build the node, which in-place
/// rewriting already produced.
pub fn shallow_map_sharing(mut lam: Lambda, f: &mut impl FnMut(Lambda) -> Mapped) -> Mapped {
    let changed = match &mut lam {
        Lambda::Lvar(_)
        | Lambda::LglobalModule(_)
        | Lambda::Lconst(_)
        | Lambda::Lbreak
        | Lambda::Lcontinue => return (lam, false),
        Lambda::Lapply(ap) => {
            let c1 = map_in(&mut ap.ap_func, f);
            let c2 = map_list(&mut ap.ap_args, f);
            if !(c1 || c2) {
                return (lam, false);
            }
            let Lambda::Lapply(ap) = lam else {
                unreachable!()
            };
            let Apply {
                ap_func,
                ap_args,
                ap_info,
            } = *ap;
            return (Lambda::apply(*ap_func, ap_args, ap_info), true);
        }
        Lambda::Lfunction(func) => map_in(&mut func.body, f),
        Lambda::Llet(_, _, e, b) => {
            let c1 = map_in(e, f);
            let c2 = map_in(b, f);
            c1 || c2
        }
        Lambda::Lletrec(bs, b) => {
            let c1 = map_snd(bs, f);
            let c2 = map_in(b, f);
            c1 || c2
        }
        Lambda::Lprim(prim) => {
            if !map_list(&mut prim.args, f) {
                return (lam, false);
            }
            let Lambda::Lprim(prim) = lam else {
                unreachable!()
            };
            let PrimInfo {
                primitive,
                args,
                loc,
            } = *prim;
            return (Lambda::prim(primitive, args, loc), true);
        }
        Lambda::Lswitch(e, sw) => {
            let c1 = map_in(e, f);
            let c2 = map_snd(&mut sw.sw_consts, f);
            let c3 = map_snd(&mut sw.sw_blocks, f);
            let c4 = map_opt(&mut sw.sw_failaction, f);
            if !(c1 || c2 || c3 || c4) {
                return (lam, false);
            }
            let Lambda::Lswitch(e, sw) = lam else {
                unreachable!()
            };
            return (Lambda::switch(*e, *sw), true);
        }
        Lambda::LstringSwitch(e, cases, d) => {
            let c1 = map_in(e, f);
            let c2 = map_snd(cases, f);
            let c3 = map_opt(d, f);
            if !(c1 || c2 || c3) {
                return (lam, false);
            }
            let Lambda::LstringSwitch(e, cases, d) = lam else {
                unreachable!()
            };
            return (Lambda::string_switch(*e, cases, d), true);
        }
        Lambda::LstaticRaise(_, args) => map_list(args, f),
        Lambda::LstaticCatch(b, _, hd) => {
            let c1 = map_in(b, f);
            let c2 = map_in(hd, f);
            c1 || c2
        }
        Lambda::LtryWith(b, _, h) | Lambda::LtryFinally(b, h) => {
            let c1 = map_in(b, f);
            let c2 = map_in(h, f);
            c1 || c2
        }
        Lambda::LifThenElse(a, b, c) => {
            let c1 = map_in(a, f);
            let c2 = map_in(b, f);
            let c3 = map_in(c, f);
            if !(c1 || c2 || c3) {
                return (lam, false);
            }
            let Lambda::LifThenElse(a, b, c) = lam else {
                unreachable!()
            };
            return (Lambda::if_(*a, *b, *c), true);
        }
        Lambda::Lsequence(a, b) => {
            let c1 = map_in(a, f);
            let c2 = map_in(b, f);
            if !(c1 || c2) {
                return (lam, false);
            }
            let Lambda::Lsequence(a, b) = lam else {
                unreachable!()
            };
            return (Lambda::seq(*a, *b), true);
        }
        Lambda::Lwhile(a, b) | Lambda::Lfor_of(_, a, b) | Lambda::Lfor_await_of(_, a, b) => {
            let c1 = map_in(a, f);
            let c2 = map_in(b, f);
            c1 || c2
        }
        Lambda::Lfor(_, a, b, _, c) => {
            let c1 = map_in(a, f);
            let c2 = map_in(b, f);
            let c3 = map_in(c, f);
            c1 || c2 || c3
        }
        Lambda::Lassign(_, b) => map_in(b, f),
    };
    (lam, changed)
}
