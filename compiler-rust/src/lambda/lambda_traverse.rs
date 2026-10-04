//! Port of the generic child walks in `compiler/ml/lambda_traverse.ml`.
//!
//! OCaml's `shallow_map_sharing` returns a node physically unchanged when
//! every child comes back physically unchanged, and otherwise rebuilds it
//! through Lambda's smart constructors. Rust values have no physical
//! identity, so the mapping function reports whether it changed its input
//! and [`shallow_map_sharing`] passes that answer up. An unchanged node is
//! reassembled exactly as it was, and a changed one goes through the same
//! smart constructor OCaml uses.

use crate::lambda::{Apply, Lambda, LambdaSwitch, PrimInfo};

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
        Lambda::Lapply(ap) => f(&ap.ap_func) || ap.ap_args.iter().any(|arg| f(arg)),
        Lambda::Lfunction(func) => f(&func.body),
        Lambda::Llet(_, _, arg, body) => f(arg) || f(body),
        Lambda::Lletrec(decl, body) => f(body) || decl.iter().any(|(_, e)| f(e)),
        Lambda::Lprim(prim) => prim.args.iter().any(|arg| f(arg)),
        Lambda::Lswitch(arg, sw) => {
            f(arg)
                || sw.sw_consts.iter().any(|(_, e)| f(e))
                || sw.sw_blocks.iter().any(|(_, e)| f(e))
                || sw.sw_failaction.as_deref().is_some_and(|e| f(e))
        }
        Lambda::LstringSwitch(arg, cases, default) => {
            f(arg) || cases.iter().any(|(_, e)| f(e)) || default.as_deref().is_some_and(|e| f(e))
        }
        Lambda::LstaticRaise(_, args) => args.iter().any(|arg| f(arg)),
        Lambda::LstaticCatch(e1, _, e2) | Lambda::LtryWith(e1, _, e2) => f(e1) || f(e2),
        Lambda::LifThenElse(e1, e2, e3) => f(e1) || f(e2) || f(e3),
        Lambda::Lsequence(e1, e2) | Lambda::Lwhile(e1, e2) => f(e1) || f(e2),
        Lambda::Lfor(_, e1, e2, _, e3) => f(e1) || f(e2) || f(e3),
        Lambda::Lfor_of(_, e1, e2) | Lambda::Lfor_await_of(_, e1, e2) => f(e1) || f(e2),
        Lambda::Lassign(_, e) => f(e),
    }
}

fn map_list(items: Vec<Lambda>, f: &mut impl FnMut(Lambda) -> Mapped) -> (Vec<Lambda>, bool) {
    let mut changed = false;
    let items = items
        .into_iter()
        .map(|item| {
            let (item, c) = f(item);
            changed |= c;
            item
        })
        .collect();
    (items, changed)
}

fn map_snd<K>(
    items: Vec<(K, Lambda)>,
    f: &mut impl FnMut(Lambda) -> Mapped,
) -> (Vec<(K, Lambda)>, bool) {
    let mut changed = false;
    let items = items
        .into_iter()
        .map(|(k, item)| {
            let (item, c) = f(item);
            changed |= c;
            (k, item)
        })
        .collect();
    (items, changed)
}

fn map_opt(
    item: Option<Box<Lambda>>,
    f: &mut impl FnMut(Lambda) -> Mapped,
) -> (Option<Box<Lambda>>, bool) {
    match item {
        None => (None, false),
        Some(item) => {
            let (item, c) = f(*item);
            (Some(Box::new(item)), c)
        }
    }
}

/// `Lambda_traverse.shallow_map_sharing`: rewrite the immediate children with
/// `f`, left to right, and rebuild through the smart constructor only when a
/// child changed.
pub fn shallow_map_sharing(lam: Lambda, f: &mut impl FnMut(Lambda) -> Mapped) -> Mapped {
    match lam {
        Lambda::Lvar(_)
        | Lambda::LglobalModule(_)
        | Lambda::Lconst(_)
        | Lambda::Lbreak
        | Lambda::Lcontinue => (lam, false),
        Lambda::Lapply(ap) => {
            let Apply { ap_func, ap_args, ap_info, ap_transformed_jsx } = *ap;
            let (func, c1) = f(*ap_func);
            let (args, c2) = map_list(ap_args, f);
            if c1 || c2 {
                (Lambda::apply(func, args, ap_info, ap_transformed_jsx), true)
            } else {
                (
                    Lambda::Lapply(Box::new(Apply {
                        ap_func: Box::new(func),
                        ap_args: args,
                        ap_info,
                        ap_transformed_jsx,
                    })),
                    false,
                )
            }
        }
        Lambda::Lfunction(mut func) => {
            let body = std::mem::replace(func.body.as_mut(), Lambda::Lbreak);
            let (body, c) = f(body);
            *func.body = body;
            (Lambda::Lfunction(func), c)
        }
        Lambda::Llet(kind, id, e, b) => {
            let (e, c1) = f(*e);
            let (b, c2) = f(*b);
            (Lambda::let_(kind, id, e, b), c1 || c2)
        }
        Lambda::Lletrec(bs, b) => {
            let (bs, c1) = map_snd(bs, f);
            let (b, c2) = f(*b);
            (Lambda::letrec(bs, b), c1 || c2)
        }
        Lambda::Lprim(prim) => {
            let PrimInfo { primitive, args, loc } = *prim;
            let (args, c) = map_list(args, f);
            if c {
                (Lambda::prim(primitive, args, loc), true)
            } else {
                (Lambda::Lprim(Box::new(PrimInfo { primitive, args, loc })), false)
            }
        }
        Lambda::Lswitch(e, sw) => {
            let (e, c1) = f(*e);
            let LambdaSwitch {
                sw_consts_full,
                sw_consts,
                sw_blocks_full,
                sw_blocks,
                sw_failaction,
                sw_dispatch,
            } = *sw;
            let (sw_consts, c2) = map_snd(sw_consts, f);
            let (sw_blocks, c3) = map_snd(sw_blocks, f);
            let (sw_failaction, c4) = map_opt(sw_failaction, f);
            let sw = LambdaSwitch {
                sw_consts_full,
                sw_consts,
                sw_blocks_full,
                sw_blocks,
                sw_failaction,
                sw_dispatch,
            };
            if c1 || c2 || c3 || c4 {
                (Lambda::switch(e, sw), true)
            } else {
                (Lambda::Lswitch(Box::new(e), Box::new(sw)), false)
            }
        }
        Lambda::LstringSwitch(e, cases, d) => {
            let (e, c1) = f(*e);
            let (cases, c2) = map_snd(cases, f);
            let (d, c3) = map_opt(d, f);
            if c1 || c2 || c3 {
                (Lambda::string_switch(e, cases, d), true)
            } else {
                (Lambda::LstringSwitch(Box::new(e), cases, d), false)
            }
        }
        Lambda::LstaticRaise(i, args) => {
            let (args, c) = map_list(args, f);
            (Lambda::static_raise(i, args), c)
        }
        Lambda::LstaticCatch(b, h, hd) => {
            let (b, c1) = f(*b);
            let (hd, c2) = f(*hd);
            (Lambda::LstaticCatch(Box::new(b), h, Box::new(hd)), c1 || c2)
        }
        Lambda::LtryWith(b, id, h) => {
            let (b, c1) = f(*b);
            let (h, c2) = f(*h);
            (Lambda::try_(b, id, h), c1 || c2)
        }
        Lambda::LifThenElse(a, b, c) => {
            let (a, c1) = f(*a);
            let (b, c2) = f(*b);
            let (c, c3) = f(*c);
            if c1 || c2 || c3 {
                (Lambda::if_(a, b, c), true)
            } else {
                (Lambda::LifThenElse(Box::new(a), Box::new(b), Box::new(c)), false)
            }
        }
        Lambda::Lsequence(a, b) => {
            let (a, c1) = f(*a);
            let (b, c2) = f(*b);
            if c1 || c2 {
                (Lambda::seq(a, b), true)
            } else {
                (Lambda::Lsequence(Box::new(a), Box::new(b)), false)
            }
        }
        Lambda::Lwhile(a, b) => {
            let (a, c1) = f(*a);
            let (b, c2) = f(*b);
            (Lambda::while_(a, b), c1 || c2)
        }
        Lambda::Lfor(id, a, b, d, c) => {
            let (a, c1) = f(*a);
            let (b, c2) = f(*b);
            let (c, c3) = f(*c);
            (Lambda::for_(id, a, b, d, c), c1 || c2 || c3)
        }
        Lambda::Lfor_of(id, a, b) => {
            let (a, c1) = f(*a);
            let (b, c2) = f(*b);
            (Lambda::for_of(id, a, b), c1 || c2)
        }
        Lambda::Lfor_await_of(id, a, b) => {
            let (a, c1) = f(*a);
            let (b, c2) = f(*b);
            (Lambda::for_await_of(id, a, b), c1 || c2)
        }
        Lambda::Lassign(id, b) => {
            let (b, c) = f(*b);
            (Lambda::assign(id, b), c)
        }
    }
}
