//! Direct port of `compiler/core/lam_exit_code.ml`.
//!
//! Predicates on `Lam.t` that detect `Lstaticraise` sites reachable without
//! crossing a `Lfunction` boundary. Used by `flatten_nested_caches` to enforce
//! the #1698 safety check: an outer `Lstaticcatch` may only absorb an inner
//! one if the inner's handler cannot raise back to any already-absorbed label.

use crate::lambda::LamLoc;
use crate::lambda::Lambda;

/// Direct port of `Lam_exit_code.has_exit_code` (lam_exit_code.ml:25-33).
///
/// Returns true when `lam` contains a `Lstaticraise(label, _)` that would
/// reach the current scope, for some `label` satisfying `exits(label)`.
/// `Lfunction` boundaries block the search because static exits cannot cross
/// them (see the `Lfunction _ -> false` arm at lam_exit_code.ml:28).
pub fn has_exit_code<F>(lam: &Lambda, exits: F) -> bool
where
    F: Fn(i32) -> bool,
{
    fn aux<F>(lam: &Lambda, exits: &F) -> bool
    where
        F: Fn(i32) -> bool,
    {
        match lam {
            Lambda::Lfunction(_) => false,
            Lambda::LstaticRaise(p, args) => {
                if exits(*p) {
                    true
                } else {
                    args.iter().any(|a| aux(a, exits))
                }
            }
            Lambda::Lvar(_) | Lambda::LglobalModule(_) | Lambda::Lconst(_) => false,
            Lambda::Lapply(apply) => {
                aux(&apply.ap_func, exits) || apply.ap_args.iter().any(|a| aux(a, exits))
            }
            Lambda::Llet(_, _, arg, body) => aux(arg, exits) || aux(body, exits),
            Lambda::Lletrec(decl, body) => {
                aux(body, exits) || decl.iter().any(|(_, l)| aux(l, exits))
            }
            Lambda::Lprim(prim) => prim.args.iter().any(|a| aux(a, exits)),
            Lambda::Lswitch(arg, sw) => {
                aux(arg, exits)
                    || sw.sw_consts.iter().any(|(_, l)| aux(l, exits))
                    || sw.sw_blocks.iter().any(|(_, l)| aux(l, exits))
                    || sw.sw_failaction.as_deref().is_some_and(|l| aux(l, exits))
            }
            Lambda::LstringSwitch(arg, cases, default) => {
                aux(arg, exits)
                    || cases.iter().any(|(_, l)| aux(l, exits))
                    || default.as_deref().is_some_and(|l| aux(l, exits))
            }
            Lambda::LstaticCatch(e1, _, e2) => aux(e1, exits) || aux(e2, exits),
            Lambda::LtryWith(e1, _, e2) | Lambda::LtryFinally(e1, e2) => {
                aux(e1, exits) || aux(e2, exits)
            }
            Lambda::LifThenElse(e1, e2, e3) => aux(e1, exits) || aux(e2, exits) || aux(e3, exits),
            Lambda::Lsequence(e1, e2) => aux(e1, exits) || aux(e2, exits),
            Lambda::Lwhile(e1, e2) => aux(e1, exits) || aux(e2, exits),
            Lambda::Lfor(_, e1, e2, _, e3) => aux(e1, exits) || aux(e2, exits) || aux(e3, exits),
            Lambda::Lfor_of(_, e1, e2) | Lambda::Lfor_await_of(_, e1, e2) => {
                aux(e1, exits) || aux(e2, exits)
            }
            Lambda::Lbreak | Lambda::Lcontinue => false,
            Lambda::Lassign(_, e) => aux(e, exits),
        }
    }
    aux(lam, &exits)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ident::{Ident, IdentFlags};
    use crate::lambda::lam_constant::Constant;

    fn ident(name: &str, stamp: i32) -> Ident {
        Ident::new(name, stamp, IdentFlags::NONE)
    }

    #[test]
    fn detects_staticraise_in_body() {
        let lam = Lambda::LstaticRaise(3, vec![]);
        assert!(has_exit_code(&lam, |p| p == 3));
        assert!(!has_exit_code(&lam, |p| p == 4));
    }

    #[test]
    fn stops_at_lfunction_boundary() {
        use crate::lambda::LFunction;
        let body = Lambda::LstaticRaise(1, vec![]);
        let func = Lambda::Lfunction(Box::new(LFunction {
            loc: LamLoc::NONE,
            arity: 0,
            params: vec![],
            body: Box::new(body),
            attr: Default::default(),
        }));
        assert!(!has_exit_code(&func, |_| true));
    }

    #[test]
    fn recurses_through_ifthenelse() {
        let lam = Lambda::LifThenElse(
            Box::new(Lambda::Lconst(Constant::int(1))),
            Box::new(Lambda::Lconst(Constant::int(2))),
            Box::new(Lambda::LstaticRaise(7, vec![])),
        );
        assert!(has_exit_code(&lam, |p| p == 7));
        assert!(!has_exit_code(&lam, |p| p == 8));
    }

    #[test]
    fn recurses_into_staticcatch() {
        let inner = Lambda::LstaticRaise(5, vec![]);
        let catch = Lambda::LstaticCatch(
            Box::new(inner),
            (2, vec![ident("x", 1)]),
            Box::new(Lambda::Lconst(Constant::int(0))),
        );
        assert!(has_exit_code(&catch, |p| p == 5));
        assert!(!has_exit_code(&catch, |p| p == 2));
    }
}
