//! Direct port of `compiler/core/lam_hit.ml`.
//!
//! Predicates that ask "does this identifier occur anywhere in this lambda
//! tree?". Unlike a free-variable analysis, these predicates do not respect
//! binders — they detect occurrences whether or not they are bound by an
//! enclosing `let`/`fun`/etc. This conservative semantic matches OCaml.
//!
//! Each match arm corresponds to a specific line in `lam_hit.ml`. Do not add
//! Rust-only logic.

use crate::ident::Ident;
use crate::lambda::{LFunction, Lambda};

/// Direct port of `Lam_hit.hit_variable` (lam_hit.ml:62-94).
///
/// Returns true when `fv` appears anywhere in `l` — as a free variable, as a
/// bound variable in some inner construct, or as the target of an `Lassign`.
pub fn hit_variable(fv: &Ident, l: &Lambda) -> bool {
    fn hit_opt(fv: &Ident, x: Option<&Lambda>) -> bool {
        x.is_some_and(|a| hit(fv, a))
    }
    fn hit_var(fv: &Ident, id: &Ident) -> bool {
        // OCaml uses `Ident.same`, which compares by stamp + name
        // (lam_hit.ml:67). PartialEq on Rust's Ident is the equivalent.
        id == fv
    }
    fn hit_list_snd<T>(fv: &Ident, xs: &[(T, Lambda)]) -> bool {
        xs.iter().any(|(_, l)| hit(fv, l))
    }
    fn hit_list(fv: &Ident, xs: &[Lambda]) -> bool {
        xs.iter().any(|l| hit(fv, l))
    }
    fn hit(fv: &Ident, l: &Lambda) -> bool {
        match l {
            Lambda::Lvar(id) => hit_var(fv, id),
            Lambda::Lassign(id, e) => hit_var(fv, id) || hit(fv, e),
            Lambda::LstaticCatch(e1, _, e2) => hit(fv, e1) || hit(fv, e2),
            Lambda::LtryWith(e1, _, e2) => hit(fv, e1) || hit(fv, e2),
            Lambda::Lfunction(__func0) => {
                let LFunction { body, .. } = __func0.as_ref();
                hit(fv, body)
            }
            Lambda::Llet(_, _, arg, body) => hit(fv, arg) || hit(fv, body),
            Lambda::Lletrec(decl, body) => hit(fv, body) || hit_list_snd(fv, decl),
            Lambda::Lfor(_, e1, e2, _, e3) => hit(fv, e1) || hit(fv, e2) || hit(fv, e3),
            Lambda::Lfor_of(_, e1, e2) | Lambda::Lfor_await_of(_, e1, e2) => {
                hit(fv, e1) || hit(fv, e2)
            }
            Lambda::Lconst(_) => false,
            Lambda::Lapply(apply) => hit(fv, &apply.ap_func) || hit_list(fv, &apply.ap_args),
            // Global persistent module — play safe (lam_hit.ml:48).
            Lambda::LglobalModule(_) => false,
            Lambda::Lprim(prim) => hit_list(fv, &prim.args),
            Lambda::Lswitch(arg, sw) => {
                hit(fv, arg)
                    || hit_list_snd(fv, &sw.sw_consts)
                    || hit_list_snd(fv, &sw.sw_blocks)
                    || hit_opt(fv, sw.sw_failaction.as_deref())
            }
            Lambda::LstringSwitch(arg, cases, default) => {
                hit(fv, arg) || hit_list_snd(fv, cases) || hit_opt(fv, default.as_deref())
            }
            Lambda::LstaticRaise(_, args) => hit_list(fv, args),
            Lambda::LifThenElse(e1, e2, e3) => hit(fv, e1) || hit(fv, e2) || hit(fv, e3),
            Lambda::Lsequence(e1, e2) => hit(fv, e1) || hit(fv, e2),
            Lambda::Lwhile(e1, e2) => hit(fv, e1) || hit(fv, e2),
            Lambda::Lbreak | Lambda::Lcontinue => false,
        }
    }
    hit(fv, l)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ident::{Ident, IdentFlags};
    use crate::lambda::lam_compat::LetKind;
    use crate::lambda::lam_constant::Constant;

    fn ident(name: &str, stamp: i32) -> Ident {
        Ident::new(name, stamp, IdentFlags::NONE)
    }

    #[test]
    fn detects_var_use() {
        let v = ident("v", 1);
        assert!(hit_variable(&v, &Lambda::Lvar(v.clone())));
    }

    #[test]
    fn does_not_detect_unrelated_var() {
        let v = ident("v", 1);
        let other = ident("other", 2);
        assert!(!hit_variable(&v, &Lambda::Lvar(other)));
    }

    /// `let v = 1 in v` should report v as hit even though it is bound — OCaml's
    /// hit_variable does not respect binders (lam_hit.ml:74-79).
    #[test]
    fn detects_var_inside_own_let() {
        let v = ident("v", 1);
        let lam = Lambda::let_(
            LetKind::Strict,
            v.clone(),
            Lambda::Lconst(Constant::int(1)),
            Lambda::Lvar(v.clone()),
        );
        assert!(hit_variable(&v, &lam));
    }
}
