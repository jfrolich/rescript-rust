//! Direct port of `compiler/core/lam_pass_lets_dce.ml`.
//!
//! Combines dead-code elimination of let bindings with alias inlining: every
//! decision is driven by the precomputed [`OccurrenceTable`] from
//! [`super::lam_pass_count::collect_occurs`], so this pass is O(n).
//!
//! Each match arm cites the OCaml line in `lam_pass_lets_dce.ml` that
//! justifies it. Do not introduce Rust-only logic.

use ahash::AHashMap as HashMap;

use crate::ident::Ident;
use crate::lambda::lam_analysis::{lfunction_can_be_inlined, no_side_effects};
use crate::lambda::lam_beta_reduce::no_names_beta_reduce;
use crate::lambda::lam_compat::LetKind;
use crate::lambda::lam_constant::Constant;
use crate::lambda::lam_pass_count::{OccurrenceTable, UsedInfo, collect_occurs};
use crate::lambda::lam_primitive::Primitive;
use crate::lambda::lam_util::refine_let_original;
use crate::lambda::lambda_traverse::{Mapped, shallow_map_sharing};
use crate::lambda::{Apply, Lambda, PrimInfo};

/// State held during the recursive pass: substitution table and an inline
/// string table for downstream `Pstringadd` constant folding. Both mirror
/// OCaml's `Hash_ident.t` (lam_pass_lets_dce.ml:15-16).
struct LetsState<'a> {
    occ: &'a OccurrenceTable,
    subst: HashMap<Ident, Lambda>,
    string_table: HashMap<Ident, String>,
}

impl<'a> LetsState<'a> {
    fn new(occ: &'a OccurrenceTable) -> Self {
        Self {
            occ,
            subst: HashMap::with_capacity(32),
            string_table: HashMap::with_capacity(32),
        }
    }

    /// Equivalent of OCaml's `count_var v` lookup
    /// (lam_pass_lets_dce.ml:209-213): returns the recorded info or the dummy.
    fn count_var(&self, v: &Ident) -> UsedInfo {
        self.occ.get(v)
    }

    /// Equivalent of OCaml's `used` helper (lam_pass_lets_dce.ml:17).
    fn used(&self, v: &Ident) -> bool {
        self.count_var(v).times > 0
    }
}

/// Direct port of `Lam_pass_lets_dce.lets_helper` (lam_pass_lets_dce.ml:14-140).
fn lets_helper_owned(state: &mut LetsState<'_>, lam: Lambda) -> Lambda {
    simplif(state, lam).0
}

/// `simplif` from `Lam_pass_lets_dce.lets_helper`. The flag reports whether
/// the result differs from the input, which OCaml reads off physical
/// equality: an unchanged node is handed back as is, and a changed child
/// makes `shallow_map_sharing` rebuild its parent through the smart
/// constructor.
fn simplif(state: &mut LetsState<'_>, lam: Lambda) -> Mapped {
    match lam {
        Lambda::Lvar(v) => match state.subst.get(&v) {
            Some(replacement) => (replacement.clone(), true),
            None => (Lambda::Lvar(v), false),
        },

        Lambda::Llet(kind, v, value, l2)
            if matches!(value.as_ref(), Lambda::Lvar(_))
                && matches!(kind, LetKind::Strict | LetKind::Alias | LetKind::StrictOpt) =>
        {
            let Lambda::Lvar(w) = *value else {
                unreachable!()
            };
            let (simplified_w, _) = simplif(state, Lambda::Lvar(w));
            state.subst.insert(v, simplified_w);
            (simplif(state, *l2).0, true)
        }

        Lambda::Llet(LetKind::Alias, v, l1, l2) => {
            let info = state.count_var(&v);
            if info.times == 0 {
                return (simplif(state, *l2).0, true);
            }

            let small_const = matches!(
                l1.as_ref(),
                Lambda::Lconst(
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
                l1.as_ref(),
                Lambda::Lprim(prim) if matches!(prim.as_ref(), PrimInfo {
                    primitive: Primitive::Pfield(_, _),
                    args,
                    ..
                } if args.len() == 1 && matches!(args[0], Lambda::LglobalModule(_)))
            );
            let subst_now = (info.times == 1 && !info.captured)
                || (info.times == 1
                    && info.captured
                    && matches!(l1.as_ref(), Lambda::Lconst(_) | Lambda::Lvar(_)))
                || small_const
                || pfield_from_global;

            if subst_now {
                let (simplified, _) = simplif(state, *l1);
                state.subst.insert(v, simplified);
                return (simplif(state, *l2).0, true);
            }

            if let Lambda::Lconst(Constant::String(s)) = l1.as_ref() {
                state.string_table.insert(v, s.clone());
                let (simplified_body, _) = simplif(state, *l2);
                return (Lambda::let_(LetKind::Alias, v, *l1, simplified_body), true);
            }

            // `simplif` records substitutions as it goes, and OCaml simplifies
            // the body before the bound expression here.
            let (new_l2, c2) = simplif(state, *l2);
            let (new_l1, c1) = simplif(state, *l1);
            (Lambda::let_(LetKind::Alias, v, new_l1, new_l2), c1 || c2)
        }

        Lambda::Llet(LetKind::StrictOpt, v, l1, lbody) => {
            if !state.used(&v) {
                return (simplif(state, *lbody).0, true);
            }
            let (new_l1, c1) = simplif(state, *l1);
            if let Lambda::Lconst(Constant::String(s)) = &new_l1 {
                state.string_table.insert(v, s.clone());
                let (simplified_body, _) = simplif(state, *lbody);
                return (
                    Lambda::let_(LetKind::Alias, v, new_l1, simplified_body),
                    true,
                );
            }
            let (simplified_body, c2) = simplif(state, *lbody);
            refine_let_original(LetKind::StrictOpt, v, new_l1, simplified_body, !(c1 || c2))
        }

        Lambda::Llet(kind @ (LetKind::Strict | LetKind::Variable), v, l1, l2) => {
            if !state.used(&v) {
                let (new_l1, _) = simplif(state, *l1);
                let (new_l2, _) = simplif(state, *l2);
                return (
                    if no_side_effects(&new_l1) {
                        new_l2
                    } else {
                        Lambda::seq(new_l1, new_l2)
                    },
                    true,
                );
            }
            let (new_l1, c1) = simplif(state, *l1);
            if matches!(kind, LetKind::Strict) {
                if let Lambda::Lconst(Constant::String(s)) = &new_l1 {
                    state.string_table.insert(v, s.clone());
                    let (simplified_body, _) = simplif(state, *l2);
                    return (
                        Lambda::let_(LetKind::Alias, v, new_l1, simplified_body),
                        true,
                    );
                }
            }
            let (simplified_body, c2) = simplif(state, *l2);
            refine_let_original(kind, v, new_l1, simplified_body, !(c1 || c2))
        }

        Lambda::Lapply(apply)
            if matches!(apply.ap_func.as_ref(), Lambda::Lfunction(func)
                if func.params.len() == apply.ap_args.len() && lfunction_can_be_inlined(func)) =>
        {
            let Apply {
                ap_func, ap_args, ..
            } = *apply;
            let Lambda::Lfunction(func) = *ap_func else {
                unreachable!()
            };
            let reduced = no_names_beta_reduce(&func.params, &func.body, &ap_args);
            (simplif(state, reduced).0, true)
        }

        Lambda::Lprim(prim)
            if matches!(prim.as_ref(), PrimInfo {
                primitive: Primitive::Pstringadd,
                args,
                ..
            } if args.len() == 2) =>
        {
            let PrimInfo { args, loc, .. } = *prim;
            let mut args = args.into_iter();
            let (l_simpl, _) = simplif(state, args.next().expect("checked left arg"));
            let (r_simpl, _) = simplif(state, args.next().expect("checked right arg"));
            let folded = match lookup_string(&l_simpl, &state.string_table) {
                None => None,
                Some(l_s) => lookup_string(&r_simpl, &state.string_table)
                    .map(|r_s| Lambda::Lconst(Constant::String([l_s, r_s].concat()))),
            };
            let result = folded.unwrap_or_else(|| {
                Lambda::prim(Primitive::Pstringadd, vec![l_simpl, r_simpl], loc)
            });
            (result, true)
        }

        _ => shallow_map_sharing(lam, &mut |child| simplif(state, child)),
    }
}

/// Equivalent of OCaml's nested string-table lookup used by the Pstringadd
/// branch (lam_pass_lets_dce.ml:158-163, 167-172). Returns Some(s) when the
/// argument is an inline string literal or an alias for one.
fn lookup_string<'a>(lam: &'a Lambda, table: &'a HashMap<Ident, String>) -> Option<&'a str> {
    match lam {
        Lambda::Lconst(Constant::String(s)) => Some(s),
        Lambda::Lvar(i) => table.get(i).map(String::as_str),
        _ => None,
    }
}

/// Borrowing test helper around [`simplify_lets_owned`].
#[cfg(test)]
fn simplify_lets(lam: &Lambda) -> Lambda {
    simplify_lets_owned(lam.clone())
}

/// Owned form of `Lam_pass_lets_dce.simplify_lets`
/// (compiler/core/lam_pass_lets_dce.ml:216-219).
pub fn simplify_lets_owned(lam: Lambda) -> Lambda {
    let occ = collect_occurs(&lam);
    let mut state = LetsState::new(&occ);
    lets_helper_owned(&mut state, lam)
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

    /// `let x = 1 in x` -> `1` via Alias single-use substitution
    /// (lam_pass_lets_dce.ml:50). Need an Alias kind to enter that arm.
    #[test]
    fn alias_single_use_const_substitutes() {
        let x = ident("x", 100);
        let lam = Lambda::let_(
            LetKind::Alias,
            x,
            Lambda::Lconst(Constant::int(1)),
            Lambda::Lvar(x),
        );
        let result = simplify_lets(&lam);
        assert!(matches!(result, Lambda::Lconst(Constant::Int { i: 1, .. })));
    }

    /// `let x = e in (); x` Alias unused -> drop binding
    /// (lam_pass_lets_dce.ml:49).
    #[test]
    fn alias_unused_binding_dropped() {
        let x = ident("x", 101);
        let other = ident("y", 102);
        let lam = Lambda::let_(
            LetKind::Alias,
            x,
            Lambda::Lconst(Constant::int(1)),
            Lambda::Lvar(other),
        );
        let result = simplify_lets(&lam);
        match result {
            Lambda::Lvar(id) => assert_eq!(id, other),
            other => panic!("expected Lvar, got {:?}", other),
        }
    }

    /// `let x = pure_e in (sequence)` Strict + unused + side-effect-free RHS
    /// -> drop the binding (lam_pass_lets_dce.ml:122-125).
    #[test]
    fn strict_unused_pure_dropped() {
        let x = ident("x", 103);
        let other = ident("y", 104);
        let lam = Lambda::let_(
            LetKind::Strict,
            x,
            Lambda::Lconst(Constant::int(7)),
            Lambda::Lvar(other),
        );
        let result = simplify_lets(&lam);
        match result {
            Lambda::Lvar(id) => assert_eq!(id, other),
            other => panic!("expected Lvar, got {:?}", other),
        }
    }

    /// `let x = "a" in let y = "b" in x ^ y` -> `"ab"` via string folding
    /// (lam_pass_lets_dce.ml:155-175).
    #[test]
    fn pstringadd_folds_through_string_table() {
        let x = ident("x", 105);
        let y = ident("y", 106);
        let concat = Lambda::prim(
            Primitive::Pstringadd,
            vec![Lambda::Lvar(x), Lambda::Lvar(y)],
            crate::location::Location::none(),
        );
        let inner = Lambda::let_(
            LetKind::Alias,
            y,
            Lambda::Lconst(Constant::string("b")),
            concat,
        );
        let lam = Lambda::let_(
            LetKind::Alias,
            x,
            Lambda::Lconst(Constant::string("a")),
            inner,
        );
        let result = simplify_lets(&lam);
        // After folding the two inner alias substitutions, Pstringadd folds.
        // Outer let-bindings are dropped because their times become 0 once
        // their uses are inlined and the Alias clause prunes them.
        match result {
            Lambda::Lconst(Constant::String(s)) => assert_eq!(s, "ab"),
            other => panic!("expected folded string, got {:?}", other),
        }
    }
}
