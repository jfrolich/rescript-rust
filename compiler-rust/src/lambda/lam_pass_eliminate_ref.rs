//! Direct port of `compiler/core/lam_pass_eliminate_ref.ml`.
//!
//! Specialises a single mutable reference into a plain mutable variable when
//! that is observably safe. Used by `Lam_pass_lets_dce` for the
//! `let v = ref e0 in body` pattern: if every read/write of `v` looks like a
//! plain field-0 access, we can rewrite it to `let v = e0; body`.
//!
//! The pass either succeeds and returns the rewritten lambda, or aborts via
//! the [`RealReference`] error to signal that the binding cannot be reified.
//! That mirrors OCaml's `Real_reference` exception (lam_pass_eliminate_ref.ml:14).
//!
//! Each match arm cites the OCaml line that justifies it.

use crate::ident::Ident;
use crate::lambda::lam_hit::hit_variable;
use crate::lambda::lam_primitive::Primitive;
use crate::lambda::{Apply, Lambda, LambdaSwitch, PrimInfo};

/// Equivalent of OCaml's `Real_reference` exception
/// (lam_pass_eliminate_ref.ml:14). The caller treats this as a signal to
/// abandon the rewrite and keep the original binding intact.
#[derive(Debug, Clone, Copy)]
pub struct RealReference;

/// Direct port of `eliminate_ref id lam` (lam_pass_eliminate_ref.ml:16-102).
///
/// Returns `Ok(rewritten)` when every reference to `id` corresponds to a plain
/// `!id` (Pfield 0) read, an `id := e` write (Psetfield 0), or an `incr`/`decr`
/// (Poffsetref). Returns `Err(RealReference)` when `id` is read/passed
/// directly anywhere else, including being captured by a closure.
pub fn eliminate_ref(id: &Ident, lam: &Lambda) -> Result<Lambda, RealReference> {
    match lam {
        // Lvar: plain reference to id is a real use (lam_pass_eliminate_ref.ml:19).
        Lambda::Lvar(v) => {
            if v == id {
                Err(RealReference)
            } else {
                Ok(lam.clone())
            }
        }

        // `!id` read via `Pfield(0, _)` (lam_pass_eliminate_ref.ml:20-21).
        Lambda::Lprim(__prim2)
            if matches!(__prim2.as_ref(), PrimInfo {
            primitive: Primitive::Pfield(0, _),
            args,
            ..
        } if args.len() == 1 && matches!(&args[0], Lambda::Lvar(v) if v == id)) =>
        {
            let PrimInfo {
                primitive: Primitive::Pfield(0, _),
                args,
                ..
            } = __prim2.as_ref()
            else {
                unreachable!()
            };

            Ok(Lambda::Lvar(id.clone()))
        }

        // Lfunction: a closure reading id at all is unsafe to reify
        // (lam_pass_eliminate_ref.ml:22-23).
        Lambda::Lfunction(_) => {
            if hit_variable(id, lam) {
                Err(RealReference)
            } else {
                Ok(lam.clone())
            }
        }

        // `id := e` via `Psetfield(0, _)` (lam_pass_eliminate_ref.ml:47-49).
        Lambda::Lprim(__prim1)
            if matches!(__prim1.as_ref(), PrimInfo {
            primitive: Primitive::Psetfield(0, _),
            args,
            ..
        } if args.len() == 2 && matches!(&args[0], Lambda::Lvar(v) if v == id)) =>
        {
            let PrimInfo {
                primitive: Primitive::Psetfield(0, _),
                args,
                ..
            } = __prim1.as_ref()
            else {
                unreachable!()
            };

            let new_value = eliminate_ref(id, &args[1])?;
            Ok(Lambda::Lassign(id.clone(), Box::new(new_value)))
        }

        // `incr`/`decr` via `Poffsetref delta` (lam_pass_eliminate_ref.ml:50-53).
        Lambda::Lprim(__prim0)
            if matches!(__prim0.as_ref(), PrimInfo {
            primitive: Primitive::Poffsetref(delta),
            args,
            loc,
        } if args.len() == 1 && matches!(&args[0], Lambda::Lvar(v) if v == id)) =>
        {
            let PrimInfo {
                primitive: Primitive::Poffsetref(delta),
                args,
                loc,
            } = __prim0.as_ref()
            else {
                unreachable!()
            };

            let inc = Lambda::prim(
                Primitive::Poffsetint(*delta),
                vec![Lambda::Lvar(id.clone())],
                loc.clone(),
            );
            Ok(Lambda::Lassign(id.clone(), Box::new(inc)))
        }

        // Lconst (lam_pass_eliminate_ref.ml:54).
        Lambda::Lconst(_) => Ok(lam.clone()),

        // Lapply (lam_pass_eliminate_ref.ml:55-58).
        Lambda::Lapply(apply) => {
            let new_func = eliminate_ref(id, &apply.ap_func)?;
            let new_args: Result<Vec<_>, _> =
                apply.ap_args.iter().map(|a| eliminate_ref(id, a)).collect();
            Ok(Lambda::Lapply(Box::new(Apply {
                ap_func: Box::new(new_func),
                ap_args: new_args?,
                ap_info: apply.ap_info.clone(),
                ap_transformed_jsx: apply.ap_transformed_jsx,
            })))
        }

        // Llet (lam_pass_eliminate_ref.ml:59-60).
        Lambda::Llet(kind, v, e1, e2) => {
            let new_e1 = eliminate_ref(id, e1)?;
            let new_e2 = eliminate_ref(id, e2)?;
            Ok(Lambda::let_(*kind, v.clone(), new_e1, new_e2))
        }

        // Lletrec (lam_pass_eliminate_ref.ml:61-64).
        Lambda::Lletrec(decls, body) => {
            let new_decls: Result<Vec<_>, _> = decls
                .iter()
                .map(|(v, e)| eliminate_ref(id, e).map(|new_e| (v.clone(), new_e)))
                .collect();
            let new_body = eliminate_ref(id, body)?;
            Ok(Lambda::letrec(new_decls?, new_body))
        }

        // Lglobal_module (lam_pass_eliminate_ref.ml:65).
        Lambda::LglobalModule(_, _) => Ok(lam.clone()),

        // Lprim (general) (lam_pass_eliminate_ref.ml:66-67).
        Lambda::Lprim(prim) => {
            let new_args: Result<Vec<_>, _> =
                prim.args.iter().map(|a| eliminate_ref(id, a)).collect();
            Ok(Lambda::prim(
                prim.primitive.clone(),
                new_args?,
                prim.loc.clone(),
            ))
        }

        // Lswitch (lam_pass_eliminate_ref.ml:68-82).
        Lambda::Lswitch(scrut, sw) => {
            let new_scrut = eliminate_ref(id, scrut)?;
            let new_consts: Result<Vec<_>, _> = sw
                .sw_consts
                .iter()
                .map(|(n, e)| eliminate_ref(id, e).map(|new_e| (n.clone(), new_e)))
                .collect();
            let new_blocks: Result<Vec<_>, _> = sw
                .sw_blocks
                .iter()
                .map(|(n, e)| eliminate_ref(id, e).map(|new_e| (n.clone(), new_e)))
                .collect();
            let new_failaction = match &sw.sw_failaction {
                None => None,
                Some(x) => Some(Box::new(eliminate_ref(id, x)?)),
            };
            Ok(Lambda::Lswitch(
                Box::new(new_scrut),
                Box::new(LambdaSwitch {
                    sw_consts_full: sw.sw_consts_full,
                    sw_consts: new_consts?,
                    sw_blocks_full: sw.sw_blocks_full,
                    sw_blocks: new_blocks?,
                    sw_failaction: new_failaction,
                    sw_dispatch: sw.sw_dispatch.clone(),
                }),
            ))
        }

        // Lstringswitch (lam_pass_eliminate_ref.ml:83-88).
        Lambda::LstringSwitch(scrut, cases, default) => {
            let new_scrut = eliminate_ref(id, scrut)?;
            let new_cases: Result<Vec<_>, _> = cases
                .iter()
                .map(|(s, e)| eliminate_ref(id, e).map(|new_e| (s.clone(), new_e)))
                .collect();
            let new_default = match default {
                None => None,
                Some(x) => Some(Box::new(eliminate_ref(id, x)?)),
            };
            Ok(Lambda::LstringSwitch(
                Box::new(new_scrut),
                new_cases?,
                new_default,
            ))
        }

        // Lstaticraise (lam_pass_eliminate_ref.ml:89-90).
        Lambda::LstaticRaise(i, args) => {
            let new_args: Result<Vec<_>, _> = args.iter().map(|a| eliminate_ref(id, a)).collect();
            Ok(Lambda::LstaticRaise(*i, new_args?))
        }

        // Lstaticcatch (lam_pass_eliminate_ref.ml:91-92).
        Lambda::LstaticCatch(e1, label, e2) => {
            let new_e1 = eliminate_ref(id, e1)?;
            let new_e2 = eliminate_ref(id, e2)?;
            Ok(Lambda::LstaticCatch(
                Box::new(new_e1),
                label.clone(),
                Box::new(new_e2),
            ))
        }

        // Ltrywith (lam_pass_eliminate_ref.ml:93-94).
        Lambda::LtryWith(e1, v, e2) => {
            let new_e1 = eliminate_ref(id, e1)?;
            let new_e2 = eliminate_ref(id, e2)?;
            Ok(Lambda::LtryWith(
                Box::new(new_e1),
                v.clone(),
                Box::new(new_e2),
            ))
        }

        // Lifthenelse (lam_pass_eliminate_ref.ml:95-96).
        Lambda::LifThenElse(e1, e2, e3) => {
            let new_e1 = eliminate_ref(id, e1)?;
            let new_e2 = eliminate_ref(id, e2)?;
            let new_e3 = eliminate_ref(id, e3)?;
            Ok(Lambda::LifThenElse(
                Box::new(new_e1),
                Box::new(new_e2),
                Box::new(new_e3),
            ))
        }

        // Lsequence (lam_pass_eliminate_ref.ml:97).
        Lambda::Lsequence(e1, e2) => {
            let new_e1 = eliminate_ref(id, e1)?;
            let new_e2 = eliminate_ref(id, e2)?;
            Ok(Lambda::Lsequence(Box::new(new_e1), Box::new(new_e2)))
        }

        // Lwhile (lam_pass_eliminate_ref.ml:98).
        Lambda::Lwhile(e1, e2) => {
            let new_e1 = eliminate_ref(id, e1)?;
            let new_e2 = eliminate_ref(id, e2)?;
            Ok(Lambda::Lwhile(Box::new(new_e1), Box::new(new_e2)))
        }

        // Lfor (lam_pass_eliminate_ref.ml:99-101).
        Lambda::Lfor(v, e1, e2, dir, e3) => {
            let new_e1 = eliminate_ref(id, e1)?;
            let new_e2 = eliminate_ref(id, e2)?;
            let new_e3 = eliminate_ref(id, e3)?;
            Ok(Lambda::Lfor(
                v.clone(),
                Box::new(new_e1),
                Box::new(new_e2),
                *dir,
                Box::new(new_e3),
            ))
        }

        // Lfor_of / Lfor_await_of (lam_pass_eliminate_ref.ml after #7887).
        Lambda::Lfor_of(v, e1, e2) => {
            let new_e1 = eliminate_ref(id, e1)?;
            let new_e2 = eliminate_ref(id, e2)?;
            Ok(Lambda::for_of(v.clone(), new_e1, new_e2))
        }
        Lambda::Lfor_await_of(v, e1, e2) => {
            let new_e1 = eliminate_ref(id, e1)?;
            let new_e2 = eliminate_ref(id, e2)?;
            Ok(Lambda::for_await_of(v.clone(), new_e1, new_e2))
        }

        // Lassign (lam_pass_eliminate_ref.ml:102).
        Lambda::Lassign(v, e) => {
            let new_e = eliminate_ref(id, e)?;
            Ok(Lambda::Lassign(v.clone(), Box::new(new_e)))
        }

        // OCaml `Lam_pass_eliminate_ref.eliminate_ref` after #8348:
        // `Lbreak -> Lam.break | Lcontinue -> Lam.continue`.
        Lambda::Lbreak => Ok(Lambda::break_()),
        Lambda::Lcontinue => Ok(Lambda::continue_()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ident::{Ident, IdentFlags};
    use crate::lambda::lam_compat::{FieldDbgInfo, LetKind};
    use crate::lambda::lam_constant::Constant;
    use crate::location::Location;

    fn ident(name: &str, stamp: i32) -> Ident {
        Ident::new(name, stamp, IdentFlags::NONE)
    }

    /// `!v` (Pfield 0 of v) becomes a plain Lvar v
    /// (lam_pass_eliminate_ref.ml:20-21).
    #[test]
    fn pfield_zero_becomes_var() {
        let v = ident("v", 1);
        let read = Lambda::prim(
            Primitive::Pfield(0, FieldDbgInfo::Tuple),
            vec![Lambda::Lvar(v.clone())],
            Location::none(),
        );
        let result = eliminate_ref(&v, &read).expect("should rewrite");
        match result {
            Lambda::Lvar(id) => assert_eq!(id, v),
            other => panic!("expected Lvar, got {:?}", other),
        }
    }

    /// A direct Lvar reference is a real reference and aborts the rewrite
    /// (lam_pass_eliminate_ref.ml:19).
    #[test]
    fn raw_lvar_reference_aborts() {
        let v = ident("v", 2);
        let lam = Lambda::Lvar(v.clone());
        assert!(eliminate_ref(&v, &lam).is_err());
    }

    /// Lambdas that don't mention `id` pass through unchanged
    /// (lam_pass_eliminate_ref.ml:22-23).
    #[test]
    fn unrelated_function_passes_through() {
        let v = ident("v", 3);
        let p = ident("p", 4);
        let func = Lambda::function_(
            1,
            vec![p],
            Lambda::Lconst(Constant::int(0)),
            crate::lambda::FunctionAttribute {
                inline: crate::lambda::InlineAttribute::Default,
                is_a_functor: false,
                return_unit: false,
                async_: false,
                directive: None,
                one_unit_arg: false,
            },
        );
        assert!(eliminate_ref(&v, &func).is_ok());
    }

    /// A function that captures `id` is a real reference
    /// (lam_pass_eliminate_ref.ml:22-23).
    #[test]
    fn capturing_function_aborts() {
        let v = ident("v", 5);
        let p = ident("p", 6);
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
        );
        assert!(eliminate_ref(&v, &func).is_err());
    }

    /// `let v = ref 0 in !v` should rewrite the body to `let v = 0 in v`
    /// when wired through Llet+Pfield(0,_) arms.
    #[test]
    fn let_with_field_zero_read_rewrites() {
        let v = ident("v", 7);
        let body = Lambda::prim(
            Primitive::Pfield(0, FieldDbgInfo::Tuple),
            vec![Lambda::Lvar(v.clone())],
            Location::none(),
        );
        let lam = Lambda::let_(
            LetKind::Strict,
            v.clone(),
            Lambda::Lconst(Constant::int(0)),
            body,
        );
        let result = eliminate_ref(&v, &lam).expect("should rewrite");
        match result {
            Lambda::Llet(_, id, _, body) => {
                assert_eq!(id, v);
                assert!(matches!(body.as_ref(), Lambda::Lvar(_)));
            }
            other => panic!("expected Llet, got {:?}", other),
        }
    }
}
