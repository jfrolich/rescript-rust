//! Direct port of helpers from `compiler/core/lam_util.ml`.
//!
//! Currently only ports the `refine_let` family that the JS-backend
//! `Lam_pass_lets_dce` pass relies on. Each branch cites the exact OCaml line
//! that justifies it; do not introduce Rust-only logic.

use crate::ident::Ident;
use crate::lambda::compat::LetKind;
use crate::lambda::lam_hit::hit_variable;
use crate::lambda::primitive::{Mutable, Primitive};
use crate::lambda::{analysis, Apply, Lambda, PrimInfo};

/// Equivalent of OCaml's `is_block_constructor` (lam_util.ml:69-72).
fn is_block_constructor(primitive: &Primitive) -> bool {
    matches!(primitive, Primitive::Pmakeblock(_, _, _))
}

/// Equivalent of OCaml's `is_safe_to_alias` recursive helper
/// (lam_util.ml:79-98). `Lvar`/`Lconst`, `Pfield` reads from a global module
/// or local var, and `PsomeNotNest` wrappers around already-safe expressions
/// are deemed safe to evaluate twice (so that lowering them to `Alias` does
/// not change observable evaluation order).
fn is_safe_to_alias(lam: &Lambda) -> bool {
    match lam {
        Lambda::Lvar(_) | Lambda::Lconst(_) => true,
        Lambda::Lprim(PrimInfo {
            primitive: Primitive::Pfield(_, dbg_info),
            args,
            ..
        }) if matches!(dbg_info, crate::lambda::compat::FieldDbgInfo::Module { .. })
            && args.len() == 1
            && matches!(
                args[0],
                Lambda::LglobalModule(_, _) | Lambda::Lvar(_)
            ) =>
        {
            true
        }
        Lambda::Lprim(PrimInfo {
            primitive: Primitive::PsomeNotNest,
            args,
            ..
        }) if args.len() == 1 => is_safe_to_alias(&args[0]),
        _ => false,
    }
}

/// Direct port of `Lam_util.refine_let` (lam_util.ml:68-138).
///
/// Normalises a let binding into a tighter representation when one of the
/// rewrite clauses applies. The clauses are matched in the same order as
/// OCaml so that the JS backend never sees a binding that was over- or
/// under-relaxed relative to the OCaml reference.
pub fn refine_let(kind: LetKind, param: Ident, arg: Lambda, body: Lambda) -> Lambda {
    match (&kind, &arg, &body) {
        // (Return) `let[k] x = e in x` -> `e` (lam_util.ml:100-104).
        (_, _, Lambda::Lvar(w)) if w == &param => arg,

        // (Prim) `let[k] x = e in prim p [x]` -> `prim p [e]`, when `p` is not
        // a block constructor (lam_util.ml:105-111).
        (
            _,
            _,
            Lambda::Lprim(PrimInfo {
                primitive,
                args,
                loc,
            }),
        ) if args.len() == 1
            && matches!(&args[0], Lambda::Lvar(w) if w == &param)
            && !is_block_constructor(primitive) =>
        {
            Lambda::prim(primitive.clone(), vec![arg], loc.clone())
        }

        // (Call) `let[k] x = e in fn(x)` -> `fn(e)`, when fn does not capture
        // x (lam_util.ml:112-117). Uses lam_hit.hit_variable for the capture
        // check, exactly as OCaml does.
        (_, _, Lambda::Lapply(apply))
            if apply.ap_args.len() == 1
                && matches!(&apply.ap_args[0], Lambda::Lvar(w) if w == &param)
                && !hit_variable(&param, &apply.ap_func) =>
        {
            Lambda::Lapply(Apply {
                ap_func: apply.ap_func.clone(),
                ap_args: vec![arg],
                ap_info: apply.ap_info.clone(),
                ap_transformed_jsx: apply.ap_transformed_jsx,
            })
        }

        // (Alias) `let[Strict|StrictOpt] x = e in body` with safe-to-alias e
        // -> `let[Alias] x = e in body` (lam_util.ml:118-124).
        (LetKind::Strict | LetKind::StrictOpt, _, _) if is_safe_to_alias(&arg) => {
            Lambda::let_(LetKind::Alias, param, arg, body)
        }

        // (Strict λ) `let[Strict] x = fn in body` -> `let[StrictOpt] x = fn in body`
        // (lam_util.ml:125-130).
        (LetKind::Strict, Lambda::Lfunction(_), _) => {
            Lambda::let_(LetKind::StrictOpt, param, arg, body)
        }

        // (Strict Pure) `let[Strict] x = e in body` with no_side_effects e ->
        // `let[StrictOpt] x = e in body` (lam_util.ml:131-136).
        (LetKind::Strict, _, _) if analysis::no_side_effects(&arg) => {
            Lambda::let_(LetKind::StrictOpt, param, arg, body)
        }

        // Fall-through: keep the original binding (lam_util.ml:137-138).
        _ => Lambda::let_(kind, param, arg, body),
    }
}

/// Convenience for OCaml's `Lam.let_ Variable v e l` shape used by
/// `Lam_pass_lets_dce` when `eliminate_ref` succeeds.
pub fn let_variable(param: Ident, arg: Lambda, body: Lambda) -> Lambda {
    Lambda::let_(LetKind::Variable, param, arg, body)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ident::{Ident, IdentFlags};
    use crate::lambda::compat::LetKind;
    use crate::lambda::constant::Constant;
    use crate::location::Location;

    fn ident(name: &str, stamp: i32) -> Ident {
        Ident::new(name, stamp, IdentFlags::NONE)
    }

    /// `let x = e in x` -> `e` (Return clause, lam_util.ml:100-104).
    #[test]
    fn return_clause_drops_let() {
        let x = ident("x", 10);
        let e = Lambda::Lconst(Constant::int(7));
        let result = refine_let(LetKind::Strict, x.clone(), e, Lambda::Lvar(x));
        assert!(matches!(result, Lambda::Lconst(_)));
    }

    /// `let x = e in prim p [x]` -> `prim p [e]` (Prim clause,
    /// lam_util.ml:105-111).
    #[test]
    fn prim_clause_inlines_argument() {
        let x = ident("x", 11);
        let e = Lambda::Lconst(Constant::int(3));
        let body = Lambda::prim(
            Primitive::Pidentity,
            vec![Lambda::Lvar(x.clone())],
            Location::none(),
        );
        let result = refine_let(LetKind::Strict, x, e, body);
        match result {
            Lambda::Lprim(p) => {
                assert!(matches!(p.primitive, Primitive::Pidentity));
                assert_eq!(p.args.len(), 1);
                assert!(matches!(p.args[0], Lambda::Lconst(_)));
            }
            _ => panic!("expected Lprim, got {:?}", result),
        }
    }

    /// `let[Strict] x = pure_e in body` -> `let[Alias] x = pure_e in body`
    /// (Alias clause, lam_util.ml:118-124).
    #[test]
    fn alias_clause_relaxes_strict_pure_constant() {
        let x = ident("x", 12);
        let other = ident("other", 13);
        let result = refine_let(
            LetKind::Strict,
            x,
            Lambda::Lconst(Constant::int(5)),
            Lambda::Lvar(other),
        );
        match result {
            Lambda::Llet(LetKind::Alias, _, _, _) => {}
            other => panic!("expected Llet(Alias, _, _, _), got {:?}", other),
        }
    }

    /// `let[Strict] x = makeblock(...) in body` should NOT take the Prim
    /// shortcut even if `body` is `prim p [x]`, because makeblock is a block
    /// constructor (lam_util.ml:69-72).
    #[test]
    fn block_constructor_blocks_prim_clause() {
        let x = ident("x", 14);
        let inner_e = Lambda::Lconst(Constant::int(1));
        let mk = Lambda::prim(
            Primitive::Pmakeblock(0, crate::lambda::TagInfo::Tuple, Mutable::Immutable),
            vec![inner_e],
            Location::none(),
        );
        let body = Lambda::prim(
            Primitive::Pidentity,
            vec![Lambda::Lvar(x.clone())],
            Location::none(),
        );
        let result = refine_let(LetKind::Strict, x, mk, body);
        // Should keep let-binding (Prim clause refused due to is_block_constructor)
        // but Strict-pure rewrite may still fire because makeblock has no side
        // effects, which downgrades to StrictOpt — that is what OCaml does.
        match result {
            Lambda::Llet(LetKind::StrictOpt, _, _, _)
            | Lambda::Llet(LetKind::Strict, _, _, _) => {}
            other => panic!(
                "expected Llet(StrictOpt|Strict, _, _, _), got {:?}",
                other
            ),
        }
    }

    /// (Call) `let x = e in fn(x)` -> `fn(e)` when fn does not capture x
    /// (lam_util.ml:112-117).
    #[test]
    fn call_clause_inlines_when_fn_does_not_capture() {
        let x = ident("x", 15);
        let f = ident("f", 16);
        let e = Lambda::Lconst(Constant::int(9));
        let apply = Lambda::Lapply(Apply {
            ap_func: Box::new(Lambda::Lvar(f)),
            ap_args: vec![Lambda::Lvar(x.clone())],
            ap_info: crate::lambda::ApInfo {
                loc: Location::none(),
                inlined: crate::lambda::InlineAttribute::Default,
                status: crate::lambda::ApplyStatus::Na,
            },
            ap_transformed_jsx: false,
        });
        let result = refine_let(LetKind::Strict, x, e, apply);
        match result {
            Lambda::Lapply(apply) => {
                assert_eq!(apply.ap_args.len(), 1);
                assert!(matches!(apply.ap_args[0], Lambda::Lconst(_)));
            }
            other => panic!("expected Lapply, got {:?}", other),
        }
    }
}
