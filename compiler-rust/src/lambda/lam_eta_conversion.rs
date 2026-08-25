//! Direct port of `compiler/core/lam_eta_conversion.ml`.
//!
//! Helper used by `Lam_pass_alpha_conversion` to transform
//! under-applications by supplying missing arguments.
//!
//! Every line traces to a specific line in OCaml. No invented logic.

use crate::context::IdGenerator;
use crate::ident::Ident;
use crate::lambda::lam_compat::{FieldDbgInfo, LetKind};
use crate::lambda::lam_constant::Constant;
use crate::lambda::lam_primitive::Primitive;
use crate::lambda::{ApInfo, FunctionAttribute, Lambda, PrimInfo};

/// Direct port of `Lam_eta_conversion.transform_under_supply`
/// (lam_eta_conversion.ml:37-75).
///
/// Builds an outer `function(extra_params) { ... fn(args ++ extra_params) }`
/// closure for the `n` missing arguments, factoring out any non-pure args
/// into outer `let` bindings so they are evaluated exactly once.
pub fn transform_under_supply(
    id_gen: &IdGenerator,
    n: i32,
    ap_info: &ApInfo,
    fn_: Lambda,
    args: Vec<Lambda>,
) -> Lambda {
    // OCaml uses the shared Ident.create counter here
    // (compiler/core/lam_eta_conversion.ml:37-39).
    let extra_args: Vec<Ident> = (0..n).map(|_| id_gen.create("param")).collect();
    let extra_lambdas: Vec<Lambda> = extra_args.iter().cloned().map(Lambda::var).collect();

    // lam_eta_conversion.ml:40-53 — fold over (fn :: args), accumulating a
    // prefix of "safe" lambdas (`acc`) and a binding list (`bind`) for
    // expressions that need to be let-bound to preserve evaluation order.
    let mut acc: Vec<Lambda> = Vec::with_capacity(args.len() + 1);
    let mut bindings: Vec<(Ident, Lambda)> = Vec::new();
    let mut input: Vec<Lambda> = Vec::with_capacity(args.len() + 1);
    input.push(fn_);
    input.extend(args);

    // OCaml folds right; we want the original order in `acc`, so iterate
    // forward and push.
    for lam in input.into_iter() {
        if is_safe_to_share(&lam) {
            acc.push(lam);
        } else {
            // OCaml allocates this with the same global counter as source
            // identifiers (compiler/core/lam_eta_conversion.ml:41-53).
            let v = id_gen.create("partial_arg");
            let var = Lambda::var(v.clone());
            bindings.push((v, lam));
            acc.push(var);
        }
    }

    // `acc` is `fn :: args`. Pop the head out as `fn`.
    let mut iter = acc.into_iter();
    let fn_ = iter
        .next()
        .expect("transform_under_supply requires at least fn");
    let args: Vec<Lambda> = iter.collect();

    // lam_eta_conversion.ml:54-66 — `fn :: args, []` pure path: build the
    // outer function directly.
    if bindings.is_empty() {
        let mut all_args = args;
        all_args.extend(extra_lambdas);
        return Lambda::function_(
            n,
            extra_args,
            Lambda::apply(fn_, all_args, ap_info.clone(), false),
            FunctionAttribute::default(),
        );
    }

    // lam_eta_conversion.ml:67-74 — `fn :: args, bindings`: build the outer
    // function then wrap with `let Strict id = x` for each captured binding.
    let mut all_args = args;
    all_args.extend(extra_lambdas);
    let body = Lambda::apply(fn_, all_args, ap_info.clone(), false);
    let rest = Lambda::function_(n, extra_args, body, FunctionAttribute::default());

    // OCaml's fold_left applies bindings in order, wrapping innermost first.
    // We collected `bindings` in the same forward order; reversing matches
    // OCaml's `Ext_list.fold_left bindings rest (fun lam (id, x) -> ...)`.
    let mut result = rest;
    for (id, x) in bindings.into_iter().rev() {
        result = Lambda::let_(LetKind::Strict, id, x, result);
    }
    result
}

/// Helper for `transform_under_supply` (lam_eta_conversion.ml:42-50). Recognises
/// `Lvar`, side-effect-free constants, module field reads and `Lfunction`.
fn is_safe_to_share(lam: &Lambda) -> bool {
    match lam {
        Lambda::Lvar(_) | Lambda::Lfunction(_) => true,
        Lambda::Lconst(c) => matches!(
            c,
            Constant::Int { .. }
                | Constant::Char(_)
                | Constant::String { .. }
                | Constant::ImmString(_)
                | Constant::Float(_)
                | Constant::BigInt { .. }
                | Constant::Pointer(_)
                | Constant::JsTrue
                | Constant::JsFalse
                | Constant::JsUndefined { .. }
        ),
        Lambda::Lprim(PrimInfo {
            primitive: Primitive::Pfield(_, FieldDbgInfo::Module { .. }),
            ..
        }) => true,
        _ => false,
    }
}
