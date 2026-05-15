//! Direct port of `compiler/core/lam_eta_conversion.ml`.
//!
//! Two helpers used by `Lam_pass_alpha_conversion` to massage applications
//! whose argument count does not match the callee's known arity:
//!
//! - [`transform_under_supply`] — under-application: build an outer
//!   `Lam.function_` that supplies the missing arguments.
//! - [`unsafe_adjust_to_arity`] — eta-(de)expand a function so its observable
//!   arity matches `to_`. Used for `@bs.uncurry` and `Pjs_fn_make`.
//!
//! Every line traces to a specific line in OCaml. No invented logic.

use crate::context::IdGenerator;
use crate::ident::Ident;
use crate::lambda::lam_compat::{FieldDbgInfo, LetKind};
use crate::lambda::lam_constant::Constant;
use crate::lambda::lam_primitive::Primitive;
use crate::lambda::{
    ApInfo, Apply, ApplyStatus, FunctionAttribute, InlineAttribute, Lambda, PrimInfo,
};
use crate::location::Location;

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

/// Direct port of `Lam_eta_conversion.unsafe_adjust_to_arity`
/// (lam_eta_conversion.ml:111-296). Adjusts `fn` so its observable arity
/// matches `to_`. Used by `Pjs_fn_make`/`Pjs_fn_make_unit` and the
/// `Lapply` over-application split in `alpha_conversion`.
pub fn unsafe_adjust_to_arity(
    id_gen: &IdGenerator,
    loc: Location,
    to_: i32,
    from: Option<i32>,
    fn_: Lambda,
) -> Lambda {
    let ap_info = ApInfo {
        loc: loc.clone(),
        inlined: InlineAttribute::Default,
        status: ApplyStatus::Na,
    };

    let is_async_fn = matches!(&fn_, Lambda::Lfunction(f) if f.attr.async_);

    // lam_eta_conversion.ml:121-122 — choose the `from` arity. When `fn` is
    // an Lfunction, fall back to its declared arity.
    let from_value: Option<i32> = match (&from, &fn_) {
        (Some(_), _) => from,
        (None, Lambda::Lfunction(f)) => Some(f.arity),
        _ => None,
    };

    if let Some(from) = from_value {
        // lam_eta_conversion.ml:123 — same arity (or async): identity.
        if from == to_ || is_async_fn {
            return fn_;
        }

        // lam_eta_conversion.ml:124-158 — to_ = 0 special case.
        if to_ == 0 {
            return adjust_to_zero(id_gen, fn_);
        }

        // lam_eta_conversion.ml:159-209 — to_ > from: eta-expand.
        if to_ > from {
            return eta_expand(id_gen, loc, ap_info, fn_, from, to_);
        }

        // lam_eta_conversion.ml:210-268 — to_ < from: eta-reduce by wrapping
        // with an outer Lfunction that re-applies the rest internally.
        return eta_reduce_to(id_gen, loc, ap_info, fn_, from, to_);
    }

    // lam_eta_conversion.ml:269-296 — `from = None` and `fn` is not Lfunction.
    if to_ == 0 {
        return adjust_to_zero(id_gen, fn_);
    }
    transform_under_supply(id_gen, to_, &ap_info, fn_, Vec::new())
}

/// lam_eta_conversion.ml:124-158 — `to_ = 0`. Special-case the unary
/// `param` Lfunction (Pjs_fn_make 0 / `[@bs] () -> ..`).
fn adjust_to_zero(id_gen: &IdGenerator, fn_: Lambda) -> Lambda {
    if let Lambda::Lfunction(f) = &fn_ {
        if f.params.len() == 1 {
            let param = f.params[0].clone();
            let body = (*f.body).clone();
            return Lambda::function_(
                0,
                Vec::new(),
                Lambda::let_(LetKind::Alias, param, Lambda::unit(), body),
                FunctionAttribute::default(),
            );
        }
    }

    let ap_info = ApInfo {
        loc: Location::none(),
        inlined: InlineAttribute::Default,
        status: ApplyStatus::Na,
    };
    let (wrapper, new_fn) = wrapper_or_inline(id_gen, &fn_);
    let cont = Lambda::function_(
        0,
        Vec::new(),
        Lambda::apply(new_fn, vec![Lambda::unit()], ap_info, false),
        FunctionAttribute::default(),
    );
    match wrapper {
        None => cont,
        Some(partial_arg) => Lambda::let_(LetKind::Strict, partial_arg, fn_, cont),
    }
}

/// lam_eta_conversion.ml:159-209 — `to_ > from` (eta-expansion).
fn eta_expand(
    id_gen: &IdGenerator,
    _loc: Location,
    ap_info: ApInfo,
    fn_: Lambda,
    from: i32,
    to_: i32,
) -> Lambda {
    if let Lambda::Lfunction(f) = &fn_ {
        // OCaml extends the original params with fresh Ident.create params
        // (compiler/core/lam_eta_conversion.ml:159-175).
        let extra_args: Vec<Ident> = (0..(to_ - from)).map(|_| id_gen.create("param")).collect();
        let mut params = f.params.clone();
        params.extend(extra_args.iter().cloned());

        let mut body = (*f.body).clone();
        for var in extra_args.iter() {
            body = Lambda::apply(body, vec![Lambda::var(var.clone())], ap_info.clone(), false);
        }

        return Lambda::function_(to_, params, body, FunctionAttribute::default());
    }

    let arity = to_;
    // Non-function eta expansion uses the same Ident.create source
    // (compiler/core/lam_eta_conversion.ml:177-209).
    let extra_args: Vec<Ident> = (0..to_).map(|_| id_gen.create("param")).collect();
    let (wrapper, new_fn) = wrapper_or_inline(id_gen, &fn_);

    let first_args: Vec<Lambda> = extra_args
        .iter()
        .take(from as usize)
        .cloned()
        .map(Lambda::var)
        .collect();
    let rest_args: Vec<Lambda> = extra_args
        .iter()
        .skip(from as usize)
        .cloned()
        .map(Lambda::var)
        .collect();

    let infer_full = ApInfo {
        status: ApplyStatus::InferFull,
        ..ap_info.clone()
    };

    let inner = Lambda::apply(new_fn, first_args, infer_full, false);
    let body = Lambda::apply(inner, rest_args, ap_info, false);

    let cont = Lambda::function_(arity, extra_args, body, FunctionAttribute::default());

    match wrapper {
        None => cont,
        Some(partial_arg) => Lambda::let_(LetKind::Strict, partial_arg, fn_, cont),
    }
}

/// lam_eta_conversion.ml:210-268 — `to_ < from` (eta-reduce).
fn eta_reduce_to(
    id_gen: &IdGenerator,
    _loc: Location,
    ap_info: ApInfo,
    fn_: Lambda,
    from: i32,
    to_: i32,
) -> Lambda {
    if let Lambda::Lfunction(f) = &fn_ {
        let arity = to_;
        let outer_count = arity as usize;
        let outer_params: Vec<Ident> = f.params.iter().take(outer_count).cloned().collect();
        let inner_params: Vec<Ident> = f.params.iter().skip(outer_count).cloned().collect();
        let inner_arity = from - to_;

        let inner = Lambda::function_(
            inner_arity,
            inner_params,
            (*f.body).clone(),
            FunctionAttribute::default(),
        );

        return Lambda::function_(arity, outer_params, inner, FunctionAttribute::default());
    }

    // Non-function eta reduction allocates wrapper params with Ident.create
    // (compiler/core/lam_eta_conversion.ml:231-268).
    let extra_outer_args: Vec<Ident> = (0..to_).map(|_| id_gen.create("param")).collect();
    let (wrapper, new_fn) = wrapper_or_inline(id_gen, &fn_);

    let arity = from - to_;
    let extra_inner_args: Vec<Ident> = (0..arity).map(|_| id_gen.create("param")).collect();

    let mut combined_args: Vec<Lambda> = Vec::with_capacity((to_ + arity) as usize);
    combined_args.extend(extra_outer_args.iter().cloned().map(Lambda::var));
    combined_args.extend(extra_inner_args.iter().cloned().map(Lambda::var));

    let infer_full = ApInfo {
        status: ApplyStatus::InferFull,
        ..ap_info.clone()
    };

    let body = Lambda::apply(new_fn, combined_args, infer_full, false);
    let inner = Lambda::function_(arity, extra_inner_args, body, FunctionAttribute::default());
    let cont = Lambda::function_(to_, extra_outer_args, inner, FunctionAttribute::default());

    match wrapper {
        None => cont,
        Some(partial_arg) => Lambda::let_(LetKind::Strict, partial_arg, fn_, cont),
    }
}

/// lam_eta_conversion.ml:135-148, repeated. Decide whether `fn` can be used
/// directly inside a wrapper (Lvar / module Pfield read) or whether it must
/// be hoisted into an outer `let partial_arg = fn`.
fn wrapper_or_inline(id_gen: &IdGenerator, fn_: &Lambda) -> (Option<Ident>, Lambda) {
    if is_var_or_module_field(fn_) {
        (None, fn_.clone())
    } else {
        // OCaml's wrapper path uses Ext_ident.create, which shares the same
        // global stamp source (compiler/core/lam_eta_conversion.ml:135-148,
        // 181-193, 235-247, 271-295).
        let partial_arg = id_gen.create("partial_arg");
        (Some(partial_arg.clone()), Lambda::var(partial_arg))
    }
}

/// Helper for the safety check used by both `transform_under_supply`
/// (lam_eta_conversion.ml:42-50) and `wrapper_or_inline`. Recognises
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

/// Helper used by `wrapper_or_inline`. Stricter than [`is_safe_to_share`]:
/// only `Lvar` and `Pfield(_, Fld_module _) [Lglobal_module | Lvar]` qualify.
fn is_var_or_module_field(lam: &Lambda) -> bool {
    match lam {
        Lambda::Lvar(_) => true,
        Lambda::Lprim(PrimInfo {
            primitive: Primitive::Pfield(_, FieldDbgInfo::Module { .. }),
            args,
            ..
        }) if matches!(
            args.as_slice(),
            [Lambda::LglobalModule(_, _) | Lambda::Lvar(_)]
        ) =>
        {
            true
        }
        _ => false,
    }
}

// `Apply` is unused here but kept available for callers that destructure
// returned applications.
#[allow(dead_code)]
fn _unused_apply() {
    let _ = std::mem::size_of::<Apply>();
}
