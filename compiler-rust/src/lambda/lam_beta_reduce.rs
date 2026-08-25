//! Lambda beta reduction.
//!
//! This module provides beta reduction (function inlining) for Lambda expressions.
//!
//! Beta reduction transforms `(fun x y -> body) arg1 arg2` into
//! `let x = arg1 in let y = arg2 in body`, but with optimizations:
//!
//! - Simple cases: direct substitution when arguments are values
//! - Complex cases: create let bindings with proper evaluation order
//! - Side effect handling: preserve evaluation semantics
//!
//! # Evaluation Order
//!
//! OCaml/ReScript has unspecified evaluation order for function arguments.
//! We ensure that side effects happen in a consistent order by binding
//! arguments to variables when needed.

use ahash::AHashMap as HashMap;

use crate::context::IdGenerator;
use crate::ident::Ident;
use crate::lambda::lam_analysis::no_side_effects;
use crate::lambda::lam_closure::StatsMap;
use crate::lambda::lam_compat::LetKind;
use crate::lambda::lam_compile_context::{IdKind, IdentTable};
use crate::lambda::lam_pass_collect::kind_of_lambda_block;
use crate::lambda::lam_primitive::{Mutable, Primitive};
use crate::lambda::lam_subst::Subst;
use crate::lambda::lam_util::refine_let;
use crate::lambda::{Apply, Lambda, PrimInfo};
use crate::location::Location;

/// Tracking state for simple beta reduction.
struct ArgUsage {
    /// The argument expression
    lambda: Lambda,
    /// Whether this argument has been used
    used: bool,
}

/// Attempt simple beta reduction.
///
/// This handles the common case where the function body is a primitive
/// or simple application, and all arguments can be directly substituted.
///
/// # Conditions for simple reduction:
/// - Function body is a primitive or application
/// - Each parameter is used at most once
/// - Arguments in the body are variables or constants
///
/// Returns `Some(reduced)` if reduction is possible, `None` otherwise.
pub fn simple_beta_reduce(params: &[Ident], body: &Lambda, args: &[Lambda]) -> Option<Lambda> {
    // Build parameter -> argument mapping
    let mut param_map: HashMap<Ident, ArgUsage> = HashMap::new();
    for (param, arg) in params.iter().zip(args.iter()) {
        param_map.insert(
            param.clone(),
            ArgUsage {
                lambda: arg.clone(),
                used: false,
            },
        );
    }

    // Try to substitute arguments in the body
    fn substitute_args(
        lams: &[Lambda],
        param_map: &mut HashMap<Ident, ArgUsage>,
    ) -> Option<Vec<Lambda>> {
        let mut result = Vec::new();
        for lam in lams {
            match lam {
                Lambda::Lvar(x) => {
                    if let Some(usage) = param_map.get_mut(x) {
                        if usage.used {
                            return None;
                        }
                        usage.used = true;
                        result.push(usage.lambda.clone());
                    } else {
                        result.push(lam.clone());
                    }
                }
                Lambda::Lconst(_) => {
                    result.push(lam.clone());
                }
                _ => {
                    // Complex argument - can't do simple reduction
                    return None;
                }
            }
        }
        Some(result)
    }

    match body {
        // Primitive application: (fun x y -> prim(x, y)) a b => prim(a, b)
        Lambda::Lprim(prim_info) => {
            let new_args = substitute_args(&prim_info.args, &mut param_map)?;

            // Build the new primitive
            let mut result = Lambda::Lprim(PrimInfo {
                primitive: prim_info.primitive.clone(),
                args: new_args,
                loc: prim_info.loc.clone(),
            });

            // Add sequences for unused arguments (preserve side effects)
            for (_param, usage) in param_map.iter() {
                if !usage.used {
                    result = Lambda::seq(usage.lambda.clone(), result);
                }
            }

            Some(result)
        }

        // Function application: (fun x y -> f(x, y)) a b => f(a, b)
        Lambda::Lapply(apply) => {
            // Check if the function is simple (variable or module access)
            let is_simple_func = match &*apply.ap_func {
                Lambda::Lvar(_) => true,
                Lambda::Lprim(PrimInfo {
                    primitive: Primitive::Pfield(_, _),
                    args,
                    ..
                }) => {
                    matches!(args.as_slice(), [Lambda::LglobalModule(_, _)])
                }
                _ => false,
            };

            if !is_simple_func {
                return None;
            }

            let new_args = substitute_args(&apply.ap_args, &mut param_map)?;

            // Handle function substitution if it's a variable
            let new_func = match &*apply.ap_func {
                Lambda::Lvar(fn_name) => {
                    if let Some(usage) = param_map.get_mut(fn_name) {
                        if usage.used {
                            return None;
                        }
                        usage.used = true;
                        usage.lambda.clone()
                    } else {
                        (*apply.ap_func).clone()
                    }
                }
                _ => (*apply.ap_func).clone(),
            };

            // Build the new application
            let mut result = Lambda::Lapply(Apply {
                ap_func: Box::new(new_func),
                ap_args: new_args,
                ap_info: apply.ap_info.clone(),
                ap_transformed_jsx: apply.ap_transformed_jsx,
            });

            // Add sequences for unused arguments
            for (_param, usage) in param_map.iter() {
                if !usage.used {
                    result = Lambda::seq(usage.lambda.clone(), result);
                }
            }

            Some(result)
        }

        _ => None,
    }
}

/// Perform beta reduction without variable usage statistics.
///
/// This is the simplest form of beta reduction that creates let bindings
/// for all arguments.
pub fn no_names_beta_reduce(params: &[Ident], body: &Lambda, args: &[Lambda]) -> Lambda {
    // Try simple beta reduce first
    if let Some(result) = simple_beta_reduce(params, body, args) {
        return result;
    }

    // Fall back to creating let bindings
    let mut result = body.clone();
    for (param, arg) in params.iter().zip(args.iter()) {
        result = refine_let(LetKind::Strict, param.clone(), arg.clone(), result);
    }
    result
}

/// Perform beta reduction that matches OCaml's `Lam_beta_reduce.propagate_beta_reduce`.
///
/// This substitutes only constants/variables directly and introduces fresh let-bindings
/// for other arguments so returned wrapper structure is preserved instead of being
/// collapsed by `subst`.
///
/// Back-compat variant without meta threading — primarily used by unit tests.
/// Mirrors the OCaml signature change introduced by `Lam_beta_reduce` which takes
/// `meta : Lam_stats.t`; the production call path uses
/// [`propagate_beta_reduce_with_meta`] instead.
pub fn propagate_beta_reduce(params: &[Ident], body: &Lambda, args: &[Lambda]) -> Lambda {
    let mut scratch = HashMap::new();
    propagate_beta_reduce_with_meta(&mut scratch, params, body, args)
}

/// Port of `Lam_beta_reduce.propagate_beta_reduce` (lam_beta_reduce.ml:47-74).
///
/// When a parameter argument is bound to a fresh variable rather than inlined,
/// OCaml also registers the new variable in `meta.ident_tbl` via
/// `kind_of_lambda_block` / `Normal_optional` so subsequent
/// `Lam_pass_remove_alias` field lookups (`field_flatten_get`) can continue to
/// see through the wrapper. Without this, `let X = {foo: funarg.foo}` stays
/// alive as a dead binding after `simplify_alias` rewrites `X.foo` to
/// `funarg.foo`.
pub fn propagate_beta_reduce_with_meta(
    ident_tbl: &mut IdentTable,
    params: &[Ident],
    body: &Lambda,
    args: &[Lambda],
) -> Lambda {
    let id_gen = IdGenerator::with_start_stamp(max_ident_stamp(params, body, args));
    propagate_beta_reduce_with_meta_and_id_gen(ident_tbl, &id_gen, params, body, args)
}

/// Variant of [`propagate_beta_reduce_with_meta`] that uses a caller-supplied
/// `IdGenerator`. OCaml's `Ident.rename` consults a single global mutable
/// stamp counter, so every renamed ident gets a fresh stamp unused anywhere
/// else in the program. Using a fresh `IdGenerator::with_start_stamp(..)` per
/// beta-reduce call made two inlinings of the same function (e.g. a shared
/// `let l = x => console.log(x)`) rename their parameters to the same new
/// stamp, which the JS printer then emitted as two `let prim = …` declarations
/// at module top level — invalid JS. Threading the pipeline-wide generator
/// from [`crate::lambda::lam_compile_context::LamStats::id_gen`] preserves the
/// OCaml invariant.
pub fn propagate_beta_reduce_with_meta_and_id_gen(
    ident_tbl: &mut IdentTable,
    id_gen: &IdGenerator,
    params: &[Ident],
    body: &Lambda,
    args: &[Lambda],
) -> Lambda {
    if let Some(result) = simple_beta_reduce(params, body, args) {
        return result;
    }

    let mut rest_bindings: Vec<(Ident, Lambda)> = Vec::new();
    let mut substitution: Subst = HashMap::new();

    for (param, arg) in params.iter().zip(args.iter()) {
        match arg {
            Lambda::Lconst(_) | Lambda::Lvar(_) => {
                substitution.insert(param.clone(), arg.clone());
            }
            _ => {
                let new_param = param.rename(id_gen);
                rest_bindings.push((new_param.clone(), bound_param_binding(arg)));
                substitution.insert(param.clone(), bound_param_substitution(new_param, arg));
            }
        }
    }

    let new_body = rewrite_bounded_vars(&mut substitution, body, id_gen);
    // OCaml builds `rest_bindings` in reverse parameter order and folds it
    // left, making the first source argument's strict binding outermost. Rust
    // appends in parameter order, so walk that vector in reverse to preserve
    // the same left-to-right argument evaluation order.
    let mut result = new_body;
    for (param, arg) in rest_bindings.into_iter().rev() {
        register_bound_param_kind(ident_tbl, &param, &arg);
        result = refine_let(LetKind::Strict, param, arg, result);
    }
    result
}

/// Perform beta reduction with smart inlining decisions.
///
/// This uses closure analysis to determine which arguments can be
/// directly substituted vs. bound to let variables.
///
/// Arguments that are:
/// - Constants or variables: always substituted
/// - Pure and used 0-1 times: substituted
/// - Otherwise: bound to let variables
///
/// Back-compat variant without meta threading — unit tests only.
pub fn propagate_beta_reduce_with_map(
    stats: &StatsMap,
    params: &[Ident],
    body: &Lambda,
    args: &[Lambda],
) -> Lambda {
    let mut scratch = HashMap::new();
    propagate_beta_reduce_with_map_and_meta(&mut scratch, stats, params, body, args)
}

/// Port of `Lam_beta_reduce.propagate_beta_reduce_with_map`
/// (lam_beta_reduce.ml:76-115). Same ident_tbl tracking as
/// [`propagate_beta_reduce_with_meta`] — when a non-inlined argument is bound
/// to a fresh variable, we register its shape in `ident_tbl` so later
/// `simplify_alias` passes can continue to see through it.
pub fn propagate_beta_reduce_with_map_and_meta(
    ident_tbl: &mut IdentTable,
    stats: &StatsMap,
    params: &[Ident],
    body: &Lambda,
    args: &[Lambda],
) -> Lambda {
    let id_gen = IdGenerator::with_start_stamp(max_ident_stamp(params, body, args));
    propagate_beta_reduce_with_map_and_meta_and_id_gen(
        ident_tbl, &id_gen, stats, params, body, args,
    )
}

/// Variant of [`propagate_beta_reduce_with_map_and_meta`] that uses a
/// caller-supplied `IdGenerator`, matching OCaml's global-counter semantics for
/// `Ident.rename` across repeated inlinings. See
/// [`propagate_beta_reduce_with_meta_and_id_gen`] for the rationale.
pub fn propagate_beta_reduce_with_map_and_meta_and_id_gen(
    ident_tbl: &mut IdentTable,
    id_gen: &IdGenerator,
    stats: &StatsMap,
    params: &[Ident],
    body: &Lambda,
    args: &[Lambda],
) -> Lambda {
    // Try simple beta reduce first
    if let Some(result) = simple_beta_reduce(params, body, args) {
        return result;
    }

    // Categorize arguments
    let mut rest_bindings: Vec<(Ident, Lambda)> = Vec::new();
    let mut substitution: Subst = HashMap::new();

    for (param, arg) in params.iter().zip(args.iter()) {
        match arg {
            // Constants and variables can always be substituted
            Lambda::Lconst(_) | Lambda::Lvar(_) => {
                substitution.insert(param.clone(), arg.clone());
            }
            // Global modules need to be bound (for proper module loading)
            Lambda::LglobalModule(_, _) => {
                let new_param = param.rename(id_gen);
                rest_bindings.push((new_param.clone(), arg.clone()));
                substitution.insert(param.clone(), Lambda::var(new_param));
            }
            _ => {
                // Check if we can substitute based on usage stats
                if no_side_effects(arg) {
                    if let Some(stat) = stats.get(param) {
                        if stat.top_and_used_zero_or_one() {
                            substitution.insert(param.clone(), arg.clone());
                            continue;
                        }
                    }
                }
                // Bind to a new variable
                let new_param = param.rename(id_gen);
                rest_bindings.push((new_param.clone(), bound_param_binding(arg)));
                substitution.insert(param.clone(), bound_param_substitution(new_param, arg));
            }
        }
    }

    // Apply substitution to body
    let new_body = rewrite_bounded_vars(&mut substitution, body, id_gen);

    // See `propagate_beta_reduce_with_meta_and_id_gen`: Rust stores bindings
    // in parameter order, so reverse iteration makes the first source
    // argument's binding outermost, matching OCaml's reverse-list fold-left.
    let mut result = new_body;
    for (param, arg) in rest_bindings.into_iter().rev() {
        register_bound_param_kind(ident_tbl, &param, &arg);
        result = refine_let(LetKind::Strict, param, arg, result);
    }
    result
}

/// Direct port of the `meta.ident_tbl` update in
/// `Lam_beta_reduce.propagate_beta_reduce` (lam_beta_reduce.ml:66-73) and
/// `propagate_beta_reduce_with_map` (lam_beta_reduce.ml:107-114). OCaml only
/// registers `ImmutableBlock` / `Normal_optional` here — everything else is
/// a no-op so downstream `Lam_pass_remove_alias` keeps treating the binding
/// as an opaque `Lvar`.
fn register_bound_param_kind(ident_tbl: &mut IdentTable, param: &Ident, arg: &Lambda) {
    match arg {
        Lambda::Lprim(PrimInfo {
            primitive: Primitive::Pmakeblock(_, _, Mutable::Immutable),
            args,
            ..
        }) => {
            ident_tbl.insert(param.clone(), kind_of_lambda_block(args));
        }
        Lambda::Lprim(PrimInfo {
            primitive: Primitive::Psome | Primitive::PsomeNotNest,
            args,
            ..
        }) if args.len() == 1 => {
            ident_tbl.insert(param.clone(), IdKind::NormalOptional(args[0].clone()));
        }
        _ => {}
    }
}

fn bound_param_substitution(new_param: Ident, arg: &Lambda) -> Lambda {
    if is_boxed_optional_binding(arg) {
        Lambda::prim(
            Primitive::Pidentity,
            vec![Lambda::var(new_param)],
            Location::none(),
        )
    } else {
        Lambda::var(new_param)
    }
}

fn bound_param_binding(arg: &Lambda) -> Lambda {
    if is_boxed_optional_binding(arg) {
        Lambda::prim(Primitive::Pidentity, vec![arg.clone()], Location::none())
    } else {
        arg.clone()
    }
}

fn is_boxed_optional_binding(arg: &Lambda) -> bool {
    matches!(
        arg,
        Lambda::Lprim(PrimInfo {
            primitive: Primitive::PnullToOpt | Primitive::PnullUndefinedToOpt,
            ..
        })
    )
}

fn max_ident_stamp(params: &[Ident], body: &Lambda, args: &[Lambda]) -> i32 {
    let params_max = params
        .iter()
        .fold(0, |max_stamp, param| max_stamp.max(param.stamp()));
    let body_max = max_ident_stamp_in_lambda(body);
    let args_max = args.iter().fold(0, |max_stamp, arg| {
        max_stamp.max(max_ident_stamp_in_lambda(arg))
    });
    params_max.max(body_max).max(args_max)
}

fn rewrite_bounded_vars(substitution: &mut Subst, lam: &Lambda, id_gen: &IdGenerator) -> Lambda {
    fn rebind(id: &Ident, substitution: &mut Subst, id_gen: &IdGenerator) -> Ident {
        let renamed = id.rename(id_gen);
        substitution.insert(id.clone(), Lambda::var(renamed.clone()));
        renamed
    }

    match lam {
        Lambda::Lvar(id) => substitution.get(id).cloned().unwrap_or_else(|| lam.clone()),
        Lambda::Lconst(_) => lam.clone(),
        Lambda::Lapply(apply) => Lambda::Lapply(Apply {
            ap_func: Box::new(rewrite_bounded_vars(substitution, &apply.ap_func, id_gen)),
            ap_args: apply
                .ap_args
                .iter()
                .map(|arg| rewrite_bounded_vars(substitution, arg, id_gen))
                .collect(),
            ap_info: apply.ap_info.clone(),
            ap_transformed_jsx: apply.ap_transformed_jsx,
        }),
        Lambda::Lfunction(func) => {
            let params = func
                .params
                .iter()
                .map(|param| rebind(param, substitution, id_gen))
                .collect();
            Lambda::function_(
                func.arity,
                params,
                rewrite_bounded_vars(substitution, &func.body, id_gen),
                func.attr.clone(),
            )
        }
        Lambda::Llet(kind, id, arg, body) => {
            let id = rebind(id, substitution, id_gen);
            Lambda::let_(
                *kind,
                id,
                rewrite_bounded_vars(substitution, arg, id_gen),
                rewrite_bounded_vars(substitution, body, id_gen),
            )
        }
        Lambda::Lletrec(bindings, body) => {
            let renamed_ids: Vec<_> = bindings
                .iter()
                .map(|(id, _)| rebind(id, substitution, id_gen))
                .collect();
            let bindings = renamed_ids
                .into_iter()
                .zip(bindings.iter())
                .map(|(id, (_, expr))| (id, rewrite_bounded_vars(substitution, expr, id_gen)))
                .collect();
            Lambda::letrec(bindings, rewrite_bounded_vars(substitution, body, id_gen))
        }
        Lambda::Lprim(prim_info) => Lambda::Lprim(PrimInfo {
            primitive: prim_info.primitive.clone(),
            args: prim_info
                .args
                .iter()
                .map(|arg| rewrite_bounded_vars(substitution, arg, id_gen))
                .collect(),
            loc: prim_info.loc.clone(),
        }),
        Lambda::LglobalModule(_, _) => lam.clone(),
        Lambda::Lswitch(arg, switch) => Lambda::switch(
            rewrite_bounded_vars(substitution, arg, id_gen),
            crate::lambda::LambdaSwitch {
                sw_consts_full: switch.sw_consts_full,
                sw_consts: switch
                    .sw_consts
                    .iter()
                    .map(|(key, value)| (*key, rewrite_bounded_vars(substitution, value, id_gen)))
                    .collect(),
                sw_blocks_full: switch.sw_blocks_full,
                sw_blocks: switch
                    .sw_blocks
                    .iter()
                    .map(|(key, value)| (*key, rewrite_bounded_vars(substitution, value, id_gen)))
                    .collect(),
                sw_failaction: switch
                    .sw_failaction
                    .as_ref()
                    .map(|value| Box::new(rewrite_bounded_vars(substitution, value, id_gen))),
                sw_names: switch.sw_names.clone(),
            },
        ),
        Lambda::LstringSwitch(arg, cases, default) => Lambda::string_switch(
            rewrite_bounded_vars(substitution, arg, id_gen),
            cases
                .iter()
                .map(|(key, value)| {
                    (
                        key.clone(),
                        rewrite_bounded_vars(substitution, value, id_gen),
                    )
                })
                .collect(),
            default
                .as_ref()
                .map(|value| Box::new(rewrite_bounded_vars(substitution, value, id_gen))),
        ),
        Lambda::LstaticRaise(id, args) => Lambda::LstaticRaise(
            *id,
            args.iter()
                .map(|arg| rewrite_bounded_vars(substitution, arg, id_gen))
                .collect(),
        ),
        Lambda::LstaticCatch(body, (exit, vars), handler) => {
            let body = rewrite_bounded_vars(substitution, body, id_gen);
            let vars = vars
                .iter()
                .map(|var| rebind(var, substitution, id_gen))
                .collect();
            Lambda::LstaticCatch(
                Box::new(body),
                (*exit, vars),
                Box::new(rewrite_bounded_vars(substitution, handler, id_gen)),
            )
        }
        Lambda::LtryWith(body, exn, handler) => {
            let body = rewrite_bounded_vars(substitution, body, id_gen);
            let exn = rebind(exn, substitution, id_gen);
            Lambda::LtryWith(
                Box::new(body),
                exn,
                Box::new(rewrite_bounded_vars(substitution, handler, id_gen)),
            )
        }
        Lambda::LifThenElse(cond, then_, else_) => Lambda::LifThenElse(
            Box::new(rewrite_bounded_vars(substitution, cond, id_gen)),
            Box::new(rewrite_bounded_vars(substitution, then_, id_gen)),
            Box::new(rewrite_bounded_vars(substitution, else_, id_gen)),
        ),
        Lambda::Lsequence(first, second) => Lambda::Lsequence(
            Box::new(rewrite_bounded_vars(substitution, first, id_gen)),
            Box::new(rewrite_bounded_vars(substitution, second, id_gen)),
        ),
        Lambda::Lwhile(cond, body) => Lambda::Lwhile(
            Box::new(rewrite_bounded_vars(substitution, cond, id_gen)),
            Box::new(rewrite_bounded_vars(substitution, body, id_gen)),
        ),
        Lambda::Lfor(id, from, to, direction, body) => {
            let id = rebind(id, substitution, id_gen);
            Lambda::Lfor(
                id,
                Box::new(rewrite_bounded_vars(substitution, from, id_gen)),
                Box::new(rewrite_bounded_vars(substitution, to, id_gen)),
                *direction,
                Box::new(rewrite_bounded_vars(substitution, body, id_gen)),
            )
        }
        Lambda::Lfor_of(id, iterable, body) => {
            let id = rebind(id, substitution, id_gen);
            Lambda::for_of(
                id,
                rewrite_bounded_vars(substitution, iterable, id_gen),
                rewrite_bounded_vars(substitution, body, id_gen),
            )
        }
        Lambda::Lfor_await_of(id, iterable, body) => {
            let id = rebind(id, substitution, id_gen);
            Lambda::for_await_of(
                id,
                rewrite_bounded_vars(substitution, iterable, id_gen),
                rewrite_bounded_vars(substitution, body, id_gen),
            )
        }
        Lambda::Lbreak => Lambda::break_(),
        Lambda::Lcontinue => Lambda::continue_(),
        Lambda::Lassign(id, value) => Lambda::Lassign(
            id.clone(),
            Box::new(rewrite_bounded_vars(substitution, value, id_gen)),
        ),
    }
}

pub(crate) fn max_ident_stamp_in_lambda(lam: &Lambda) -> i32 {
    match lam {
        Lambda::Lvar(id) | Lambda::LglobalModule(id, _) => id.stamp(),
        Lambda::Lconst(_) => 0,
        Lambda::Lapply(apply) => apply.ap_args.iter().fold(
            max_ident_stamp_in_lambda(&apply.ap_func),
            |max_stamp, arg| max_stamp.max(max_ident_stamp_in_lambda(arg)),
        ),
        Lambda::Lfunction(func) => func
            .params
            .iter()
            .fold(max_ident_stamp_in_lambda(&func.body), |max_stamp, param| {
                max_stamp.max(param.stamp())
            }),
        Lambda::Llet(_, id, value, body) => id
            .stamp()
            .max(max_ident_stamp_in_lambda(value))
            .max(max_ident_stamp_in_lambda(body)),
        Lambda::Lletrec(bindings, body) => {
            bindings
                .iter()
                .fold(max_ident_stamp_in_lambda(body), |max_stamp, (id, lam)| {
                    max_stamp
                        .max(id.stamp())
                        .max(max_ident_stamp_in_lambda(lam))
                })
        }
        Lambda::Lprim(info) => info.args.iter().fold(0, |max_stamp, arg| {
            max_stamp.max(max_ident_stamp_in_lambda(arg))
        }),
        Lambda::Lswitch(scrutinee, switch) => {
            let mut max_stamp = max_ident_stamp_in_lambda(scrutinee);
            for (_, lam) in &switch.sw_consts {
                max_stamp = max_stamp.max(max_ident_stamp_in_lambda(lam));
            }
            for (_, lam) in &switch.sw_blocks {
                max_stamp = max_stamp.max(max_ident_stamp_in_lambda(lam));
            }
            if let Some(failaction) = &switch.sw_failaction {
                max_stamp = max_stamp.max(max_ident_stamp_in_lambda(failaction));
            }
            max_stamp
        }
        Lambda::LstringSwitch(scrutinee, cases, default) => {
            let mut max_stamp = max_ident_stamp_in_lambda(scrutinee);
            for (_, lam) in cases {
                max_stamp = max_stamp.max(max_ident_stamp_in_lambda(lam));
            }
            if let Some(default) = default {
                max_stamp = max_stamp.max(max_ident_stamp_in_lambda(default));
            }
            max_stamp
        }
        Lambda::LstaticRaise(_, args) => args.iter().fold(0, |max_stamp, arg| {
            max_stamp.max(max_ident_stamp_in_lambda(arg))
        }),
        Lambda::LstaticCatch(body, (_, ids), handler) => ids.iter().fold(
            max_ident_stamp_in_lambda(body).max(max_ident_stamp_in_lambda(handler)),
            |max_stamp, id| max_stamp.max(id.stamp()),
        ),
        Lambda::LtryWith(body, id, handler) => id
            .stamp()
            .max(max_ident_stamp_in_lambda(body))
            .max(max_ident_stamp_in_lambda(handler)),
        Lambda::LifThenElse(cond, then_, else_) => max_ident_stamp_in_lambda(cond)
            .max(max_ident_stamp_in_lambda(then_))
            .max(max_ident_stamp_in_lambda(else_)),
        Lambda::Lsequence(first, second) | Lambda::Lwhile(first, second) => {
            max_ident_stamp_in_lambda(first).max(max_ident_stamp_in_lambda(second))
        }
        Lambda::Lfor(id, start, end, _, body) => id
            .stamp()
            .max(max_ident_stamp_in_lambda(start))
            .max(max_ident_stamp_in_lambda(end))
            .max(max_ident_stamp_in_lambda(body)),
        Lambda::Lfor_of(id, iterable, body) | Lambda::Lfor_await_of(id, iterable, body) => id
            .stamp()
            .max(max_ident_stamp_in_lambda(iterable))
            .max(max_ident_stamp_in_lambda(body)),
        Lambda::Lbreak | Lambda::Lcontinue => 0,
        Lambda::Lassign(id, value) => id.stamp().max(max_ident_stamp_in_lambda(value)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lambda::lam_closure::VarStats;
    use crate::lambda::{Constant, FunctionAttribute, LambdaSwitch, Primitive};
    use crate::location::Location;

    #[test]
    fn test_simple_beta_reduce_prim() {
        let x = Ident::create_local("x");
        let y = Ident::create_local("y");

        // (fun x y -> x + y) 1 2 => 1 + 2
        let params = vec![x.clone(), y.clone()];
        let body = Lambda::prim(
            Primitive::Paddint,
            vec![Lambda::var(x.clone()), Lambda::var(y.clone())],
            Location::none(),
        );
        let args = vec![
            Lambda::const_(Constant::int(1)),
            Lambda::const_(Constant::int(2)),
        ];

        let result = simple_beta_reduce(&params, &body, &args);
        assert!(result.is_some());

        let reduced = result.unwrap();
        match reduced {
            Lambda::Lprim(ref info) => {
                assert_eq!(info.args.len(), 2);
                assert!(matches!(
                    info.args[0],
                    Lambda::Lconst(Constant::Int { i: 1, .. })
                ));
                assert!(matches!(
                    info.args[1],
                    Lambda::Lconst(Constant::Int { i: 2, .. })
                ));
            }
            _ => panic!("Expected Lprim"),
        }
    }

    #[test]
    fn test_simple_beta_reduce_unused_arg() {
        let x = Ident::create_local("x");
        let y = Ident::create_local("y");

        // (fun x y -> x) 1 (side_effect) => side_effect; 1
        // Note: y is unused, but we need to evaluate the argument
        let params = vec![x.clone(), y.clone()];
        let body = Lambda::var(x.clone()); // Only uses x

        // For simple_beta_reduce, complex unused args prevent optimization
        let args = vec![
            Lambda::const_(Constant::int(1)),
            Lambda::var(Ident::create_local("z")), // Variable, so it's okay
        ];

        // This should NOT work because body is not a prim or apply
        let result = simple_beta_reduce(&params, &body, &args);
        assert!(result.is_none());
    }

    #[test]
    fn test_simple_beta_reduce_double_use() {
        let x = Ident::create_local("x");

        // (fun x -> x + x) 1 => should NOT simple reduce (x used twice)
        let params = vec![x.clone()];
        let body = Lambda::prim(
            Primitive::Paddint,
            vec![Lambda::var(x.clone()), Lambda::var(x.clone())],
            Location::none(),
        );
        let args = vec![Lambda::const_(Constant::int(1))];

        let result = simple_beta_reduce(&params, &body, &args);
        assert!(result.is_none());
    }

    #[test]
    fn test_no_names_beta_reduce() {
        let x = Ident::create_local("x");
        let y = Ident::create_local("y");

        // (fun x y -> x + x + y) (f) (g)
        // x is used twice, so simple_beta_reduce won't work
        // => let x = f in let y = g in x + x + y
        let params = vec![x.clone(), y.clone()];
        // Body uses x twice, which prevents simple_beta_reduce
        let body = Lambda::prim(
            Primitive::Paddint,
            vec![
                Lambda::prim(
                    Primitive::Paddint,
                    vec![Lambda::var(x.clone()), Lambda::var(x.clone())],
                    Location::none(),
                ),
                Lambda::var(y.clone()),
            ],
            Location::none(),
        );
        let f = Ident::create_local("f");
        let g = Ident::create_local("g");
        let args = vec![Lambda::var(f), Lambda::var(g)];

        let result = no_names_beta_reduce(&params, &body, &args);

        // Should create let bindings because x is used twice
        match result {
            Lambda::Llet(_, _, _, _) => {}
            _ => panic!("Expected Llet, got {result:?}"),
        }
    }

    #[test]
    fn test_propagate_beta_reduce_preserves_source_argument_order() {
        let x = Ident::create_local("x");
        let y = Ident::create_local("y");
        // A sequence is deliberately outside `simple_beta_reduce`'s
        // primitive/application fast path, so both effectful arguments become
        // explicit strict bindings whose nesting order is observable.
        let body = Lambda::seq(Lambda::var(x.clone()), Lambda::var(y.clone()));
        let call = |name: &str| {
            Lambda::prim(
                Primitive::PjsCall {
                    prim_name: name.to_string(),
                    arg_types: vec![],
                    ffi: crate::lambda::lam_primitive::ExternalFfiSpec {
                        kind: crate::lambda::lam_primitive::ExternalFfiKind::Default,
                        spec: None,
                        obj_params: None,
                        return_wrapper:
                            crate::lambda::lam_primitive::ExternalReturnWrapper::Identity,
                        inline_constant: None,
                    },
                    dynamic_import: false,
                    transformed_jsx: false,
                },
                vec![],
                Location::none(),
            )
        };
        let first = call("first");
        let second = call("second");

        let reduced = propagate_beta_reduce(&[x, y], &body, &[first, second]);
        let Lambda::Llet(_, _, outer_value, inner) = reduced else {
            panic!("expected first argument binding to be outermost");
        };
        assert!(matches!(
            outer_value.as_ref(),
            Lambda::Lprim(PrimInfo {
                primitive: Primitive::PjsCall { prim_name, .. },
                ..
            }) if prim_name == "first"
        ));
        assert!(matches!(
            inner.as_ref(),
            Lambda::Llet(
                _,
                _,
                inner_value,
                _
            ) if matches!(
                inner_value.as_ref(),
                Lambda::Lprim(PrimInfo {
                    primitive: Primitive::PjsCall { prim_name, .. },
                    ..
                }) if prim_name == "second"
            )
        ));
    }

    #[test]
    #[ignore = "stale internal shape expectation; covered by strict lambda/JS parity gates"]
    fn test_propagate_beta_reduce_keeps_let_wrapped_returned_functions() {
        let outer = Ident::create_local("outer");
        let helper = Ident::create_local("helper");
        let inner = Ident::create_local("inner");
        let params = vec![outer];
        let body = Lambda::let_(
            LetKind::Strict,
            helper.clone(),
            Lambda::const_(Constant::int(1)),
            Lambda::function_(
                1,
                vec![inner.clone()],
                Lambda::const_(Constant::int(0)),
                FunctionAttribute::default(),
            ),
        );
        let args = vec![Lambda::const_(Constant::String {
            s: "".to_string(),
            delim: None,
        })];

        let reduced = propagate_beta_reduce(&params, &body, &args);
        let Lambda::Llet(kind, id, value, body) = reduced else {
            panic!("expected helper let-binding to remain");
        };
        assert_eq!(kind, LetKind::Strict);
        assert_eq!(id, helper);
        assert!(matches!(*value, Lambda::Lconst(Constant::Int { i, .. }) if i == 1));
        let Lambda::Lfunction(func) = *body else {
            panic!("expected returned function to remain wrapped by the let");
        };
        assert_eq!(func.params, vec![inner]);
    }

    #[test]
    fn test_propagate_beta_reduce_marks_boxed_nullable_bindings_with_identity() {
        let x = Ident::create_local("x");
        let params = vec![x.clone()];
        let body = Lambda::if_(
            Lambda::prim(
                Primitive::PisNotNone,
                vec![Lambda::var(x.clone())],
                Location::none(),
            ),
            Lambda::prim(
                Primitive::PvalFromOption,
                vec![Lambda::var(x.clone())],
                Location::none(),
            ),
            Lambda::const_(Constant::JsUndefined { is_unit: false }),
        );
        let args = vec![Lambda::prim(
            Primitive::PnullToOpt,
            vec![Lambda::prim(
                Primitive::PjsCall {
                    prim_name: "exec".to_string(),
                    arg_types: vec![],
                    ffi: crate::lambda::lam_primitive::ExternalFfiSpec {
                        kind: crate::lambda::lam_primitive::ExternalFfiKind::Default,
                        spec: None,
                        obj_params: None,
                        return_wrapper:
                            crate::lambda::lam_primitive::ExternalReturnWrapper::Identity,
                        inline_constant: None,
                    },
                    dynamic_import: false,
                    transformed_jsx: false,
                },
                vec![Lambda::const_(Constant::string("subject"))],
                Location::none(),
            )],
            Location::none(),
        )];

        let reduced = propagate_beta_reduce(&params, &body, &args);
        let Lambda::Llet(kind, fresh, value, body) = reduced else {
            panic!("expected boxed nullable beta reduction to introduce a fresh let");
        };
        assert_eq!(kind, LetKind::Strict);
        assert!(matches!(
            *value,
            Lambda::Lprim(PrimInfo {
                primitive: Primitive::Pidentity,
                args,
                ..
            }) if matches!(
                args.as_slice(),
                [Lambda::Lprim(PrimInfo {
                    primitive: Primitive::PnullToOpt,
                    ..
                })]
            )
        ));
        let Lambda::LifThenElse(cond, then_, _) = *body else {
            panic!("expected the reduced body to stay as an if");
        };
        assert!(matches!(
            cond.as_ref(),
            Lambda::Lprim(PrimInfo {
                primitive: Primitive::PisNotNone,
                args,
                ..
            }) if matches!(
                args.as_slice(),
                [Lambda::Lprim(PrimInfo {
                    primitive: Primitive::Pidentity,
                    args: inner_args,
                    ..
                })] if matches!(inner_args.as_slice(), [Lambda::Lvar(id)] if id.same(&fresh))
            )
        ));
        assert!(matches!(
            then_.as_ref(),
            Lambda::Lprim(PrimInfo {
                primitive: Primitive::PvalFromOption,
                args,
                ..
            }) if matches!(
                args.as_slice(),
                [Lambda::Lprim(PrimInfo {
                    primitive: Primitive::Pidentity,
                    args: inner_args,
                    ..
                })] if matches!(inner_args.as_slice(), [Lambda::Lvar(id)] if id.same(&fresh))
            )
        ));
    }

    #[test]
    fn test_propagate_beta_reduce_renames_reused_returned_function_params() {
        let none = Ident::create_local("none");
        let params = vec![none.clone()];
        let body = Lambda::function_(
            1,
            vec![none.clone()],
            Lambda::var(none.clone()),
            FunctionAttribute::default(),
        );
        let args = vec![Lambda::const_(Constant::JsUndefined { is_unit: false })];

        let reduced = propagate_beta_reduce(&params, &body, &args);
        let Lambda::Lfunction(func) = reduced else {
            panic!("expected beta reduction to keep the returned wrapper");
        };
        let [param] = func.params.as_slice() else {
            panic!("expected a single returned parameter");
        };
        assert!(
            !param.same(&none),
            "expected the reused returned parameter to be alpha-renamed"
        );
        assert!(
            matches!(func.body.as_ref(), Lambda::Lvar(body_id) if body_id.same(param)),
            "expected the returned wrapper body to keep using its own parameter, got {func:?}"
        );
    }

    #[test]
    fn test_propagate_beta_reduce_with_map_const() {
        let x = Ident::create_local("x");

        // (fun x -> x + 1) 5
        // With stats showing x is used once in top position
        // => 5 + 1 (direct substitution)
        let params = vec![x.clone()];
        let body = Lambda::prim(
            Primitive::Paddint,
            vec![Lambda::var(x.clone()), Lambda::const_(Constant::int(1))],
            Location::none(),
        );
        let args = vec![Lambda::const_(Constant::int(5))];

        let mut stats = StatsMap::new();
        stats.insert(
            x.clone(),
            VarStats {
                top: true,
                times: 1,
            },
        );

        let result = propagate_beta_reduce_with_map(&stats, &params, &body, &args);

        // Should get direct primitive application
        match result {
            Lambda::Lprim(ref info) => {
                assert!(matches!(
                    info.args[0],
                    Lambda::Lconst(Constant::Int { i: 5, .. })
                ));
            }
            _ => panic!("Expected Lprim, got {result:?}"),
        }
    }

    #[test]
    fn test_propagate_beta_reduce_with_map_pure_once() {
        let x = Ident::create_local("x");
        let y = Ident::create_local("y");

        // (fun x -> x + 1) y where y is pure
        // With stats showing x is used once in top position
        // => y + 1 (substitute because pure and used once)
        let params = vec![x.clone()];
        let body = Lambda::prim(
            Primitive::Paddint,
            vec![Lambda::var(x.clone()), Lambda::const_(Constant::int(1))],
            Location::none(),
        );
        // Lambda::var is pure
        let args = vec![Lambda::var(y.clone())];

        let mut stats = StatsMap::new();
        stats.insert(
            x.clone(),
            VarStats {
                top: true,
                times: 1,
            },
        );

        let result = propagate_beta_reduce_with_map(&stats, &params, &body, &args);

        // Should substitute y directly
        match result {
            Lambda::Lprim(ref info) => match &info.args[0] {
                Lambda::Lvar(id) => assert_eq!(id.name(), "y"),
                _ => panic!("Expected Lvar"),
            },
            _ => panic!("Expected Lprim, got {result:?}"),
        }
    }

    #[test]
    fn test_propagate_beta_reduce_with_map_renames_reused_returned_function_params() {
        let none = Ident::create_local("none");
        let params = vec![none.clone()];
        let body = Lambda::function_(
            1,
            vec![none.clone()],
            Lambda::var(none.clone()),
            FunctionAttribute::default(),
        );
        let args = vec![Lambda::const_(Constant::JsUndefined { is_unit: false })];

        let mut stats = StatsMap::new();
        stats.insert(
            none.clone(),
            VarStats {
                top: true,
                times: 1,
            },
        );

        let reduced = propagate_beta_reduce_with_map(&stats, &params, &body, &args);
        let Lambda::Lfunction(func) = reduced else {
            panic!("expected beta reduction with stats to keep the returned wrapper");
        };
        let [param] = func.params.as_slice() else {
            panic!("expected a single returned parameter");
        };
        assert!(
            !param.same(&none),
            "expected the reused returned parameter to be alpha-renamed"
        );
        assert!(
            matches!(func.body.as_ref(), Lambda::Lvar(body_id) if body_id.same(param)),
            "expected the returned wrapper body to keep using its own parameter, got {func:?}"
        );
    }

    #[test]
    fn test_propagate_beta_reduce_folds_constant_switch_scrutinee_like_ocaml() {
        let x = Ident::create_local("x");
        let reduced = propagate_beta_reduce(
            std::slice::from_ref(&x),
            &Lambda::Lswitch(
                Box::new(Lambda::var(x.clone())),
                LambdaSwitch {
                    sw_consts_full: true,
                    sw_consts: vec![
                        (0, Lambda::const_(Constant::JsFalse)),
                        (1, Lambda::const_(Constant::JsTrue)),
                    ],
                    sw_blocks_full: true,
                    sw_blocks: vec![],
                    sw_failaction: None,
                    sw_names: None,
                },
            ),
            &[Lambda::const_(Constant::int(1))],
        );

        assert!(matches!(reduced, Lambda::Lconst(Constant::JsTrue)));
    }

    #[test]
    fn test_refine_let_identity() {
        let x = Ident::create_local("x");

        // let x = v in x => v
        let value = Lambda::const_(Constant::int(42));
        let body = Lambda::var(x.clone());

        let result = refine_let(LetKind::Strict, x, value.clone(), body);

        assert!(matches!(
            result,
            Lambda::Lconst(Constant::Int { i: 42, .. })
        ));
    }

    #[test]
    fn test_refine_let_normal() {
        let x = Ident::create_local("x");
        let y = Ident::create_local("y");

        // let x = 42 in y => let x = 42 in y (can't optimize)
        let value = Lambda::const_(Constant::int(42));
        let body = Lambda::var(y);

        let result = refine_let(LetKind::Strict, x, value, body);

        assert!(matches!(result, Lambda::Llet(_, _, _, _)));
    }
}
