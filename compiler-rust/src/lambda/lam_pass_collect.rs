//! Direct port of `compiler/core/lam_pass_collect.ml` and the supporting
//! helpers from `compiler/core/lam_arity_analysis.ml` and
//! `compiler/core/lam_util.ml`.
//!
//! Single traversal that populates the [`LamStats`] / `ident_tbl` consumed
//! downstream by `simplify_alias` and `alpha_conversion`. Mirrors
//! OCaml's `Lam_pass_collect.collect_info`.
//!
//! Cross-module arity lookup (`Lam_compile_env.query_external_id_info`) has
//! no Rust counterpart yet, so the two `Pfield (_, Fld_module _)` arms in
//! `get_arity` short-circuit to [`Arity::Na`]. That mirrors what OCaml does
//! when external info is missing: downstream passes simply treat the function
//! as an unknown arity.

use ahash::AHashMap;

use crate::ident::Ident;
use crate::lambda::lam_analysis::{
    SMALL_INLINE_SIZE, lfunction_can_be_inlined, no_side_effects, size_upto,
};
use crate::lambda::lam_arity::Arity;
use crate::lambda::lam_compat::FieldDbgInfo;
use crate::lambda::lam_compile_context::{
    BoxedNullable, Element, ExternalArityInfo, ExternalArityTable, IdKind, LamStats, RecFlag,
};
use crate::lambda::lam_primitive::{Mutable, Primitive};
use crate::lambda::{InlineAttribute, LFunction, Lambda, PrimInfo};

/// Rust counterpart to `Lam_compile_env.query_external_id_info` for
/// `Lam_arity_analysis.get_arity` (compiler/core/lam_arity_analysis.ml:43-71).
pub type ExternalArityResolver<'a> = dyn FnMut(&Ident, &str) -> Option<ExternalArityInfo> + 'a;

/// Direct port of `Lam_util.element_of_lambda` (lam_util.ml:188-196).
///
/// Decides whether a single block field is "simple" enough to substitute on
/// reads. Anything but a Lvar, Lconst or a `Pfield(_, Fld_module _)` from a
/// global module / Lvar is reported as `NA`.
pub(crate) fn element_of_lambda(lam: &Lambda) -> Element {
    match lam {
        Lambda::Lvar(_) | Lambda::Lconst(_) => Element::SimpleForm(lam.clone()),
        Lambda::Lprim(__prim7)
            if matches!(__prim7.as_ref(), PrimInfo {
                primitive: Primitive::Pfield(_, FieldDbgInfo::Module { .. }),
                args,
                ..
            } if matches!(
                args.as_slice(),
                [Lambda::LglobalModule(_) | Lambda::Lvar(_)]
            )) =>
        {
            let PrimInfo {
                primitive: Primitive::Pfield(_, FieldDbgInfo::Module { .. }),
                args: _,
                ..
            } = __prim7.as_ref()
            else {
                unreachable!()
            };

            Element::SimpleForm(lam.clone())
        }
        _ => Element::Na,
    }
}

/// Direct port of `Lam_util.kind_of_lambda_block` (lam_util.ml:198-200).
pub(crate) fn kind_of_lambda_block(xs: &[Lambda]) -> IdKind {
    IdKind::ImmutableBlock(xs.iter().map(element_of_lambda).collect())
}

/// Direct port of `Lam_util.alias_ident_or_global` (lam_util.ml:140-152).
fn alias_ident_or_global(meta: &mut LamStats, k: Ident, v: &Ident, v_kind: IdKind) {
    match v_kind {
        // NA case (lam_util.ml:146-151): only propagate when v already has info.
        IdKind::Na => {
            if let Some(info) = meta.ident_tbl.get(v).cloned() {
                meta.ident_tbl.insert(k, info);
            }
        }
        // Any concrete kind: assign directly (lam_util.ml:152).
        info => {
            meta.ident_tbl.insert(k, info);
        }
    }
}

/// Direct port of `Lam_arity_analysis.arity_of_var` (lam_arity_analysis.ml:25-31).
fn arity_of_var(ident_tbl: &AHashMap<Ident, IdKind>, v: &Ident) -> Arity {
    match ident_tbl.get(v) {
        Some(IdKind::FunctionId { arity, .. }) => arity.clone(),
        _ => Arity::na(),
    }
}

fn lookup_external_arity_entry<'a>(
    external_arities: &'a ExternalArityTable,
    module_id: &Ident,
    field_name: &str,
) -> Option<&'a Option<ExternalArityInfo>> {
    external_arities
        .get(module_id.name())
        .and_then(|fields| fields.get(field_name))
}

fn lookup_cached_external_arity<'a>(
    external_arities: &'a ExternalArityTable,
    module_id: &Ident,
    field_name: &str,
) -> Option<&'a ExternalArityInfo> {
    lookup_external_arity_entry(external_arities, module_id, field_name).and_then(Option::as_ref)
}

fn resolve_external_arity(
    external_arities: &mut ExternalArityTable,
    module_id: &Ident,
    field_name: &str,
    resolver: &mut ExternalArityResolver<'_>,
) -> Option<ExternalArityInfo> {
    if let Some(cached) = lookup_external_arity_entry(external_arities, module_id, field_name) {
        return cached.clone();
    }
    let resolved = resolver(module_id, field_name);
    external_arities
        .entry(module_id.name().to_string())
        .or_default()
        .insert(field_name.to_string(), resolved.clone());
    resolved
}

/// Direct port of `Lam_arity_analysis.get_arity` (lam_arity_analysis.ml:38-132).
///
/// The two `Pfield (_, Fld_module _)` arms in OCaml call
/// `Lam_compile_env.query_external_id_info` to fetch the foreign module's
/// recorded arity (compiler/core/lam_arity_analysis.ml:43-71).
fn get_arity_impl<F>(
    ident_tbl: &AHashMap<Ident, IdKind>,
    lam: &Lambda,
    lookup_external_arity: &mut F,
) -> Arity
where
    F: FnMut(&Ident, &str) -> Option<ExternalArityInfo>,
{
    match lam {
        // lam_arity_analysis.ml:40
        Lambda::Lvar(v) => arity_of_var(ident_tbl, v),
        // lam_arity_analysis.ml:41
        Lambda::Lconst(_) => Arity::non_function(),
        // lam_arity_analysis.ml:42
        Lambda::Llet(_, _, _, body) => get_arity_impl(ident_tbl, body, lookup_external_arity),
        // lam_arity_analysis.ml:43-56 — cross-module Pfield arm.
        Lambda::Lprim(__prim6)
            if matches!(__prim6.as_ref(), PrimInfo {
            primitive: Primitive::Pfield(_, FieldDbgInfo::Module { name }),
            args,
            ..
        } if matches!(args.as_slice(), [Lambda::LglobalModule(_)])) =>
        {
            let PrimInfo {
                primitive: Primitive::Pfield(_, FieldDbgInfo::Module { name }),
                args,
                ..
            } = __prim6.as_ref()
            else {
                unreachable!()
            };

            let [Lambda::LglobalModule(id)] = args.as_slice() else {
                unreachable!("guarded by matches!");
            };
            match lookup_external_arity(id, name) {
                Some(ExternalArityInfo::Single(arity)) => arity.clone(),
                Some(ExternalArityInfo::Submodule(_)) | None => Arity::na(),
            }
        }
        // lam_arity_analysis.ml:57-71 — nested submodule Pfield arm.
        Lambda::Lprim(__prim5)
            if matches!(__prim5.as_ref(), PrimInfo {
                        primitive: Primitive::Pfield(index, _),
                        args,
                        ..
                    } if matches!(
                        args.as_slice(),
                        [Lambda::Lprim(__prim100)] if matches!(__prim100.as_ref(), PrimInfo {
                            primitive: Primitive::Pfield(_, FieldDbgInfo::Module { .. }),
                            args: inner_args,
                            ..
                        } if matches!(inner_args.as_slice(), [Lambda::LglobalModule(_)]))
            )) =>
        {
            let PrimInfo {
                primitive: Primitive::Pfield(index, _),
                args,
                ..
            } = __prim5.as_ref()
            else {
                unreachable!()
            };

            let [Lambda::Lprim(__prim200)] = args.as_slice() else {
                unreachable!("guarded by matches!");
            };
            let PrimInfo {
                primitive: Primitive::Pfield(_, FieldDbgInfo::Module { name }),
                args: inner_args,
                ..
            } = __prim200.as_ref()
            else {
                unreachable!("guarded by matches!");
            };
            let [Lambda::LglobalModule(id)] = inner_args.as_slice() else {
                unreachable!("guarded by matches!");
            };
            match lookup_external_arity(id, name) {
                Some(ExternalArityInfo::Submodule(arities)) => arities
                    .get(*index as usize)
                    .cloned()
                    .unwrap_or_else(Arity::na),
                Some(ExternalArityInfo::Single(_)) | None => Arity::na(),
            }
        }
        // lam_arity_analysis.ml:72
        Lambda::Lprim(__prim4)
            if matches!(
                __prim4.as_ref(),
                PrimInfo {
                    primitive: Primitive::Praise,
                    ..
                }
            ) =>
        {
            let PrimInfo {
                primitive: Primitive::Praise,
                ..
            } = __prim4.as_ref()
            else {
                unreachable!()
            };
            Arity::raise()
        }
        // lam_arity_analysis.ml:73-74
        Lambda::LglobalModule(_) | Lambda::Lprim(_) => Arity::na(),
        // lam_arity_analysis.ml:87
        Lambda::Lletrec(_, body) => get_arity_impl(ident_tbl, body, lookup_external_arity),
        // lam_arity_analysis.ml:88-105
        Lambda::Lapply(apply) => {
            let fn_arity = get_arity_impl(ident_tbl, &apply.ap_func, lookup_external_arity);
            match fn_arity {
                Arity::Na => Arity::na(),
                Arity::Info { arities, variadic } => {
                    fn take(mut arities: Vec<i32>, mut arg_length: i32, variadic: bool) -> Arity {
                        loop {
                            match arities.first().copied() {
                                Some(x) => {
                                    if arg_length == x {
                                        arities.remove(0);
                                        return Arity::info(arities, variadic);
                                    } else if arg_length > x {
                                        arities.remove(0);
                                        arg_length -= x;
                                    } else {
                                        let remaining = x - arg_length;
                                        arities[0] = remaining;
                                        return Arity::info(arities, variadic);
                                    }
                                }
                                None => {
                                    return if variadic {
                                        Arity::raise()
                                    } else {
                                        Arity::na()
                                    };
                                }
                            }
                        }
                    }
                    take(arities, apply.ap_args.len() as i32, variadic)
                }
            }
        }
        // lam_arity_analysis.ml:106
        Lambda::Lfunction(func) => {
            get_arity_impl(ident_tbl, &func.body, lookup_external_arity).merge(func.arity)
        }
        // lam_arity_analysis.ml:107-122
        Lambda::Lswitch(_, switch) => {
            let mut all: Vec<&Lambda> = switch.sw_consts.iter().map(|(_, l)| l).collect();
            all.extend(switch.sw_blocks.iter().map(|(_, l)| l));
            if let Some(fail) = switch.sw_failaction.as_deref() {
                let mut with_fail = vec![fail];
                with_fail.extend(all);
                all_lambdas(ident_tbl, &with_fail, lookup_external_arity)
            } else {
                all_lambdas(ident_tbl, &all, lookup_external_arity)
            }
        }
        // lam_arity_analysis.ml:123-126
        Lambda::LstringSwitch(_, sw, d) => {
            let cases: Vec<&Lambda> = sw.iter().map(|(_, l)| l).collect();
            match d.as_deref() {
                None => all_lambdas(ident_tbl, &cases, lookup_external_arity),
                Some(default) => {
                    let mut with_default = vec![default];
                    with_default.extend(cases);
                    all_lambdas(ident_tbl, &with_default, lookup_external_arity)
                }
            }
        }
        // lam_arity_analysis.ml:127
        Lambda::LstaticCatch(_, _, handler) => {
            get_arity_impl(ident_tbl, handler, lookup_external_arity)
        }
        // lam_arity_analysis.ml:128
        Lambda::LtryWith(l1, _, l2) => all_lambdas(ident_tbl, &[l1, l2], lookup_external_arity),
        // lam_arity_analysis.ml:129
        Lambda::LifThenElse(_, l2, l3) => all_lambdas(ident_tbl, &[l2, l3], lookup_external_arity),
        // lam_arity_analysis.ml:130
        Lambda::Lsequence(_, l2) => get_arity_impl(ident_tbl, l2, lookup_external_arity),
        // lam_arity_analysis.ml:131
        Lambda::LstaticRaise(_, _) => Arity::na(),
        // lam_arity_analysis.ml:132
        Lambda::Lwhile(_, _)
        | Lambda::Lfor(_, _, _, _, _)
        | Lambda::Lfor_of(_, _, _)
        | Lambda::Lfor_await_of(_, _, _)
        | Lambda::Lbreak
        | Lambda::Lcontinue
        | Lambda::Lassign(_, _) => Arity::non_function(),
    }
}

pub fn get_arity(meta: &LamStats, lam: &Lambda) -> Arity {
    let mut lookup_external_arity = |module_id: &Ident, field_name: &str| {
        lookup_cached_external_arity(&meta.external_arities, module_id, field_name).cloned()
    };
    get_arity_impl(&meta.ident_tbl, lam, &mut lookup_external_arity)
}

pub(crate) fn get_arity_with_external_arity(
    meta: &mut LamStats,
    lam: &Lambda,
    resolver: &mut ExternalArityResolver<'_>,
) -> Arity {
    let ident_tbl = &meta.ident_tbl;
    let external_arities = &mut meta.external_arities;
    let mut lookup_external_arity = |module_id: &Ident, field_name: &str| {
        resolve_external_arity(external_arities, module_id, field_name, resolver)
    };
    get_arity_impl(ident_tbl, lam, &mut lookup_external_arity)
}

/// Direct port of `Lam_arity_analysis.all_lambdas` (lam_arity_analysis.ml:134-149).
fn all_lambdas<F>(
    ident_tbl: &AHashMap<Ident, IdKind>,
    xs: &[&Lambda],
    lookup_external_arity: &mut F,
) -> Arity
where
    F: FnMut(&Ident, &str) -> Option<ExternalArityInfo>,
{
    match xs.split_first() {
        None => Arity::na(),
        Some((y, ys)) => {
            let mut acc = get_arity_impl(ident_tbl, y, lookup_external_arity);
            for x in ys {
                match acc {
                    Arity::Na => return Arity::na(),
                    Arity::Info { arities, variadic } => {
                        match get_arity_impl(ident_tbl, x, lookup_external_arity) {
                            Arity::Na => return Arity::na(),
                            Arity::Info {
                                arities: ya,
                                variadic: vy,
                            } => {
                                acc = Arity::merge_arities(&arities, &ya, variadic, vy);
                            }
                        }
                    }
                }
            }
            acc
        }
    }
}

/// Direct port of `Lam_pass_collect.annotate` (lam_pass_collect.ml:34-37).
fn annotate(
    meta: &mut LamStats,
    rec_flag: RecFlag,
    k: Ident,
    arity: Arity,
    lambda: Option<Lambda>,
) {
    meta.ident_tbl.insert(
        k,
        IdKind::FunctionId {
            arity,
            lambda: lambda.map(|lambda| (lambda, rec_flag)),
        },
    );
}

fn param_driven_destructuring_may_inline(func: &LFunction) -> bool {
    fn is_param(params: &[Ident], test: &Lambda) -> bool {
        match test {
            Lambda::Lvar(v) => params.iter().any(|p| p == v),
            _ => false,
        }
    }

    match func.body.as_ref() {
        Lambda::Lswitch(test, _) => is_param(&func.params, test),
        Lambda::LifThenElse(test, _, _) => is_param(&func.params, test),
        _ => false,
    }
}

fn function_payload_needed(func: &LFunction) -> bool {
    if !lfunction_can_be_inlined(func) {
        return false;
    }

    // OCaml stores every lambda in collect (lam_pass_collect.ml:79-89)
    // because that is only pointer sharing. In Rust it is a deep clone, so we
    // keep payloads only for cases remove-alias can consume:
    // functors are always beta-reduced (lam_pass_remove_alias.ml:185-197),
    // and normal functions are gated by ok_to_inline_fun_when_app
    // (lam_analysis.ml:250-260).
    if func.attr.is_a_functor {
        return true;
    }

    match func.attr.inline {
        InlineAttribute::Always => true,
        InlineAttribute::Never => false,
        InlineAttribute::Default => {
            let body_size = size_upto(10, &func.body);
            body_size < SMALL_INLINE_SIZE
                || body_size < 10 && no_side_effects(&func.body)
                || param_driven_destructuring_may_inline(func)
        }
    }
}

/// Direct port of `Lam_pass_collect.collect_bind` (lam_pass_collect.ml:58-93).
fn collect_bind_with_external(
    meta: &mut LamStats,
    rec_flag: RecFlag,
    ident: &Ident,
    lam: &Lambda,
    resolver: &mut Option<&mut ExternalArityResolver<'_>>,
) {
    match lam {
        // lam_pass_collect.ml:60
        Lambda::Lconst(v) => {
            meta.ident_tbl.insert(*ident, IdKind::Constant(v.clone()));
        }
        // lam_pass_collect.ml:61-63 — Pmakeblock immutable: ImmutableBlock + recurse.
        Lambda::Lprim(__prim3)
            if matches!(
                __prim3.as_ref(),
                PrimInfo {
                    primitive: Primitive::Pmakeblock(_, Mutable::Immutable),
                    args: _,
                    ..
                }
            ) =>
        {
            let PrimInfo {
                primitive: Primitive::Pmakeblock(_, Mutable::Immutable),
                args,
                ..
            } = __prim3.as_ref()
            else {
                unreachable!()
            };

            meta.ident_tbl.insert(*ident, kind_of_lambda_block(args));
            for arg in args {
                collect_with_external(meta, arg, resolver);
            }
        }
        // lam_pass_collect.ml:64-66 — Psome / Psome_not_nest: Normal_optional.
        Lambda::Lprim(__prim2)
            if matches!(__prim2.as_ref(), PrimInfo {
            primitive: Primitive::Psome | Primitive::PsomeNotNest,
            args,
            ..
        } if args.len() == 1) =>
        {
            let PrimInfo {
                primitive: Primitive::Psome | Primitive::PsomeNotNest,
                args,
                ..
            } = __prim2.as_ref()
            else {
                unreachable!()
            };

            meta.ident_tbl
                .insert(*ident, IdKind::NormalOptional(args[0].clone()));
            collect_with_external(meta, &args[0], resolver);
        }
        // lam_pass_collect.ml:67-68 — Pnull_to_opt with [Lvar]: OptionalBlock(_, Null).
        Lambda::Lprim(__prim1)
            if matches!(__prim1.as_ref(), PrimInfo {
            primitive: Primitive::PnullToOpt,
            args,
            ..
        } if matches!(args.as_slice(), [Lambda::Lvar(_)])) =>
        {
            let PrimInfo {
                primitive: Primitive::PnullToOpt,
                args,
                ..
            } = __prim1.as_ref()
            else {
                unreachable!()
            };

            meta.ident_tbl.insert(
                *ident,
                IdKind::OptionalBlock(args[0].clone(), BoxedNullable::Null),
            );
        }
        // lam_pass_collect.ml:69-71 — Pnull_undefined_to_opt with [Lvar].
        Lambda::Lprim(__prim0)
            if matches!(__prim0.as_ref(), PrimInfo {
            primitive: Primitive::PnullUndefinedToOpt,
            args,
            ..
        } if matches!(args.as_slice(), [Lambda::Lvar(_)])) =>
        {
            let PrimInfo {
                primitive: Primitive::PnullUndefinedToOpt,
                args,
                ..
            } = __prim0.as_ref()
            else {
                unreachable!()
            };

            meta.ident_tbl.insert(
                *ident,
                IdKind::OptionalBlock(args[0].clone(), BoxedNullable::NullUndefined),
            );
        }
        // lam_pass_collect.ml:72-73 — Lglobal_module: alias to Module.
        Lambda::LglobalModule(v) => {
            alias_ident_or_global(meta, *ident, v, IdKind::Module(*v));
        }
        // lam_pass_collect.ml:74-77 — Lvar: alias with NA propagation.
        Lambda::Lvar(v) => {
            alias_ident_or_global(meta, *ident, v, IdKind::Na);
        }
        // lam_pass_collect.ml:79-89 — Lfunction: register params and FunctionId.
        Lambda::Lfunction(func) => {
            for p in &func.params {
                meta.ident_tbl.insert(*p, IdKind::Parameter);
            }
            let arity = match resolver.as_deref_mut() {
                Some(resolver) => get_arity_with_external_arity(meta, lam, resolver),
                None => get_arity(meta, lam),
            };
            let payload = (meta.collect_function_payloads && function_payload_needed(func))
                .then(|| lam.clone());
            annotate(meta, rec_flag, *ident, arity, payload);
            collect_with_external(meta, &func.body, resolver);
        }
        // lam_pass_collect.ml:90-93 — fallback: collect, annotate exports.
        x => {
            collect_with_external(meta, x, resolver);
            if meta.export_idents.contains(ident) {
                let arity = match resolver.as_deref_mut() {
                    Some(resolver) => get_arity_with_external_arity(meta, x, resolver),
                    None => get_arity(meta, x),
                };
                // OCaml stores `x` too (lam_pass_collect.ml:90-93), but the
                // only reader of the payload, remove-alias inlining, wants an
                // `Lfunction` (lam_pass_remove_alias.ml:185-197) and `x` is not
                // one; skip the deep copy.
                annotate(meta, rec_flag, *ident, arity, None);
            }
        }
    }
}

/// Direct port of `Lam_pass_collect.collect` (lam_pass_collect.ml:94-150).
fn collect_with_external(
    meta: &mut LamStats,
    lam: &Lambda,
    resolver: &mut Option<&mut ExternalArityResolver<'_>>,
) {
    match lam {
        // lam_pass_collect.ml:96-97
        Lambda::Lconst(_) | Lambda::Lvar(_) => {}
        // lam_pass_collect.ml:98-100
        Lambda::Lapply(apply) => {
            collect_with_external(meta, &apply.ap_func, resolver);
            for arg in &apply.ap_args {
                collect_with_external(meta, arg, resolver);
            }
        }
        // lam_pass_collect.ml:101-104
        Lambda::Lfunction(func) => {
            for p in &func.params {
                meta.ident_tbl.insert(*p, IdKind::Parameter);
            }
            collect_with_external(meta, &func.body, resolver);
        }
        // lam_pass_collect.ml:105-107
        Lambda::Llet(_kind, ident, arg, body) => {
            collect_bind_with_external(meta, RecFlag::NonRec, ident, arg, resolver);
            collect_with_external(meta, body, resolver);
        }
        // lam_pass_collect.ml:108-114
        Lambda::Lletrec(bindings, body) => {
            match bindings.as_slice() {
                [(ident, arg)] => {
                    collect_bind_with_external(meta, RecFlag::SelfRec, ident, arg, resolver)
                }
                _ => {
                    for (ident, arg) in bindings {
                        collect_bind_with_external(meta, RecFlag::Rec, ident, arg, resolver);
                    }
                }
            }
            collect_with_external(meta, body, resolver);
        }
        // lam_pass_collect.ml:115
        Lambda::LglobalModule(_) => {}
        // lam_pass_collect.ml:116
        Lambda::Lprim(prim) => {
            for arg in &prim.args {
                collect_with_external(meta, arg, resolver);
            }
        }
        // lam_pass_collect.ml:117-121
        Lambda::Lswitch(scrut, switch) => {
            collect_with_external(meta, scrut, resolver);
            for (_, body) in &switch.sw_consts {
                collect_with_external(meta, body, resolver);
            }
            for (_, body) in &switch.sw_blocks {
                collect_with_external(meta, body, resolver);
            }
            if let Some(fail) = switch.sw_failaction.as_deref() {
                collect_with_external(meta, fail, resolver);
            }
        }
        // lam_pass_collect.ml:122-125
        Lambda::LstringSwitch(scrut, sw, d) => {
            collect_with_external(meta, scrut, resolver);
            for (_, body) in sw {
                collect_with_external(meta, body, resolver);
            }
            if let Some(default) = d.as_deref() {
                collect_with_external(meta, default, resolver);
            }
        }
        // lam_pass_collect.ml:126
        Lambda::LstaticRaise(_, args) => {
            for arg in args {
                collect_with_external(meta, arg, resolver);
            }
        }
        // lam_pass_collect.ml:127-129
        Lambda::LstaticCatch(l1, _, l2) => {
            collect_with_external(meta, l1, resolver);
            collect_with_external(meta, l2, resolver);
        }
        // lam_pass_collect.ml:130-132
        Lambda::LtryWith(l1, _, l2) => {
            collect_with_external(meta, l1, resolver);
            collect_with_external(meta, l2, resolver);
        }
        // lam_pass_collect.ml:133-136
        Lambda::LifThenElse(l1, l2, l3) => {
            collect_with_external(meta, l1, resolver);
            collect_with_external(meta, l2, resolver);
            collect_with_external(meta, l3, resolver);
        }
        // lam_pass_collect.ml:137-139
        Lambda::Lsequence(l1, l2) => {
            collect_with_external(meta, l1, resolver);
            collect_with_external(meta, l2, resolver);
        }
        // lam_pass_collect.ml:140-142
        Lambda::Lwhile(l1, l2) => {
            collect_with_external(meta, l1, resolver);
            collect_with_external(meta, l2, resolver);
        }
        // lam_pass_collect.ml:143-146
        Lambda::Lfor(_, l1, l2, _, l3) => {
            collect_with_external(meta, l1, resolver);
            collect_with_external(meta, l2, resolver);
            collect_with_external(meta, l3, resolver);
        }
        // lam_pass_collect.ml after #7887: Lfor_of / Lfor_await_of.
        Lambda::Lfor_of(_, l1, l2) | Lambda::Lfor_await_of(_, l1, l2) => {
            collect_with_external(meta, l1, resolver);
            collect_with_external(meta, l2, resolver);
        }
        // OCaml `Lam_pass_collect.collect` after #8348:
        // `Lbreak | Lcontinue -> ()`.
        Lambda::Lbreak | Lambda::Lcontinue => {}
        // lam_pass_collect.ml:147-150
        Lambda::Lassign(_, l) => collect_with_external(meta, l, resolver),
    }
}

/// Direct port of `Lam_pass_collect.collect_info`
/// (lam_pass_collect.ml:57-152). Mutates `meta.ident_tbl` with the kind /
/// arity info gathered from a single traversal of `lam`.
pub fn collect_info(meta: &mut LamStats, lam: &Lambda) {
    let mut resolver = None;
    collect_with_external(meta, lam, &mut resolver);
}

pub fn collect_info_with_external_arity(
    meta: &mut LamStats,
    lam: &Lambda,
    resolver: &mut ExternalArityResolver<'_>,
) {
    let mut resolver = Some(resolver);
    collect_with_external(meta, lam, &mut resolver);
}
