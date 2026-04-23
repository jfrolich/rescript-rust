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

use crate::ident::Ident;
use crate::lambda::lam_arity::Arity;
use crate::lambda::lam_compat::FieldDbgInfo;
use crate::lambda::lam_compile_context::{BoxedNullable, Element, IdKind, LamStats, RecFlag};
use crate::lambda::lam_primitive::{Mutable, Primitive};
use crate::lambda::{Lambda, PrimInfo};

/// Direct port of `Lam_util.element_of_lambda` (lam_util.ml:188-196).
///
/// Decides whether a single block field is "simple" enough to substitute on
/// reads. Anything but a Lvar, Lconst or a `Pfield(_, Fld_module _)` from a
/// global module / Lvar is reported as `NA`.
pub(crate) fn element_of_lambda(lam: &Lambda) -> Element {
    match lam {
        Lambda::Lvar(_) | Lambda::Lconst(_) => Element::SimpleForm(lam.clone()),
        Lambda::Lprim(PrimInfo {
            primitive: Primitive::Pfield(_, FieldDbgInfo::Module { .. }),
            args,
            ..
        }) if matches!(
            args.as_slice(),
            [Lambda::LglobalModule(_, _) | Lambda::Lvar(_)]
        ) =>
        {
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
fn arity_of_var(meta: &LamStats, v: &Ident) -> Arity {
    match meta.ident_tbl.get(v) {
        Some(IdKind::FunctionId { arity, .. }) => arity.clone(),
        _ => Arity::na(),
    }
}

/// Direct port of `Lam_arity_analysis.get_arity` (lam_arity_analysis.ml:38-132).
///
/// The two `Pfield (_, Fld_module _)` arms in OCaml call
/// `Lam_compile_env.query_external_id_info` to fetch the foreign module's
/// recorded arity. The Rust code has no equivalent yet, so both arms return
/// [`Arity::na`] here. This matches OCaml's behavior whenever the external
/// info is unavailable.
pub fn get_arity(meta: &LamStats, lam: &Lambda) -> Arity {
    match lam {
        // lam_arity_analysis.ml:40
        Lambda::Lvar(v) => arity_of_var(meta, v),
        // lam_arity_analysis.ml:41
        Lambda::Lconst(_) => Arity::non_function(),
        // lam_arity_analysis.ml:42
        Lambda::Llet(_, _, _, body) => get_arity(meta, body),
        // lam_arity_analysis.ml:43-71 — cross-module Pfield arms. No Rust
        // counterpart for `query_external_id_info`, so fall back to NA.
        Lambda::Lprim(PrimInfo {
            primitive: Primitive::Pfield(_, FieldDbgInfo::Module { .. }),
            args,
            ..
        }) if matches!(args.as_slice(), [Lambda::LglobalModule(_, _)]) => Arity::na(),
        Lambda::Lprim(PrimInfo {
            primitive: Primitive::Pfield(_, _),
            args,
            ..
        }) if matches!(
            args.as_slice(),
            [Lambda::Lprim(PrimInfo {
                primitive: Primitive::Pfield(_, FieldDbgInfo::Module { .. }),
                args: inner_args,
                ..
            })] if matches!(inner_args.as_slice(), [Lambda::LglobalModule(_, _)])
        ) =>
        {
            Arity::na()
        }
        // lam_arity_analysis.ml:72
        Lambda::Lprim(PrimInfo {
            primitive: Primitive::Praise,
            ..
        }) => Arity::raise(),
        // lam_arity_analysis.ml:73-74
        Lambda::LglobalModule(_, _) | Lambda::Lprim(_) => Arity::na(),
        // lam_arity_analysis.ml:87
        Lambda::Lletrec(_, body) => get_arity(meta, body),
        // lam_arity_analysis.ml:88-105
        Lambda::Lapply(apply) => {
            let fn_arity = get_arity(meta, &apply.ap_func);
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
        Lambda::Lfunction(func) => get_arity(meta, &func.body).merge(func.arity),
        // lam_arity_analysis.ml:107-122
        Lambda::Lswitch(_, switch) => {
            let mut all: Vec<&Lambda> = switch.sw_consts.iter().map(|(_, l)| l).collect();
            all.extend(switch.sw_blocks.iter().map(|(_, l)| l));
            if let Some(fail) = switch.sw_failaction.as_deref() {
                let mut with_fail = vec![fail];
                with_fail.extend(all);
                all_lambdas(meta, &with_fail)
            } else {
                all_lambdas(meta, &all)
            }
        }
        // lam_arity_analysis.ml:123-126
        Lambda::LstringSwitch(_, sw, d) => {
            let cases: Vec<&Lambda> = sw.iter().map(|(_, l)| l).collect();
            match d.as_deref() {
                None => all_lambdas(meta, &cases),
                Some(default) => {
                    let mut with_default = vec![default];
                    with_default.extend(cases);
                    all_lambdas(meta, &with_default)
                }
            }
        }
        // lam_arity_analysis.ml:127
        Lambda::LstaticCatch(_, _, handler) => get_arity(meta, handler),
        // lam_arity_analysis.ml:128
        Lambda::LtryWith(l1, _, l2) => all_lambdas(meta, &[l1, l2]),
        // lam_arity_analysis.ml:129
        Lambda::LifThenElse(_, l2, l3) => all_lambdas(meta, &[l2, l3]),
        // lam_arity_analysis.ml:130
        Lambda::Lsequence(_, l2) => get_arity(meta, l2),
        // lam_arity_analysis.ml:131
        Lambda::LstaticRaise(_, _) => Arity::na(),
        // lam_arity_analysis.ml:132
        Lambda::Lwhile(_, _)
        | Lambda::Lfor(_, _, _, _, _)
        | Lambda::Lbreak
        | Lambda::Lcontinue
        | Lambda::Lassign(_, _) => Arity::non_function(),
    }
}

/// Direct port of `Lam_arity_analysis.all_lambdas` (lam_arity_analysis.ml:134-149).
fn all_lambdas(meta: &LamStats, xs: &[&Lambda]) -> Arity {
    match xs.split_first() {
        None => Arity::na(),
        Some((y, ys)) => {
            let mut acc = get_arity(meta, y);
            for x in ys {
                match acc {
                    Arity::Na => return Arity::na(),
                    Arity::Info { arities, variadic } => match get_arity(meta, x) {
                        Arity::Na => return Arity::na(),
                        Arity::Info {
                            arities: ya,
                            variadic: vy,
                        } => {
                            acc = Arity::merge_arities(&arities, &ya, variadic, vy);
                        }
                    },
                }
            }
            acc
        }
    }
}

/// Direct port of `Lam_pass_collect.annotate` (lam_pass_collect.ml:34-37).
fn annotate(meta: &mut LamStats, rec_flag: RecFlag, k: Ident, arity: Arity, lambda: Lambda) {
    meta.ident_tbl.insert(
        k,
        IdKind::FunctionId {
            arity,
            lambda: Some((lambda, rec_flag)),
        },
    );
}

/// Direct port of `Lam_pass_collect.collect_bind` (lam_pass_collect.ml:58-93).
fn collect_bind(meta: &mut LamStats, rec_flag: RecFlag, ident: &Ident, lam: &Lambda) {
    match lam {
        // lam_pass_collect.ml:60
        Lambda::Lconst(v) => {
            meta.ident_tbl.insert(ident.clone(), IdKind::Constant(v.clone()));
        }
        // lam_pass_collect.ml:61-63 — Pmakeblock immutable: ImmutableBlock + recurse.
        Lambda::Lprim(PrimInfo {
            primitive: Primitive::Pmakeblock(_, _, Mutable::Immutable),
            args,
            ..
        }) => {
            meta.ident_tbl.insert(ident.clone(), kind_of_lambda_block(args));
            for arg in args {
                collect(meta, arg);
            }
        }
        // lam_pass_collect.ml:64-66 — Psome / Psome_not_nest: Normal_optional.
        Lambda::Lprim(PrimInfo {
            primitive: Primitive::Psome | Primitive::PsomeNotNest,
            args,
            ..
        }) if args.len() == 1 => {
            meta.ident_tbl
                .insert(ident.clone(), IdKind::NormalOptional(args[0].clone()));
            collect(meta, &args[0]);
        }
        // lam_pass_collect.ml:67-68 — Pnull_to_opt with [Lvar]: OptionalBlock(_, Null).
        Lambda::Lprim(PrimInfo {
            primitive: Primitive::PnullToOpt,
            args,
            ..
        }) if matches!(args.as_slice(), [Lambda::Lvar(_)]) => {
            meta.ident_tbl.insert(
                ident.clone(),
                IdKind::OptionalBlock(args[0].clone(), BoxedNullable::Null),
            );
        }
        // lam_pass_collect.ml:69-71 — Pnull_undefined_to_opt with [Lvar].
        Lambda::Lprim(PrimInfo {
            primitive: Primitive::PnullUndefinedToOpt,
            args,
            ..
        }) if matches!(args.as_slice(), [Lambda::Lvar(_)]) => {
            meta.ident_tbl.insert(
                ident.clone(),
                IdKind::OptionalBlock(args[0].clone(), BoxedNullable::NullUndefined),
            );
        }
        // lam_pass_collect.ml:72-73 — Lglobal_module: alias to Module.
        Lambda::LglobalModule(v, _) => {
            alias_ident_or_global(meta, ident.clone(), v, IdKind::Module(v.clone()));
        }
        // lam_pass_collect.ml:74-77 — Lvar: alias with NA propagation.
        Lambda::Lvar(v) => {
            alias_ident_or_global(meta, ident.clone(), v, IdKind::Na);
        }
        // lam_pass_collect.ml:79-89 — Lfunction: register params and FunctionId.
        Lambda::Lfunction(func) => {
            for p in &func.params {
                meta.ident_tbl.insert(p.clone(), IdKind::Parameter);
            }
            let arity = get_arity(meta, lam);
            annotate(meta, rec_flag, ident.clone(), arity, lam.clone());
            collect(meta, &func.body);
        }
        // lam_pass_collect.ml:90-93 — fallback: collect, annotate exports.
        x => {
            collect(meta, x);
            if meta.export_idents.contains(ident) {
                let arity = get_arity(meta, x);
                annotate(meta, rec_flag, ident.clone(), arity, lam.clone());
            }
        }
    }
}

/// Direct port of `Lam_pass_collect.collect` (lam_pass_collect.ml:94-150).
fn collect(meta: &mut LamStats, lam: &Lambda) {
    match lam {
        // lam_pass_collect.ml:96-97
        Lambda::Lconst(_) | Lambda::Lvar(_) => {}
        // lam_pass_collect.ml:98-100
        Lambda::Lapply(apply) => {
            collect(meta, &apply.ap_func);
            for arg in &apply.ap_args {
                collect(meta, arg);
            }
        }
        // lam_pass_collect.ml:101-104
        Lambda::Lfunction(func) => {
            for p in &func.params {
                meta.ident_tbl.insert(p.clone(), IdKind::Parameter);
            }
            collect(meta, &func.body);
        }
        // lam_pass_collect.ml:105-107
        Lambda::Llet(_kind, ident, arg, body) => {
            collect_bind(meta, RecFlag::NonRec, ident, arg);
            collect(meta, body);
        }
        // lam_pass_collect.ml:108-114
        Lambda::Lletrec(bindings, body) => {
            match bindings.as_slice() {
                [(ident, arg)] => collect_bind(meta, RecFlag::SelfRec, ident, arg),
                _ => {
                    for (ident, arg) in bindings {
                        collect_bind(meta, RecFlag::Rec, ident, arg);
                    }
                }
            }
            collect(meta, body);
        }
        // lam_pass_collect.ml:115
        Lambda::LglobalModule(_, _) => {}
        // lam_pass_collect.ml:116
        Lambda::Lprim(prim) => {
            for arg in &prim.args {
                collect(meta, arg);
            }
        }
        // lam_pass_collect.ml:117-121
        Lambda::Lswitch(scrut, switch) => {
            collect(meta, scrut);
            for (_, body) in &switch.sw_consts {
                collect(meta, body);
            }
            for (_, body) in &switch.sw_blocks {
                collect(meta, body);
            }
            if let Some(fail) = switch.sw_failaction.as_deref() {
                collect(meta, fail);
            }
        }
        // lam_pass_collect.ml:122-125
        Lambda::LstringSwitch(scrut, sw, d) => {
            collect(meta, scrut);
            for (_, body) in sw {
                collect(meta, body);
            }
            if let Some(default) = d.as_deref() {
                collect(meta, default);
            }
        }
        // lam_pass_collect.ml:126
        Lambda::LstaticRaise(_, args) => {
            for arg in args {
                collect(meta, arg);
            }
        }
        // lam_pass_collect.ml:127-129
        Lambda::LstaticCatch(l1, _, l2) => {
            collect(meta, l1);
            collect(meta, l2);
        }
        // lam_pass_collect.ml:130-132
        Lambda::LtryWith(l1, _, l2) => {
            collect(meta, l1);
            collect(meta, l2);
        }
        // lam_pass_collect.ml:133-136
        Lambda::LifThenElse(l1, l2, l3) => {
            collect(meta, l1);
            collect(meta, l2);
            collect(meta, l3);
        }
        // lam_pass_collect.ml:137-139
        Lambda::Lsequence(l1, l2) => {
            collect(meta, l1);
            collect(meta, l2);
        }
        // lam_pass_collect.ml:140-142
        Lambda::Lwhile(l1, l2) => {
            collect(meta, l1);
            collect(meta, l2);
        }
        // lam_pass_collect.ml:143-146
        Lambda::Lfor(_, l1, l2, _, l3) => {
            collect(meta, l1);
            collect(meta, l2);
            collect(meta, l3);
        }
        // OCaml `Lam_pass_collect.collect` after #8348:
        // `Lbreak | Lcontinue -> ()`.
        Lambda::Lbreak | Lambda::Lcontinue => {}
        // lam_pass_collect.ml:147-150
        Lambda::Lassign(_, l) => collect(meta, l),
    }
}

/// Direct port of `Lam_pass_collect.collect_info`
/// (lam_pass_collect.ml:57-152). Mutates `meta.ident_tbl` with the kind /
/// arity info gathered from a single traversal of `lam`.
pub fn collect_info(meta: &mut LamStats, lam: &Lambda) {
    collect(meta, lam);
}
