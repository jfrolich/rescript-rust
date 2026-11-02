//! Direct port of `compiler/core/lam_pass_remove_alias.ml`.
//!
//! Field folding, optional-block unwrapping, cross-module function inlining
//! and boolean-constant folding using the `ident_tbl` populated by
//! `Lam_pass_collect.collect_info`.
//!
//! Every line below must trace to a specific line in OCaml. No invented
//! logic.

use crate::ident::Ident;
use crate::lambda::lam_analysis::{lfunction_can_be_inlined, ok_to_inline_fun_when_app};
use crate::lambda::lam_closure::is_closed_with_map;
use crate::lambda::lam_compat::{Comparison, FieldDbgInfo};
use crate::lambda::lam_compile_context::{BoxedNullable, IdKind, IdentTable, LamStats, RecFlag};
use crate::lambda::lam_constant::Constant;
use crate::lambda::lam_hit::hit_variable;
use crate::lambda::lam_primitive::Primitive;
use crate::lambda::lam_tag_info::TagInfo;
use crate::lambda::lam_util::field_flatten_get;
use crate::lambda::{Apply, Lambda, PrimInfo};
use crate::location::Location;

/// Rust counterpart to `Lam_compile_env.query_external_id_info` used by
/// `Lam_pass_remove_alias.simplify_alias` (lam_pass_remove_alias.ml:143-159).
pub type ExternalInlineResolver<'a> = dyn FnMut(&Ident, &str) -> Option<Lambda> + 'a;

/// Direct port of `Lam_pass_remove_alias.outcome` (lam_pass_remove_alias.ml:25).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Outcome {
    EvalFalse,
    EvalTrue,
    EvalUnknown,
}

/// Direct port of `Lam_pass_remove_alias.id_is_for_sure_true_in_boolean`
/// (lam_pass_remove_alias.ml:27-42).
fn id_is_for_sure_true_in_boolean(tbl: &IdentTable, id: &crate::ident::Ident) -> Outcome {
    match tbl.get(id) {
        Some(IdKind::NormalOptional(Lambda::Lconst(
            Constant::JsFalse | Constant::JsNull | Constant::JsUndefined { .. },
        ))) => Outcome::EvalFalse,
        Some(IdKind::Constant(Constant::JsTrue)) => Outcome::EvalTrue,
        Some(IdKind::Constant(Constant::Int { i, .. })) => {
            if *i == 0 {
                Outcome::EvalFalse
            } else {
                Outcome::EvalTrue
            }
        }
        Some(IdKind::Constant(
            Constant::JsFalse | Constant::JsNull | Constant::JsUndefined { .. },
        )) => Outcome::EvalFalse,
        _ => Outcome::EvalUnknown,
    }
}

/// Direct port of `Lam_pass_remove_alias.is_const_some` (lam_pass_remove_alias.ml:44-48).
///
/// Recognises constants whose runtime shape is `Some(_)` — either the
/// dedicated `Constant::Some` carrier or a record block tagged
/// [`TagInfo::Some`] / [`TagInfo::SomeNotNested`].
fn is_const_some(cst: &Constant) -> bool {
    match cst {
        Constant::Some(_) => true,
        Constant::Block { tag_info, .. } => {
            matches!(&**tag_info, TagInfo::Some | TagInfo::SomeNotNested)
        }
        _ => false,
    }
}

/// Port of `Lam.not_` (lam.ml:584-588). Folds `Pintcomp Cneq -> Pintcomp Ceq`
/// to keep the outcome shape clean; otherwise wraps the argument in `Pnot`.
fn lam_not(loc: Location, x: Lambda) -> Lambda {
    match x {
        Lambda::Lprim(__prim9)
            if matches!(
                __prim9.as_ref(),
                PrimInfo {
                    primitive: Primitive::Pintcomp(Comparison::Neq),
                    args: _,
                    loc: _l,
                }
            ) =>
        {
            let PrimInfo {
                primitive: Primitive::Pintcomp(Comparison::Neq),
                args,
                loc: l,
            } = *__prim9
            else {
                unreachable!()
            };
            Lambda::Lprim(Box::new(PrimInfo {
                primitive: Primitive::Pintcomp(Comparison::Eq),
                args,
                loc: l,
            }))
        }
        x => Lambda::prim(Primitive::Pnot, vec![x], loc),
    }
}

fn module_field_apply_target(lam: &Lambda) -> Option<(&Ident, &str)> {
    let Lambda::Lprim(__prim201) = lam else {
        return None;
    };
    let PrimInfo {
        primitive: Primitive::Pfield(_, FieldDbgInfo::Module { name }),
        args,
        ..
    } = __prim201.as_ref()
    else {
        return None;
    };
    let [Lambda::LglobalModule(id)] = args.as_slice() else {
        return None;
    };
    Some((id, name.as_str()))
}

fn external_inline_args_are_allowed(args: &[Lambda], ident_tbl: &IdentTable) -> bool {
    args.iter().all(|arg| match arg {
        Lambda::Lvar(param) => !matches!(ident_tbl.get(param), Some(IdKind::Parameter)),
        _ => true,
    })
}

/// Direct port of `Lam_pass_remove_alias.simplify_alias`
/// (lam_pass_remove_alias.ml:50-290).
///
/// The `meta` parameter is mutable so that the beta-reduction helpers called
/// from inside the pass can register `ImmutableBlock` / `Normal_optional`
/// entries for their fresh let-bound parameters (lam_beta_reduce.ml:66-73).
/// Without this, blocks introduced by beta-reduced functor arguments remain
/// opaque to subsequent `field_flatten_get` lookups.
/// How deep inlining may nest: simplifying an inlined body can inline the
/// functions it calls, and so on. Without a bound, a chain of small functions
/// that each call the previous one gets the whole chain inlined into every
/// function, which is quadratic in the length of the chain. Functions marked
/// `@inline` are always inlined.
pub(crate) const MAX_INLINE_DEPTH: usize = 4;

pub fn simplify_alias_with_external_inline_owned(
    meta: &mut LamStats,
    lam: Lambda,
    external_inline: &mut ExternalInlineResolver<'_>,
) -> Lambda {
    let export_idents = std::mem::take(&mut meta.export_idents);
    let id_gen = meta.id_gen.clone();
    let result = Simplifier {
        ident_tbl: &mut meta.ident_tbl,
        export_idents: &export_idents,
        id_gen: &id_gen,
        external_inline,
        inline_depth: 0,
    }
    .simpl_owned(lam);
    meta.export_idents = export_idents;
    result
}

struct Simplifier<'a> {
    ident_tbl: &'a mut crate::lambda::lam_compile_context::IdentTable,
    export_idents: &'a ahash::AHashSet<crate::ident::Ident>,
    /// Shared stamp counter used for `Ident.rename` during beta reduction.
    /// Mirrors OCaml's global `Ident.rename` counter so fresh stamps never
    /// collide across independent beta reductions of the same function.
    id_gen: &'a crate::context::IdGenerator,
    external_inline: &'a mut ExternalInlineResolver<'a>,
    inline_depth: usize,
}

use crate::lambda::lambda_traverse::Mapped;

impl<'a> Simplifier<'a> {
    /// Owned port of `Lam_pass_remove_alias.simplify_alias`
    /// (compiler/core/lam_pass_remove_alias.ml:50-290). Each branch mirrors
    /// the borrowed `simpl` walker below but consumes unchanged Rust nodes.
    fn simpl_owned(&mut self, lam: Lambda) -> Lambda {
        self.simpl_sharing(lam).0
    }

    fn simpl_list(&mut self, items: Vec<Lambda>) -> (Vec<Lambda>, bool) {
        let mut changed = false;
        let items = items
            .into_iter()
            .map(|item| {
                let (item, c) = self.simpl_sharing(item);
                changed |= c;
                item
            })
            .collect();
        (items, changed)
    }

    /// `Lam_pass_remove_alias.simplify_alias.simpl`
    /// (compiler/core/lam_pass_remove_alias.ml:49-247). OCaml hands back the
    /// physically same term when nothing was rewritten; the flag in the
    /// returned pair says whether the term is a new one, so callers rebuild
    /// through the folding smart constructors only when OCaml would.
    fn simpl_sharing(&mut self, lam: Lambda) -> Mapped {
        match lam {
            // Keep a JSX tag like `M.make` as it is: flattening it may give a
            // variable with a lowercase name, which JSX reads as an intrinsic
            // element (#7432).
            Lambda::Lprim(prim)
                if matches!(prim.primitive, Primitive::Pjsx(_))
                    && matches!(
                        prim.args.first(),
                        Some(Lambda::Lprim(first)) if matches!(first.primitive, Primitive::Pfield(_, _))
                    ) =>
            {
                let PrimInfo {
                    primitive,
                    mut args,
                    loc,
                } = *prim;
                let rest = args.split_off(1);
                let (rest, changed) = self.simpl_list(rest);
                args.extend(rest);
                if changed {
                    (Lambda::prim(primitive, args, loc), true)
                } else {
                    (
                        Lambda::Lprim(Box::new(PrimInfo {
                            primitive,
                            args,
                            loc,
                        })),
                        false,
                    )
                }
            }
            Lambda::Lprim(prim)
                if matches!(prim.primitive, Primitive::Pfield(_, _)) && prim.args.len() == 1 =>
            {
                let PrimInfo {
                    primitive,
                    mut args,
                    loc,
                } = *prim;
                let Primitive::Pfield(i, info) = primitive.clone() else {
                    unreachable!()
                };
                let (arg, arg_changed) =
                    self.simpl_sharing(args.pop().expect("checked one Pfield arg"));
                let rebuild = |arg: Lambda| {
                    if arg_changed {
                        (Lambda::prim(primitive, vec![arg], loc), true)
                    } else {
                        (
                            Lambda::Lprim(Box::new(PrimInfo {
                                primitive,
                                args: vec![arg],
                                loc,
                            })),
                            false,
                        )
                    }
                };
                match arg {
                    Lambda::Lvar(v) => {
                        let mut fallback_used = false;
                        let fallback_v = v;
                        let result = field_flatten_get(
                            || {
                                fallback_used = true;
                                rebuild(Lambda::Lvar(fallback_v)).0
                            },
                            &v,
                            i,
                            &info,
                            self.ident_tbl,
                        );
                        let changed = !fallback_used || arg_changed;
                        (result, changed)
                    }
                    other => rebuild(other),
                }
            }
            Lambda::Lprim(prim)
                if matches!(
                    prim.primitive,
                    Primitive::PvalFromOption | Primitive::PvalFromOptionNotNest
                ) && matches!(prim.args.as_slice(), [Lambda::Lvar(_)]) =>
            {
                let Lambda::Lvar(v) = &prim.args[0] else {
                    unreachable!()
                };
                match self.ident_tbl.get(v).cloned() {
                    Some(IdKind::OptionalBlock(l, _)) => (l, true),
                    _ if matches!(prim.primitive, Primitive::PvalFromOptionNotNest) => {
                        let PrimInfo { mut args, .. } = *prim;
                        (args.pop().expect("checked one optional arg"), true)
                    }
                    _ => (Lambda::Lprim(prim), false),
                }
            }
            Lambda::LifThenElse(cond, then_, else_)
                if matches!(
                    cond.as_ref(),
                    Lambda::Lprim(prim)
                        if matches!(prim.primitive, Primitive::PisNotNone)
                            && matches!(prim.args.as_slice(), [Lambda::Lvar(_)])
                ) =>
            {
                let id = match cond.as_ref() {
                    Lambda::Lprim(prim) => match &prim.args[0] {
                        Lambda::Lvar(id) => *id,
                        _ => unreachable!(),
                    },
                    _ => unreachable!(),
                };
                let optional_test = |primitive: Primitive, l: Lambda| {
                    lam_not(
                        Location::none(),
                        Lambda::prim(primitive, vec![l], Location::none()),
                    )
                };
                match self.ident_tbl.get(&id).cloned() {
                    Some(IdKind::Constant(c)) if is_const_some(&c) => {
                        (self.simpl_owned(*then_), true)
                    }
                    Some(
                        IdKind::ImmutableBlock(_)
                        | IdKind::MutableBlock(_)
                        | IdKind::NormalOptional(_),
                    ) => (self.simpl_owned(*then_), true),
                    Some(IdKind::OptionalBlock(l, nullable)) => {
                        let primitive = match nullable {
                            BoxedNullable::Null => Primitive::PisNull,
                            BoxedNullable::Undefined => Primitive::PisUndefined,
                            BoxedNullable::NullUndefined => Primitive::PisNullUndefined,
                        };
                        let then_ = self.simpl_owned(*then_);
                        let else_ = self.simpl_owned(*else_);
                        (Lambda::if_(optional_test(primitive, l), then_, else_), true)
                    }
                    _ => crate::lambda::lambda_traverse::shallow_map_sharing(
                        Lambda::LifThenElse(cond, then_, else_),
                        &mut |inner| self.simpl_sharing(inner),
                    ),
                }
            }
            Lambda::LifThenElse(cond, then_, else_) if matches!(cond.as_ref(), Lambda::Lvar(_)) => {
                let Lambda::Lvar(id) = cond.as_ref() else {
                    unreachable!()
                };
                match id_is_for_sure_true_in_boolean(self.ident_tbl, id) {
                    Outcome::EvalTrue => (self.simpl_owned(*then_), true),
                    Outcome::EvalFalse => (self.simpl_owned(*else_), true),
                    Outcome::EvalUnknown => crate::lambda::lambda_traverse::shallow_map_sharing(
                        Lambda::LifThenElse(cond, then_, else_),
                        &mut |inner| self.simpl_sharing(inner),
                    ),
                }
            }
            Lambda::Lapply(apply)
                if module_field_apply_target(apply.ap_func.as_ref()).is_some() =>
            {
                let Apply {
                    ap_func,
                    ap_args,
                    ap_info,
                } = *apply;
                let (module_id, field_name) = module_field_apply_target(ap_func.as_ref())
                    .expect("checked module field target");
                if let Some(Lambda::Lfunction(func)) = (self.external_inline)(module_id, field_name)
                    && func.params.len() == ap_args.len()
                    && external_inline_args_are_allowed(&ap_args, self.ident_tbl)
                    && lfunction_can_be_inlined(&func)
                {
                    let reduced =
                        crate::lambda::lam_beta_reduce::propagate_beta_reduce_with_meta_and_id_gen(
                            self.ident_tbl,
                            self.id_gen,
                            &func.params,
                            &func.body,
                            &ap_args,
                        );
                    return (self.simpl_owned(reduced), true);
                }
                let (func, c1) = self.simpl_sharing(*ap_func);
                let (args, c2) = self.simpl_list(ap_args);
                if c1 || c2 {
                    (Lambda::apply(func, args, ap_info), true)
                } else {
                    (
                        Lambda::Lapply(Box::new(Apply {
                            ap_func: Box::new(func),
                            ap_args: args,
                            ap_info,
                        })),
                        false,
                    )
                }
            }
            Lambda::Lapply(apply) if matches!(apply.ap_func.as_ref(), Lambda::Lvar(_)) => {
                let Apply {
                    ap_func,
                    ap_args,
                    ap_info,
                } = *apply;
                let Lambda::Lvar(v) = *ap_func else {
                    unreachable!()
                };
                let (ap_args, args_changed) = self.simpl_list(ap_args);
                let normal = |this: &mut Self, ap_args: Vec<Lambda>| {
                    let (func, func_changed) = this.simpl_sharing(Lambda::Lvar(v));
                    if func_changed || args_changed {
                        (Lambda::apply(func, ap_args, ap_info.clone()), true)
                    } else {
                        (
                            Lambda::Lapply(Box::new(Apply {
                                ap_func: Box::new(func),
                                ap_args,
                                ap_info: ap_info.clone(),
                            })),
                            false,
                        )
                    }
                };
                let func_info = match self.ident_tbl.get(&v) {
                    Some(IdKind::FunctionId {
                        lambda: Some((Lambda::Lfunction(func), rec_flag)),
                        ..
                    }) if lfunction_can_be_inlined(func) => Some((func.clone(), *rec_flag)),
                    _ => None,
                };
                let Some((func, rec_flag)) = func_info else {
                    return normal(self, ap_args);
                };
                if ap_args.len() != func.params.len() {
                    return normal(self, ap_args);
                }
                if func.attr.is_a_functor {
                    let reduced =
                        crate::lambda::lam_beta_reduce::propagate_beta_reduce_with_meta_and_id_gen(
                            self.ident_tbl,
                            self.id_gen,
                            &func.params,
                            &func.body,
                            &ap_args,
                        );
                    return (self.simpl_owned(reduced), true);
                }
                if !ok_to_inline_fun_when_app(&func, &ap_args) {
                    return normal(self, ap_args);
                }
                let (param_ok, param_map) =
                    is_closed_with_map(self.export_idents, &func.params, &func.body);
                let is_export_id = self.export_idents.contains(&v);
                if is_export_id && !param_ok {
                    return normal(self, ap_args);
                }
                match rec_flag {
                    RecFlag::Rec => (
                        crate::lambda::lam_beta_reduce::propagate_beta_reduce_with_map_and_meta_and_id_gen(
                            self.ident_tbl,
                            self.id_gen,
                            &param_map,
                            &func.params,
                            &func.body,
                            &ap_args,
                        ),
                        true,
                    ),
                    RecFlag::SelfRec => normal(self, ap_args),
                    RecFlag::NonRec => {
                        if ap_args.iter().any(|arg| hit_variable(&v, arg))
                            || (self.inline_depth >= MAX_INLINE_DEPTH
                                && func.attr.inline != crate::lambda::InlineAttribute::Always)
                        {
                            normal(self, ap_args)
                        } else {
                            let reduced =
                                crate::lambda::lam_beta_reduce::propagate_beta_reduce_with_map_and_meta_and_id_gen(
                                    self.ident_tbl,
                                    self.id_gen,
                                    &param_map,
                                    &func.params,
                                    &func.body,
                                    &ap_args,
                                );
                            self.inline_depth += 1;
                            let inlined = self.simpl_owned(reduced);
                            self.inline_depth -= 1;
                            (inlined, true)
                        }
                    }
                }
            }
            Lambda::Lapply(apply)
                if matches!(
                    apply.ap_func.as_ref(),
                    Lambda::Lfunction(func)
                        if func.params.len() == apply.ap_args.len() && lfunction_can_be_inlined(func)
                ) =>
            {
                let Apply {
                    ap_func, ap_args, ..
                } = *apply;
                let Lambda::Lfunction(func) = *ap_func else {
                    unreachable!()
                };
                let reduced =
                    crate::lambda::lam_beta_reduce::propagate_beta_reduce_with_meta_and_id_gen(
                        self.ident_tbl,
                        self.id_gen,
                        &func.params,
                        &func.body,
                        &ap_args,
                    );
                (self.simpl_owned(reduced), true)
            }
            Lambda::LstringSwitch(scrut, cases, default)
                if matches!(
                    scrut.as_ref(),
                    Lambda::Lvar(s) if matches!(self.ident_tbl.get(s), Some(IdKind::Constant(_)))
                ) =>
            {
                let Lambda::Lvar(s) = scrut.as_ref() else {
                    unreachable!()
                };
                let Some(IdKind::Constant(c)) = self.ident_tbl.get(s).cloned() else {
                    unreachable!()
                };
                // Switch on the constant the scrutinee is bound to.
                let cases = cases
                    .into_iter()
                    .map(|(k, v)| (k, self.simpl_owned(v)))
                    .collect();
                let default = default.map(|d| self.simpl_owned(*d));
                (
                    Lambda::string_switch(Lambda::const_(c), cases, default.map(Box::new)),
                    true,
                )
            }
            lam => crate::lambda::lambda_traverse::shallow_map_sharing(lam, &mut |inner| {
                self.simpl_sharing(inner)
            }),
        }
    }
}
