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
use crate::lambda::map_prim_args;
use crate::lambda::{Apply, Lambda, LambdaSwitch, PrimInfo};
use crate::lambda::{LFunction, map_box};
use crate::location::Location;

/// Rust counterpart to `Lam_compile_env.query_external_id_info` used by
/// `Lam_pass_remove_alias.simplify_alias` (lam_pass_remove_alias.ml:143-159).
pub type ExternalInlineResolver<'a> = dyn FnMut(&Ident, bool, &str) -> Option<Lambda> + 'a;

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

fn module_field_apply_target(lam: &Lambda) -> Option<(&Ident, bool, &str)> {
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
    let [Lambda::LglobalModule(id, dynamic_import)] = args.as_slice() else {
        return None;
    };
    Some((id, *dynamic_import, name.as_str()))
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
pub fn simplify_alias(meta: &mut LamStats, lam: &Lambda) -> Lambda {
    simplify_alias_owned(meta, lam.clone())
}

/// Owned form of [`simplify_alias`]. The behavioral branch order remains the
/// OCaml `Lam_pass_remove_alias.simplify_alias` order
/// (compiler/core/lam_pass_remove_alias.ml:50-290); only the Rust tree plumbing
/// changes so callers that already own the previous pass output do not clone it
/// before this pass.
pub fn simplify_alias_owned(meta: &mut LamStats, lam: Lambda) -> Lambda {
    let mut no_external_inline = |_: &Ident, _: bool, _: &str| None;
    simplify_alias_with_external_inline_owned(meta, lam, &mut no_external_inline)
}

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
        jsx_preserve: false,
        external_inline,
    }
    .simpl_owned(lam);
    meta.export_idents = export_idents;
    result
}

/// Same as [`simplify_alias`] but threads the JSX preservation flag — a port
/// of OCaml's `Js_config.jsx_preserve` global. The 7432-tagged Pjs_call arm
/// inside `simpl` only fires when this flag is true (lam_pass_remove_alias.ml:54-62).
pub fn simplify_alias_with_jsx(meta: &mut LamStats, lam: &Lambda, jsx_preserve: bool) -> Lambda {
    simplify_alias_with_jsx_owned(meta, lam.clone(), jsx_preserve)
}

/// Owned form of [`simplify_alias_with_jsx`], following
/// `compiler/core/lam_pass_remove_alias.ml:50-290` with the same JSX preserve
/// guard at `lam_pass_remove_alias.ml:54-62`.
pub fn simplify_alias_with_jsx_owned(
    meta: &mut LamStats,
    lam: Lambda,
    jsx_preserve: bool,
) -> Lambda {
    let mut no_external_inline = |_: &Ident, _: bool, _: &str| None;
    simplify_alias_with_jsx_and_external_inline_owned(
        meta,
        lam,
        jsx_preserve,
        &mut no_external_inline,
    )
}

pub fn simplify_alias_with_jsx_and_external_inline_owned(
    meta: &mut LamStats,
    lam: Lambda,
    jsx_preserve: bool,
    external_inline: &mut ExternalInlineResolver<'_>,
) -> Lambda {
    let export_idents = std::mem::take(&mut meta.export_idents);
    let id_gen = meta.id_gen.clone();
    let result = Simplifier {
        ident_tbl: &mut meta.ident_tbl,
        export_idents: &export_idents,
        id_gen: &id_gen,
        jsx_preserve,
        external_inline,
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
    jsx_preserve: bool,
    external_inline: &'a mut ExternalInlineResolver<'a>,
}

impl<'a> Simplifier<'a> {
    /// Owned port of `Lam_pass_remove_alias.simplify_alias`
    /// (compiler/core/lam_pass_remove_alias.ml:50-290). Each branch mirrors
    /// the borrowed `simpl` walker below but consumes unchanged Rust nodes.
    fn simpl_owned(&mut self, lam: Lambda) -> Lambda {
        match lam {
            // lam_pass_remove_alias.ml:53
            Lambda::Lvar(_) => lam,

            // lam_pass_remove_alias.ml:54-62 — JSX preserve guard for jsx/jsxs.
            Lambda::Lprim(__prim8)
                if matches!(__prim8.as_ref(), PrimInfo {
                    primitive,
                    args,
                    loc,
                } if self.jsx_preserve
                    && matches!(
                        &primitive,
                        Primitive::PjsCall { prim_name, .. }
                            if prim_name == "jsx" || prim_name == "jsxs"
                    )
                    && matches!(
                        args.first(),
                        Some(Lambda::Lprim(first)) if matches!(first.primitive, Primitive::Pfield(_, _))
                    )) =>
            {
                let PrimInfo {
                    primitive,
                    args,
                    loc,
                } = *__prim8;

                let mut new_args = Vec::with_capacity(args.len());
                let mut iter = args.into_iter();
                if let Some(first) = iter.next() {
                    new_args.push(first);
                }
                new_args.extend(iter.map(|arg| self.simpl_owned(arg)));
                Lambda::prim(primitive, new_args, loc)
            }

            // lam_pass_remove_alias.ml:63-71 — Pfield [arg] with a known Lvar.
            Lambda::Lprim(__prim7)
                if matches!(__prim7.as_ref(), PrimInfo {
                primitive: Primitive::Pfield(i, info),
                args,
                loc,
            } if args.len() == 1) =>
            {
                let PrimInfo {
                    primitive: Primitive::Pfield(i, info),
                    mut args,
                    loc,
                } = *__prim7
                else {
                    unreachable!()
                };

                let simplified = self.simpl_owned(args.pop().expect("checked one Pfield arg"));
                match simplified {
                    Lambda::Lvar(v) => {
                        let fallback_v = v.clone();
                        let fallback_info = info.clone();
                        field_flatten_get(
                            move || {
                                Lambda::prim(
                                    Primitive::Pfield(i, fallback_info),
                                    vec![Lambda::Lvar(fallback_v)],
                                    loc,
                                )
                            },
                            &v,
                            i,
                            &info,
                            self.ident_tbl,
                        )
                    }
                    other => Lambda::prim(Primitive::Pfield(i, info), vec![other], loc),
                }
            }

            // lam_pass_remove_alias.ml:72-79 — unwrap known optional blocks.
            Lambda::Lprim(__prim6)
                if matches!(__prim6.as_ref(), PrimInfo {
                primitive: p @ (Primitive::PvalFromOption | Primitive::PvalFromOptionNotNest),
                args,
                loc,
            } if matches!(args.as_slice(), [Lambda::Lvar(_)])) =>
            {
                let PrimInfo {
                    primitive: p @ (Primitive::PvalFromOption | Primitive::PvalFromOptionNotNest),
                    mut args,
                    loc,
                } = *__prim6
                else {
                    unreachable!()
                };

                let Lambda::Lvar(v) = args.pop().expect("checked one optional arg") else {
                    unreachable!()
                };
                match self.ident_tbl.get(&v).cloned() {
                    Some(IdKind::OptionalBlock(l, _)) => l,
                    _ if matches!(p, Primitive::PvalFromOptionNotNest) => Lambda::Lvar(v),
                    _ => Lambda::Lprim(Box::new(PrimInfo {
                        primitive: p,
                        args: vec![Lambda::Lvar(v)],
                        loc,
                    })),
                }
            }

            // lam_pass_remove_alias.ml:80
            Lambda::LglobalModule(_, _) => lam,

            // lam_pass_remove_alias.ml:81-82 — fallback Lprim.
            Lambda::Lprim(info) => map_prim_args(info, |arg| self.simpl_owned(arg)),

            // lam_pass_remove_alias.ml:83-117 — Lifthenelse special cases,
            // followed by the generic boolean simplification fallback.
            Lambda::LifThenElse(cond, then_, else_) => match *cond {
                Lambda::Lprim(__prim4)
                    if matches!(__prim4.as_ref(), PrimInfo {
                    primitive: Primitive::PisNotNone,
                    args,
                    loc,
                } if matches!(args.as_slice(), [Lambda::Lvar(_)])) =>
                {
                    let PrimInfo {
                        primitive: Primitive::PisNotNone,
                        mut args,
                        loc,
                    } = *__prim4
                    else {
                        unreachable!()
                    };

                    let Lambda::Lvar(id) = args.pop().expect("checked one Pis_not_none arg") else {
                        unreachable!()
                    };
                    match self.ident_tbl.get(&id).cloned() {
                        Some(IdKind::Constant(c)) if is_const_some(&c) => self.simpl_owned(*then_),
                        Some(
                            IdKind::ImmutableBlock(_)
                            | IdKind::MutableBlock(_)
                            | IdKind::NormalOptional(_),
                        ) => self.simpl_owned(*then_),
                        Some(IdKind::OptionalBlock(l, BoxedNullable::Null)) => Lambda::if_(
                            lam_not(
                                Location::none(),
                                Lambda::prim(Primitive::PisNull, vec![l], Location::none()),
                            ),
                            self.simpl_owned(*then_),
                            self.simpl_owned(*else_),
                        ),
                        Some(IdKind::OptionalBlock(l, BoxedNullable::Undefined)) => Lambda::if_(
                            lam_not(
                                Location::none(),
                                Lambda::prim(Primitive::PisUndefined, vec![l], Location::none()),
                            ),
                            self.simpl_owned(*then_),
                            self.simpl_owned(*else_),
                        ),
                        Some(IdKind::OptionalBlock(l, BoxedNullable::NullUndefined)) => {
                            Lambda::if_(
                                lam_not(
                                    Location::none(),
                                    Lambda::prim(
                                        Primitive::PisNullUndefined,
                                        vec![l],
                                        Location::none(),
                                    ),
                                ),
                                self.simpl_owned(*then_),
                                self.simpl_owned(*else_),
                            )
                        }
                        _ => Lambda::if_(
                            Lambda::Lprim(Box::new(PrimInfo {
                                primitive: Primitive::PisNotNone,
                                args: vec![Lambda::Lvar(id)],
                                loc,
                            })),
                            self.simpl_owned(*then_),
                            self.simpl_owned(*else_),
                        ),
                    }
                }
                Lambda::Lvar(id) => match id_is_for_sure_true_in_boolean(self.ident_tbl, &id) {
                    Outcome::EvalTrue => self.simpl_owned(*then_),
                    Outcome::EvalFalse => self.simpl_owned(*else_),
                    Outcome::EvalUnknown => Lambda::if_(
                        self.simpl_owned(Lambda::Lvar(id)),
                        self.simpl_owned(*then_),
                        self.simpl_owned(*else_),
                    ),
                },
                other => Lambda::if_(
                    self.simpl_owned(other),
                    self.simpl_owned(*then_),
                    self.simpl_owned(*else_),
                ),
            },

            // lam_pass_remove_alias.ml:118
            Lambda::Lconst(_) => lam,

            // lam_pass_remove_alias.ml:119
            Lambda::Llet(kind, v, l1, l2) => Lambda::Llet(
                kind,
                v,
                map_box(l1, |inner| self.simpl_owned(inner)),
                map_box(l2, |inner| self.simpl_owned(inner)),
            ),

            // lam_pass_remove_alias.ml:120-122
            Lambda::Lletrec(bindings, body) => {
                let bindings = bindings
                    .into_iter()
                    .map(|(id, expr)| (id, self.simpl_owned(expr)))
                    .collect();
                Lambda::Lletrec(bindings, map_box(body, |inner| self.simpl_owned(inner)))
            }

            // lam_pass_remove_alias.ml:131-246 — cross-module, local, and
            // direct application inlining. The cross-module arm runs before
            // local/direct application just like OCaml, and uses plain
            // `propagate_beta_reduce` (lam_pass_remove_alias.ml:159), not
            // the later with-map reducer from lam_compile.ml:289.
            Lambda::Lapply(apply) => {
                let Apply {
                    ap_func,
                    ap_args,
                    ap_info,
                    ap_transformed_jsx,
                } = *apply;

                if let Some((module_id, dynamic_import, field_name)) =
                    module_field_apply_target(ap_func.as_ref())
                    && let Some(Lambda::Lfunction(func)) =
                        (self.external_inline)(module_id, dynamic_import, field_name)
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
                    return self.simpl_owned(reduced);
                }

                match *ap_func {
                    Lambda::Lvar(v) => {
                        let ap_args: Vec<Lambda> = ap_args
                            .into_iter()
                            .map(|arg| self.simpl_owned(arg))
                            .collect();

                        let func_info = match self.ident_tbl.get(&v) {
                            Some(IdKind::FunctionId {
                                lambda: Some((Lambda::Lfunction(func), rec_flag)),
                                ..
                            }) if lfunction_can_be_inlined(func)
                                && ap_args.len() == func.params.len() =>
                            {
                                Some((func.clone(), *rec_flag))
                            }
                            _ => None,
                        };

                        match func_info {
                            Some((func, _rec_flag)) if func.attr.is_a_functor => {
                                // lam_pass_remove_alias.ml:188-197.
                                let reduced =
                                    crate::lambda::lam_beta_reduce::propagate_beta_reduce_with_meta_and_id_gen(
                                        self.ident_tbl,
                                        self.id_gen,
                                        &func.params,
                                        &func.body,
                                        &ap_args,
                                    );
                                self.simpl_owned(reduced)
                            }
                            Some((func, rec_flag))
                                if ok_to_inline_fun_when_app(&func, &ap_args) =>
                            {
                                // lam_pass_remove_alias.ml:198-231.
                                let (param_ok, param_map) = is_closed_with_map(
                                    self.export_idents,
                                    &func.params,
                                    &func.body,
                                );
                                let is_export_id = self.export_idents.contains(&v);
                                let allow = match (is_export_id, param_ok) {
                                    (false, _) => true,
                                    (true, true) => true,
                                    (true, false) => false,
                                };
                                if allow {
                                    match rec_flag {
                                        RecFlag::Rec => {
                                            return crate::lambda::lam_beta_reduce::propagate_beta_reduce_with_map_and_meta_and_id_gen(
                                                self.ident_tbl,
                                                self.id_gen,
                                                &param_map,
                                                &func.params,
                                                &func.body,
                                                &ap_args,
                                            );
                                        }
                                        RecFlag::SelfRec => {}
                                        RecFlag::NonRec => {
                                            if !ap_args.iter().any(|arg| hit_variable(&v, arg)) {
                                                let reduced =
                                                    crate::lambda::lam_beta_reduce::propagate_beta_reduce_with_map_and_meta_and_id_gen(
                                                        self.ident_tbl,
                                                        self.id_gen,
                                                        &param_map,
                                                        &func.params,
                                                        &func.body,
                                                        &ap_args,
                                                    );
                                                return self.simpl_owned(reduced);
                                            }
                                        }
                                    }
                                }
                                Lambda::apply(
                                    self.simpl_owned(Lambda::Lvar(v)),
                                    ap_args,
                                    ap_info,
                                    ap_transformed_jsx,
                                )
                            }
                            _ => Lambda::apply(
                                self.simpl_owned(Lambda::Lvar(v)),
                                ap_args,
                                ap_info,
                                ap_transformed_jsx,
                            ),
                        }
                    }
                    Lambda::Lfunction(func) => {
                        let args: Vec<Lambda> = ap_args
                            .into_iter()
                            .map(|arg| self.simpl_owned(arg))
                            .collect();
                        if args.len() == func.params.len() && lfunction_can_be_inlined(&func) {
                            // lam_pass_remove_alias.ml:233-237.
                            let reduced =
                                crate::lambda::lam_beta_reduce::propagate_beta_reduce_with_meta_and_id_gen(
                                    self.ident_tbl,
                                    self.id_gen,
                                    &func.params,
                                    &func.body,
                                    &args,
                                );
                            self.simpl_owned(reduced)
                        } else {
                            Lambda::apply(
                                self.simpl_owned(Lambda::Lfunction(func)),
                                args,
                                ap_info,
                                ap_transformed_jsx,
                            )
                        }
                    }
                    func => Lambda::apply(
                        self.simpl_owned(func),
                        ap_args
                            .into_iter()
                            .map(|arg| self.simpl_owned(arg))
                            .collect(),
                        ap_info,
                        ap_transformed_jsx,
                    ),
                }
            }

            // lam_pass_remove_alias.ml:247-248
            Lambda::Lfunction(func) => Lambda::Lfunction(Box::new(LFunction {
                arity: func.arity,
                params: func.params,
                body: map_box(func.body, |inner| self.simpl_owned(inner)),
                attr: func.attr,
            })),

            // lam_pass_remove_alias.ml:249-267
            Lambda::Lswitch(scrut, switch) => Lambda::switch(
                self.simpl_owned(*scrut),
                LambdaSwitch {
                    sw_consts_full: switch.sw_consts_full,
                    sw_consts: switch
                        .sw_consts
                        .into_iter()
                        .map(|(k, expr)| (k, self.simpl_owned(expr)))
                        .collect(),
                    sw_blocks_full: switch.sw_blocks_full,
                    sw_blocks: switch
                        .sw_blocks
                        .into_iter()
                        .map(|(k, expr)| (k, self.simpl_owned(expr)))
                        .collect(),
                    sw_failaction: switch
                        .sw_failaction
                        .map(|expr| map_box(expr, |inner| self.simpl_owned(inner))),
                    sw_dispatch: switch.sw_dispatch,
                },
            ),

            // lam_pass_remove_alias.ml:268-277
            Lambda::LstringSwitch(scrut, sw, d) => {
                let scrut = match *scrut {
                    Lambda::Lvar(s) => match self.ident_tbl.get(&s).cloned() {
                        Some(IdKind::Constant(c)) => Lambda::const_(c),
                        _ => self.simpl_owned(Lambda::Lvar(s)),
                    },
                    other => self.simpl_owned(other),
                };
                Lambda::string_switch(
                    scrut,
                    sw.into_iter()
                        .map(|(k, v)| (k, self.simpl_owned(v)))
                        .collect(),
                    d.map(|d| map_box(d, |inner| self.simpl_owned(inner))),
                )
            }

            // lam_pass_remove_alias.ml:278
            Lambda::LstaticRaise(i, ls) => {
                Lambda::static_raise(i, ls.into_iter().map(|arg| self.simpl_owned(arg)).collect())
            }

            // lam_pass_remove_alias.ml:279
            Lambda::LstaticCatch(l1, ids, l2) => Lambda::LstaticCatch(
                map_box(l1, |inner| self.simpl_owned(inner)),
                (ids.0, ids.1),
                map_box(l2, |inner| self.simpl_owned(inner)),
            ),

            // lam_pass_remove_alias.ml:280
            Lambda::LtryWith(l1, v, l2) => Lambda::LtryWith(
                map_box(l1, |inner| self.simpl_owned(inner)),
                v,
                map_box(l2, |inner| self.simpl_owned(inner)),
            ),

            // lam_pass_remove_alias.ml:281
            Lambda::Lsequence(l1, l2) => Lambda::seq(self.simpl_owned(*l1), self.simpl_owned(*l2)),

            // lam_pass_remove_alias.ml:282
            Lambda::Lwhile(l1, l2) => Lambda::Lwhile(
                map_box(l1, |inner| self.simpl_owned(inner)),
                map_box(l2, |inner| self.simpl_owned(inner)),
            ),

            // lam_pass_remove_alias.ml:283-284
            Lambda::Lfor(var, l1, l2, dir, l3) => Lambda::Lfor(
                var,
                map_box(l1, |inner| self.simpl_owned(inner)),
                map_box(l2, |inner| self.simpl_owned(inner)),
                dir,
                map_box(l3, |inner| self.simpl_owned(inner)),
            ),

            // lam_pass_remove_alias.ml after #7887.
            Lambda::Lfor_of(var, l1, l2) => Lambda::Lfor_of(
                var,
                map_box(l1, |inner| self.simpl_owned(inner)),
                map_box(l2, |inner| self.simpl_owned(inner)),
            ),
            Lambda::Lfor_await_of(var, l1, l2) => Lambda::Lfor_await_of(
                var,
                map_box(l1, |inner| self.simpl_owned(inner)),
                map_box(l2, |inner| self.simpl_owned(inner)),
            ),

            // OCaml `Lam_pass_remove_alias.simplify_alias` after #8348.
            Lambda::Lbreak => Lambda::break_(),
            Lambda::Lcontinue => Lambda::continue_(),

            // lam_pass_remove_alias.ml:285-288
            Lambda::Lassign(v, l) => {
                Lambda::Lassign(v, map_box(l, |inner| self.simpl_owned(inner)))
            }
        }
    }

    fn simpl(&mut self, lam: &Lambda) -> Lambda {
        match lam {
            // lam_pass_remove_alias.ml:53
            Lambda::Lvar(_) => lam.clone(),

            // lam_pass_remove_alias.ml:54-62 — JSX preserve guard for jsx/jsxs
            // calls. The first argument (the field-bearing Pfield) is kept
            // verbatim, the rest are recursively simplified.
            Lambda::Lprim(__prim3)
                if matches!(__prim3.as_ref(), PrimInfo {
                    primitive: primitive @ Primitive::PjsCall { .. },
                    args,
                    loc,
                } if self.jsx_preserve
                    && matches!(
                        primitive,
                        Primitive::PjsCall { prim_name, .. }
                            if prim_name == "jsx" || prim_name == "jsxs"
                    )
                    && matches!(
                        args.first(),
                        Some(Lambda::Lprim(first)) if matches!(first.primitive, Primitive::Pfield(_, _))
                    )) =>
            {
                let PrimInfo {
                    primitive: primitive @ Primitive::PjsCall { .. },
                    args,
                    loc,
                } = __prim3.as_ref()
                else {
                    unreachable!()
                };

                let mut new_args: Vec<Lambda> = Vec::with_capacity(args.len());
                let mut iter = args.iter();
                if let Some(first) = iter.next() {
                    new_args.push(first.clone());
                }
                for arg in iter {
                    new_args.push(self.simpl(arg));
                }
                Lambda::prim(primitive.clone(), new_args, loc.clone())
            }

            // lam_pass_remove_alias.ml:63-71 — `Pfield(i, info) [arg]` where
            // arg simplifies to `Lvar v`: use `field_flatten_get` to lift the
            // known slot out of the binding.
            Lambda::Lprim(__prim2)
                if matches!(__prim2.as_ref(), PrimInfo {
                primitive: primitive @ Primitive::Pfield(i, info),
                args,
                loc,
            } if args.len() == 1) =>
            {
                let PrimInfo {
                    primitive: primitive @ Primitive::Pfield(i, info),
                    args,
                    loc,
                } = __prim2.as_ref()
                else {
                    unreachable!()
                };

                let simplified = self.simpl(&args[0]);
                match simplified {
                    Lambda::Lvar(ref v) => {
                        let l_clone = simplified.clone();
                        let primitive_clone = primitive.clone();
                        let loc_clone = loc.clone();
                        field_flatten_get(
                            move || Lambda::prim(primitive_clone, vec![l_clone], loc_clone),
                            v,
                            *i,
                            info,
                            self.ident_tbl,
                        )
                    }
                    other => Lambda::prim(primitive.clone(), vec![other], loc.clone()),
                }
            }

            // lam_pass_remove_alias.ml:72-79 — `Pval_from_option(_not_nest)
            // [Lvar v]` where v is known to be an OptionalBlock: unwrap to
            // the inner lambda. The `_not_nest` variant additionally folds
            // away the outer wrapper even if the binding is unknown.
            Lambda::Lprim(__prim1)
                if matches!(__prim1.as_ref(), PrimInfo {
                primitive: p @ (Primitive::PvalFromOption | Primitive::PvalFromOptionNotNest),
                args,
                loc: _,
            } if matches!(args.as_slice(), [Lambda::Lvar(_)])) =>
            {
                let PrimInfo {
                    primitive: p @ (Primitive::PvalFromOption | Primitive::PvalFromOptionNotNest),
                    args,
                    loc: _,
                } = __prim1.as_ref()
                else {
                    unreachable!()
                };

                let Lambda::Lvar(v) = &args[0] else {
                    unreachable!()
                };
                let kind = self.ident_tbl.get(v).cloned();
                match kind {
                    Some(IdKind::OptionalBlock(l, _)) => l,
                    _ => {
                        if matches!(p, Primitive::PvalFromOptionNotNest) {
                            args[0].clone()
                        } else {
                            lam.clone()
                        }
                    }
                }
            }

            // lam_pass_remove_alias.ml:80
            Lambda::LglobalModule(_, _) => lam.clone(),

            // lam_pass_remove_alias.ml:81-82 — fallback Lprim: recurse args.
            Lambda::Lprim(__prim0) => {
                let PrimInfo {
                    primitive,
                    args,
                    loc,
                } = __prim0.as_ref();
                Lambda::prim(
                    primitive.clone(),
                    args.iter().map(|a| self.simpl(a)).collect(),
                    loc.clone(),
                )
            }

            // lam_pass_remove_alias.ml:83-104 — Lifthenelse with a
            // `Pis_not_none [Lvar id]` discriminator: consult `meta.ident_tbl`
            // to fold the test or rewrite it into an explicit null/undefined
            // probe.
            Lambda::LifThenElse(cond, then_, else_)
                if matches!(
                                    cond.as_ref(),
                                    Lambda::Lprim(__prim100) if matches!(__prim100.as_ref(), PrimInfo {
                                        primitive: Primitive::PisNotNone,
                                        args,
                                        ..
                                    } if matches!(args.as_slice(), [Lambda::Lvar(_)]))
                ) =>
            {
                let Lambda::Lprim(__prim200) = cond.as_ref() else {
                    unreachable!()
                };
                let PrimInfo {
                    args: cond_args, ..
                } = __prim200.as_ref();
                let Lambda::Lvar(id) = &cond_args[0] else {
                    unreachable!()
                };
                let kind = self.ident_tbl.get(id).cloned();
                match kind {
                    Some(IdKind::Constant(c)) if is_const_some(&c) => self.simpl(then_),
                    Some(
                        IdKind::ImmutableBlock(_)
                        | IdKind::MutableBlock(_)
                        | IdKind::NormalOptional(_),
                    ) => self.simpl(then_),
                    Some(IdKind::OptionalBlock(l, BoxedNullable::Null)) => Lambda::if_(
                        lam_not(
                            Location::none(),
                            Lambda::prim(Primitive::PisNull, vec![l.clone()], Location::none()),
                        ),
                        self.simpl(then_),
                        self.simpl(else_),
                    ),
                    Some(IdKind::OptionalBlock(l, BoxedNullable::Undefined)) => Lambda::if_(
                        lam_not(
                            Location::none(),
                            Lambda::prim(
                                Primitive::PisUndefined,
                                vec![l.clone()],
                                Location::none(),
                            ),
                        ),
                        self.simpl(then_),
                        self.simpl(else_),
                    ),
                    Some(IdKind::OptionalBlock(l, BoxedNullable::NullUndefined)) => Lambda::if_(
                        lam_not(
                            Location::none(),
                            Lambda::prim(
                                Primitive::PisNullUndefined,
                                vec![l.clone()],
                                Location::none(),
                            ),
                        ),
                        self.simpl(then_),
                        self.simpl(else_),
                    ),
                    _ => Lambda::if_(cond.as_ref().clone(), self.simpl(then_), self.simpl(else_)),
                }
            }

            // lam_pass_remove_alias.ml:105-117 — Lifthenelse fallback.
            // Lvar conditions consult `id_is_for_sure_true_in_boolean`; other
            // conditions are recursively simplified.
            Lambda::LifThenElse(cond, then_, else_) => match cond.as_ref() {
                Lambda::Lvar(id) => {
                    let outcome = id_is_for_sure_true_in_boolean(self.ident_tbl, id);
                    match outcome {
                        Outcome::EvalTrue => self.simpl(then_),
                        Outcome::EvalFalse => self.simpl(else_),
                        Outcome::EvalUnknown => {
                            Lambda::if_(self.simpl(cond), self.simpl(then_), self.simpl(else_))
                        }
                    }
                }
                _ => Lambda::if_(self.simpl(cond), self.simpl(then_), self.simpl(else_)),
            },

            // lam_pass_remove_alias.ml:118
            Lambda::Lconst(_) => lam.clone(),

            // lam_pass_remove_alias.ml:119
            Lambda::Llet(kind, v, l1, l2) => {
                Lambda::let_(*kind, v.clone(), self.simpl(l1), self.simpl(l2))
            }

            // lam_pass_remove_alias.ml:120-122
            Lambda::Lletrec(bindings, body) => {
                let bindings = bindings
                    .iter()
                    .map(|(id, e)| (id.clone(), self.simpl(e)))
                    .collect();
                Lambda::letrec(bindings, self.simpl(body))
            }

            // lam_pass_remove_alias.ml:131-162 — cross-module fn inlining via
            // `Lam_compile_env.query_external_id_info`. This pass uses plain
            // `propagate_beta_reduce` at line 159, so complex arguments are
            // let-bound here before the later compile-time with-map inliner
            // (lam_compile.ml:289) ever sees the call.
            Lambda::Lapply(apply)
                if module_field_apply_target(apply.ap_func.as_ref()).is_some() =>
            {
                let (module_id, dynamic_import, field_name) =
                    module_field_apply_target(apply.ap_func.as_ref()).expect("guarded above");
                if let Some(Lambda::Lfunction(func)) =
                    (self.external_inline)(module_id, dynamic_import, field_name)
                    && func.params.len() == apply.ap_args.len()
                    && external_inline_args_are_allowed(&apply.ap_args, self.ident_tbl)
                    && lfunction_can_be_inlined(&func)
                {
                    let reduced =
                        crate::lambda::lam_beta_reduce::propagate_beta_reduce_with_meta_and_id_gen(
                            self.ident_tbl,
                            self.id_gen,
                            &func.params,
                            &func.body,
                            &apply.ap_args,
                        );
                    self.simpl(&reduced)
                } else {
                    Lambda::apply(
                        self.simpl(apply.ap_func.as_ref()),
                        apply.ap_args.iter().map(|a| self.simpl(a)).collect(),
                        apply.ap_info.clone(),
                        apply.ap_transformed_jsx,
                    )
                }
            }

            // lam_pass_remove_alias.ml:169-232 — local Lvar callee inlining.
            Lambda::Lapply(apply) if matches!(apply.ap_func.as_ref(), Lambda::Lvar(_)) => {
                let Lambda::Lvar(v) = apply.ap_func.as_ref() else {
                    unreachable!()
                };
                let ap_args: Vec<Lambda> = apply.ap_args.iter().map(|a| self.simpl(a)).collect();

                // Clone the FunctionId payload to release the immutable
                // borrow on `self.ident_tbl`; the beta-reduction helpers below
                // mutate it to register fresh let-bindings, and the `self.simpl`
                // recursion that follows needs `&mut self` in turn.
                let func_info = match self.ident_tbl.get(v) {
                    Some(IdKind::FunctionId {
                        lambda: Some((Lambda::Lfunction(func), rec_flag)),
                        ..
                    }) if lfunction_can_be_inlined(func) && ap_args.len() == func.params.len() => {
                        Some((func.clone(), *rec_flag))
                    }
                    _ => None,
                };

                let normal = |simplifier: &mut Self| {
                    Lambda::apply(
                        simplifier.simpl(apply.ap_func.as_ref()),
                        ap_args.clone(),
                        apply.ap_info.clone(),
                        apply.ap_transformed_jsx,
                    )
                };

                match func_info {
                    Some((func, _rec_flag)) if func.attr.is_a_functor => {
                        // lam_pass_remove_alias.ml:188-197 — functor:
                        // always beta-reduce (callers are expected to
                        // be at most one site).
                        let reduced = crate::lambda::lam_beta_reduce::propagate_beta_reduce_with_meta_and_id_gen(
                            self.ident_tbl,
                            self.id_gen,
                            &func.params,
                            &func.body,
                            &ap_args,
                        );
                        self.simpl(&reduced)
                    }
                    Some((func, rec_flag)) if ok_to_inline_fun_when_app(&func, &ap_args) => {
                        // lam_pass_remove_alias.ml:198-231 —
                        // size-bounded inlining.
                        let (param_ok, param_map) =
                            is_closed_with_map(self.export_idents, &func.params, &func.body);
                        let is_export_id = self.export_idents.contains(v);
                        let allow = match (is_export_id, param_ok) {
                            (false, _) => true,
                            (true, true) => true,
                            (true, false) => false,
                        };
                        if allow {
                            match rec_flag {
                                RecFlag::Rec => {
                                    crate::lambda::lam_beta_reduce::propagate_beta_reduce_with_map_and_meta_and_id_gen(
                                        self.ident_tbl,
                                        self.id_gen,
                                        &param_map,
                                        &func.params,
                                        &func.body,
                                        &ap_args,
                                    )
                                }
                                RecFlag::SelfRec => normal(self),
                                RecFlag::NonRec => {
                                    // lam_pass_remove_alias.ml:220-228:
                                    // avoid non-termination such as
                                    // `g(g)` by checking whether v
                                    // appears in the args.
                                    if ap_args.iter().any(|lam| hit_variable(v, lam)) {
                                        normal(self)
                                    } else {
                                        let reduced = crate::lambda::lam_beta_reduce::propagate_beta_reduce_with_map_and_meta_and_id_gen(
                                            self.ident_tbl,
                                            self.id_gen,
                                            &param_map,
                                            &func.params,
                                            &func.body,
                                            &ap_args,
                                        );
                                        self.simpl(&reduced)
                                    }
                                }
                            }
                        } else {
                            normal(self)
                        }
                    }
                    _ => normal(self),
                }
            }

            // lam_pass_remove_alias.ml:233-237 — direct
            // `Lapply(Lfunction _, args)` with same-arity, inlinable body:
            // beta-reduce in place.
            Lambda::Lapply(apply) if matches!(apply.ap_func.as_ref(), Lambda::Lfunction(_)) => {
                // Clone the function payload up front: the mutable meta
                // borrow used by `propagate_beta_reduce_with_meta` is
                // incompatible with the `apply.ap_func` / `apply.ap_args`
                // borrows we need to carry across the call.
                let func_clone = match apply.ap_func.as_ref() {
                    Lambda::Lfunction(func) => func.clone(),
                    _ => unreachable!(),
                };
                let args: Vec<Lambda> = apply.ap_args.iter().map(|a| self.simpl(a)).collect();
                if args.len() == func_clone.params.len() && lfunction_can_be_inlined(&func_clone) {
                    let reduced =
                        crate::lambda::lam_beta_reduce::propagate_beta_reduce_with_meta_and_id_gen(
                            self.ident_tbl,
                            self.id_gen,
                            &func_clone.params,
                            &func_clone.body,
                            &args,
                        );
                    self.simpl(&reduced)
                } else {
                    Lambda::apply(
                        self.simpl(apply.ap_func.as_ref()),
                        args,
                        apply.ap_info.clone(),
                        apply.ap_transformed_jsx,
                    )
                }
            }

            // lam_pass_remove_alias.ml:245-246 — fallback Lapply.
            Lambda::Lapply(apply) => Lambda::apply(
                self.simpl(apply.ap_func.as_ref()),
                apply.ap_args.iter().map(|a| self.simpl(a)).collect(),
                apply.ap_info.clone(),
                apply.ap_transformed_jsx,
            ),

            // lam_pass_remove_alias.ml:247-248
            Lambda::Lfunction(func) => Lambda::function_(
                func.arity,
                func.params.clone(),
                self.simpl(&func.body),
                func.attr.clone(),
            ),

            // lam_pass_remove_alias.ml:249-267
            Lambda::Lswitch(scrut, switch) => Lambda::switch(
                self.simpl(scrut),
                LambdaSwitch {
                    sw_consts_full: switch.sw_consts_full,
                    sw_consts: switch
                        .sw_consts
                        .iter()
                        .map(|(k, l)| (k.clone(), self.simpl(l)))
                        .collect(),
                    sw_blocks_full: switch.sw_blocks_full,
                    sw_blocks: switch
                        .sw_blocks
                        .iter()
                        .map(|(k, l)| (k.clone(), self.simpl(l)))
                        .collect(),
                    sw_failaction: switch
                        .sw_failaction
                        .as_ref()
                        .map(|f| Box::new(self.simpl(f))),
                    sw_dispatch: switch.sw_dispatch.clone(),
                },
            ),

            // lam_pass_remove_alias.ml:268-277 — Lstringswitch with a Lvar
            // scrutinee: try const-folding via the ident_tbl, then recurse.
            Lambda::LstringSwitch(scrut, sw, d) => {
                let folded = match scrut.as_ref() {
                    Lambda::Lvar(s) => match self.ident_tbl.get(s).cloned() {
                        Some(IdKind::Constant(c)) => Some(Lambda::const_(c)),
                        _ => None,
                    },
                    _ => None,
                };
                let scrut = match folded {
                    Some(c) => c,
                    None => self.simpl(scrut),
                };
                Lambda::string_switch(
                    scrut,
                    sw.iter().map(|(k, v)| (k.clone(), self.simpl(v))).collect(),
                    d.as_ref().map(|d| Box::new(self.simpl(d))),
                )
            }

            // lam_pass_remove_alias.ml:278
            Lambda::LstaticRaise(i, ls) => {
                Lambda::static_raise(*i, ls.iter().map(|l| self.simpl(l)).collect())
            }

            // lam_pass_remove_alias.ml:279
            Lambda::LstaticCatch(l1, ids, l2) => {
                Lambda::static_catch(self.simpl(l1), ids.0, ids.1.clone(), self.simpl(l2))
            }

            // lam_pass_remove_alias.ml:280
            Lambda::LtryWith(l1, v, l2) => Lambda::try_(self.simpl(l1), v.clone(), self.simpl(l2)),

            // lam_pass_remove_alias.ml:281
            Lambda::Lsequence(l1, l2) => Lambda::seq(self.simpl(l1), self.simpl(l2)),

            // lam_pass_remove_alias.ml:282
            Lambda::Lwhile(l1, l2) => Lambda::while_(self.simpl(l1), self.simpl(l2)),

            // lam_pass_remove_alias.ml:283-284
            Lambda::Lfor(var, l1, l2, dir, l3) => Lambda::for_(
                var.clone(),
                self.simpl(l1),
                self.simpl(l2),
                *dir,
                self.simpl(l3),
            ),

            // lam_pass_remove_alias.ml after #7887: Lfor_of / Lfor_await_of.
            Lambda::Lfor_of(var, l1, l2) => {
                Lambda::for_of(var.clone(), self.simpl(l1), self.simpl(l2))
            }
            Lambda::Lfor_await_of(var, l1, l2) => {
                Lambda::for_await_of(var.clone(), self.simpl(l1), self.simpl(l2))
            }

            // OCaml `Lam_pass_remove_alias.simplify_alias` after #8348:
            // `Lbreak -> Lam.break | Lcontinue -> Lam.continue`.
            Lambda::Lbreak => Lambda::break_(),
            Lambda::Lcontinue => Lambda::continue_(),

            // lam_pass_remove_alias.ml:285-288
            Lambda::Lassign(v, l) => Lambda::assign(v.clone(), self.simpl(l)),
        }
    }
}
