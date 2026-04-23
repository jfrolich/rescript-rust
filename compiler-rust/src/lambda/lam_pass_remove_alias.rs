//! Direct port of `compiler/core/lam_pass_remove_alias.ml`.
//!
//! Field folding, optional-block unwrapping, cross-module function inlining
//! and boolean-constant folding using the `ident_tbl` populated by
//! `Lam_pass_collect.collect_info`.
//!
//! Cross-module inlining (`Lam_compile_env.query_external_id_info`) has no
//! Rust counterpart yet, so the corresponding `Lapply` arm short-circuits to
//! the default fallthrough. This mirrors what OCaml does whenever the
//! external info is missing — the application is left intact.
//!
//! Every line below must trace to a specific line in OCaml. No invented
//! logic.

use crate::lambda::lam_analysis::{lfunction_can_be_inlined, ok_to_inline_fun_when_app};
use crate::lambda::lam_closure::is_closed_with_map;
use crate::lambda::lam_compat::Comparison;
use crate::lambda::lam_compile_context::{BoxedNullable, IdKind, IdentTable, LamStats, RecFlag};
use crate::lambda::lam_constant::Constant;
use crate::lambda::lam_hit::hit_variable;
use crate::lambda::lam_util::field_flatten_get;
use crate::lambda::lam_primitive::Primitive;
use crate::lambda::lam_tag_info::TagInfo;
use crate::lambda::{Lambda, LambdaSwitch, PrimInfo};
use crate::location::Location;

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
            matches!(tag_info, TagInfo::Some | TagInfo::SomeNotNested)
        }
        _ => false,
    }
}

/// Port of `Lam.not_` (lam.ml:584-588). Folds `Pintcomp Cneq -> Pintcomp Ceq`
/// to keep the outcome shape clean; otherwise wraps the argument in `Pnot`.
fn lam_not(loc: Location, x: Lambda) -> Lambda {
    match x {
        Lambda::Lprim(PrimInfo {
            primitive: Primitive::Pintcomp(Comparison::Neq),
            args,
            loc: l,
        }) => Lambda::Lprim(PrimInfo {
            primitive: Primitive::Pintcomp(Comparison::Eq),
            args,
            loc: l,
        }),
        x => Lambda::prim(Primitive::Pnot, vec![x], loc),
    }
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
    let export_idents = std::mem::take(&mut meta.export_idents);
    let id_gen = meta.id_gen.clone();
    let result = Simplifier {
        ident_tbl: &mut meta.ident_tbl,
        export_idents: &export_idents,
        id_gen: &id_gen,
        jsx_preserve: false,
    }
    .simpl(lam);
    meta.export_idents = export_idents;
    result
}

/// Same as [`simplify_alias`] but threads the JSX preservation flag — a port
/// of OCaml's `Js_config.jsx_preserve` global. The 7432-tagged Pjs_call arm
/// inside `simpl` only fires when this flag is true (lam_pass_remove_alias.ml:54-62).
pub fn simplify_alias_with_jsx(meta: &mut LamStats, lam: &Lambda, jsx_preserve: bool) -> Lambda {
    let export_idents = std::mem::take(&mut meta.export_idents);
    let id_gen = meta.id_gen.clone();
    let result = Simplifier {
        ident_tbl: &mut meta.ident_tbl,
        export_idents: &export_idents,
        id_gen: &id_gen,
        jsx_preserve,
    }
    .simpl(lam);
    meta.export_idents = export_idents;
    result
}

struct Simplifier<'a> {
    ident_tbl: &'a mut crate::lambda::lam_compile_context::IdentTable,
    export_idents: &'a std::collections::HashSet<crate::ident::Ident>,
    /// Shared stamp counter used for `Ident.rename` during beta reduction.
    /// Mirrors OCaml's global `Ident.rename` counter so fresh stamps never
    /// collide across independent beta reductions of the same function.
    id_gen: &'a crate::context::IdGenerator,
    jsx_preserve: bool,
}

impl<'a> Simplifier<'a> {
    fn simpl(&mut self, lam: &Lambda) -> Lambda {
        match lam {
            // lam_pass_remove_alias.ml:53
            Lambda::Lvar(_) => lam.clone(),

            // lam_pass_remove_alias.ml:54-62 — JSX preserve guard for jsx/jsxs
            // calls. The first argument (the field-bearing Pfield) is kept
            // verbatim, the rest are recursively simplified.
            Lambda::Lprim(PrimInfo {
                primitive: primitive @ Primitive::PjsCall { .. },
                args,
                loc,
            }) if self.jsx_preserve
                && matches!(
                    primitive,
                    Primitive::PjsCall { prim_name, .. }
                        if prim_name == "jsx" || prim_name == "jsxs"
                )
                && matches!(
                    args.first(),
                    Some(Lambda::Lprim(PrimInfo {
                        primitive: Primitive::Pfield(_, _),
                        ..
                    }))
                ) =>
            {
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
            Lambda::Lprim(PrimInfo {
                primitive: primitive @ Primitive::Pfield(i, info),
                args,
                loc,
            }) if args.len() == 1 => {
                let simplified = self.simpl(&args[0]);
                match simplified {
                    Lambda::Lvar(ref v) => {
                        let l_clone = simplified.clone();
                        let primitive_clone = primitive.clone();
                        let loc_clone = loc.clone();
                        field_flatten_get(
                            move || {
                                Lambda::prim(primitive_clone, vec![l_clone], loc_clone)
                            },
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
            Lambda::Lprim(PrimInfo {
                primitive: p @ (Primitive::PvalFromOption | Primitive::PvalFromOptionNotNest),
                args,
                loc: _,
            }) if matches!(args.as_slice(), [Lambda::Lvar(_)]) => {
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
            Lambda::Lprim(PrimInfo {
                primitive,
                args,
                loc,
            }) => Lambda::prim(
                primitive.clone(),
                args.iter().map(|a| self.simpl(a)).collect(),
                loc.clone(),
            ),

            // lam_pass_remove_alias.ml:83-104 — Lifthenelse with a
            // `Pis_not_none [Lvar id]` discriminator: consult `meta.ident_tbl`
            // to fold the test or rewrite it into an explicit null/undefined
            // probe.
            Lambda::LifThenElse(cond, then_, else_)
                if matches!(
                    cond.as_ref(),
                    Lambda::Lprim(PrimInfo {
                        primitive: Primitive::PisNotNone,
                        args,
                        ..
                    }) if matches!(args.as_slice(), [Lambda::Lvar(_)])
                ) =>
            {
                let Lambda::Lprim(PrimInfo { args: cond_args, .. }) = cond.as_ref() else {
                    unreachable!()
                };
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
                    _ => Lambda::if_(
                        cond.as_ref().clone(),
                        self.simpl(then_),
                        self.simpl(else_),
                    ),
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
                        Outcome::EvalUnknown => Lambda::if_(
                            self.simpl(cond),
                            self.simpl(then_),
                            self.simpl(else_),
                        ),
                    }
                }
                _ => Lambda::if_(self.simpl(cond), self.simpl(then_), self.simpl(else_)),
            },

            // lam_pass_remove_alias.ml:118
            Lambda::Lconst(_) => lam.clone(),

            // lam_pass_remove_alias.ml:119
            Lambda::Llet(kind, v, l1, l2) => Lambda::let_(
                *kind,
                v.clone(),
                self.simpl(l1),
                self.simpl(l2),
            ),

            // lam_pass_remove_alias.ml:120-122
            Lambda::Lletrec(bindings, body) => {
                let bindings = bindings
                    .iter()
                    .map(|(id, e)| (id.clone(), self.simpl(e)))
                    .collect();
                Lambda::letrec(bindings, self.simpl(body))
            }

            // lam_pass_remove_alias.ml:131-162 — cross-module fn inlining via
            // `Lam_compile_env.query_external_id_info`. The Rust JS backend
            // has no env counterpart, so we cannot resolve the foreign
            // function's `persistent_closed_lambda`. Fall through to the
            // default Lapply arm below by NOT catching this case here.
            //
            // lam_pass_remove_alias.ml:169-232 — local Lvar callee inlining.
            Lambda::Lapply(apply) if matches!(apply.ap_func.as_ref(), Lambda::Lvar(_)) => {
                let Lambda::Lvar(v) = apply.ap_func.as_ref() else {
                    unreachable!()
                };
                let ap_args: Vec<Lambda> =
                    apply.ap_args.iter().map(|a| self.simpl(a)).collect();

                // Clone the FunctionId payload to release the immutable
                // borrow on `self.ident_tbl`; the beta-reduction helpers below
                // mutate it to register fresh let-bindings, and the `self.simpl`
                // recursion that follows needs `&mut self` in turn.
                let func_info = match self.ident_tbl.get(v) {
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
                        let (param_ok, param_map) = is_closed_with_map(
                            self.export_idents,
                            &func.params,
                            &func.body,
                        );
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
            Lambda::Lapply(apply)
                if matches!(apply.ap_func.as_ref(), Lambda::Lfunction(_)) =>
            {
                // Clone the function payload up front: the mutable meta
                // borrow used by `propagate_beta_reduce_with_meta` is
                // incompatible with the `apply.ap_func` / `apply.ap_args`
                // borrows we need to carry across the call.
                let func_clone = match apply.ap_func.as_ref() {
                    Lambda::Lfunction(func) => func.clone(),
                    _ => unreachable!(),
                };
                let args: Vec<Lambda> =
                    apply.ap_args.iter().map(|a| self.simpl(a)).collect();
                if args.len() == func_clone.params.len()
                    && lfunction_can_be_inlined(&func_clone)
                {
                    let reduced = crate::lambda::lam_beta_reduce::propagate_beta_reduce_with_meta_and_id_gen(
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
                        .map(|(k, l)| (*k, self.simpl(l)))
                        .collect(),
                    sw_blocks_full: switch.sw_blocks_full,
                    sw_blocks: switch
                        .sw_blocks
                        .iter()
                        .map(|(k, l)| (*k, self.simpl(l)))
                        .collect(),
                    sw_failaction: switch
                        .sw_failaction
                        .as_ref()
                        .map(|f| Box::new(self.simpl(f))),
                    sw_names: switch.sw_names.clone(),
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
            Lambda::LstaticCatch(l1, ids, l2) => Lambda::static_catch(
                self.simpl(l1),
                ids.0,
                ids.1.clone(),
                self.simpl(l2),
            ),

            // lam_pass_remove_alias.ml:280
            Lambda::LtryWith(l1, v, l2) => {
                Lambda::try_(self.simpl(l1), v.clone(), self.simpl(l2))
            }

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

            // OCaml `Lam_pass_remove_alias.simplify_alias` after #8348:
            // `Lbreak -> Lam.break | Lcontinue -> Lam.continue`.
            Lambda::Lbreak => Lambda::break_(),
            Lambda::Lcontinue => Lambda::continue_(),

            // lam_pass_remove_alias.ml:285-288
            Lambda::Lassign(v, l) => Lambda::assign(v.clone(), self.simpl(l)),
        }
    }
}

