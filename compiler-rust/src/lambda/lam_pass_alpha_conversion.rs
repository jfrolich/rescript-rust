//! Direct port of `compiler/core/lam_pass_alpha_conversion.ml`.
//!
//! Visits applications, consulting [`get_arity`]
//! (`Lam_arity_analysis.get_arity`) to tag applications with
//! `App_infer_full` or transform under-application.
//!
//! Every line traces to a specific line in OCaml. No invented logic.

use crate::lambda::lam_compile_context::LamStats;
use crate::lambda::lam_eta_conversion::transform_under_supply;
use crate::lambda::lam_pass_collect::ExternalArityResolver;
use crate::lambda::lam_primitive::Primitive;
use crate::lambda::{ApInfo, Apply, ApplyStatus, Lambda, LambdaSwitch, PrimInfo};

/// Direct port of `Lam_pass_alpha_conversion.alpha_conversion`
/// (lam_pass_alpha_conversion.ml:25-129).
pub fn alpha_conversion(meta: &LamStats, lam: &Lambda) -> Lambda {
    alpha_conversion_owned(meta, lam.clone())
}

/// Owned entry point for the same OCaml pass
/// (`compiler/core/lam_pass_alpha_conversion.ml:25-129`).
///
/// OCaml rebuilds the immutable Lambda tree. Rust can consume the previous
/// pass result in the backend pipeline, preserving the same case behavior while
/// avoiding an eager clone of the whole tree before the rebuild.
pub fn alpha_conversion_owned(meta: &LamStats, lam: Lambda) -> Lambda {
    let mut meta = meta.clone();
    let mut alpha = Alpha {
        meta: &mut meta,
        external_arity: None,
    };
    alpha.simpl_owned(lam)
}

pub fn alpha_conversion_with_external_arity_owned(
    meta: &mut LamStats,
    lam: Lambda,
    external_arity: &mut ExternalArityResolver<'_>,
) -> Lambda {
    let mut alpha = Alpha {
        meta,
        external_arity: Some(external_arity),
    };
    alpha.simpl_owned(lam)
}

struct Alpha<'a, 'r> {
    meta: &'a mut LamStats,
    external_arity: Option<&'a mut ExternalArityResolver<'r>>,
}

impl<'a, 'r> Alpha<'a, 'r> {
    fn get_arity(&mut self, lam: &Lambda) -> crate::lambda::lam_arity::Arity {
        match self.external_arity.as_deref_mut() {
            Some(resolver) => crate::lambda::lam_pass_collect::get_arity_with_external_arity(
                self.meta, lam, resolver,
            ),
            None => crate::lambda::lam_pass_collect::get_arity(self.meta, lam),
        }
    }

    /// Direct port of `populate_apply_info`
    /// (lam_pass_alpha_conversion.ml:26-49).
    fn populate_apply_info(
        &mut self,
        ap_transformed_jsx: bool,
        args_arity: &[i32],
        len: i32,
        fn_: &Lambda,
        args: &[Lambda],
        ap_info: &ApInfo,
    ) -> Lambda {
        // lam_pass_alpha_conversion.ml:30-31 — arity unknown / 0 head: pure
        // recursion through `Lam.apply`.
        match args_arity.first().copied() {
            None | Some(0) => Lambda::apply(
                self.simpl(fn_),
                args.iter().map(|a| self.simpl(a)).collect(),
                ap_info.clone(),
                ap_transformed_jsx,
            ),
            Some(x) => {
                if x == len {
                    // lam_pass_alpha_conversion.ml:33-36 — exact match: tag
                    // the application as `App_infer_full`.
                    let new_info = ApInfo {
                        status: ApplyStatus::InferFull,
                        ..ap_info.clone()
                    };
                    Lambda::apply(
                        self.simpl(fn_),
                        args.iter().map(|a| self.simpl(a)).collect(),
                        new_info,
                        ap_transformed_jsx,
                    )
                } else if x > len {
                    // lam_pass_alpha_conversion.ml:37-42 — under-application:
                    // eta-expand to fill the missing arguments.
                    let fn_ = self.simpl(fn_);
                    let args: Vec<Lambda> = args.iter().map(|a| self.simpl(a)).collect();
                    let new_info = ApInfo {
                        status: ApplyStatus::InferFull,
                        ..ap_info.clone()
                    };
                    transform_under_supply(&self.meta.id_gen, x - len, &new_info, fn_, args)
                } else {
                    // lam_pass_alpha_conversion.ml:43-48 — over-application:
                    // split into nested `Lam.apply` calls. The inner call
                    // gets `App_infer_full`; the outer keeps the original.
                    let split = x as usize;
                    let first: Vec<Lambda> = args[..split].iter().map(|a| self.simpl(a)).collect();
                    let rest: Vec<Lambda> = args[split..].iter().map(|a| self.simpl(a)).collect();
                    let infer_full = ApInfo {
                        status: ApplyStatus::InferFull,
                        ..ap_info.clone()
                    };
                    let inner = Lambda::apply(self.simpl(fn_), first, infer_full, false);
                    Lambda::apply(inner, rest, ap_info.clone(), ap_transformed_jsx)
                }
            }
        }
    }

    /// Owned form of `populate_apply_info`
    /// (`compiler/core/lam_pass_alpha_conversion.ml:26-49`).
    fn populate_apply_info_owned(
        &mut self,
        ap_transformed_jsx: bool,
        args_arity: &[i32],
        len: i32,
        fn_: Lambda,
        args: Vec<Lambda>,
        ap_info: ApInfo,
    ) -> Lambda {
        match args_arity.first().copied() {
            None | Some(0) => Lambda::apply(
                self.simpl_owned(fn_),
                args.into_iter().map(|a| self.simpl_owned(a)).collect(),
                ap_info,
                ap_transformed_jsx,
            ),
            Some(x) if x == len => {
                let new_info = ApInfo {
                    status: ApplyStatus::InferFull,
                    ..ap_info
                };
                Lambda::apply(
                    self.simpl_owned(fn_),
                    args.into_iter().map(|a| self.simpl_owned(a)).collect(),
                    new_info,
                    ap_transformed_jsx,
                )
            }
            Some(x) if x > len => {
                let fn_ = self.simpl_owned(fn_);
                let args = args.into_iter().map(|a| self.simpl_owned(a)).collect();
                let new_info = ApInfo {
                    status: ApplyStatus::InferFull,
                    ..ap_info
                };
                transform_under_supply(&self.meta.id_gen, x - len, &new_info, fn_, args)
            }
            Some(x) => {
                let split = x as usize;
                let mut args = args.into_iter();
                let first: Vec<Lambda> = args
                    .by_ref()
                    .take(split)
                    .map(|a| self.simpl_owned(a))
                    .collect();
                let rest: Vec<Lambda> = args.map(|a| self.simpl_owned(a)).collect();
                let infer_full = ApInfo {
                    status: ApplyStatus::InferFull,
                    ..ap_info.clone()
                };
                let inner = Lambda::apply(self.simpl_owned(fn_), first, infer_full, false);
                Lambda::apply(inner, rest, ap_info, ap_transformed_jsx)
            }
        }
    }

    /// Direct port of `simpl` (lam_pass_alpha_conversion.ml:50-126).
    fn simpl(&mut self, lam: &Lambda) -> Lambda {
        match lam {
            // lam_pass_alpha_conversion.ml:52-53
            Lambda::Lconst(_) | Lambda::Lvar(_) => lam.clone(),

            // lam_pass_alpha_conversion.ml:54-61
            Lambda::Lapply(Apply {
                ap_func,
                ap_args,
                ap_info,
                ap_transformed_jsx,
            }) => {
                let args_arity = self.get_arity(ap_func).extract_arity();
                let len = ap_args.len() as i32;
                self.populate_apply_info(
                    *ap_transformed_jsx,
                    &args_arity,
                    len,
                    ap_func,
                    ap_args,
                    ap_info,
                )
            }

            // lam_pass_alpha_conversion.ml:62
            Lambda::Llet(str, v, l1, l2) => {
                Lambda::let_(*str, v.clone(), self.simpl(l1), self.simpl(l2))
            }

            // lam_pass_alpha_conversion.ml:63-65
            Lambda::Lletrec(bindings, body) => {
                let bindings = bindings
                    .iter()
                    .map(|(id, e)| (id.clone(), self.simpl(e)))
                    .collect();
                Lambda::letrec(bindings, self.simpl(body))
            }

            // lam_pass_alpha_conversion.ml:66
            Lambda::LglobalModule(_, _) => lam.clone(),

            // lam_pass_alpha_conversion.ml:67-68 — recurse through primitives.
            Lambda::Lprim(PrimInfo {
                primitive,
                args,
                loc,
            }) => Lambda::prim(
                primitive.clone(),
                args.iter().map(|a| self.simpl(a)).collect(),
                loc.clone(),
            ),

            // lam_pass_alpha_conversion.ml:88-90
            Lambda::Lfunction(f) => Lambda::function_(
                f.arity,
                f.params.clone(),
                self.simpl(&f.body),
                f.attr.clone(),
            ),

            // lam_pass_alpha_conversion.ml:91-109
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

            // lam_pass_alpha_conversion.ml:110-113
            Lambda::LstringSwitch(scrut, sw, d) => Lambda::string_switch(
                self.simpl(scrut),
                sw.iter().map(|(k, v)| (k.clone(), self.simpl(v))).collect(),
                d.as_ref().map(|d| Box::new(self.simpl(d))),
            ),

            // lam_pass_alpha_conversion.ml:114
            Lambda::LstaticRaise(i, ls) => {
                Lambda::static_raise(*i, ls.iter().map(|l| self.simpl(l)).collect())
            }

            // lam_pass_alpha_conversion.ml:115
            Lambda::LstaticCatch(l1, ids, l2) => {
                Lambda::static_catch(self.simpl(l1), ids.0, ids.1.clone(), self.simpl(l2))
            }

            // lam_pass_alpha_conversion.ml:116
            Lambda::LtryWith(l1, v, l2) => Lambda::try_(self.simpl(l1), v.clone(), self.simpl(l2)),

            // lam_pass_alpha_conversion.ml:117
            Lambda::LifThenElse(l1, l2, l3) => {
                Lambda::if_(self.simpl(l1), self.simpl(l2), self.simpl(l3))
            }

            // lam_pass_alpha_conversion.ml:118
            Lambda::Lsequence(l1, l2) => Lambda::seq(self.simpl(l1), self.simpl(l2)),

            // lam_pass_alpha_conversion.ml:119
            Lambda::Lwhile(l1, l2) => Lambda::while_(self.simpl(l1), self.simpl(l2)),

            // lam_pass_alpha_conversion.ml:120-121
            Lambda::Lfor(var, l1, l2, dir, l3) => Lambda::for_(
                var.clone(),
                self.simpl(l1),
                self.simpl(l2),
                *dir,
                self.simpl(l3),
            ),

            // lam_pass_alpha_conversion.ml after #7887: Lfor_of / Lfor_await_of.
            Lambda::Lfor_of(var, l1, l2) => {
                Lambda::for_of(var.clone(), self.simpl(l1), self.simpl(l2))
            }
            Lambda::Lfor_await_of(var, l1, l2) => {
                Lambda::for_await_of(var.clone(), self.simpl(l1), self.simpl(l2))
            }

            // OCaml `Lam_pass_alpha_conversion.simpl` after #8348:
            // `Lbreak -> Lam.break | Lcontinue -> Lam.continue`.
            Lambda::Lbreak => Lambda::break_(),
            Lambda::Lcontinue => Lambda::continue_(),

            // lam_pass_alpha_conversion.ml:122-125
            Lambda::Lassign(v, l) => Lambda::assign(v.clone(), self.simpl(l)),
        }
    }

    /// Owned form of `simpl` (`compiler/core/lam_pass_alpha_conversion.ml:50-126`).
    fn simpl_owned(&mut self, lam: Lambda) -> Lambda {
        match lam {
            Lambda::Lconst(_) | Lambda::Lvar(_) | Lambda::LglobalModule(_, _) => lam,
            Lambda::Lapply(Apply {
                ap_func,
                ap_args,
                ap_info,
                ap_transformed_jsx,
            }) => {
                let args_arity = self.get_arity(&ap_func).extract_arity();
                let len = ap_args.len() as i32;
                self.populate_apply_info_owned(
                    ap_transformed_jsx,
                    &args_arity,
                    len,
                    *ap_func,
                    ap_args,
                    ap_info,
                )
            }
            Lambda::Llet(str, v, l1, l2) => {
                Lambda::let_(str, v, self.simpl_owned(*l1), self.simpl_owned(*l2))
            }
            Lambda::Lletrec(bindings, body) => {
                let bindings = bindings
                    .into_iter()
                    .map(|(id, e)| (id, self.simpl_owned(e)))
                    .collect();
                Lambda::letrec(bindings, self.simpl_owned(*body))
            }
            Lambda::Lprim(PrimInfo {
                primitive,
                args,
                loc,
            }) => Lambda::prim(
                primitive,
                args.into_iter().map(|a| self.simpl_owned(a)).collect(),
                loc,
            ),
            Lambda::Lfunction(f) => {
                Lambda::function_(f.arity, f.params, self.simpl_owned(*f.body), f.attr)
            }
            Lambda::Lswitch(scrut, switch) => Lambda::switch(
                self.simpl_owned(*scrut),
                LambdaSwitch {
                    sw_consts_full: switch.sw_consts_full,
                    sw_consts: switch
                        .sw_consts
                        .into_iter()
                        .map(|(k, l)| (k, self.simpl_owned(l)))
                        .collect(),
                    sw_blocks_full: switch.sw_blocks_full,
                    sw_blocks: switch
                        .sw_blocks
                        .into_iter()
                        .map(|(k, l)| (k, self.simpl_owned(l)))
                        .collect(),
                    sw_failaction: switch.sw_failaction.map(|f| Box::new(self.simpl_owned(*f))),
                    sw_dispatch: switch.sw_dispatch,
                },
            ),
            Lambda::LstringSwitch(scrut, sw, d) => Lambda::string_switch(
                self.simpl_owned(*scrut),
                sw.into_iter()
                    .map(|(k, v)| (k, self.simpl_owned(v)))
                    .collect(),
                d.map(|d| Box::new(self.simpl_owned(*d))),
            ),
            Lambda::LstaticRaise(i, ls) => {
                Lambda::static_raise(i, ls.into_iter().map(|l| self.simpl_owned(l)).collect())
            }
            Lambda::LstaticCatch(l1, ids, l2) => {
                Lambda::static_catch(self.simpl_owned(*l1), ids.0, ids.1, self.simpl_owned(*l2))
            }
            Lambda::LtryWith(l1, v, l2) => {
                Lambda::try_(self.simpl_owned(*l1), v, self.simpl_owned(*l2))
            }
            Lambda::LifThenElse(l1, l2, l3) => Lambda::if_(
                self.simpl_owned(*l1),
                self.simpl_owned(*l2),
                self.simpl_owned(*l3),
            ),
            Lambda::Lsequence(l1, l2) => Lambda::seq(self.simpl_owned(*l1), self.simpl_owned(*l2)),
            Lambda::Lwhile(l1, l2) => Lambda::while_(self.simpl_owned(*l1), self.simpl_owned(*l2)),
            Lambda::Lfor(var, l1, l2, dir, l3) => Lambda::for_(
                var,
                self.simpl_owned(*l1),
                self.simpl_owned(*l2),
                dir,
                self.simpl_owned(*l3),
            ),
            Lambda::Lfor_of(var, l1, l2) => {
                Lambda::for_of(var, self.simpl_owned(*l1), self.simpl_owned(*l2))
            }
            Lambda::Lfor_await_of(var, l1, l2) => {
                Lambda::for_await_of(var, self.simpl_owned(*l1), self.simpl_owned(*l2))
            }
            Lambda::Lbreak => Lambda::break_(),
            Lambda::Lcontinue => Lambda::continue_(),
            Lambda::Lassign(v, l) => Lambda::assign(v, self.simpl_owned(*l)),
        }
    }
}
