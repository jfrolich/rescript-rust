//! Direct port of `compiler/core/lam_pass_lets_dce.ml`.
//!
//! Combines dead-code elimination of let bindings with alias inlining: every
//! decision is driven by the precomputed [`OccTbl`] from
//! [`super::lam_pass_count::collect_occurs`], so this pass is O(n).
//!
//! Each match arm cites the OCaml line in `lam_pass_lets_dce.ml` that
//! justifies it. Do not introduce Rust-only logic.

use crate::lambda::map_box;
use ahash::AHashMap as HashMap;

use crate::ident::Ident;
use crate::lambda::lam_analysis::{lfunction_can_be_inlined, no_side_effects};
use crate::lambda::lam_beta_reduce::no_names_beta_reduce;
use crate::lambda::lam_compat::LetKind;
use crate::lambda::lam_constant::Constant;
use crate::lambda::lam_pass_count::{OccTbl, UsedInfo, collect_occurs, dummy_info};
use crate::lambda::lam_pass_eliminate_ref::{RealReference, eliminate_ref};
use crate::lambda::lam_primitive::{Mutable, Primitive};
use crate::lambda::lam_util::refine_let;
use crate::lambda::{Apply, LFunction, Lambda, LambdaSwitch, PrimInfo};

/// State held during the recursive pass: substitution table and an inline
/// string table for downstream `Pstringadd` constant folding. Both mirror
/// OCaml's `Hash_ident.t` (lam_pass_lets_dce.ml:15-16).
struct LetsState<'a> {
    occ: &'a OccTbl,
    subst: HashMap<Ident, Lambda>,
    string_table: HashMap<Ident, String>,
}

impl<'a> LetsState<'a> {
    fn new(occ: &'a OccTbl) -> Self {
        Self {
            occ,
            subst: HashMap::with_capacity(32),
            string_table: HashMap::with_capacity(32),
        }
    }

    /// Equivalent of OCaml's `count_var v` lookup
    /// (lam_pass_lets_dce.ml:209-213): returns the recorded info or the dummy.
    fn count_var(&self, v: &Ident) -> UsedInfo {
        self.occ
            .get(v)
            .map(|cell| *cell.borrow())
            .unwrap_or_else(dummy_info)
    }

    /// Equivalent of OCaml's `used` helper (lam_pass_lets_dce.ml:17).
    fn used(&self, v: &Ident) -> bool {
        self.count_var(v).times > 0
    }
}

/// Direct port of `Lam_pass_lets_dce.lets_helper` (lam_pass_lets_dce.ml:14-205).
fn lets_helper(state: &mut LetsState<'_>, lam: &Lambda) -> Lambda {
    match lam {
        // Lvar (lam_pass_lets_dce.ml:20): look up in subst, default to lam.
        Lambda::Lvar(v) => state.subst.get(v).cloned().unwrap_or_else(|| lam.clone()),

        // `Llet ((Strict | Alias | StrictOpt), v, Lvar w, l2)`
        // (lam_pass_lets_dce.ml:21-23). Always alias-inline the rhs `Lvar w`.
        // Variable-kind let bindings of an Lvar are NOT covered by this arm —
        // they fall through to the kind-specific arms below.
        Lambda::Llet(kind, v, value, l2)
            if matches!(value.as_ref(), Lambda::Lvar(_))
                && matches!(kind, LetKind::Strict | LetKind::Alias | LetKind::StrictOpt) =>
        {
            let w = match value.as_ref() {
                Lambda::Lvar(w) => w.clone(),
                _ => unreachable!(),
            };
            let simplified_w = lets_helper(state, &Lambda::Lvar(w));
            state.subst.insert(v.clone(), simplified_w);
            lets_helper(state, l2)
        }

        // `Llet (Strict, v, Pmakeblock( _, Mutable) [linit], lbody)`
        // (lam_pass_lets_dce.ml:24-43): try `eliminate_ref` to reify the
        // ref-cell into a plain mutable variable. On success use Variable
        // kind; on failure fall back to refine_let with the original kind.
        Lambda::Llet(LetKind::Strict, v, value, lbody)
            if matches!(
                value.as_ref(),
                Lambda::Lprim(PrimInfo {
                    primitive: Primitive::Pmakeblock( _, Mutable::Mutable),
                    args,
                    ..
                }) if args.len() == 1
            ) =>
        {
            let (primitive, linit, loc) = match value.as_ref() {
                Lambda::Lprim(prim) => (
                    prim.primitive.clone(),
                    prim.args[0].clone(),
                    prim.loc.clone(),
                ),
                _ => unreachable!(),
            };
            let slinit = lets_helper(state, &linit);
            let slbody = lets_helper(state, lbody);
            match eliminate_ref(v, &slbody) {
                Ok(reified) => refine_let(LetKind::Variable, v.clone(), slinit, reified),
                Err(RealReference) => refine_let(
                    LetKind::Strict,
                    v.clone(),
                    Lambda::prim(primitive, vec![slinit], loc),
                    slbody,
                ),
            }
        }

        // `Llet (Alias, v, l1, l2)` (lam_pass_lets_dce.ml:44-73).
        Lambda::Llet(LetKind::Alias, v, l1, l2) => {
            let info = state.count_var(v);

            // times = 0: drop the binding entirely (lam_pass_lets_dce.ml:49).
            if info.times == 0 {
                return lets_helper(state, l2);
            }

            // times = 1 + not captured: substitute (lam_pass_lets_dce.ml:50).
            // times = 1 + captured but rhs is Lconst|Lvar: substitute
            //   (lam_pass_lets_dce.ml:51).
            // any times + rhs is a "small" constant or Pfield-from-global:
            //   substitute (lam_pass_lets_dce.ml:52-57).
            let small_const = matches!(
                l1.as_ref(),
                Lambda::Lconst(
                    Constant::Int { .. }
                        | Constant::Constructor(_)
                        | Constant::NativeInt { .. }
                        | Constant::Char(_)
                        | Constant::Float(_)
                        | Constant::BigInt { .. }
                        | Constant::Pointer(_)
                        | Constant::JsTrue
                        | Constant::JsFalse
                        | Constant::JsUndefined { .. }
                )
            );
            let pfield_from_global = matches!(
                l1.as_ref(),
                Lambda::Lprim(PrimInfo {
                    primitive: Primitive::Pfield(_, _),
                    args,
                    ..
                }) if args.len() == 1 && matches!(args[0], Lambda::LglobalModule(_, _))
            );
            let subst_now = (info.times == 1 && !info.captured)
                || (info.times == 1
                    && info.captured
                    && matches!(l1.as_ref(), Lambda::Lconst(_) | Lambda::Lvar(_)))
                || small_const
                || pfield_from_global;

            if subst_now {
                let simplified = lets_helper(state, l1);
                state.subst.insert(v.clone(), simplified);
                return lets_helper(state, l2);
            }

            // String constants — record in string_table for later Pstringadd
            // folding, but keep the binding (lam_pass_lets_dce.ml:66-69).
            if let Lambda::Lconst(Constant::String { s, delim: None }) = l1.as_ref() {
                state.string_table.insert(v.clone(), s.clone());
                let simplified_body = lets_helper(state, l2);
                return Lambda::let_(LetKind::Alias, v.clone(), (**l1).clone(), simplified_body);
            }

            // Fall-through: keep the alias binding (lam_pass_lets_dce.ml:71-72).
            let new_l1 = lets_helper(state, l1);
            let new_l2 = lets_helper(state, l2);
            Lambda::let_(LetKind::Alias, v.clone(), new_l1, new_l2)
        }

        // `Llet (StrictOpt, v, l1, lbody)` (lam_pass_lets_dce.ml:74-120).
        Lambda::Llet(LetKind::StrictOpt, v, l1, lbody) => {
            // Drop the binding if v is unused — counted matches in
            // collect_occurs already skipped over its initializer
            // (lam_pass_lets_dce.ml:74-93).
            if !state.used(v) {
                return lets_helper(state, lbody);
            }

            // ref-cell special case (lam_pass_lets_dce.ml:95-111).
            if let Lambda::Lprim(PrimInfo {
                primitive: Primitive::Pmakeblock(info, Mutable::Mutable),
                args,
                loc,
            }) = l1.as_ref()
            {
                if args.len() == 1 {
                    let primitive = Primitive::Pmakeblock(info.clone(), Mutable::Mutable);
                    let linit = args[0].clone();
                    let loc = loc.clone();
                    let slinit = lets_helper(state, &linit);
                    let slbody = lets_helper(state, lbody);
                    return match eliminate_ref(v, &slbody) {
                        Ok(reified) => refine_let(LetKind::Variable, v.clone(), slinit, reified),
                        Err(RealReference) => refine_let(
                            LetKind::StrictOpt,
                            v.clone(),
                            Lambda::prim(primitive, vec![slinit], loc),
                            slbody,
                        ),
                    };
                }
            }

            // General StrictOpt path (lam_pass_lets_dce.ml:112-120).
            let new_l1 = lets_helper(state, l1);
            if let Lambda::Lconst(Constant::String { s, delim: None }) = &new_l1 {
                state.string_table.insert(v.clone(), s.clone());
                let simplified_body = lets_helper(state, lbody);
                return Lambda::let_(LetKind::Alias, v.clone(), new_l1, simplified_body);
            }
            let simplified_body = lets_helper(state, lbody);
            refine_let(LetKind::StrictOpt, v.clone(), new_l1, simplified_body)
        }

        // `Llet ((Strict | Variable), v, l1, l2)` (lam_pass_lets_dce.ml:121-133).
        Lambda::Llet(kind @ (LetKind::Strict | LetKind::Variable), v, l1, l2) => {
            if !state.used(v) {
                let new_l1 = lets_helper(state, l1);
                let new_l2 = lets_helper(state, l2);
                return if no_side_effects(&new_l1) {
                    new_l2
                } else {
                    Lambda::seq(new_l1, new_l2)
                };
            }
            let new_l1 = lets_helper(state, l1);
            // Strict + Const_string special case
            // (lam_pass_lets_dce.ml:129-132).
            if matches!(kind, LetKind::Strict) {
                if let Lambda::Lconst(Constant::String { s, delim: None }) = &new_l1 {
                    state.string_table.insert(v.clone(), s.clone());
                    let simplified_body = lets_helper(state, l2);
                    return Lambda::let_(LetKind::Alias, v.clone(), new_l1, simplified_body);
                }
            }
            let simplified_body = lets_helper(state, l2);
            refine_let(*kind, v.clone(), new_l1, simplified_body)
        }

        // Lsequence (lam_pass_lets_dce.ml:134).
        Lambda::Lsequence(l1, l2) => {
            let s1 = lets_helper(state, l1);
            let s2 = lets_helper(state, l2);
            Lambda::seq(s1, s2)
        }

        // Lapply with inlineable Lfunction body (lam_pass_lets_dce.ml:135-139):
        // run the OCaml-style direct beta reduction through `simplif` again.
        Lambda::Lapply(apply)
            if matches!(apply.ap_func.as_ref(), Lambda::Lfunction(f)
                if f.params.len() == apply.ap_args.len() && lfunction_can_be_inlined(f)) =>
        {
            let f = match apply.ap_func.as_ref() {
                Lambda::Lfunction(f) => f,
                _ => unreachable!(),
            };
            let reduced = no_names_beta_reduce(&f.params, &f.body, &apply.ap_args);
            lets_helper(state, &reduced)
        }

        // Lapply general (lam_pass_lets_dce.ml:147-149).
        Lambda::Lapply(apply) => {
            let new_func = lets_helper(state, &apply.ap_func);
            let new_args: Vec<Lambda> = apply
                .ap_args
                .iter()
                .map(|a| lets_helper(state, a))
                .collect();
            Lambda::Lapply(Apply {
                ap_func: Box::new(new_func),
                ap_args: new_args,
                ap_info: apply.ap_info.clone(),
                ap_transformed_jsx: apply.ap_transformed_jsx,
            })
        }

        // Lfunction (lam_pass_lets_dce.ml:150-151).
        Lambda::Lfunction(LFunction {
            arity,
            params,
            body,
            attr,
        }) => {
            let new_body = lets_helper(state, body);
            Lambda::function_(*arity, params.clone(), new_body, attr.clone())
        }

        // Lconst (lam_pass_lets_dce.ml:152).
        Lambda::Lconst(_) => lam.clone(),

        // Lletrec (lam_pass_lets_dce.ml:153-154).
        Lambda::Lletrec(bindings, body) => {
            let new_bindings: Vec<(Ident, Lambda)> = bindings
                .iter()
                .map(|(id, e)| (id.clone(), lets_helper(state, e)))
                .collect();
            let new_body = lets_helper(state, body);
            Lambda::letrec(new_bindings, new_body)
        }

        // Lprim Pstringadd [l; r] (lam_pass_lets_dce.ml:155-175). Folds string
        // concatenation through the precomputed string_table.
        Lambda::Lprim(PrimInfo {
            primitive: Primitive::Pstringadd,
            args,
            loc,
        }) if args.len() == 2 => {
            let l_simpl = lets_helper(state, &args[0]);
            let r_simpl = lets_helper(state, &args[1]);
            let opt_l = lookup_string(&l_simpl, &state.string_table);
            match opt_l {
                None => Lambda::prim(Primitive::Pstringadd, vec![l_simpl, r_simpl], loc.clone()),
                Some(l_s) => {
                    let opt_r = lookup_string(&r_simpl, &state.string_table);
                    match opt_r {
                        None => {
                            Lambda::prim(Primitive::Pstringadd, vec![l_simpl, r_simpl], loc.clone())
                        }
                        Some(r_s) => Lambda::Lconst(Constant::String {
                            s: format!("{}{}", l_s, r_s),
                            delim: None,
                        }),
                    }
                }
            }
        }

        // Lglobal_module (lam_pass_lets_dce.ml:176).
        Lambda::LglobalModule(_, _) => lam.clone(),

        // Lprim general (lam_pass_lets_dce.ml:177-178).
        Lambda::Lprim(prim) => {
            let new_args: Vec<Lambda> = prim.args.iter().map(|a| lets_helper(state, a)).collect();
            Lambda::prim(prim.primitive.clone(), new_args, prim.loc.clone())
        }

        // Lswitch (lam_pass_lets_dce.ml:179-190).
        Lambda::Lswitch(scrut, sw) => {
            let new_scrut = lets_helper(state, scrut);
            let new_consts: Vec<(crate::lambda::SwitchKey, Lambda)> = sw
                .sw_consts
                .iter()
                .map(|(n, e)| (n.clone(), lets_helper(state, e)))
                .collect();
            let new_blocks: Vec<(crate::lambda::SwitchKey, Lambda)> = sw
                .sw_blocks
                .iter()
                .map(|(n, e)| (n.clone(), lets_helper(state, e)))
                .collect();
            let new_failaction = sw
                .sw_failaction
                .as_deref()
                .map(|x| Box::new(lets_helper(state, x)));
            Lambda::Lswitch(
                Box::new(new_scrut),
                LambdaSwitch {
                    sw_consts_full: sw.sw_consts_full,
                    sw_consts: new_consts,
                    sw_blocks_full: sw.sw_blocks_full,
                    sw_blocks: new_blocks,
                    sw_failaction: new_failaction,
                    sw_dispatch: sw.sw_dispatch.clone(),
                },
            )
        }

        // Lstringswitch (lam_pass_lets_dce.ml:191-194).
        Lambda::LstringSwitch(scrut, cases, default) => {
            let new_scrut = lets_helper(state, scrut);
            let new_cases: Vec<(String, Lambda)> = cases
                .iter()
                .map(|(s, e)| (s.clone(), lets_helper(state, e)))
                .collect();
            let new_default = default.as_deref().map(|x| Box::new(lets_helper(state, x)));
            Lambda::LstringSwitch(Box::new(new_scrut), new_cases, new_default)
        }

        // Lstaticraise (lam_pass_lets_dce.ml:195).
        Lambda::LstaticRaise(i, args) => {
            let new_args: Vec<Lambda> = args.iter().map(|a| lets_helper(state, a)).collect();
            Lambda::LstaticRaise(*i, new_args)
        }

        // Lstaticcatch (lam_pass_lets_dce.ml:196-197).
        Lambda::LstaticCatch(l1, label, l2) => {
            let s1 = lets_helper(state, l1);
            let s2 = lets_helper(state, l2);
            Lambda::LstaticCatch(Box::new(s1), label.clone(), Box::new(s2))
        }

        // Ltrywith (lam_pass_lets_dce.ml:198).
        Lambda::LtryWith(l1, v, l2) => {
            let s1 = lets_helper(state, l1);
            let s2 = lets_helper(state, l2);
            Lambda::LtryWith(Box::new(s1), v.clone(), Box::new(s2))
        }

        // OCaml uses Lam.if_ after simplification here
        // (compiler/core/lam_pass_lets_dce.ml:199), so preserve Lam.if_'s
        // raise/sequence rewrite from compiler/core/lam.ml:665-668.
        Lambda::LifThenElse(l1, l2, l3) => {
            let s1 = lets_helper(state, l1);
            let s2 = lets_helper(state, l2);
            let s3 = lets_helper(state, l3);
            Lambda::if_(s1, s2, s3)
        }

        // Lwhile (lam_pass_lets_dce.ml:200).
        Lambda::Lwhile(l1, l2) => {
            let s1 = lets_helper(state, l1);
            let s2 = lets_helper(state, l2);
            Lambda::Lwhile(Box::new(s1), Box::new(s2))
        }

        // Lfor (lam_pass_lets_dce.ml:201-202).
        Lambda::Lfor(v, l1, l2, dir, l3) => {
            let s1 = lets_helper(state, l1);
            let s2 = lets_helper(state, l2);
            let s3 = lets_helper(state, l3);
            Lambda::Lfor(v.clone(), Box::new(s1), Box::new(s2), *dir, Box::new(s3))
        }

        // Lfor_of / Lfor_await_of (lam_pass_lets_dce.ml after #7887).
        Lambda::Lfor_of(v, l1, l2) => {
            let s1 = lets_helper(state, l1);
            let s2 = lets_helper(state, l2);
            Lambda::for_of(v.clone(), s1, s2)
        }
        Lambda::Lfor_await_of(v, l1, l2) => {
            let s1 = lets_helper(state, l1);
            let s2 = lets_helper(state, l2);
            Lambda::for_await_of(v.clone(), s1, s2)
        }

        // Lassign (lam_pass_lets_dce.ml:203).
        Lambda::Lassign(v, l) => {
            let s = lets_helper(state, l);
            Lambda::Lassign(v.clone(), Box::new(s))
        }

        // OCaml `Lam_pass_lets_dce.lets_helper` after #8348:
        // `Lbreak -> Lam.break | Lcontinue -> Lam.continue`.
        Lambda::Lbreak => Lambda::break_(),
        Lambda::Lcontinue => Lambda::continue_(),
    }
}

/// Owned form of [`lets_helper`].
///
/// The branch order and decisions are the same direct port of
/// `Lam_pass_lets_dce.lets_helper` (compiler/core/lam_pass_lets_dce.ml:14-205);
/// this variant only consumes the Rust tree when the caller already owns it, so
/// pass-to-pass plumbing does not deep-clone every unchanged node.
fn lets_helper_owned(state: &mut LetsState<'_>, lam: Lambda) -> Lambda {
    match lam {
        Lambda::Lvar(v) => state.subst.get(&v).cloned().unwrap_or(Lambda::Lvar(v)),

        Lambda::Llet(kind, v, value, l2)
            if matches!(value.as_ref(), Lambda::Lvar(_))
                && matches!(kind, LetKind::Strict | LetKind::Alias | LetKind::StrictOpt) =>
        {
            let Lambda::Lvar(w) = *value else {
                unreachable!()
            };
            let simplified_w = lets_helper_owned(state, Lambda::Lvar(w));
            state.subst.insert(v, simplified_w);
            lets_helper_owned(state, *l2)
        }

        Lambda::Llet(LetKind::Strict, v, value, lbody)
            if matches!(
                value.as_ref(),
                Lambda::Lprim(PrimInfo {
                    primitive: Primitive::Pmakeblock( _, Mutable::Mutable),
                    args,
                    ..
                }) if args.len() == 1
            ) =>
        {
            let Lambda::Lprim(PrimInfo {
                primitive,
                mut args,
                loc,
            }) = *value
            else {
                unreachable!()
            };
            let linit = args.pop().expect("checked one ref initializer");
            let slinit = lets_helper_owned(state, linit);
            let slbody = lets_helper_owned(state, *lbody);
            match eliminate_ref(&v, &slbody) {
                Ok(reified) => refine_let(LetKind::Variable, v, slinit, reified),
                Err(RealReference) => refine_let(
                    LetKind::Strict,
                    v,
                    Lambda::prim(primitive, vec![slinit], loc),
                    slbody,
                ),
            }
        }

        Lambda::Llet(LetKind::Alias, v, l1, l2) => {
            let info = state.count_var(&v);
            if info.times == 0 {
                return lets_helper_owned(state, *l2);
            }

            let small_const = matches!(
                l1.as_ref(),
                Lambda::Lconst(
                    Constant::Int { .. }
                        | Constant::Constructor(_)
                        | Constant::NativeInt { .. }
                        | Constant::Char(_)
                        | Constant::Float(_)
                        | Constant::BigInt { .. }
                        | Constant::Pointer(_)
                        | Constant::JsTrue
                        | Constant::JsFalse
                        | Constant::JsUndefined { .. }
                )
            );
            let pfield_from_global = matches!(
                l1.as_ref(),
                Lambda::Lprim(PrimInfo {
                    primitive: Primitive::Pfield(_, _),
                    args,
                    ..
                }) if args.len() == 1 && matches!(args[0], Lambda::LglobalModule(_, _))
            );
            let subst_now = (info.times == 1 && !info.captured)
                || (info.times == 1
                    && info.captured
                    && matches!(l1.as_ref(), Lambda::Lconst(_) | Lambda::Lvar(_)))
                || small_const
                || pfield_from_global;

            if subst_now {
                let simplified = lets_helper_owned(state, *l1);
                state.subst.insert(v, simplified);
                return lets_helper_owned(state, *l2);
            }

            if let Lambda::Lconst(Constant::String { s, delim: None }) = l1.as_ref() {
                state.string_table.insert(v.clone(), s.clone());
                let simplified_body = lets_helper_owned(state, *l2);
                return Lambda::let_(LetKind::Alias, v, *l1, simplified_body);
            }

            let new_l1 = lets_helper_owned(state, *l1);
            let new_l2 = lets_helper_owned(state, *l2);
            Lambda::let_(LetKind::Alias, v, new_l1, new_l2)
        }

        Lambda::Llet(LetKind::StrictOpt, v, l1, lbody) => {
            if !state.used(&v) {
                return lets_helper_owned(state, *lbody);
            }

            if matches!(
                l1.as_ref(),
                Lambda::Lprim(PrimInfo {
                    primitive: Primitive::Pmakeblock( _, Mutable::Mutable),
                    args,
                    ..
                }) if args.len() == 1
            ) {
                let Lambda::Lprim(PrimInfo {
                    primitive,
                    mut args,
                    loc,
                }) = *l1
                else {
                    unreachable!()
                };
                let linit = args.pop().expect("checked one ref initializer");
                let slinit = lets_helper_owned(state, linit);
                let slbody = lets_helper_owned(state, *lbody);
                return match eliminate_ref(&v, &slbody) {
                    Ok(reified) => refine_let(LetKind::Variable, v, slinit, reified),
                    Err(RealReference) => refine_let(
                        LetKind::StrictOpt,
                        v,
                        Lambda::prim(primitive, vec![slinit], loc),
                        slbody,
                    ),
                };
            }

            let new_l1 = lets_helper_owned(state, *l1);
            if let Lambda::Lconst(Constant::String { s, delim: None }) = &new_l1 {
                state.string_table.insert(v.clone(), s.clone());
                let simplified_body = lets_helper_owned(state, *lbody);
                return Lambda::let_(LetKind::Alias, v, new_l1, simplified_body);
            }
            let simplified_body = lets_helper_owned(state, *lbody);
            refine_let(LetKind::StrictOpt, v, new_l1, simplified_body)
        }

        Lambda::Llet(kind @ (LetKind::Strict | LetKind::Variable), v, l1, l2) => {
            if !state.used(&v) {
                let new_l1 = lets_helper_owned(state, *l1);
                let new_l2 = lets_helper_owned(state, *l2);
                return if no_side_effects(&new_l1) {
                    new_l2
                } else {
                    Lambda::seq(new_l1, new_l2)
                };
            }
            let new_l1 = lets_helper_owned(state, *l1);
            if matches!(kind, LetKind::Strict) {
                if let Lambda::Lconst(Constant::String { s, delim: None }) = &new_l1 {
                    state.string_table.insert(v.clone(), s.clone());
                    let simplified_body = lets_helper_owned(state, *l2);
                    return Lambda::let_(LetKind::Alias, v, new_l1, simplified_body);
                }
            }
            let simplified_body = lets_helper_owned(state, *l2);
            refine_let(kind, v, new_l1, simplified_body)
        }

        Lambda::Lsequence(l1, l2) => {
            let s1 = lets_helper_owned(state, *l1);
            let s2 = lets_helper_owned(state, *l2);
            Lambda::seq(s1, s2)
        }

        Lambda::Lapply(apply) => {
            let Apply {
                ap_func,
                ap_args,
                ap_info,
                ap_transformed_jsx,
            } = apply;
            match *ap_func {
                Lambda::Lfunction(func)
                    if func.params.len() == ap_args.len() && lfunction_can_be_inlined(&func) =>
                {
                    let reduced = no_names_beta_reduce(&func.params, &func.body, &ap_args);
                    lets_helper_owned(state, reduced)
                }
                func => {
                    let new_func = lets_helper_owned(state, func);
                    let new_args = ap_args
                        .into_iter()
                        .map(|a| lets_helper_owned(state, a))
                        .collect();
                    Lambda::Lapply(Apply {
                        ap_func: Box::new(new_func),
                        ap_args: new_args,
                        ap_info,
                        ap_transformed_jsx,
                    })
                }
            }
        }

        Lambda::Lfunction(LFunction {
            arity,
            params,
            body,
            attr,
        }) => Lambda::Lfunction(LFunction {
            arity: arity,
            params: params,
            body: map_box(body, |inner| lets_helper_owned(state, inner)),
            attr: attr,
        }),

        Lambda::Lconst(_) | Lambda::LglobalModule(_, _) => lam,

        Lambda::Lletrec(bindings, body) => {
            let new_bindings = bindings
                .into_iter()
                .map(|(id, e)| (id, lets_helper_owned(state, e)))
                .collect();
            let new_body = lets_helper_owned(state, *body);
            Lambda::letrec(new_bindings, new_body)
        }

        Lambda::Lprim(PrimInfo {
            primitive: Primitive::Pstringadd,
            args,
            loc,
        }) if args.len() == 2 => {
            let mut args = args.into_iter();
            let l_simpl = lets_helper_owned(state, args.next().expect("checked left arg"));
            let r_simpl = lets_helper_owned(state, args.next().expect("checked right arg"));
            let opt_l = lookup_string(&l_simpl, &state.string_table);
            match opt_l {
                None => Lambda::prim(Primitive::Pstringadd, vec![l_simpl, r_simpl], loc),
                Some(l_s) => {
                    let opt_r = lookup_string(&r_simpl, &state.string_table);
                    match opt_r {
                        None => Lambda::prim(Primitive::Pstringadd, vec![l_simpl, r_simpl], loc),
                        Some(r_s) => Lambda::Lconst(Constant::String {
                            s: format!("{}{}", l_s, r_s),
                            delim: None,
                        }),
                    }
                }
            }
        }

        Lambda::Lprim(prim) => Lambda::prim(
            prim.primitive,
            prim.args
                .into_iter()
                .map(|a| lets_helper_owned(state, a))
                .collect(),
            prim.loc,
        ),

        Lambda::Lswitch(scrut, sw) => {
            let new_scrut = lets_helper_owned(state, *scrut);
            let new_consts = sw
                .sw_consts
                .into_iter()
                .map(|(n, e)| (n, lets_helper_owned(state, e)))
                .collect();
            let new_blocks = sw
                .sw_blocks
                .into_iter()
                .map(|(n, e)| (n, lets_helper_owned(state, e)))
                .collect();
            let new_failaction = sw
                .sw_failaction
                .map(|x| map_box(x, |inner| lets_helper_owned(state, inner)));
            Lambda::Lswitch(
                Box::new(new_scrut),
                LambdaSwitch {
                    sw_consts_full: sw.sw_consts_full,
                    sw_consts: new_consts,
                    sw_blocks_full: sw.sw_blocks_full,
                    sw_blocks: new_blocks,
                    sw_failaction: new_failaction,
                    sw_dispatch: sw.sw_dispatch,
                },
            )
        }

        Lambda::LstringSwitch(scrut, cases, default) => {
            let new_scrut = lets_helper_owned(state, *scrut);
            let new_cases = cases
                .into_iter()
                .map(|(s, e)| (s, lets_helper_owned(state, e)))
                .collect();
            let new_default = default.map(|x| map_box(x, |inner| lets_helper_owned(state, inner)));
            Lambda::LstringSwitch(Box::new(new_scrut), new_cases, new_default)
        }

        Lambda::LstaticRaise(i, args) => Lambda::LstaticRaise(
            i,
            args.into_iter()
                .map(|a| lets_helper_owned(state, a))
                .collect(),
        ),

        Lambda::LstaticCatch(l1, label, l2) => {
            let s1 = lets_helper_owned(state, *l1);
            let s2 = lets_helper_owned(state, *l2);
            Lambda::LstaticCatch(Box::new(s1), label, Box::new(s2))
        }

        Lambda::LtryWith(l1, v, l2) => {
            let s1 = lets_helper_owned(state, *l1);
            let s2 = lets_helper_owned(state, *l2);
            Lambda::LtryWith(Box::new(s1), v, Box::new(s2))
        }

        Lambda::LifThenElse(l1, l2, l3) => {
            let s1 = lets_helper_owned(state, *l1);
            let s2 = lets_helper_owned(state, *l2);
            let s3 = lets_helper_owned(state, *l3);
            Lambda::if_(s1, s2, s3)
        }

        Lambda::Lwhile(l1, l2) => {
            let s1 = lets_helper_owned(state, *l1);
            let s2 = lets_helper_owned(state, *l2);
            Lambda::Lwhile(Box::new(s1), Box::new(s2))
        }

        Lambda::Lfor(v, l1, l2, dir, l3) => {
            let s1 = lets_helper_owned(state, *l1);
            let s2 = lets_helper_owned(state, *l2);
            let s3 = lets_helper_owned(state, *l3);
            Lambda::Lfor(v, Box::new(s1), Box::new(s2), dir, Box::new(s3))
        }

        Lambda::Lfor_of(v, l1, l2) => {
            let s1 = lets_helper_owned(state, *l1);
            let s2 = lets_helper_owned(state, *l2);
            Lambda::for_of(v, s1, s2)
        }
        Lambda::Lfor_await_of(v, l1, l2) => {
            let s1 = lets_helper_owned(state, *l1);
            let s2 = lets_helper_owned(state, *l2);
            Lambda::for_await_of(v, s1, s2)
        }

        Lambda::Lassign(v, l) => {
            let s = lets_helper_owned(state, *l);
            Lambda::Lassign(v, Box::new(s))
        }

        Lambda::Lbreak => Lambda::break_(),
        Lambda::Lcontinue => Lambda::continue_(),
    }
}

/// Equivalent of OCaml's nested string-table lookup used by the Pstringadd
/// branch (lam_pass_lets_dce.ml:158-163, 167-172). Returns Some(s) when the
/// argument is an inline string literal or an alias for one.
fn lookup_string(lam: &Lambda, table: &HashMap<Ident, String>) -> Option<String> {
    match lam {
        Lambda::Lconst(Constant::String { s, delim: None }) => Some(s.clone()),
        Lambda::Lvar(i) => table.get(i).cloned(),
        _ => None,
    }
}

/// Direct port of `Lam_pass_lets_dce.simplify_lets` (lam_pass_lets_dce.ml:216-219).
pub fn simplify_lets(lam: &Lambda) -> Lambda {
    simplify_lets_owned(lam.clone())
}

/// Owned form of `Lam_pass_lets_dce.simplify_lets`
/// (compiler/core/lam_pass_lets_dce.ml:216-219).
pub fn simplify_lets_owned(lam: Lambda) -> Lambda {
    let occ = collect_occurs(&lam);
    let mut state = LetsState::new(&occ);
    lets_helper_owned(&mut state, lam)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ident::{Ident, IdentFlags};
    use crate::lambda::lam_compat::LetKind;
    use crate::lambda::lam_constant::Constant;

    fn ident(name: &str, stamp: i32) -> Ident {
        Ident::new(name, stamp, IdentFlags::NONE)
    }

    /// `let x = 1 in x` -> `1` via Alias single-use substitution
    /// (lam_pass_lets_dce.ml:50). Need an Alias kind to enter that arm.
    #[test]
    fn alias_single_use_const_substitutes() {
        let x = ident("x", 100);
        let lam = Lambda::let_(
            LetKind::Alias,
            x.clone(),
            Lambda::Lconst(Constant::int(1)),
            Lambda::Lvar(x),
        );
        let result = simplify_lets(&lam);
        assert!(matches!(result, Lambda::Lconst(Constant::Int { i: 1, .. })));
    }

    /// `let x = e in (); x` Alias unused -> drop binding
    /// (lam_pass_lets_dce.ml:49).
    #[test]
    fn alias_unused_binding_dropped() {
        let x = ident("x", 101);
        let other = ident("y", 102);
        let lam = Lambda::let_(
            LetKind::Alias,
            x,
            Lambda::Lconst(Constant::int(1)),
            Lambda::Lvar(other.clone()),
        );
        let result = simplify_lets(&lam);
        match result {
            Lambda::Lvar(id) => assert_eq!(id, other),
            other => panic!("expected Lvar, got {:?}", other),
        }
    }

    /// `let x = pure_e in (sequence)` Strict + unused + side-effect-free RHS
    /// -> drop the binding (lam_pass_lets_dce.ml:122-125).
    #[test]
    fn strict_unused_pure_dropped() {
        let x = ident("x", 103);
        let other = ident("y", 104);
        let lam = Lambda::let_(
            LetKind::Strict,
            x,
            Lambda::Lconst(Constant::int(7)),
            Lambda::Lvar(other.clone()),
        );
        let result = simplify_lets(&lam);
        match result {
            Lambda::Lvar(id) => assert_eq!(id, other),
            other => panic!("expected Lvar, got {:?}", other),
        }
    }

    /// `let x = "a" in let y = "b" in x ^ y` -> `"ab"` via string folding
    /// (lam_pass_lets_dce.ml:155-175).
    #[test]
    fn pstringadd_folds_through_string_table() {
        let x = ident("x", 105);
        let y = ident("y", 106);
        let concat = Lambda::prim(
            Primitive::Pstringadd,
            vec![Lambda::Lvar(x.clone()), Lambda::Lvar(y.clone())],
            crate::location::Location::none(),
        );
        let inner = Lambda::let_(
            LetKind::Alias,
            y,
            Lambda::Lconst(Constant::string("b")),
            concat,
        );
        let lam = Lambda::let_(
            LetKind::Alias,
            x,
            Lambda::Lconst(Constant::string("a")),
            inner,
        );
        let result = simplify_lets(&lam);
        // After folding the two inner alias substitutions, Pstringadd folds.
        // Outer let-bindings are dropped because their times become 0 once
        // their uses are inlined and the Alias clause prunes them.
        match result {
            Lambda::Lconst(Constant::String { s, delim: None }) => assert_eq!(s, "ab"),
            other => panic!("expected folded string, got {:?}", other),
        }
    }
}
