//! `Lam_pass_remove_alias.simplify_alias` over the Lambda arena: field
//! folding, optional unwrapping, boolean folding and function inlining from
//! the metadata `Lam_pass_collect` recorded.

use crate::ident::Ident;
use crate::lambda::LamLoc;
use crate::lambda::arena::{Lam, LamArena, Node};
use crate::lambda::lam_analysis::{lfunction_can_be_inlined, ok_to_inline_fun_when_app};
use crate::lambda::lam_beta_reduce::{propagate_beta_reduce, propagate_beta_reduce_with_map};
use crate::lambda::lam_closure::is_closed_with_map;
use crate::lambda::lam_compat::{Comparison, FieldDbgInfo};
use crate::lambda::lam_compile_context::{BoxedNullable, RecFlag};
use crate::lambda::lam_constant::Constant;
use crate::lambda::lam_hit::hit_variable;
use crate::lambda::lam_primitive::Primitive;
use crate::lambda::lam_stats::{IdKind, IdentTable, LamStats};
use crate::lambda::lam_tag_info::TagInfo;
use crate::lambda::lam_util::field_flatten_get;
use crate::lambda::{ApInfo, Lambda};

/// Rust counterpart to `Lam_compile_env.query_external_id_info` used by
/// `Lam_pass_remove_alias.simplify_alias` (lam_pass_remove_alias.ml:143-159).
pub type ExternalInlineResolver<'a> = dyn FnMut(&Ident, &str) -> Option<Lambda> + 'a;

/// `Lam_pass_remove_alias.outcome` (lam_pass_remove_alias.ml:25).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Outcome {
    EvalFalse,
    EvalTrue,
    EvalUnknown,
}

/// `id_is_for_sure_true_in_boolean` (lam_pass_remove_alias.ml:27-42).
fn id_is_for_sure_true_in_boolean(a: &LamArena, tbl: &IdentTable, id: &Ident) -> Outcome {
    let falsy = |c: &Constant| {
        matches!(
            c,
            Constant::JsFalse | Constant::JsNull | Constant::JsUndefined { .. }
        )
    };
    match tbl.get(id) {
        Some(IdKind::NormalOptional(l)) if a.as_const(*l).is_some_and(falsy) => Outcome::EvalFalse,
        Some(IdKind::Constant(c)) => match a.constant(*c) {
            Constant::JsTrue => Outcome::EvalTrue,
            Constant::Int { i, .. } => {
                if *i == 0 {
                    Outcome::EvalFalse
                } else {
                    Outcome::EvalTrue
                }
            }
            c if falsy(c) => Outcome::EvalFalse,
            _ => Outcome::EvalUnknown,
        },
        _ => Outcome::EvalUnknown,
    }
}

/// `is_const_some` (lam_pass_remove_alias.ml:44-48).
fn is_const_some(cst: &Constant) -> bool {
    match cst {
        Constant::Some(_) => true,
        Constant::Block { tag_info, .. } => {
            matches!(&**tag_info, TagInfo::Some | TagInfo::SomeNotNested)
        }
        _ => false,
    }
}

/// `Lam.not_` (lam.ml:584-588).
fn lam_not(a: &mut LamArena, loc: LamLoc, x: Lam) -> Lam {
    if let Node::Prim { args, info } = a.node(x)
        && matches!(
            a.prim_payload(info).primitive,
            Primitive::Pintcomp(Comparison::Neq)
        )
    {
        let l = a.prim_payload(info).loc;
        let info = a.add_prim(Primitive::Pintcomp(Comparison::Eq), l);
        return a.prim_raw_with(info, args);
    }
    a.prim(Primitive::Pnot, &[x], loc)
}

/// The module and field of `Pfield(_, Fld_module name) [Lglobal_module id]`.
fn module_field_apply_target(a: &LamArena, lam: Lam) -> Option<(Ident, crate::name::Name)> {
    let (Primitive::Pfield(_, FieldDbgInfo::Module { name }), [m], _) = a.as_prim(lam)? else {
        return None;
    };
    match a.node(*m) {
        Node::GlobalModule(id) => Some((a.ident(id), *name)),
        _ => None,
    }
}

fn external_inline_args_are_allowed(a: &LamArena, args: &[Lam], ident_tbl: &IdentTable) -> bool {
    args.iter().all(|arg| match a.as_var(*arg) {
        Some(param) => !matches!(ident_tbl.get(&param), Some(IdKind::Parameter)),
        None => true,
    })
}

/// `Lam_pass_remove_alias.simplify_alias` (lam_pass_remove_alias.ml:50-290).
pub fn simplify_alias(
    a: &mut LamArena,
    meta: &mut LamStats,
    lam: Lam,
    jsx_preserve: bool,
    external_inline: &mut ExternalInlineResolver<'_>,
) -> Lam {
    let export_idents = std::mem::take(&mut meta.export_idents);
    let id_gen = meta.id_gen.clone();
    let result = Simplifier {
        ident_tbl: &mut meta.ident_tbl,
        export_idents: &export_idents,
        id_gen: &id_gen,
        jsx_preserve,
        external_inline,
    }
    .simpl(a, lam);
    meta.export_idents = export_idents;
    result
}

struct Simplifier<'a, 'r> {
    ident_tbl: &'a mut IdentTable,
    export_idents: &'a ahash::AHashSet<Ident>,
    id_gen: &'a crate::context::IdGenerator,
    jsx_preserve: bool,
    external_inline: &'a mut ExternalInlineResolver<'r>,
}

impl Simplifier<'_, '_> {
    fn simpl_children(&mut self, a: &mut LamArena, lam: Lam) -> Lam {
        a.shallow_map(lam, &mut |a, x| self.simpl(a, x))
    }

    /// `Lam_pass_remove_alias.simplify_alias.simpl`
    /// (lam_pass_remove_alias.ml:49-247). Returns `lam` itself when nothing
    /// was rewritten, as OCaml's physical sharing does.
    fn simpl(&mut self, a: &mut LamArena, lam: Lam) -> Lam {
        match a.node(lam) {
            Node::Prim { args, info } => self.simpl_prim(a, lam, args, info),
            Node::If { cond, then_, else_ } => {
                // `if Pis_not_none v then ...`
                if let Some((Primitive::PisNotNone, [v], _)) = a.as_prim(cond)
                    && let Some(id) = a.as_var(*v)
                {
                    match self.ident_tbl.get(&id) {
                        Some(IdKind::Constant(c)) if is_const_some(a.constant(*c)) => {
                            return self.simpl(a, then_);
                        }
                        Some(
                            IdKind::ImmutableBlock(_)
                            | IdKind::MutableBlock(_)
                            | IdKind::NormalOptional(_),
                        ) => return self.simpl(a, then_),
                        Some(IdKind::OptionalBlock(l, nullable)) => {
                            let (l, nullable) = (*l, *nullable);
                            let primitive = match nullable {
                                BoxedNullable::Null => Primitive::PisNull,
                                BoxedNullable::Undefined => Primitive::PisUndefined,
                                BoxedNullable::NullUndefined => Primitive::PisNullUndefined,
                            };
                            let then_ = self.simpl(a, then_);
                            let else_ = self.simpl(a, else_);
                            let test = a.prim(primitive, &[l], LamLoc::NONE);
                            let test = lam_not(a, LamLoc::NONE, test);
                            return a.if_(test, then_, else_);
                        }
                        _ => return self.simpl_children(a, lam),
                    }
                }
                if let Some(id) = a.as_var(cond) {
                    return match id_is_for_sure_true_in_boolean(a, self.ident_tbl, &id) {
                        Outcome::EvalTrue => self.simpl(a, then_),
                        Outcome::EvalFalse => self.simpl(a, else_),
                        Outcome::EvalUnknown => self.simpl_children(a, lam),
                    };
                }
                self.simpl_children(a, lam)
            }
            Node::Apply { func, args, info } => self.simpl_apply(a, lam, func, args, info),
            Node::StringSwitch {
                scrut,
                actions,
                info,
            } => {
                if let Some(s) = a.as_var(scrut)
                    && let Some(IdKind::Constant(c)) = self.ident_tbl.get(&s)
                {
                    // Switch on the constant the scrutinee is bound to.
                    let c = *c;
                    let (actions, _) = a.map_list(actions, &mut |a, x| self.simpl(a, x));
                    let scrut = a.push(Node::Const(c));
                    return a.string_switch_with(scrut, actions, info);
                }
                self.simpl_children(a, lam)
            }
            _ => self.simpl_children(a, lam),
        }
    }

    fn simpl_prim(
        &mut self,
        a: &mut LamArena,
        lam: Lam,
        args: crate::lambda::arena::LamList,
        info: crate::lambda::arena::PrimId,
    ) -> Lam {
        let primitive = &a.prim_payload(info).primitive;
        // 7432: no optimization of the component of a JSX call in preserve
        // mode.
        if self.jsx_preserve
            && matches!(primitive, Primitive::PjsCall(call)
                if call.prim_name == "jsx" || call.prim_name == "jsxs")
            && a.list(args)
                .first()
                .is_some_and(|f| matches!(a.as_prim(*f), Some((Primitive::Pfield(_, _), _, _))))
        {
            let all = a.list_vec(args);
            let mut changed = false;
            let mut out = smallvec::SmallVec::<[Lam; 8]>::with_capacity(all.len());
            out.push(all[0]);
            for &x in &all[1..] {
                let y = self.simpl(a, x);
                changed |= y != x;
                out.push(y);
            }
            if !changed {
                return lam;
            }
            let args = a.add_list(&out);
            return a.prim_with(info, args);
        }
        match primitive {
            Primitive::Pfield(i, field_info) if a.list_len(args) == 1 => {
                let (i, field_info) = (*i, *field_info);
                let arg = a.list(args)[0];
                let new_arg = self.simpl(a, arg);
                let rebuild = |a: &mut LamArena| {
                    if new_arg == arg {
                        lam
                    } else {
                        let args = a.add_list(&[new_arg]);
                        a.prim_with(info, args)
                    }
                };
                match a.as_var(new_arg) {
                    Some(v) => field_flatten_get(a, rebuild, &v, i, &field_info, self.ident_tbl),
                    None => rebuild(a),
                }
            }
            Primitive::PvalFromOption | Primitive::PvalFromOptionNotNest if matches!(a.list(args), [x] if matches!(a.node(*x), Node::Var(_))) =>
            {
                let not_nest = matches!(primitive, Primitive::PvalFromOptionNotNest);
                let x = a.list(args)[0];
                let v = a.as_var(x).expect("checked variable");
                match self.ident_tbl.get(&v) {
                    Some(IdKind::OptionalBlock(l, _)) => *l,
                    _ if not_nest => x,
                    _ => lam,
                }
            }
            _ => self.simpl_children(a, lam),
        }
    }

    fn beta(&mut self, a: &mut LamArena, params: &[Ident], body: Lam, args: &[Lam]) -> Lam {
        propagate_beta_reduce(a, self.ident_tbl, self.id_gen, params, body, args)
    }

    fn simpl_apply(
        &mut self,
        a: &mut LamArena,
        lam: Lam,
        func: Lam,
        args: crate::lambda::arena::LamList,
        info: crate::lambda::arena::ApplyId,
    ) -> Lam {
        // Cross-module inlining (lam_pass_remove_alias.ml:131-162).
        if let Some((module_id, field_name)) = module_field_apply_target(a, func) {
            let arg_list = a.list_vec(args);
            if let Some(Lambda::Lfunction(f)) = (self.external_inline)(&module_id, field_name.as_str())
                && f.params.len() == arg_list.len()
                && external_inline_args_are_allowed(a, &arg_list, self.ident_tbl)
                && crate::lambda::lam_analysis::attr_can_be_inlined(&f.attr)
            {
                let body = a.import(&f.body);
                let reduced = self.beta(a, &f.params, body, &arg_list);
                return self.simpl(a, reduced);
            }
            // `Lambda.apply fn args' ap_info ?ap_transformed_jsx:None`.
            let nf = self.simpl(a, func);
            let (nargs, changed) = a.map_list(args, &mut |a, x| self.simpl(a, x));
            if nf == func && !changed {
                return lam;
            }
            let ap_info: ApInfo = a.apply_payload(info).info.clone();
            let nargs = a.list_vec(nargs);
            return a.apply(nf, &nargs, ap_info, false);
        }
        match a.node(func) {
            Node::Var(v) => {
                let v = a.ident(v);
                let (nargs, args_changed) = a.map_list(args, &mut |a, x| self.simpl(a, x));
                let normal = |this: &mut Self, a: &mut LamArena| {
                    let nf = this.simpl(a, func);
                    if nf == func && !args_changed {
                        lam
                    } else {
                        a.apply_with(nf, nargs, info)
                    }
                };
                let func_info = match self.ident_tbl.get(&v) {
                    Some(IdKind::FunctionId {
                        lambda: Some((f, rec_flag)),
                        ..
                    }) => match a.node(*f) {
                        Node::Function { body, info: fi } if lfunction_can_be_inlined(a, fi) => {
                            Some((fi, body, *rec_flag))
                        }
                        _ => None,
                    },
                    _ => None,
                };
                let Some((fi, body, rec_flag)) = func_info else {
                    return normal(self, a);
                };
                let arg_list = a.list_vec(nargs);
                let params: smallvec::SmallVec<[Ident; 8]> = a.params(fi).iter().copied().collect();
                if arg_list.len() != params.len() {
                    return normal(self, a);
                }
                if a.func_payload(fi).attr.is_a_functor {
                    let reduced = self.beta(a, &params, body, &arg_list);
                    return self.simpl(a, reduced);
                }
                if !ok_to_inline_fun_when_app(a, fi, body, &arg_list) {
                    return normal(self, a);
                }
                let (param_ok, param_map) =
                    is_closed_with_map(a, self.export_idents, &params, body);
                if self.export_idents.contains(&v) && !param_ok {
                    return normal(self, a);
                }
                match rec_flag {
                    RecFlag::Rec => propagate_beta_reduce_with_map(
                        a,
                        self.ident_tbl,
                        self.id_gen,
                        &param_map,
                        &params,
                        body,
                        &arg_list,
                    ),
                    RecFlag::SelfRec => normal(self, a),
                    RecFlag::NonRec => {
                        if arg_list.iter().any(|x| hit_variable(a, &v, *x)) {
                            normal(self, a)
                        } else {
                            let reduced = propagate_beta_reduce_with_map(
                                a,
                                self.ident_tbl,
                                self.id_gen,
                                &param_map,
                                &params,
                                body,
                                &arg_list,
                            );
                            self.simpl(a, reduced)
                        }
                    }
                }
            }
            Node::Function { body, info: fi }
                if a.params(fi).len() == a.list_len(args) && lfunction_can_be_inlined(a, fi) =>
            {
                let params: smallvec::SmallVec<[Ident; 8]> = a.params(fi).iter().copied().collect();
                let arg_list = a.list_vec(args);
                let reduced = self.beta(a, &params, body, &arg_list);
                self.simpl(a, reduced)
            }
            _ => self.simpl_children(a, lam),
        }
    }
}
