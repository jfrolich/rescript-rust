//! `Lam_beta_reduce` and `Lam_bounded_vars` over the Lambda arena.

use ahash::AHashMap as HashMap;

use crate::context::IdGenerator;
use crate::ident::Ident;
use crate::lambda::LamLoc;
use crate::lambda::arena::{Lam, LamArena, Node};
use crate::lambda::lam_analysis::no_side_effects;
use crate::lambda::lam_closure::StatsMap;
use crate::lambda::lam_compat::LetKind;
use crate::lambda::lam_pass_collect::kind_of_lambda_block;
use crate::lambda::lam_primitive::{Mutable, Primitive};
use crate::lambda::lam_stats::{IdKind, IdentTable};
use crate::lambda::lam_subst::Subst;
use crate::lambda::lam_util::refine_let;

/// `Lam_beta_reduce_util.simple_beta_reduce`: a body that is one primitive
/// or one call of a variable or module field, whose operands are variables
/// and constants each parameter fills at most once.
pub fn simple_beta_reduce(
    a: &mut LamArena,
    params: &[Ident],
    body: Lam,
    args: &[Lam],
) -> Option<Lam> {
    let indices: HashMap<Ident, usize> = params
        .iter()
        .enumerate()
        .map(|(index, param)| (*param, index))
        .collect();
    let n = params.len().min(args.len());
    let mut used = smallvec::SmallVec::<[bool; 8]>::from_elem(false, n);

    // `Some(Some(arg))`: the parameter's argument; `Some(None)`: not a
    // parameter; `None`: a parameter used twice.
    let take_param = |used: &mut [bool], x: &Ident| -> Option<Option<Lam>> {
        match indices.get(x).copied().filter(|i| *i < n) {
            Some(i) if used[i] => None,
            Some(i) => {
                used[i] = true;
                Some(Some(args[i]))
            }
            None => Some(None),
        }
    };
    let substitute_args =
        |a: &LamArena, used: &mut [bool], lams: &[Lam]| -> Option<smallvec::SmallVec<[Lam; 8]>> {
            let mut result = smallvec::SmallVec::with_capacity(lams.len());
            for &lam in lams {
                match a.node(lam) {
                    Node::Var(x) => result.push(take_param(used, &a.ident(x))?.unwrap_or(lam)),
                    Node::Const(_) => result.push(lam),
                    _ => return None,
                }
            }
            Some(result)
        };
    // `Lam_beta_reduce_util.seq_unused`: sequence the unused arguments
    // before the body, in parameter order.
    let wrap_unused = |a: &mut LamArena, used: &[bool], mut result: Lam| {
        for index in (0..n).rev() {
            if !used[index] {
                result = a.seq(args[index], result);
            }
        }
        result
    };

    match a.node(body) {
        Node::Prim { args: pargs, info } => {
            let new_args = substitute_args(a, &mut used, a.list(pargs))?;
            let new_args = a.add_list(&new_args);
            let result = a.prim_with(info, new_args);
            Some(wrap_unused(a, &used, result))
        }
        Node::Apply {
            func,
            args: fargs,
            info,
        } => {
            let simple_func = match a.node(func) {
                Node::Var(_) => true,
                Node::Prim { .. } => matches!(
                    a.as_prim(func),
                    Some((Primitive::Pfield(_, _), [m], _)) if matches!(a.node(*m), Node::GlobalModule(_))
                ),
                _ => false,
            };
            if !simple_func {
                return None;
            }
            let new_args = substitute_args(a, &mut used, a.list(fargs))?;
            let new_func = match a.node(func) {
                Node::Var(f) => take_param(&mut used, &a.ident(f))?.unwrap_or(func),
                _ => func,
            };
            let new_args = a.add_list(&new_args);
            let result = a.apply_raw_with(new_func, new_args, info);
            Some(wrap_unused(a, &used, result))
        }
        _ => None,
    }
}

/// `Lam_beta_reduce.no_names_beta_reduce`.
pub fn no_names_beta_reduce(a: &mut LamArena, params: &[Ident], body: Lam, args: &[Lam]) -> Lam {
    if let Some(result) = simple_beta_reduce(a, params, body, args) {
        return result;
    }
    let mut result = body;
    for (param, arg) in params.iter().zip(args) {
        result = refine_let(a, LetKind::Strict, *param, *arg, result);
    }
    result
}

/// `Lam_beta_reduce.propagate_beta_reduce` (lam_beta_reduce.ml:47-74).
pub fn propagate_beta_reduce(
    a: &mut LamArena,
    ident_tbl: &mut IdentTable,
    id_gen: &IdGenerator,
    params: &[Ident],
    body: Lam,
    args: &[Lam],
) -> Lam {
    propagate(a, ident_tbl, id_gen, None, params, body, args)
}

/// `Lam_beta_reduce.propagate_beta_reduce_with_map` (lam_beta_reduce.ml:76-115).
pub fn propagate_beta_reduce_with_map(
    a: &mut LamArena,
    ident_tbl: &mut IdentTable,
    id_gen: &IdGenerator,
    stats: &StatsMap,
    params: &[Ident],
    body: Lam,
    args: &[Lam],
) -> Lam {
    propagate(a, ident_tbl, id_gen, Some(stats), params, body, args)
}

fn propagate(
    a: &mut LamArena,
    ident_tbl: &mut IdentTable,
    id_gen: &IdGenerator,
    stats: Option<&StatsMap>,
    params: &[Ident],
    body: Lam,
    args: &[Lam],
) -> Lam {
    if let Some(result) = simple_beta_reduce(a, params, body, args) {
        return result;
    }
    let mut rest_bindings: smallvec::SmallVec<[(Ident, Lam); 8]> = smallvec::SmallVec::new();
    let mut substitution: Subst = HashMap::new();
    for (param, &arg) in params.iter().zip(args) {
        match a.node(arg) {
            Node::Const(_) | Node::Var(_) => {
                substitution.insert(*param, arg);
            }
            Node::GlobalModule(_) if stats.is_some() => {
                let new_param = param.rename(id_gen);
                rest_bindings.push((new_param, arg));
                let v = a.var(new_param);
                substitution.insert(*param, v);
            }
            _ => {
                if let Some(stats) = stats
                    && no_side_effects(a, arg)
                    && stats
                        .get(param)
                        .is_some_and(|stat| stat.top_and_used_zero_or_one())
                {
                    substitution.insert(*param, arg);
                    continue;
                }
                let new_param = param.rename(id_gen);
                let boxed = is_boxed_optional_binding(a, arg);
                let binding = if boxed {
                    a.prim(Primitive::Pidentity, &[arg], LamLoc::NONE)
                } else {
                    arg
                };
                rest_bindings.push((new_param, binding));
                let v = a.var(new_param);
                let replacement = if boxed {
                    a.prim(Primitive::Pidentity, &[v], LamLoc::NONE)
                } else {
                    v
                };
                substitution.insert(*param, replacement);
            }
        }
    }
    let mut result = rewrite_bounded_vars(a, &mut substitution, body, id_gen);
    // OCaml builds `rest_bindings` in reverse parameter order and folds it
    // left, making the first source argument's binding outermost.
    for (param, arg) in rest_bindings.into_iter().rev() {
        register_bound_param_kind(a, ident_tbl, &param, arg);
        result = refine_let(a, LetKind::Strict, param, arg, result);
    }
    result
}

/// The `meta.ident_tbl` update of `propagate_beta_reduce`
/// (lam_beta_reduce.ml:66-73, 107-114).
fn register_bound_param_kind(a: &LamArena, ident_tbl: &mut IdentTable, param: &Ident, arg: Lam) {
    match a.as_prim(arg) {
        Some((Primitive::Pmakeblock(_, Mutable::Immutable), args, _)) => {
            ident_tbl.insert(*param, kind_of_lambda_block(a, args));
        }
        Some((Primitive::Psome | Primitive::PsomeNotNest, [x], _)) => {
            ident_tbl.insert(*param, IdKind::NormalOptional(*x));
        }
        _ => {}
    }
}

fn is_boxed_optional_binding(a: &LamArena, arg: Lam) -> bool {
    matches!(
        a.as_prim(arg),
        Some((Primitive::PnullToOpt | Primitive::PnullUndefinedToOpt, _, _))
    )
}

/// `Lam_bounded_vars.rewrite`: substitute and give every binder of `lam` a
/// fresh name, rebuilding through the smart constructors.
fn rewrite_bounded_vars(a: &mut LamArena, s: &mut Subst, lam: Lam, id_gen: &IdGenerator) -> Lam {
    fn rebind(a: &mut LamArena, id: Ident, s: &mut Subst, id_gen: &IdGenerator) -> Ident {
        let renamed = id.rename(id_gen);
        let v = a.var(renamed);
        s.insert(id, v);
        renamed
    }
    let rw = |a: &mut LamArena, s: &mut Subst, x: Lam| rewrite_bounded_vars(a, s, x, id_gen);
    match a.node(lam) {
        Node::Var(id) => s.get(&a.ident(id)).copied().unwrap_or(lam),
        Node::Const(_) | Node::GlobalModule(_) => lam,
        Node::Apply { func, args, info } => {
            let func = rw(a, s, func);
            let args: smallvec::SmallVec<[Lam; 8]> =
                a.list_vec(args).into_iter().map(|x| rw(a, s, x)).collect();
            let p = a.apply_payload(info).clone();
            a.apply(func, &args, p.info)
        }
        Node::Function { body, info } => {
            let p = a.func_payload(info).clone();
            let params: smallvec::SmallVec<[Ident; 8]> = a
                .idents(p.params)
                .to_vec()
                .into_iter()
                .map(|x| rebind(a, x, s, id_gen))
                .collect();
            let body = rw(a, s, body);
            a.function_(p.arity, &params, body, p.attr, p.loc)
        }
        Node::Let {
            kind,
            id,
            value,
            body,
        } => {
            let id = rebind(a, a.ident(id), s, id_gen);
            let value = rw(a, s, value);
            let body = rw(a, s, body);
            a.let_(kind, id, value, body)
        }
        Node::LetRec { ids, values, body } => {
            let values = a.list_vec(values);
            let old: smallvec::SmallVec<[Ident; 8]> =
                a.ident_run(ids, values.len()).iter().copied().collect();
            let renamed: smallvec::SmallVec<[Ident; 8]> =
                old.into_iter().map(|x| rebind(a, x, s, id_gen)).collect();
            let bindings: smallvec::SmallVec<[(Ident, Lam); 8]> = renamed
                .into_iter()
                .zip(values)
                .map(|(id, x)| (id, rw(a, s, x)))
                .collect();
            let body = rw(a, s, body);
            a.letrec(&bindings, body)
        }
        Node::Prim { args, info } => {
            let args: smallvec::SmallVec<[Lam; 8]> =
                a.list_vec(args).into_iter().map(|x| rw(a, s, x)).collect();
            let args = a.add_list(&args);
            a.prim_with(info, args)
        }
        Node::Switch {
            scrut,
            actions,
            info,
        } => {
            let scrut = rw(a, s, scrut);
            let actions: smallvec::SmallVec<[Lam; 8]> = a
                .list_vec(actions)
                .into_iter()
                .map(|x| rw(a, s, x))
                .collect();
            let actions = a.add_list(&actions);
            a.switch_with(scrut, actions, info)
        }
        Node::StringSwitch {
            scrut,
            actions,
            info,
        } => {
            let scrut = rw(a, s, scrut);
            let actions: smallvec::SmallVec<[Lam; 8]> = a
                .list_vec(actions)
                .into_iter()
                .map(|x| rw(a, s, x))
                .collect();
            let actions = a.add_list(&actions);
            a.string_switch_with(scrut, actions, info)
        }
        Node::StaticRaise { label, args } => {
            let args: smallvec::SmallVec<[Lam; 8]> =
                a.list_vec(args).into_iter().map(|x| rw(a, s, x)).collect();
            a.static_raise(label, &args)
        }
        Node::StaticCatch {
            body,
            handler,
            info,
        } => {
            let body = rw(a, s, body);
            let p = a.catch_payload(info);
            let vars: smallvec::SmallVec<[Ident; 8]> = a
                .idents(p.params)
                .to_vec()
                .into_iter()
                .map(|x| rebind(a, x, s, id_gen))
                .collect();
            let handler = rw(a, s, handler);
            a.static_catch(body, p.label, &vars, handler)
        }
        Node::TryWith { body, id, handler } => {
            let body = rw(a, s, body);
            let exn = rebind(a, a.ident(id), s, id_gen);
            let handler = rw(a, s, handler);
            a.try_(body, exn, handler)
        }
        // lam_bounded_vars.ml: `let l1 = aux l1 in let l2 = aux l2 in try_finally l1 l2`.
        Node::TryFinally { body, finally } => {
            let body = rw(a, s, body);
            let finally = rw(a, s, finally);
            a.try_finally(body, finally)
        }
        Node::If { cond, then_, else_ } => {
            let cond = rw(a, s, cond);
            let then_ = rw(a, s, then_);
            let else_ = rw(a, s, else_);
            a.if_(cond, then_, else_)
        }
        Node::Sequence(x, y) => {
            let x = rw(a, s, x);
            let y = rw(a, s, y);
            a.seq(x, y)
        }
        Node::While(x, y) => {
            let x = rw(a, s, x);
            let y = rw(a, s, y);
            a.while_(x, y)
        }
        Node::For { dir, id, kids } => {
            let (from, to, body) = a.for_parts(kids);
            let id = rebind(a, a.ident(id), s, id_gen);
            let from = rw(a, s, from);
            let to = rw(a, s, to);
            let body = rw(a, s, body);
            // lam_bounded_vars.ml: `Lambda.for_ ident (aux l1) l2 dir l3`
            // rewrites the already rewritten start expression once more.
            let from = rw(a, s, from);
            a.for_(id, from, to, dir, body)
        }
        Node::ForOf { id, iter, body } => {
            let id = rebind(a, a.ident(id), s, id_gen);
            let iter = rw(a, s, iter);
            let body = rw(a, s, body);
            a.for_of(id, iter, body)
        }
        Node::ForAwaitOf { id, iter, body } => {
            let id = rebind(a, a.ident(id), s, id_gen);
            let iter = rw(a, s, iter);
            let body = rw(a, s, body);
            a.for_await_of(id, iter, body)
        }
        Node::Break | Node::Continue => lam,
        Node::Assign { id, value } => {
            let value = rw(a, s, value);
            a.assign_with(id, value)
        }
    }
}

/// The largest identifier stamp in `lam`.
pub(crate) fn max_ident_stamp_in_lambda(a: &LamArena, lam: Lam) -> i32 {
    let own = match a.node(lam) {
        Node::Var(id)
        | Node::GlobalModule(id)
        | Node::Let { id, .. }
        | Node::TryWith { id, .. }
        | Node::For { id, .. }
        | Node::ForOf { id, .. }
        | Node::ForAwaitOf { id, .. }
        | Node::Assign { id, .. } => a.ident(id).stamp(),
        Node::Function { info, .. } => a.params(info).iter().map(Ident::stamp).max().unwrap_or(0),
        Node::LetRec { ids, values, .. } => a
            .ident_run(ids, a.list_len(values))
            .iter()
            .map(Ident::stamp)
            .max()
            .unwrap_or(0),
        Node::StaticCatch { info, .. } => a
            .idents(a.catch_payload(info).params)
            .iter()
            .map(Ident::stamp)
            .max()
            .unwrap_or(0),
        _ => 0,
    };
    let mut max = own;
    a.iter_children(lam, |x| max = max.max(max_ident_stamp_in_lambda(a, x)));
    max
}

#[cfg(test)]
mod regression_tests {
    use super::*;
    use crate::ident::IdentFlags;
    fn ids(start: i32, count: usize) -> Vec<Ident> {
        (0..count)
            .map(|i| Ident::new(format!("p{i}"), start + i as i32, IdentFlags::NONE))
            .collect()
    }
    fn effect(name: &str) -> crate::lambda::Lambda {
        crate::lambda::Lambda::prim(
            Primitive::PjsCall(Box::new(crate::lambda::lam_primitive::JsCall {
                prim_name: name.into(),
                arg_types: vec![],
                ffi: crate::lambda::lam_primitive::ExternalDecl::test_val("", 0),
            })),
            vec![],
            LamLoc::NONE,
        )
    }
    #[test]
    fn unused_effectful_arguments_are_evaluated_in_parameter_order() {
        let params = ids(1, 3);
        let body = crate::lambda::Lambda::prim(
            Primitive::Pidentity,
            vec![crate::lambda::Lambda::var(params[0])],
            LamLoc::NONE,
        );
        let mut store = LamArena::new();
        let root = store.import(&body);
        let args: Vec<_> = ["a", "b", "c"]
            .into_iter()
            .map(|name| store.import(&effect(name)))
            .collect();
        let reduced = simple_beta_reduce(&mut store, &params, root, &args).unwrap();
        let mut names = Vec::new();
        let mut current = store.export(reduced);
        while let crate::lambda::Lambda::Lsequence(first, rest) = current {
            if let crate::lambda::Lambda::Lprim(info) = *first
                && let Primitive::PjsCall(call) = info.primitive
            {
                names.push(call.prim_name);
            }
            current = *rest;
        }
        assert_eq!(names, vec!["b", "c"]);
    }
}
