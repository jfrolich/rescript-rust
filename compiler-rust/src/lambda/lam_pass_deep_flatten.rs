//! Direct port of `compiler/core/lam_pass_deep_flatten.ml`.
//!
//! Flattens nested `Llet` chains and pulls projected tuple/record fields out
//! of named module-block bindings so downstream passes see a flat sequence of
//! single bindings. Mirrors `Lam_pass_deep_flatten.deep_flatten`.

use std::collections::HashMap;

use crate::ident::Ident;
use crate::lambda::lam_compat::LetKind;
use crate::lambda::lam_util::refine_let;
use crate::lambda::lam_primitive::{Mutable, Primitive};
use crate::lambda::{Apply, Lambda, LambdaSwitch, PrimInfo};
use crate::location::Location;

#[derive(Clone)]
enum FlattenGroup {
    Single(LetKind, Ident, Lambda),
    Recursive(Vec<(Ident, Lambda)>),
    Nop(Lambda),
}

/// Direct port of `Lam_pass_deep_flatten.deep_flatten`
/// (compiler/core/lam_pass_deep_flatten.ml).
pub fn deep_flatten(lam: &Lambda) -> Lambda {
    fn lambda_of_groups(rev_bindings: Vec<FlattenGroup>, result: Lambda) -> Lambda {
        // lam_pass_deep_flatten.ml:108 — fold each Single back through
        // `Lam_util.refine_let` so Strict bindings whose RHS is safe to alias
        // (e.g. module field reads) are downgraded to Alias. Without this the
        // later `simplify_lets` Alias arm cannot inline single-use bindings.
        rev_bindings
            .into_iter()
            .fold(result, |acc, group| match group {
                FlattenGroup::Single(kind, ident, lam) => refine_let(kind, ident, lam, acc),
                FlattenGroup::Recursive(bindings) => Lambda::letrec(bindings, acc),
                FlattenGroup::Nop(lam) => Lambda::seq(lam, acc),
            })
    }

    fn hit_variable(target: &Ident, lam: &Lambda) -> bool {
        match lam {
            Lambda::Lvar(id) => id.same(target),
            Lambda::LglobalModule(_, _) | Lambda::Lconst(_) => false,
            Lambda::Lapply(apply) => {
                hit_variable(target, &apply.ap_func)
                    || apply.ap_args.iter().any(|arg| hit_variable(target, arg))
            }
            Lambda::Lfunction(func) => hit_variable(target, &func.body),
            Lambda::Llet(_, _, value, body) => {
                hit_variable(target, value) || hit_variable(target, body)
            }
            Lambda::Lletrec(bindings, body) => {
                hit_variable(target, body)
                    || bindings.iter().any(|(_, lam)| hit_variable(target, lam))
            }
            Lambda::Lprim(info) => info.args.iter().any(|arg| hit_variable(target, arg)),
            Lambda::Lswitch(arg, switch) => {
                hit_variable(target, arg)
                    || switch
                        .sw_consts
                        .iter()
                        .any(|(_, lam)| hit_variable(target, lam))
                    || switch
                        .sw_blocks
                        .iter()
                        .any(|(_, lam)| hit_variable(target, lam))
                    || switch
                        .sw_failaction
                        .as_deref()
                        .is_some_and(|lam| hit_variable(target, lam))
            }
            Lambda::LstringSwitch(arg, cases, default) => {
                hit_variable(target, arg)
                    || cases.iter().any(|(_, lam)| hit_variable(target, lam))
                    || default
                        .as_deref()
                        .is_some_and(|lam| hit_variable(target, lam))
            }
            Lambda::LstaticRaise(_, args) => args.iter().any(|arg| hit_variable(target, arg)),
            Lambda::LstaticCatch(body, _, handler) | Lambda::LtryWith(body, _, handler) => {
                hit_variable(target, body) || hit_variable(target, handler)
            }
            Lambda::LifThenElse(cond, then_, else_) => {
                hit_variable(target, cond)
                    || hit_variable(target, then_)
                    || hit_variable(target, else_)
            }
            Lambda::Lsequence(first, second) | Lambda::Lwhile(first, second) => {
                hit_variable(target, first) || hit_variable(target, second)
            }
            Lambda::Lfor(_, start, end, _, body) => {
                hit_variable(target, start)
                    || hit_variable(target, end)
                    || hit_variable(target, body)
            }
            Lambda::Lfor_of(_, iterable, body) | Lambda::Lfor_await_of(_, iterable, body) => {
                hit_variable(target, iterable) || hit_variable(target, body)
            }
            Lambda::Lbreak | Lambda::Lcontinue => false,
            Lambda::Lassign(id, value) => id.same(target) || hit_variable(target, value),
        }
    }

    fn eliminate_tuple(
        id: &Ident,
        lam: &Lambda,
        tuple_mapping: HashMap<i32, Ident>,
    ) -> Option<(HashMap<i32, Ident>, Lambda)> {
        match lam {
            Lambda::Llet(LetKind::Alias, projected, value, body)
                if matches!(
                    &**value,
                    Lambda::Lprim(PrimInfo {
                        primitive: Primitive::Pfield(_, _),
                        args,
                        ..
                    }) if matches!(args.as_slice(), [Lambda::Lvar(tuple)] if tuple.same(id))
                ) =>
            {
                let Lambda::Lprim(PrimInfo {
                    primitive: Primitive::Pfield(index, _),
                    ..
                }) = &**value
                else {
                    unreachable!();
                };
                let mut tuple_mapping = tuple_mapping;
                tuple_mapping.insert(*index, projected.clone());
                eliminate_tuple(id, body, tuple_mapping)
            }
            _ => {
                if hit_variable(id, lam) {
                    None
                } else {
                    Some((tuple_mapping, lam.clone()))
                }
            }
        }
    }

    fn flatten(acc: Vec<FlattenGroup>, lam: &Lambda) -> (Lambda, Vec<FlattenGroup>) {
        match lam {
            Lambda::Llet(kind, id, value, body)
                if matches!(
                    value.as_ref(),
                    Lambda::Lprim(PrimInfo {
                        primitive: Primitive::PnullToOpt | Primitive::PnullUndefinedToOpt,
                        args,
                        ..
                    }) if matches!(args.as_slice(), [Lambda::Lvar(_)])
                ) =>
            {
                let res = aux(value);
                let mut next_acc = Vec::with_capacity(acc.len() + 1);
                next_acc.push(FlattenGroup::Single(*kind, id.clone(), res));
                next_acc.extend(acc);
                flatten(next_acc, body)
            }
            Lambda::Llet(kind, id, value, body) => {
                if let Lambda::Lprim(PrimInfo {
                    primitive, args, ..
                }) = value.as_ref()
                {
                    if matches!(
                        primitive,
                        Primitive::PnullToOpt | Primitive::PnullUndefinedToOpt
                    ) && matches!(args.as_slice(), [arg] if !matches!(arg, Lambda::Lvar(_)))
                    {
                        let [arg] = args.as_slice() else {
                            unreachable!();
                        };
                        let new_id = Ident::create_local(id.name().to_string());
                        let lowered = Lambda::let_(
                            *kind,
                            new_id.clone(),
                            arg.clone(),
                            Lambda::let_(
                                LetKind::Alias,
                                id.clone(),
                                Lambda::prim(
                                    primitive.clone(),
                                    vec![Lambda::var(new_id)],
                                    Location::none(),
                                ),
                                body.as_ref().clone(),
                            ),
                        );
                        return flatten(acc, &lowered);
                    }
                }

                let (res, accux) = flatten(acc, value);
                let flatten_named_module_block = matches!(
                    (id.name(), *kind, &res),
                    (
                        "match" | "include" | "param",
                        LetKind::Alias | LetKind::Strict | LetKind::StrictOpt,
                        Lambda::Lprim(PrimInfo {
                            primitive: Primitive::Pmakeblock(_, _, Mutable::Immutable),
                            ..
                        })
                    )
                );
                if flatten_named_module_block {
                    let Lambda::Lprim(PrimInfo { args, .. }) = &res else {
                        unreachable!();
                    };
                    if let Some((tuple_mapping, stripped_body)) =
                        eliminate_tuple(id, body, HashMap::new())
                    {
                        let mut flattened_args = args
                            .iter()
                            .enumerate()
                            .map(|(index, arg)| match tuple_mapping.get(&(index as i32)) {
                                Some(projected) => {
                                    FlattenGroup::Single(*kind, projected.clone(), arg.clone())
                                }
                                None => FlattenGroup::Nop(arg.clone()),
                            })
                            .collect::<Vec<_>>();
                        flattened_args.reverse();
                        flattened_args.extend(accux);
                        return flatten(flattened_args, &stripped_body);
                    }
                }

                let mut next_acc = Vec::with_capacity(accux.len() + 1);
                next_acc.push(FlattenGroup::Single(*kind, id.clone(), res));
                next_acc.extend(accux);
                flatten(next_acc, body)
            }
            Lambda::Lletrec(bindings, body) => {
                let bindings = bindings
                    .iter()
                    .map(|(id, expr)| (id.clone(), aux(expr)))
                    .collect();
                let mut next_acc = Vec::with_capacity(acc.len() + 1);
                next_acc.push(FlattenGroup::Recursive(bindings));
                next_acc.extend(acc);
                flatten(next_acc, body)
            }
            Lambda::Lsequence(first, second) => {
                let (res, first_acc) = flatten(acc, first);
                let mut next_acc = Vec::with_capacity(first_acc.len() + 1);
                next_acc.push(FlattenGroup::Nop(res));
                next_acc.extend(first_acc);
                flatten(next_acc, second)
            }
            _ => (aux(lam), acc),
        }
    }

    fn aux(lam: &Lambda) -> Lambda {
        match lam {
            Lambda::Llet(_, _, _, _) => {
                let (result, groups) = flatten(Vec::new(), lam);
                lambda_of_groups(groups, result)
            }
            Lambda::Lletrec(bindings, body) => Lambda::letrec(
                bindings
                    .iter()
                    .map(|(id, expr)| (id.clone(), aux(expr)))
                    .collect(),
                aux(body),
            ),
            Lambda::Lsequence(first, second) => Lambda::seq(aux(first), aux(second)),
            Lambda::Lvar(_) | Lambda::LglobalModule(_, _) | Lambda::Lconst(_) => lam.clone(),
            Lambda::Lapply(apply) => Lambda::Lapply(Apply {
                ap_func: Box::new(aux(&apply.ap_func)),
                ap_args: apply.ap_args.iter().map(aux).collect(),
                ap_info: apply.ap_info.clone(),
                ap_transformed_jsx: apply.ap_transformed_jsx,
            }),
            Lambda::Lfunction(func) => Lambda::function_(
                func.arity,
                func.params.clone(),
                aux(&func.body),
                func.attr.clone(),
            ),
            Lambda::Lprim(info) => Lambda::prim(
                info.primitive.clone(),
                info.args.iter().map(aux).collect(),
                info.loc.clone(),
            ),
            Lambda::Lswitch(scrutinee, switch) => Lambda::Lswitch(
                Box::new(aux(scrutinee)),
                LambdaSwitch {
                    sw_consts_full: switch.sw_consts_full,
                    sw_consts: switch
                        .sw_consts
                        .iter()
                        .map(|(tag, lam)| (*tag, aux(lam)))
                        .collect(),
                    sw_blocks_full: switch.sw_blocks_full,
                    sw_blocks: switch
                        .sw_blocks
                        .iter()
                        .map(|(tag, lam)| (*tag, aux(lam)))
                        .collect(),
                    sw_failaction: switch.sw_failaction.as_ref().map(|lam| Box::new(aux(lam))),
                    sw_names: switch.sw_names.clone(),
                },
            ),
            Lambda::LstringSwitch(scrutinee, cases, default) => Lambda::LstringSwitch(
                Box::new(aux(scrutinee)),
                cases
                    .iter()
                    .map(|(tag, lam)| (tag.clone(), aux(lam)))
                    .collect(),
                default.as_ref().map(|lam| Box::new(aux(lam))),
            ),
            Lambda::LstaticRaise(id, args) => {
                Lambda::LstaticRaise(*id, args.iter().map(aux).collect())
            }
            Lambda::LstaticCatch(body, ids, handler) => {
                Lambda::LstaticCatch(Box::new(aux(body)), ids.clone(), Box::new(aux(handler)))
            }
            Lambda::LtryWith(body, exn, handler) => {
                Lambda::LtryWith(Box::new(aux(body)), exn.clone(), Box::new(aux(handler)))
            }
            Lambda::LifThenElse(cond, then_, else_) => {
                Lambda::if_(aux(cond), aux(then_), aux(else_))
            }
            Lambda::Lwhile(cond, body) => Lambda::Lwhile(Box::new(aux(cond)), Box::new(aux(body))),
            Lambda::Lfor(id, start, end, direction, body) => Lambda::Lfor(
                id.clone(),
                Box::new(aux(start)),
                Box::new(aux(end)),
                *direction,
                Box::new(aux(body)),
            ),
            Lambda::Lfor_of(id, iterable, body) => {
                Lambda::for_of(id.clone(), aux(iterable), aux(body))
            }
            Lambda::Lfor_await_of(id, iterable, body) => {
                Lambda::for_await_of(id.clone(), aux(iterable), aux(body))
            }
            Lambda::Lbreak => Lambda::break_(),
            Lambda::Lcontinue => Lambda::continue_(),
            Lambda::Lassign(id, value) => Lambda::Lassign(id.clone(), Box::new(aux(value))),
        }
    }

    aux(lam)
}
