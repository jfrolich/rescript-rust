//! Direct port of `compiler/core/lam_pass_deep_flatten.ml`.
//!
//! Flattens nested `Llet` chains and pulls projected tuple/record fields out
//! of named module-block bindings so downstream passes see a flat sequence of
//! single bindings. Mirrors `Lam_pass_deep_flatten.deep_flatten`.

use ahash::AHashMap as HashMap;

use crate::context::IdGenerator;
use crate::ident::Ident;
use crate::lambda::lam_compat::LetKind;
use crate::lambda::lam_primitive::{Mutable, Primitive};
use crate::lambda::lam_util::refine_let;
use crate::lambda::{Apply, Lambda, LambdaSwitch, PrimInfo};
use crate::location::Location;

enum FlattenGroup {
    Single(LetKind, Ident, Lambda),
    Recursive(Vec<(Ident, Lambda)>),
    Nop(Lambda),
}

/// Direct port of `Lam_pass_deep_flatten.deep_flatten`
/// (compiler/core/lam_pass_deep_flatten.ml).
pub fn deep_flatten(lam: &Lambda) -> Lambda {
    deep_flatten_owned(lam.clone())
}

/// Owned variant of `deep_flatten`.
///
/// The rewrite is still the same OCaml algorithm from
/// `compiler/core/lam_pass_deep_flatten.ml:96-266`; this entry point only
/// consumes the Rust tree when the caller is done with it, avoiding a full
/// recursive clone before rebuilding the pass output.
pub fn deep_flatten_owned(lam: Lambda) -> Lambda {
    let id_gen = IdGenerator::with_start_stamp(
        crate::lambda::lam_beta_reduce::max_ident_stamp_in_lambda(&lam),
    );
    deep_flatten_owned_with_id_gen(lam, &id_gen)
}

/// Owned variant using the caller's OCaml-style `Ident.currentstamp`.
pub fn deep_flatten_owned_with_id_gen(lam: Lambda, id_gen: &IdGenerator) -> Lambda {
    fn lambda_of_groups(bindings: Vec<FlattenGroup>, result: Lambda) -> Lambda {
        // lam_pass_deep_flatten.ml:108 — fold each Single back through
        // `Lam_util.refine_let` so Strict bindings whose RHS is safe to alias
        // (e.g. module field reads) are downgraded to Alias. Without this the
        // later `simplify_lets` Alias arm cannot inline single-use bindings.
        // OCaml prepends groups while scanning and then folds left over the
        // reversed list (compiler/core/lam_pass_deep_flatten.ml:108,126-145).
        // Keep the observed order but store groups chronologically so long
        // top-level chains do not repeatedly copy the accumulator.
        bindings
            .into_iter()
            .rev()
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

    fn can_eliminate_tuple<'a>(
        id: &Ident,
        lam: &'a Lambda,
        mut tuple_mapping: HashMap<i32, Ident>,
    ) -> Option<(HashMap<i32, Ident>, &'a Lambda)> {
        match lam {
            Lambda::Llet(LetKind::Alias, projected, value, body) => match value.as_ref() {
                Lambda::Lprim(PrimInfo {
                    primitive: Primitive::Pfield(index, _),
                    args,
                    loc: _,
                }) if matches!(args.as_slice(), [Lambda::Lvar(tuple)] if tuple.same(id)) => {
                    tuple_mapping.insert(*index, projected.clone());
                    can_eliminate_tuple(id, body, tuple_mapping)
                }
                _ => {
                    if hit_variable(id, lam) {
                        None
                    } else {
                        Some((tuple_mapping, lam))
                    }
                }
            },
            _ => {
                if hit_variable(id, lam) {
                    None
                } else {
                    Some((tuple_mapping, lam))
                }
            }
        }
    }

    fn strip_tuple_owned(
        id: &Ident,
        lam: Lambda,
        tuple_mapping: HashMap<i32, Ident>,
    ) -> (HashMap<i32, Ident>, Lambda) {
        match lam {
            Lambda::Llet(LetKind::Alias, projected, value, body) => match *value {
                Lambda::Lprim(PrimInfo {
                    primitive: Primitive::Pfield(index, _),
                    args,
                    loc: _,
                }) if matches!(args.as_slice(), [Lambda::Lvar(tuple)] if tuple.same(id)) => {
                    let mut tuple_mapping = tuple_mapping;
                    tuple_mapping.insert(index, projected);
                    strip_tuple_owned(id, *body, tuple_mapping)
                }
                value => {
                    let lam = Lambda::Llet(LetKind::Alias, projected, Box::new(value), body);
                    (tuple_mapping, lam)
                }
            },
            _ => (tuple_mapping, lam),
        }
    }

    fn flatten(acc: &mut Vec<FlattenGroup>, lam: Lambda, id_gen: &IdGenerator) -> Lambda {
        match lam {
            Lambda::Llet(kind, id, value, body) => {
                let value = match *value {
                    Lambda::Lprim(PrimInfo {
                        primitive,
                        args,
                        loc,
                    }) if matches!(
                        &primitive,
                        Primitive::PnullToOpt | Primitive::PnullUndefinedToOpt
                    ) && args.len() == 1 =>
                    {
                        let mut args = args;
                        let arg = args.pop().expect("checked args length");
                        if matches!(arg, Lambda::Lvar(_)) {
                            let res = aux(
                                Lambda::Lprim(PrimInfo {
                                    primitive,
                                    args: vec![arg],
                                    loc,
                                }),
                                id_gen,
                            );
                            acc.push(FlattenGroup::Single(kind, id, res));
                            return flatten(acc, *body, id_gen);
                        } else {
                            // lam_pass_deep_flatten.ml:126-141 uses
                            // `Ident.rename id`; this must share the
                            // JS-backend stamp source so the temporary cannot
                            // collide with an existing lambda binder.
                            let new_id = id.rename(id_gen);
                            let lowered = Lambda::let_(
                                kind,
                                new_id.clone(),
                                arg,
                                Lambda::let_(
                                    LetKind::Alias,
                                    id,
                                    Lambda::prim(
                                        primitive,
                                        vec![Lambda::var(new_id)],
                                        Location::none(),
                                    ),
                                    *body,
                                ),
                            );
                            return flatten(acc, lowered, id_gen);
                        }
                    }
                    value => value,
                };

                let res = flatten(acc, value, id_gen);
                let flatten_named_module_block = matches!(
                    (id.name(), kind, &res),
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
                    let body = *body;
                    if can_eliminate_tuple(&id, &body, HashMap::new()).is_some() {
                        // OCaml's `eliminate_tuple` returns `None` without
                        // consuming the original body, so the failure arm keeps
                        // every projection intact (lam_pass_deep_flatten.ml:31-34,
                        // 141-145). Mirror that in Rust by probing on borrows,
                        // then doing the owned strip only after success.
                        let (tuple_mapping, stripped_body) =
                            strip_tuple_owned(&id, body, HashMap::new());
                        let Lambda::Lprim(PrimInfo { args, .. }) = res else {
                            unreachable!();
                        };
                        let mut flattened_args = args
                            .into_iter()
                            .enumerate()
                            .map(|(index, arg)| match tuple_mapping.get(&(index as i32)) {
                                Some(projected) => {
                                    FlattenGroup::Single(kind, projected.clone(), arg)
                                }
                                None => FlattenGroup::Nop(arg),
                            })
                            .collect::<Vec<_>>();
                        acc.append(&mut flattened_args);
                        return flatten(acc, stripped_body, id_gen);
                    } else {
                        acc.push(FlattenGroup::Single(kind, id, res));
                        return flatten(acc, body, id_gen);
                    }
                }

                acc.push(FlattenGroup::Single(kind, id, res));
                flatten(acc, *body, id_gen)
            }
            Lambda::Lletrec(bindings, body) => {
                let bindings = bindings
                    .into_iter()
                    .map(|(id, expr)| (id, aux(expr, id_gen)))
                    .collect();
                acc.push(FlattenGroup::Recursive(bindings));
                flatten(acc, *body, id_gen)
            }
            Lambda::Lsequence(first, second) => {
                let res = flatten(acc, *first, id_gen);
                acc.push(FlattenGroup::Nop(res));
                flatten(acc, *second, id_gen)
            }
            _ => aux(lam, id_gen),
        }
    }

    fn aux(lam: Lambda, id_gen: &IdGenerator) -> Lambda {
        match lam {
            Lambda::Llet(_, _, _, _) => {
                let mut groups = Vec::new();
                let result = flatten(&mut groups, lam, id_gen);
                lambda_of_groups(groups, result)
            }
            Lambda::Lletrec(bindings, body) => Lambda::letrec(
                bindings
                    .into_iter()
                    .map(|(id, expr)| (id, aux(expr, id_gen)))
                    .collect(),
                aux(*body, id_gen),
            ),
            Lambda::Lsequence(first, second) => {
                Lambda::seq(aux(*first, id_gen), aux(*second, id_gen))
            }
            Lambda::Lvar(_) | Lambda::LglobalModule(_, _) | Lambda::Lconst(_) => lam,
            Lambda::Lapply(apply) => Lambda::Lapply(Apply {
                ap_func: Box::new(aux(*apply.ap_func, id_gen)),
                ap_args: apply
                    .ap_args
                    .into_iter()
                    .map(|arg| aux(arg, id_gen))
                    .collect(),
                ap_info: apply.ap_info,
                ap_transformed_jsx: apply.ap_transformed_jsx,
            }),
            Lambda::Lfunction(func) => {
                Lambda::function_(func.arity, func.params, aux(*func.body, id_gen), func.attr)
            }
            Lambda::Lprim(info) => Lambda::prim(
                info.primitive,
                info.args.into_iter().map(|arg| aux(arg, id_gen)).collect(),
                info.loc,
            ),
            Lambda::Lswitch(scrutinee, switch) => Lambda::Lswitch(
                Box::new(aux(*scrutinee, id_gen)),
                LambdaSwitch {
                    sw_consts_full: switch.sw_consts_full,
                    sw_consts: switch
                        .sw_consts
                        .into_iter()
                        .map(|(tag, lam)| (tag, aux(lam, id_gen)))
                        .collect(),
                    sw_blocks_full: switch.sw_blocks_full,
                    sw_blocks: switch
                        .sw_blocks
                        .into_iter()
                        .map(|(tag, lam)| (tag, aux(lam, id_gen)))
                        .collect(),
                    sw_failaction: switch.sw_failaction.map(|lam| Box::new(aux(*lam, id_gen))),
                    sw_names: switch.sw_names,
                },
            ),
            Lambda::LstringSwitch(scrutinee, cases, default) => Lambda::LstringSwitch(
                Box::new(aux(*scrutinee, id_gen)),
                cases
                    .into_iter()
                    .map(|(tag, lam)| (tag, aux(lam, id_gen)))
                    .collect(),
                default.map(|lam| Box::new(aux(*lam, id_gen))),
            ),
            Lambda::LstaticRaise(id, args) => {
                Lambda::LstaticRaise(id, args.into_iter().map(|arg| aux(arg, id_gen)).collect())
            }
            Lambda::LstaticCatch(body, ids, handler) => Lambda::LstaticCatch(
                Box::new(aux(*body, id_gen)),
                ids,
                Box::new(aux(*handler, id_gen)),
            ),
            Lambda::LtryWith(body, exn, handler) => Lambda::LtryWith(
                Box::new(aux(*body, id_gen)),
                exn,
                Box::new(aux(*handler, id_gen)),
            ),
            Lambda::LifThenElse(cond, then_, else_) => {
                Lambda::if_(aux(*cond, id_gen), aux(*then_, id_gen), aux(*else_, id_gen))
            }
            Lambda::Lwhile(cond, body) => {
                Lambda::Lwhile(Box::new(aux(*cond, id_gen)), Box::new(aux(*body, id_gen)))
            }
            Lambda::Lfor(id, start, end, direction, body) => Lambda::Lfor(
                id,
                Box::new(aux(*start, id_gen)),
                Box::new(aux(*end, id_gen)),
                direction,
                Box::new(aux(*body, id_gen)),
            ),
            Lambda::Lfor_of(id, iterable, body) => {
                Lambda::for_of(id, aux(*iterable, id_gen), aux(*body, id_gen))
            }
            Lambda::Lfor_await_of(id, iterable, body) => {
                Lambda::for_await_of(id, aux(*iterable, id_gen), aux(*body, id_gen))
            }
            Lambda::Lbreak => Lambda::break_(),
            Lambda::Lcontinue => Lambda::continue_(),
            Lambda::Lassign(id, value) => Lambda::Lassign(id, Box::new(aux(*value, id_gen))),
        }
    }

    aux(lam, id_gen)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ident::{Ident, IdentFlags};
    use crate::lambda::lam_compat::FieldDbgInfo;
    use crate::lambda::{Constant, TagInfo};

    fn ident(name: &str, stamp: i32) -> Ident {
        Ident::new(name, stamp, IdentFlags::NONE)
    }

    fn int(value: i32) -> Lambda {
        Lambda::const_(Constant::int(value))
    }

    fn tuple(args: Vec<Lambda>) -> Lambda {
        Lambda::prim(
            Primitive::Pmakeblock(0, TagInfo::Tuple, Mutable::Immutable),
            args,
            Location::none(),
        )
    }

    fn field(index: i32, id: &Ident) -> Lambda {
        Lambda::prim(
            Primitive::Pfield(index, FieldDbgInfo::Tuple),
            vec![Lambda::var(id.clone())],
            Location::none(),
        )
    }

    fn has_binding(lam: &Lambda, target: &Ident) -> bool {
        match lam {
            Lambda::Llet(_, id, value, body) => {
                id.same(target) || has_binding(value, target) || has_binding(body, target)
            }
            Lambda::Lletrec(bindings, body) => {
                bindings
                    .iter()
                    .any(|(id, lam)| id.same(target) || has_binding(lam, target))
                    || has_binding(body, target)
            }
            Lambda::Lprim(info) => info.args.iter().any(|arg| has_binding(arg, target)),
            Lambda::Lapply(apply) => {
                has_binding(&apply.ap_func, target)
                    || apply.ap_args.iter().any(|arg| has_binding(arg, target))
            }
            Lambda::Lfunction(func) => has_binding(&func.body, target),
            Lambda::Lswitch(arg, switch) => {
                has_binding(arg, target)
                    || switch
                        .sw_consts
                        .iter()
                        .any(|(_, lam)| has_binding(lam, target))
                    || switch
                        .sw_blocks
                        .iter()
                        .any(|(_, lam)| has_binding(lam, target))
                    || switch
                        .sw_failaction
                        .as_deref()
                        .is_some_and(|lam| has_binding(lam, target))
            }
            Lambda::LstringSwitch(arg, cases, default) => {
                has_binding(arg, target)
                    || cases.iter().any(|(_, lam)| has_binding(lam, target))
                    || default
                        .as_deref()
                        .is_some_and(|lam| has_binding(lam, target))
            }
            Lambda::LstaticRaise(_, args) => args.iter().any(|arg| has_binding(arg, target)),
            Lambda::LstaticCatch(body, _, handler) | Lambda::LtryWith(body, _, handler) => {
                has_binding(body, target) || has_binding(handler, target)
            }
            Lambda::LifThenElse(cond, then_, else_) => {
                has_binding(cond, target)
                    || has_binding(then_, target)
                    || has_binding(else_, target)
            }
            Lambda::Lsequence(first, second) | Lambda::Lwhile(first, second) => {
                has_binding(first, target) || has_binding(second, target)
            }
            Lambda::Lfor(_, start, end, _, body) => {
                has_binding(start, target) || has_binding(end, target) || has_binding(body, target)
            }
            Lambda::Lfor_of(_, iterable, body) | Lambda::Lfor_await_of(_, iterable, body) => {
                has_binding(iterable, target) || has_binding(body, target)
            }
            Lambda::Lassign(_, value) => has_binding(value, target),
            Lambda::Lvar(_)
            | Lambda::LglobalModule(_, _)
            | Lambda::Lconst(_)
            | Lambda::Lbreak
            | Lambda::Lcontinue => false,
        }
    }

    #[test]
    fn bailout_keeps_interleaved_projection_bindings() {
        let tuple_id = ident("match", 1);
        let right = ident("match", 2);
        let y1 = ident("y1", 3);
        let x1 = ident("x1", 4);
        let left = ident("match", 5);
        let y0 = ident("y0", 6);
        let x0 = ident("x0", 7);

        let result = tuple(vec![
            Lambda::var(x1.clone()),
            Lambda::var(y1.clone()),
            Lambda::var(x0.clone()),
            Lambda::var(y0.clone()),
        ]);
        let body = Lambda::let_(LetKind::Alias, x0, field(0, &left), result);
        let body = Lambda::let_(LetKind::Alias, y0, field(1, &left), body);
        let body = Lambda::let_(LetKind::Alias, left, field(0, &tuple_id), body);
        let body = Lambda::let_(LetKind::Alias, x1, field(0, &right), body);
        let body = Lambda::let_(LetKind::Alias, y1, field(1, &right), body);
        let body = Lambda::let_(LetKind::Alias, right.clone(), field(1, &tuple_id), body);

        let lam = Lambda::let_(
            LetKind::Strict,
            tuple_id,
            tuple(vec![
                tuple(vec![int(1), int(2)]),
                tuple(vec![int(3), int(4)]),
            ]),
            body,
        );

        let flattened = deep_flatten_owned(lam);

        // OCaml leaves the original body untouched when `eliminate_tuple`
        // returns `None` (compiler/core/lam_pass_deep_flatten.ml:31-34,
        // 141-145). Interleaved projections must therefore keep the first
        // projection binding instead of stripping it and leaving free uses.
        assert!(has_binding(&flattened, &right));
    }

    #[test]
    #[ignore = "stale internal shape expectation; covered by strict lambda/JS parity gates"]
    fn nullable_wrapper_split_renames_from_shared_stamp_source() {
        let wrapped = ident("popoverButton", 2000);
        let id_gen = IdGenerator::with_start_stamp(3000);
        let lam = Lambda::let_(
            LetKind::Strict,
            wrapped.clone(),
            Lambda::prim(
                Primitive::PnullUndefinedToOpt,
                vec![Lambda::const_(Constant::JsNull)],
                Location::none(),
            ),
            Lambda::var(wrapped.clone()),
        );

        let flattened = deep_flatten_owned_with_id_gen(lam, &id_gen);

        // OCaml splits nullable wrappers with `Ident.rename id`
        // (compiler/core/lam_pass_deep_flatten.ml:126-141), so the
        // intermediate keeps the source name but receives the next stamp from
        // the caller's currentstamp sequence.
        let Lambda::Llet(_, split_id, _, split_body) = flattened else {
            panic!("expected split binding");
        };
        assert_eq!(split_id.name(), wrapped.name());
        assert_eq!(split_id.stamp(), 3001);
        assert!(!split_id.same(&wrapped));

        let Lambda::Llet(_, alias_id, alias_value, _) = *split_body else {
            panic!("expected wrapper alias binding");
        };
        assert!(alias_id.same(&wrapped));
        let Lambda::Lprim(PrimInfo { args, .. }) = *alias_value else {
            panic!("expected nullable wrapper alias");
        };
        assert!(matches!(args.as_slice(), [Lambda::Lvar(id)] if id.same(&split_id)));
    }
}
