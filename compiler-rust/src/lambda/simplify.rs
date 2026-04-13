//! Small post-lowering lambda simplifications used on the JS backend path.

use std::collections::{HashMap, HashSet};

use crate::ident::Ident;
use crate::lambda::analysis;
use crate::lambda::beta_reduce;
use crate::lambda::compat::{FieldDbgInfo, LetKind};
use crate::lambda::compile_context::BoxedNullable;
use crate::lambda::constant::Constant;
use crate::lambda::free_variables::free_variables;
use crate::lambda::primitive::Primitive;
use crate::lambda::{
    Apply, ApplyStatus, FunctionAttribute, InlineAttribute, LFunction, Lambda, LambdaSwitch,
    TagInfo,
};
use crate::location::Location;

#[derive(Clone, Default)]
struct SimplifyEnv {
    blocks: HashMap<Ident, ImmutableBlockInfo>,
    functions: HashMap<Ident, LFunction>,
    optional_blocks: HashMap<Ident, OptionalBlockInfo>,
    substitutions: HashMap<Ident, Lambda>,
}

#[derive(Clone)]
enum BlockElement {
    Na,
    Simple(Lambda),
}

#[derive(Clone)]
struct ImmutableBlockInfo {
    tag_info: TagInfo,
    elements: Vec<BlockElement>,
}

#[derive(Clone)]
struct OptionalBlockInfo {
    value: Lambda,
    kind: BoxedNullable,
}

#[derive(Clone)]
enum FlattenGroup {
    Single(LetKind, Ident, Lambda),
    Recursive(Vec<(Ident, Lambda)>),
    Nop(Lambda),
}

impl SimplifyEnv {
    fn without_ident(&self, id: &Ident) -> Self {
        let mut next = self.clone();
        next.blocks.remove(id);
        next.functions.remove(id);
        next.optional_blocks.remove(id);
        next.substitutions.remove(id);
        next
    }

    fn without_idents<'a>(&self, ids: impl IntoIterator<Item = &'a Ident>) -> Self {
        let mut next = self.clone();
        for id in ids {
            next.blocks.remove(id);
            next.functions.remove(id);
            next.optional_blocks.remove(id);
            next.substitutions.remove(id);
        }
        next
    }
}

/// Simplify lowered lambda before JS IR lowering.
pub fn simplify_for_js_backend(lam: &Lambda) -> Lambda {
    let flattened = deep_flatten_for_js_backend(lam);
    let exports = collect_exported_idents(&flattened);
    let env = SimplifyEnv {
        functions: collect_inlineable_functions(&flattened),
        ..SimplifyEnv::default()
    };
    simplify_with_env(&flattened, &env, &exports)
}

fn deep_flatten_for_js_backend(lam: &Lambda) -> Lambda {
    fn lambda_of_groups(rev_bindings: Vec<FlattenGroup>, result: Lambda) -> Lambda {
        rev_bindings
            .into_iter()
            .fold(result, |acc, group| match group {
                FlattenGroup::Single(kind, ident, lam) => Lambda::let_(kind, ident, lam, acc),
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
                    Lambda::Lprim(crate::lambda::PrimInfo {
                        primitive: Primitive::Pfield(index, _),
                        args,
                        ..
                    }) if matches!(args.as_slice(), [Lambda::Lvar(tuple)] if tuple.same(id))
                ) =>
            {
                let Lambda::Lprim(crate::lambda::PrimInfo {
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
                    Lambda::Lprim(crate::lambda::PrimInfo {
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
                if let Lambda::Lprim(crate::lambda::PrimInfo {
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
                        Lambda::Lprim(crate::lambda::PrimInfo {
                            primitive: Primitive::Pmakeblock(
                                _,
                                _,
                                crate::lambda::primitive::Mutable::Immutable
                            ),
                            ..
                        })
                    )
                );
                if flatten_named_module_block {
                    let Lambda::Lprim(crate::lambda::PrimInfo { args, .. }) = &res else {
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
            Lambda::Lassign(id, value) => Lambda::Lassign(id.clone(), Box::new(aux(value))),
        }
    }

    aux(lam)
}

fn simplify_with_env(lam: &Lambda, env: &SimplifyEnv, exports: &HashSet<Ident>) -> Lambda {
    match lam {
        Lambda::Lvar(id) => env
            .substitutions
            .get(id)
            .cloned()
            .unwrap_or_else(|| lam.clone()),
        Lambda::LglobalModule(_, _) | Lambda::Lconst(_) => lam.clone(),
        Lambda::Lapply(apply) => simplify_apply(apply, env, exports),
        Lambda::Lfunction(func) => {
            let body_env = env.without_idents(func.params.iter());
            Lambda::function_(
                func.arity,
                func.params.clone(),
                simplify_with_env(&func.body, &body_env, exports),
                func.attr.clone(),
            )
        }
        Lambda::Llet(kind, id, value, body) => {
            let value = simplify_with_env(value, env, exports);
            let mut body_env = env.without_ident(id);
            if let Some(block_info) = immutable_block_elements(&value) {
                body_env.blocks.insert(id.clone(), block_info);
            }
            if let Some(optional_info) = optional_block_info(&value) {
                body_env.optional_blocks.insert(id.clone(), optional_info);
            }
            if let Some(substitution) = substitution_candidate(*kind, &value) {
                body_env.substitutions.insert(id.clone(), substitution);
            }
            if *kind != LetKind::Variable {
                if let Some(func) = inlineable_local_function(&value) {
                    if analysis::lfunction_can_be_inlined(&func) {
                        body_env.functions.insert(id.clone(), func);
                    }
                }
            }
            let body = simplify_with_env(body, &body_env, exports);
            if *kind == LetKind::Alias && !exports.contains(id) {
                let use_info = alias_use_info(id, &body);
                if use_info.times == 1 && !use_info.captured {
                    return substitute_alias_use(&body, id, &value);
                }
            }
            if !exports.contains(id) && !free_variables(&body).contains(id) {
                if analysis::no_side_effects(&value) {
                    body
                } else {
                    Lambda::seq(value, body)
                }
            } else {
                refine_let_binding(*kind, id, value, body)
            }
        }
        Lambda::Lletrec(bindings, body) => {
            let bound_ids = bindings.iter().map(|(id, _)| id);
            let scoped_env = env.without_idents(bound_ids);
            let bindings = bindings
                .iter()
                .map(|(id, expr)| (id.clone(), simplify_with_env(expr, &scoped_env, exports)))
                .collect();
            let body = simplify_with_env(body, &scoped_env, exports);
            Lambda::letrec(bindings, body)
        }
        Lambda::Lprim(info) => simplify_primitive(info, env, exports),
        Lambda::Lswitch(scrutinee, switch) => Lambda::Lswitch(
            Box::new(simplify_with_env(scrutinee, env, exports)),
            LambdaSwitch {
                sw_consts_full: switch.sw_consts_full,
                sw_consts: switch
                    .sw_consts
                    .iter()
                    .map(|(tag, lam)| (*tag, simplify_with_env(lam, env, exports)))
                    .collect(),
                sw_blocks_full: switch.sw_blocks_full,
                sw_blocks: switch
                    .sw_blocks
                    .iter()
                    .map(|(tag, lam)| (*tag, simplify_with_env(lam, env, exports)))
                    .collect(),
                sw_failaction: switch
                    .sw_failaction
                    .as_ref()
                    .map(|lam| Box::new(simplify_with_env(lam, env, exports))),
                sw_names: switch.sw_names.clone(),
            },
        ),
        Lambda::LstringSwitch(scrutinee, cases, default) => Lambda::LstringSwitch(
            Box::new(simplify_with_env(scrutinee, env, exports)),
            cases
                .iter()
                .map(|(tag, lam)| (tag.clone(), simplify_with_env(lam, env, exports)))
                .collect(),
            default
                .as_ref()
                .map(|lam| Box::new(simplify_with_env(lam, env, exports))),
        ),
        Lambda::LstaticRaise(id, args) => Lambda::LstaticRaise(
            *id,
            args.iter()
                .map(|arg| simplify_with_env(arg, env, exports))
                .collect(),
        ),
        Lambda::LstaticCatch(body, (id, vars), handler) => {
            let scoped_env = env.without_idents(vars.iter());
            Lambda::LstaticCatch(
                Box::new(simplify_with_env(body, env, exports)),
                (*id, vars.clone()),
                Box::new(simplify_with_env(handler, &scoped_env, exports)),
            )
        }
        Lambda::LtryWith(body, exn, handler) => {
            let scoped_env = env.without_ident(exn);
            Lambda::LtryWith(
                Box::new(simplify_with_env(body, env, exports)),
                exn.clone(),
                Box::new(simplify_with_env(handler, &scoped_env, exports)),
            )
        }
        Lambda::LifThenElse(cond, then_, else_) => {
            if let Some((optional_value, kind)) = optional_block_predicate(cond, env) {
                let predicate = optional_is_some_predicate(optional_value, kind);
                return Lambda::if_(
                    predicate,
                    simplify_with_env(then_, env, exports),
                    simplify_with_env(else_, env, exports),
                );
            }

            Lambda::if_(
                simplify_with_env(cond, env, exports),
                simplify_with_env(then_, env, exports),
                simplify_with_env(else_, env, exports),
            )
        }
        Lambda::Lsequence(first, second) => {
            let first = simplify_with_env(first, env, exports);
            let second = simplify_with_env(second, env, exports);
            if analysis::no_side_effects(&first) {
                second
            } else {
                Lambda::seq(first, second)
            }
        }
        Lambda::Lwhile(cond, body) => Lambda::Lwhile(
            Box::new(simplify_with_env(cond, env, exports)),
            Box::new(simplify_with_env(body, env, exports)),
        ),
        Lambda::Lfor(id, from, to, direction, body) => {
            let scoped_env = env.without_ident(id);
            Lambda::Lfor(
                id.clone(),
                Box::new(simplify_with_env(from, env, exports)),
                Box::new(simplify_with_env(to, env, exports)),
                *direction,
                Box::new(simplify_with_env(body, &scoped_env, exports)),
            )
        }
        Lambda::Lassign(id, value) => {
            Lambda::Lassign(id.clone(), Box::new(simplify_with_env(value, env, exports)))
        }
    }
}

#[derive(Clone, Copy, Default)]
struct AliasUseInfo {
    times: usize,
    captured: bool,
}

fn alias_use_info(target: &Ident, lam: &Lambda) -> AliasUseInfo {
    fn collect(target: &Ident, lam: &Lambda, info: &mut AliasUseInfo) {
        match lam {
            Lambda::Lvar(id) => {
                if id.same(target) {
                    info.times += 1;
                }
            }
            Lambda::LglobalModule(_, _) | Lambda::Lconst(_) => {}
            Lambda::Lapply(apply) => {
                collect(target, &apply.ap_func, info);
                for arg in &apply.ap_args {
                    collect(target, arg, info);
                }
            }
            Lambda::Lfunction(func) => {
                if free_variables(&func.body).contains(target) {
                    info.captured = true;
                }
                collect(target, &func.body, info);
            }
            Lambda::Llet(_, _, value, body) => {
                collect(target, value, info);
                collect(target, body, info);
            }
            Lambda::Lletrec(bindings, body) => {
                for (_, binding) in bindings {
                    collect(target, binding, info);
                }
                collect(target, body, info);
            }
            Lambda::Lprim(info_) => {
                for arg in &info_.args {
                    collect(target, arg, info);
                }
            }
            Lambda::Lswitch(scrutinee, switch) => {
                collect(target, scrutinee, info);
                for (_, lam) in &switch.sw_consts {
                    collect(target, lam, info);
                }
                for (_, lam) in &switch.sw_blocks {
                    collect(target, lam, info);
                }
                if let Some(fallback) = &switch.sw_failaction {
                    collect(target, fallback, info);
                }
            }
            Lambda::LstringSwitch(scrutinee, cases, default) => {
                collect(target, scrutinee, info);
                for (_, lam) in cases {
                    collect(target, lam, info);
                }
                if let Some(fallback) = default {
                    collect(target, fallback, info);
                }
            }
            Lambda::LstaticRaise(_, args) => {
                for arg in args {
                    collect(target, arg, info);
                }
            }
            Lambda::LstaticCatch(body, _, handler) | Lambda::LtryWith(body, _, handler) => {
                collect(target, body, info);
                collect(target, handler, info);
            }
            Lambda::LifThenElse(cond, then_, else_) => {
                collect(target, cond, info);
                collect(target, then_, info);
                collect(target, else_, info);
            }
            Lambda::Lsequence(first, second) | Lambda::Lwhile(first, second) => {
                collect(target, first, info);
                collect(target, second, info);
            }
            Lambda::Lfor(_, from, to, _, body) => {
                collect(target, from, info);
                collect(target, to, info);
                collect(target, body, info);
            }
            Lambda::Lassign(id, value) => {
                if id.same(target) {
                    info.times += 1;
                }
                collect(target, value, info);
            }
        }
    }

    let mut info = AliasUseInfo::default();
    collect(target, lam, &mut info);
    info
}

fn substitute_alias_use(lam: &Lambda, target: &Ident, replacement: &Lambda) -> Lambda {
    match lam {
        Lambda::Lvar(id) if id.same(target) => replacement.clone(),
        Lambda::Lvar(_) | Lambda::LglobalModule(_, _) | Lambda::Lconst(_) => lam.clone(),
        Lambda::Lapply(apply) => Lambda::Lapply(Apply {
            ap_func: Box::new(substitute_alias_use(&apply.ap_func, target, replacement)),
            ap_args: apply
                .ap_args
                .iter()
                .map(|arg| substitute_alias_use(arg, target, replacement))
                .collect(),
            ap_info: apply.ap_info.clone(),
            ap_transformed_jsx: apply.ap_transformed_jsx,
        }),
        Lambda::Lfunction(func) => Lambda::function_(
            func.arity,
            func.params.clone(),
            substitute_alias_use(&func.body, target, replacement),
            func.attr.clone(),
        ),
        Lambda::Llet(kind, id, value, body) => Lambda::let_(
            *kind,
            id.clone(),
            substitute_alias_use(value, target, replacement),
            substitute_alias_use(body, target, replacement),
        ),
        Lambda::Lletrec(bindings, body) => Lambda::letrec(
            bindings
                .iter()
                .map(|(id, lam)| (id.clone(), substitute_alias_use(lam, target, replacement)))
                .collect(),
            substitute_alias_use(body, target, replacement),
        ),
        Lambda::Lprim(info) => Lambda::prim(
            info.primitive.clone(),
            info.args
                .iter()
                .map(|arg| substitute_alias_use(arg, target, replacement))
                .collect(),
            info.loc.clone(),
        ),
        Lambda::Lswitch(scrutinee, switch) => Lambda::Lswitch(
            Box::new(substitute_alias_use(scrutinee, target, replacement)),
            LambdaSwitch {
                sw_consts_full: switch.sw_consts_full,
                sw_consts: switch
                    .sw_consts
                    .iter()
                    .map(|(tag, lam)| (*tag, substitute_alias_use(lam, target, replacement)))
                    .collect(),
                sw_blocks_full: switch.sw_blocks_full,
                sw_blocks: switch
                    .sw_blocks
                    .iter()
                    .map(|(tag, lam)| (*tag, substitute_alias_use(lam, target, replacement)))
                    .collect(),
                sw_failaction: switch
                    .sw_failaction
                    .as_ref()
                    .map(|lam| Box::new(substitute_alias_use(lam, target, replacement))),
                sw_names: switch.sw_names.clone(),
            },
        ),
        Lambda::LstringSwitch(scrutinee, cases, default) => Lambda::LstringSwitch(
            Box::new(substitute_alias_use(scrutinee, target, replacement)),
            cases
                .iter()
                .map(|(tag, lam)| (tag.clone(), substitute_alias_use(lam, target, replacement)))
                .collect(),
            default
                .as_ref()
                .map(|lam| Box::new(substitute_alias_use(lam, target, replacement))),
        ),
        Lambda::LstaticRaise(id, args) => Lambda::LstaticRaise(
            *id,
            args.iter()
                .map(|arg| substitute_alias_use(arg, target, replacement))
                .collect(),
        ),
        Lambda::LstaticCatch(body, ids, handler) => Lambda::LstaticCatch(
            Box::new(substitute_alias_use(body, target, replacement)),
            ids.clone(),
            Box::new(substitute_alias_use(handler, target, replacement)),
        ),
        Lambda::LtryWith(body, exn, handler) => Lambda::LtryWith(
            Box::new(substitute_alias_use(body, target, replacement)),
            exn.clone(),
            Box::new(substitute_alias_use(handler, target, replacement)),
        ),
        Lambda::LifThenElse(cond, then_, else_) => Lambda::if_(
            substitute_alias_use(cond, target, replacement),
            substitute_alias_use(then_, target, replacement),
            substitute_alias_use(else_, target, replacement),
        ),
        Lambda::Lsequence(first, second) => Lambda::seq(
            substitute_alias_use(first, target, replacement),
            substitute_alias_use(second, target, replacement),
        ),
        Lambda::Lwhile(cond, body) => Lambda::Lwhile(
            Box::new(substitute_alias_use(cond, target, replacement)),
            Box::new(substitute_alias_use(body, target, replacement)),
        ),
        Lambda::Lfor(id, from, to, direction, body) => Lambda::Lfor(
            id.clone(),
            Box::new(substitute_alias_use(from, target, replacement)),
            Box::new(substitute_alias_use(to, target, replacement)),
            *direction,
            Box::new(substitute_alias_use(body, target, replacement)),
        ),
        Lambda::Lassign(id, value) => Lambda::Lassign(
            id.clone(),
            Box::new(substitute_alias_use(value, target, replacement)),
        ),
    }
}

fn refine_let_binding(kind: LetKind, id: &Ident, value: Lambda, body: Lambda) -> Lambda {
    let is_block_constructor =
        |primitive: &Primitive| matches!(primitive, Primitive::Pmakeblock(_, _, _));

    match &body {
        Lambda::Lvar(bound) if bound.same(id) => value,
        Lambda::Lprim(info)
            if !is_block_constructor(&info.primitive)
                && matches!(info.args.as_slice(), [Lambda::Lvar(bound)] if bound.same(id)) =>
        {
            Lambda::prim(info.primitive.clone(), vec![value], info.loc.clone())
        }
        Lambda::Lapply(apply)
            if matches!(apply.ap_args.as_slice(), [Lambda::Lvar(bound)] if bound.same(id))
                && !lambda_hits_variable(id, &apply.ap_func) =>
        {
            Lambda::Lapply(Apply {
                ap_func: apply.ap_func.clone(),
                ap_args: vec![value],
                ap_info: apply.ap_info.clone(),
                ap_transformed_jsx: apply.ap_transformed_jsx,
            })
        }
        _ => Lambda::let_(kind, id.clone(), value, body),
    }
}

fn simplify_primitive(
    info: &crate::lambda::PrimInfo,
    env: &SimplifyEnv,
    exports: &HashSet<Ident>,
) -> Lambda {
    if let Primitive::Pmakeblock(_, TagInfo::ModuleExport(export_ids), _) = &info.primitive {
        debug_assert_eq!(
            export_ids.len(),
            info.args.len(),
            "module export idents and payloads must stay aligned"
        );
        let args = info
            .args
            .iter()
            .zip(export_ids.iter())
            .map(|(arg, export_id)| match arg {
                Lambda::Lvar(id) if id.same(export_id) => {
                    match env.substitutions.get(id) {
                        // OCaml's simplify_alias still collapses module-alias
                        // exports to Const_module_alias, which forces later
                        // export coercion to synthesize the trailing placeholder
                        // instead of keeping the inert alias at its source
                        // position.
                        Some(Lambda::Lconst(Constant::ModuleAlias)) => {
                            Lambda::const_(Constant::ModuleAlias)
                        }
                        _ => Lambda::var(id.clone()),
                    }
                }
                _ => simplify_with_env(arg, env, exports),
            })
            .collect();
        return Lambda::prim(info.primitive.clone(), args, info.loc.clone());
    }

    let args: Vec<_> = info
        .args
        .iter()
        .map(|arg| simplify_with_env(arg, env, exports))
        .collect();

    match (&info.primitive, args.as_slice()) {
        (Primitive::PjsFnMake(arity), [Lambda::Lfunction(func)]) => simplify_with_env(
            &adjust_direct_js_fn_make_function(func, *arity, &info.loc),
            env,
            exports,
        ),
        (Primitive::PjsFnMakeUnit, [Lambda::Lfunction(func)])
            if func.arity == 1
                && matches!(func.params.as_slice(), [param] if param.name() == "param") =>
        {
            let mut func = func.clone();
            func.attr.one_unit_arg = true;
            Lambda::Lfunction(func)
        }
        (Primitive::PjsFnMakeUnit, [arg]) => arg.clone(),
        (Primitive::Pfield(index, dbg), [arg]) => {
            simplify_field_access(*index, dbg, arg, env, &info.primitive, &info.loc)
        }
        (Primitive::PvalFromOption | Primitive::PvalFromOptionNotNest, [Lambda::Lvar(id)]) => env
            .optional_blocks
            .get(id)
            .map(|optional| optional.value.clone())
            .unwrap_or_else(|| Lambda::prim(info.primitive.clone(), args, info.loc.clone())),
        (
            Primitive::Pstringadd,
            [
                Lambda::Lconst(Constant::String {
                    s: left,
                    delim: left_delim,
                }),
                Lambda::Lconst(Constant::String {
                    s: right,
                    delim: right_delim,
                }),
            ],
        ) => Lambda::const_(Constant::String {
            s: format!("{left}{right}"),
            delim: left_delim.clone().or(right_delim.clone()),
        }),
        _ => Lambda::prim(info.primitive.clone(), args, info.loc.clone()),
    }
}

fn adjust_direct_js_fn_make_function(func: &LFunction, to_: i32, loc: &Location) -> Lambda {
    let from = func.arity;
    if from == to_ || func.attr.async_ {
        return Lambda::Lfunction(func.clone());
    }

    if to_ == 0 {
        let [param] = func.params.as_slice() else {
            unreachable!("direct js fn make arity adjustment should preserve a function body");
        };
        return Lambda::function_(
            0,
            vec![],
            Lambda::let_(
                LetKind::Alias,
                param.clone(),
                Lambda::unit(),
                (*func.body).clone(),
            ),
            FunctionAttribute::default(),
        );
    }

    if to_ > from {
        let extra_args = fresh_js_fn_params((to_ - from) as usize);
        let mut body = (*func.body).clone();
        for extra_arg in &extra_args {
            body = apply_lambda_with_default_info(
                body,
                vec![Lambda::var(extra_arg.clone())],
                loc,
                ApplyStatus::Na,
            );
        }

        let mut params = func.params.clone();
        params.extend(extra_args);
        return Lambda::function_(to_, params, body, FunctionAttribute::default());
    }

    let outer_arity = to_ as usize;
    let outer_params = func.params[..outer_arity].to_vec();
    let inner_params = func.params[outer_arity..].to_vec();
    let inner = Lambda::function_(
        from - to_,
        inner_params,
        (*func.body).clone(),
        FunctionAttribute::default(),
    );
    Lambda::function_(to_, outer_params, inner, FunctionAttribute::default())
}

fn fresh_js_fn_params(count: usize) -> Vec<Ident> {
    (0..count).map(|_| Ident::create_local("param")).collect()
}

fn apply_lambda_with_default_info(
    func: Lambda,
    args: Vec<Lambda>,
    loc: &Location,
    status: ApplyStatus,
) -> Lambda {
    Lambda::Lapply(Apply {
        ap_func: Box::new(func),
        ap_args: args,
        ap_info: crate::lambda::ApInfo {
            loc: loc.clone(),
            inlined: InlineAttribute::Default,
            status,
        },
        ap_transformed_jsx: false,
    })
}

fn simplify_field_access(
    index: i32,
    dbg: &FieldDbgInfo,
    arg: &Lambda,
    env: &SimplifyEnv,
    primitive: &Primitive,
    loc: &crate::location::Location,
) -> Lambda {
    match arg {
        Lambda::Lvar(id) => match env.blocks.get(id).and_then(|elements| {
            block_field(elements, index, dbg).and_then(BlockElement::as_simple_form)
        }) {
            Some(value) => value.clone(),
            None => Lambda::prim(primitive.clone(), vec![arg.clone()], loc.clone()),
        },
        Lambda::Lconst(Constant::Block {
            tag_info, elements, ..
        }) => constant_block_field(tag_info, elements, index, dbg)
            .map(Lambda::const_)
            .unwrap_or_else(|| Lambda::prim(primitive.clone(), vec![arg.clone()], loc.clone())),
        _ => Lambda::prim(primitive.clone(), vec![arg.clone()], loc.clone()),
    }
}

fn immutable_block_elements(value: &Lambda) -> Option<ImmutableBlockInfo> {
    match value {
        Lambda::Lprim(info)
            if matches!(
                info.primitive,
                Primitive::Pmakeblock(_, _, crate::lambda::primitive::Mutable::Immutable)
            ) =>
        {
            let Primitive::Pmakeblock(_, tag_info, _) = &info.primitive else {
                unreachable!();
            };
            Some(ImmutableBlockInfo {
                tag_info: tag_info.clone(),
                elements: info.args.iter().map(block_element_of_lambda).collect(),
            })
        }
        Lambda::Lconst(Constant::Block {
            tag_info, elements, ..
        }) => Some(ImmutableBlockInfo {
            tag_info: tag_info.clone(),
            elements: elements
                .iter()
                .cloned()
                .map(Lambda::const_)
                .map(BlockElement::Simple)
                .collect(),
        }),
        _ => None,
    }
}

fn optional_block_info(value: &Lambda) -> Option<OptionalBlockInfo> {
    match value {
        Lambda::Lprim(crate::lambda::PrimInfo {
            primitive: Primitive::PnullToOpt,
            args,
            ..
        }) if matches!(args.as_slice(), [Lambda::Lvar(_)]) => Some(OptionalBlockInfo {
            value: args[0].clone(),
            kind: BoxedNullable::Null,
        }),
        Lambda::Lprim(crate::lambda::PrimInfo {
            primitive: Primitive::PnullUndefinedToOpt,
            args,
            ..
        }) if matches!(args.as_slice(), [Lambda::Lvar(_)]) => Some(OptionalBlockInfo {
            value: args[0].clone(),
            kind: BoxedNullable::NullUndefined,
        }),
        _ => None,
    }
}

fn optional_block_predicate(cond: &Lambda, env: &SimplifyEnv) -> Option<(Lambda, BoxedNullable)> {
    match cond {
        Lambda::Lprim(crate::lambda::PrimInfo {
            primitive: Primitive::PisNotNone,
            args,
            ..
        }) => match args.as_slice() {
            [Lambda::Lvar(id)] => env
                .optional_blocks
                .get(id)
                .map(|optional| (optional.value.clone(), optional.kind)),
            _ => None,
        },
        _ => None,
    }
}

fn optional_is_some_predicate(value: Lambda, kind: BoxedNullable) -> Lambda {
    let primitive = match kind {
        BoxedNullable::Undefined => Primitive::PisUndefined,
        BoxedNullable::Null => Primitive::PisNull,
        BoxedNullable::NullUndefined => Primitive::PisNullUndefined,
    };
    Lambda::prim(
        Primitive::Pnot,
        vec![Lambda::prim(primitive, vec![value], Location::none())],
        Location::none(),
    )
}

fn lambda_hits_variable(target: &Ident, lam: &Lambda) -> bool {
    match lam {
        Lambda::Lvar(id) => id.same(target),
        Lambda::LglobalModule(_, _) | Lambda::Lconst(_) => false,
        Lambda::Lapply(apply) => {
            lambda_hits_variable(target, &apply.ap_func)
                || apply
                    .ap_args
                    .iter()
                    .any(|arg| lambda_hits_variable(target, arg))
        }
        Lambda::Lfunction(func) => lambda_hits_variable(target, &func.body),
        Lambda::Llet(_, _, value, body) => {
            lambda_hits_variable(target, value) || lambda_hits_variable(target, body)
        }
        Lambda::Lletrec(bindings, body) => {
            lambda_hits_variable(target, body)
                || bindings
                    .iter()
                    .any(|(_, lam)| lambda_hits_variable(target, lam))
        }
        Lambda::Lprim(info) => info
            .args
            .iter()
            .any(|arg| lambda_hits_variable(target, arg)),
        Lambda::Lswitch(arg, switch) => {
            lambda_hits_variable(target, arg)
                || switch
                    .sw_consts
                    .iter()
                    .any(|(_, lam)| lambda_hits_variable(target, lam))
                || switch
                    .sw_blocks
                    .iter()
                    .any(|(_, lam)| lambda_hits_variable(target, lam))
                || switch
                    .sw_failaction
                    .as_deref()
                    .is_some_and(|lam| lambda_hits_variable(target, lam))
        }
        Lambda::LstringSwitch(arg, cases, default) => {
            lambda_hits_variable(target, arg)
                || cases
                    .iter()
                    .any(|(_, lam)| lambda_hits_variable(target, lam))
                || default
                    .as_deref()
                    .is_some_and(|lam| lambda_hits_variable(target, lam))
        }
        Lambda::LstaticRaise(_, args) => args.iter().any(|arg| lambda_hits_variable(target, arg)),
        Lambda::LstaticCatch(body, _, handler) | Lambda::LtryWith(body, _, handler) => {
            lambda_hits_variable(target, body) || lambda_hits_variable(target, handler)
        }
        Lambda::LifThenElse(cond, then_, else_) => {
            lambda_hits_variable(target, cond)
                || lambda_hits_variable(target, then_)
                || lambda_hits_variable(target, else_)
        }
        Lambda::Lsequence(first, second) | Lambda::Lwhile(first, second) => {
            lambda_hits_variable(target, first) || lambda_hits_variable(target, second)
        }
        Lambda::Lfor(_, start, end, _, body) => {
            lambda_hits_variable(target, start)
                || lambda_hits_variable(target, end)
                || lambda_hits_variable(target, body)
        }
        Lambda::Lassign(id, value) => id.same(target) || lambda_hits_variable(target, value),
    }
}

fn lambda_hits_variable_through_env(target: &Ident, lam: &Lambda, env: &SimplifyEnv) -> bool {
    // OCaml's lam_pass_remove_alias avoids non-terminating re-inlining of
    // recursive applications such as g(g). On the Rust JS-backend path, the
    // simplifier can expose the same cycle indirectly through alias and block
    // environments (for example g(x) where x is known to project back to g),
    // so we need to follow those simplifier-visible expansions as part of the
    // same guard.
    fn hits(
        target: &Ident,
        lam: &Lambda,
        env: &SimplifyEnv,
        visiting: &mut HashSet<Ident>,
    ) -> bool {
        match lam {
            Lambda::Lvar(id) => {
                if id.same(target) {
                    return true;
                }
                if !visiting.insert(id.clone()) {
                    return false;
                }
                let hit = env
                    .substitutions
                    .get(id)
                    .is_some_and(|substitution| hits(target, substitution, env, visiting))
                    || env.optional_blocks.get(id).is_some_and(|optional| {
                        hits(target, &optional.value, env, visiting)
                    })
                    || env.blocks.get(id).is_some_and(|block| {
                        block
                            .elements
                            .iter()
                            .filter_map(BlockElement::as_simple_form)
                            .any(|value| hits(target, value, env, visiting))
                    });
                visiting.remove(id);
                hit
            }
            Lambda::LglobalModule(_, _) | Lambda::Lconst(_) => false,
            Lambda::Lapply(apply) => {
                hits(target, &apply.ap_func, env, visiting)
                    || apply
                        .ap_args
                        .iter()
                        .any(|arg| hits(target, arg, env, visiting))
            }
            Lambda::Lfunction(func) => hits(target, &func.body, env, visiting),
            Lambda::Llet(_, _, value, body) => {
                hits(target, value, env, visiting) || hits(target, body, env, visiting)
            }
            Lambda::Lletrec(bindings, body) => {
                hits(target, body, env, visiting)
                    || bindings
                        .iter()
                        .any(|(_, lam)| hits(target, lam, env, visiting))
            }
            Lambda::Lprim(info) => info.args.iter().any(|arg| hits(target, arg, env, visiting)),
            Lambda::Lswitch(arg, switch) => {
                hits(target, arg, env, visiting)
                    || switch
                        .sw_consts
                        .iter()
                        .any(|(_, lam)| hits(target, lam, env, visiting))
                    || switch
                        .sw_blocks
                        .iter()
                        .any(|(_, lam)| hits(target, lam, env, visiting))
                    || switch
                        .sw_failaction
                        .as_deref()
                        .is_some_and(|lam| hits(target, lam, env, visiting))
            }
            Lambda::LstringSwitch(arg, cases, default) => {
                hits(target, arg, env, visiting)
                    || cases
                        .iter()
                        .any(|(_, lam)| hits(target, lam, env, visiting))
                    || default
                        .as_deref()
                        .is_some_and(|lam| hits(target, lam, env, visiting))
            }
            Lambda::LstaticRaise(_, args) => args
                .iter()
                .any(|arg| hits(target, arg, env, visiting)),
            Lambda::LstaticCatch(body, _, handler) | Lambda::LtryWith(body, _, handler) => {
                hits(target, body, env, visiting) || hits(target, handler, env, visiting)
            }
            Lambda::LifThenElse(cond, then_, else_) => {
                hits(target, cond, env, visiting)
                    || hits(target, then_, env, visiting)
                    || hits(target, else_, env, visiting)
            }
            Lambda::Lsequence(first, second) | Lambda::Lwhile(first, second) => {
                hits(target, first, env, visiting) || hits(target, second, env, visiting)
            }
            Lambda::Lfor(_, start, end, _, body) => {
                hits(target, start, env, visiting)
                    || hits(target, end, env, visiting)
                    || hits(target, body, env, visiting)
            }
            Lambda::Lassign(id, value) => id.same(target) || hits(target, value, env, visiting),
        }
    }

    let mut visiting = HashSet::new();
    hits(target, lam, env, &mut visiting)
}

fn inlineable_local_function(value: &Lambda) -> Option<LFunction> {
    match value {
        Lambda::Lfunction(func) => Some(func.clone()),
        Lambda::Lprim(crate::lambda::PrimInfo {
            primitive: Primitive::PjsFnMake(arity),
            args,
            ..
        }) => match args.as_slice() {
            [Lambda::Lfunction(func)] if func.arity == *arity => Some(func.clone()),
            _ => None,
        },
        Lambda::Lprim(crate::lambda::PrimInfo {
            primitive: Primitive::PjsFnMakeUnit,
            args,
            ..
        }) => match args.as_slice() {
            [Lambda::Lfunction(func)] => {
                let mut func = func.clone();
                if matches!(func.params.as_slice(), [param] if param.name() == "param") {
                    func.attr.one_unit_arg = true;
                }
                Some(func)
            }
            _ => None,
        },
        _ => None,
    }
}

fn inlineable_direct_wrapper_function(value: &Lambda) -> Option<LFunction> {
    match value {
        Lambda::Lprim(crate::lambda::PrimInfo {
            primitive: Primitive::PjsFnMake(arity),
            args,
            ..
        }) => match args.as_slice() {
            [Lambda::Lfunction(func)] if func.arity == *arity => Some(func.clone()),
            _ => None,
        },
        Lambda::Lprim(crate::lambda::PrimInfo {
            primitive: Primitive::PjsFnMakeUnit,
            args,
            ..
        }) => match args.as_slice() {
            [Lambda::Lfunction(func)] => {
                let mut func = func.clone();
                if matches!(func.params.as_slice(), [param] if param.name() == "param") {
                    func.attr.one_unit_arg = true;
                }
                Some(func)
            }
            _ => None,
        },
        _ => None,
    }
}

fn block_element_of_lambda(value: &Lambda) -> BlockElement {
    match value {
        Lambda::Lvar(_) | Lambda::Lconst(_) => BlockElement::Simple(value.clone()),
        Lambda::Lprim(info)
            if matches!(
                &info.primitive,
                Primitive::Pfield(_, FieldDbgInfo::Module { .. })
            ) && matches!(
                info.args.as_slice(),
                [Lambda::LglobalModule(_, _) | Lambda::Lvar(_)]
            ) =>
        {
            BlockElement::Simple(value.clone())
        }
        _ => BlockElement::Na,
    }
}

fn constant_block_field(
    tag_info: &TagInfo,
    elements: &[Constant],
    index: i32,
    dbg: &FieldDbgInfo,
) -> Option<Constant> {
    if index < 0 {
        return None;
    }

    let index = index as usize;
    match (tag_info, dbg) {
        (TagInfo::Module(fields), _) => dbg
            .name()
            .and_then(|name| fields.iter().position(|field_name| field_name == name))
            .and_then(|position| elements.get(position))
            .filter(|constant| !constant.is_allocating())
            .cloned(),
        (TagInfo::Record { fields, .. }, _) | (TagInfo::RecordInlined { fields, .. }, _) => dbg
            .name()
            .and_then(|name| fields.iter().position(|(field_name, _)| field_name == name))
            .and_then(|position| elements.get(position))
            .filter(|constant| !constant.is_allocating())
            .cloned(),
        (TagInfo::RecordExt { fields, .. }, _) => dbg
            .name()
            .and_then(|name| fields.iter().position(|field_name| field_name == name))
            .and_then(|position| elements.get(position))
            .filter(|constant| !constant.is_allocating())
            .cloned(),
        _ => elements
            .get(index)
            .filter(|constant| !constant.is_allocating())
            .cloned(),
    }
}

fn block_field<'a>(
    block: &'a ImmutableBlockInfo,
    index: i32,
    dbg: &FieldDbgInfo,
) -> Option<&'a BlockElement> {
    if index < 0 {
        return None;
    }

    match (&block.tag_info, dbg) {
        (TagInfo::Module(fields), _) => dbg
            .name()
            .and_then(|name| fields.iter().position(|field_name| field_name == name))
            .and_then(|position| block.elements.get(position)),
        (TagInfo::Record { fields, .. }, _) | (TagInfo::RecordInlined { fields, .. }, _) => dbg
            .name()
            .and_then(|name| fields.iter().position(|(field_name, _)| field_name == name))
            .and_then(|position| block.elements.get(position)),
        (TagInfo::RecordExt { fields, .. }, _) => dbg
            .name()
            .and_then(|name| fields.iter().position(|field_name| field_name == name))
            .and_then(|position| block.elements.get(position)),
        _ => block.elements.get(index as usize),
    }
}

fn simplify_apply(apply: &Apply, env: &SimplifyEnv, exports: &HashSet<Ident>) -> Lambda {
    let args: Vec<_> = apply
        .ap_args
        .iter()
        .map(|arg| simplify_with_env(arg, env, exports))
        .collect();

    if let Lambda::Lvar(id) = &*apply.ap_func {
        if !args
            .iter()
            .any(|arg| lambda_hits_variable_through_env(id, arg, env))
        {
            if let Some(func) = env.functions.get(id) {
                if should_inline_named_function(func, &args) {
                    let reduced =
                        beta_reduce::no_names_beta_reduce(&func.params, &func.body, &args);
                    return simplify_with_env(&reduced, env, exports);
                }
            }
        }
    }

    let func = simplify_with_env(&apply.ap_func, env, exports);
    if let Lambda::Lvar(id) = &func {
        if !args
            .iter()
            .any(|arg| lambda_hits_variable_through_env(id, arg, env))
        {
            if let Some(func) = env.functions.get(id) {
                if should_inline_named_function(func, &args) {
                    let reduced =
                        beta_reduce::no_names_beta_reduce(&func.params, &func.body, &args);
                    return simplify_with_env(&reduced, env, exports);
                }
            }
        }
    }
    if !matches!(apply.ap_func.as_ref(), Lambda::Lapply(_)) {
        if let Some(inline_func) = inlineable_direct_wrapper_function(&func) {
            if should_inline_direct_function(&inline_func, &args) {
                let reduced = beta_reduce::no_names_beta_reduce(
                    &inline_func.params,
                    &inline_func.body,
                    &args,
                );
                return simplify_with_env(&reduced, env, exports);
            }
        }
    }
    if let Lambda::Lfunction(inline_func) = &func {
        if should_inline_direct_function(inline_func, &args) {
            let reduced =
                beta_reduce::no_names_beta_reduce(&inline_func.params, &inline_func.body, &args);
            return simplify_with_env(&reduced, env, exports);
        }
    }

    Lambda::Lapply(Apply {
        ap_func: Box::new(func),
        ap_args: args,
        ap_info: apply.ap_info.clone(),
        ap_transformed_jsx: apply.ap_transformed_jsx,
    })
}

fn should_inline_named_function(func: &LFunction, args: &[Lambda]) -> bool {
    func.params.len() == args.len()
        && analysis::lfunction_can_be_inlined(func)
        && analysis::ok_to_inline_fun_when_app(func, args)
}

fn should_inline_direct_function(func: &LFunction, args: &[Lambda]) -> bool {
    func.params.len() == args.len() && analysis::lfunction_can_be_inlined(func)
}

fn collect_inlineable_functions(lam: &Lambda) -> HashMap<Ident, LFunction> {
    fn collect_into(lam: &Lambda, functions: &mut HashMap<Ident, LFunction>) {
        match lam {
            Lambda::Lvar(_) | Lambda::LglobalModule(_, _) | Lambda::Lconst(_) => {}
            Lambda::Lapply(apply) => {
                collect_into(&apply.ap_func, functions);
                for arg in &apply.ap_args {
                    collect_into(arg, functions);
                }
            }
            Lambda::Lfunction(func) => collect_into(&func.body, functions),
            Lambda::Llet(kind, id, value, body) => {
                collect_into(value, functions);
                if *kind != LetKind::Variable {
                    if let Some(func) = inlineable_local_function(value) {
                        if analysis::lfunction_can_be_inlined(&func) {
                            functions.insert(id.clone(), func);
                        }
                    }
                }
                collect_into(body, functions);
            }
            Lambda::Lletrec(bindings, body) => {
                for (_, expr) in bindings {
                    collect_into(expr, functions);
                }
                collect_into(body, functions);
            }
            Lambda::Lprim(info) => {
                for arg in &info.args {
                    collect_into(arg, functions);
                }
            }
            Lambda::Lswitch(scrutinee, switch) => {
                collect_into(scrutinee, functions);
                for (_, lam) in &switch.sw_consts {
                    collect_into(lam, functions);
                }
                for (_, lam) in &switch.sw_blocks {
                    collect_into(lam, functions);
                }
                if let Some(failaction) = &switch.sw_failaction {
                    collect_into(failaction, functions);
                }
            }
            Lambda::LstringSwitch(scrutinee, cases, default) => {
                collect_into(scrutinee, functions);
                for (_, lam) in cases {
                    collect_into(lam, functions);
                }
                if let Some(default) = default {
                    collect_into(default, functions);
                }
            }
            Lambda::LstaticRaise(_, args) => {
                for arg in args {
                    collect_into(arg, functions);
                }
            }
            Lambda::LstaticCatch(body, _, handler) | Lambda::LtryWith(body, _, handler) => {
                collect_into(body, functions);
                collect_into(handler, functions);
            }
            Lambda::LifThenElse(cond, then_, else_) => {
                collect_into(cond, functions);
                collect_into(then_, functions);
                collect_into(else_, functions);
            }
            Lambda::Lsequence(first, second) | Lambda::Lwhile(first, second) => {
                collect_into(first, functions);
                collect_into(second, functions);
            }
            Lambda::Lfor(_, start, end, _, body) => {
                collect_into(start, functions);
                collect_into(end, functions);
                collect_into(body, functions);
            }
            Lambda::Lassign(_, value) => collect_into(value, functions),
        }
    }

    let mut functions = HashMap::new();
    collect_into(lam, &mut functions);
    functions
}

fn substitution_candidate(kind: LetKind, value: &Lambda) -> Option<Lambda> {
    if kind == LetKind::Variable {
        return None;
    }

    match value {
        Lambda::Lvar(_) | Lambda::LglobalModule(_, _) => Some(value.clone()),
        Lambda::Lconst(constant) if !constant.is_allocating() => Some(value.clone()),
        Lambda::Lprim(info)
            if matches!(
                (&info.primitive, info.args.as_slice()),
                (
                    Primitive::Pfield(_, FieldDbgInfo::Module { .. }),
                    [Lambda::LglobalModule(_, _) | Lambda::Lvar(_)]
                )
            ) =>
        {
            Some(value.clone())
        }
        _ => None,
    }
}

impl BlockElement {
    fn as_simple_form(&self) -> Option<&Lambda> {
        match self {
            BlockElement::Na => None,
            BlockElement::Simple(value) => Some(value),
        }
    }
}

fn collect_exported_idents(lam: &Lambda) -> HashSet<Ident> {
    let mut exports = HashSet::new();
    collect_exported_idents_into(lam, &mut exports);
    exports
}

fn collect_exported_idents_into(lam: &Lambda, exports: &mut HashSet<Ident>) {
    match lam {
        Lambda::Lvar(_) | Lambda::LglobalModule(_, _) | Lambda::Lconst(_) => {}
        Lambda::Lapply(apply) => {
            collect_exported_idents_into(&apply.ap_func, exports);
            for arg in &apply.ap_args {
                collect_exported_idents_into(arg, exports);
            }
        }
        Lambda::Lfunction(func) => collect_exported_idents_into(&func.body, exports),
        Lambda::Llet(_, _, value, body) => {
            collect_exported_idents_into(value, exports);
            collect_exported_idents_into(body, exports);
        }
        Lambda::Lletrec(bindings, body) => {
            for (_, expr) in bindings {
                collect_exported_idents_into(expr, exports);
            }
            collect_exported_idents_into(body, exports);
        }
        Lambda::Lprim(info) => {
            if let Primitive::Pmakeblock(_, TagInfo::ModuleExport(ids), _) = &info.primitive {
                exports.extend(ids.iter().cloned());
            }
            for arg in &info.args {
                collect_exported_idents_into(arg, exports);
            }
        }
        Lambda::Lswitch(scrutinee, switch) => {
            collect_exported_idents_into(scrutinee, exports);
            for (_, lam) in &switch.sw_consts {
                collect_exported_idents_into(lam, exports);
            }
            for (_, lam) in &switch.sw_blocks {
                collect_exported_idents_into(lam, exports);
            }
            if let Some(failaction) = &switch.sw_failaction {
                collect_exported_idents_into(failaction, exports);
            }
        }
        Lambda::LstringSwitch(scrutinee, cases, default) => {
            collect_exported_idents_into(scrutinee, exports);
            for (_, lam) in cases {
                collect_exported_idents_into(lam, exports);
            }
            if let Some(default) = default {
                collect_exported_idents_into(default, exports);
            }
        }
        Lambda::LstaticRaise(_, args) => {
            for arg in args {
                collect_exported_idents_into(arg, exports);
            }
        }
        Lambda::LstaticCatch(body, _, handler)
        | Lambda::LtryWith(body, _, handler)
        | Lambda::Lsequence(body, handler)
        | Lambda::Lwhile(body, handler) => {
            collect_exported_idents_into(body, exports);
            collect_exported_idents_into(handler, exports);
        }
        Lambda::LifThenElse(cond, then_, else_) => {
            collect_exported_idents_into(cond, exports);
            collect_exported_idents_into(then_, exports);
            collect_exported_idents_into(else_, exports);
        }
        Lambda::Lfor(_, start, end, _, body) => {
            collect_exported_idents_into(start, exports);
            collect_exported_idents_into(end, exports);
            collect_exported_idents_into(body, exports);
        }
        Lambda::Lassign(_, value) => collect_exported_idents_into(value, exports),
    }
}

#[cfg(test)]
mod tests {
    use crate::ident::Ident;
    use crate::lambda::compat::{FieldDbgInfo, LetKind};
    use crate::lambda::constant::Constant;
    use crate::lambda::primitive::{
        ExternalArgAttr, ExternalObjLabel, ExternalObjSpec, Mutable, Primitive,
    };
    use crate::lambda::{
        ApInfo, Apply, ApplyStatus, FunctionAttribute, InlineAttribute, Lambda, TagInfo,
    };
    use crate::location::Location;

    use super::simplify_for_js_backend;

    #[test]
    fn inlines_known_local_function_applications() {
        let fun_id = Ident::create_local("mo");
        let param = Ident::create_local("name");
        let options = Ident::create_local("options");
        let lambda = Lambda::let_(
            LetKind::Alias,
            fun_id.clone(),
            Lambda::function_(
                1,
                vec![param.clone()],
                Lambda::prim(
                    Primitive::PjsObjectCreate(vec![ExternalObjSpec {
                        obj_arg_type: ExternalArgAttr::Nothing,
                        obj_arg_label: ExternalObjLabel::Label {
                            name: "name".to_string(),
                        },
                    }]),
                    vec![Lambda::var(param.clone())],
                    Location::none(),
                ),
                FunctionAttribute::default(),
            ),
            Lambda::let_(
                LetKind::Strict,
                options.clone(),
                Lambda::Lapply(Apply {
                    ap_func: Box::new(Lambda::var(fun_id)),
                    ap_args: vec![Lambda::const_(Constant::String {
                        s: "foo".to_string(),
                        delim: None,
                    })],
                    ap_info: ApInfo {
                        loc: Location::none(),
                        inlined: InlineAttribute::Default,
                        status: crate::lambda::ApplyStatus::Na,
                    },
                    ap_transformed_jsx: false,
                }),
                Lambda::var(options),
            ),
        );

        let simplified = simplify_for_js_backend(&lambda);
        let Lambda::Llet(_, _, value, _) = simplified else {
            panic!("expected let-binding for options");
        };
        let Lambda::Lprim(info) = *value else {
            panic!("expected inlined primitive");
        };
        assert!(matches!(info.primitive, Primitive::PjsObjectCreate(_)));
    }

    #[test]
    fn does_not_reinline_named_function_through_block_aliases() {
        let g = Ident::create_local("g");
        let x = Ident::create_local("x");
        let param = Ident::create_local("param");
        let extracted = Ident::create_local("v");
        let arg = Ident::create_local("arg");

        let g_body = Lambda::let_(
            LetKind::Alias,
            extracted.clone(),
            Lambda::prim(
                Primitive::Pfield(0, FieldDbgInfo::Variant),
                vec![Lambda::var(param.clone())],
                Location::none(),
            ),
            Lambda::Lapply(Apply {
                ap_func: Box::new(Lambda::var(extracted)),
                ap_args: vec![Lambda::var(param.clone())],
                ap_info: ApInfo {
                    loc: Location::none(),
                    inlined: InlineAttribute::Default,
                    status: ApplyStatus::Uncurry,
                },
                ap_transformed_jsx: false,
            }),
        );

        let lambda = Lambda::let_(
            LetKind::Strict,
            g.clone(),
            Lambda::prim(
                Primitive::PjsFnMake(1),
                vec![Lambda::function_(
                    1,
                    vec![param],
                    g_body,
                    FunctionAttribute::default(),
                )],
                Location::none(),
            ),
            Lambda::let_(
                LetKind::Strict,
                x.clone(),
                Lambda::prim(
                    Primitive::Pmakeblock(
                        0,
                        TagInfo::constructor("A", 1, 0),
                        Mutable::Immutable,
                    ),
                    vec![Lambda::var(g.clone())],
                    Location::none(),
                ),
                Lambda::let_(
                    LetKind::Strict,
                    arg,
                    Lambda::Lapply(Apply {
                        ap_func: Box::new(Lambda::var(g.clone())),
                        ap_args: vec![Lambda::var(x.clone())],
                        ap_info: ApInfo {
                            loc: Location::none(),
                            inlined: InlineAttribute::Default,
                            status: ApplyStatus::Uncurry,
                        },
                        ap_transformed_jsx: false,
                    }),
                    Lambda::var(x.clone()),
                ),
            ),
        );

        let simplified = simplify_for_js_backend(&lambda);
        let rendered = crate::lambda::print::lambda_to_string(&simplified);
        assert!(
            rendered.contains("(apply g x)"),
            "expected simplified lambda to keep the recursive-looking application instead of re-inlining forever: {rendered}"
        );
    }

    #[test]
    fn removes_unused_pure_let_bindings() {
        let unused = Ident::create_local("unused");
        let lambda = Lambda::let_(
            LetKind::Strict,
            unused,
            Lambda::const_(Constant::int(1)),
            Lambda::const_(Constant::int(2)),
        );

        let simplified = simplify_for_js_backend(&lambda);
        assert!(matches!(
            simplified,
            Lambda::Lconst(Constant::Int { i: 2, .. })
        ));
    }

    #[test]
    fn refines_immediate_module_field_reads_over_awaited_imports() {
        let imported = Ident::create_local("M3");
        let lambda = Lambda::let_(
            LetKind::Strict,
            imported.clone(),
            Lambda::prim(
                Primitive::Pawait,
                vec![Lambda::prim(
                    Primitive::Pimport,
                    vec![Lambda::global_module(
                        Ident::create_persistent("Belt_List"),
                        true,
                    )],
                    Location::none(),
                )],
                Location::none(),
            ),
            Lambda::prim(
                Primitive::Pfield(
                    36,
                    FieldDbgInfo::Module {
                        name: "forEach".to_string(),
                    },
                ),
                vec![Lambda::var(imported)],
                Location::none(),
            ),
        );

        let simplified = simplify_for_js_backend(&lambda);
        let Lambda::Lprim(crate::lambda::PrimInfo {
            primitive: Primitive::Pfield(36, FieldDbgInfo::Module { name }),
            args,
            ..
        }) = simplified
        else {
            panic!("expected the let-bound import field read to inline into the primitive");
        };

        assert_eq!(name, "forEach");
        assert!(matches!(
            args.as_slice(),
            [Lambda::Lprim(crate::lambda::PrimInfo {
                primitive: Primitive::Pawait,
                args,
                ..
            })] if matches!(
                args.as_slice(),
                [Lambda::Lprim(crate::lambda::PrimInfo {
                    primitive: Primitive::Pimport,
                    args,
                    ..
                })] if matches!(
                    args.as_slice(),
                    [Lambda::LglobalModule(id, true)] if id.name() == "Belt_List"
                )
            )
        ));
    }

    #[test]
    fn aliases_module_field_reads_from_local_module_bindings_into_tuple_blocks() {
        let imported = Ident::create_local("MS");
        let projected = Ident::create_local("b");
        let lambda = Lambda::let_(
            LetKind::Strict,
            imported.clone(),
            Lambda::prim(
                Primitive::Pawait,
                vec![Lambda::prim(
                    Primitive::Pimport,
                    vec![Lambda::global_module(
                        Ident::create_persistent("Belt_MapString"),
                        true,
                    )],
                    Location::none(),
                )],
                Location::none(),
            ),
            Lambda::let_(
                LetKind::Strict,
                projected.clone(),
                Lambda::prim(
                    Primitive::Pfield(
                        36,
                        FieldDbgInfo::Module {
                            name: "forEach".to_string(),
                        },
                    ),
                    vec![Lambda::var(imported.clone())],
                    Location::none(),
                ),
                Lambda::prim(
                    Primitive::Pmakeblock(
                        0,
                        TagInfo::Tuple,
                        crate::lambda::primitive::Mutable::Immutable,
                    ),
                    vec![
                        Lambda::const_(Constant::int(0)),
                        Lambda::var(projected.clone()),
                    ],
                    Location::none(),
                ),
            ),
        );

        let simplified = simplify_for_js_backend(&lambda);
        let Lambda::Llet(_, kept_id, kept_value, kept_body) = simplified else {
            panic!("expected the awaited import binding to remain");
        };
        assert_eq!(kept_id, imported);
        assert!(matches!(
            *kept_value,
            Lambda::Lprim(crate::lambda::PrimInfo {
                primitive: Primitive::Pawait,
                ..
            })
        ));
        let Lambda::Lprim(crate::lambda::PrimInfo {
            primitive:
                Primitive::Pmakeblock(0, TagInfo::Tuple, crate::lambda::primitive::Mutable::Immutable),
            args,
            ..
        }) = *kept_body
        else {
            panic!("expected the local module field alias to inline into the tuple block");
        };
        assert!(matches!(
            args.as_slice(),
            [
                Lambda::Lconst(Constant::Int { i: 0, .. }),
                Lambda::Lprim(crate::lambda::PrimInfo {
                    primitive:
                        Primitive::Pfield(
                            36,
                            FieldDbgInfo::Module {
                                name,
                            },
                        ),
                    args,
                    ..
                })
            ] if name == "forEach"
                && matches!(args.as_slice(), [Lambda::Lvar(id)] if id == &imported)
        ));
    }

    #[test]
    fn keeps_unused_impure_lets_as_sequences() {
        let unused = Ident::create_local("unused");
        let lambda = Lambda::let_(
            LetKind::Strict,
            unused,
            Lambda::prim(
                Primitive::PjsCall {
                    prim_name: "sideEffect".to_string(),
                    arg_types: vec![],
                    ffi: crate::lambda::primitive::ExternalFfiSpec {
                        kind: crate::lambda::primitive::ExternalFfiKind::Default,
                        spec: None,
                        obj_params: None,
                        return_wrapper: crate::lambda::primitive::ExternalReturnWrapper::Identity,
                        inline_constant: None,
                    },
                    dynamic_import: false,
                    transformed_jsx: false,
                },
                vec![],
                Location::none(),
            ),
            Lambda::const_(Constant::int(2)),
        );

        let simplified = simplify_for_js_backend(&lambda);
        let Lambda::Lsequence(first, second) = simplified else {
            panic!("expected side-effect sequence");
        };
        assert!(matches!(
            *first,
            Lambda::Lprim(crate::lambda::PrimInfo {
                primitive: Primitive::PjsCall { .. },
                ..
            })
        ));
        assert!(matches!(
            *second,
            Lambda::Lconst(Constant::Int { i: 2, .. })
        ));
    }

    #[test]
    fn keeps_exported_alias_binding_but_inlines_constant_rhs() {
        let x = Ident::create_local("x");
        let xx = Ident::create_local("xx");
        let export_block = Lambda::prim(
            Primitive::Pmakeblock(
                0,
                TagInfo::ModuleExport(vec![x.clone(), xx.clone()]),
                Mutable::Immutable,
            ),
            vec![Lambda::var(x.clone()), Lambda::var(xx.clone())],
            Location::none(),
        );
        let lambda = Lambda::let_(
            LetKind::Strict,
            x.clone(),
            Lambda::const_(Constant::int(1)),
            Lambda::let_(LetKind::Strict, xx.clone(), Lambda::var(x), export_block),
        );

        let simplified = simplify_for_js_backend(&lambda);
        let Lambda::Llet(_, _, _, body) = simplified else {
            panic!("expected exported x binding");
        };
        let Lambda::Llet(_, _, value, _) = *body else {
            panic!("expected exported xx binding");
        };
        assert!(matches!(*value, Lambda::Lconst(Constant::Int { i: 1, .. })));
    }

    #[test]
    fn simplifies_module_alias_export_payloads_before_export_coercion() {
        let url = Ident::create_local("URL");
        let my_url = Ident::create_local("MyURL");
        let export_block = Lambda::prim(
            Primitive::Pmakeblock(
                0,
                TagInfo::ModuleExport(vec![url.clone(), my_url.clone()]),
                Mutable::Immutable,
            ),
            vec![Lambda::var(url.clone()), Lambda::var(my_url.clone())],
            Location::none(),
        );
        let lambda = Lambda::let_(
            LetKind::Strict,
            url.clone(),
            Lambda::prim(
                Primitive::Pmakeblock(
                    0,
                    TagInfo::module(vec!["revokeObjectURL".to_string()]),
                    Mutable::Immutable,
                ),
                vec![],
                Location::none(),
            ),
            Lambda::let_(
                LetKind::Alias,
                my_url.clone(),
                Lambda::const_(Constant::ModuleAlias),
                export_block,
            ),
        );

        let simplified = simplify_for_js_backend(&lambda);
        let Lambda::Llet(_, kept_url, _, body) = simplified else {
            panic!("expected the URL binding to remain");
        };
        assert_eq!(kept_url, url);
        let Lambda::Llet(_, kept_alias, _, body) = *body else {
            panic!("expected the module-alias binding to remain until export coercion");
        };
        assert_eq!(kept_alias, my_url);
        let Lambda::Lprim(crate::lambda::PrimInfo {
            primitive: Primitive::Pmakeblock(_, TagInfo::ModuleExport(export_ids), _),
            args,
            ..
        }) = *body
        else {
            panic!("expected the export block to remain at the tail");
        };
        assert_eq!(export_ids, vec![url.clone(), my_url.clone()]);
        assert!(matches!(
            args.as_slice(),
            [Lambda::Lvar(first), Lambda::Lconst(Constant::ModuleAlias)]
                if *first == url
        ));
    }

    #[test]
    fn inlines_direct_function_applications_without_named_call_profitability_gate() {
        let outer = Ident::create_local("x");
        let inner = Ident::create_local("f");
        let lambda = Lambda::Lapply(Apply {
            ap_func: Box::new(Lambda::function_(
                1,
                vec![outer],
                Lambda::function_(
                    1,
                    vec![inner.clone()],
                    Lambda::const_(Constant::int(0)),
                    FunctionAttribute::default(),
                ),
                FunctionAttribute::default(),
            )),
            ap_args: vec![Lambda::const_(Constant::String {
                s: "".to_string(),
                delim: None,
            })],
            ap_info: ApInfo {
                loc: Location::none(),
                inlined: InlineAttribute::Default,
                status: crate::lambda::ApplyStatus::Na,
            },
            ap_transformed_jsx: false,
        });

        let simplified = simplify_for_js_backend(&lambda);
        let Lambda::Lfunction(func) = simplified else {
            panic!("expected the direct function application to beta-reduce");
        };
        assert_eq!(func.params, vec![inner]);
        assert!(matches!(
            *func.body,
            Lambda::Lconst(Constant::Int { i: 0, .. })
        ));
    }

    #[test]
    fn removes_unused_pure_sequences() {
        let lambda = Lambda::seq(
            Lambda::const_(Constant::int(1)),
            Lambda::const_(Constant::int(2)),
        );

        let simplified = simplify_for_js_backend(&lambda);
        assert!(matches!(
            simplified,
            Lambda::Lconst(Constant::Int { i: 2, .. })
        ));
    }

    #[test]
    fn flattens_immutable_module_block_field_aliases() {
        let field_fn = Ident::create_local("myField");
        let include = Ident::create_local("include");
        let projected = Ident::create_local("projected");
        let param = Ident::create_local("param");
        let lambda = Lambda::let_(
            LetKind::Strict,
            field_fn.clone(),
            Lambda::function_(
                1,
                vec![param.clone()],
                Lambda::prim(
                    Primitive::Pfield(
                        0,
                        FieldDbgInfo::Record {
                            name: "myField".to_string(),
                            mutable_flag: crate::parser::ast::MutableFlag::Immutable,
                        },
                    ),
                    vec![Lambda::var(param)],
                    Location::none(),
                ),
                FunctionAttribute::default(),
            ),
            Lambda::let_(
                LetKind::Strict,
                include.clone(),
                Lambda::prim(
                    Primitive::Pmakeblock(
                        0,
                        TagInfo::Module(vec!["myField".to_string()]),
                        Mutable::Immutable,
                    ),
                    vec![Lambda::var(field_fn.clone())],
                    Location::none(),
                ),
                Lambda::let_(
                    LetKind::Alias,
                    projected.clone(),
                    Lambda::prim(
                        Primitive::Pfield(
                            0,
                            FieldDbgInfo::Module {
                                name: "myField".to_string(),
                            },
                        ),
                        vec![Lambda::var(include)],
                        Location::none(),
                    ),
                    Lambda::var(projected),
                ),
            ),
        );

        let simplified = simplify_for_js_backend(&lambda);
        let Lambda::Llet(_, kept_id, kept_value, kept_body) = simplified else {
            panic!("expected the projected function binding to remain");
        };
        assert_eq!(kept_id, field_fn);
        assert!(matches!(*kept_value, Lambda::Lfunction(_)));
        let Lambda::Lvar(body_id) = *kept_body else {
            panic!("expected the body to reference the original function");
        };
        assert_eq!(body_id, kept_id);
    }

    #[test]
    fn deep_flattens_nested_include_blocks_before_beta_reducing_field_accessors() {
        let field_fn = Ident::create_local("myField");
        let include_inner = Ident::create_local("include");
        let projected_inner = Ident::create_local("myField");
        let include_outer = Ident::create_local("include");
        let exported = Ident::create_local("myField");
        let param = Ident::create_local("param");

        let accessor = Lambda::function_(
            1,
            vec![param.clone()],
            Lambda::prim(
                Primitive::Pfield(
                    0,
                    FieldDbgInfo::Record {
                        name: "myField".to_string(),
                        mutable_flag: crate::parser::ast::MutableFlag::Immutable,
                    },
                ),
                vec![Lambda::var(param)],
                Location::none(),
            ),
            FunctionAttribute::default(),
        );

        let lambda = Lambda::let_(
            LetKind::Strict,
            include_outer.clone(),
            Lambda::let_(
                LetKind::Strict,
                include_inner.clone(),
                Lambda::let_(
                    LetKind::Strict,
                    field_fn.clone(),
                    accessor,
                    Lambda::prim(
                        Primitive::Pmakeblock(
                            0,
                            TagInfo::module(vec!["myField".to_string()]),
                            Mutable::Immutable,
                        ),
                        vec![Lambda::var(field_fn.clone())],
                        Location::none(),
                    ),
                ),
                Lambda::let_(
                    LetKind::Alias,
                    projected_inner.clone(),
                    Lambda::prim(
                        Primitive::Pfield(
                            0,
                            FieldDbgInfo::Module {
                                name: "myField".to_string(),
                            },
                        ),
                        vec![Lambda::var(include_inner)],
                        Location::none(),
                    ),
                    Lambda::prim(
                        Primitive::Pmakeblock(
                            0,
                            TagInfo::module(vec!["myField".to_string()]),
                            Mutable::Immutable,
                        ),
                        vec![Lambda::var(projected_inner.clone())],
                        Location::none(),
                    ),
                ),
            ),
            Lambda::let_(
                LetKind::Alias,
                exported.clone(),
                Lambda::prim(
                    Primitive::Pfield(
                        0,
                        FieldDbgInfo::Module {
                            name: "myField".to_string(),
                        },
                    ),
                    vec![Lambda::var(include_outer)],
                    Location::none(),
                ),
                Lambda::var(exported),
            ),
        );

        let simplified = simplify_for_js_backend(&lambda);
        let Lambda::Llet(_, kept_id, kept_value, kept_body) = simplified else {
            panic!("expected the flattened accessor binding to remain");
        };
        assert_eq!(kept_id, field_fn);
        assert!(matches!(*kept_value, Lambda::Lfunction(_)));
        let Lambda::Lvar(body_id) = *kept_body else {
            panic!("expected the body to reference the original accessor binding");
        };
        assert_eq!(body_id, kept_id);
    }

    #[test]
    fn folds_record_field_from_constant_block() {
        let name = Ident::create_local("name");
        let lambda = Lambda::let_(
            LetKind::Strict,
            name.clone(),
            Lambda::prim(
                Primitive::Pfield(
                    1,
                    FieldDbgInfo::Record {
                        name: "name".to_string(),
                        mutable_flag: crate::parser::ast::MutableFlag::Immutable,
                    },
                ),
                vec![Lambda::const_(Constant::Block {
                    tag: 0,
                    tag_info: TagInfo::Record {
                        fields: vec![("number".to_string(), false), ("name".to_string(), false)],
                        mutable_flag: crate::parser::ast::MutableFlag::Immutable,
                    },
                    elements: vec![
                        Constant::int(42),
                        Constant::String {
                            s: "a".to_string(),
                            delim: None,
                        },
                    ],
                })],
                Location::none(),
            ),
            Lambda::var(name),
        );

        let simplified = simplify_for_js_backend(&lambda);
        let Lambda::Lconst(Constant::String { s, .. }) = simplified else {
            panic!("expected the record field read to fold to a string constant");
        };
        assert_eq!(s, "a");
    }

    #[test]
    fn inlines_single_use_alias_field_reads_into_module_blocks() {
        let source = Ident::create_local("source");
        let match_id = Ident::create_local("match");
        let set = Ident::create_local("set");
        let get = Ident::create_local("get");

        let lambda = Lambda::let_(
            LetKind::Strict,
            match_id.clone(),
            Lambda::var(source.clone()),
            Lambda::let_(
                LetKind::Alias,
                set.clone(),
                Lambda::prim(
                    Primitive::Pfield(1, FieldDbgInfo::Tuple),
                    vec![Lambda::var(match_id.clone())],
                    Location::none(),
                ),
                Lambda::let_(
                    LetKind::Alias,
                    get.clone(),
                    Lambda::prim(
                        Primitive::Pfield(0, FieldDbgInfo::Tuple),
                        vec![Lambda::var(match_id.clone())],
                        Location::none(),
                    ),
                    Lambda::prim(
                        Primitive::Pmakeblock(
                            0,
                            TagInfo::module(vec!["get".to_string(), "set".to_string()]),
                            Mutable::Immutable,
                        ),
                        vec![Lambda::var(get.clone()), Lambda::var(set.clone())],
                        Location::none(),
                    ),
                ),
            ),
        );

        let simplified = simplify_for_js_backend(&lambda);
        let Lambda::Lprim(crate::lambda::PrimInfo {
            primitive: Primitive::Pmakeblock(_, TagInfo::Module(fields), _),
            args,
            ..
        }) = simplified
        else {
            panic!("expected the alias lets to inline into the module block");
        };
        assert_eq!(fields, vec!["get".to_string(), "set".to_string()]);
        assert!(matches!(
            &args[0],
            Lambda::Lprim(crate::lambda::PrimInfo {
                primitive: Primitive::Pfield(0, FieldDbgInfo::Tuple),
                args,
                ..
            }) if matches!(args.as_slice(), [Lambda::Lvar(id)] if *id == source)
        ));
        assert!(matches!(
            &args[1],
            Lambda::Lprim(crate::lambda::PrimInfo {
                primitive: Primitive::Pfield(1, FieldDbgInfo::Tuple),
                args,
                ..
            }) if matches!(args.as_slice(), [Lambda::Lvar(id)] if *id == source)
        ));
    }

    #[test]
    fn does_not_inline_captured_single_use_aliases() {
        let source = Ident::create_local("source");
        let match_id = Ident::create_local("match");
        let projected = Ident::create_local("projected");

        let lambda = Lambda::let_(
            LetKind::Strict,
            match_id.clone(),
            Lambda::var(source.clone()),
            Lambda::let_(
                LetKind::Alias,
                projected.clone(),
                Lambda::prim(
                    Primitive::Pfield(0, FieldDbgInfo::Tuple),
                    vec![Lambda::var(match_id.clone())],
                    Location::none(),
                ),
                Lambda::function_(
                    0,
                    vec![],
                    Lambda::var(projected.clone()),
                    FunctionAttribute::default(),
                ),
            ),
        );

        let simplified = simplify_for_js_backend(&lambda);
        let Lambda::Llet(kind, kept_projected, projected_value, body) = simplified else {
            panic!("expected the captured alias binding to remain");
        };
        assert_eq!(kind, LetKind::Alias);
        assert_eq!(kept_projected, projected);
        assert!(matches!(
            *projected_value,
            Lambda::Lprim(crate::lambda::PrimInfo {
                primitive: Primitive::Pfield(0, FieldDbgInfo::Tuple),
                args,
                ..
            }) if matches!(args.as_slice(), [Lambda::Lvar(id)] if *id == source)
        ));
        let Lambda::Lfunction(func) = *body else {
            panic!("expected the captured alias to remain referenced from a closure");
        };
        assert!(matches!(
            *func.body,
            Lambda::Lvar(id) if id == projected
        ));
    }

    #[test]
    fn flattens_record_field_aliases_by_name() {
        let record = Ident::create_local("record");
        let name = Ident::create_local("name");
        let lambda = Lambda::let_(
            LetKind::Strict,
            record.clone(),
            Lambda::prim(
                Primitive::Pmakeblock(
                    0,
                    TagInfo::Record {
                        fields: vec![("number".to_string(), false), ("name".to_string(), false)],
                        mutable_flag: crate::parser::ast::MutableFlag::Immutable,
                    },
                    Mutable::Immutable,
                ),
                vec![
                    Lambda::const_(Constant::int(42)),
                    Lambda::const_(Constant::String {
                        s: "a".to_string(),
                        delim: None,
                    }),
                ],
                Location::none(),
            ),
            Lambda::let_(
                LetKind::Strict,
                name.clone(),
                Lambda::prim(
                    Primitive::Pfield(
                        0,
                        FieldDbgInfo::Record {
                            name: "name".to_string(),
                            mutable_flag: crate::parser::ast::MutableFlag::Immutable,
                        },
                    ),
                    vec![Lambda::var(record)],
                    Location::none(),
                ),
                Lambda::var(name),
            ),
        );

        let simplified = simplify_for_js_backend(&lambda);
        let Lambda::Lconst(Constant::String { s, .. }) = simplified else {
            panic!("expected the bound record field read to fold to a string constant");
        };
        assert_eq!(s, "a");
    }

    #[test]
    fn flattens_constant_record_block_bindings_by_name() {
        let record = Ident::create_local("record");
        let name = Ident::create_local("name");
        let lambda = Lambda::let_(
            LetKind::Strict,
            record.clone(),
            Lambda::const_(Constant::Block {
                tag: 0,
                tag_info: TagInfo::Record {
                    fields: vec![("number".to_string(), false), ("name".to_string(), false)],
                    mutable_flag: crate::parser::ast::MutableFlag::Immutable,
                },
                elements: vec![
                    Constant::int(42),
                    Constant::String {
                        s: "a".to_string(),
                        delim: None,
                    },
                ],
            }),
            Lambda::let_(
                LetKind::Strict,
                name.clone(),
                Lambda::prim(
                    Primitive::Pfield(
                        0,
                        FieldDbgInfo::Record {
                            name: "name".to_string(),
                            mutable_flag: crate::parser::ast::MutableFlag::Immutable,
                        },
                    ),
                    vec![Lambda::var(record)],
                    Location::none(),
                ),
                Lambda::var(name),
            ),
        );

        let simplified = simplify_for_js_backend(&lambda);
        let Lambda::Lconst(Constant::String { s, .. }) = simplified else {
            panic!("expected the bound constant-record field read to fold");
        };
        assert_eq!(s, "a");
    }

    #[test]
    fn folds_string_alias_chains() {
        let a0 = Ident::create_local("a0");
        let a1 = Ident::create_local("a1");
        let exported = Ident::create_local("a2");
        let export_block = Lambda::prim(
            Primitive::Pmakeblock(
                0,
                TagInfo::ModuleExport(vec![exported.clone()]),
                Mutable::Immutable,
            ),
            vec![Lambda::var(exported.clone())],
            Location::none(),
        );
        let lambda = Lambda::let_(
            LetKind::Strict,
            a0.clone(),
            Lambda::const_(Constant::string("hello ")),
            Lambda::let_(
                LetKind::Strict,
                a1.clone(),
                Lambda::var(a0),
                Lambda::let_(
                    LetKind::Strict,
                    exported.clone(),
                    Lambda::prim(
                        Primitive::Pstringadd,
                        vec![Lambda::var(a1), Lambda::const_(Constant::string("world"))],
                        Location::none(),
                    ),
                    export_block,
                ),
            ),
        );

        let simplified = simplify_for_js_backend(&lambda);
        let Lambda::Llet(_, id, value, body) = simplified else {
            panic!("expected exported binding after alias cleanup");
        };
        assert_eq!(id, exported);
        assert!(matches!(
            *value,
            Lambda::Lconst(Constant::String { ref s, .. }) if s == "hello world"
        ));
        assert!(matches!(*body, Lambda::Lprim(_)));
    }

    #[test]
    fn rewrites_null_to_opt_alias_checks_to_raw_null_predicates() {
        let source = Ident::create_local("source");
        let optional = Ident::create_local("optional");
        let lambda = Lambda::let_(
            LetKind::Strict,
            source.clone(),
            Lambda::prim(
                Primitive::PjsCall {
                    prim_name: "getElementById".to_string(),
                    arg_types: vec![],
                    ffi: crate::lambda::primitive::ExternalFfiSpec {
                        kind: crate::lambda::primitive::ExternalFfiKind::Default,
                        spec: None,
                        obj_params: None,
                        return_wrapper: crate::lambda::primitive::ExternalReturnWrapper::Identity,
                        inline_constant: None,
                    },
                    dynamic_import: false,
                    transformed_jsx: false,
                },
                vec![],
                Location::none(),
            ),
            Lambda::let_(
                LetKind::Strict,
                optional.clone(),
                Lambda::prim(
                    Primitive::PnullToOpt,
                    vec![Lambda::var(source.clone())],
                    Location::none(),
                ),
                Lambda::if_(
                    Lambda::prim(
                        Primitive::PisNotNone,
                        vec![Lambda::var(optional.clone())],
                        Location::none(),
                    ),
                    Lambda::prim(
                        Primitive::PvalFromOptionNotNest,
                        vec![Lambda::var(optional)],
                        Location::none(),
                    ),
                    Lambda::const_(Constant::int(1)),
                ),
            ),
        );

        let simplified = simplify_for_js_backend(&lambda);
        let Lambda::Llet(_, kept_id, _, body) = simplified else {
            panic!("expected the source binding to remain");
        };
        assert_eq!(kept_id, source);
        let Lambda::LifThenElse(cond, then_, else_) = *body else {
            panic!("expected the optional alias binding to fold into an if");
        };
        assert!(matches!(
            cond.as_ref(),
            Lambda::Lprim(crate::lambda::PrimInfo {
                primitive: Primitive::Pnot,
                args,
                ..
            }) if matches!(
                args.as_slice(),
                [Lambda::Lprim(crate::lambda::PrimInfo {
                    primitive: Primitive::PisNull,
                    args,
                    ..
                })] if matches!(args.as_slice(), [Lambda::Lvar(id)] if *id == kept_id)
            )
        ));
        assert!(matches!(then_.as_ref(), Lambda::Lvar(id) if *id == kept_id));
        assert!(matches!(
            else_.as_ref(),
            Lambda::Lconst(Constant::Int { i: 1, .. })
        ));
    }

    #[test]
    fn rewrites_nullable_alias_checks_to_raw_nullable_predicates() {
        let source = Ident::create_local("source");
        let optional = Ident::create_local("optional");
        let lambda = Lambda::let_(
            LetKind::Strict,
            source.clone(),
            Lambda::prim(
                Primitive::PjsCall {
                    prim_name: "getNullable".to_string(),
                    arg_types: vec![],
                    ffi: crate::lambda::primitive::ExternalFfiSpec {
                        kind: crate::lambda::primitive::ExternalFfiKind::Default,
                        spec: None,
                        obj_params: None,
                        return_wrapper: crate::lambda::primitive::ExternalReturnWrapper::Identity,
                        inline_constant: None,
                    },
                    dynamic_import: false,
                    transformed_jsx: false,
                },
                vec![],
                Location::none(),
            ),
            Lambda::let_(
                LetKind::Strict,
                optional.clone(),
                Lambda::prim(
                    Primitive::PnullUndefinedToOpt,
                    vec![Lambda::var(source.clone())],
                    Location::none(),
                ),
                Lambda::if_(
                    Lambda::prim(
                        Primitive::PisNotNone,
                        vec![Lambda::var(optional.clone())],
                        Location::none(),
                    ),
                    Lambda::prim(
                        Primitive::PvalFromOption,
                        vec![Lambda::var(optional)],
                        Location::none(),
                    ),
                    Lambda::const_(Constant::int(0)),
                ),
            ),
        );

        let simplified = simplify_for_js_backend(&lambda);
        let Lambda::Llet(_, kept_id, _, body) = simplified else {
            panic!("expected the source binding to remain");
        };
        assert_eq!(kept_id, source);
        let Lambda::LifThenElse(cond, then_, else_) = *body else {
            panic!("expected the nullable alias binding to fold into an if");
        };
        assert!(matches!(
            cond.as_ref(),
            Lambda::Lprim(crate::lambda::PrimInfo {
                primitive: Primitive::Pnot,
                args,
                ..
            }) if matches!(
                args.as_slice(),
                [Lambda::Lprim(crate::lambda::PrimInfo {
                    primitive: Primitive::PisNullUndefined,
                    args,
                    ..
                })] if matches!(args.as_slice(), [Lambda::Lvar(id)] if *id == kept_id)
            )
        ));
        assert!(matches!(then_.as_ref(), Lambda::Lvar(id) if *id == kept_id));
        assert!(matches!(
            else_.as_ref(),
            Lambda::Lconst(Constant::Int { i: 0, .. })
        ));
    }

    #[test]
    fn keeps_allocating_constant_bindings_shared() {
        let shared = Ident::create_local("shared");
        let projected = Ident::create_local("projected");
        let exported = Ident::create_local("exported");
        let export_block = Lambda::prim(
            Primitive::Pmakeblock(
                0,
                TagInfo::ModuleExport(vec![exported.clone()]),
                Mutable::Immutable,
            ),
            vec![Lambda::var(exported.clone())],
            Location::none(),
        );
        let lambda = Lambda::let_(
            LetKind::Strict,
            exported.clone(),
            Lambda::let_(
                LetKind::Strict,
                shared.clone(),
                Lambda::const_(Constant::Block {
                    tag: 0,
                    tag_info: TagInfo::record(
                        vec![("number".to_string(), false), ("name".to_string(), false)],
                        crate::parser::ast::MutableFlag::Immutable,
                    ),
                    elements: vec![
                        Constant::int(42),
                        Constant::string_with_delim(
                            "a",
                            crate::lambda::constant::StringDelim::StarJ,
                        ),
                    ],
                }),
                Lambda::let_(
                    LetKind::Strict,
                    projected.clone(),
                    Lambda::prim(
                        Primitive::Pfield(
                            0,
                            crate::lambda::compat::FieldDbgInfo::Record {
                                name: "name".to_string(),
                                mutable_flag: crate::parser::ast::MutableFlag::Immutable,
                            },
                        ),
                        vec![Lambda::var(shared.clone())],
                        Location::none(),
                    ),
                    Lambda::prim(
                        Primitive::Pmakeblock(
                            0,
                            TagInfo::module(vec!["a".to_string(), "name".to_string()]),
                            Mutable::Immutable,
                        ),
                        vec![Lambda::var(shared.clone()), Lambda::var(projected.clone())],
                        Location::none(),
                    ),
                ),
            ),
            export_block,
        );

        let simplified = simplify_for_js_backend(&lambda);
        let Lambda::Llet(_, id, value, _) = simplified else {
            panic!("expected exported binding to remain");
        };
        assert_eq!(id, exported);
        let Lambda::Llet(_, shared_id, shared_value, body) = *value else {
            panic!("expected shared allocating constant binding to remain");
        };
        assert_eq!(shared_id, shared);
        assert!(matches!(
            *shared_value,
            Lambda::Lconst(Constant::Block { .. })
        ));
        let Lambda::Llet(_, projected_id, _, body) = *body else {
            panic!("expected projected field binding");
        };
        assert_eq!(projected_id, projected);
        let Lambda::Lprim(crate::lambda::PrimInfo {
            primitive: Primitive::Pmakeblock(_, TagInfo::Module(fields), _),
            args,
            ..
        }) = *body
        else {
            panic!("expected module block");
        };
        assert_eq!(fields, vec!["a".to_string(), "name".to_string()]);
        assert!(matches!(&args[0], Lambda::Lvar(id) if *id == shared));
        assert!(matches!(&args[1], Lambda::Lvar(id) if *id == projected));
    }

    #[test]
    fn unwraps_pjs_fn_make_bindings_before_beta_reducing_local_calls() {
        let add = Ident::create_local("add");
        let add5 = Ident::create_local("add5");
        let left = Ident::create_local("left");
        let right = Ident::create_local("right");
        let extra = Ident::create_local("extra");

        let lambda = Lambda::let_(
            LetKind::Strict,
            add.clone(),
            Lambda::prim(
                Primitive::PjsFnMake(2),
                vec![Lambda::function_(
                    2,
                    vec![left.clone(), right.clone()],
                    Lambda::prim(
                        Primitive::Paddint,
                        vec![Lambda::var(left), Lambda::var(right)],
                        Location::none(),
                    ),
                    FunctionAttribute::default(),
                )],
                Location::none(),
            ),
            Lambda::let_(
                LetKind::Strict,
                add5.clone(),
                Lambda::function_(
                    1,
                    vec![extra.clone()],
                    Lambda::Lapply(Apply {
                        ap_func: Box::new(Lambda::var(add)),
                        ap_args: vec![Lambda::const_(Constant::int(5)), Lambda::var(extra.clone())],
                        ap_info: ApInfo {
                            loc: Location::none(),
                            inlined: InlineAttribute::Default,
                            status: crate::lambda::ApplyStatus::Uncurry,
                        },
                        ap_transformed_jsx: false,
                    }),
                    FunctionAttribute::default(),
                ),
                Lambda::var(add5.clone()),
            ),
        );

        let simplified = simplify_for_js_backend(&lambda);
        let func = match simplified {
            Lambda::Llet(_, id, value, body)
                if id == add5 && matches!(*body, Lambda::Lvar(ref body_id) if body_id == &add5) =>
            {
                let Lambda::Lfunction(func) = *value else {
                    panic!("expected add5 to stay a function");
                };
                func
            }
            Lambda::Lfunction(func) => func,
            other => panic!("expected simplification to leave a direct function, got {other:?}"),
        };
        assert_eq!(func.params, vec![extra.clone()]);
        assert!(matches!(
            *func.body,
            Lambda::Lprim(crate::lambda::PrimInfo {
                primitive: Primitive::Paddint,
                args,
                ..
            }) if matches!(args.as_slice(), [
                Lambda::Lconst(Constant::Int { i: 5, .. }),
                Lambda::Lvar(id)
            ] if *id == extra)
        ));
    }

    #[test]
    fn adjusts_direct_pjs_fn_make_callbacks_to_requested_arity_during_simplify() {
        let this_param = Ident::create_local("this");
        let async_arg = Ident::create_local("arg");

        let simplified = simplify_for_js_backend(&Lambda::prim(
            Primitive::PjsFnMake(2),
            vec![Lambda::function_(
                1,
                vec![this_param.clone()],
                Lambda::function_(
                    1,
                    vec![async_arg.clone()],
                    Lambda::prim(
                        Primitive::Paddint,
                        vec![Lambda::var(this_param.clone()), Lambda::var(async_arg.clone())],
                        Location::none(),
                    ),
                    FunctionAttribute {
                        async_: true,
                        ..FunctionAttribute::default()
                    },
                ),
                FunctionAttribute::default(),
            )],
            Location::none(),
        ));

        let Lambda::Lfunction(func) = simplified else {
            panic!("expected eta-adjusted callback to stay a function");
        };
        assert_eq!(func.arity, 2);
        assert_eq!(func.params.len(), 2);
        assert!(func.params[0].same(&this_param));

        let Lambda::Lapply(apply) = *func.body else {
            panic!("expected the expanded callback body to apply the async inner function");
        };
        assert_eq!(apply.ap_args.len(), 1);
        assert!(matches!(
            apply.ap_args.as_slice(),
            [Lambda::Lvar(id)] if id.same(&func.params[1])
        ));
        assert!(matches!(
            apply.ap_func.as_ref(),
            Lambda::Lfunction(inner)
                if inner.attr.async_
                    && matches!(inner.params.as_slice(), [param] if param.same(&async_arg))
        ));
    }

    #[test]
    fn beta_reduces_downarity_pjs_fn_make_calls_before_js_lowering() {
        let x = Ident::create_local("x");
        let y = Ident::create_local("y");
        let z = Ident::create_local("z");

        let simplified = simplify_for_js_backend(&Lambda::Lapply(Apply {
            ap_func: Box::new(Lambda::Lapply(Apply {
                ap_func: Box::new(Lambda::prim(
                    Primitive::PjsFnMake(1),
                    vec![Lambda::function_(
                        3,
                        vec![x.clone(), y.clone(), z.clone()],
                        Lambda::prim(
                            Primitive::Paddint,
                            vec![
                                Lambda::prim(
                                    Primitive::Paddint,
                                    vec![Lambda::var(x), Lambda::var(y)],
                                    Location::none(),
                                ),
                                Lambda::var(z),
                            ],
                            Location::none(),
                        ),
                        FunctionAttribute::default(),
                    )],
                    Location::none(),
                )),
                ap_args: vec![Lambda::const_(Constant::int(1))],
                ap_info: crate::lambda::ApInfo {
                    loc: Location::none(),
                    inlined: InlineAttribute::Default,
                    status: ApplyStatus::Uncurry,
                },
                ap_transformed_jsx: false,
            })),
            ap_args: vec![
                Lambda::const_(Constant::int(2)),
                Lambda::const_(Constant::int(3)),
            ],
            ap_info: crate::lambda::ApInfo {
                loc: Location::none(),
                inlined: InlineAttribute::Default,
                status: ApplyStatus::Uncurry,
            },
            ap_transformed_jsx: false,
        }));

        let Lambda::Lprim(crate::lambda::PrimInfo {
            primitive: Primitive::Paddint,
            args,
            ..
        }) = simplified
        else {
            panic!("expected the fully-applied wrapper call to simplify to an integer addition");
        };
        let [left, Lambda::Lconst(Constant::Int { i: 3, .. })] = args.as_slice() else {
            panic!("expected the final argument to remain the trailing constant");
        };
        let Lambda::Lprim(crate::lambda::PrimInfo {
            primitive: Primitive::Paddint,
            args,
            ..
        }) = left
        else {
            panic!("expected the remaining wrapper to disappear into the left-hand addition");
        };
        assert!(matches!(
            args.as_slice(),
            [
                Lambda::Lconst(Constant::Int { i: 1, .. }),
                Lambda::Lconst(Constant::Int { i: 2, .. })
            ]
        ));
    }

    #[test]
    fn beta_reduces_fully_applied_returned_pjs_fn_make_wrappers() {
        let h = Ident::create_local("h");
        let x = Ident::create_local("x");
        let j = Ident::create_local("j");
        let f = Ident::create_local("f");
        let arg = Lambda::const_(Constant::string_with_delim(
            "",
            crate::lambda::constant::StringDelim::StarJ,
        ));

        let wrapped = Lambda::let_(
            LetKind::Strict,
            h,
            Lambda::const_(Constant::JsTrue),
            Lambda::prim(
                Primitive::PjsFnMake(1),
                vec![Lambda::function_(
                    1,
                    vec![x],
                    Lambda::let_(
                        LetKind::Strict,
                        j,
                        Lambda::prim(
                            Primitive::PjsFnMake(1),
                            vec![Lambda::function_(
                                1,
                                vec![f.clone()],
                                Lambda::const_(Constant::JsTrue),
                                FunctionAttribute::default(),
                            )],
                            Location::none(),
                        ),
                        Lambda::prim(
                            Primitive::PjsFnMake(1),
                            vec![Lambda::function_(
                                1,
                                vec![f],
                                Lambda::const_(Constant::int(0)),
                                FunctionAttribute::default(),
                            )],
                            Location::none(),
                        ),
                    ),
                    FunctionAttribute::default(),
                )],
                Location::none(),
            ),
        );

        let lambda = Lambda::Lapply(Apply {
            ap_func: Box::new(Lambda::Lapply(Apply {
                ap_func: Box::new(wrapped),
                ap_args: vec![arg.clone()],
                ap_info: ApInfo {
                    loc: Location::none(),
                    inlined: InlineAttribute::Default,
                    status: crate::lambda::ApplyStatus::Uncurry,
                },
                ap_transformed_jsx: false,
            })),
            ap_args: vec![arg],
            ap_info: ApInfo {
                loc: Location::none(),
                inlined: InlineAttribute::Default,
                status: crate::lambda::ApplyStatus::Uncurry,
            },
            ap_transformed_jsx: false,
        });

        let simplified = simplify_for_js_backend(&lambda);
        assert!(matches!(simplified, Lambda::Lconst(Constant::Int { i: 0, .. })));
    }

    #[test]
    fn unwraps_pjs_fn_make_unit_into_one_unit_arg_functions() {
        let param = Ident::create_local("param");

        let simplified = simplify_for_js_backend(&Lambda::prim(
            Primitive::PjsFnMakeUnit,
            vec![Lambda::function_(
                1,
                vec![param.clone()],
                Lambda::unit(),
                FunctionAttribute::default(),
            )],
            Location::none(),
        ));

        let Lambda::Lfunction(func) = simplified else {
            panic!("expected the unit wrapper to unwrap to a function");
        };
        assert_eq!(func.params, vec![param]);
        assert!(func.attr.one_unit_arg);
    }
}
