//! Small post-lowering lambda simplifications used on the JS backend path.

use std::collections::{HashMap, HashSet};

use crate::ident::Ident;
use crate::lambda::analysis;
use crate::lambda::beta_reduce;
use crate::lambda::closure;
use crate::lambda::compat::{FieldDbgInfo, LetKind};
use crate::lambda::compile_context::BoxedNullable;
use crate::lambda::constant::Constant;
use crate::lambda::free_variables::free_variables;
use crate::lambda::primitive::{Mutable, Primitive};
use crate::lambda::{
    Apply, ApplyStatus, FunctionAttribute, InlineAttribute, LFunction, Lambda, LambdaSwitch,
    TagInfo,
};
use crate::location::Location;

#[derive(Clone, Default)]
struct SimplifyEnv {
    blocks: HashMap<Ident, ImmutableBlockInfo>,
    call_substitutions: HashMap<Ident, Lambda>,
    functions: HashMap<Ident, LFunction>,
    known_functions: HashMap<Ident, LFunction>,
    optional_blocks: HashMap<Ident, OptionalBlockInfo>,
    plain_strings: HashMap<Ident, String>,
    preserved_export_bindings: HashSet<Ident>,
    allow_direct_function_beta_reduce: bool,
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
        next.call_substitutions.remove(id);
        next.functions.remove(id);
        next.known_functions.remove(id);
        next.optional_blocks.remove(id);
        next.plain_strings.remove(id);
        next.substitutions.remove(id);
        next
    }

    fn without_idents<'a>(&self, ids: impl IntoIterator<Item = &'a Ident>) -> Self {
        let mut next = self.clone();
        for id in ids {
            next.blocks.remove(id);
            next.call_substitutions.remove(id);
            next.functions.remove(id);
            next.known_functions.remove(id);
            next.optional_blocks.remove(id);
            next.plain_strings.remove(id);
            next.substitutions.remove(id);
        }
        next
    }
}

/// Simplify lowered lambda before JS IR lowering.
pub fn simplify_for_js_backend(lam: &Lambda) -> Lambda {
    let flattened = deep_flatten_for_js_backend(lam);
    let exports = collect_exported_idents(&flattened);
    let preserved_export_bindings = collect_exported_apply_bindings(&flattened, &exports);
    let first = simplify_for_js_backend_once(&flattened, &preserved_export_bindings, true);
    let second = simplify_for_js_backend_once(&first, &preserved_export_bindings, false);
    let lets_dce_style = simplify_direct_function_applications_like_lets_dce(&second);
    simplify_for_js_backend_once(&lets_dce_style, &preserved_export_bindings, false)
}

fn simplify_for_js_backend_once(
    lam: &Lambda,
    preserved_export_bindings: &HashSet<Ident>,
    allow_direct_function_beta_reduce: bool,
) -> Lambda {
    let flattened = deep_flatten_for_js_backend(lam);
    let exports = collect_exported_idents(&flattened);
    let env = SimplifyEnv {
        functions: collect_inlineable_functions(&flattened),
        known_functions: collect_known_functions(&flattened),
        preserved_export_bindings: preserved_export_bindings.clone(),
        allow_direct_function_beta_reduce,
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

fn simplify_direct_function_applications_like_lets_dce(lam: &Lambda) -> Lambda {
    match lam {
        Lambda::Lvar(_) | Lambda::LglobalModule(_, _) | Lambda::Lconst(_) => lam.clone(),
        Lambda::Lapply(apply)
            if matches!(
                apply.ap_func.as_ref(),
                Lambda::Lfunction(func)
                    if func.params.len() == apply.ap_args.len()
                        && analysis::lfunction_can_be_inlined(func)
            ) =>
        {
            let Lambda::Lfunction(func) = apply.ap_func.as_ref() else {
                unreachable!("guard above ensures a direct function callee");
            };
            let reduced =
                beta_reduce::no_names_beta_reduce(&func.params, &func.body, &apply.ap_args);
            simplify_direct_function_applications_like_lets_dce(&reduced)
        }
        Lambda::Lapply(apply) => Lambda::Lapply(Apply {
            ap_func: Box::new(simplify_direct_function_applications_like_lets_dce(
                &apply.ap_func,
            )),
            ap_args: apply
                .ap_args
                .iter()
                .map(simplify_direct_function_applications_like_lets_dce)
                .collect(),
            ap_info: apply.ap_info.clone(),
            ap_transformed_jsx: apply.ap_transformed_jsx,
        }),
        Lambda::Lfunction(func) => Lambda::function_(
            func.arity,
            func.params.clone(),
            simplify_direct_function_applications_like_lets_dce(&func.body),
            func.attr.clone(),
        ),
        Lambda::Llet(kind, id, value, body) => Lambda::let_(
            *kind,
            id.clone(),
            simplify_direct_function_applications_like_lets_dce(value),
            simplify_direct_function_applications_like_lets_dce(body),
        ),
        Lambda::Lletrec(bindings, body) => Lambda::letrec(
            bindings
                .iter()
                .map(|(id, binding)| {
                    (
                        id.clone(),
                        simplify_direct_function_applications_like_lets_dce(binding),
                    )
                })
                .collect(),
            simplify_direct_function_applications_like_lets_dce(body),
        ),
        Lambda::Lprim(info) => Lambda::prim(
            info.primitive.clone(),
            info.args
                .iter()
                .map(simplify_direct_function_applications_like_lets_dce)
                .collect(),
            info.loc.clone(),
        ),
        Lambda::Lswitch(scrutinee, switch) => Lambda::Lswitch(
            Box::new(simplify_direct_function_applications_like_lets_dce(
                scrutinee,
            )),
            LambdaSwitch {
                sw_consts_full: switch.sw_consts_full,
                sw_consts: switch
                    .sw_consts
                    .iter()
                    .map(|(tag, lam)| {
                        (
                            *tag,
                            simplify_direct_function_applications_like_lets_dce(lam),
                        )
                    })
                    .collect(),
                sw_blocks_full: switch.sw_blocks_full,
                sw_blocks: switch
                    .sw_blocks
                    .iter()
                    .map(|(tag, lam)| {
                        (
                            *tag,
                            simplify_direct_function_applications_like_lets_dce(lam),
                        )
                    })
                    .collect(),
                sw_failaction: switch.sw_failaction.as_ref().map(|lam| {
                    Box::new(simplify_direct_function_applications_like_lets_dce(lam))
                }),
                sw_names: switch.sw_names.clone(),
            },
        ),
        Lambda::LstringSwitch(scrutinee, cases, default) => Lambda::LstringSwitch(
            Box::new(simplify_direct_function_applications_like_lets_dce(
                scrutinee,
            )),
            cases
                .iter()
                .map(|(tag, lam)| {
                    (
                        tag.clone(),
                        simplify_direct_function_applications_like_lets_dce(lam),
                    )
                })
                .collect(),
            default.as_ref().map(|lam| {
                Box::new(simplify_direct_function_applications_like_lets_dce(lam))
            }),
        ),
        Lambda::LstaticRaise(id, args) => Lambda::LstaticRaise(
            *id,
            args.iter()
                .map(simplify_direct_function_applications_like_lets_dce)
                .collect(),
        ),
        Lambda::LstaticCatch(body, handler, recover) => Lambda::LstaticCatch(
            Box::new(simplify_direct_function_applications_like_lets_dce(body)),
            handler.clone(),
            Box::new(simplify_direct_function_applications_like_lets_dce(recover)),
        ),
        Lambda::LtryWith(body, exn, handler) => Lambda::LtryWith(
            Box::new(simplify_direct_function_applications_like_lets_dce(body)),
            exn.clone(),
            Box::new(simplify_direct_function_applications_like_lets_dce(handler)),
        ),
        Lambda::LifThenElse(cond, then_, else_) => Lambda::if_(
            simplify_direct_function_applications_like_lets_dce(cond),
            simplify_direct_function_applications_like_lets_dce(then_),
            simplify_direct_function_applications_like_lets_dce(else_),
        ),
        Lambda::Lsequence(first, second) => Lambda::seq(
            simplify_direct_function_applications_like_lets_dce(first),
            simplify_direct_function_applications_like_lets_dce(second),
        ),
        Lambda::Lwhile(cond, body) => Lambda::Lwhile(
            Box::new(simplify_direct_function_applications_like_lets_dce(cond)),
            Box::new(simplify_direct_function_applications_like_lets_dce(body)),
        ),
        Lambda::Lfor(id, from, to, direction, body) => Lambda::Lfor(
            id.clone(),
            Box::new(simplify_direct_function_applications_like_lets_dce(from)),
            Box::new(simplify_direct_function_applications_like_lets_dce(to)),
            *direction,
            Box::new(simplify_direct_function_applications_like_lets_dce(body)),
        ),
        Lambda::Lassign(id, value) => Lambda::Lassign(
            id.clone(),
            Box::new(simplify_direct_function_applications_like_lets_dce(value)),
        ),
    }
}

fn simplify_with_env(lam: &Lambda, env: &SimplifyEnv, exports: &HashSet<Ident>) -> Lambda {
    match lam {
        Lambda::Lvar(id) => resolve_transitive_substitution(id, env).unwrap_or_else(|| lam.clone()),
        Lambda::LglobalModule(_, _) | Lambda::Lconst(_) => lam.clone(),
        Lambda::Lapply(apply) => simplify_apply(apply, env, exports),
        Lambda::Lfunction(func) => {
            let body_env = env.without_idents(func.params.iter());
            let simplified = Lambda::function_(
                func.arity,
                func.params.clone(),
                simplify_with_env(&func.body, &body_env, exports),
                func.attr.clone(),
            );
            if let Lambda::Lfunction(func) = &simplified {
                eta_reduce_function_value(func, &body_env).unwrap_or(simplified)
            } else {
                simplified
            }
        }
        Lambda::Llet(kind, id, value, body) => {
            let original_value = value.as_ref();
            let mut kind = *kind;
            let mut value = simplify_with_env(value, env, exports);
            let mut body_env = env.without_ident(id);
            let binding_is_exported = lambda_exports_ident(body, id);
            let mut body_exports = None;
            let preserve_exported_eta_alias =
                binding_is_exported && preserve_exported_eta_alias_binding(original_value, &value);
            if let Some(block_info) = immutable_block_elements(&value) {
                body_env.blocks.insert(id.clone(), block_info);
            }
            if let Some(optional_info) = optional_block_info(&value) {
                body_env.optional_blocks.insert(id.clone(), optional_info);
            }
            if matches!(kind, LetKind::Strict | LetKind::StrictOpt) && is_safe_to_alias(&value) {
                kind = LetKind::Alias;
            } else if kind == LetKind::Strict {
                if matches!(value, Lambda::Lfunction(_)) {
                    kind = LetKind::StrictOpt;
                } else if analysis::no_side_effects(&value) {
                    kind = LetKind::StrictOpt;
                }
            }
            if let Some(string_value) = plain_string_constant(&value) {
                body_env.plain_strings.insert(id.clone(), string_value);
            }
            if let Some(substitution) = substitution_candidate(kind, original_value, &value) {
                if binding_is_exported {
                    if let Some(export_target) = exported_alias_target(&substitution) {
                        let propagated = body_exports.get_or_insert_with(|| exports.clone());
                        propagated.insert(export_target);
                    }
                }
                if preserve_exported_eta_alias {
                    if module_field_call_substitution_candidate(&substitution) {
                        body_env
                            .call_substitutions
                            .insert(id.clone(), substitution.clone());
                    }
                } else if !env.preserved_export_bindings.contains(id) {
                    body_env.substitutions.insert(id.clone(), substitution);
                }
            }
            if kind != LetKind::Variable {
                if let Some(func) = inlineable_local_function(&value) {
                    body_env.known_functions.insert(id.clone(), func.clone());
                    if analysis::lfunction_can_be_inlined(&func) {
                        body_env.functions.insert(id.clone(), func);
                    }
                }
            }
            let mut body =
                simplify_with_env(body, &body_env, body_exports.as_ref().unwrap_or(exports));
            if matches!(kind, LetKind::Strict | LetKind::StrictOpt) {
                if let Some(init) = mutable_ref_init(&value) {
                    if let Ok(eliminated_body) = eliminate_non_escaping_ref_binding(id, &body) {
                        kind = LetKind::Variable;
                        value = init;
                        body = eliminated_body;
                    }
                }
            }
            if binding_is_exported
                && export_only_single_use_allocating_constant_candidate(id, &value, &body)
            {
                body = substitute_alias_use(&body, id, &value);
            }
            if kind == LetKind::Alias
                && !preserve_exported_eta_alias
                && !env.preserved_export_bindings.contains(id)
            {
                let use_info = alias_use_info(id, &body);
                if use_info.times == 1
                    && (!use_info.captured || matches!(value, Lambda::Lconst(_) | Lambda::Lvar(_)))
                {
                    return substitute_alias_use(&body, id, &value);
                }
            }
            if !preserve_exported_eta_alias && !free_variables(&body).contains(id) {
                if analysis::no_side_effects(&value) {
                    body
                } else {
                    Lambda::seq(value, body)
                }
            } else {
                refine_let_binding(kind, id, value, body)
            }
        }
        Lambda::Lletrec(bindings, body) => {
            let bound_ids = bindings.iter().map(|(id, _)| id);
            let scoped_env = env.without_idents(bound_ids);
            let mut recursive_env = scoped_env.clone();
            for (id, expr) in bindings {
                if let Some(func) = inlineable_local_function(expr) {
                    recursive_env.known_functions.insert(id.clone(), func);
                }
            }
            let bindings = bindings
                .iter()
                .map(|(id, expr)| {
                    let expr_env = recursive_env.without_ident(id);
                    (id.clone(), simplify_with_env(expr, &expr_env, exports))
                })
                .collect();
            let body = simplify_with_env(body, &recursive_env, exports);
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

fn resolve_transitive_substitution(id: &Ident, env: &SimplifyEnv) -> Option<Lambda> {
    fn resolve(id: &Ident, env: &SimplifyEnv, visiting: &mut HashSet<Ident>) -> Option<Lambda> {
        if !visiting.insert(id.clone()) {
            return Some(Lambda::var(id.clone()));
        }

        let resolved = match env.substitutions.get(id) {
            Some(Lambda::Lvar(next)) => {
                resolve(next, env, visiting).or_else(|| Some(Lambda::var(next.clone())))
            }
            Some(value) => Some(value.clone()),
            None => None,
        };

        visiting.remove(id);
        resolved
    }

    resolve(id, env, &mut HashSet::new())
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

fn export_only_single_use_allocating_constant_candidate(
    id: &Ident,
    value: &Lambda,
    body: &Lambda,
) -> bool {
    if !matches!(value, Lambda::Lconst(Constant::Block { .. })) {
        return false;
    }

    let use_info = alias_use_info(id, body);
    use_info.times == 1 && !use_info.captured && used_only_in_module_export_payload(id, body)
}

fn used_only_in_module_export_payload(target: &Ident, lam: &Lambda) -> bool {
    fn collect(
        target: &Ident,
        lam: &Lambda,
        inside_export_payload: bool,
        saw_use: &mut bool,
        saw_non_export_use: &mut bool,
    ) {
        if *saw_non_export_use {
            return;
        }

        match lam {
            Lambda::Lvar(id) => {
                if id.same(target) {
                    *saw_use = true;
                    if !inside_export_payload {
                        *saw_non_export_use = true;
                    }
                }
            }
            Lambda::LglobalModule(_, _) | Lambda::Lconst(_) => {}
            Lambda::Lapply(apply) => {
                collect(
                    target,
                    &apply.ap_func,
                    inside_export_payload,
                    saw_use,
                    saw_non_export_use,
                );
                for arg in &apply.ap_args {
                    collect(
                        target,
                        arg,
                        inside_export_payload,
                        saw_use,
                        saw_non_export_use,
                    );
                }
            }
            Lambda::Lfunction(func) => collect(
                target,
                &func.body,
                inside_export_payload,
                saw_use,
                saw_non_export_use,
            ),
            Lambda::Llet(_, _, value, body) => {
                collect(
                    target,
                    value,
                    inside_export_payload,
                    saw_use,
                    saw_non_export_use,
                );
                collect(
                    target,
                    body,
                    inside_export_payload,
                    saw_use,
                    saw_non_export_use,
                );
            }
            Lambda::Lletrec(bindings, body) => {
                for (_, binding) in bindings {
                    collect(
                        target,
                        binding,
                        inside_export_payload,
                        saw_use,
                        saw_non_export_use,
                    );
                }
                collect(
                    target,
                    body,
                    inside_export_payload,
                    saw_use,
                    saw_non_export_use,
                );
            }
            Lambda::Lprim(info) => {
                let payload_flag = matches!(
                    info.primitive,
                    Primitive::Pmakeblock(_, TagInfo::ModuleExport(_), Mutable::Immutable)
                );
                for arg in &info.args {
                    collect(
                        target,
                        arg,
                        inside_export_payload || payload_flag,
                        saw_use,
                        saw_non_export_use,
                    );
                }
            }
            Lambda::Lswitch(scrutinee, switch) => {
                collect(
                    target,
                    scrutinee,
                    inside_export_payload,
                    saw_use,
                    saw_non_export_use,
                );
                for (_, lam) in &switch.sw_consts {
                    collect(
                        target,
                        lam,
                        inside_export_payload,
                        saw_use,
                        saw_non_export_use,
                    );
                }
                for (_, lam) in &switch.sw_blocks {
                    collect(
                        target,
                        lam,
                        inside_export_payload,
                        saw_use,
                        saw_non_export_use,
                    );
                }
                if let Some(fallback) = &switch.sw_failaction {
                    collect(
                        target,
                        fallback,
                        inside_export_payload,
                        saw_use,
                        saw_non_export_use,
                    );
                }
            }
            Lambda::LstringSwitch(scrutinee, cases, default) => {
                collect(
                    target,
                    scrutinee,
                    inside_export_payload,
                    saw_use,
                    saw_non_export_use,
                );
                for (_, lam) in cases {
                    collect(
                        target,
                        lam,
                        inside_export_payload,
                        saw_use,
                        saw_non_export_use,
                    );
                }
                if let Some(fallback) = default {
                    collect(
                        target,
                        fallback,
                        inside_export_payload,
                        saw_use,
                        saw_non_export_use,
                    );
                }
            }
            Lambda::LstaticRaise(_, args) => {
                for arg in args {
                    collect(
                        target,
                        arg,
                        inside_export_payload,
                        saw_use,
                        saw_non_export_use,
                    );
                }
            }
            Lambda::LstaticCatch(body, _, handler) | Lambda::LtryWith(body, _, handler) => {
                collect(
                    target,
                    body,
                    inside_export_payload,
                    saw_use,
                    saw_non_export_use,
                );
                collect(
                    target,
                    handler,
                    inside_export_payload,
                    saw_use,
                    saw_non_export_use,
                );
            }
            Lambda::LifThenElse(cond, then_, else_) => {
                collect(
                    target,
                    cond,
                    inside_export_payload,
                    saw_use,
                    saw_non_export_use,
                );
                collect(
                    target,
                    then_,
                    inside_export_payload,
                    saw_use,
                    saw_non_export_use,
                );
                collect(
                    target,
                    else_,
                    inside_export_payload,
                    saw_use,
                    saw_non_export_use,
                );
            }
            Lambda::Lsequence(first, second) | Lambda::Lwhile(first, second) => {
                collect(
                    target,
                    first,
                    inside_export_payload,
                    saw_use,
                    saw_non_export_use,
                );
                collect(
                    target,
                    second,
                    inside_export_payload,
                    saw_use,
                    saw_non_export_use,
                );
            }
            Lambda::Lfor(_, start, end, _, body) => {
                collect(
                    target,
                    start,
                    inside_export_payload,
                    saw_use,
                    saw_non_export_use,
                );
                collect(
                    target,
                    end,
                    inside_export_payload,
                    saw_use,
                    saw_non_export_use,
                );
                collect(
                    target,
                    body,
                    inside_export_payload,
                    saw_use,
                    saw_non_export_use,
                );
            }
            Lambda::Lassign(id, value) => {
                if id.same(target) {
                    *saw_use = true;
                    if !inside_export_payload {
                        *saw_non_export_use = true;
                    }
                }
                collect(
                    target,
                    value,
                    inside_export_payload,
                    saw_use,
                    saw_non_export_use,
                );
            }
        }
    }

    let mut saw_use = false;
    let mut saw_non_export_use = false;
    collect(target, lam, false, &mut saw_use, &mut saw_non_export_use);
    saw_use && !saw_non_export_use
}

fn mutable_ref_init(lam: &Lambda) -> Option<Lambda> {
    match lam {
        Lambda::Lprim(crate::lambda::PrimInfo {
            primitive: Primitive::Pmakeblock(0, _, crate::lambda::primitive::Mutable::Mutable),
            args,
            ..
        }) => match args.as_slice() {
            [init] => Some(init.clone()),
            _ => None,
        },
        _ => None,
    }
}

fn eliminate_non_escaping_ref_binding(id: &Ident, lam: &Lambda) -> Result<Lambda, ()> {
    match lam {
        Lambda::Lvar(v) => {
            if v.same(id) {
                Err(())
            } else {
                Ok(lam.clone())
            }
        }
        Lambda::Lprim(crate::lambda::PrimInfo {
            primitive: Primitive::Pfield(0, _),
            args,
            ..
        }) if matches!(args.as_slice(), [Lambda::Lvar(v)] if v.same(id)) => {
            Ok(Lambda::var(id.clone()))
        }
        Lambda::Lfunction(func) => {
            if lambda_hits_variable(id, &func.body) {
                Err(())
            } else {
                Ok(lam.clone())
            }
        }
        Lambda::Lprim(crate::lambda::PrimInfo {
            primitive: Primitive::Psetfield(0, _),
            args,
            ..
        }) if matches!(args.as_slice(), [Lambda::Lvar(v), _] if v.same(id)) => {
            let [_, value] = args.as_slice() else {
                unreachable!();
            };
            Ok(Lambda::assign(
                id.clone(),
                eliminate_non_escaping_ref_binding(id, value)?,
            ))
        }
        Lambda::Lprim(crate::lambda::PrimInfo {
            primitive: Primitive::Poffsetref(delta),
            args,
            loc,
        }) if matches!(args.as_slice(), [Lambda::Lvar(v)] if v.same(id)) => Ok(Lambda::assign(
            id.clone(),
            Lambda::prim(
                Primitive::Poffsetint(*delta),
                vec![Lambda::var(id.clone())],
                loc.clone(),
            ),
        )),
        Lambda::LglobalModule(_, _) | Lambda::Lconst(_) => Ok(lam.clone()),
        Lambda::Lapply(apply) => Ok(Lambda::Lapply(Apply {
            ap_func: Box::new(eliminate_non_escaping_ref_binding(id, &apply.ap_func)?),
            ap_args: apply
                .ap_args
                .iter()
                .map(|arg| eliminate_non_escaping_ref_binding(id, arg))
                .collect::<Result<Vec<_>, _>>()?,
            ap_info: apply.ap_info.clone(),
            ap_transformed_jsx: apply.ap_transformed_jsx,
        })),
        Lambda::Llet(kind, ident, value, body) => Ok(Lambda::let_(
            *kind,
            ident.clone(),
            eliminate_non_escaping_ref_binding(id, value)?,
            eliminate_non_escaping_ref_binding(id, body)?,
        )),
        Lambda::Lletrec(bindings, body) => Ok(Lambda::letrec(
            bindings
                .iter()
                .map(|(ident, lam)| {
                    Ok((ident.clone(), eliminate_non_escaping_ref_binding(id, lam)?))
                })
                .collect::<Result<Vec<_>, ()>>()?,
            eliminate_non_escaping_ref_binding(id, body)?,
        )),
        Lambda::Lprim(info) => Ok(Lambda::prim(
            info.primitive.clone(),
            info.args
                .iter()
                .map(|arg| eliminate_non_escaping_ref_binding(id, arg))
                .collect::<Result<Vec<_>, _>>()?,
            info.loc.clone(),
        )),
        Lambda::Lswitch(scrutinee, switch) => Ok(Lambda::Lswitch(
            Box::new(eliminate_non_escaping_ref_binding(id, scrutinee)?),
            LambdaSwitch {
                sw_consts_full: switch.sw_consts_full,
                sw_consts: switch
                    .sw_consts
                    .iter()
                    .map(|(tag, lam)| Ok((*tag, eliminate_non_escaping_ref_binding(id, lam)?)))
                    .collect::<Result<Vec<_>, ()>>()?,
                sw_blocks_full: switch.sw_blocks_full,
                sw_blocks: switch
                    .sw_blocks
                    .iter()
                    .map(|(tag, lam)| Ok((*tag, eliminate_non_escaping_ref_binding(id, lam)?)))
                    .collect::<Result<Vec<_>, ()>>()?,
                sw_failaction: switch
                    .sw_failaction
                    .as_ref()
                    .map(|lam| eliminate_non_escaping_ref_binding(id, lam).map(Box::new))
                    .transpose()?,
                sw_names: switch.sw_names.clone(),
            },
        )),
        Lambda::LstringSwitch(scrutinee, cases, default) => Ok(Lambda::LstringSwitch(
            Box::new(eliminate_non_escaping_ref_binding(id, scrutinee)?),
            cases
                .iter()
                .map(|(tag, lam)| Ok((tag.clone(), eliminate_non_escaping_ref_binding(id, lam)?)))
                .collect::<Result<Vec<_>, ()>>()?,
            default
                .as_ref()
                .map(|lam| eliminate_non_escaping_ref_binding(id, lam).map(Box::new))
                .transpose()?,
        )),
        Lambda::LstaticRaise(tag, args) => Ok(Lambda::LstaticRaise(
            *tag,
            args.iter()
                .map(|arg| eliminate_non_escaping_ref_binding(id, arg))
                .collect::<Result<Vec<_>, _>>()?,
        )),
        Lambda::LstaticCatch(body, handler, rescue) => Ok(Lambda::LstaticCatch(
            Box::new(eliminate_non_escaping_ref_binding(id, body)?),
            handler.clone(),
            Box::new(eliminate_non_escaping_ref_binding(id, rescue)?),
        )),
        Lambda::LtryWith(body, exn, handler) => Ok(Lambda::LtryWith(
            Box::new(eliminate_non_escaping_ref_binding(id, body)?),
            exn.clone(),
            Box::new(eliminate_non_escaping_ref_binding(id, handler)?),
        )),
        Lambda::LifThenElse(cond, then_, else_) => Ok(Lambda::if_(
            eliminate_non_escaping_ref_binding(id, cond)?,
            eliminate_non_escaping_ref_binding(id, then_)?,
            eliminate_non_escaping_ref_binding(id, else_)?,
        )),
        Lambda::Lsequence(first, second) => Ok(Lambda::seq(
            eliminate_non_escaping_ref_binding(id, first)?,
            eliminate_non_escaping_ref_binding(id, second)?,
        )),
        Lambda::Lwhile(cond, body) => Ok(Lambda::while_(
            eliminate_non_escaping_ref_binding(id, cond)?,
            eliminate_non_escaping_ref_binding(id, body)?,
        )),
        Lambda::Lfor(loop_var, from, to, direction, body) => Ok(Lambda::for_(
            loop_var.clone(),
            eliminate_non_escaping_ref_binding(id, from)?,
            eliminate_non_escaping_ref_binding(id, to)?,
            *direction,
            eliminate_non_escaping_ref_binding(id, body)?,
        )),
        Lambda::Lassign(ident, value) => Ok(Lambda::assign(
            ident.clone(),
            eliminate_non_escaping_ref_binding(id, value)?,
        )),
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

fn is_safe_to_alias(lam: &Lambda) -> bool {
    match lam {
        Lambda::Lvar(_) | Lambda::Lconst(_) => true,
        Lambda::Lprim(crate::lambda::PrimInfo {
            primitive: Primitive::Pfield(_, FieldDbgInfo::Module { .. }),
            args,
            ..
        }) => matches!(
            args.as_slice(),
            [Lambda::LglobalModule(_, _) | Lambda::Lvar(_)]
        ),
        Lambda::Lprim(crate::lambda::PrimInfo {
            primitive: Primitive::PsomeNotNest,
            args,
            ..
        }) => matches!(args.as_slice(), [inner] if is_safe_to_alias(inner)),
        _ => false,
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
            .map(|arg| simplify_with_env(arg, env, exports))
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
        (Primitive::PjsFnMake(_), [arg]) if module_field_call_substitution_candidate(arg) => {
            arg.clone()
        }
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
        (Primitive::PvalFromOption, [Lambda::Lvar(id)]) => env
            .optional_blocks
            .get(id)
            .map(|optional| optional.value.clone())
            .unwrap_or_else(|| Lambda::prim(info.primitive.clone(), args, info.loc.clone())),
        (Primitive::PvalFromOptionNotNest, [Lambda::Lvar(id)]) => env
            .optional_blocks
            .get(id)
            .map(|optional| optional.value.clone())
            .unwrap_or_else(|| Lambda::var(id.clone())),
        (
            Primitive::Pmakeblock(
                _,
                TagInfo::Module(fields),
                crate::lambda::primitive::Mutable::Immutable,
            ),
            _,
        ) => collapse_identity_module_block(fields, &args)
            .unwrap_or_else(|| Lambda::prim(info.primitive.clone(), args, info.loc.clone())),
        (Primitive::Pstringadd, [left, right]) => match (
            plain_string_value(left, env),
            plain_string_value(right, env),
        ) {
            (Some(left), Some(right)) => Lambda::const_(Constant::String {
                s: format!("{left}{right}"),
                delim: None,
            }),
            _ => Lambda::prim(info.primitive.clone(), args, info.loc.clone()),
        },
        _ => fold_ocaml_backend_int_primitive(&info.primitive, &args)
            .unwrap_or_else(|| Lambda::prim(info.primitive.clone(), args, info.loc.clone())),
    }
}

fn fold_ocaml_backend_int_primitive(primitive: &Primitive, args: &[Lambda]) -> Option<Lambda> {
    match (primitive, args) {
        (
            Primitive::Psubint,
            [
                Lambda::Lconst(Constant::Int { i: left, .. }),
                Lambda::Lconst(Constant::Int { i: right, .. }),
            ],
        ) => Some(Lambda::const_(Constant::int(left.wrapping_sub(*right)))),
        _ => None,
    }
}

fn collapse_identity_module_block(fields: &[String], args: &[Lambda]) -> Option<Lambda> {
    if fields.len() != args.len() || fields.is_empty() {
        return None;
    }

    let target = projected_identity_module_target(&fields[0], 0, &args[0])?;
    for (index, (field_name, arg)) in fields.iter().zip(args.iter()).enumerate().skip(1) {
        let arg_target = projected_identity_module_target(field_name, index as i32, arg)?;
        if !same_identity_module_target(&target, &arg_target) {
            return None;
        }
    }

    Some(target)
}

fn projected_identity_module_target(field_name: &str, index: i32, arg: &Lambda) -> Option<Lambda> {
    match arg {
        Lambda::Lprim(crate::lambda::PrimInfo {
            primitive:
                Primitive::Pfield(
                    field_index,
                    FieldDbgInfo::Module {
                        name: projected_name,
                    },
                ),
            args,
            ..
        }) if *field_index == index && projected_name == field_name => match args.as_slice() {
            [Lambda::Lvar(_) | Lambda::LglobalModule(_, _)] => Some(args[0].clone()),
            _ => None,
        },
        _ => None,
    }
}

fn same_identity_module_target(left: &Lambda, right: &Lambda) -> bool {
    match (left, right) {
        (Lambda::Lvar(left_id), Lambda::Lvar(right_id)) => left_id.same(right_id),
        (
            Lambda::LglobalModule(left_id, left_dynamic_import),
            Lambda::LglobalModule(right_id, right_dynamic_import),
        ) => left_id.same(right_id) && left_dynamic_import == right_dynamic_import,
        _ => false,
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
                    || env
                        .optional_blocks
                        .get(id)
                        .is_some_and(|optional| hits(target, &optional.value, env, visiting))
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
            Lambda::LstaticRaise(_, args) => {
                args.iter().any(|arg| hits(target, arg, env, visiting))
            }
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
    if env.allow_direct_function_beta_reduce {
        if let Lambda::Lfunction(inline_func) = apply.ap_func.as_ref() {
            if should_inline_direct_function(inline_func, &apply.ap_args) {
                let reduced = beta_reduce::propagate_beta_reduce(
                    &inline_func.params,
                    &inline_func.body,
                    &apply.ap_args,
                );
                return simplify_with_env(&reduced, env, exports);
            }
        }
    }

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
                if let Some(reduced) = reduce_named_function_application(id, func, &args, exports) {
                    return simplify_with_env(&reduced, env, exports);
                }
            }
        }
    }

    // OCaml's lam_pass_remove_alias only tries named-function inlining when the
    // original callee is syntactically an Lvar. If simplifying a projected
    // callee later exposes an Lvar, OCaml rebuilds the apply instead of retrying
    // the inlining decision at that new shape.
    let func = match apply.ap_func.as_ref() {
        Lambda::Lvar(id) => env
            .call_substitutions
            .get(id)
            .cloned()
            .unwrap_or_else(|| simplify_with_env(&apply.ap_func, env, exports)),
        _ => simplify_with_env(&apply.ap_func, env, exports),
    };
    Lambda::Lapply(Apply {
        ap_func: Box::new(func),
        ap_args: args,
        ap_info: apply.ap_info.clone(),
        ap_transformed_jsx: apply.ap_transformed_jsx,
    })
}

fn reduce_named_function_application(
    id: &Ident,
    func: &LFunction,
    args: &[Lambda],
    exports: &HashSet<Ident>,
) -> Option<Lambda> {
    if func.params.len() != args.len() || !analysis::lfunction_can_be_inlined(func) {
        return None;
    }

    if func.attr.is_a_functor {
        return Some(beta_reduce::propagate_beta_reduce(
            &func.params,
            &func.body,
            args,
        ));
    }

    if !analysis::ok_to_inline_fun_when_app(func, args) {
        return None;
    }

    let (is_closed, param_map) = closure::is_closed_with_map(exports, &func.params, &func.body);
    if exports.contains(id) && !is_closed {
        return None;
    }

    Some(beta_reduce::propagate_beta_reduce_with_map(
        &param_map,
        &func.params,
        &func.body,
        args,
    ))
}

fn should_inline_direct_function(func: &LFunction, args: &[Lambda]) -> bool {
    func.params.len() == args.len() && analysis::lfunction_can_be_inlined(func)
}

fn js_function_arity(func: &LFunction) -> usize {
    if func.attr.one_unit_arg {
        0
    } else {
        func.params.len()
    }
}

fn eta_wrapped_args_match_params(params: &[Ident], args: &[Lambda]) -> bool {
    params.len() == args.len()
        && params.iter().zip(args).all(|(param, arg)| match arg {
            Lambda::Lvar(id) => id.same(param),
            Lambda::Lprim(crate::lambda::PrimInfo {
                primitive: Primitive::PjsFnMake(_) | Primitive::PjsFnMakeUnit,
                args: inner_args,
                ..
            }) => matches!(inner_args.as_slice(), [Lambda::Lvar(id)] if id.same(param)),
            _ => false,
        })
}

fn eta_reduce_function_value(func: &LFunction, env: &SimplifyEnv) -> Option<Lambda> {
    if func.attr.async_ || func.attr.directive.is_some() || func.attr.one_unit_arg {
        return None;
    }

    let apply = match func.body.as_ref() {
        Lambda::Lapply(apply) => apply,
        Lambda::Lsequence(first, second)
            if matches!(
                second.as_ref(),
                Lambda::Lconst(Constant::JsUndefined { .. })
            ) =>
        {
            let Lambda::Lapply(apply) = first.as_ref() else {
                return None;
            };
            apply
        }
        _ => return None,
    };

    if !eta_wrapped_args_match_params(&func.params, &apply.ap_args) {
        return None;
    }

    match apply.ap_func.as_ref() {
        Lambda::Lvar(id)
            if env
                .known_functions
                .get(id)
                .is_some_and(|known| js_function_arity(known) == func.params.len()) =>
        {
            Some(Lambda::var(id.clone()))
        }
        Lambda::Lprim(crate::lambda::PrimInfo {
            primitive: Primitive::Pfield(_, FieldDbgInfo::Module { .. }),
            args,
            ..
        }) if apply.ap_info.status != ApplyStatus::Na
            && matches!(
                args.as_slice(),
                [Lambda::LglobalModule(_, _) | Lambda::Lvar(_)]
            ) =>
        {
            Some((*apply.ap_func).clone())
        }
        _ => None,
    }
}

fn preserve_exported_eta_alias_binding(original_value: &Lambda, simplified_value: &Lambda) -> bool {
    if inlineable_local_function(original_value).is_none() {
        return false;
    }

    match simplified_value {
        Lambda::Lvar(_) => true,
        Lambda::Lprim(crate::lambda::PrimInfo {
            primitive: Primitive::Pfield(_, FieldDbgInfo::Module { .. }),
            args,
            ..
        }) => matches!(
            args.as_slice(),
            [Lambda::LglobalModule(_, _) | Lambda::Lvar(_)]
        ),
        _ => false,
    }
}

fn lambda_exports_ident(lam: &Lambda, id: &Ident) -> bool {
    match lam {
        Lambda::Lvar(_) | Lambda::LglobalModule(_, _) | Lambda::Lconst(_) => false,
        Lambda::Lapply(apply) => {
            lambda_exports_ident(&apply.ap_func, id)
                || apply
                    .ap_args
                    .iter()
                    .any(|arg| lambda_exports_ident(arg, id))
        }
        Lambda::Lfunction(func) => lambda_exports_ident(&func.body, id),
        Lambda::Llet(_, _, value, body) => {
            lambda_exports_ident(value, id) || lambda_exports_ident(body, id)
        }
        Lambda::Lletrec(bindings, body) => {
            bindings
                .iter()
                .any(|(_, expr)| lambda_exports_ident(expr, id))
                || lambda_exports_ident(body, id)
        }
        Lambda::Lprim(info) => {
            matches!(
                &info.primitive,
                Primitive::Pmakeblock(_, TagInfo::ModuleExport(ids), _)
                    if ids.iter().any(|exported| exported.same(id))
            ) || info.args.iter().any(|arg| lambda_exports_ident(arg, id))
        }
        Lambda::Lswitch(scrutinee, switch) => {
            lambda_exports_ident(scrutinee, id)
                || switch
                    .sw_consts
                    .iter()
                    .any(|(_, lam)| lambda_exports_ident(lam, id))
                || switch
                    .sw_blocks
                    .iter()
                    .any(|(_, lam)| lambda_exports_ident(lam, id))
                || switch
                    .sw_failaction
                    .as_deref()
                    .is_some_and(|lam| lambda_exports_ident(lam, id))
        }
        Lambda::LstringSwitch(scrutinee, cases, default) => {
            lambda_exports_ident(scrutinee, id)
                || cases.iter().any(|(_, lam)| lambda_exports_ident(lam, id))
                || default
                    .as_deref()
                    .is_some_and(|lam| lambda_exports_ident(lam, id))
        }
        Lambda::LstaticRaise(_, args) => args.iter().any(|arg| lambda_exports_ident(arg, id)),
        Lambda::LstaticCatch(body, _, handler) | Lambda::LtryWith(body, _, handler) => {
            lambda_exports_ident(body, id) || lambda_exports_ident(handler, id)
        }
        Lambda::LifThenElse(cond, then_, else_) => {
            lambda_exports_ident(cond, id)
                || lambda_exports_ident(then_, id)
                || lambda_exports_ident(else_, id)
        }
        Lambda::Lsequence(first, second) | Lambda::Lwhile(first, second) => {
            lambda_exports_ident(first, id) || lambda_exports_ident(second, id)
        }
        Lambda::Lfor(_, start, end, _, body) => {
            lambda_exports_ident(start, id)
                || lambda_exports_ident(end, id)
                || lambda_exports_ident(body, id)
        }
        Lambda::Lassign(_, value) => lambda_exports_ident(value, id),
    }
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

fn collect_known_functions(lam: &Lambda) -> HashMap<Ident, LFunction> {
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
                        functions.insert(id.clone(), func);
                    }
                }
                collect_into(body, functions);
            }
            Lambda::Lletrec(bindings, body) => {
                for (id, expr) in bindings {
                    collect_into(expr, functions);
                    if let Some(func) = inlineable_local_function(expr) {
                        functions.insert(id.clone(), func);
                    }
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

fn substitution_candidate(
    kind: LetKind,
    original_value: &Lambda,
    simplified_value: &Lambda,
) -> Option<Lambda> {
    if kind == LetKind::Variable {
        return None;
    }

    if matches!(original_value, Lambda::Lapply(_)) {
        return None;
    }

    match simplified_value {
        Lambda::Lvar(_) | Lambda::LglobalModule(_, _) => Some(simplified_value.clone()),
        Lambda::Lconst(constant) if can_substitute_constant_unconditionally(constant) => {
            Some(simplified_value.clone())
        }
        Lambda::Lprim(info)
            if matches!(
                (&info.primitive, info.args.as_slice()),
                (
                    Primitive::Pfield(_, FieldDbgInfo::Module { .. }),
                    [Lambda::LglobalModule(_, _) | Lambda::Lvar(_)]
                )
            ) =>
        {
            Some(simplified_value.clone())
        }
        _ => None,
    }
}

fn plain_string_constant(lam: &Lambda) -> Option<String> {
    match lam {
        Lambda::Lconst(Constant::String { s, delim: None }) => Some(s.clone()),
        _ => None,
    }
}

fn module_field_call_substitution_candidate(lam: &Lambda) -> bool {
    match lam {
        Lambda::Lprim(crate::lambda::PrimInfo {
            primitive: Primitive::Pfield(_, FieldDbgInfo::Module { .. }),
            args,
            ..
        }) => matches!(
            args.as_slice(),
            [Lambda::LglobalModule(_, _) | Lambda::Lvar(_)]
        ),
        _ => false,
    }
}

fn plain_string_value(lam: &Lambda, env: &SimplifyEnv) -> Option<String> {
    match lam {
        Lambda::Lconst(Constant::String { s, delim: None }) => Some(s.clone()),
        Lambda::Lvar(id) => env.plain_strings.get(id).cloned(),
        _ => None,
    }
}

fn can_substitute_constant_unconditionally(constant: &Constant) -> bool {
    !constant.is_allocating()
        && !matches!(constant, Constant::String { .. } | Constant::ImmString(_))
}

fn exported_alias_target(value: &Lambda) -> Option<Ident> {
    match value {
        Lambda::Lvar(target) => Some(target.clone()),
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

fn collect_exported_apply_bindings(lam: &Lambda, exports: &HashSet<Ident>) -> HashSet<Ident> {
    let mut preserved = HashSet::new();
    collect_exported_apply_bindings_into(lam, exports, &mut preserved);
    preserved
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
                for (exported, arg) in ids.iter().zip(info.args.iter()) {
                    if let Lambda::Lvar(target) = arg {
                        if target.name() == exported.name() {
                            exports.insert(target.clone());
                        }
                    }
                }
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

fn collect_exported_apply_bindings_into(
    lam: &Lambda,
    exports: &HashSet<Ident>,
    preserved: &mut HashSet<Ident>,
) {
    match lam {
        Lambda::Lvar(_) | Lambda::LglobalModule(_, _) | Lambda::Lconst(_) => {}
        Lambda::Lapply(apply) => {
            collect_exported_apply_bindings_into(&apply.ap_func, exports, preserved);
            for arg in &apply.ap_args {
                collect_exported_apply_bindings_into(arg, exports, preserved);
            }
        }
        Lambda::Lfunction(func) => {
            collect_exported_apply_bindings_into(&func.body, exports, preserved)
        }
        Lambda::Llet(_, id, value, body) => {
            if exports.contains(id)
                && (matches!(value.as_ref(), Lambda::Lapply(_))
                    || exported_eta_wrapper_binding(value))
            {
                preserved.insert(id.clone());
            }
            collect_exported_apply_bindings_into(value, exports, preserved);
            collect_exported_apply_bindings_into(body, exports, preserved);
        }
        Lambda::Lletrec(bindings, body) => {
            for (id, expr) in bindings {
                if exports.contains(id)
                    && (matches!(expr, Lambda::Lapply(_)) || exported_eta_wrapper_binding(expr))
                {
                    preserved.insert(id.clone());
                }
                collect_exported_apply_bindings_into(expr, exports, preserved);
            }
            collect_exported_apply_bindings_into(body, exports, preserved);
        }
        Lambda::Lprim(info) => {
            for arg in &info.args {
                collect_exported_apply_bindings_into(arg, exports, preserved);
            }
        }
        Lambda::Lswitch(scrutinee, switch) => {
            collect_exported_apply_bindings_into(scrutinee, exports, preserved);
            for (_, lam) in &switch.sw_consts {
                collect_exported_apply_bindings_into(lam, exports, preserved);
            }
            for (_, lam) in &switch.sw_blocks {
                collect_exported_apply_bindings_into(lam, exports, preserved);
            }
            if let Some(failaction) = &switch.sw_failaction {
                collect_exported_apply_bindings_into(failaction, exports, preserved);
            }
        }
        Lambda::LstringSwitch(scrutinee, cases, default) => {
            collect_exported_apply_bindings_into(scrutinee, exports, preserved);
            for (_, lam) in cases {
                collect_exported_apply_bindings_into(lam, exports, preserved);
            }
            if let Some(default) = default {
                collect_exported_apply_bindings_into(default, exports, preserved);
            }
        }
        Lambda::LstaticRaise(_, args) => {
            for arg in args {
                collect_exported_apply_bindings_into(arg, exports, preserved);
            }
        }
        Lambda::LstaticCatch(body, _, handler) | Lambda::LtryWith(body, _, handler) => {
            collect_exported_apply_bindings_into(body, exports, preserved);
            collect_exported_apply_bindings_into(handler, exports, preserved);
        }
        Lambda::LifThenElse(cond, then_, else_) => {
            collect_exported_apply_bindings_into(cond, exports, preserved);
            collect_exported_apply_bindings_into(then_, exports, preserved);
            collect_exported_apply_bindings_into(else_, exports, preserved);
        }
        Lambda::Lsequence(first, second) | Lambda::Lwhile(first, second) => {
            collect_exported_apply_bindings_into(first, exports, preserved);
            collect_exported_apply_bindings_into(second, exports, preserved);
        }
        Lambda::Lfor(_, start, end, _, body) => {
            collect_exported_apply_bindings_into(start, exports, preserved);
            collect_exported_apply_bindings_into(end, exports, preserved);
            collect_exported_apply_bindings_into(body, exports, preserved);
        }
        Lambda::Lassign(_, value) => {
            collect_exported_apply_bindings_into(value, exports, preserved)
        }
    }
}

fn exported_eta_wrapper_binding(value: &Lambda) -> bool {
    let Some(func) = inlineable_local_function(value) else {
        return false;
    };

    match func.body.as_ref() {
        Lambda::Lapply(apply) => eta_wrapped_args_match_params(&func.params, &apply.ap_args),
        Lambda::Lsequence(first, second)
            if matches!(
                second.as_ref(),
                Lambda::Lconst(Constant::JsUndefined { is_unit: true })
            ) =>
        {
            matches!(
                first.as_ref(),
                Lambda::Lapply(apply)
                    if eta_wrapped_args_match_params(&func.params, &apply.ap_args)
            )
        }
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use crate::ident::Ident;
    use crate::lambda::compat::{FieldDbgInfo, LetKind, SetFieldDbgInfo};
    use crate::lambda::constant::Constant;
    use crate::lambda::primitive::{
        ExternalArgAttr, ExternalObjLabel, ExternalObjSpec, Mutable, Primitive,
    };
    use crate::lambda::{
        ApInfo, Apply, ApplyStatus, DirectionFlag, FunctionAttribute, InlineAttribute, Lambda,
        TagInfo,
    };
    use crate::location::Location;

    use super::simplify_for_js_backend;

    fn find_binding_value<'a>(lam: &'a Lambda, target: &Ident) -> Option<&'a Lambda> {
        match lam {
            Lambda::Lvar(_) | Lambda::LglobalModule(_, _) | Lambda::Lconst(_) => None,
            Lambda::Lapply(apply) => find_binding_value(&apply.ap_func, target).or_else(|| {
                apply
                    .ap_args
                    .iter()
                    .find_map(|arg| find_binding_value(arg, target))
            }),
            Lambda::Lfunction(func) => find_binding_value(&func.body, target),
            Lambda::Llet(_, id, value, body) => {
                if id.same(target) {
                    Some(value.as_ref())
                } else {
                    find_binding_value(value, target).or_else(|| find_binding_value(body, target))
                }
            }
            Lambda::Lletrec(bindings, body) => bindings
                .iter()
                .find_map(|(id, value)| {
                    if id.same(target) {
                        Some(value)
                    } else {
                        find_binding_value(value, target)
                    }
                })
                .or_else(|| find_binding_value(body, target)),
            Lambda::Lprim(info) => info
                .args
                .iter()
                .find_map(|arg| find_binding_value(arg, target)),
            Lambda::Lswitch(scrutinee, switch) => find_binding_value(scrutinee, target)
                .or_else(|| {
                    switch
                        .sw_consts
                        .iter()
                        .find_map(|(_, lam)| find_binding_value(lam, target))
                })
                .or_else(|| {
                    switch
                        .sw_blocks
                        .iter()
                        .find_map(|(_, lam)| find_binding_value(lam, target))
                })
                .or_else(|| {
                    switch
                        .sw_failaction
                        .as_deref()
                        .and_then(|lam| find_binding_value(lam, target))
                }),
            Lambda::LstringSwitch(scrutinee, cases, default) => {
                find_binding_value(scrutinee, target)
                    .or_else(|| {
                        cases
                            .iter()
                            .find_map(|(_, lam)| find_binding_value(lam, target))
                    })
                    .or_else(|| {
                        default
                            .as_deref()
                            .and_then(|lam| find_binding_value(lam, target))
                    })
            }
            Lambda::LstaticRaise(_, args) => {
                args.iter().find_map(|arg| find_binding_value(arg, target))
            }
            Lambda::LstaticCatch(body, _, handler) | Lambda::LtryWith(body, _, handler) => {
                find_binding_value(body, target).or_else(|| find_binding_value(handler, target))
            }
            Lambda::LifThenElse(cond, then_, else_) => find_binding_value(cond, target)
                .or_else(|| find_binding_value(then_, target))
                .or_else(|| find_binding_value(else_, target)),
            Lambda::Lsequence(first, second) | Lambda::Lwhile(first, second) => {
                find_binding_value(first, target).or_else(|| find_binding_value(second, target))
            }
            Lambda::Lfor(_, start, end, _, body) => find_binding_value(start, target)
                .or_else(|| find_binding_value(end, target))
                .or_else(|| find_binding_value(body, target)),
            Lambda::Lassign(_, value) => find_binding_value(value, target),
        }
    }

    fn contains_apply_to(target: &Ident, lam: &Lambda) -> bool {
        match lam {
            Lambda::Lvar(_) | Lambda::LglobalModule(_, _) | Lambda::Lconst(_) => false,
            Lambda::Lapply(apply) => {
                matches!(apply.ap_func.as_ref(), Lambda::Lvar(id) if id.same(target))
                    || contains_apply_to(target, &apply.ap_func)
                    || apply
                        .ap_args
                        .iter()
                        .any(|arg| contains_apply_to(target, arg))
            }
            Lambda::Lfunction(func) => contains_apply_to(target, &func.body),
            Lambda::Llet(_, _, value, body) => {
                contains_apply_to(target, value) || contains_apply_to(target, body)
            }
            Lambda::Lletrec(bindings, body) => {
                bindings
                    .iter()
                    .any(|(_, value)| contains_apply_to(target, value))
                    || contains_apply_to(target, body)
            }
            Lambda::Lprim(info) => info.args.iter().any(|arg| contains_apply_to(target, arg)),
            Lambda::Lswitch(scrutinee, switch) => {
                contains_apply_to(target, scrutinee)
                    || switch
                        .sw_consts
                        .iter()
                        .any(|(_, lam)| contains_apply_to(target, lam))
                    || switch
                        .sw_blocks
                        .iter()
                        .any(|(_, lam)| contains_apply_to(target, lam))
                    || switch
                        .sw_failaction
                        .as_deref()
                        .is_some_and(|lam| contains_apply_to(target, lam))
            }
            Lambda::LstringSwitch(scrutinee, cases, default) => {
                contains_apply_to(target, scrutinee)
                    || cases.iter().any(|(_, lam)| contains_apply_to(target, lam))
                    || default
                        .as_deref()
                        .is_some_and(|lam| contains_apply_to(target, lam))
            }
            Lambda::LstaticRaise(_, args) => args.iter().any(|arg| contains_apply_to(target, arg)),
            Lambda::LstaticCatch(body, _, handler) | Lambda::LtryWith(body, _, handler) => {
                contains_apply_to(target, body) || contains_apply_to(target, handler)
            }
            Lambda::LifThenElse(cond, then_, else_) => {
                contains_apply_to(target, cond)
                    || contains_apply_to(target, then_)
                    || contains_apply_to(target, else_)
            }
            Lambda::Lsequence(first, second) | Lambda::Lwhile(first, second) => {
                contains_apply_to(target, first) || contains_apply_to(target, second)
            }
            Lambda::Lfor(_, start, end, _, body) => {
                contains_apply_to(target, start)
                    || contains_apply_to(target, end)
                    || contains_apply_to(target, body)
            }
            Lambda::Lassign(_, value) => contains_apply_to(target, value),
        }
    }

    #[test]
    fn eliminates_non_captured_ref_cells_to_mutable_variables() {
        let cell = Ident::create_local("cell");
        let lambda = Lambda::let_(
            LetKind::Strict,
            cell.clone(),
            Lambda::prim(
                Primitive::Pmakeblock(0, TagInfo::Tuple, Mutable::Mutable),
                vec![Lambda::const_(Constant::int(-1))],
                Location::none(),
            ),
            Lambda::seq(
                Lambda::prim(
                    Primitive::Psetfield(0, SetFieldDbgInfo::RecordSet("contents".to_string())),
                    vec![Lambda::var(cell.clone()), Lambda::const_(Constant::int(3))],
                    Location::none(),
                ),
                Lambda::prim(
                    Primitive::Pfield(0, FieldDbgInfo::Tuple),
                    vec![Lambda::var(cell.clone())],
                    Location::none(),
                ),
            ),
        );

        let simplified = simplify_for_js_backend(&lambda);
        let Lambda::Llet(kind, binding, value, body) = &simplified else {
            panic!("expected mutable variable binding, got {simplified:?}");
        };
        assert_eq!(*kind, LetKind::Variable);
        assert!(binding.same(&cell));
        assert!(matches!(
            value.as_ref(),
            Lambda::Lconst(Constant::Int { i: -1, .. })
        ));
        let Lambda::Lsequence(assign, read) = body.as_ref() else {
            panic!("expected assignment/read sequence, got {body:?}");
        };
        assert!(matches!(
            assign.as_ref(),
            Lambda::Lassign(id, value)
                if id.same(&cell)
                    && matches!(value.as_ref(), Lambda::Lconst(Constant::Int { i: 3, .. }))
        ));
        assert!(matches!(read.as_ref(), Lambda::Lvar(id) if id.same(&cell)));
    }

    #[test]
    fn eliminates_offsetref_updates_on_non_captured_ref_cells() {
        let cell = Ident::create_local("cell");
        let lambda = Lambda::let_(
            LetKind::Strict,
            cell.clone(),
            Lambda::prim(
                Primitive::Pmakeblock(0, TagInfo::Tuple, Mutable::Mutable),
                vec![Lambda::const_(Constant::int(0))],
                Location::none(),
            ),
            Lambda::seq(
                Lambda::prim(
                    Primitive::Poffsetref(1),
                    vec![Lambda::var(cell.clone())],
                    Location::none(),
                ),
                Lambda::prim(
                    Primitive::Pfield(0, FieldDbgInfo::Tuple),
                    vec![Lambda::var(cell.clone())],
                    Location::none(),
                ),
            ),
        );

        let simplified = simplify_for_js_backend(&lambda);
        let Lambda::Llet(kind, binding, value, body) = &simplified else {
            panic!("expected mutable variable binding, got {simplified:?}");
        };
        assert_eq!(*kind, LetKind::Variable);
        assert!(binding.same(&cell));
        assert!(matches!(
            value.as_ref(),
            Lambda::Lconst(Constant::Int { i: 0, .. })
        ));
        let Lambda::Lsequence(assign, read) = body.as_ref() else {
            panic!("expected assignment/read sequence, got {body:?}");
        };
        assert!(matches!(
            assign.as_ref(),
            Lambda::Lassign(id, value)
                if id.same(&cell)
                    && matches!(
                        value.as_ref(),
                        Lambda::Lprim(crate::lambda::PrimInfo {
                            primitive: Primitive::Poffsetint(1),
                            args,
                            ..
                        }) if matches!(args.as_slice(), [Lambda::Lvar(var)] if var.same(&cell))
                    )
        ));
        assert!(matches!(read.as_ref(), Lambda::Lvar(id) if id.same(&cell)));
    }

    #[test]
    fn keeps_closure_captured_ref_cells_boxed() {
        let cell = Ident::create_local("cell");
        let reader = Ident::create_local("reader");
        let lambda = Lambda::let_(
            LetKind::Strict,
            cell.clone(),
            Lambda::prim(
                Primitive::Pmakeblock(0, TagInfo::Tuple, Mutable::Mutable),
                vec![Lambda::const_(Constant::int(0))],
                Location::none(),
            ),
            Lambda::let_(
                LetKind::Strict,
                reader.clone(),
                Lambda::function_(
                    0,
                    vec![],
                    Lambda::prim(
                        Primitive::Pfield(0, FieldDbgInfo::Tuple),
                        vec![Lambda::var(cell.clone())],
                        Location::none(),
                    ),
                    FunctionAttribute::default(),
                ),
                Lambda::var(reader),
            ),
        );

        let simplified = simplify_for_js_backend(&lambda);
        let Some(binding) = find_binding_value(&simplified, &cell) else {
            panic!("expected ref binding to remain");
        };
        assert!(matches!(
            binding,
            Lambda::Lprim(crate::lambda::PrimInfo {
                primitive: Primitive::Pmakeblock(0, _, Mutable::Mutable),
                args,
                ..
            }) if matches!(args.as_slice(), [Lambda::Lconst(Constant::Int { i: 0, .. })])
        ));
    }

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
                    Primitive::Pmakeblock(0, TagInfo::constructor("A", 1, 0), Mutable::Immutable),
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
    fn simplifies_export_payloads_before_export_coercion() {
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
            Lambda::let_(
                LetKind::Strict,
                xx.clone(),
                Lambda::var(x.clone()),
                export_block,
            ),
        );

        let simplified = simplify_for_js_backend(&lambda);
        let Lambda::Lprim(crate::lambda::PrimInfo {
            primitive: Primitive::Pmakeblock(_, TagInfo::ModuleExport(export_ids), _),
            args,
            ..
        }) = simplified
        else {
            panic!("expected the export block to remain at the tail");
        };
        assert_eq!(export_ids, vec![x.clone(), xx.clone()]);
        assert!(matches!(
            args.as_slice(),
            [
                Lambda::Lconst(Constant::Int { i: 1, .. }),
                Lambda::Lconst(Constant::Int { i: 1, .. })
            ]
        ));
    }

    #[test]
    fn simplifies_exported_marshaled_string_payloads_before_export_coercion() {
        let exported = Ident::create_local("s");
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
            Lambda::const_(Constant::String {
                s: "😀".to_string(),
                delim: Some(crate::lambda::constant::StringDelim::StarJ),
            }),
            export_block,
        );

        let simplified = simplify_for_js_backend(&lambda);
        let Lambda::Lprim(crate::lambda::PrimInfo {
            primitive: Primitive::Pmakeblock(_, TagInfo::ModuleExport(exports), _),
            args,
            ..
        }) = &simplified
        else {
            panic!("expected the export block after marshaled-string alias cleanup");
        };
        assert_eq!(exports, &vec![exported.clone()]);
        assert!(matches!(
            args.as_slice(),
            [Lambda::Lconst(Constant::String { s, delim })]
                if s == "😀"
                    && matches!(delim, Some(crate::lambda::constant::StringDelim::StarJ))
        ));
        assert!(
            find_binding_value(&lambda, &exported).is_some(),
            "expected the original binding to exist before simplification",
        );
        assert!(
            find_binding_value(&simplified, &exported).is_none(),
            "expected the single-use exported plain string binding to inline",
        );
    }

    #[test]
    fn simplifies_export_only_constant_block_payloads_before_export_coercion() {
        let v = Ident::create_local("v");
        let res = Ident::create_local("res");
        let export_block = Lambda::prim(
            Primitive::Pmakeblock(
                0,
                TagInfo::ModuleExport(vec![v.clone(), res.clone()]),
                Mutable::Immutable,
            ),
            vec![Lambda::var(v.clone()), Lambda::var(res.clone())],
            Location::none(),
        );
        let lambda = Lambda::let_(
            LetKind::Strict,
            v.clone(),
            Lambda::const_(Constant::Block {
                tag: 0,
                tag_info: TagInfo::record(
                    vec![
                        ("x".to_string(), false),
                        ("y".to_string(), false),
                        ("z".to_string(), false),
                    ],
                    crate::parser::ast::MutableFlag::Immutable,
                ),
                elements: vec![
                    Constant::int(3),
                    Constant::int(4),
                    Constant::JsUndefined { is_unit: false },
                ],
            }),
            Lambda::let_(
                LetKind::Strict,
                res.clone(),
                Lambda::prim(
                    Primitive::Pfield(
                        0,
                        crate::lambda::compat::FieldDbgInfo::Record {
                            name: "x".to_string(),
                            mutable_flag: crate::parser::ast::MutableFlag::Immutable,
                        },
                    ),
                    vec![Lambda::var(v.clone())],
                    Location::none(),
                ),
                export_block,
            ),
        );

        let simplified = simplify_for_js_backend(&lambda);
        assert!(
            find_binding_value(&simplified, &v).is_none(),
            "expected the export-only constant block binding to disappear",
        );

        let (export_body, kept_res_binding) = match simplified {
            Lambda::Llet(_, kept_binding, kept_value, body) => {
                assert_eq!(kept_binding, res);
                assert!(matches!(
                    *kept_value,
                    Lambda::Lconst(Constant::Int { i: 3, .. })
                ));
                (*body, true)
            }
            Lambda::Lprim(_) => (simplified, false),
            other => panic!("expected the export block or a surviving `res` binding, got {other:?}"),
        };

        let Lambda::Lprim(crate::lambda::PrimInfo {
            primitive: Primitive::Pmakeblock(_, TagInfo::ModuleExport(export_ids), _),
            args,
            ..
        }) = export_body
        else {
            panic!("expected the export block to remain at the tail");
        };
        assert_eq!(export_ids, vec![v.clone(), res.clone()]);
        assert!(matches!(&args[0], Lambda::Lconst(Constant::Block { .. })));
        if kept_res_binding {
            assert!(matches!(&args[1], Lambda::Lvar(id) if *id == res));
        } else {
            assert!(matches!(
                &args[1],
                Lambda::Lconst(Constant::Int { i: 3, .. })
            ));
        }
    }

    #[test]
    fn keeps_export_bindings_reduced_from_named_function_calls() {
        let compose = Ident::create_local("compose");
        let composed = Ident::create_local("composed");
        let param = Ident::create_local("param");
        let export_block = Lambda::prim(
            Primitive::Pmakeblock(
                0,
                TagInfo::ModuleExport(vec![composed.clone()]),
                Mutable::Immutable,
            ),
            vec![Lambda::var(composed.clone())],
            Location::none(),
        );
        let lambda = Lambda::let_(
            LetKind::Strict,
            compose.clone(),
            Lambda::function_(
                1,
                vec![param.clone()],
                Lambda::var(param),
                FunctionAttribute::default(),
            ),
            Lambda::let_(
                LetKind::Strict,
                composed.clone(),
                Lambda::Lapply(Apply {
                    ap_func: Box::new(Lambda::var(compose)),
                    ap_args: vec![Lambda::const_(Constant::int(1))],
                    ap_info: ApInfo {
                        loc: Location::none(),
                        inlined: InlineAttribute::Default,
                        status: ApplyStatus::Na,
                    },
                    ap_transformed_jsx: false,
                }),
                export_block,
            ),
        );

        let simplified = simplify_for_js_backend(&lambda);
        let Lambda::Llet(_, kept_binding, kept_value, body) = simplified else {
            panic!("expected the reduced export binding to remain");
        };
        assert_eq!(kept_binding, composed);
        assert!(matches!(
            *kept_value,
            Lambda::Lconst(Constant::Int { i: 1, .. })
        ));
        let Lambda::Lprim(crate::lambda::PrimInfo {
            primitive: Primitive::Pmakeblock(_, TagInfo::ModuleExport(export_ids), _),
            args,
            ..
        }) = *body
        else {
            panic!("expected the export block to remain at the tail");
        };
        assert_eq!(export_ids, vec![kept_binding.clone()]);
        assert!(matches!(args.as_slice(), [Lambda::Lvar(id)] if *id == kept_binding));
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
    fn beta_reduces_nested_direct_wrapper_applications_after_intermediate_let_cleanup() {
        let outer = Ident::create_local("outer");
        let ignored = Ident::create_local("ignored");
        let inner = Ident::create_local("inner");

        let outer_func = Lambda::prim(
            Primitive::PjsFnMake(1),
            vec![Lambda::function_(
                1,
                vec![outer],
                Lambda::let_(
                    LetKind::Strict,
                    Ident::create_local("helper"),
                    Lambda::prim(
                        Primitive::PjsFnMake(1),
                        vec![Lambda::function_(
                            1,
                            vec![ignored],
                            Lambda::const_(Constant::int(1)),
                            FunctionAttribute::default(),
                        )],
                        Location::none(),
                    ),
                    Lambda::prim(
                        Primitive::PjsFnMake(1),
                        vec![Lambda::function_(
                            1,
                            vec![inner.clone()],
                            Lambda::const_(Constant::int(0)),
                            FunctionAttribute::default(),
                        )],
                        Location::none(),
                    ),
                ),
                FunctionAttribute::default(),
            )],
            Location::none(),
        );

        let lambda = Lambda::Lapply(Apply {
            ap_func: Box::new(Lambda::Lapply(Apply {
                ap_func: Box::new(outer_func),
                ap_args: vec![Lambda::const_(Constant::String {
                    s: "".to_string(),
                    delim: None,
                })],
                ap_info: ApInfo {
                    loc: Location::none(),
                    inlined: InlineAttribute::Default,
                    status: ApplyStatus::Na,
                },
                ap_transformed_jsx: false,
            })),
            ap_args: vec![Lambda::const_(Constant::String {
                s: "".to_string(),
                delim: None,
            })],
            ap_info: ApInfo {
                loc: Location::none(),
                inlined: InlineAttribute::Default,
                status: ApplyStatus::Na,
            },
            ap_transformed_jsx: false,
        });

        let simplified = simplify_for_js_backend(&lambda);
        assert!(matches!(
            simplified,
            Lambda::Lconst(Constant::Int { i: 0, .. })
        ));
    }

    #[test]
    fn lets_dce_pass_beta_reduces_nested_curried_direct_function_applications() {
        let x = Ident::create_local("x");
        let extra = Ident::create_local("extra");

        let lambda = Lambda::Lapply(Apply {
            ap_func: Box::new(Lambda::Lapply(Apply {
                ap_func: Box::new(Lambda::function_(
                    1,
                    vec![x.clone()],
                    Lambda::function_(
                        1,
                        vec![extra.clone()],
                        Lambda::prim(
                            Primitive::Paddint,
                            vec![Lambda::var(x), Lambda::var(extra)],
                            Location::none(),
                        ),
                        FunctionAttribute::default(),
                    ),
                    FunctionAttribute::default(),
                )),
                ap_args: vec![Lambda::const_(Constant::int(3))],
                ap_info: ApInfo {
                    loc: Location::none(),
                    inlined: InlineAttribute::Default,
                    status: ApplyStatus::Na,
                },
                ap_transformed_jsx: false,
            })),
            ap_args: vec![Lambda::const_(Constant::int(4))],
            ap_info: ApInfo {
                loc: Location::none(),
                inlined: InlineAttribute::Default,
                status: ApplyStatus::Na,
            },
            ap_transformed_jsx: false,
        });

        let simplified = simplify_for_js_backend(&lambda);
        assert!(
            matches!(
                simplified,
                Lambda::Lprim(crate::lambda::PrimInfo {
                    primitive: Primitive::Paddint,
                    ref args,
                    ..
                }) if matches!(
                    args.as_slice(),
                    [
                        Lambda::Lconst(Constant::Int { i: 3, .. }),
                        Lambda::Lconst(Constant::Int { i: 4, .. }),
                    ]
                )
            ),
            "expected nested curried call to collapse to a direct integer add, got {simplified:?}"
        );
    }

    #[test]
    fn simplifies_named_nested_pjs_fn_make_application_chain_from_ari_regress_shape() {
        let f = Ident::create_local("f");
        let x = Ident::create_local("x");
        let extra = Ident::create_local("extra");
        let prim0 = Ident::create_local("prim0");
        let prim1 = Ident::create_local("prim1");
        let g = Ident::create_local("g");

        let lambda = Lambda::let_(
            LetKind::Alias,
            f.clone(),
            Lambda::prim(
                Primitive::PjsFnMake(1),
                vec![Lambda::function_(
                    1,
                    vec![x.clone()],
                    Lambda::function_(
                        1,
                        vec![extra.clone()],
                        Lambda::Lapply(Apply {
                            ap_func: Box::new(Lambda::function_(
                                2,
                                vec![prim0.clone(), prim1.clone()],
                                Lambda::prim(
                                    Primitive::Paddint,
                                    vec![Lambda::var(prim0), Lambda::var(prim1)],
                                    Location::none(),
                                ),
                                FunctionAttribute::default(),
                            )),
                            ap_args: vec![Lambda::var(x), Lambda::var(extra)],
                            ap_info: ApInfo {
                                loc: Location::none(),
                                inlined: InlineAttribute::Default,
                                status: ApplyStatus::Uncurry,
                            },
                            ap_transformed_jsx: false,
                        }),
                        FunctionAttribute::default(),
                    ),
                    FunctionAttribute::default(),
                )],
                Location::none(),
            ),
            Lambda::let_(
                LetKind::Alias,
                g.clone(),
                Lambda::Lapply(Apply {
                    ap_func: Box::new(Lambda::Lapply(Apply {
                        ap_func: Box::new(Lambda::var(f)),
                        ap_args: vec![Lambda::const_(Constant::int(3))],
                        ap_info: ApInfo {
                            loc: Location::none(),
                            inlined: InlineAttribute::Default,
                            status: ApplyStatus::Uncurry,
                        },
                        ap_transformed_jsx: false,
                    })),
                    ap_args: vec![Lambda::const_(Constant::int(4))],
                    ap_info: ApInfo {
                        loc: Location::none(),
                        inlined: InlineAttribute::Default,
                        status: ApplyStatus::Uncurry,
                    },
                    ap_transformed_jsx: false,
                }),
                Lambda::var(g),
            ),
        );

        let simplified = simplify_for_js_backend(&lambda);
        assert!(
            matches!(
                simplified,
                Lambda::Lprim(crate::lambda::PrimInfo {
                    primitive: Primitive::Paddint,
                    ref args,
                    ..
                }) if matches!(
                    args.as_slice(),
                    [
                        Lambda::Lconst(Constant::Int { i: 3, .. }),
                        Lambda::Lconst(Constant::Int { i: 4, .. }),
                    ]
                )
            ),
            "expected ari_regress-style nested call to collapse to a direct integer add, got {simplified:?}"
        );
    }

    #[test]
    fn reruns_backend_cleanup_after_lets_dce_beta_reduces_uncurried_pjs_fn_make_calls() {
        fn contains_let(lam: &Lambda) -> bool {
            match lam {
                Lambda::Llet(_, _, _, _) | Lambda::Lletrec(_, _) => true,
                Lambda::Lvar(_) | Lambda::LglobalModule(_, _) | Lambda::Lconst(_) => false,
                Lambda::Lapply(apply) => {
                    contains_let(&apply.ap_func) || apply.ap_args.iter().any(contains_let)
                }
                Lambda::Lfunction(func) => contains_let(&func.body),
                Lambda::Lprim(info) => info.args.iter().any(contains_let),
                Lambda::Lswitch(scrutinee, switch) => {
                    contains_let(scrutinee)
                        || switch.sw_consts.iter().any(|(_, lam)| contains_let(lam))
                        || switch.sw_blocks.iter().any(|(_, lam)| contains_let(lam))
                        || switch
                            .sw_failaction
                            .as_deref()
                            .is_some_and(contains_let)
                }
                Lambda::LstringSwitch(scrutinee, cases, default) => {
                    contains_let(scrutinee)
                        || cases.iter().any(|(_, lam)| contains_let(lam))
                        || default.as_deref().is_some_and(contains_let)
                }
                Lambda::LstaticRaise(_, args) => args.iter().any(contains_let),
                Lambda::LstaticCatch(body, _, handler) | Lambda::LtryWith(body, _, handler) => {
                    contains_let(body) || contains_let(handler)
                }
                Lambda::LifThenElse(cond, then_, else_) => {
                    contains_let(cond) || contains_let(then_) || contains_let(else_)
                }
                Lambda::Lsequence(first, second) | Lambda::Lwhile(first, second) => {
                    contains_let(first) || contains_let(second)
                }
                Lambda::Lfor(_, start, end, _, body) => {
                    contains_let(start) || contains_let(end) || contains_let(body)
                }
                Lambda::Lassign(_, value) => contains_let(value),
            }
        }

        let f1 = Ident::create_local("f1");
        let x = Ident::create_local("x");
        let y = Ident::create_local("y");
        let z = Ident::create_local("z");

        let lambda = Lambda::let_(
            LetKind::Strict,
            f1.clone(),
            Lambda::prim(
                Primitive::PjsFnMake(1),
                vec![Lambda::function_(
                    1,
                    vec![x.clone()],
                    Lambda::prim(
                        Primitive::PjsFnMake(2),
                        vec![Lambda::function_(
                            2,
                            vec![y.clone(), z.clone()],
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
                    ),
                    FunctionAttribute::default(),
                )],
                Location::none(),
            ),
            Lambda::Lapply(Apply {
                ap_func: Box::new(Lambda::Lapply(Apply {
                    ap_func: Box::new(Lambda::var(f1)),
                    ap_args: vec![Lambda::const_(Constant::int(1))],
                    ap_info: ApInfo {
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
                ap_info: ApInfo {
                    loc: Location::none(),
                    inlined: InlineAttribute::Default,
                    status: ApplyStatus::Uncurry,
                },
                ap_transformed_jsx: false,
            }),
        );

        let simplified = simplify_for_js_backend(&lambda);
        assert!(
            !contains_let(&simplified),
            "expected the final backend cleanup pass to remove beta-reduction lets, got {simplified:?}"
        );
        assert!(
            matches!(
                simplified,
                Lambda::Lprim(crate::lambda::PrimInfo {
                    primitive: Primitive::Paddint,
                    ref args,
                    ..
                }) if matches!(
                    args.as_slice(),
                    [
                        Lambda::Lprim(crate::lambda::PrimInfo {
                            primitive: Primitive::Paddint,
                            args: inner_args,
                            ..
                        }),
                        Lambda::Lconst(Constant::Int { i: 3, .. }),
                    ] if matches!(
                        inner_args.as_slice(),
                        [
                            Lambda::Lconst(Constant::Int { i: 1, .. }),
                            Lambda::Lconst(Constant::Int { i: 2, .. }),
                        ]
                    )
                )
            ),
            "expected the arity_deopt-style uncurry chain to collapse to nested integer adds, got {simplified:?}"
        );
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
    fn collapses_identity_module_block_built_from_alias_projections() {
        let module_param = Ident::create_local("U");
        let projected = Ident::create_local("x");

        let lambda = Lambda::let_(
            LetKind::Alias,
            projected.clone(),
            Lambda::prim(
                Primitive::Pfield(
                    0,
                    FieldDbgInfo::Module {
                        name: "x".to_string(),
                    },
                ),
                vec![Lambda::var(module_param.clone())],
                Location::none(),
            ),
            Lambda::prim(
                Primitive::Pmakeblock(
                    0,
                    TagInfo::Module(vec!["x".to_string()]),
                    Mutable::Immutable,
                ),
                vec![Lambda::var(projected)],
                Location::none(),
            ),
        );

        let simplified = simplify_for_js_backend(&lambda);
        let Lambda::Lvar(id) = simplified else {
            panic!("expected the identity module block to collapse to the original module");
        };
        assert!(id.same(&module_param));
    }

    #[test]
    fn collapses_identity_module_block_built_from_global_module_projections() {
        let source = Ident::create_persistent("Belt_List");
        let lambda = Lambda::prim(
            Primitive::Pmakeblock(
                0,
                TagInfo::Module(vec!["length".to_string(), "size".to_string()]),
                Mutable::Immutable,
            ),
            vec![
                Lambda::prim(
                    Primitive::Pfield(
                        0,
                        FieldDbgInfo::Module {
                            name: "length".to_string(),
                        },
                    ),
                    vec![Lambda::global_module(source.clone(), false)],
                    Location::none(),
                ),
                Lambda::prim(
                    Primitive::Pfield(
                        1,
                        FieldDbgInfo::Module {
                            name: "size".to_string(),
                        },
                    ),
                    vec![Lambda::global_module(source.clone(), false)],
                    Location::none(),
                ),
            ],
            Location::none(),
        );

        let simplified = simplify_for_js_backend(&lambda);
        let Lambda::LglobalModule(id, dynamic_import) = simplified else {
            panic!("expected the identity module block to collapse to the global module");
        };
        assert!(id.same(&source));
        assert!(!dynamic_import);
    }

    #[test]
    fn keeps_non_identity_module_block_with_mixed_sources() {
        let left = Ident::create_local("Left");
        let right = Ident::create_local("Right");
        let lambda = Lambda::prim(
            Primitive::Pmakeblock(
                0,
                TagInfo::Module(vec!["x".to_string(), "y".to_string()]),
                Mutable::Immutable,
            ),
            vec![
                Lambda::prim(
                    Primitive::Pfield(
                        0,
                        FieldDbgInfo::Module {
                            name: "x".to_string(),
                        },
                    ),
                    vec![Lambda::var(left.clone())],
                    Location::none(),
                ),
                Lambda::prim(
                    Primitive::Pfield(
                        1,
                        FieldDbgInfo::Module {
                            name: "y".to_string(),
                        },
                    ),
                    vec![Lambda::var(right.clone())],
                    Location::none(),
                ),
            ],
            Location::none(),
        );

        let simplified = simplify_for_js_backend(&lambda);
        let Lambda::Lprim(crate::lambda::PrimInfo {
            primitive: Primitive::Pmakeblock(_, TagInfo::Module(fields), _),
            ..
        }) = simplified
        else {
            panic!("expected mixed-source module blocks to stay explicit");
        };
        assert_eq!(fields, vec!["x".to_string(), "y".to_string()]);
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
        let Lambda::Lprim(crate::lambda::PrimInfo {
            primitive: Primitive::Pmakeblock(_, TagInfo::ModuleExport(exports), _),
            args,
            ..
        }) = &simplified
        else {
            panic!("expected the export block after alias cleanup");
        };
        assert!(matches!(
            exports.as_slice(),
            [id] if *id == exported
        ));
        assert!(matches!(
            args.as_slice(),
            [Lambda::Lconst(Constant::String { s, .. })] if s == "hello world"
        ));
        assert!(find_binding_value(&simplified, &exported).is_none());
    }

    #[test]
    fn folds_transitive_string_alias_chains_like_ocaml_lets_dce() {
        let a0 = Ident::create_local("a0");
        let a1 = Ident::create_local("a1");
        let a2 = Ident::create_local("a2");
        let a3 = Ident::create_local("a3");
        let exported = Ident::create_local("a4");
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
                    a2.clone(),
                    Lambda::var(a1),
                    Lambda::let_(
                        LetKind::Strict,
                        a3.clone(),
                        Lambda::var(a2),
                        Lambda::let_(
                            LetKind::Strict,
                            exported.clone(),
                            Lambda::prim(
                                Primitive::Pstringadd,
                                vec![
                                    Lambda::var(a3),
                                    Lambda::const_(Constant::string("world")),
                                ],
                                Location::none(),
                            ),
                            export_block,
                        ),
                    ),
                ),
            ),
        );

        let simplified = simplify_for_js_backend(&lambda);
        let Lambda::Lprim(crate::lambda::PrimInfo {
            primitive: Primitive::Pmakeblock(_, TagInfo::ModuleExport(exports), _),
            args,
            ..
        }) = &simplified
        else {
            panic!("expected the export block after transitive alias cleanup");
        };
        assert!(matches!(
            exports.as_slice(),
            [id] if *id == exported
        ));
        assert!(matches!(
            args.as_slice(),
            [Lambda::Lconst(Constant::String { s, .. })] if s == "hello world"
        ));
        assert!(find_binding_value(&simplified, &exported).is_none());
    }

    #[test]
    fn keeps_multi_use_plain_string_bindings_like_ocaml() {
        let shared = Ident::create_local("shared");
        let lambda = Lambda::let_(
            LetKind::Strict,
            shared.clone(),
            Lambda::const_(Constant::String {
                s: "hello".to_string(),
                delim: None,
            }),
            Lambda::prim(
                Primitive::Pmakeblock(
                    0,
                    TagInfo::module(vec!["a".to_string(), "b".to_string()]),
                    Mutable::Immutable,
                ),
                vec![Lambda::var(shared.clone()), Lambda::var(shared.clone())],
                Location::none(),
            ),
        );

        let simplified = simplify_for_js_backend(&lambda);
        let Lambda::Llet(kind, kept_id, kept_value, body) = simplified else {
            panic!("expected the shared plain-string binding to remain");
        };
        assert_eq!(kind, LetKind::Alias);
        assert_eq!(kept_id, shared);
        assert!(matches!(
            *kept_value,
            Lambda::Lconst(Constant::String { ref s, delim: None }) if s == "hello"
        ));

        let Lambda::Lprim(crate::lambda::PrimInfo {
            primitive: Primitive::Pmakeblock(_, TagInfo::Module(fields), _),
            args,
            ..
        }) = *body
        else {
            panic!("expected the module block to keep both shared string references");
        };
        assert_eq!(fields, vec!["a".to_string(), "b".to_string()]);
        assert!(matches!(&args[0], Lambda::Lvar(id) if id == &shared));
        assert!(matches!(&args[1], Lambda::Lvar(id) if id == &shared));
    }

    #[test]
    fn inlines_captured_single_use_plain_string_aliases_like_ocaml() {
        let alias = Ident::create_local("alias");
        let lambda = Lambda::let_(
            LetKind::Alias,
            alias.clone(),
            Lambda::const_(Constant::String {
                s: "hello".to_string(),
                delim: None,
            }),
            Lambda::function_(0, vec![], Lambda::var(alias), FunctionAttribute::default()),
        );

        let simplified = simplify_for_js_backend(&lambda);
        let Lambda::Lfunction(func) = simplified else {
            panic!("expected the captured single-use string alias to inline");
        };
        assert!(matches!(
            *func.body,
            Lambda::Lconst(Constant::String { ref s, delim: None }) if s == "hello"
        ));
    }

    #[test]
    fn inlines_single_use_strict_plain_string_field_reads_into_module_blocks_like_ocaml() {
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
                    elements: vec![Constant::int(42), Constant::string("a")],
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
        let Some(shared_value) = find_binding_value(&simplified, &shared) else {
            panic!("expected shared allocating constant binding to remain");
        };
        assert!(matches!(
            shared_value,
            Lambda::Lconst(Constant::Block { .. })
        ));
        assert!(
            find_binding_value(&simplified, &projected).is_none(),
            "expected the single-use projected plain-string binding to inline",
        );
        let Some(exported_value) = find_binding_value(&simplified, &exported) else {
            panic!("expected exported binding to remain");
        };
        let Lambda::Lprim(crate::lambda::PrimInfo {
            primitive: Primitive::Pmakeblock(_, TagInfo::Module(fields), _),
            args,
            ..
        }) = exported_value
        else {
            panic!("expected module block");
        };
        assert_eq!(fields, &vec!["a".to_string(), "name".to_string()]);
        assert!(matches!(&args[0], Lambda::Lvar(id) if *id == shared));
        assert!(matches!(
            &args[1],
            Lambda::Lconst(Constant::String { s, delim: None }) if s == "a"
        ));
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
    fn unboxes_plain_val_from_option_not_nest_vars() {
        let value = Ident::create_local("value");
        let simplified = simplify_for_js_backend(&Lambda::prim(
            Primitive::PvalFromOptionNotNest,
            vec![Lambda::var(value.clone())],
            Location::none(),
        ));

        assert!(matches!(simplified, Lambda::Lvar(id) if id == value));
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
    fn does_not_inline_exported_non_closed_function_applications() {
        let closed_over = Ident::create_local("map");
        let helper = Ident::create_local("xFromJs");
        let helper_param = Ident::create_local("param");
        let consumer = Ident::create_local("idx");
        let consumer_param = Ident::create_local("v");
        let export_block = Lambda::prim(
            Primitive::Pmakeblock(
                0,
                TagInfo::ModuleExport(vec![helper.clone(), consumer.clone()]),
                Mutable::Immutable,
            ),
            vec![Lambda::var(helper.clone()), Lambda::var(consumer.clone())],
            Location::none(),
        );

        let lambda = Lambda::let_(
            LetKind::Strict,
            closed_over.clone(),
            Lambda::prim(
                Primitive::Paddint,
                vec![
                    Lambda::const_(Constant::int(1)),
                    Lambda::const_(Constant::int(1)),
                ],
                Location::none(),
            ),
            Lambda::let_(
                LetKind::Strict,
                helper.clone(),
                Lambda::function_(
                    1,
                    vec![helper_param.clone()],
                    Lambda::prim(
                        Primitive::Paddint,
                        vec![Lambda::var(helper_param), Lambda::var(closed_over.clone())],
                        Location::none(),
                    ),
                    FunctionAttribute::default(),
                ),
                Lambda::let_(
                    LetKind::Strict,
                    consumer.clone(),
                    Lambda::function_(
                        1,
                        vec![consumer_param.clone()],
                        Lambda::prim(
                            Primitive::Paddint,
                            vec![
                                Lambda::Lapply(Apply {
                                    ap_func: Box::new(Lambda::var(helper.clone())),
                                    ap_args: vec![Lambda::var(consumer_param.clone())],
                                    ap_info: ApInfo {
                                        loc: Location::none(),
                                        inlined: InlineAttribute::Default,
                                        status: ApplyStatus::Na,
                                    },
                                    ap_transformed_jsx: false,
                                }),
                                Lambda::var(consumer_param),
                            ],
                            Location::none(),
                        ),
                        FunctionAttribute::default(),
                    ),
                    export_block,
                ),
            ),
        );

        let simplified = simplify_for_js_backend(&lambda);
        let helper_value =
            find_binding_value(&simplified, &helper).expect("expected exported helper binding");
        assert!(matches!(helper_value, Lambda::Lfunction(_)));

        let consumer_value =
            find_binding_value(&simplified, &consumer).expect("expected consumer binding");
        let Lambda::Lfunction(consumer_func) = consumer_value else {
            panic!("expected consumer binding to remain a function");
        };
        assert!(
            contains_apply_to(&helper, &consumer_func.body),
            "exported non-closed helpers should stay materialized at call sites"
        );
    }

    #[test]
    fn still_inlines_exported_closed_function_applications() {
        let helper = Ident::create_local("xToJs");
        let helper_param = Ident::create_local("param");
        let consumer = Ident::create_local("idx");
        let consumer_param = Ident::create_local("v");
        let export_block = Lambda::prim(
            Primitive::Pmakeblock(
                0,
                TagInfo::ModuleExport(vec![helper.clone(), consumer.clone()]),
                Mutable::Immutable,
            ),
            vec![Lambda::var(helper.clone()), Lambda::var(consumer.clone())],
            Location::none(),
        );

        let lambda = Lambda::let_(
            LetKind::Strict,
            helper.clone(),
            Lambda::function_(
                1,
                vec![helper_param.clone()],
                Lambda::prim(
                    Primitive::Paddint,
                    vec![Lambda::var(helper_param), Lambda::const_(Constant::int(1))],
                    Location::none(),
                ),
                FunctionAttribute::default(),
            ),
            Lambda::let_(
                LetKind::Strict,
                consumer.clone(),
                Lambda::function_(
                    1,
                    vec![consumer_param.clone()],
                    Lambda::prim(
                        Primitive::Paddint,
                        vec![
                            Lambda::Lapply(Apply {
                                ap_func: Box::new(Lambda::var(helper.clone())),
                                ap_args: vec![Lambda::var(consumer_param.clone())],
                                ap_info: ApInfo {
                                    loc: Location::none(),
                                    inlined: InlineAttribute::Default,
                                    status: ApplyStatus::Na,
                                },
                                ap_transformed_jsx: false,
                            }),
                            Lambda::var(consumer_param),
                        ],
                        Location::none(),
                    ),
                    FunctionAttribute::default(),
                ),
                export_block,
            ),
        );

        let simplified = simplify_for_js_backend(&lambda);
        let helper_value =
            find_binding_value(&simplified, &helper).expect("expected exported helper binding");
        assert!(matches!(helper_value, Lambda::Lfunction(_)));

        let consumer_value =
            find_binding_value(&simplified, &consumer).expect("expected consumer binding");
        let Lambda::Lfunction(consumer_func) = consumer_value else {
            panic!("expected consumer binding to remain a function");
        };
        assert!(
            !contains_apply_to(&helper, &consumer_func.body),
            "exported closed helpers should still inline at call sites"
        );
    }

    #[test]
    fn does_not_inline_non_closed_helpers_reached_through_export_aliases() {
        let closed_over = Ident::create_local("map");
        let helper_impl = Ident::create_local("xFromJs");
        let helper_alias = Ident::create_local("xFromJs");
        let exported_helper = Ident::create_local("xFromJs");
        let helper_param = Ident::create_local("param");
        let consumer = Ident::create_local("idx");
        let consumer_param = Ident::create_local("v");
        let export_block = Lambda::prim(
            Primitive::Pmakeblock(
                0,
                TagInfo::ModuleExport(vec![exported_helper.clone(), consumer.clone()]),
                Mutable::Immutable,
            ),
            vec![
                Lambda::var(exported_helper.clone()),
                Lambda::var(consumer.clone()),
            ],
            Location::none(),
        );

        let lambda = Lambda::let_(
            LetKind::Strict,
            closed_over.clone(),
            Lambda::prim(
                Primitive::Paddint,
                vec![
                    Lambda::const_(Constant::int(1)),
                    Lambda::const_(Constant::int(1)),
                ],
                Location::none(),
            ),
            Lambda::let_(
                LetKind::Strict,
                helper_impl.clone(),
                Lambda::function_(
                    1,
                    vec![helper_param.clone()],
                    Lambda::prim(
                        Primitive::Paddint,
                        vec![Lambda::var(helper_param), Lambda::var(closed_over.clone())],
                        Location::none(),
                    ),
                    FunctionAttribute::default(),
                ),
                Lambda::let_(
                    LetKind::Alias,
                    helper_alias.clone(),
                    Lambda::var(helper_impl.clone()),
                    Lambda::let_(
                        LetKind::Alias,
                        exported_helper.clone(),
                        Lambda::var(helper_alias),
                        Lambda::let_(
                            LetKind::Strict,
                            consumer.clone(),
                            Lambda::function_(
                                1,
                                vec![consumer_param.clone()],
                                Lambda::prim(
                                    Primitive::Paddint,
                                    vec![
                                        Lambda::Lapply(Apply {
                                            ap_func: Box::new(Lambda::var(exported_helper.clone())),
                                            ap_args: vec![Lambda::var(consumer_param.clone())],
                                            ap_info: ApInfo {
                                                loc: Location::none(),
                                                inlined: InlineAttribute::Default,
                                                status: ApplyStatus::Na,
                                            },
                                            ap_transformed_jsx: false,
                                        }),
                                        Lambda::var(consumer_param),
                                    ],
                                    Location::none(),
                                ),
                                FunctionAttribute::default(),
                            ),
                            export_block,
                        ),
                    ),
                ),
            ),
        );

        let simplified = simplify_for_js_backend(&lambda);
        let helper_value =
            find_binding_value(&simplified, &helper_impl).expect("expected helper implementation");
        assert!(matches!(helper_value, Lambda::Lfunction(_)));

        let consumer_value =
            find_binding_value(&simplified, &consumer).expect("expected consumer binding");
        let Lambda::Lfunction(consumer_func) = consumer_value else {
            panic!("expected consumer binding to remain a function");
        };
        assert!(
            contains_apply_to(&helper_impl, &consumer_func.body),
            "non-closed helpers reached through exported aliases should stay materialized, got {simplified:?}"
        );
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
                        vec![
                            Lambda::var(this_param.clone()),
                            Lambda::var(async_arg.clone()),
                        ],
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
    fn eta_reduces_module_field_function_values_like_ocaml() {
        let belt_map = Ident::create_persistent("Belt_MapInt");
        let param = Ident::create_local("items");

        let simplified = simplify_for_js_backend(&Lambda::function_(
            1,
            vec![param.clone()],
            Lambda::Lapply(Apply {
                ap_func: Box::new(Lambda::prim(
                    Primitive::Pfield(
                        0,
                        FieldDbgInfo::Module {
                            name: "fromArray".to_string(),
                        },
                    ),
                    vec![Lambda::LglobalModule(belt_map.clone(), false)],
                    Location::none(),
                )),
                ap_args: vec![Lambda::var(param.clone())],
                ap_info: ApInfo {
                    loc: Location::none(),
                    inlined: InlineAttribute::Default,
                    status: ApplyStatus::Uncurry,
                },
                ap_transformed_jsx: false,
            }),
            FunctionAttribute::default(),
        ));

        assert!(matches!(
            simplified,
            Lambda::Lprim(crate::lambda::PrimInfo {
                primitive: Primitive::Pfield(_, FieldDbgInfo::Module { ref name }),
                args,
                ..
            }) if name == "fromArray"
                && matches!(args.as_slice(), [Lambda::LglobalModule(id, false)] if id.same(&belt_map))
        ));
    }

    #[test]
    fn eta_reduces_unit_returning_module_field_wrappers_like_ocaml() {
        let belt_set = Ident::create_persistent("Belt_Set");
        let param = Ident::create_local("set");

        let simplified = simplify_for_js_backend(&Lambda::function_(
            1,
            vec![param.clone()],
            Lambda::seq(
                Lambda::Lapply(Apply {
                    ap_func: Box::new(Lambda::prim(
                        Primitive::Pfield(
                            0,
                            FieldDbgInfo::Module {
                                name: "checkInvariantInternal".to_string(),
                            },
                        ),
                        vec![Lambda::LglobalModule(belt_set.clone(), false)],
                        Location::none(),
                    )),
                    ap_args: vec![Lambda::var(param.clone())],
                    ap_info: ApInfo {
                        loc: Location::none(),
                        inlined: InlineAttribute::Default,
                        status: ApplyStatus::Uncurry,
                    },
                    ap_transformed_jsx: false,
                }),
                Lambda::const_(Constant::JsUndefined { is_unit: true }),
            ),
            FunctionAttribute {
                return_unit: true,
                ..FunctionAttribute::default()
            },
        ));

        assert!(matches!(
            simplified,
            Lambda::Lprim(crate::lambda::PrimInfo {
                primitive: Primitive::Pfield(_, FieldDbgInfo::Module { ref name }),
                args,
                ..
            }) if name == "checkInvariantInternal"
                && matches!(args.as_slice(), [Lambda::LglobalModule(id, false)] if id.same(&belt_set))
        ));
    }

    #[test]
    fn eta_reduces_wrappers_around_known_async_functions_like_ocaml() {
        let target = Ident::create_local("broken");
        let param = Ident::create_local("someAsyncFunction");
        let exported = Ident::create_local("broken");

        let simplified = simplify_for_js_backend(&Lambda::let_(
            LetKind::Strict,
            target.clone(),
            Lambda::function_(
                1,
                vec![param.clone()],
                Lambda::var(param.clone()),
                FunctionAttribute {
                    async_: true,
                    ..FunctionAttribute::default()
                },
            ),
            Lambda::let_(
                LetKind::Strict,
                exported.clone(),
                Lambda::function_(
                    1,
                    vec![param.clone()],
                    Lambda::Lapply(Apply {
                        ap_func: Box::new(Lambda::var(target.clone())),
                        ap_args: vec![Lambda::var(param.clone())],
                        ap_info: ApInfo {
                            loc: Location::none(),
                            inlined: InlineAttribute::Default,
                            status: ApplyStatus::Na,
                        },
                        ap_transformed_jsx: false,
                    }),
                    FunctionAttribute::default(),
                ),
                Lambda::prim(
                    Primitive::Pmakeblock(
                        0,
                        TagInfo::ModuleExport(vec![exported.clone()]),
                        Mutable::Immutable,
                    ),
                    vec![Lambda::var(exported.clone())],
                    Location::none(),
                ),
            ),
        ));

        match simplified {
            Lambda::Llet(_, id, value, body) if id.same(&target) => {
                let Lambda::Lfunction(func) = *value else {
                    panic!("expected the async target binding to stay a function");
                };
                assert!(func.attr.async_);
                let Lambda::Llet(_, alias_id, alias_value, export_body) = *body else {
                    panic!(
                        "expected the exported wrapper binding to stay materialized, got body: {body:?}"
                    );
                };
                assert!(alias_id.same(&exported));
                assert!(matches!(*alias_value, Lambda::Lvar(alias) if alias.same(&target)));
                assert!(matches!(
                    *export_body,
                    Lambda::Lprim(crate::lambda::PrimInfo {
                        primitive: Primitive::Pmakeblock(_, TagInfo::ModuleExport(ids), _),
                        args,
                        ..
                    }) if matches!(ids.as_slice(), [id] if id.same(&exported))
                        && matches!(args.as_slice(), [Lambda::Lvar(id)] if id.same(&exported))
                ));
            }
            other => {
                panic!("expected a retained async binding with a direct alias body, got {other:?}")
            }
        }
    }

    #[test]
    fn exported_eta_alias_calls_use_direct_callee_but_keep_export_binding_like_ocaml() {
        let stdlib_lazy = Ident::create_persistent("Stdlib_Lazy");
        let exported = Ident::create_local("a2");
        let result = Ident::create_local("a4");
        let param = Ident::create_local("x");
        let direct_callee = Lambda::prim(
            Primitive::Pfield(
                0,
                FieldDbgInfo::Module {
                    name: "from_val".to_string(),
                },
            ),
            vec![Lambda::LglobalModule(stdlib_lazy.clone(), false)],
            Location::none(),
        );

        let simplified = simplify_for_js_backend(&Lambda::let_(
            LetKind::Strict,
            exported.clone(),
            Lambda::function_(
                1,
                vec![param.clone()],
                Lambda::Lapply(Apply {
                    ap_func: Box::new(direct_callee.clone()),
                    ap_args: vec![Lambda::var(param.clone())],
                    ap_info: ApInfo {
                        loc: Location::none(),
                        inlined: InlineAttribute::Default,
                        status: ApplyStatus::Uncurry,
                    },
                    ap_transformed_jsx: false,
                }),
                FunctionAttribute::default(),
            ),
            Lambda::let_(
                LetKind::Strict,
                result.clone(),
                Lambda::Lapply(Apply {
                    ap_func: Box::new(Lambda::var(exported.clone())),
                    ap_args: vec![Lambda::const_(Constant::int(3))],
                    ap_info: ApInfo {
                        loc: Location::none(),
                        inlined: InlineAttribute::Default,
                        status: ApplyStatus::Uncurry,
                    },
                    ap_transformed_jsx: false,
                }),
                Lambda::prim(
                    Primitive::Pmakeblock(
                        0,
                        TagInfo::ModuleExport(vec![exported.clone(), result.clone()]),
                        Mutable::Immutable,
                    ),
                    vec![Lambda::var(exported.clone()), Lambda::var(result.clone())],
                    Location::none(),
                ),
            ),
        ));

        let Lambda::Llet(_, kept_export, export_value, body) = simplified else {
            panic!("expected the exported alias binding to remain materialized");
        };
        assert!(kept_export.same(&exported));
        assert!(matches!(
            *export_value,
            Lambda::Lprim(crate::lambda::PrimInfo {
                primitive: Primitive::Pfield(_, FieldDbgInfo::Module { ref name }),
                args,
                ..
            }) if name == "from_val"
                && matches!(args.as_slice(), [Lambda::LglobalModule(id, false)] if id.same(&stdlib_lazy))
        ));

        let Lambda::Llet(_, kept_result, result_value, export_block) = *body else {
            panic!("expected the direct call result binding to remain before exports");
        };
        assert!(kept_result.same(&result));
        assert!(matches!(
            *result_value,
            Lambda::Lapply(Apply { ap_func, ap_args, .. })
                if matches!(
                    ap_func.as_ref(),
                    Lambda::Lprim(crate::lambda::PrimInfo {
                        primitive: Primitive::Pfield(_, FieldDbgInfo::Module { name }),
                        args,
                        ..
                    }) if name == "from_val"
                        && matches!(args.as_slice(), [Lambda::LglobalModule(id, false)] if id.same(&stdlib_lazy))
                )
                    && matches!(
                        ap_args.as_slice(),
                        [Lambda::Lconst(Constant::Int { i: 3, .. })]
                    )
        ));

        assert!(matches!(
            *export_block,
            Lambda::Lprim(crate::lambda::PrimInfo {
                primitive: Primitive::Pmakeblock(_, TagInfo::ModuleExport(ids), _),
                args,
                ..
            }) if matches!(ids.as_slice(), [first, second] if first.same(&exported) && second.same(&result))
                && matches!(args.as_slice(), [Lambda::Lvar(first), Lambda::Lvar(second)] if first.same(&exported) && second.same(&result))
        ));
    }

    #[test]
    fn exported_pjs_fn_make_eta_alias_calls_use_direct_callee_like_lazy_test() {
        let stdlib_lazy = Ident::create_persistent("Stdlib_Lazy");
        let exported = Ident::create_local("a2");
        let result = Ident::create_local("a4");
        let param = Ident::create_local("x");
        let direct_callee = Lambda::prim(
            Primitive::Pfield(
                7,
                FieldDbgInfo::Module {
                    name: "from_val".to_string(),
                },
            ),
            vec![Lambda::LglobalModule(stdlib_lazy.clone(), false)],
            Location::none(),
        );

        let simplified = simplify_for_js_backend(&Lambda::let_(
            LetKind::Strict,
            exported.clone(),
            Lambda::prim(
                Primitive::PjsFnMake(1),
                vec![Lambda::function_(
                    1,
                    vec![param.clone()],
                    Lambda::Lapply(Apply {
                        ap_func: Box::new(direct_callee.clone()),
                        ap_args: vec![Lambda::var(param.clone())],
                        ap_info: ApInfo {
                            loc: Location::none(),
                            inlined: InlineAttribute::Default,
                            status: ApplyStatus::Uncurry,
                        },
                        ap_transformed_jsx: false,
                    }),
                    FunctionAttribute::default(),
                )],
                Location::none(),
            ),
            Lambda::let_(
                LetKind::Strict,
                result.clone(),
                Lambda::Lapply(Apply {
                    ap_func: Box::new(Lambda::var(exported.clone())),
                    ap_args: vec![Lambda::const_(Constant::int(3))],
                    ap_info: ApInfo {
                        loc: Location::none(),
                        inlined: InlineAttribute::Default,
                        status: ApplyStatus::Uncurry,
                    },
                    ap_transformed_jsx: false,
                }),
                Lambda::prim(
                    Primitive::Pmakeblock(
                        0,
                        TagInfo::ModuleExport(vec![exported.clone(), result.clone()]),
                        Mutable::Immutable,
                    ),
                    vec![Lambda::var(exported.clone()), Lambda::var(result.clone())],
                    Location::none(),
                ),
            ),
        ));

        let Lambda::Llet(_, kept_export, export_value, body) = simplified else {
            panic!("expected the exported wrapper binding to simplify to a direct alias");
        };
        assert!(kept_export.same(&exported));
        assert!(matches!(
            *export_value,
            Lambda::Lprim(crate::lambda::PrimInfo {
                primitive: Primitive::Pfield(_, FieldDbgInfo::Module { ref name }),
                ref args,
                ..
            }) if name == "from_val"
                && matches!(args.as_slice(), [Lambda::LglobalModule(id, false)] if id.same(&stdlib_lazy))
        ));

        let Lambda::Llet(_, kept_result, result_value, _) = *body else {
            panic!("expected the direct call result binding to remain before exports");
        };
        assert!(kept_result.same(&result));
        assert!(matches!(
            *result_value,
            Lambda::Lapply(Apply { ap_func, ap_args, .. })
                if matches!(
                    ap_func.as_ref(),
                    Lambda::Lprim(crate::lambda::PrimInfo {
                        primitive: Primitive::Pfield(_, FieldDbgInfo::Module { name }),
                        args,
                        ..
                    }) if name == "from_val"
                        && matches!(args.as_slice(), [Lambda::LglobalModule(id, false)] if id.same(&stdlib_lazy))
                )
                    && matches!(
                        ap_args.as_slice(),
                        [Lambda::Lconst(Constant::Int { i: 3, .. })]
                    )
        ));
    }

    #[test]
    fn zero_arg_wrappers_do_not_eta_reduce_like_ocaml() {
        let target = Ident::create_local("fff");

        let simplified = simplify_for_js_backend(&Lambda::let_(
            LetKind::Strict,
            target.clone(),
            Lambda::function_(
                0,
                vec![],
                Lambda::const_(Constant::int(3)),
                FunctionAttribute::default(),
            ),
            Lambda::function_(
                0,
                vec![],
                Lambda::Lapply(Apply {
                    ap_func: Box::new(Lambda::var(target.clone())),
                    ap_args: vec![],
                    ap_info: ApInfo {
                        loc: Location::none(),
                        inlined: InlineAttribute::Default,
                        status: ApplyStatus::Na,
                    },
                    ap_transformed_jsx: false,
                }),
                FunctionAttribute::default(),
            ),
        ));

        assert!(matches!(
            simplified,
            Lambda::Llet(_, _, _, _) | Lambda::Lfunction(_)
        ));
        assert!(!matches!(simplified, Lambda::Lvar(_)));
    }

    #[test]
    fn beta_reduces_downarity_pjs_fn_make_calls_past_the_outer_apply() {
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
                                    vec![Lambda::var(x.clone()), Lambda::var(y.clone())],
                                    Location::none(),
                                ),
                                Lambda::var(z.clone()),
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

        let Lambda::Lapply(apply) = simplified else {
            panic!("expected the outer uncurry apply to survive the final backend cleanup");
        };
        let Lambda::Lfunction(func) = apply.ap_func.as_ref() else {
            panic!("expected the final cleanup pass to unwrap the surviving callee to a direct function, got {apply:?}");
        };

        assert_eq!(func.params.len(), 2);
        assert!(matches!(
            func.params.as_slice(),
            [first, second] if first.same(&y) && second.same(&z)
        ));
        assert!(matches!(
            func.body.as_ref(),
            Lambda::Lprim(crate::lambda::PrimInfo {
                primitive: Primitive::Paddint,
                args,
                ..
            }) if matches!(
                args.as_slice(),
                [
                    Lambda::Lprim(crate::lambda::PrimInfo {
                        primitive: Primitive::Paddint,
                        args: inner_args,
                        ..
                    }),
                    Lambda::Lvar(last),
                ] if last.same(&z)
                    && matches!(
                        inner_args.as_slice(),
                        [
                            Lambda::Lconst(Constant::Int { i: 1, .. }),
                            Lambda::Lvar(middle),
                        ] if middle.same(&y)
                    )
            )
        ));
        assert_eq!(apply.ap_args.len(), 2);
    }

    #[test]
    fn beta_reduces_let_wrapped_returned_functions_across_backend_alias_passes() {
        let x = Ident::create_local("x");
        let y = Ident::create_local("y");
        let u = Ident::create_local("u");
        let z = Ident::create_local("z");

        let lambda = Lambda::Lapply(Apply {
            ap_func: Box::new(Lambda::Lapply(Apply {
                ap_func: Box::new(Lambda::function_(
                    2,
                    vec![x.clone(), y.clone()],
                    Lambda::let_(
                        LetKind::Strict,
                        u.clone(),
                        Lambda::prim(
                            Primitive::Paddint,
                            vec![Lambda::var(x), Lambda::var(y)],
                            Location::none(),
                        ),
                        Lambda::function_(
                            1,
                            vec![z.clone()],
                            Lambda::prim(
                                Primitive::Paddint,
                                vec![Lambda::var(u.clone()), Lambda::var(z.clone())],
                                Location::none(),
                            ),
                            FunctionAttribute::default(),
                        ),
                    ),
                    FunctionAttribute::default(),
                )),
                ap_args: vec![Lambda::const_(Constant::int(3)), Lambda::const_(Constant::int(5))],
                ap_info: crate::lambda::ApInfo {
                    loc: Location::none(),
                    inlined: InlineAttribute::Default,
                    status: ApplyStatus::Uncurry,
                },
                ap_transformed_jsx: false,
            })),
            ap_args: vec![Lambda::const_(Constant::int(6))],
            ap_info: crate::lambda::ApInfo {
                loc: Location::none(),
                inlined: InlineAttribute::Default,
                status: ApplyStatus::Uncurry,
            },
            ap_transformed_jsx: false,
        });

        let simplified = simplify_for_js_backend(&lambda);
        let Lambda::Lapply(apply) = simplified else {
            panic!("expected the outer apply to remain after one backend beta-reduction sweep");
        };
        let Lambda::Llet(kind, bound, value, body) = *apply.ap_func else {
            panic!("expected the simplified callee to stay let-wrapped");
        };

        assert_eq!(kind, LetKind::StrictOpt);
        assert!(bound.same(&u));
        assert!(!matches!(*value, Lambda::Lapply(_)));
        assert!(matches!(*body, Lambda::Lfunction(_)));
        assert_eq!(apply.ap_args.len(), 1);
    }

    #[test]
    fn beta_reduces_returned_pjs_fn_make_wrappers_across_backend_alias_passes() {
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
            h.clone(),
            Lambda::const_(Constant::JsTrue),
            Lambda::prim(
                Primitive::PjsFnMake(1),
                vec![Lambda::function_(
                    1,
                    vec![x.clone()],
                    Lambda::let_(
                        LetKind::Strict,
                        j.clone(),
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
                                vec![f.clone()],
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
        let Lambda::Lapply(apply) = simplified else {
            panic!("expected the outer call to survive the final backend simplification sweep");
        };
        let Lambda::Llet(kind, bound, value, body) = apply.ap_func.as_ref() else {
            panic!("expected the surviving callee to stay let-wrapped, got {apply:?}");
        };

        assert_eq!(*kind, LetKind::Strict);
        assert!(bound.same(&x));
        assert!(matches!(
            value.as_ref(),
            Lambda::Lconst(Constant::String {
                s,
                delim: Some(crate::lambda::constant::StringDelim::StarJ),
            }) if s.is_empty()
        ));
        assert!(matches!(body.as_ref(), Lambda::Lfunction(_)));
        assert_eq!(apply.ap_args.len(), 1);
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

    #[test]
    fn inlines_named_functor_applications_even_when_inline_heuristics_reject_them() {
        let make = Ident::create_local("Make");
        let module_param = Ident::create_local("U");
        let belt_list = Ident::create_persistent("Belt_List");

        let simplified = simplify_for_js_backend(&Lambda::let_(
            LetKind::Strict,
            make.clone(),
            Lambda::function_(
                1,
                vec![module_param.clone()],
                Lambda::var(module_param),
                FunctionAttribute {
                    inline: InlineAttribute::Never,
                    is_a_functor: true,
                    ..FunctionAttribute::default()
                },
            ),
            Lambda::Lapply(Apply {
                ap_func: Box::new(Lambda::var(make)),
                ap_args: vec![Lambda::global_module(belt_list.clone(), false)],
                ap_info: ApInfo {
                    loc: Location::none(),
                    inlined: InlineAttribute::Default,
                    status: ApplyStatus::Na,
                },
                ap_transformed_jsx: false,
            }),
        ));

        let Lambda::LglobalModule(id, dynamic_import) = simplified else {
            panic!("expected named functor application to inline to the module argument");
        };
        assert!(id.same(&belt_list));
        assert!(!dynamic_import);
    }

    #[test]
    fn reruns_js_backend_simplify_after_functor_inlining_exposes_projected_module_fields() {
        let functor_id = Ident::create_local("F");
        let x_param = Ident::create_local("X");
        let y_param = Ident::create_local("Y");
        let cow_id = Ident::create_local("cow");
        let sheep_id = Ident::create_local("sheep");
        let identity_param = Ident::create_local("x");
        let arg0 = Ident::create_local("funarg");
        let arg1 = Ident::create_local("funarg$1");
        let first_apply = Ident::create_local("let");
        let second_apply = Ident::create_local("let");
        let loc = Location::none();

        let functor_attr = FunctionAttribute {
            is_a_functor: true,
            ..FunctionAttribute::default()
        };

        let identity_fn = || {
            Lambda::function_(
                1,
                vec![identity_param.clone()],
                Lambda::var(identity_param.clone()),
                FunctionAttribute::default(),
            )
        };

        let lambda = Lambda::let_(
            LetKind::Strict,
            functor_id.clone(),
            Lambda::function_(
                1,
                vec![x_param],
                Lambda::function_(
                    1,
                    vec![y_param],
                    Lambda::let_(
                        LetKind::Strict,
                        cow_id.clone(),
                        identity_fn(),
                        Lambda::let_(
                            LetKind::Strict,
                            sheep_id.clone(),
                            identity_fn(),
                            Lambda::prim(
                                Primitive::Pmakeblock(
                                    0,
                                    TagInfo::module(vec!["cow".to_string(), "sheep".to_string()]),
                                    Mutable::Immutable,
                                ),
                                vec![Lambda::var(cow_id.clone()), Lambda::var(sheep_id.clone())],
                                loc.clone(),
                            ),
                        ),
                    ),
                    functor_attr.clone(),
                ),
                functor_attr.clone(),
            ),
            Lambda::function_(
                1,
                vec![arg0.clone()],
                Lambda::let_(
                    LetKind::Strict,
                    first_apply.clone(),
                    Lambda::Lapply(Apply {
                        ap_func: Box::new(Lambda::var(functor_id)),
                        ap_args: vec![Lambda::prim(
                            Primitive::Pmakeblock(
                                0,
                                TagInfo::module(vec!["foo".to_string()]),
                                Mutable::Immutable,
                            ),
                            vec![Lambda::prim(
                                Primitive::Pfield(
                                    1,
                                    FieldDbgInfo::Module {
                                        name: "foo".to_string(),
                                    },
                                ),
                                vec![Lambda::var(arg0)],
                                loc.clone(),
                            )],
                            loc.clone(),
                        )],
                        ap_info: ApInfo {
                            loc: loc.clone(),
                            inlined: InlineAttribute::Default,
                            status: ApplyStatus::Na,
                        },
                        ap_transformed_jsx: false,
                    }),
                    Lambda::function_(
                        1,
                        vec![arg1.clone()],
                        Lambda::let_(
                            LetKind::Strict,
                            second_apply.clone(),
                            Lambda::Lapply(Apply {
                                ap_func: Box::new(Lambda::var(first_apply.clone())),
                                ap_args: vec![Lambda::prim(
                                    Primitive::Pmakeblock(
                                        0,
                                        TagInfo::module(vec!["foo".to_string()]),
                                        Mutable::Immutable,
                                    ),
                                    vec![Lambda::prim(
                                        Primitive::Pfield(
                                            1,
                                            FieldDbgInfo::Module {
                                                name: "foo".to_string(),
                                            },
                                        ),
                                        vec![Lambda::var(arg1)],
                                        loc.clone(),
                                    )],
                                    loc.clone(),
                                )],
                                ap_info: ApInfo {
                                    loc: loc.clone(),
                                    inlined: InlineAttribute::Default,
                                    status: ApplyStatus::Na,
                                },
                                ap_transformed_jsx: false,
                            }),
                            Lambda::prim(
                                Primitive::Pmakeblock(
                                    0,
                                    TagInfo::module(vec!["sheep".to_string()]),
                                    Mutable::Immutable,
                                ),
                                vec![Lambda::prim(
                                    Primitive::Pfield(
                                        1,
                                        FieldDbgInfo::Module {
                                            name: "sheep".to_string(),
                                        },
                                    ),
                                    vec![Lambda::var(second_apply.clone())],
                                    loc,
                                )],
                                Location::none(),
                            ),
                        ),
                        functor_attr.clone(),
                    ),
                ),
                functor_attr,
            ),
        );

        let simplified = simplify_for_js_backend(&lambda);
        assert!(
            !super::lambda_hits_variable(&first_apply, &simplified),
            "the first functor application should inline away"
        );
        assert!(
            !super::lambda_hits_variable(&second_apply, &simplified),
            "the second functor application should flatten before field projection"
        );

        let outer_functor = match simplified {
            Lambda::Lfunction(func) => func,
            Lambda::Llet(_, _, _, body) => match *body {
                Lambda::Lfunction(func) => func,
                other => panic!("expected the simplified outer lambda function, got {other:?}"),
            },
            other => panic!("expected the simplified outer lambda function, got {other:?}"),
        };
        let Lambda::Lfunction(inner_functor) = *outer_functor.body else {
            panic!("expected the outer functor to return the projected inner function");
        };
        let (kept_sheep, final_block) = match *inner_functor.body {
            Lambda::Llet(_, first_id, _, sheep_binding) => match *sheep_binding {
                Lambda::Lprim(crate::lambda::PrimInfo {
                    primitive: Primitive::Pmakeblock(_, TagInfo::Module(_), _),
                    ..
                }) => (first_id, sheep_binding),
                Lambda::Llet(_, kept_sheep, _, final_block) => (kept_sheep, final_block),
                other => panic!("expected the projected sheep binding, got {other:?}"),
            },
            other => panic!(
                "expected the inner functor body to end in lets plus a module block, got {other:?}"
            ),
        };
        let Lambda::Lprim(crate::lambda::PrimInfo {
            primitive: Primitive::Pmakeblock(_, TagInfo::Module(fields), _),
            args,
            ..
        }) = *final_block
        else {
            panic!("expected the simplified inner function to finish with a module block");
        };
        assert_eq!(fields, vec!["sheep".to_string()]);
        assert!(matches!(args.as_slice(), [Lambda::Lvar(id)] if id.same(&kept_sheep)));
    }

    #[test]
    fn folds_constant_subint_loop_finish_before_for_range_lowering_like_ocaml() {
        let loop_var = Ident::create_local("i");
        let limit = Ident::create_local("limit");
        let lambda = Lambda::let_(
            LetKind::Strict,
            limit.clone(),
            Lambda::const_(Constant::int(10)),
            Lambda::for_(
                loop_var.clone(),
                Lambda::const_(Constant::int(0)),
                Lambda::prim(
                    Primitive::Psubint,
                    vec![Lambda::var(limit), Lambda::const_(Constant::int(1))],
                    Location::none(),
                ),
                DirectionFlag::Upto,
                Lambda::unit(),
            ),
        );

        let simplified = simplify_for_js_backend(&lambda);
        let Lambda::Lfor(loop_ident, start, finish, direction, body) = simplified else {
            panic!("expected simplified for-loop, got {simplified:?}");
        };

        assert!(loop_ident.same(&loop_var));
        assert_eq!(direction, DirectionFlag::Upto);
        assert!(matches!(
            start.as_ref(),
            Lambda::Lconst(Constant::Int { i: 0, .. })
        ));
        assert!(matches!(
            finish.as_ref(),
            Lambda::Lconst(Constant::Int { i: 9, .. })
        ));
        assert!(matches!(
            body.as_ref(),
            Lambda::Lconst(Constant::JsUndefined { .. })
        ));
    }
}
