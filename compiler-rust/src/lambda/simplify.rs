//! Small post-lowering lambda simplifications used on the JS backend path.

use std::collections::{HashMap, HashSet};

use crate::ident::Ident;
use crate::lambda::analysis;
use crate::lambda::beta_reduce;
use crate::lambda::compat::{FieldDbgInfo, LetKind};
use crate::lambda::constant::Constant;
use crate::lambda::free_variables::free_variables;
use crate::lambda::primitive::Primitive;
use crate::lambda::{Apply, LFunction, Lambda, LambdaSwitch, TagInfo};

#[derive(Clone, Default)]
struct SimplifyEnv {
    functions: HashMap<Ident, LFunction>,
    substitutions: HashMap<Ident, Lambda>,
}

impl SimplifyEnv {
    fn without_ident(&self, id: &Ident) -> Self {
        let mut next = self.clone();
        next.functions.remove(id);
        next.substitutions.remove(id);
        next
    }

    fn without_idents<'a>(&self, ids: impl IntoIterator<Item = &'a Ident>) -> Self {
        let mut next = self.clone();
        for id in ids {
            next.functions.remove(id);
            next.substitutions.remove(id);
        }
        next
    }
}

/// Simplify lowered lambda before JS IR lowering.
pub fn simplify_for_js_backend(lam: &Lambda) -> Lambda {
    let exports = collect_exported_idents(lam);
    simplify_with_env(lam, &SimplifyEnv::default(), &exports)
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
            if let Some(substitution) = substitution_candidate(&value) {
                body_env.substitutions.insert(id.clone(), substitution);
            }
            if *kind != LetKind::Variable {
                if let Lambda::Lfunction(func) = &value {
                    if analysis::lfunction_can_be_inlined(func) {
                        body_env.functions.insert(id.clone(), func.clone());
                    }
                }
            }
            let body = simplify_with_env(body, &body_env, exports);
            if !exports.contains(id) && !free_variables(&body).contains(id) {
                if analysis::no_side_effects(&value) {
                    body
                } else {
                    Lambda::seq(value, body)
                }
            } else {
                Lambda::let_(*kind, id.clone(), value, body)
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
        Lambda::LifThenElse(cond, then_, else_) => Lambda::if_(
            simplify_with_env(cond, env, exports),
            simplify_with_env(then_, env, exports),
            simplify_with_env(else_, env, exports),
        ),
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

fn simplify_primitive(
    info: &crate::lambda::PrimInfo,
    env: &SimplifyEnv,
    exports: &HashSet<Ident>,
) -> Lambda {
    let args: Vec<_> = info
        .args
        .iter()
        .map(|arg| simplify_with_env(arg, env, exports))
        .collect();

    match (&info.primitive, args.as_slice()) {
        (
            Primitive::Pstringadd,
            [
                Lambda::Lconst(Constant::String { s: left, delim: left_delim }),
                Lambda::Lconst(Constant::String { s: right, delim: right_delim }),
            ],
        ) => Lambda::const_(Constant::String {
            s: format!("{left}{right}"),
            delim: left_delim.clone().or(right_delim.clone()),
        }),
        _ => Lambda::prim(info.primitive.clone(), args, info.loc.clone()),
    }
}

fn simplify_apply(apply: &Apply, env: &SimplifyEnv, exports: &HashSet<Ident>) -> Lambda {
    let args: Vec<_> = apply
        .ap_args
        .iter()
        .map(|arg| simplify_with_env(arg, env, exports))
        .collect();

    if let Lambda::Lvar(id) = &*apply.ap_func {
        if let Some(func) = env.functions.get(id) {
            if should_inline_function(func, &args) {
                let reduced = beta_reduce::no_names_beta_reduce(&func.params, &func.body, &args);
                return simplify_with_env(&reduced, env, exports);
            }
        }
    }

    let func = simplify_with_env(&apply.ap_func, env, exports);
    if let Lambda::Lfunction(inline_func) = &func {
        if should_inline_function(inline_func, &args) {
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

fn should_inline_function(func: &LFunction, args: &[Lambda]) -> bool {
    func.params.len() == args.len()
        && analysis::lfunction_can_be_inlined(func)
        && analysis::ok_to_inline_fun_when_app(func, args)
}

fn substitution_candidate(value: &Lambda) -> Option<Lambda> {
    match value {
        Lambda::Lvar(_) | Lambda::Lconst(_) | Lambda::LglobalModule(_, _) => Some(value.clone()),
        Lambda::Lprim(info)
            if matches!(
                (&info.primitive, info.args.as_slice()),
                (
                    Primitive::Pfield(_, FieldDbgInfo::Module { .. }),
                    [Lambda::LglobalModule(_, _)]
                )
            ) =>
        {
            Some(value.clone())
        }
        _ => None,
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
    use crate::lambda::compat::LetKind;
    use crate::lambda::constant::Constant;
    use crate::lambda::primitive::{ExternalArgAttr, ExternalObjLabel, ExternalObjSpec, Mutable, Primitive};
    use crate::lambda::{ApInfo, Apply, FunctionAttribute, InlineAttribute, Lambda, TagInfo};
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
                        vec![
                            Lambda::var(a1),
                            Lambda::const_(Constant::string("world")),
                        ],
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
}
