//! Small post-lowering lambda simplifications used on the JS backend path.

use std::collections::HashMap;

use crate::ident::Ident;
use crate::lambda::analysis;
use crate::lambda::beta_reduce;
use crate::lambda::compat::LetKind;
use crate::lambda::free_variables::free_variables;
use crate::lambda::{Apply, LFunction, Lambda, LambdaSwitch};

#[derive(Clone, Default)]
struct SimplifyEnv {
    functions: HashMap<Ident, LFunction>,
}

impl SimplifyEnv {
    fn without_ident(&self, id: &Ident) -> Self {
        let mut next = self.clone();
        next.functions.remove(id);
        next
    }

    fn without_idents<'a>(&self, ids: impl IntoIterator<Item = &'a Ident>) -> Self {
        let mut next = self.clone();
        for id in ids {
            next.functions.remove(id);
        }
        next
    }
}

/// Simplify lowered lambda before JS IR lowering.
pub fn simplify_for_js_backend(lam: &Lambda) -> Lambda {
    simplify_with_env(lam, &SimplifyEnv::default())
}

fn simplify_with_env(lam: &Lambda, env: &SimplifyEnv) -> Lambda {
    match lam {
        Lambda::Lvar(_) | Lambda::LglobalModule(_, _) | Lambda::Lconst(_) => lam.clone(),
        Lambda::Lapply(apply) => simplify_apply(apply, env),
        Lambda::Lfunction(func) => {
            let body_env = env.without_idents(func.params.iter());
            Lambda::function_(
                func.arity,
                func.params.clone(),
                simplify_with_env(&func.body, &body_env),
                func.attr.clone(),
            )
        }
        Lambda::Llet(kind, id, value, body) => {
            let value = simplify_with_env(value, env);
            let mut body_env = env.without_ident(id);
            if *kind != LetKind::Variable {
                if let Lambda::Lfunction(func) = &value {
                    if analysis::lfunction_can_be_inlined(func) {
                        body_env.functions.insert(id.clone(), func.clone());
                    }
                }
            }
            let body = simplify_with_env(body, &body_env);
            if !free_variables(&body).contains(id) {
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
                .map(|(id, expr)| (id.clone(), simplify_with_env(expr, &scoped_env)))
                .collect();
            let body = simplify_with_env(body, &scoped_env);
            Lambda::letrec(bindings, body)
        }
        Lambda::Lprim(info) => Lambda::prim(
            info.primitive.clone(),
            info.args
                .iter()
                .map(|arg| simplify_with_env(arg, env))
                .collect(),
            info.loc.clone(),
        ),
        Lambda::Lswitch(scrutinee, switch) => Lambda::Lswitch(
            Box::new(simplify_with_env(scrutinee, env)),
            LambdaSwitch {
                sw_consts_full: switch.sw_consts_full,
                sw_consts: switch
                    .sw_consts
                    .iter()
                    .map(|(tag, lam)| (*tag, simplify_with_env(lam, env)))
                    .collect(),
                sw_blocks_full: switch.sw_blocks_full,
                sw_blocks: switch
                    .sw_blocks
                    .iter()
                    .map(|(tag, lam)| (*tag, simplify_with_env(lam, env)))
                    .collect(),
                sw_failaction: switch
                    .sw_failaction
                    .as_ref()
                    .map(|lam| Box::new(simplify_with_env(lam, env))),
                sw_names: switch.sw_names.clone(),
            },
        ),
        Lambda::LstringSwitch(scrutinee, cases, default) => Lambda::LstringSwitch(
            Box::new(simplify_with_env(scrutinee, env)),
            cases
                .iter()
                .map(|(tag, lam)| (tag.clone(), simplify_with_env(lam, env)))
                .collect(),
            default
                .as_ref()
                .map(|lam| Box::new(simplify_with_env(lam, env))),
        ),
        Lambda::LstaticRaise(id, args) => Lambda::LstaticRaise(
            *id,
            args.iter().map(|arg| simplify_with_env(arg, env)).collect(),
        ),
        Lambda::LstaticCatch(body, (id, vars), handler) => {
            let scoped_env = env.without_idents(vars.iter());
            Lambda::LstaticCatch(
                Box::new(simplify_with_env(body, env)),
                (*id, vars.clone()),
                Box::new(simplify_with_env(handler, &scoped_env)),
            )
        }
        Lambda::LtryWith(body, exn, handler) => {
            let scoped_env = env.without_ident(exn);
            Lambda::LtryWith(
                Box::new(simplify_with_env(body, env)),
                exn.clone(),
                Box::new(simplify_with_env(handler, &scoped_env)),
            )
        }
        Lambda::LifThenElse(cond, then_, else_) => Lambda::if_(
            simplify_with_env(cond, env),
            simplify_with_env(then_, env),
            simplify_with_env(else_, env),
        ),
        Lambda::Lsequence(first, second) => Lambda::seq(
            simplify_with_env(first, env),
            simplify_with_env(second, env),
        ),
        Lambda::Lwhile(cond, body) => Lambda::Lwhile(
            Box::new(simplify_with_env(cond, env)),
            Box::new(simplify_with_env(body, env)),
        ),
        Lambda::Lfor(id, from, to, direction, body) => {
            let scoped_env = env.without_ident(id);
            Lambda::Lfor(
                id.clone(),
                Box::new(simplify_with_env(from, env)),
                Box::new(simplify_with_env(to, env)),
                *direction,
                Box::new(simplify_with_env(body, &scoped_env)),
            )
        }
        Lambda::Lassign(id, value) => {
            Lambda::Lassign(id.clone(), Box::new(simplify_with_env(value, env)))
        }
    }
}

fn simplify_apply(apply: &Apply, env: &SimplifyEnv) -> Lambda {
    let args: Vec<_> = apply
        .ap_args
        .iter()
        .map(|arg| simplify_with_env(arg, env))
        .collect();

    if let Lambda::Lvar(id) = &*apply.ap_func {
        if let Some(func) = env.functions.get(id) {
            if should_inline_function(func, &args) {
                let reduced = beta_reduce::no_names_beta_reduce(&func.params, &func.body, &args);
                return simplify_with_env(&reduced, env);
            }
        }
    }

    let func = simplify_with_env(&apply.ap_func, env);
    if let Lambda::Lfunction(inline_func) = &func {
        if should_inline_function(inline_func, &args) {
            let reduced =
                beta_reduce::no_names_beta_reduce(&inline_func.params, &inline_func.body, &args);
            return simplify_with_env(&reduced, env);
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

#[cfg(test)]
mod tests {
    use crate::ident::Ident;
    use crate::lambda::compat::LetKind;
    use crate::lambda::constant::Constant;
    use crate::lambda::primitive::{ExternalArgAttr, ExternalObjLabel, ExternalObjSpec, Primitive};
    use crate::lambda::{ApInfo, Apply, FunctionAttribute, InlineAttribute, Lambda};
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
}
