// Port of compiler/gentype/Dependencies.ml:1-73.

use crate::types::path::PathView;
use crate::gentype::gen_type_common::{Dep, dep_to_string};
use crate::types::Path;

pub fn handle_namespace(name: &str, dep: &Dep) -> Dep {
    match dep {
        Dep::External(_) | Dep::Internal(_) => dep.clone(),
        Dep::Dot(dep1, module_name) => match dep1.as_ref() {
            Dep::External(s) if s == name => Dep::External(module_name.clone()),
            _ => Dep::Dot(Box::new(handle_namespace(name, dep1)), module_name.clone()),
        },
    }
}

pub fn from_path1(
    config: &crate::gentype::config::T,
    type_env: &crate::gentype::type_env::T,
    path: &Path,
) -> (crate::gentype::type_env::T, Dep) {
    let stripped_path = crate::gentype::type_env::strip_current_module_prefix(path, type_env);
    let path = stripped_path.as_ref().unwrap_or(path);

    match path.view() {
        PathView::Pident(id) => {
            let name = id.name();
            match crate::gentype::type_env::lookup(name, type_env) {
                None => (type_env.clone(), Dep::External(name.to_string())),
                Some(type_env1) => {
                    let type_env2 = match crate::gentype::type_env::get_module(name, type_env) {
                        Some(type_env2) => type_env2,
                        None => type_env1.clone(),
                    };
                    match crate::gentype::type_env::expand_alias_to_external_module(
                        name, &type_env1,
                    ) {
                        Some(dep) => (type_env2, dep),
                        None => {
                            let resolved_name =
                                crate::gentype::type_env::add_module_path(&type_env1, name);
                            (type_env2, Dep::Internal(resolved_name))
                        }
                    }
                }
            }
        }
        PathView::Pdot(p, s, _pos) if matches!(p.view(), PathView::Pident(id) if crate::gentype::gen_type_common::scoped_package::is_generated_module(id, config)) =>
        {
            let generated_module = match p.view() {
                PathView::Pident(id) => id,
                _ => unreachable!(),
            };
            (
                type_env.clone(),
                Dep::External(
                    crate::gentype::gen_type_common::scoped_package::add_generated_module(
                        s,
                        generated_module,
                    ),
                ),
            )
        }
        PathView::Pdot(p, s, _pos) => {
            let (type_env_from_p, dep) = from_path1(config, type_env, p);
            match crate::gentype::type_env::expand_alias_to_external_module(s, &type_env_from_p) {
                Some(dep) => (type_env_from_p, dep),
                None => (type_env_from_p, Dep::Dot(Box::new(dep), s.to_string())),
            }
        }
        PathView::Papply(_, _) => (
            type_env.clone(),
            Dep::Internal(crate::gentype::resolved_name::from_string(
                "__Papply_unsupported_genType__",
            )),
        ),
    }
}

pub fn is_internal(dep: &Dep) -> bool {
    match dep {
        Dep::External(_) => false,
        Dep::Internal(_) => true,
        Dep::Dot(d, _) => is_internal(d),
    }
}

pub fn from_path(
    config: &crate::gentype::config::T,
    type_env: &crate::gentype::type_env::T,
    path: &Path,
) -> Dep {
    let (_, dep) = from_path1(config, type_env, path);
    if crate::gentype::debug::type_resolution.load(std::sync::atomic::Ordering::Relaxed) {
        crate::gentype::log_::item(&format!(
            "fromPath path:{} typeEnv:{} {} resolved:{}\n",
            path.name(),
            crate::gentype::type_env::to_string(type_env),
            match is_internal(&dep) {
                true => "Internal",
                false => "External",
            },
            dep_to_string(&dep)
        ));
    }
    match &config.namespace {
        None => dep,
        Some(name) => handle_namespace(name, &dep),
    }
}

pub fn get_outer_module_name(dep: &Dep) -> crate::gentype::module_name::T {
    match dep {
        Dep::External(name) => crate::gentype::module_name::from_string_unsafe(name),
        Dep::Internal(resolved_name) => crate::gentype::module_name::from_string_unsafe(
            &crate::gentype::resolved_name::to_string(resolved_name),
        ),
        Dep::Dot(dep1, _) => get_outer_module_name(dep1),
    }
}

pub fn remove_external_outer_module(dep: &Dep) -> Dep {
    match dep {
        Dep::External(_) | Dep::Internal(_) => dep.clone(),
        Dep::Dot(dep1, s) => match dep1.as_ref() {
            Dep::External(_) => Dep::External(s.clone()),
            _ => Dep::Dot(Box::new(remove_external_outer_module(dep1)), s.clone()),
        },
    }
}
