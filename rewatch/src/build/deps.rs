use super::build_types::*;
use super::packages;
use crate::helpers;
use ahash::{AHashMap, AHashSet};
use rayon::prelude::*;
use rescript_compiler::binary_ast::Dependencies;

/// What resolving a module's raw dependency names needs from its package.
struct DepContext<'a> {
    namespace: Option<String>,
    package_modules: &'a AHashSet<String>,
    /// The packages this package may depend on (dependencies and dev
    /// dependencies).
    allowed_dependencies: &'a AHashSet<String>,
}

fn resolve_dep_modules<'a>(
    raw_deps: impl Iterator<Item = &'a String>,
    ctx: &DepContext,
    valid_modules: &AHashSet<String>,
    package: &packages::Package,
    build_state: &BuildState,
) -> AHashSet<String> {
    let namespace = ctx.namespace.as_deref();
    raw_deps
        .map(|dep| {
            let (dep_first, dep_second) = match dep.split_once('.') {
                Some((first, rest)) => (first, Some(rest.split('.').next().unwrap_or(rest))),
                None => (dep.as_str(), None),
            };
            match namespace {
                Some(namespace) => {
                    // if the module is in the own namespace, take the submodule -- so:
                    // if the module is TeamwalnutApp.MyModule inside of the namespace TeamwalnutApp
                    // we need the dependency to be MyModule in the same namespace
                    let dep = match dep_second {
                        Some(dep_second) if dep_first == namespace => dep_second,
                        _ => dep_first,
                    };
                    let namespaced_name = dep.to_owned() + "-" + namespace;
                    if ctx.package_modules.contains(&namespaced_name)
                        || valid_modules.contains(&namespaced_name)
                    {
                        namespaced_name
                    } else {
                        dep.to_string()
                    }
                }
                None => dep_first.to_string(),
            }
        })
        .filter(|dep| {
            // First check if the module exists
            let module_exists = valid_modules.contains(dep) && Some(dep.as_str()) != namespace;

            if !module_exists {
                return false;
            }

            if let Some(dep_module) = build_state.modules.get(dep) {
                // If the module exists, check if it's in the same package (always allowed)
                if dep_module.package_name == package.name {
                    return true;
                }

                // If it's in a different package, check if that package is a declared dependency
                return ctx.allowed_dependencies.contains(&dep_module.package_name);
            }

            true
        })
        .collect::<AHashSet<String>>()
}

fn get_dep_modules(
    ast_file: &str,
    ctx: &DepContext,
    valid_modules: &AHashSet<String>,
    package: &packages::Package,
    build_state: &BuildState,
) -> AHashSet<String> {
    let mut deps = Dependencies::new();
    let ast_file = package.get_build_path().join(ast_file);
    match helpers::read_lines(&ast_file) {
        Ok(lines) => {
            // we skip the first line with is some null characters
            // the following lines in the AST are the dependency modules
            // we stop when we hit a line that is an absolute path, this is the path of the file.
            // this is the point where the dependencies end and the actual AST starts
            for line in lines.skip(1).flatten() {
                let line = line.trim().to_string();
                if std::path::Path::new(&line).is_absolute() {
                    break;
                } else if !line.is_empty() {
                    deps.insert(line);
                }
            }
        }
        _ => {
            panic!("Could not read file {}", ast_file.to_string_lossy());
        }
    }

    resolve_dep_modules(deps.iter(), ctx, valid_modules, package, build_state)
}

fn rebuild_dependents(modules: &mut ahash::AHashMap<String, Module>) {
    for module in modules.values_mut() {
        module.dependents.clear();
    }

    let edges = modules
        .iter()
        .flat_map(|(module_name, module)| {
            module
                .deps
                .iter()
                .map(move |dependency| (dependency.clone(), module_name.clone()))
        })
        .collect::<Vec<_>>();

    for (dependency, dependent) in edges {
        if let Some(module) = modules.get_mut(&dependency) {
            module.dependents.insert(dependent);
        }
    }
}

pub fn get_deps(build_state: &mut BuildCommandState, deleted_modules: &AHashSet<String>) {
    let all_mod = &build_state.module_names.union(deleted_modules).cloned().collect();
    let in_process_mode = build_state.build_mode().is_in_process();
    let in_memory_deps = in_process_mode.then(|| build_state.snapshot_in_memory_deps());
    let allowed_dependencies: AHashMap<&str, AHashSet<String>> = build_state
        .packages
        .iter()
        .map(|(name, package)| {
            let allowed = package
                .config
                .get_dependency_names()
                .into_iter()
                .chain(package.config.get_dev_dependency_names())
                .collect();
            (name.as_str(), allowed)
        })
        .collect();
    build_state
        .modules
        .par_iter()
        .map(|(module_name, module)| match &module.source_type {
            SourceType::MlMap(_) => (module_name.to_string(), module.deps.to_owned()),
            SourceType::SourceFile(source_file) => {
                let package = build_state
                    .get_package(&module.package_name)
                    .expect("Package not found");
                let ast_path = helpers::get_ast_path(&source_file.implementation.path);
                if module.deps_dirty || !build_state.deps_initialized {
                    let ctx = DepContext {
                        namespace: package.namespace.to_suffix(),
                        package_modules: package.modules.as_ref().unwrap(),
                        allowed_dependencies: &allowed_dependencies[module.package_name.as_str()],
                    };
                    let impl_key = format!("{module_name}:impl");
                    let mut deps = if in_process_mode {
                        in_memory_deps
                            .as_ref()
                            .and_then(|deps| deps.get(&impl_key))
                            .map(|in_memory_dep| {
                                resolve_dep_modules(in_memory_dep.iter(), &ctx, all_mod, package, build_state)
                            })
                            .unwrap_or_else(|| {
                                panic!(
                                    "in-process invariant violated: missing stored implementation deps for {module_name}; refusing to read {} from disk",
                                    ast_path.display()
                                )
                            })
                    } else {
                        get_dep_modules(&ast_path.to_string_lossy(), &ctx, all_mod, package, build_state)
                    };

                    if let Some(interface) = &source_file.interface {
                        let iast_path = helpers::get_ast_path(&interface.path);

                        let intf_key = format!("{module_name}:intf");
                        let intf_deps = if in_process_mode {
                            in_memory_deps
                                .as_ref()
                                .and_then(|deps| deps.get(&intf_key))
                                .map(|in_memory_dep| {
                                    resolve_dep_modules(in_memory_dep.iter(), &ctx, all_mod, package, build_state)
                                })
                                .unwrap_or_else(|| {
                                    panic!(
                                        "in-process invariant violated: missing stored interface deps for {module_name}; refusing to read {} from disk",
                                        iast_path.display()
                                    )
                                })
                        } else {
                            get_dep_modules(&iast_path.to_string_lossy(), &ctx, all_mod, package, build_state)
                        };
                        deps.extend(intf_deps)
                    }
                    match &package.namespace {
                        packages::Namespace::NamespaceWithEntry { namespace: _, entry }
                            if entry == module_name =>
                        {
                            deps.insert(package.namespace.to_suffix().unwrap());
                        }
                        _ => (),
                    }
                    deps.remove(module_name);
                    (module_name.to_string(), deps)
                } else {
                    (module_name.to_string(), module.deps.to_owned())
                }
            }
        })
        .collect::<Vec<(String, AHashSet<String>)>>()
        .into_iter()
        .for_each(|(module_name, deps)| {
            if let Some(module) = build_state.modules.get_mut(&module_name) {
                module.deps = deps;
                module.deps_dirty = false;
            }
        });
    rebuild_dependents(&mut build_state.modules);
    build_state.deps_initialized = true;
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::SystemTime;

    fn module(deps: &[&str], dependents: &[&str]) -> Module {
        Module {
            source_type: SourceType::MlMap(MlMap { parse_dirty: false }),
            deps: deps.iter().map(|dep| (*dep).to_string()).collect(),
            dependents: dependents.iter().map(|dep| (*dep).to_string()).collect(),
            package_name: "test".to_string(),
            compile_dirty: false,
            last_compiled_cmi: None,
            last_compiled_cmt: Some(SystemTime::UNIX_EPOCH),
            deps_dirty: false,
            is_type_dev: false,
        }
    }

    #[test]
    fn rebuilding_dependents_removes_stale_edges() {
        let mut modules = ahash::AHashMap::new();
        modules.insert("A".to_string(), module(&[], &["B"]));
        modules.insert("B".to_string(), module(&["C"], &[]));
        modules.insert("C".to_string(), module(&[], &[]));

        rebuild_dependents(&mut modules);

        assert!(modules["A"].dependents.is_empty());
        assert_eq!(modules["C"].dependents, AHashSet::from(["B".to_string()]));
    }
}
