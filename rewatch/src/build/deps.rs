use super::build_types::*;
use super::packages;
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

fn get_dep_modules_from_memory(
    deps: &Dependencies,
    ctx: &DepContext,
    valid_modules: &AHashSet<String>,
    package: &packages::Package,
    build_state: &BuildState,
) -> AHashSet<String> {
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
    // Nothing to resolve again: every module's dependencies are known and
    // the set of modules they resolve against is the same.
    if build_state.deps_initialized
        && deleted_modules.is_empty()
        && !build_state.modules.values().any(|module| module.deps_dirty)
    {
        return;
    }
    let with_deleted: AHashSet<String>;
    let all_mod = if deleted_modules.is_empty() {
        &build_state.module_names
    } else {
        with_deleted = build_state.module_names.union(deleted_modules).cloned().collect();
        &with_deleted
    };
    // Borrowed under the lock: nothing the resolution below runs takes it.
    let in_memory_deps_guard = build_state.in_memory_deps.lock().unwrap();
    let in_memory_deps: &AHashMap<String, Dependencies> = &in_memory_deps_guard;
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
    let resolved = build_state
        .modules
        .par_iter()
        .filter_map(|(module_name, module)| match &module.source_type {
            SourceType::MlMap(_) => None,
            SourceType::SourceFile(source_file) => {
                let package = build_state
                    .get_package(&module.package_name)
                    .expect("Package not found");
                if module.deps_dirty || !build_state.deps_initialized {
                    let ctx = DepContext {
                        namespace: package.namespace.to_suffix(),
                        package_modules: package.modules.as_ref().unwrap(),
                        allowed_dependencies: &allowed_dependencies[module.package_name.as_str()],
                    };
                    let deps_for = |key: &str, kind: &str| {
                        let stored = in_memory_deps
                            .get(key)
                            .unwrap_or_else(|| panic!("missing stored {kind} deps for {module_name}"));
                        get_dep_modules_from_memory(stored, &ctx, all_mod, package, build_state)
                    };
                    let mut deps = deps_for(&format!("{module_name}:impl"), "implementation");
                    if source_file.interface.is_some() {
                        deps.extend(deps_for(&format!("{module_name}:intf"), "interface"));
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
                    Some((module_name.to_string(), deps))
                } else {
                    None
                }
            }
        })
        .collect::<Vec<(String, AHashSet<String>)>>();
    drop(in_memory_deps_guard);
    let mut changed = !build_state.deps_initialized;
    for (module_name, deps) in resolved {
        if let Some(module) = build_state.modules.get_mut(&module_name) {
            changed |= module.deps != deps;
            module.deps = deps;
        }
    }
    for module in build_state.modules.values_mut() {
        module.deps_dirty = false;
    }
    if changed {
        rebuild_dependents(&mut build_state.modules);
    }
    build_state.deps_initialized = true;
}

#[cfg(test)]
mod tests {
    use super::*;

    fn module(deps: &[&str], dependents: &[&str]) -> Module {
        Module {
            source_type: SourceType::MlMap(MlMap { parse_dirty: false }),
            deps: deps.iter().map(|dep| (*dep).to_string()).collect(),
            dependents: dependents.iter().map(|dep| (*dep).to_string()).collect(),
            package_name: "test".to_string(),
            compile_dirty: false,
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
