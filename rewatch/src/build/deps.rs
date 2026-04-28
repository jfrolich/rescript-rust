use super::build_types::*;
use super::packages;
use crate::helpers;
use ahash::AHashSet;
use rayon::prelude::*;
use rescript_compiler::binary_ast::Dependencies;

fn resolve_dep_modules<'a>(
    raw_deps: impl Iterator<Item = &'a String>,
    namespace: Option<String>,
    package_modules: &AHashSet<String>,
    valid_modules: &AHashSet<String>,
    package: &packages::Package,
    build_state: &BuildState,
) -> AHashSet<String> {
    let deps = raw_deps.cloned().collect::<AHashSet<String>>();

    // Get the list of allowed dependency packages for this package
    let allowed_dependencies: AHashSet<String> = package
        .config
        .get_dependency_names()
        .into_iter()
        .chain(package.config.get_dev_dependency_names())
        .collect();

    deps.iter()
        .map(|dep| {
            let dep_first = dep.split('.').next().unwrap();
            let dep_second = dep.split('.').nth(1);
            match &namespace {
                Some(namespace) => {
                    // if the module is in the own namespace, take the submodule -- so:
                    // if the module is TeamwalnutApp.MyModule inside of the namespace TeamwalnutApp
                    // we need the dependency to be MyModule in the same namespace
                    let dep = match dep_second {
                        Some(dep_second) if dep_first == namespace => dep_second,
                        _ => dep_first,
                    };
                    let namespaced_name = dep.to_owned() + "-" + namespace;
                    if package_modules.contains(&namespaced_name) || valid_modules.contains(&namespaced_name)
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
            let module_exists = valid_modules.contains(dep)
                && match namespace.to_owned() {
                    Some(namespace) => !dep.eq(&namespace),
                    None => true,
                };

            if !module_exists {
                return false;
            }

            if let Some(dep_module) = build_state.modules.get(dep) {
                // If the module exists, check if it's in the same package (always allowed)
                if dep_module.package_name == package.name {
                    return true;
                }

                // If it's in a different package, check if that package is a declared dependency
                return allowed_dependencies.contains(&dep_module.package_name);
            }

            true
        })
        .collect::<AHashSet<String>>()
}

fn get_dep_modules(
    ast_file: &str,
    namespace: Option<String>,
    package_modules: &AHashSet<String>,
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

    resolve_dep_modules(
        deps.iter(),
        namespace,
        package_modules,
        valid_modules,
        package,
        build_state,
    )
}

fn get_dep_modules_from_memory(
    deps: &Dependencies,
    namespace: Option<String>,
    package_modules: &AHashSet<String>,
    valid_modules: &AHashSet<String>,
    package: &packages::Package,
    build_state: &BuildState,
) -> AHashSet<String> {
    resolve_dep_modules(
        deps.iter(),
        namespace,
        package_modules,
        valid_modules,
        package,
        build_state,
    )
}

pub fn get_deps(build_state: &mut BuildCommandState, deleted_modules: &AHashSet<String>) {
    let all_mod = &build_state.module_names.union(deleted_modules).cloned().collect();
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
                    let impl_key = format!("{module_name}:impl");
                    let mut deps = if build_state.build_mode().is_in_process() {
                        build_state
                            .get_in_memory_deps(&impl_key)
                            .map(|in_memory_deps| {
                                get_dep_modules_from_memory(
                                    &in_memory_deps,
                                    package.namespace.to_suffix(),
                                    package.modules.as_ref().unwrap(),
                                    all_mod,
                                    package,
                                    build_state,
                                )
                            })
                            .unwrap_or_else(|| {
                                panic!(
                                    "in-process invariant violated: missing stored implementation deps for {module_name}; refusing to read {} from disk",
                                    ast_path.display()
                                )
                            })
                    } else {
                        get_dep_modules(
                            &ast_path.to_string_lossy(),
                            package.namespace.to_suffix(),
                            package.modules.as_ref().unwrap(),
                            all_mod,
                            package,
                            build_state,
                        )
                    };

                    if let Some(interface) = &source_file.interface {
                        let iast_path = helpers::get_ast_path(&interface.path);

                        let intf_key = format!("{module_name}:intf");
                        let intf_deps = if build_state.build_mode().is_in_process() {
                            build_state
                                .get_in_memory_deps(&intf_key)
                                .map(|in_memory_deps| {
                                    get_dep_modules_from_memory(
                                        &in_memory_deps,
                                        package.namespace.to_suffix(),
                                        package.modules.as_ref().unwrap(),
                                        all_mod,
                                        package,
                                        build_state,
                                    )
                                })
                                .unwrap_or_else(|| {
                                    panic!(
                                        "in-process invariant violated: missing stored interface deps for {module_name}; refusing to read {} from disk",
                                        iast_path.display()
                                    )
                                })
                        } else {
                            get_dep_modules(
                                &iast_path.to_string_lossy(),
                                package.namespace.to_suffix(),
                                package.modules.as_ref().unwrap(),
                                all_mod,
                                package,
                                build_state,
                            )
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
                module.deps = deps.clone();
                module.deps_dirty = false;
            }
            deps.iter().for_each(|dep_name| {
                if let Some(module) = build_state.modules.get_mut(dep_name) {
                    module.dependents.insert(module_name.to_string());
                }
            });
        });
    build_state.deps_initialized = true;
}
