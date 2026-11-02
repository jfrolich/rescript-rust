// Port of compiler/gentype/ModuleResolver.ml:1-201.

use std::collections::BTreeMap;
use std::fs;
use std::path::Path;
use std::sync::OnceLock;

use crate::gentype::paths::concat;

type ModuleNameMap = BTreeMap<crate::gentype::module_name::T, String>;

pub fn read_bs_dependencies_dirs(root: &str) -> Vec<String> {
    // Mirrors compiler/gentype/ModuleResolver.ml:6-20.
    let mut dirs = Vec::new();

    fn find_sub_dirs(root: &str, dir: &str, dirs: &mut Vec<String>) {
        let abs_dir = match dir.is_empty() {
            true => root.to_string(),
            false => concat(root, dir),
        };
        if Path::new(&abs_dir).exists() && Path::new(&abs_dir).is_dir() {
            dirs.push(dir.to_string());
            if let Ok(entries) = fs::read_dir(&abs_dir) {
                for entry in entries.flatten() {
                    let name = entry.file_name().to_string_lossy().to_string();
                    find_sub_dirs(root, &concat(dir, &name), dirs);
                }
            }
        }
    }

    find_sub_dirs(root, "", &mut dirs);
    // OCaml conses each directory onto the result, so it lists them in
    // reverse visit order.
    dirs.reverse();
    dirs
}

pub fn sourcedirs_to_map(
    config: &crate::gentype::config::T,
    extensions: &[String],
    exclude_file: &impl Fn(&str) -> bool,
) -> (ModuleNameMap, ModuleNameMap) {
    // Mirrors compiler/gentype/ModuleResolver.ml:22-69.
    fn chop_extensions(fname: &str) -> String {
        let mut current = fname.to_string();
        while let Some(idx) = current.rfind('.') {
            if idx == 0 {
                break;
            }
            current.truncate(idx);
        }
        current
    }

    fn add_dir(
        dir_on_disk: &str,
        dir_emitted: &str,
        filter: &impl Fn(&str) -> bool,
        map: &mut ModuleNameMap,
    ) {
        if let Ok(entries) = fs::read_dir(dir_on_disk) {
            for entry in entries.flatten() {
                let fname = entry.file_name().to_string_lossy().to_string();
                if filter(&fname) {
                    map.insert(
                        crate::gentype::module_name::from_string_unsafe(&chop_extensions(&fname)),
                        dir_emitted.to_string(),
                    );
                }
            }
        }
    }

    let mut file_map = ModuleNameMap::new();
    let mut bs_dependencies_file_map = ModuleNameMap::new();

    let filter_given_extension = |file_name: &str| {
        extensions.iter().any(|ext| file_name.ends_with(ext)) && !exclude_file(file_name)
    };

    for dir in &config.sources {
        let dir_on_disk = concat(&config.project_root, dir);
        if Path::new(&dir_on_disk).exists() && Path::new(&dir_on_disk).is_dir() {
            add_dir(&dir_on_disk, dir, &filter_given_extension, &mut file_map);
        }
    }

    for package_name in &config.bs_dependencies {
        if let Some(path) = config.dep_paths.get(package_name) {
            let root = ["lib", "bs"]
                .iter()
                .fold(path.clone(), |acc, segment| concat(&acc, segment));
            let filter =
                |file_name: &str| file_name.ends_with(".cmt") || file_name.ends_with(".cmti");
            for dir in read_bs_dependencies_dirs(&root) {
                let dir_on_disk = concat(&root, &dir);
                let dir_emitted = concat(package_name, &dir);
                add_dir(
                    &dir_on_disk,
                    &dir_emitted,
                    &filter,
                    &mut bs_dependencies_file_map,
                );
            }
        }
    }

    (file_map, bs_dependencies_file_map)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum Case {
    Lowercase,
    Uppercase,
}

pub struct Resolver {
    config: crate::gentype::config::T,
    extensions: Vec<String>,
    exclude_file: Box<dyn Fn(&str) -> bool + Send + Sync>,
    /// The source and bs-dependency module maps, built on first use.
    maps: OnceLock<(ModuleNameMap, ModuleNameMap)>,
}

pub fn create_lazy_resolver(
    config: &crate::gentype::config::T,
    extensions: &[String],
    exclude_file: impl Fn(&str) -> bool + Send + Sync + 'static,
) -> Resolver {
    // Mirrors compiler/gentype/ModuleResolver.ml:79-106.
    Resolver {
        config: config.clone(),
        extensions: extensions.to_vec(),
        exclude_file: Box::new(exclude_file),
        maps: OnceLock::new(),
    }
}

fn find(
    bs_dependencies: bool,
    map: &ModuleNameMap,
    module_name: &crate::gentype::module_name::T,
) -> Option<(String, Case, bool)> {
    match map.get(module_name) {
        Some(resolved_module_dir) => Some((
            resolved_module_dir.clone(),
            Case::Uppercase,
            bs_dependencies,
        )),
        None => {
            let uncapitalized = crate::gentype::module_name::uncapitalize(module_name);
            map.get(&uncapitalized).map(|resolved_module_dir| {
                (
                    resolved_module_dir.clone(),
                    Case::Lowercase,
                    bs_dependencies,
                )
            })
        }
    }
}

pub fn apply(
    resolver: &Resolver,
    use_bs_dependencies: bool,
    module_name: &crate::gentype::module_name::T,
) -> Option<(String, Case, bool)> {
    // Mirrors compiler/gentype/ModuleResolver.ml:108-109.
    let (module_name_map, bs_dependencies_file_map) = resolver.maps.get_or_init(|| {
        sourcedirs_to_map(&resolver.config, &resolver.extensions, &|file_name| {
            (resolver.exclude_file)(file_name)
        })
    });
    match find(false, module_name_map, module_name) {
        None if use_bs_dependencies => find(true, bs_dependencies_file_map, module_name),
        res => res,
    }
}

/// Whether a source file exists. Sources do not change during a build, so
/// in-process builds remember the answer per worker until the next build.
fn source_file_exists(path: &str) -> bool {
    let generation = crate::types::thread_store::build_generation();
    if generation == 0 {
        return Path::new(path).exists();
    }
    thread_local! {
        static CACHE: std::cell::RefCell<(u64, crate::fast_hash::AHashMap<String, bool>)> =
            std::cell::RefCell::new((0, crate::fast_hash::AHashMap::new()));
    }
    CACHE.with(|cache| {
        let mut cache = cache.borrow_mut();
        if cache.0 != generation {
            *cache = (generation, crate::fast_hash::AHashMap::new());
        }
        if let Some(&exists) = cache.1.get(path) {
            return exists;
        }
        let exists = Path::new(path).exists();
        cache.1.insert(path.to_string(), exists);
        exists
    })
}

pub fn resolve_module(
    config: &crate::gentype::config::T,
    import_extension: &str,
    output_file_relative: &str,
    resolver: &Resolver,
    use_bs_dependencies: bool,
    module_name: &crate::gentype::module_name::T,
) -> crate::gentype::import_path::T {
    // Mirrors compiler/gentype/ModuleResolver.ml:111-164.
    let output_file_relative_dir = dirname(output_file_relative);
    let output_file_absolute_dir = concat(&config.project_root, &output_file_relative_dir);
    let module_name_res_file = concat(
        &output_file_absolute_dir,
        &format!(
            "{}.res",
            crate::gentype::module_name::to_string(module_name)
        ),
    );
    let candidate = crate::gentype::import_path::from_module(".", import_extension, module_name);

    if source_file_exists(&module_name_res_file) {
        candidate
    } else {
        match apply(resolver, use_bs_dependencies, module_name) {
            None => candidate,
            Some((resolved_module_dir, case, bs_dependencies)) => {
                let l = path_to_list(&output_file_relative_dir)
                    .into_iter()
                    .map(|_| "..".to_string())
                    .collect::<Vec<_>>();
                let walk_up_output_dir = match l.as_slice() {
                    [] => String::new(),
                    [_first, rest @ ..] => rest
                        .iter()
                        .fold("..".to_string(), |acc, segment| concat(&acc, segment)),
                };
                let from_output_dir_to_module_dir = match bs_dependencies {
                    true => resolved_module_dir,
                    false => concat(&walk_up_output_dir, &resolved_module_dir),
                };
                let module_name = match case == Case::Uppercase {
                    true => module_name.clone(),
                    false => crate::gentype::module_name::uncapitalize(module_name),
                };
                crate::gentype::import_path::from_module(
                    &from_output_dir_to_module_dir,
                    import_extension,
                    &module_name,
                )
            }
        }
    }
}

pub fn resolve_generated_module(
    config: &crate::gentype::config::T,
    output_file_relative: &str,
    resolver: &Resolver,
    module_name: &crate::gentype::module_name::T,
) -> crate::gentype::import_path::T {
    // Mirrors compiler/gentype/ModuleResolver.ml:166-178.
    if crate::gentype::debug::module_resolution.load(std::sync::atomic::Ordering::Relaxed) {
        crate::gentype::log_::item(&format!(
            "Resolve Generated Module: {}\n",
            crate::gentype::module_name::to_string(module_name)
        ));
    }
    let import_path = resolve_module(
        config,
        &crate::gentype::module_extension::generated_module_extension(config),
        output_file_relative,
        resolver,
        true,
        module_name,
    );
    if crate::gentype::debug::module_resolution.load(std::sync::atomic::Ordering::Relaxed) {
        crate::gentype::log_::item(&format!(
            "Import Path: {}\n",
            crate::gentype::import_path::dump(&import_path)
        ));
    }
    import_path
}

pub fn import_path_for_reason_module_name(
    config: &crate::gentype::config::T,
    output_file_relative: &str,
    resolver: &Resolver,
    module_name: &crate::gentype::module_name::T,
) -> crate::gentype::import_path::T {
    // Mirrors compiler/gentype/ModuleResolver.ml:180-201.
    if crate::gentype::debug::module_resolution.load(std::sync::atomic::Ordering::Relaxed) {
        crate::gentype::log_::item(&format!(
            "Resolve Reason Module: {}\n",
            crate::gentype::module_name::to_string(module_name)
        ));
    }
    match config.shims_map.get(module_name) {
        Some(shim_module_name) => {
            if crate::gentype::debug::module_resolution.load(std::sync::atomic::Ordering::Relaxed) {
                crate::gentype::log_::item(&format!(
                    "ShimModuleName: {}\n",
                    crate::gentype::module_name::to_string(shim_module_name)
                ));
            }
            let import_extension =
                crate::gentype::module_extension::shim_ts_output_file_extension(config);
            let import_path = resolve_module(
                config,
                &import_extension,
                output_file_relative,
                resolver,
                false,
                shim_module_name,
            );
            if crate::gentype::debug::module_resolution.load(std::sync::atomic::Ordering::Relaxed) {
                crate::gentype::log_::item(&format!(
                    "Import Path: {}\n",
                    crate::gentype::import_path::dump(&import_path)
                ));
            }
            import_path
        }
        None => resolve_generated_module(config, output_file_relative, resolver, module_name),
    }
}

fn dirname(path: &str) -> String {
    match Path::new(path).parent().and_then(|p| p.to_str()) {
        Some("") | None => ".".to_string(),
        Some(parent) => parent.to_string(),
    }
}

fn basename(path: &str) -> String {
    Path::new(path)
        .file_name()
        .and_then(|p| p.to_str())
        .unwrap_or(path)
        .to_string()
}

fn path_to_list(path: &str) -> Vec<String> {
    // Mirrors compiler/gentype/module_resolver.ml `path_to_list`. On Windows,
    // the basename of a drive root omits the drive prefix, so a path whose
    // parent is itself is a root too.
    let base = basename(path);
    let parent = dirname(path);
    if base == path || parent == path {
        vec![path.to_string()]
    } else {
        let mut out = vec![base];
        out.extend(path_to_list(&parent));
        out
    }
}
