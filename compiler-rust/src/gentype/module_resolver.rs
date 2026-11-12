// Port of compiler/gentype/ModuleResolver.ml:1-201.

use std::collections::BTreeMap;
use std::fs;
use std::path::Path;
use std::sync::OnceLock;

use crate::gentype::paths::concat;

type ModuleNameMap = BTreeMap<crate::gentype::module_name::T, String>;

/// The source path in the header of the AST at `path`, read from its first
/// bytes (a header is a few hundred bytes), or `None` when the file is not an
/// AST. Mirrors compiler/gentype/module_resolver.ml `ast_source`.
fn ast_source(path: &Path) -> Option<Vec<u8>> {
    use std::io::Read;
    const PREFIX: u64 = 4096;
    let mut file = fs::File::open(path).ok()?;
    let mut contents = Vec::new();
    file.by_ref().take(PREFIX).read_to_end(&mut contents).ok()?;
    let read = |contents: &[u8]| {
        crate::binary_ast::header::read_header(contents)
            .map(|header| crate::binary_ast::header::header_source(contents, &header).to_vec())
    };
    match read(&contents) {
        Some(source) => Some(source),
        None if contents.len() as u64 == PREFIX => {
            file.read_to_end(&mut contents).ok()?;
            read(&contents)
        }
        None => None,
    }
}

/// The directories of a dependency's sources, relative to its `root`, by the
/// name of their ASTs (`X` for `X.ast`): each AST records its source.
/// Mirrors compiler/gentype/module_resolver.ml `read_source_dirs`.
fn read_source_dirs(root: &str, artifact_dir: &str, names: &[String]) -> BTreeMap<String, String> {
    let prefix = format!("{root}{}", std::path::MAIN_SEPARATOR);
    let mut source_dirs = BTreeMap::new();
    for name in names {
        let Some(stem) = name.strip_suffix(".ast") else {
            continue;
        };
        let Some(source) = ast_source(Path::new(&concat(artifact_dir, name))) else {
            continue;
        };
        let source = String::from_utf8_lossy(&source);
        let Some(relative) = source.strip_prefix(&prefix) else {
            continue;
        };
        let dir = match Path::new(relative).parent() {
            Some(dir) => dir.to_string_lossy().to_string(),
            None => String::new(),
        };
        source_dirs.insert(stem.to_string(), dir);
    }
    source_dirs
}

/// The `.cmt`/`.cmti` files of a dependency at `root`, each with the
/// directory of its module's source relative to `root`. The artifacts are
/// flat in `lib/rescript`, so a module's `X.cmt` or `X-Ns.cmt` lies in the
/// directory of the source that `X.ast` names. Mirrors
/// compiler/gentype/module_resolver.ml `dependency_module_dirs`; the resolver
/// builds its maps once per build, so the AST headers are read once per build
/// as there.
pub fn dependency_module_dirs(root: &str) -> Vec<(String, String)> {
    let artifact_dir = ["lib", "rescript"]
        .iter()
        .fold(root.to_string(), |acc, segment| concat(&acc, segment));
    let Ok(entries) = fs::read_dir(&artifact_dir) else {
        return Vec::new();
    };
    let mut names: Vec<String> = entries
        .flatten()
        .map(|entry| entry.file_name().to_string_lossy().to_string())
        .collect();
    names.sort();
    let source_dirs = read_source_dirs(root, &artifact_dir, &names);
    // A namespaced module's compiled files append "-" and the namespace,
    // which has no "-" of its own, to the source file name. The namespace
    // itself has a map instead of a source, and belongs to the package root.
    let source_dir = |compiled: &str| -> Option<String> {
        if let Some(dir) = source_dirs.get(compiled) {
            return Some(dir.clone());
        }
        if names
            .iter()
            .any(|name| name.strip_suffix(".mlmap") == Some(compiled))
        {
            return Some(String::new());
        }
        let index = compiled.rfind('-')?;
        source_dirs.get(&compiled[..index]).cloned()
    };
    names
        .iter()
        .filter_map(|name| {
            let stem = name
                .strip_suffix(".cmt")
                .or_else(|| name.strip_suffix(".cmti"))?;
            source_dir(stem).map(|dir| (name.clone(), dir))
        })
        .collect()
}

/// The module maps of the project's source directories and of its
/// `bs-dependencies`: each module name, from a file with one of `extensions`
/// that `exclude_file` does not reject, mapped to its directory.
pub fn sourcedirs_to_map(
    config: &crate::gentype::config::T,
    extensions: &[String],
    exclude_file: &impl Fn(&str) -> bool,
) -> (ModuleNameMap, ModuleNameMap) {
    // Mirrors compiler/gentype/module_resolver.ml `sourcedirs_to_map`.
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
            for (fname, dir) in dependency_module_dirs(path) {
                bs_dependencies_file_map.insert(
                    crate::gentype::module_name::from_string_unsafe(&chop_extensions(&fname)),
                    concat(package_name, &dir),
                );
            }
        }
    }

    (file_map, bs_dependencies_file_map)
}

/// The case a module was found in.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum Case {
    /// The file name starts with a lowercase letter.
    Lowercase,
    /// The file name is capitalized like the module.
    Uppercase,
}

/// Finds the directory of a module among the package's sources and its
/// `bs-dependencies`.
pub struct Resolver {
    config: crate::gentype::config::T,
    extensions: Vec<String>,
    exclude_file: Box<dyn Fn(&str) -> bool + Send + Sync>,
    /// The source and bs-dependency module maps, built on first use.
    maps: OnceLock<(ModuleNameMap, ModuleNameMap)>,
}

/// A resolver over the files with one of `extensions` that `exclude_file`
/// does not reject; the source directories are scanned on first use.
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

/// The directory of `module_name`, the case its file name has, and whether
/// it is in a dependency; dependencies are searched when
/// `use_bs_dependencies` is set.
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

/// The path a generated file at `output_file_relative` imports
/// `module_name` from: next to it when that module's `.res` file is there,
/// else wherever the resolver finds it.
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

/// The path a generated file imports the generated file of `module_name`
/// from.
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

/// The path a generated file imports the TypeScript of ReScript module
/// `module_name` from: its shim when one is configured, else its generated
/// file.
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

#[cfg(test)]
mod tests {
    use super::*;

    /// An AST whose header records `source`, followed by bytes that stand in
    /// for the marshalled tree.
    fn ast_with_source(source: &str) -> Vec<u8> {
        let block = b"\nDep\n";
        let mut contents = (block.len() as i32).to_be_bytes().to_vec();
        contents.extend_from_slice(block);
        contents.extend_from_slice(source.as_bytes());
        contents.push(b'\n');
        contents.extend_from_slice(&[0u8; 64]);
        contents
    }

    #[test]
    fn dependency_modules_lie_in_the_directories_their_asts_name() {
        let dir = tempfile::tempdir().unwrap();
        let root = dir.path().join("dep");
        let artifacts = root.join("lib").join("rescript");
        fs::create_dir_all(&artifacts).unwrap();
        let root = root.to_string_lossy().to_string();
        let source = |relative: &str| {
            Path::new(&root)
                .join(relative)
                .to_string_lossy()
                .to_string()
        };
        fs::write(
            artifacts.join("A.ast"),
            ast_with_source(&source("src/nested/A.res")),
        )
        .unwrap();
        fs::write(artifacts.join("B.ast"), ast_with_source(&source("B.res"))).unwrap();
        fs::write(
            artifacts.join("Other.ast"),
            ast_with_source("/elsewhere/Other.res"),
        )
        .unwrap();
        for name in [
            "A-Ns.cmt",
            "A-Ns.cmti",
            "B-Ns.cmt",
            "Ns.cmt",
            "Ns.mlmap",
            "Other.cmt",
            "Lost.cmt",
        ] {
            fs::write(artifacts.join(name), b"").unwrap();
        }

        let dirs = dependency_module_dirs(&root);

        assert_eq!(
            dirs,
            vec![
                ("A-Ns.cmt".to_string(), "src/nested".to_string()),
                ("A-Ns.cmti".to_string(), "src/nested".to_string()),
                ("B-Ns.cmt".to_string(), String::new()),
                ("Ns.cmt".to_string(), String::new()),
            ]
        );
    }

    #[test]
    fn a_dependency_without_an_artifact_directory_has_no_modules() {
        let dir = tempfile::tempdir().unwrap();
        assert!(dependency_module_dirs(&dir.path().to_string_lossy()).is_empty());
    }
}
