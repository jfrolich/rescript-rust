// Port of compiler/gentype/GenTypeConfig.ml:1-177.

use std::collections::{BTreeMap, HashMap};
use std::path::Path;

/// Maps module names to the modules that shim them.
pub type ModuleNameMap = BTreeMap<crate::gentype::module_name::T, crate::gentype::module_name::T>;

/// The JavaScript module format the compiler emits.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum Module {
    /// CommonJS (`require`).
    CommonJS,
    /// ES modules (`import`).
    ESModule,
}

/// Compatibility for `compilerOptions.moduleResolution` in TypeScript projects.
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum ModuleResolution {
    /// should drop extension on import statements
    Node,
    /// should use TS output's extension (e.g. `.gen.js`) on import statements
    Node16,
    /// should use TS input's extension (e.g. `.gen.tsx`) on import statements
    Bundler,
}

/// A compiler version as major, minor and patch.
pub type BsVersion = (i32, i32, i32);

/// A package's gentype configuration (`GenTypeConfig.t`).
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct T {
    /// The root of the build, which may be an enclosing monorepo.
    pub bsb_project_root: String,
    /// The package's dependencies.
    pub bs_dependencies: Vec<String>,
    /// Map from package name to its install path, used to locate [.cmt]/[.cmti]
    /// files of cross-package references.
    pub dep_paths: HashMap<String, String>,
    /// Whether the generated file needs to import the `Curry` runtime module.
    pub emit_import_curry: bool,
    /// Whether the generated file needs to import React.
    pub emit_import_react: bool,
    /// Whether the `Props` type of the file's component has been emitted.
    pub emit_type_prop_done: bool,
    /// Whether every item is exported, as in a module annotated with `@genType`.
    pub everything: bool,
    /// Whether object types are exported as TypeScript interfaces.
    pub export_interfaces: bool,
    /// The extension of generated files, instead of the default `.gen.tsx`.
    pub generated_file_extension: Option<String>,
    /// The module format of the compiled JavaScript.
    pub module_: Module,
    /// How generated files write import paths.
    pub module_resolution: ModuleResolution,
    /// The package's namespace, if it has one.
    pub namespace: Option<String>,
    /// The name of the compiler's npm package.
    pub platform_lib: String,
    /// The package's root directory.
    pub project_root: String,
    /// The shims that replace modules in imports.
    pub shims_map: ModuleNameMap,
    /// The package's source directories, relative to its root.
    pub sources: Vec<String>,
    /// The suffix of compiled JavaScript files, such as `.bs.js`.
    pub suffix: String,
}

/// The configuration with every option at its default.
pub fn default() -> T {
    T {
        bsb_project_root: String::new(),
        bs_dependencies: vec![],
        dep_paths: HashMap::new(),
        emit_import_curry: false,
        emit_import_react: false,
        emit_type_prop_done: false,
        everything: false,
        export_interfaces: false,
        generated_file_extension: None,
        module_: Module::ESModule,
        module_resolution: ModuleResolution::Node,
        namespace: None,
        platform_lib: String::new(),
        project_root: String::new(),
        shims_map: BTreeMap::new(),
        sources: vec![],
        suffix: ".bs.js".to_string(),
    }
}

/// The directory of the compiler's runtime in the configured module format.
pub fn bs_platform_lib(config: &T) -> String {
    match config.module_ {
        Module::ESModule => format!("{}/lib/es6", config.platform_lib),
        Module::CommonJS => format!("{}/lib/js", config.platform_lib),
    }
}

/// The path of the runtime's `curry.js`.
pub fn get_bs_curry_path(config: &T) -> String {
    Path::new(&bs_platform_lib(config))
        .join("curry.js")
        .to_string_lossy()
        .to_string()
}

// ----- CLI-flag backing state -----------------------------------------

/// The following fields are populated by bsc's CLI flags. Everything the
/// gentype config used to read from rescript.json now comes through here.
#[derive(Debug, Clone, Default)]
pub struct FlagState {
    /// `-bs-project-root`.
    pub project_root: String,
    /// `-bs-gentype-bsb-project-root`.
    pub bsb_project_root: String,
    /// `-bs-gentype-module`.
    pub module_flag: Option<Module>,
    /// `-bs-gentype-module-resolution`.
    pub module_resolution_flag: Option<ModuleResolution>,
    /// `-bs-gentype-export-interfaces`.
    pub export_interfaces_flag: bool,
    /// `-bs-gentype-generated-extension`.
    pub generated_file_extension_flag: Option<String>,
    /// `-bs-gentype-suffix`.
    pub suffix_flag: Option<String>,
    /// `-bs-gentype-shim`, as (module, shim) pairs, last flag first.
    pub shims: Vec<(String, String)>,
    /// `-bs-gentype-dep`, last flag first.
    pub bs_dependencies_flag: Vec<String>,
    /// `-bs-gentype-source-dir`, last flag first.
    pub source_dirs_flag: Vec<String>,
    /// `-bs-gentype-dep-path`, as (package, path) pairs, last flag first.
    pub dep_paths_flag: Vec<(String, String)>,
}

/// The module format named by a `-bs-gentype-module` value.
pub fn module_of_string(s: &str) -> Option<Module> {
    match s {
        "commonjs" => Some(Module::CommonJS),
        "esmodule" => Some(Module::ESModule),
        _ => None,
    }
}

/// The module resolution named by a `-bs-gentype-module-resolution` value.
pub fn module_resolution_of_string(s: &str) -> Option<ModuleResolution> {
    match s {
        "node" => Some(ModuleResolution::Node),
        "node16" => Some(ModuleResolution::Node16),
        "bundler" => Some(ModuleResolution::Bundler),
        _ => None,
    }
}

// ----- Build the Config.t from flags ----------------------------------

/// `GenTypeConfig.read_config`: the configuration from the flags, in
/// package `namespace`.
pub fn build_config_from_flags(namespace: Option<String>, flags: FlagState) -> T {
    // Mirrors compiler/gentype/GenTypeConfig.ml:112-177. The input is the
    // same CLI-backed flag state that OCaml populates from
    // compiler/bsc/rescript_compiler_main.ml:300-343.
    let shims_map =
        flags
            .shims
            .iter()
            .fold(BTreeMap::new(), |mut map, (from_module, to_module)| {
                let module_name = crate::gentype::module_name::from_string_unsafe(from_module);
                let shim_module_name = crate::gentype::module_name::from_string_unsafe(to_module);
                map.insert(module_name, shim_module_name);
                map
            });

    let project_root = match flags.project_root.as_str() {
        "" => crate::process_cwd::current_dir()
            .unwrap_or_else(|_| Path::new(""))
            .to_string_lossy()
            .to_string(),
        dir => dir.to_string(),
    };
    let bsb_project_root = match flags.bsb_project_root.as_str() {
        "" => project_root.clone(),
        dir => dir.to_string(),
    };
    let default = default();
    let module_ = flags.module_flag.unwrap_or(default.module_);
    let module_resolution = flags
        .module_resolution_flag
        .unwrap_or(default.module_resolution);
    let suffix = flags.suffix_flag.unwrap_or(default.suffix);

    if crate::gentype::debug::config.load(std::sync::atomic::Ordering::Relaxed) {
        crate::gentype::log_::item(&format!("Project root: {project_root}\n"));
        if bsb_project_root != project_root {
            crate::gentype::log_::item(&format!("bsb project root: {bsb_project_root}\n"));
        }
        crate::gentype::log_::item(&format!("Config shims:{} entries \n", shims_map.len()));
    }

    let dep_paths = flags
        .dep_paths_flag
        .iter()
        .fold(HashMap::new(), |mut tbl, (name, path)| {
            tbl.insert(name.clone(), path.clone());
            tbl
        });

    T {
        bsb_project_root,
        bs_dependencies: flags.bs_dependencies_flag,
        dep_paths,
        emit_import_curry: false,
        emit_import_react: false,
        emit_type_prop_done: false,
        everything: false,
        export_interfaces: flags.export_interfaces_flag,
        generated_file_extension: flags.generated_file_extension_flag,
        module_,
        module_resolution,
        namespace,
        platform_lib: "rescript".to_string(),
        project_root,
        shims_map,
        sources: flags.source_dirs_flag,
        suffix,
    }
}

impl FlagState {
    /// Apply one GenType CLI flag, reading its value (if it takes one) from
    /// `next`. Returns whether `flag` is a GenType flag; `next` is called
    /// only for flags that take a value. Mirrors
    /// compiler/bsc/rescript_compiler_main.ml:266-270 and :300-343.
    pub fn apply(&mut self, flag: &str, next: impl FnOnce() -> Option<String>) -> bool {
        match flag {
            "-bs-project-root" => {
                if let Some(value) = next() {
                    self.project_root = value;
                }
            }
            "-bs-gentype-module" => {
                if let Some(value) = next() {
                    self.module_flag = module_of_string(&value);
                }
            }
            "-bs-gentype-module-resolution" => {
                if let Some(value) = next() {
                    self.module_resolution_flag = module_resolution_of_string(&value);
                }
            }
            "-bs-gentype-export-interfaces" => {
                self.export_interfaces_flag = true;
            }
            "-bs-gentype-generated-extension" => {
                if let Some(value) = next() {
                    self.generated_file_extension_flag = Some(value);
                }
            }
            "-bs-gentype-suffix" => {
                if let Some(value) = next() {
                    self.suffix_flag = Some(value);
                }
            }
            "-bs-gentype-shim" => {
                if let Some(value) = next()
                    && let Some((from_module, to_module)) = value.split_once('=')
                {
                    self.shims
                        .insert(0, (from_module.to_string(), to_module.to_string()));
                }
            }
            "-bs-gentype-debug" => {
                if let Some(value) = next() {
                    crate::gentype::debug::set_item(&value);
                }
            }
            "-bs-gentype-dep" => {
                if let Some(value) = next() {
                    self.bs_dependencies_flag.insert(0, value);
                }
            }
            "-bs-gentype-source-dir" => {
                if let Some(value) = next() {
                    self.source_dirs_flag.insert(0, value);
                }
            }
            "-bs-gentype-dep-path" => {
                if let Some(value) = next()
                    && let Some((name, path)) = value.split_once('=')
                {
                    self.dep_paths_flag
                        .insert(0, (name.to_string(), path.to_string()));
                }
            }
            "-bs-gentype-bsb-project-root" => {
                if let Some(value) = next() {
                    self.bsb_project_root = value;
                }
            }
            _ => return false,
        }
        true
    }
}

/// The flag state that the gentype flags in `args` set.
pub fn flag_state_from_cli_args(args: &[String]) -> FlagState {
    // Mirrors compiler/bsc/rescript_compiler_main.ml:300-343. This helper lets
    // the bsc subprocess path and rewatch in-process path build GenTypeConfig.t
    // from the same observable flags.
    let mut flags = FlagState::default();
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        flags.apply(arg, || args.next().cloned());
    }
    flags
}

/// The configuration bsc would build from the `-bs-gentype*` and related
/// flags in `args`.
pub fn build_config_from_cli_args(namespace: Option<String>, args: &[String]) -> T {
    build_config_from_flags(namespace, flag_state_from_cli_args(args))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn strings(args: &[&str]) -> Vec<String> {
        args.iter().map(|arg| (*arg).to_string()).collect()
    }

    #[test]
    fn parses_cli_backed_gentype_config() {
        let args = strings(&[
            "-bs-project-root",
            "/repo/pkg",
            "-bs-gentype",
            "-bs-gentype-module",
            "commonjs",
            "-bs-gentype-module-resolution",
            "node16",
            "-bs-gentype-export-interfaces",
            "-bs-gentype-generated-extension",
            ".gen.ts",
            "-bs-gentype-suffix",
            ".res.js",
            "-bs-gentype-shim",
            "Js=JsShim",
            "-bs-gentype-dep",
            "@scope/dep",
            "-bs-gentype-source-dir",
            "src",
            "-bs-gentype-dep-path",
            "@scope/dep=/repo/node_modules/@scope/dep",
            "-bs-gentype-bsb-project-root",
            "/repo",
        ]);

        let config = build_config_from_cli_args(Some("Ns".to_string()), &args);

        assert_eq!(config.project_root, "/repo/pkg");
        assert_eq!(config.bsb_project_root, "/repo");
        assert_eq!(config.module_, Module::CommonJS);
        assert_eq!(config.module_resolution, ModuleResolution::Node16);
        assert!(config.export_interfaces);
        assert_eq!(config.generated_file_extension.as_deref(), Some(".gen.ts"));
        assert_eq!(config.suffix, ".res.js");
        assert_eq!(config.namespace.as_deref(), Some("Ns"));
        assert_eq!(config.bs_dependencies, vec!["@scope/dep".to_string()]);
        assert_eq!(config.sources, vec!["src".to_string()]);
        assert_eq!(
            config.dep_paths.get("@scope/dep").map(String::as_str),
            Some("/repo/node_modules/@scope/dep")
        );
        assert_eq!(
            config
                .shims_map
                .get(&crate::gentype::module_name::from_string_unsafe("Js"))
                .cloned(),
            Some(crate::gentype::module_name::from_string_unsafe("JsShim"))
        );
    }
}
