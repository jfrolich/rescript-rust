// Port of compiler/gentype/GenTypeConfig.ml:1-177.
// This Stage 2 GenType port is intentionally not wired into the crate yet.

use std::collections::{BTreeMap, HashMap};
use std::path::Path;
use std::sync::{Mutex, OnceLock};

pub type ModuleNameMap = BTreeMap<crate::gentype::module_name::T, crate::gentype::module_name::T>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum Module {
    CommonJS,
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

pub type BsVersion = (i32, i32, i32);

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct T {
    pub bsb_project_root: String,
    pub bs_dependencies: Vec<String>,
    /// Map from package name to its install path, used to locate [.cmt]/[.cmti]
    /// files of cross-package references.
    pub dep_paths: HashMap<String, String>,
    pub emit_import_curry: bool,
    pub emit_import_react: bool,
    pub emit_type_prop_done: bool,
    pub everything: bool,
    pub export_interfaces: bool,
    pub generated_file_extension: Option<String>,
    pub module_: Module,
    pub module_resolution: ModuleResolution,
    pub namespace: Option<String>,
    pub platform_lib: String,
    pub project_root: String,
    pub shims_map: ModuleNameMap,
    pub sources: Vec<String>,
    pub suffix: String,
}

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

pub fn bs_platform_lib(config: &T) -> String {
    match config.module_ {
        Module::ESModule => format!("{}/lib/es6", config.platform_lib),
        Module::CommonJS => format!("{}/lib/js", config.platform_lib),
    }
}

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
    pub project_root: String,
    pub bsb_project_root: String,
    pub module_flag: Option<Module>,
    pub module_resolution_flag: Option<ModuleResolution>,
    pub export_interfaces_flag: bool,
    pub generated_file_extension_flag: Option<String>,
    pub suffix_flag: Option<String>,
    pub shims: Vec<(String, String)>,
    pub bs_dependencies_flag: Vec<String>,
    pub source_dirs_flag: Vec<String>,
    pub dep_paths_flag: Vec<(String, String)>,
}

static FLAGS: OnceLock<Mutex<FlagState>> = OnceLock::new();

fn flags() -> &'static Mutex<FlagState> {
    FLAGS.get_or_init(|| Mutex::new(FlagState::default()))
}

pub fn module_of_string(s: &str) -> Option<Module> {
    match s {
        "commonjs" => Some(Module::CommonJS),
        "esmodule" => Some(Module::ESModule),
        _ => None,
    }
}

pub fn module_resolution_of_string(s: &str) -> Option<ModuleResolution> {
    match s {
        "node" => Some(ModuleResolution::Node),
        "node16" => Some(ModuleResolution::Node16),
        "bundler" => Some(ModuleResolution::Bundler),
        _ => None,
    }
}

pub fn set_project_root(dir: String) {
    flags().lock().unwrap().project_root = dir;
}

pub fn set_bsb_project_root(dir: String) {
    flags().lock().unwrap().bsb_project_root = dir;
}

pub fn set_module_flag(module_: Option<Module>) {
    flags().lock().unwrap().module_flag = module_;
}

pub fn set_module_resolution_flag(module_resolution: Option<ModuleResolution>) {
    flags().lock().unwrap().module_resolution_flag = module_resolution;
}

pub fn set_export_interfaces_flag(value: bool) {
    flags().lock().unwrap().export_interfaces_flag = value;
}

pub fn set_generated_file_extension_flag(value: Option<String>) {
    flags().lock().unwrap().generated_file_extension_flag = value;
}

pub fn set_suffix_flag(value: Option<String>) {
    flags().lock().unwrap().suffix_flag = value;
}

pub fn add_shim(raw: &str) {
    if let Some((from_module, to_module)) = raw.split_once('=') {
        flags()
            .lock()
            .unwrap()
            .shims
            .insert(0, (from_module.to_string(), to_module.to_string()));
    }
}

pub fn add_bs_dependency(name: &str) {
    flags()
        .lock()
        .unwrap()
        .bs_dependencies_flag
        .insert(0, name.to_string());
}

pub fn add_source_dir(dir: &str) {
    flags()
        .lock()
        .unwrap()
        .source_dirs_flag
        .insert(0, dir.to_string());
}

pub fn add_dep_path(raw: &str) {
    if let Some((name, path)) = raw.split_once('=') {
        flags()
            .lock()
            .unwrap()
            .dep_paths_flag
            .insert(0, (name.to_string(), path.to_string()));
    }
}

// ----- Build the Config.t from flags ----------------------------------

pub fn build_config(namespace: Option<String>) -> T {
    build_config_from_flags(namespace, flags().lock().unwrap().clone())
}

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
            .unwrap_or_else(|_| Path::new("").to_path_buf())
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

pub fn flag_state_from_cli_args(args: &[String]) -> FlagState {
    // Mirrors compiler/bsc/rescript_compiler_main.ml:300-343. This helper lets
    // the bsc subprocess path and rewatch in-process path build GenTypeConfig.t
    // from the same observable flags.
    let mut flags = FlagState::default();
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "-bs-project-root" => {
                if let Some(value) = args.get(i + 1) {
                    flags.project_root = value.clone();
                }
                i += 2;
            }
            "-bs-gentype-module" => {
                if let Some(value) = args.get(i + 1) {
                    flags.module_flag = module_of_string(value);
                }
                i += 2;
            }
            "-bs-gentype-module-resolution" => {
                if let Some(value) = args.get(i + 1) {
                    flags.module_resolution_flag = module_resolution_of_string(value);
                }
                i += 2;
            }
            "-bs-gentype-export-interfaces" => {
                flags.export_interfaces_flag = true;
                i += 1;
            }
            "-bs-gentype-generated-extension" => {
                if let Some(value) = args.get(i + 1) {
                    flags.generated_file_extension_flag = Some(value.clone());
                }
                i += 2;
            }
            "-bs-gentype-suffix" => {
                if let Some(value) = args.get(i + 1) {
                    flags.suffix_flag = Some(value.clone());
                }
                i += 2;
            }
            "-bs-gentype-shim" => {
                if let Some(value) = args.get(i + 1)
                    && let Some((from_module, to_module)) = value.split_once('=')
                {
                    flags
                        .shims
                        .insert(0, (from_module.to_string(), to_module.to_string()));
                }
                i += 2;
            }
            "-bs-gentype-debug" => {
                if let Some(value) = args.get(i + 1) {
                    crate::gentype::debug::set_item(value);
                }
                i += 2;
            }
            "-bs-gentype-dep" => {
                if let Some(value) = args.get(i + 1) {
                    flags.bs_dependencies_flag.insert(0, value.clone());
                }
                i += 2;
            }
            "-bs-gentype-source-dir" => {
                if let Some(value) = args.get(i + 1) {
                    flags.source_dirs_flag.insert(0, value.clone());
                }
                i += 2;
            }
            "-bs-gentype-dep-path" => {
                if let Some(value) = args.get(i + 1)
                    && let Some((name, path)) = value.split_once('=')
                {
                    flags
                        .dep_paths_flag
                        .insert(0, (name.to_string(), path.to_string()));
                }
                i += 2;
            }
            "-bs-gentype-bsb-project-root" => {
                if let Some(value) = args.get(i + 1) {
                    flags.bsb_project_root = value.clone();
                }
                i += 2;
            }
            _ => {
                i += 1;
            }
        }
    }
    flags
}

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
