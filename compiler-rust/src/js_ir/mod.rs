//! JavaScript IR - Intermediate representation for JavaScript output.
//!
//! This module provides the JavaScript IR, which is the final intermediate
//! representation before generating JavaScript source code. It's a subset
//! of JavaScript AST specialized for the ReScript compilation target.
//!
//! # Architecture
//!
//! The JS IR is organized into:
//!
//! - [`op`] - Operators, properties, and other JS-specific types
//! - Expressions - Values that produce results
//! - Statements - Instructions that have effects
//! - Programs - Complete compilation units

pub mod arena;
pub mod build;
#[cfg(test)]
pub mod dump;
pub mod op;
pub mod printer;
pub mod program_printer;
pub mod source_map;
#[cfg(test)]
pub(crate) mod test_util;
pub(crate) mod walk;

use ahash::AHashMap;
use std::cell::RefCell;
use std::ffi::OsString;
use std::fs;
use std::path::{Component, Path as FsPath, PathBuf};
use std::sync::Arc;

use crate::cmi::persistent_env::{
    CmjExportArity, CmjExportConstant, CmjFileCase, CmjPackageModuleSystem, CmjPackageName,
    CmjPackageSpec, PersistentEnv,
};
use crate::ident::Ident;
pub use op::{BinOp, IdentInfo, Kind, LengthObject, MutableFlag, Number, Property, PropertyName};
pub use printer::JsPrinter;
pub use program_printer::{
    print_deps_program, print_deps_program_with_directives,
    print_deps_program_with_directives_and_options, print_deps_program_with_source_map,
    print_program,
};

/// Module identifier for imports/requires
#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub struct ModuleId {
    /// The module identifier
    pub id: Ident,
    /// Module kind (Ml, Runtime, External)
    pub kind: Kind,
    /// Is this a dynamic import?
    pub dynamic_import: bool,
}

/// Output module format used to resolve import paths.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModuleFormat {
    /// ECMAScript modules (`.mjs`)
    EsModule,
    /// CommonJS (`.js`, `.bs.js`)
    CommonJs,
}

/// One `-bs-package-output` of the package being compiled
/// (compiler/core/js_packages_info.ml:133-159): where its JavaScript for a
/// module system goes and with which suffix. Every package of a build gets the
/// root configuration's specs, so a dependency's are the same.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JsPackageSpec {
    pub module_format: ModuleFormat,
    /// Next to the source, or under `lib/<out_of_source_dir>/`.
    pub in_source: bool,
    pub out_of_source_dir: String,
    pub suffix: String,
}

/// Resolves lowered module identifiers to emitted JavaScript import paths.
#[derive(Clone)]
pub struct ModulePathResolver {
    format: ModuleFormat,
    output_suffix: String,
    /// The package's specs in configuration order (see [`JsPackageSpec`]).
    package_specs: Vec<JsPackageSpec>,
    current_source_path: Option<PathBuf>,
    /// `Filename.dirname` of the output prefix, which script-mode imports are
    /// relative to (js_name_of_module_id.ml `~output_dir`).
    output_dir: Option<PathBuf>,
    current_package_name: Option<String>,
    current_package_has_output: bool,
    runtime_path: Option<PathBuf>,
    persistent_env: Option<PersistentEnv>,
    current_package_is_runtime: bool,
    path_overrides: AHashMap<String, String>,
    module_path_cache: RefCell<AHashMap<String, Option<String>>>,
    runtime_module_cache: RefCell<AHashMap<String, bool>>,
    pure_module_cache: RefCell<AHashMap<String, bool>>,
    cmj_export_constants_cache:
        RefCell<AHashMap<String, Option<Arc<AHashMap<String, CmjExportConstant>>>>>,
    cmj_export_arities_cache:
        RefCell<AHashMap<String, Option<Arc<AHashMap<String, CmjExportArity>>>>>,
    cmj_export_lambdas_cache:
        RefCell<AHashMap<String, Option<Arc<crate::lambda::CmjExportLambdas>>>>,
    cmj_hoisted_exports_cache: RefCell<AHashMap<(String, Vec<String>), Option<String>>>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ModulePathResolutionError {
    CmjNotFound { module_name: String },
    JsNotFound { js_file: String },
    MissingMlDependency { module_name: String },
    DependencyScriptModuleDependentNot { module_name: String },
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum PackageInfoQuery {
    Script,
    NotFound,
    Found,
}

impl ModulePathResolver {
    /// Build a resolver from the current compilation context.
    pub fn from_compile_options(
        source_filename: Option<&str>,
        output_path: Option<&FsPath>,
        output_module_format: Option<ModuleFormat>,
        package_name: Option<&str>,
        runtime_path: Option<&FsPath>,
        persistent_env: Option<PersistentEnv>,
        current_package_is_runtime: bool,
    ) -> Self {
        Self {
            format: output_module_format
                .unwrap_or_else(|| module_format_from_output_path(output_path)),
            output_suffix: output_suffix_from_paths(source_filename.map(FsPath::new), output_path),
            package_specs: Vec::new(),
            current_source_path: source_filename
                .map(|path| normalize_absolute_path(FsPath::new(path))),
            output_dir: output_path
                .or(source_filename.map(FsPath::new))
                .and_then(|path| {
                    normalize_absolute_path(path)
                        .parent()
                        .map(FsPath::to_path_buf)
                }),
            current_package_name: package_name.map(ToOwned::to_owned),
            current_package_has_output: package_name.is_some() && output_module_format.is_some(),
            runtime_path: runtime_path.map(normalize_absolute_path),
            persistent_env,
            current_package_is_runtime,
            path_overrides: AHashMap::new(),
            module_path_cache: RefCell::new(AHashMap::new()),
            runtime_module_cache: RefCell::new(AHashMap::new()),
            pure_module_cache: RefCell::new(AHashMap::new()),
            cmj_export_constants_cache: RefCell::new(AHashMap::new()),
            cmj_export_arities_cache: RefCell::new(AHashMap::new()),
            cmj_export_lambdas_cache: RefCell::new(AHashMap::new()),
            cmj_hoisted_exports_cache: RefCell::new(AHashMap::new()),
        }
    }

    /// The package specs imports are resolved with (see [`JsPackageSpec`]).
    pub fn set_package_specs(&mut self, specs: &[JsPackageSpec]) {
        self.package_specs = specs.to_vec();
        self.module_path_cache.borrow_mut().clear();
    }

    /// The spec a module's import path follows for the current module system:
    /// OCaml's `query_package_infos` (js_packages_info.ml:110-121) takes the
    /// first compatible entry of `module_systems`, which `add_npm_package_path`
    /// builds by prepending each `-bs-package-output`, so the last one in
    /// configuration order wins.
    fn found_package_spec(&self) -> Option<&JsPackageSpec> {
        self.package_specs
            .iter()
            .rev()
            .find(|spec| spec.module_format == self.format)
    }

    /// Override a module's emitted JS import path.
    pub fn set_module_path_override(&mut self, module_name: &str, path: String) {
        self.path_overrides.insert(module_name.to_string(), path);
        self.module_path_cache.borrow_mut().remove(module_name);
    }

    /// Module format for the current output target.
    pub fn module_format(&self) -> ModuleFormat {
        self.format
    }

    /// Whether module resolution is backed by the in-memory registry. In this
    /// mode the build scheduler has already scanned source files, so JS
    /// lowering must not probe sibling directories.
    pub fn is_in_process_mode(&self) -> bool {
        self.persistent_env
            .as_ref()
            .is_some_and(PersistentEnv::is_in_process_mode)
    }

    /// Resolve a same-directory source fallback path for an ML module.
    pub fn resolve_local_module_fallback_path(&self, module_name: &str) -> Option<String> {
        if self.is_in_process_mode() {
            return None;
        }
        let target_source = self.fallback_local_module_source(module_name)?;
        self.relative_output_path(&target_source)
    }

    /// Resolve the emitted JavaScript import path for a lowered module id.
    pub fn resolve_module_path(&self, module: &ModuleId) -> Option<String> {
        if let Some(path) = self.path_overrides.get(module.id.name()) {
            return Some(path.clone());
        }

        match &module.kind {
            Kind::External { name, .. } => Some(name.clone()),
            Kind::Runtime => Some(self.runtime_module_path(module.id.name())),
            Kind::Ml => {
                let module_name = module.id.name();
                if let Some(cached) = self.module_path_cache.borrow().get(module_name).cloned() {
                    return cached;
                }
                let resolved = if let Some(path) = self.script_module_path(module_name) {
                    Some(path)
                } else if self.is_runtime_module(module_name) {
                    Some(self.runtime_module_path(module.id.name()))
                } else {
                    let target_source = self
                        .persistent_env
                        .as_ref()
                        .and_then(|env| env.resolve_module_source_path(module_name))
                        .map(|path| normalize_absolute_path(&path));
                    target_source.and_then(|target_source| {
                        self.package_module_path(module_name, &target_source)
                            .or_else(|| self.relative_output_path(&target_source))
                    })
                };
                self.module_path_cache
                    .borrow_mut()
                    .insert(module_name.to_string(), resolved.clone());
                resolved
            }
        }
    }

    /// Return the package-mode dependency error that OCaml raises while turning
    /// an ML module id into a JS import path.
    pub fn module_path_resolution_error(
        &self,
        module: &ModuleId,
    ) -> Option<ModulePathResolutionError> {
        if module.dynamic_import
            || self.path_overrides.contains_key(module.id.name())
            || !matches!(module.kind, Kind::Ml)
            || self.is_runtime_module(module.id.name())
        {
            return None;
        }

        let env = self.persistent_env.as_ref()?;
        let module_name = module.id.name();
        let Some(import_info) = env.module_cmj_import_info(module_name) else {
            if !env.module_has_in_memory_info(module_name)
                && env.resolve_module_cmj_path(module_name).is_none()
            {
                return Some(ModulePathResolutionError::CmjNotFound {
                    module_name: module_name.to_string(),
                });
            }
            return None;
        };
        let dep_query = self.query_package_spec(&import_info.package_spec);
        let current_query = self.current_package_query();
        match (&dep_query, &current_query) {
            (PackageInfoQuery::NotFound, _) => {
                Some(ModulePathResolutionError::MissingMlDependency {
                    module_name: module_name.to_string(),
                })
            }
            (PackageInfoQuery::Script, PackageInfoQuery::Found) => Some(
                ModulePathResolutionError::DependencyScriptModuleDependentNot {
                    module_name: module_name.to_string(),
                },
            ),
            (PackageInfoQuery::Script, PackageInfoQuery::Script) => {
                // A module compiled in memory (the playground, tests) has no
                // file to find.
                if env.module_has_in_memory_info(module_name) {
                    return None;
                }
                let js_file = js_name_of_module_name(module_name, import_info.file_case, ".js");
                (!env.file_exists_in_load_path_uncap(&js_file))
                    .then_some(ModulePathResolutionError::JsNotFound { js_file })
            }
            _ => None,
        }
    }

    /// Return the side-effect reason OCaml records for a required module, if it
    /// is not marked pure.
    pub fn module_side_effect_reason(&self, module: &ModuleId) -> Option<String> {
        if self.is_pure_module(module) {
            return None;
        }

        Some(match &module.kind {
            Kind::External { name, .. } => name.clone(),
            Kind::Runtime | Kind::Ml => module.id.name().to_string(),
        })
    }

    /// Read closed constant exports recorded in a module's companion `.cmj`.
    pub fn module_cmj_export_constants(
        &self,
        module_name: &str,
    ) -> Option<Arc<AHashMap<String, CmjExportConstant>>> {
        if let Some(cached) = self
            .cmj_export_constants_cache
            .borrow()
            .get(module_name)
            .cloned()
        {
            return cached;
        }
        let resolved = self
            .persistent_env
            .as_ref()
            .and_then(|env| env.module_cmj_export_constants(module_name));
        self.cmj_export_constants_cache
            .borrow_mut()
            .insert(module_name.to_string(), resolved.clone());
        resolved
    }

    /// Read arity metadata recorded in a module's companion `.cmj`.
    pub fn module_cmj_export_arities(
        &self,
        module_name: &str,
    ) -> Option<Arc<AHashMap<String, CmjExportArity>>> {
        if let Some(cached) = self
            .cmj_export_arities_cache
            .borrow()
            .get(module_name)
            .cloned()
        {
            return cached;
        }
        let resolved = self
            .persistent_env
            .as_ref()
            .and_then(|env| env.module_cmj_export_arities(module_name));
        self.cmj_export_arities_cache
            .borrow_mut()
            .insert(module_name.to_string(), resolved.clone());
        resolved
    }

    /// Resolve a source-level nested field path through hoisted CMJ metadata.
    pub fn module_cmj_hoisted_export(&self, module_name: &str, path: &[String]) -> Option<String> {
        let key = (module_name.to_string(), path.to_vec());
        if let Some(cached) = self.cmj_hoisted_exports_cache.borrow().get(&key) {
            return cached.clone();
        }
        let resolved = self
            .persistent_env
            .as_ref()
            .and_then(|env| env.module_cmj_hoisted_export(module_name, path));
        self.cmj_hoisted_exports_cache
            .borrow_mut()
            .insert(key, resolved.clone());
        resolved
    }

    /// Read closed lambda exports recorded in a module's companion `.cmj`.
    pub fn module_cmj_export_lambdas(
        &self,
        module_name: &str,
    ) -> Option<Arc<crate::lambda::CmjExportLambdas>> {
        if let Some(cached) = self
            .cmj_export_lambdas_cache
            .borrow()
            .get(module_name)
            .cloned()
        {
            return cached;
        }
        let resolved = self
            .persistent_env
            .as_ref()
            .and_then(|env| env.module_cmj_export_lambdas(module_name));
        self.cmj_export_lambdas_cache
            .borrow_mut()
            .insert(module_name.to_string(), resolved.clone());
        resolved
    }

    fn runtime_module_path(&self, module_name: &str) -> String {
        // OCaml emits sibling runtime imports while compiling the runtime
        // package itself; see compiler/core/js_name_of_module_id.ml:68-84
        // and compiler/core/js_packages_info.ml:49-50.
        if self.current_package_is_runtime {
            return format!("./{module_name}{}", self.output_suffix);
        }

        // Mirror upstream PR #8207: runtime files use .mjs / .cjs extensions
        // matching the module system, not .js.
        let (dir, ext) = match self.format {
            ModuleFormat::EsModule => ("es6", "mjs"),
            ModuleFormat::CommonJs => ("js", "cjs"),
        };
        format!("@rescript/runtime/lib/{dir}/{module_name}.{ext}")
    }

    fn is_runtime_module(&self, module_name: &str) -> bool {
        if let Some(cached) = self.runtime_module_cache.borrow().get(module_name).copied() {
            return cached;
        }

        let resolved = self.compute_is_runtime_module(module_name);
        self.runtime_module_cache
            .borrow_mut()
            .insert(module_name.to_string(), resolved);
        resolved
    }

    fn compute_is_runtime_module(&self, module_name: &str) -> bool {
        if let Some(env) = &self.persistent_env {
            if env.module_is_runtime(module_name) {
                return true;
            }
            if env.is_in_process_mode() {
                return false;
            }
        }

        let Some(runtime_path) = &self.runtime_path else {
            return false;
        };
        let ocaml_dir = runtime_path.join("lib").join("ocaml");
        ocaml_dir.join(format!("{module_name}.cmi")).exists()
            || ocaml_dir.join(format!("{module_name}.ast")).exists()
            || ocaml_dir.join(format!("{module_name}.iast")).exists()
    }

    fn is_pure_module(&self, module: &ModuleId) -> bool {
        if !matches!(module.kind, Kind::Ml) {
            return matches!(module.kind, Kind::Runtime);
        }

        // OCaml only treats Lam_module_ident.Runtime as automatically pure;
        // Ml modules still read their `.cmj` purity even when their JS path
        // points into @rescript/runtime. See
        // compiler/core/lam_compile_env.ml:124-136.
        let module_name = module.id.name();
        if let Some(cached) = self.pure_module_cache.borrow().get(module_name).copied() {
            return cached;
        }

        let resolved = self
            .persistent_env
            .as_ref()
            .and_then(|env| env.module_cmj_is_pure(module_name))
            .unwrap_or(false);
        self.pure_module_cache
            .borrow_mut()
            .insert(module_name.to_string(), resolved);
        resolved
    }

    /// js_name_of_module_id.ml `Package_script, Package_script`: a script
    /// dependency of a script unit is imported from the `.js` file found on
    /// the load path, relative to the output directory.
    fn script_module_path(&self, module_name: &str) -> Option<String> {
        if !matches!(self.current_package_query(), PackageInfoQuery::Script) {
            return None;
        }
        let env = self.persistent_env.as_ref()?;
        let import_info = env.module_cmj_import_info(module_name)?;
        // `Package_found dep, Package_script`: `pkg.pkg_rel_path // js_file`
        // (js_packages_info.ml `query_package_infos`).
        let package_name = match &import_info.package_spec.name {
            crate::cmi::persistent_env::CmjPackageName::Empty => None,
            crate::cmi::persistent_env::CmjPackageName::Runtime => Some("@rescript/runtime"),
            crate::cmi::persistent_env::CmjPackageName::Normal(name) => Some(name.as_str()),
        };
        if let Some(package_name) = package_name {
            let info = import_info
                .package_spec
                .module_systems
                .iter()
                .find(|info| module_system_compatible(info.module_system, self.format))?;
            let js_file = js_name_of_module_name(module_name, import_info.file_case, &info.suffix);
            return Some(filename_concat(
                &filename_concat(package_name, &info.path),
                &js_file,
            ));
        }
        // In process, the build has scanned the sources already: no probing
        // the load path for a script-mode dependency's JavaScript.
        if self.is_in_process_mode() {
            return None;
        }
        let js_file = js_name_of_module_name(module_name, import_info.file_case, ".js");
        let found = normalize_absolute_path(FsPath::new(&env.find_in_load_path_uncap(&js_file)?));
        let relative = relative_path_between(self.output_dir.as_ref()?, &found)?;
        let mut rendered = relative.to_string_lossy().replace('\\', "/");
        if !rendered.starts_with("./") && !rendered.starts_with("../") {
            rendered = format!("./{rendered}");
        }
        Some(rendered)
    }

    fn relative_output_path(&self, target_source: &FsPath) -> Option<String> {
        let current_source = self.current_source_path.as_ref()?;
        let from_dir = current_source.parent()?;
        let target_dir = target_source.parent()?;
        let target_stem = target_source.file_stem()?.to_str()?;
        // Within a package, `node_rebase_file` between the two modules'
        // directories of the found spec (js_name_of_module_id.ml:115-127) is
        // the relative path between their source directories either way; the
        // spec decides the suffix.
        let suffix = self
            .found_package_spec()
            .map_or(self.output_suffix.as_str(), |spec| spec.suffix.as_str());
        let target_output = target_dir.join(format!("{target_stem}{suffix}"));
        let relative = relative_path_between(from_dir, &target_output)?;
        let mut rendered = relative.to_string_lossy().replace('\\', "/");
        if !rendered.starts_with("./") && !rendered.starts_with("../") {
            rendered = format!("./{rendered}");
        }
        Some(rendered)
    }

    fn package_module_path(&self, module_name: &str, target_source: &FsPath) -> Option<String> {
        let current_package_name = self.current_package_name.as_deref()?;
        let (target_package_name, target_package_root, target_suffix) = self
            .persistent_env
            .as_ref()?
            .module_js_package_info(module_name)?;
        if target_package_name.as_ref() == current_package_name {
            return None;
        }

        // OCaml distinguishes same-package rebasing from dependency-package
        // paths through Js_packages_info.query_package_infos and
        // same_package_by_name; see compiler/core/js_name_of_module_id.ml:115-146.
        let target_package_root = normalize_absolute_path(target_package_root.as_ref());
        let relative_source = target_source.strip_prefix(&target_package_root).ok()?;
        // `dep_pkg.pkg_rel_path // js_file` (js_name_of_module_id.ml:132):
        // the found spec's directory, out of source under `lib/`.
        let relative_output = match self.found_package_spec() {
            Some(spec) => {
                let output = source_path_with_js_suffix(relative_source, &spec.suffix)?;
                if spec.in_source {
                    output
                } else {
                    PathBuf::from("lib")
                        .join(&spec.out_of_source_dir)
                        .join(output)
                }
            }
            None => {
                let suffix = target_suffix.as_deref().unwrap_or(&self.output_suffix);
                source_path_with_js_suffix(relative_source, suffix)?
            }
        };
        Some(format!(
            "{}/{}",
            target_package_name.as_ref(),
            relative_output.to_string_lossy().replace('\\', "/")
        ))
    }

    fn current_package_query(&self) -> PackageInfoQuery {
        if self.current_package_is_runtime {
            return PackageInfoQuery::NotFound;
        }
        let Some(_current_package_name) = &self.current_package_name else {
            return PackageInfoQuery::Script;
        };
        if !self.current_package_has_output {
            return PackageInfoQuery::NotFound;
        }

        PackageInfoQuery::Found
    }

    fn query_package_spec(&self, package_spec: &CmjPackageSpec) -> PackageInfoQuery {
        match &package_spec.name {
            CmjPackageName::Empty => return PackageInfoQuery::Script,
            CmjPackageName::Runtime | CmjPackageName::Normal(_) => {}
        };

        if package_spec
            .module_systems
            .iter()
            .any(|info| module_system_compatible(info.module_system, self.format))
        {
            PackageInfoQuery::Found
        } else {
            PackageInfoQuery::NotFound
        }
    }

    fn fallback_local_module_source(&self, module_name: &str) -> Option<PathBuf> {
        let current_source = self.current_source_path.as_ref()?;
        let current_dir = current_source.parent()?;
        let entries = fs::read_dir(current_dir)
            .ok()?
            .filter_map(Result::ok)
            .map(|entry| entry.path())
            .collect::<Vec<_>>();
        // File names are matched case-insensitively, which also covers the
        // lowercase-first-letter spelling of the module name.
        for ext in ["res", "ml"] {
            let candidate_name = format!("{module_name}.{ext}");
            if let Some(path) = entries.iter().find(|path| {
                path.file_name()
                    .and_then(|name| name.to_str())
                    .is_some_and(|name| name.eq_ignore_ascii_case(&candidate_name))
            }) {
                return Some(path.clone());
            }
        }

        None
    }
}

fn module_format_from_output_path(output_path: Option<&FsPath>) -> ModuleFormat {
    match output_path
        .and_then(|path| path.file_name())
        .and_then(|name| name.to_str())
    {
        Some(name) if name.ends_with(".mjs") => ModuleFormat::EsModule,
        _ => ModuleFormat::CommonJs,
    }
}

/// OCaml `Filename.concat`.
fn filename_concat(dir: &str, file: &str) -> String {
    if dir.is_empty() || dir.ends_with('/') {
        format!("{dir}{file}")
    } else {
        format!("{dir}/{file}")
    }
}

fn module_system_compatible(dep: CmjPackageModuleSystem, query: ModuleFormat) -> bool {
    matches!(
        (dep, query),
        (CmjPackageModuleSystem::CommonJs, ModuleFormat::CommonJs)
            | (CmjPackageModuleSystem::EsModule, ModuleFormat::EsModule)
    )
}

fn js_name_of_module_name(module_name: &str, file_case: CmjFileCase, suffix: &str) -> String {
    let name = match file_case {
        CmjFileCase::Upper => module_name.to_string(),
        CmjFileCase::Little => uncapitalize_ascii(module_name),
    };
    if let Some(index) = name.rfind('-') {
        format!("{}{}", &name[..index], suffix)
    } else {
        format!("{name}{suffix}")
    }
}

fn uncapitalize_ascii(name: &str) -> String {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return String::new();
    };
    format!("{}{}", first.to_ascii_lowercase(), chars.as_str())
}

/// The suffix of the output file: what follows the source file's stem in its
/// name (`Foo.res` -> `Foo.res.js` is `.res.js`), else guessed from the name.
fn output_suffix_from_paths(source_path: Option<&FsPath>, output_path: Option<&FsPath>) -> String {
    let stem = source_path
        .and_then(|path| path.file_stem())
        .and_then(|stem| stem.to_str());
    let name = output_path
        .and_then(|path| path.file_name())
        .and_then(|name| name.to_str());
    if let (Some(stem), Some(name)) = (stem, name)
        && let Some(suffix) = name.strip_prefix(stem)
        && suffix.starts_with('.')
    {
        return suffix.to_string();
    }
    output_suffix_from_path(output_path)
}

fn output_suffix_from_path(output_path: Option<&FsPath>) -> String {
    match output_path
        .and_then(|path| path.file_name())
        .and_then(|name| name.to_str())
    {
        Some(name) if name.ends_with(".mjs") => ".mjs".to_string(),
        Some(name) if name.ends_with(".cjs") => ".cjs".to_string(),
        Some(name) if name.ends_with(".bs.js") => ".bs.js".to_string(),
        _ => ".js".to_string(),
    }
}

fn source_path_with_js_suffix(source_path: &FsPath, suffix: &str) -> Option<PathBuf> {
    let stem = source_path.file_stem()?.to_str()?;
    let mut output = source_path.to_path_buf();
    output.set_file_name(format!("{stem}{suffix}"));
    Some(output)
}

fn normalize_absolute_path(path: &FsPath) -> PathBuf {
    let base = if path.is_absolute() {
        path.to_path_buf()
    } else {
        crate::process_cwd::current_dir()
            .unwrap_or_else(|_| FsPath::new("."))
            .join(path)
    };
    normalize_lexical_path(base)
}

/// Whether `bytes` is an absolute Unix path with no empty, `.` or `..`
/// component and no trailing separator, so lexical normalization keeps it.
#[cfg(unix)]
fn is_normal_absolute_unix_path(bytes: &[u8]) -> bool {
    bytes.len() > 1
        && bytes[0] == b'/'
        && bytes[1..]
            .split(|&byte| byte == b'/')
            .all(|part| !part.is_empty() && part != b"." && part != b"..")
}

fn normalize_lexical_path(path: PathBuf) -> PathBuf {
    #[cfg(unix)]
    {
        use std::os::unix::ffi::OsStrExt;
        if is_normal_absolute_unix_path(path.as_os_str().as_bytes()) {
            return path;
        }
    }
    let mut prefix: Option<OsString> = None;
    let mut has_root = false;
    let mut parts: Vec<OsString> = Vec::new();

    for component in path.components() {
        match component {
            Component::Prefix(value) => prefix = Some(value.as_os_str().to_os_string()),
            Component::RootDir => has_root = true,
            Component::CurDir => {}
            Component::ParentDir => match parts.last() {
                Some(last) if last != ".." => {
                    parts.pop();
                }
                _ if !has_root && prefix.is_none() => parts.push(OsString::from("..")),
                _ => {}
            },
            Component::Normal(part) => parts.push(part.to_os_string()),
        }
    }

    let mut normalized = PathBuf::new();
    if let Some(prefix) = prefix {
        normalized.push(prefix);
    }
    if has_root {
        normalized.push(std::path::MAIN_SEPARATOR.to_string());
    }
    for part in parts {
        normalized.push(part);
    }

    if normalized.as_os_str().is_empty() && !has_root {
        PathBuf::from(".")
    } else {
        normalized
    }
}

fn relative_path_between(base_dir: &FsPath, target: &FsPath) -> Option<PathBuf> {
    #[cfg(unix)]
    {
        use std::os::unix::ffi::{OsStrExt, OsStringExt};
        let base = base_dir.as_os_str().as_bytes();
        let target = target.as_os_str().as_bytes();
        if is_normal_absolute_unix_path(base) && is_normal_absolute_unix_path(target) {
            // Both paths are already normal, so their components are the
            // `/`-separated parts; this is the general case below without
            // copying and re-parsing either path.
            let base_parts = base[1..].split(|&byte| byte == b'/');
            let mut target_parts = target[1..].split(|&byte| byte == b'/').peekable();
            let mut ups = 0usize;
            let mut diverged = false;
            for part in base_parts {
                if !diverged && target_parts.peek() == Some(&part) {
                    target_parts.next();
                } else {
                    diverged = true;
                    ups += 1;
                }
            }
            let mut relative = Vec::with_capacity(ups * 3 + target.len());
            for _ in 0..ups {
                if !relative.is_empty() {
                    relative.push(b'/');
                }
                relative.extend_from_slice(b"..");
            }
            for part in target_parts {
                if !relative.is_empty() {
                    relative.push(b'/');
                }
                relative.extend_from_slice(part);
            }
            return Some(PathBuf::from(std::ffi::OsString::from_vec(relative)));
        }
    }
    relative_path_between_general(base_dir, target)
}

fn relative_path_between_general(base_dir: &FsPath, target: &FsPath) -> Option<PathBuf> {
    let base = normalize_lexical_path(base_dir.to_path_buf());
    let target = normalize_lexical_path(target.to_path_buf());

    let base_components: Vec<_> = base.components().collect();
    let target_components: Vec<_> = target.components().collect();

    if matches!(
        (base_components.first(), target_components.first()),
        (Some(Component::Prefix(left)), Some(Component::Prefix(right)))
            if left.as_os_str() != right.as_os_str()
    ) {
        return None;
    }

    let shared_prefix = base_components
        .iter()
        .zip(target_components.iter())
        .take_while(|(left, right)| left == right)
        .count();

    let mut relative = PathBuf::new();
    for component in &base_components[shared_prefix..] {
        if matches!(component, Component::Normal(_)) {
            relative.push("..");
        }
    }
    for component in &target_components[shared_prefix..] {
        match component {
            Component::Normal(part) => relative.push(part),
            Component::CurDir => {}
            Component::ParentDir => relative.push(".."),
            Component::RootDir | Component::Prefix(_) => return None,
        }
    }

    Some(relative)
}

/// For loop direction
#[derive(Debug, Clone, Copy, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum ForDirection {
    /// i++
    Upto,
    /// i--
    Downto,
    /// for...of style
    Up,
}

/// Kind of call, matching OCaml's `Js_call_info.call_info`
/// (js_call_info.ml:27-34).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, serde::Serialize, serde::Deserialize)]
pub enum CallKind {
    /// Plain ML expression call. Mirrors OCaml's `Call_ml`.
    MlCall,
    /// Built-in runtime call. Mirrors OCaml's `Call_builtin_runtime`.
    BuiltinRuntime,
    /// External / FFI / uncurried call. Mirrors OCaml's `Call_na`. Printer
    /// must not apply the `pp_function` eta-reduction rewrite to these
    /// (js_dump.ml:299-344 gates on `Call_ml | Call_builtin_runtime`).
    #[default]
    Na,
}

/// Arity-known flag carried on the call site, matching OCaml's
/// `Js_call_info.arity` (js_call_info.ml:25). `Na` means unknown arity; the
/// `pp_function` rewrite wraps such calls with `Curry.__N(...)`. Rust does
/// not currently emit the Curry wrapper, so the printer's rewrite is gated
/// on `Full` only.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, serde::Serialize, serde::Deserialize)]
pub enum CallArity {
    /// Full application (arity matches).
    Full,
    /// Arity unknown.
    #[default]
    Na,
}

/// Call information for function calls
#[derive(Debug, Clone, Default, serde::Serialize, serde::Deserialize)]
pub struct CallInfo {
    /// Is this a method call?
    pub is_method: bool,
    /// Whether this call came from a transformed JSX node that should print
    /// back to preserved JSX syntax.
    pub call_transformed_jsx: bool,
    /// Call kind (ML / runtime / NA). Mirrors OCaml's `Js_call_info.call_info`.
    pub kind: CallKind,
    /// Arity-known flag. Mirrors OCaml's `Js_call_info.arity`.
    pub arity: CallArity,
    /// Additional metadata
    pub comment: Option<String>,
}

/// Raw JavaScript code info
#[derive(Debug, Clone, PartialEq, serde::Serialize, serde::Deserialize)]
pub struct JsRawInfo {
    /// The JavaScript code
    pub code: String,
    /// Is this a statement?
    pub is_stmt: bool,
}

/// A field excluded by object-rest destructuring.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct RecordRestField {
    pub label: String,
    pub ident: Option<Ident>,
}

/// Exports from a module
pub type Exports = Vec<Ident>;

/// Required (imported) modules
pub type RequiredModules = Vec<ModuleId>;

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::tempdir;
    #[cfg(unix)]
    #[test]
    fn relative_path_fast_path_matches_general_case() {
        use super::{relative_path_between, relative_path_between_general};
        use std::path::Path;
        let paths = [
            "/a",
            "/a/b",
            "/a/b/c",
            "/a/bc",
            "/a/.hidden/c",
            "/a/.hidden/d/e.js",
            "/x/y",
            "/a/b/c/d",
        ];
        for base in paths {
            for target in paths {
                assert_eq!(
                    relative_path_between(Path::new(base), Path::new(target)),
                    relative_path_between_general(Path::new(base), Path::new(target)),
                    "{base} -> {target}"
                );
            }
        }
        assert!(!super::is_normal_absolute_unix_path(b"/a/./b"));
        assert!(!super::is_normal_absolute_unix_path(b"/a/../b"));
        assert!(!super::is_normal_absolute_unix_path(b"/a//b"));
        assert!(!super::is_normal_absolute_unix_path(b"/a/"));
        assert!(super::is_normal_absolute_unix_path(b"/a/.b/..c"));
    }

    #[test]
    fn resolve_local_module_fallback_path_uses_sibling_source_file() {
        let project = tempdir().expect("failed to create tempdir");
        let source_dir = project.path().join("src");
        std::fs::create_dir_all(&source_dir).expect("failed to create source dir");

        let current_source = source_dir.join("include_side_effect.res");
        let target_source = source_dir.join("side_effect.res");
        std::fs::write(&current_source, "").expect("failed to write current source");
        std::fs::write(&target_source, "").expect("failed to write target source");

        let resolver = ModulePathResolver::from_compile_options(
            Some(current_source.to_str().expect("utf8 current source")),
            Some(source_dir.join("include_side_effect.mjs").as_path()),
            None,
            None,
            None,
            None,
            false,
        );
        let module = ModuleId {
            id: Ident::create_local("Side_effect"),
            kind: Kind::Ml,
            dynamic_import: false,
        };

        assert_eq!(
            resolver
                .resolve_local_module_fallback_path(module.id.name())
                .as_deref(),
            Some("./side_effect.mjs")
        );
    }

    fn sibling_resolver(
        output_name: &str,
        specs: &[JsPackageSpec],
    ) -> (tempfile::TempDir, ModulePathResolver) {
        let project = tempdir().expect("failed to create tempdir");
        let source_dir = project.path().join("src");
        std::fs::create_dir_all(&source_dir).expect("failed to create source dir");
        let current_source = source_dir.join("Current.res");
        std::fs::write(&current_source, "").expect("failed to write current source");
        std::fs::write(source_dir.join("Sibling.res"), "").expect("failed to write target source");
        let mut resolver = ModulePathResolver::from_compile_options(
            Some(current_source.to_str().expect("utf8 current source")),
            Some(source_dir.join(output_name).as_path()),
            Some(ModuleFormat::EsModule),
            None,
            None,
            None,
            false,
        );
        resolver.set_package_specs(specs);
        (project, resolver)
    }

    #[test]
    fn sibling_import_keeps_a_multi_part_suffix() {
        let (_project, resolver) = sibling_resolver("Current.res.js", &[]);
        assert_eq!(
            resolver
                .resolve_local_module_fallback_path("Sibling")
                .as_deref(),
            Some("./Sibling.res.js")
        );
    }

    #[test]
    fn sibling_import_follows_the_last_matching_package_spec() {
        // js_packages_info.ml:159 prepends each -bs-package-output, and
        // query_package_infos takes the first compatible one.
        let spec = |in_source, suffix: &str| JsPackageSpec {
            module_format: ModuleFormat::EsModule,
            in_source,
            out_of_source_dir: "es6".to_string(),
            suffix: suffix.to_string(),
        };
        let (_project, resolver) =
            sibling_resolver("Current.mjs", &[spec(true, ".mjs"), spec(false, ".res.js")]);
        assert_eq!(
            resolver
                .resolve_local_module_fallback_path("Sibling")
                .as_deref(),
            Some("./Sibling.res.js")
        );
    }
}
