//! Editor tooling inside the watcher.
//!
//! Builds write no `.cmi`/`.cmt`/`.cmti` files and keep only the published
//! interfaces (the module registry) in memory. Editor tooling runs inside a
//! watch session instead: a command names a source file, which is
//! type-checked on demand against the registry, and the command works on the
//! resulting Rust typed tree.

use super::build_types::{BuildCommandState, SourceType, StoredAst};
use super::{compile, packages, parse};
use crate::helpers;
use anyhow::{Result, anyhow};
use std::path::{Path, PathBuf};

/// `path` with its nearest existing ancestor canonicalized, so tooling may
/// name a project through another spelling (e.g. a symlink).
fn canonical(path: &Path) -> PathBuf {
    let mut existing = path;
    let mut rest = Vec::new();
    while !existing.exists() {
        match (existing.file_name(), existing.parent()) {
            (Some(name), Some(parent)) => {
                rest.push(name);
                existing = parent;
            }
            _ => return path.to_path_buf(),
        }
    }
    let mut canonical = existing.canonicalize().unwrap_or_else(|_| existing.to_path_buf());
    for part in rest.iter().rev() {
        canonical.push(part);
    }
    canonical
}

/// A project source file of this watch session.
pub struct SourceModule<'a> {
    pub module_name: &'a str,
    pub package: &'a packages::Package,
    /// The implementation, relative to the package root.
    pub implementation: &'a Path,
    /// The interface, relative to the package root.
    pub interface: Option<&'a Path>,
    /// Whether `path` named the interface.
    pub is_interface: bool,
}

/// The module whose implementation or interface is at `path`.
pub fn source_module<'a>(build_state: &'a BuildCommandState, path: &Path) -> Option<SourceModule<'a>> {
    let path = canonical(path);
    build_state.modules.iter().find_map(|(module_name, module)| {
        let SourceType::SourceFile(source_file) = &module.source_type else {
            return None;
        };
        let package = build_state.packages.get(&module.package_name)?;
        let root = Path::new(&package.path);
        let implementation = source_file.implementation.path.as_path();
        let interface = source_file.interface.as_ref().map(|i| i.path.as_path());
        let is_interface = if root.join(implementation) == path {
            false
        } else if interface.is_some_and(|i| root.join(i) == path) {
            true
        } else {
            return None;
        };
        Some(SourceModule {
            module_name,
            package,
            implementation,
            interface,
            is_interface,
        })
    })
}

/// Type-check a module's implementation on demand, from its current source,
/// and run `query` on the result. The typed tree is not `Send`, so `query`
/// runs on the thread that type-checks.
pub fn with_typed_implementation<R: Send>(
    build_state: &BuildCommandState,
    source: &SourceModule<'_>,
    query: impl FnOnce(&rescript_compiler::driver::ToolingTypedModule) -> R + Send,
) -> Result<R> {
    let options = compile::build_compiler_options(
        source.package,
        source.module_name,
        source.implementation,
        build_state,
    )?;
    let StoredAst::Structure(ast) =
        parse::parse_for_tooling(source.package, source.implementation, build_state)?
    else {
        return Err(anyhow!(
            "expected an implementation AST for {}",
            source.implementation.display()
        ));
    };
    let filename = helpers::ocaml_absname(&Path::new(&source.package.path).join(source.implementation));
    let registry = build_state.snapshot_module_registry();
    // The compiler may recurse deeply on large modules; give it the stack
    // the build's compile workers get.
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .name("rewatch-tooling-typecheck".to_string())
            .stack_size(256 * 1024 * 1024)
            .spawn_scoped(scope, || {
                let typed = rescript_compiler::driver::typecheck_structure_for_tooling(
                    &ast.arena,
                    &ast.structure,
                    &filename.to_string_lossy(),
                    source.module_name,
                    &options,
                    &registry,
                );
                query(&typed)
            })
            .map_err(|err| anyhow!("could not start type-checking: {err}"))?
            .join()
            .map_err(|_| anyhow!("type-checking {} panicked", source.module_name))
    })
}

/// Run an editor tooling command (the arguments of `rescript-editor-analysis`,
/// relative paths resolved against `cwd`) and return what it prints.
pub fn run_command(_build_state: &BuildCommandState, cwd: PathBuf, args: Vec<String>) -> Result<Vec<u8>> {
    rescript_compiler::analysis::run(&rescript_compiler::analysis::Request { cwd, args })
        .map_err(|err| anyhow!(err))
}
