//! `rescript verify`: run the checks of a project (docs/verify).
//!
//! A build type checks every `@law` and `@spec` and leaves it out of the
//! JavaScript.
//! After a build, this compiles each file that has checks once more, in
//! memory against the build's interfaces, with its checks kept as exports,
//! and writes the result next to the file's JavaScript as `<name>.verify`
//! with the same suffix. A runner (`rewatch/src/verify/runner.mjs`) then
//! loads those files under Node and runs each check. The extra files are
//! removed again, so a verify run leaves the build's output as it was.

use super::build_types::{BuildCommandState, SourceType, StoredAst};
use super::{compile, packages, parse};
use crate::helpers;
use anyhow::{Context, Result, anyhow};
use rescript_compiler::verify::Checks;
use std::path::{Path, PathBuf};

/// The runner, written into the project's `lib/verify` for Node to run.
const RUNNER: &str = include_str!("../verify/runner.mjs");

/// How `rescript verify` runs the checks.
pub struct Options {
    /// The seed of the random cases; the report prints it when a check fails.
    pub seed: u32,
    /// The number of random cases per law.
    pub cases: u32,
    /// The most states of a spec's machine to go through.
    pub states: u32,
    /// Whether the report is coloured.
    pub color: bool,
}

/// A file compiled with its checks kept.
struct Companion {
    /// The written JavaScript.
    file: PathBuf,
    /// The source, relative to the directory the command runs in.
    source: String,
    items: Vec<serde_json::Value>,
}

/// `Foo.res.mjs` -> `Foo.res.verify.mjs`.
fn companion_path(js: &Path) -> PathBuf {
    let extension = js.extension().and_then(|ext| ext.to_str()).unwrap_or("js");
    js.with_extension(format!("verify.{extension}"))
}

/// Whether a source can have a check. O(source bytes), with no parse.
fn mentions_check(source: &str) -> bool {
    source.contains("@law") || source.contains("@spec")
}

/// Compile one module with its checks kept. `None` when it has none.
fn compile_companion(
    build_state: &BuildCommandState,
    registry: &rescript_compiler::cmi::persistent_env::ModuleRegistry,
    module_name: &str,
    package: &packages::Package,
    relative: &Path,
    cwd: &Path,
) -> Result<Option<Companion>> {
    let path = Path::new(&package.path).join(relative);
    let source = compile::read_source_latin1(&path)?;
    if !mentions_check(&source) {
        return Ok(None);
    }
    let StoredAst::Structure(ast) = parse::parse_for_tooling(package, relative, build_state)? else {
        return Ok(None);
    };
    if !ast.arena.has_verify_annotations() {
        return Ok(None);
    }
    let mut options = compile::build_compiler_options(package, module_name, relative, build_state)?;
    let checks = Checks::kept();
    options.checks = checks.clone();
    // The project was type checked only; this file's JavaScript is wanted.
    options.check_only = false;
    let filename = helpers::ocaml_absname(&path).to_string_lossy().into_owned();
    // The file is compiled as if it had no interface: its checks are
    // exports of this copy only, which nothing but the runner loads.
    let compiled = rescript_compiler::driver::compile_preprocessed_structure_in_process(
        &ast.arena,
        &ast.structure,
        &filename,
        module_name,
        &options,
        registry,
        false,
    )
    .map_err(|error| anyhow!("{error:#}"))?;
    let Checks::Kept(items) = checks else {
        unreachable!("the checks are kept above")
    };
    let items: Vec<serde_json::Value> = items.lock().unwrap().iter().map(|item| item.to_json()).collect();
    if items.is_empty() {
        return Ok(None);
    }
    let output = compiled
        .js_outputs
        .first()
        .ok_or_else(|| anyhow!("{} compiled to no JavaScript file", path.display()))?;
    let file = companion_path(&output.path);
    std::fs::write(&file, &output.code).with_context(|| format!("failed to write {}", file.display()))?;
    let source = path
        .strip_prefix(cwd)
        .unwrap_or(&path)
        .to_string_lossy()
        .replace('\\', "/");
    Ok(Some(Companion { file, source, items }))
}

/// Run the checks of the project at `path`, which a build has just compiled,
/// print the report, and return the process exit code: 0 when every check
/// passed.
///
/// The files with checks are compiled against the project's interfaces in
/// memory. A build that found nothing to compile has loaded none, so the
/// project is type checked once more here, writing no files, as `rescript
/// doc` does; it keeps source locations, for the line of each check.
pub fn verify(path: &Path, plain_output: bool, options: &Options) -> Result<i32> {
    let mut build_state = super::initialize_build_with_mode(
        /* no_timing */ true,
        &None,
        /* show_progress */ false,
        path,
        plain_output,
        /* warn_error */ None,
        /* prod */ false,
        /* features */ None,
        crate::config::SourceMapCommand::Build,
        /* check_only */ true,
    )
    .with_context(|| "Could not initialize the build")?;
    build_state.print_warnings = false;
    build_state.diagnostic_locations = true;
    super::incremental_build_without_lock(
        &mut build_state,
        /* no_timing */ true,
        /* initial_build */ true,
        /* show_progress */ false,
        /* only_incremental */ false,
        plain_output,
        super::CompilerInfoWrite::WithRecord,
    )
    .map_err(|error| anyhow!("{error}"))?;
    let code = verify_built(&build_state, options);
    // A one-shot command: let the OS reclaim the build graph at exit.
    std::mem::forget(build_state);
    code
}

fn verify_built(build_state: &BuildCommandState, options: &Options) -> Result<i32> {
    let cwd = std::env::current_dir()?;
    let cwd = cwd.canonicalize().unwrap_or(cwd);
    let registry = build_state.snapshot_module_registry();
    let mut sources: Vec<(&str, &packages::Package, &Path)> = Vec::new();
    for (module_name, module) in build_state.modules.iter() {
        let SourceType::SourceFile(source_file) = &module.source_type else {
            continue;
        };
        let Some(package) = build_state.packages.get(&module.package_name) else {
            continue;
        };
        // The checks of installed dependencies are their authors' to run.
        if !(package.is_root || package.is_local_dep) {
            continue;
        }
        sources.push((module_name, package, source_file.implementation.path.as_path()));
    }
    sources.sort_by(|a, b| (&a.1.path, a.2).cmp(&(&b.1.path, b.2)));

    let mut companions = Vec::new();
    let mut failure = None;
    for (module_name, package, relative) in sources {
        match compile_companion(build_state, &registry, module_name, package, relative, &cwd) {
            Ok(Some(companion)) => companions.push(companion),
            Ok(None) => {}
            Err(error) => {
                failure = Some(error);
                break;
            }
        }
    }
    let result = match failure {
        Some(error) => Err(error),
        None if companions.is_empty() => {
            println!(
                "No checks found: mark a property of the program with @law, or a state machine with @spec."
            );
            Ok(0)
        }
        None => run(build_state, &companions, options),
    };
    for companion in &companions {
        let _ = std::fs::remove_file(&companion.file);
    }
    result
}

/// Write the runner and its manifest, and run them under Node.
fn run(build_state: &BuildCommandState, companions: &[Companion], options: &Options) -> Result<i32> {
    let root = build_state
        .packages
        .values()
        .find(|package| package.is_root)
        .ok_or_else(|| anyhow!("the build has no root package"))?;
    let dir = Path::new(&root.path).join("lib").join("verify");
    std::fs::create_dir_all(&dir).with_context(|| format!("failed to create {}", dir.display()))?;
    let runner = dir.join("runner.mjs");
    let manifest = dir.join("manifest.json");
    std::fs::write(&runner, RUNNER)?;
    let modules: Vec<serde_json::Value> = companions
        .iter()
        .map(|companion| {
            serde_json::json!({
                "file": companion.file,
                "source": companion.source,
                "items": companion.items,
            })
        })
        .collect();
    std::fs::write(
        &manifest,
        serde_json::to_string(&serde_json::json!({
            "seed": options.seed,
            "cases": options.cases,
            "states": options.states,
            "color": options.color,
            "modules": modules,
        }))?,
    )?;
    let status = std::process::Command::new("node")
        .arg(&runner)
        .arg(&manifest)
        .status()
        .context("failed to run `node`, which runs the checks: is Node.js installed?")?;
    Ok(status.code().unwrap_or(1))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_companion_keeps_the_suffix() {
        assert_eq!(
            companion_path(Path::new("/app/src/Cart.res.mjs")),
            Path::new("/app/src/Cart.res.verify.mjs")
        );
        assert_eq!(
            companion_path(Path::new("/app/lib/js/src/Cart.js")),
            Path::new("/app/lib/js/src/Cart.verify.js")
        );
    }

    #[test]
    fn a_source_without_the_attribute_is_not_parsed() {
        assert!(mentions_check("@law\nlet a = () => true"));
        assert!(mentions_check("@spec\nlet a: Spec.t<int, bool> = machine"));
        assert!(!mentions_check("let law = 1"));
    }
}
