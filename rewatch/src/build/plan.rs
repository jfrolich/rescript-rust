//! The hidden `rescript build-reference` command (test-only).
//!
//! Builds compile in-process and write no `.ast`/`.cmi`/`.cmj`/`.cmt` files.
//! The parity scripts still need a reference build by the OCaml `bsc`, which
//! reads and writes those files. This runs that file-backed build with a
//! given `bsc` executable: for every module, after the modules it depends
//! on, the `bsc` command lines (parse to `.ast`, compile the interface,
//! compile the implementation), copying the artifacts into `lib/ocaml` after
//! each command so dependents find them. Normal builds never run a compiler
//! executable.

use super::build_types::*;
use super::{compile, deps, mark_modules_dirty, packages, parse};
use crate::config::SourceMapCommand;
use crate::helpers;
use crate::project_context::ProjectContext;
use ahash::{AHashMap, AHashSet};
use anyhow::{Result, anyhow};
use std::path::{Path, PathBuf};

/// One module of the build. Run `commands` in order, each with `bsc` and the
/// working directory `cwd`, after the steps of every module in `deps`; after
/// each command copy each `(from, to)` of `copies` (a missing `from` is
/// skipped).
struct Step {
    module: String,
    package: String,
    deps: Vec<String>,
    cwd: PathBuf,
    /// Directories to create before running the commands.
    mkdirs: Vec<PathBuf>,
    commands: Vec<Vec<String>>,
    copies: Vec<(PathBuf, PathBuf)>,
}

/// Build the project at `path` with the `bsc` executable `bsc`. Prints the
/// failures to stderr and returns whether every module built. Each package's
/// compiler output (colours stripped) goes to its `lib/bs/.compiler.log` as a
/// `rescript build` writes it (compile.rs): errors as modules fail, then the
/// warnings sorted by module name.
///
/// Each `(spec, executable)` of `ppx_overrides` runs `executable` for a
/// configured PPX whose resolved path ends in `spec` (for instance
/// `@jfrolich/ppx-spice/ppx`), so the reference can run the PPX version the
/// compiler's builtin port follows instead of the one a project installed.
pub fn build_reference(
    path: &Path,
    bsc: &Path,
    prod: bool,
    ppx_overrides: &[(String, PathBuf)],
) -> Result<bool> {
    use rayon::prelude::*;
    let bsc = std::fs::canonicalize(bsc)?;
    let steps = steps(path, prod, ppx_overrides)?;
    let index: AHashMap<&str, usize> = steps
        .iter()
        .enumerate()
        .map(|(i, step)| (step.module.as_str(), i))
        .collect();
    // 0: pending, 1: built, 2: failed or skipped.
    let mut state = vec![0u8; steps.len()];
    let mut failures = Vec::new();
    // Per package build folder, the errors in build order and the warnings
    // with their module names.
    let mut logs: Vec<(PathBuf, String, Vec<(String, String)>)> = Vec::new();
    for step in &steps {
        if !logs.iter().any(|(dir, _, _)| *dir == step.cwd) {
            logs.push((step.cwd.clone(), String::new(), Vec::new()));
        }
    }
    loop {
        let mut ready = Vec::new();
        for (i, step) in steps.iter().enumerate() {
            if state[i] != 0 {
                continue;
            }
            let deps: Vec<u8> = step
                .deps
                .iter()
                .filter_map(|dep| index.get(dep.as_str()))
                .map(|&d| state[d])
                .collect();
            if deps.contains(&2) {
                state[i] = 2;
            } else if !deps.contains(&0) {
                ready.push(i);
            }
        }
        if ready.is_empty() {
            break;
        }
        let results: Vec<(usize, StepOutput)> = ready
            .par_iter()
            .map(|&i| (i, run_step(&bsc, &steps[i])))
            .collect();
        for (i, output) in results {
            state[i] = if output.failure.is_some() { 2 } else { 1 };
            if let Some((_, errors, warnings)) = logs.iter_mut().find(|(dir, _, _)| *dir == steps[i].cwd) {
                errors.push_str(&output.error);
                if !output.warnings.is_empty() {
                    warnings.push((steps[i].module.clone(), output.warnings));
                }
            }
            failures.extend(output.failure);
        }
    }
    for (dir, errors, warnings) in &mut logs {
        warnings.sort_by(|a, b| a.0.cmp(&b.0));
        let mut log = std::mem::take(errors);
        for (_, warning) in warnings.iter() {
            log.push_str(warning);
        }
        let log = format!("#Start(0)\n{}#Done(0)\n", super::logs::escape_colours(&log));
        if let Err(err) = std::fs::write(dir.join(".compiler.log"), log) {
            eprintln!("{}: {err}", dir.display());
        }
    }
    let built = state.iter().filter(|&&s| s == 1).count();
    for failure in &failures {
        eprintln!("{failure}");
    }
    println!("OCaml reference build: {built} of {} modules built", steps.len());
    Ok(built == steps.len())
}

struct StepOutput {
    /// What the successful commands printed to stderr.
    warnings: String,
    /// What the failing command printed to stderr.
    error: String,
    /// The report of the failing command, if one failed.
    failure: Option<String>,
}

/// Run one step's commands, stopping at the first that fails.
fn run_step(bsc: &Path, step: &Step) -> StepOutput {
    let mut output = StepOutput {
        warnings: String::new(),
        error: String::new(),
        failure: None,
    };
    output.failure = run_step_commands(bsc, step, &mut output);
    output
}

fn run_step_commands(bsc: &Path, step: &Step, out: &mut StepOutput) -> Option<String> {
    for dir in std::iter::once(&step.cwd).chain(&step.mkdirs) {
        if let Err(err) = std::fs::create_dir_all(dir) {
            return Some(format!("{}: {}\n{err}", step.package, step.module));
        }
    }
    for args in &step.commands {
        let output = match std::process::Command::new(bsc)
            .args(args)
            .current_dir(&step.cwd)
            .output()
        {
            Ok(output) => output,
            Err(err) => return Some(format!("{}: {}\n{err}", step.package, step.module)),
        };
        if !output.status.success() {
            out.error.push_str(&String::from_utf8_lossy(&output.stderr));
            return Some(format!(
                "{}: {}\n{}{}",
                step.package,
                step.module,
                String::from_utf8_lossy(&output.stderr),
                String::from_utf8_lossy(&output.stdout)
            ));
        }
        out.warnings.push_str(&String::from_utf8_lossy(&output.stderr));
        // Publish what each command wrote before the next one runs: an
        // implementation compile finds its interface's .cmi in lib/ocaml.
        for (from, to) in &step.copies {
            if from.exists() {
                let _ = std::fs::copy(from, to);
            }
        }
    }
    None
}

/// The project at `path` with every module parsed and its dependencies
/// read, every module marked dirty. Discovers the packages without
/// `initialize_build`: its compiler check and cleanup would delete the build
/// folders (and the runtime's `lib/ocaml` sources the in-process build reads).
fn parsed_state(path: &Path, prod: bool) -> Result<BuildCommandState> {
    let project_context = ProjectContext::new(path)?;
    let compiler = super::get_compiler_info(&project_context)?;
    let packages = packages::make(&None, &project_context, false, prod, None)?;
    if !packages::validate_packages_dependencies(&packages) {
        return Err(anyhow!("Failed to validate package dependencies"));
    }
    let mut build_state = BuildCommandState::new(
        path.to_path_buf(),
        project_context,
        packages,
        compiler,
        None,
        None,
        SourceMapCommand::Build,
    );
    packages::parse_packages(&mut build_state)?;
    mark_modules_dirty(&mut build_state);
    parse::generate_asts(&mut build_state, || (), parse::ParseWarningLog::Append)?;
    let deleted = AHashSet::new();
    deps::get_deps(&mut build_state, &deleted);
    Ok(build_state)
}

/// Compile the project at `path` into a module registry, in process, writing
/// nothing to disk. `rescript bsc` resolves an `-I` package's modules in it.
pub fn build_in_memory(path: &Path) -> Result<rescript_compiler::cmi::persistent_env::ModuleRegistry> {
    let mut build_state = parsed_state(path, false)?;
    build_state.in_memory_only = true;
    let (errors, _warnings, _) = compile::compile(&mut build_state, false, || (), |_| ())?;
    if !errors.is_empty() {
        return Err(anyhow!("{errors}"));
    }
    Ok(build_state.snapshot_module_registry())
}

fn steps(path: &Path, prod: bool, ppx_overrides: &[(String, PathBuf)]) -> Result<Vec<Step>> {
    let build_state = parsed_state(path, prod)?;

    let mut steps = Vec::new();
    for module_name in topological_order(&build_state)? {
        let module = build_state.get_module(&module_name).unwrap();
        let package = build_state.get_package(&module.package_name).unwrap();
        let step = match &module.source_type {
            SourceType::MlMap(_) => mlmap_step(&build_state, package, &module_name)?,
            SourceType::SourceFile(source_file) => source_step(
                &build_state,
                package,
                module,
                &module_name,
                source_file,
                ppx_overrides,
            )?,
        };
        steps.push(step);
    }
    Ok(steps)
}

/// Modules in an order where each comes after its dependencies; namespace
/// maps first, as they only alias their members (`-no-alias-deps`).
fn topological_order(build_state: &BuildCommandState) -> Result<Vec<String>> {
    let mut names: Vec<&String> = build_state.modules.keys().collect();
    names.sort();
    let mut pending: AHashMap<&str, usize> = AHashMap::new();
    let mut dependents: AHashMap<&str, Vec<&str>> = AHashMap::new();
    for name in &names {
        let module = &build_state.modules[*name];
        let deps: Vec<&str> = if module.is_mlmap() {
            Vec::new()
        } else {
            module
                .deps
                .iter()
                .filter(|dep| build_state.modules.get(*dep).is_some_and(|dep| !dep.is_mlmap()))
                .map(String::as_str)
                .collect()
        };
        pending.insert(name.as_str(), deps.len());
        for dep in deps {
            dependents.entry(dep).or_default().push(name.as_str());
        }
    }
    let mut ready: Vec<&str> = names
        .iter()
        .filter(|name| build_state.modules[**name].is_mlmap())
        .map(|name| name.as_str())
        .collect();
    ready.extend(
        names
            .iter()
            .filter(|name| !build_state.modules[**name].is_mlmap() && pending[name.as_str()] == 0)
            .map(|name| name.as_str()),
    );
    let mut order = Vec::with_capacity(names.len());
    let mut next = 0;
    while next < ready.len() {
        let name = ready[next];
        next += 1;
        order.push(name.to_string());
        if let Some(waiting) = dependents.get(name) {
            let mut released: Vec<&str> = Vec::new();
            for dependent in waiting {
                let count = pending.get_mut(dependent).unwrap();
                *count -= 1;
                if *count == 0 {
                    released.push(dependent);
                }
            }
            released.sort();
            ready.extend(released);
        }
    }
    if order.len() != names.len() {
        return Err(anyhow!("the module graph has a cycle"));
    }
    Ok(order)
}

fn mlmap_step(build_state: &BuildCommandState, package: &packages::Package, namespace: &str) -> Result<Step> {
    let mut args = compile::get_runtime_path_args(&package.config, &build_state.project_context)?;
    args.extend(
        ["-w", "-49", "-color", "always", "-no-alias-deps"]
            .iter()
            .map(|arg| arg.to_string()),
    );
    args.push(format!("{namespace}.mlmap"));
    let build_path = package.get_build_path();
    let ocaml_path = package.get_ocaml_build_path();
    let copies = ["cmi", "cmt", "cmj", "mlmap"]
        .iter()
        .map(|ext| {
            (
                build_path.join(format!("{namespace}.{ext}")),
                ocaml_path.join(format!("{namespace}.{ext}")),
            )
        })
        .collect();
    Ok(Step {
        module: namespace.to_string(),
        package: package.name.clone(),
        deps: Vec::new(),
        cwd: build_path,
        mkdirs: vec![ocaml_path],
        commands: vec![args],
        copies,
    })
}

/// Only the test-only OCaml reference build needs an executable for spice.
fn reference_spice_args(
    args: &mut Vec<String>,
    config: &crate::config::Config,
    context: &ProjectContext,
    overrides: &[(String, PathBuf)],
) -> Result<()> {
    if !args.iter().any(|arg| arg == "-bs-builtin-spice-ppx") {
        return Ok(());
    }
    args.retain(|arg| arg != "-bs-builtin-spice-ppx");
    for flag in config.ppx_flags.iter().flatten() {
        let parts = match flag {
            crate::config::OneOrMore::Single(command) => std::slice::from_ref(command),
            crate::config::OneOrMore::Multiple(parts) => parts.as_slice(),
        };
        let Some(command) = parts.first() else { continue };
        let executable = if let Some((_, path)) = overrides.iter()
            .find(|(spec, _)| Path::new(command).ends_with(spec))
        {
            path.clone()
        } else {
            let spec = if command.starts_with('.') {
                format!("{}/{}", config.name, command)
            } else {
                command.clone()
            };
            helpers::try_package_path(config, context, &spec)?
        };
        args.push("-ppx".to_string());
        args.push(std::iter::once(executable.to_string_lossy().into_owned())
            .chain(parts[1..].iter().cloned()).collect::<Vec<_>>().join(" "));
    }
    Ok(())
}

fn source_step(
    build_state: &BuildCommandState,
    package: &packages::Package,
    module: &Module,
    module_name: &str,
    source_file: &SourceFile,
    ppx_overrides: &[(String, PathBuf)],
) -> Result<Step> {
    let project_context = &build_state.project_context;
    let build_path = package.get_build_path();
    let ocaml_path = package.get_ocaml_build_path();
    let implementation = &source_file.implementation.path;
    let interface = source_file.interface.as_ref().map(|interface| &interface.path);
    let gentype_dirs: &[PathBuf] = package.gentype_dirs.as_deref().unwrap_or(&[]);
    let mut mkdirs = vec![ocaml_path.clone()];
    let mut commands = Vec::new();
    let mut copies = Vec::new();

    // Parse each source file to its `.ast`/`.iast`.
    let mut parse = |source: &PathBuf| -> Result<PathBuf> {
        let contents = helpers::read_file(&Path::new(&package.path).join(source))?;
        let (ast_path, mut args) = parse::parser_args(
            project_context,
            &package.config,
            source,
            &contents,
            package.is_local_dep,
            None,
        )?;
        reference_spice_args(&mut args, &package.config, project_context, ppx_overrides)?;
        if let Some(parent) = build_path.join(&ast_path).parent() {
            mkdirs.push(parent.to_path_buf());
        }
        commands.push(args);
        copies.push((
            build_path.join(&ast_path),
            ocaml_path.join(ast_path.file_name().unwrap()),
        ));
        Ok(ast_path)
    };
    let iast_path = interface.map(&mut parse).transpose()?;
    let ast_path = parse(implementation)?;

    let compile = |ast_path: &Path, is_interface: bool| {
        compile::compiler_args(
            &package.config,
            &package.path,
            ast_path,
            implementation,
            is_interface,
            interface.is_some(),
            project_context,
            &Some(&build_state.packages),
            module.is_type_dev,
            package.is_local_dep,
            None,
            SourceMapCommand::Build,
            gentype_dirs,
        )
    };
    if let Some(iast_path) = &iast_path {
        commands.push(compile(iast_path, true)?);
    }
    commands.push(compile(&ast_path, false)?);

    // Publish the compiled interface where dependent packages look (`-I lib/ocaml`).
    let basename = helpers::file_path_to_compiler_asset_basename(implementation, &package.namespace);
    let dir = build_path.join(implementation.parent().unwrap_or(Path::new("")));
    let extensions: &[&str] = if interface.is_some() {
        &["cmi", "cmj", "cmt", "cmti"]
    } else {
        &["cmi", "cmj", "cmt"]
    };
    for ext in extensions {
        copies.push((
            dir.join(format!("{basename}.{ext}")),
            ocaml_path.join(format!("{basename}.{ext}")),
        ));
    }
    for source in interface.into_iter().chain([implementation]) {
        copies.push((
            Path::new(&package.path).join(source),
            ocaml_path.join(source.file_name().unwrap()),
        ));
    }

    // A namespace's step only compiles its alias map; a dependency on another
    // package's namespace also needs that package's members (the map's deps).
    let mut deps: Vec<String> = Vec::new();
    for dep in &module.deps {
        let Some(dep_module) = build_state.modules.get(dep) else {
            continue;
        };
        deps.push(dep.clone());
        if dep_module.is_mlmap() && dep_module.package_name != module.package_name {
            deps.extend(
                dep_module
                    .deps
                    .iter()
                    .filter(|member| build_state.modules.contains_key(*member))
                    .cloned(),
            );
        }
    }
    // Members of a namespace compile with `-bs-ns`, which opens the map:
    // its .cmi must be in lib/ocaml first.
    deps.extend(
        build_state
            .modules
            .iter()
            .filter(|(_, other)| other.is_mlmap() && other.package_name == module.package_name)
            .map(|(name, _)| name.clone()),
    );
    deps.sort();
    deps.dedup();
    mkdirs.sort();
    mkdirs.dedup();
    Ok(Step {
        module: module_name.to_string(),
        package: package.name.clone(),
        deps,
        cwd: build_path,
        mkdirs,
        commands,
        copies,
    })
}
