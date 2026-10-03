use super::build_types::*;
use super::compile::retain_critical_external_warnings;
use super::logs;
use super::namespaces;
use crate::build::packages::Package;
use crate::config;
use crate::config::{Config, ExperimentalFeature, OneOrMore};
use crate::helpers;
use crate::project_context::ProjectContext;
use ahash::AHashSet;
use anyhow::{Context, anyhow};
use log::debug;
use rayon::prelude::*;
use rescript_compiler::binary_ast::{
    Dependencies, extract_signature_deps, extract_structure_deps,
    write_signature_ast_current_with_extra_deps_and_builtin_ppx,
    write_structure_ast_current_with_extra_deps_and_builtin_ppx,
};
use rescript_compiler::parser::{Parser, module};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Arc;
use tracing::info_span;

struct GeneratedAst {
    path: PathBuf,
    stderr: Option<helpers::StdErr>,
    stored_ast: Option<super::build_types::StoredAst>,
    deps: Option<Dependencies>,
}

pub fn generate_asts(
    build_state: &mut BuildCommandState,
    inc: impl Fn() + std::marker::Sync,
) -> anyhow::Result<String> {
    let mut has_failure = false;
    let mut stderr = "".to_string();
    let use_rust_parser = build_state.use_rust_parser();
    let in_process = build_state.build_mode().is_in_process();
    if use_rust_parser {
        // `bsc` defaults to `-color always` (compiler/bsc/rescript_compiler_main.ml:494),
        // and the in-process frontend stands in for `bsc -bs-ast`.
        rescript_compiler::parser::code_frame::set_color_mode(
            rescript_compiler::parser::code_frame::ColorMode::Always,
        );
    }
    let store_ast = use_rust_parser && (in_process || build_state.dump_typed_sexp());

    // Count dirty modules for the span attribute only when a subscriber is
    // listening. Otherwise iterating every module every parse phase is pure
    // waste on the hot path.
    let parse_span = if tracing::enabled!(tracing::Level::INFO) {
        let dirty_modules = build_state
            .modules
            .values()
            .filter(|m| match &m.source_type {
                SourceType::SourceFile(sf) => {
                    sf.implementation.parse_dirty || sf.interface.as_ref().is_some_and(|i| i.parse_dirty)
                }
                SourceType::MlMap(mlmap) => mlmap.parse_dirty,
            })
            .count();
        info_span!("build.parse", dirty_modules = dirty_modules)
    } else {
        tracing::Span::none()
    };
    let _span = parse_span.enter();

    build_state
        .modules
        .par_iter()
        .map(|(module_name, module)| {
            let package = build_state
                .get_package(&module.package_name)
                .expect("Package not found");
            match &module.source_type {
                SourceType::MlMap(_mlmap) => {
                    let path = package.get_mlmap_path();
                    (
                        module_name.to_owned(),
                        Ok(GeneratedAst {
                            path: Path::new(&path).to_path_buf(),
                            stderr: None,
                            stored_ast: None,
                            deps: None,
                        }),
                        Ok(None),
                        false,
                    )
                }

                SourceType::SourceFile(source_file) => {
                    let (ast_result, iast_result, dirty) = if source_file.implementation.parse_dirty
                        || source_file
                            .interface
                            .as_ref()
                            .map(|i| i.parse_dirty)
                            .unwrap_or(false)
                    {
                        debug!("Generating AST for module: {module_name}");
                        inc();
                        let ast_result = generate_ast(
                            package,
                            &source_file.implementation.path.to_owned(),
                            build_state,
                            build_state.get_warn_error_override(),
                            use_rust_parser,
                            store_ast,
                            in_process,
                            &parse_span,
                        )
                        .map_err(|e| e.to_string());

                        let iast_result = match source_file.interface.as_ref().map(|i| i.path.to_owned()) {
                            Some(interface_file_path) => {
                                match generate_ast(
                                    package,
                                    &interface_file_path.to_owned(),
                                    build_state,
                                    build_state.get_warn_error_override(),
                                    use_rust_parser,
                                    store_ast,
                                    in_process,
                                    &parse_span,
                                ) {
                                    Ok(v) => Ok(Some(v)),
                                    Err(e) => Err(e.to_string()),
                                }
                            }
                            _ => Ok(None),
                        };

                        (ast_result, iast_result, true)
                    } else {
                        (
                            Ok(GeneratedAst {
                                path: PathBuf::from(helpers::get_basename(&source_file.implementation.path))
                                    .with_extension("ast"),
                                stderr: None,
                                stored_ast: None,
                                deps: None,
                            }),
                            Ok(source_file.interface.as_ref().map(|i| GeneratedAst {
                                path: PathBuf::from(helpers::get_basename(&i.path)).with_extension("iast"),
                                stderr: None,
                                stored_ast: None,
                                deps: None,
                            })),
                            false,
                        )
                    };

                    (module_name.to_owned(), ast_result, iast_result, dirty)
                }
            }
        })
        .collect::<Vec<(
            String,
            Result<GeneratedAst, String>,
            Result<Option<GeneratedAst>, String>,
            bool,
        )>>()
        .into_iter()
        .for_each(|(module_name, ast_result, iast_result, is_dirty)| {
            // Get package name first to avoid borrow checker issues
            let package_name = build_state
                .build_state
                .modules
                .get(&module_name)
                .map(|module| module.package_name.clone())
                .unwrap_or_else(|| {
                    eprintln!("Module not found: {module_name}");
                    String::new()
                });

            let package = build_state
                .build_state
                .packages
                .get(&package_name)
                .expect("Package not found");

            if let Some(module) = build_state.build_state.modules.get_mut(&module_name) {
                // if the module is dirty, mark it also compile_dirty
                // do NOT set to false if the module is not parse_dirty, it needs to keep
                // the compile_dirty flag if it was set before
                if is_dirty {
                    module.compile_dirty = true;
                    module.deps_dirty = true;
                }
                if let SourceType::SourceFile(ref mut source_file) = module.source_type {
                    // We get Err(x) when there is a parse error. When it's Ok(_, Some(
                    // stderr_warnings )), the outputs are warnings
                    match ast_result {
                        // In case of an internal dependency, we want to keep on
                        // propagating the warning with every compile. So we mark it as dirty for
                        // the next round
                        Ok(GeneratedAst {
                            stderr: Some(stderr_warnings),
                            stored_ast,
                            deps,
                            ..
                        }) if package.is_local_dep => {
                            source_file.implementation.parse_state = ParseState::Warning;
                            source_file.implementation.parse_dirty = true;
                            logs::append(package, &stderr_warnings);
                            stderr.push_str(&stderr_warnings);
                            if let Some(ast) = stored_ast {
                                build_state
                                    .stored_asts
                                    .lock()
                                    .unwrap()
                                    .insert(format!("{module_name}:impl"), ast);
                            }
                            if let Some(deps) = deps {
                                build_state
                                    .in_memory_deps
                                    .lock()
                                    .unwrap()
                                    .insert(format!("{module_name}:impl"), deps);
                            }
                        }
                        Ok(GeneratedAst {
                            stderr: Some(stderr_warnings),
                            stored_ast,
                            deps,
                            ..
                        }) => {
                            source_file.implementation.parse_state = ParseState::Success;
                            source_file.implementation.parse_dirty = false;
                            // External dep: surface only the critical warnings
                            // (e.g. legacy `(. ...)` uncurried syntax) so
                            // downstream users can report breakage upstream.
                            if let Some(kept) = retain_critical_external_warnings(&stderr_warnings) {
                                logs::append(package, &kept);
                                stderr.push_str(&kept);
                            }
                            if let Some(ast) = stored_ast {
                                build_state
                                    .stored_asts
                                    .lock()
                                    .unwrap()
                                    .insert(format!("{module_name}:impl"), ast);
                            }
                            if let Some(deps) = deps {
                                build_state
                                    .in_memory_deps
                                    .lock()
                                    .unwrap()
                                    .insert(format!("{module_name}:impl"), deps);
                            }
                        }
                        Ok(GeneratedAst {
                            stderr: None,
                            stored_ast,
                            deps,
                            ..
                        }) => {
                            source_file.implementation.parse_state = ParseState::Success;
                            source_file.implementation.parse_dirty = false;
                            if let Some(ast) = stored_ast {
                                build_state
                                    .stored_asts
                                    .lock()
                                    .unwrap()
                                    .insert(format!("{module_name}:impl"), ast);
                            }
                            if let Some(deps) = deps {
                                build_state
                                    .in_memory_deps
                                    .lock()
                                    .unwrap()
                                    .insert(format!("{module_name}:impl"), deps);
                            }
                        }
                        Err(err) => {
                            // Some compilation error
                            source_file.implementation.parse_state = ParseState::ParseError;
                            source_file.implementation.parse_dirty = true;
                            logs::append(package, &err);
                            has_failure = true;
                            stderr.push_str(&err);
                        }
                    };

                    // We get Err(x) when there is a parse error. When it's Ok(_, Some(( _path,
                    // stderr_warnings ))), the outputs are warnings
                    match iast_result {
                        // In case of an internal dependency, we want to keep on
                        // propagating the warning with every compile. So we mark it as dirty for
                        // the next round
                        Ok(Some(GeneratedAst {
                            stderr: Some(stderr_warnings),
                            stored_ast,
                            deps,
                            ..
                        })) if package.is_local_dep => {
                            if let Some(interface) = source_file.interface.as_mut() {
                                interface.parse_state = ParseState::Warning;
                                interface.parse_dirty = true;
                            }
                            logs::append(package, &stderr_warnings);
                            stderr.push_str(&stderr_warnings);
                            if let Some(ast) = stored_ast {
                                build_state
                                    .stored_asts
                                    .lock()
                                    .unwrap()
                                    .insert(format!("{module_name}:intf"), ast);
                            }
                            if let Some(deps) = deps {
                                build_state
                                    .in_memory_deps
                                    .lock()
                                    .unwrap()
                                    .insert(format!("{module_name}:intf"), deps);
                            }
                        }
                        Ok(Some(GeneratedAst {
                            stderr: Some(stderr_warnings),
                            stored_ast,
                            deps,
                            ..
                        })) => {
                            if let Some(interface) = source_file.interface.as_mut() {
                                interface.parse_state = ParseState::Success;
                                interface.parse_dirty = false;
                            }
                            if let Some(kept) = retain_critical_external_warnings(&stderr_warnings) {
                                logs::append(package, &kept);
                                stderr.push_str(&kept);
                            }
                            if let Some(ast) = stored_ast {
                                build_state
                                    .stored_asts
                                    .lock()
                                    .unwrap()
                                    .insert(format!("{module_name}:intf"), ast);
                            }
                            if let Some(deps) = deps {
                                build_state
                                    .in_memory_deps
                                    .lock()
                                    .unwrap()
                                    .insert(format!("{module_name}:intf"), deps);
                            }
                        }
                        Ok(Some(GeneratedAst {
                            stderr: None,
                            stored_ast,
                            deps,
                            ..
                        })) => {
                            if let Some(interface) = source_file.interface.as_mut() {
                                interface.parse_state = ParseState::Success;
                                interface.parse_dirty = false;
                            }
                            if let Some(ast) = stored_ast {
                                build_state
                                    .stored_asts
                                    .lock()
                                    .unwrap()
                                    .insert(format!("{module_name}:intf"), ast);
                            }
                            if let Some(deps) = deps {
                                build_state
                                    .in_memory_deps
                                    .lock()
                                    .unwrap()
                                    .insert(format!("{module_name}:intf"), deps);
                            }
                        }
                        Err(err) => {
                            // Some compilation error
                            if let Some(interface) = source_file.interface.as_mut() {
                                interface.parse_state = ParseState::ParseError;
                                interface.parse_dirty = true;
                            }
                            logs::append(package, &err);
                            has_failure = true;
                            stderr.push_str(&err);
                        }
                        Ok(None) => {
                            // The file had no interface file associated
                        }
                    }
                };
            }
        });

    // compile the mlmaps of dirty modules
    // first collect dirty packages
    let dirty_packages = build_state
        .modules
        .iter()
        .filter(|(_, module)| module.compile_dirty)
        .map(|(_, module)| module.package_name.clone())
        .collect::<AHashSet<String>>();

    // Collect package names first to avoid borrow checker issues
    let module_package_pairs = build_state.module_name_package_pairs();

    for (module_name, package_name) in module_package_pairs {
        if let Some(module) = build_state.build_state.modules.get_mut(&module_name) {
            let is_dirty = match &module.source_type {
                SourceType::MlMap(_) => {
                    if dirty_packages.contains(&package_name) {
                        if in_process {
                            // In-process builds synthesize namespace signatures directly into
                            // the module registry during compilation. The file-backed mlmap
                            // compiler only creates .cmi/.cmj/.cmt assets for subprocess mode.
                            true
                        } else {
                            let package = build_state
                                .build_state
                                .packages
                                .get(&package_name)
                                .expect("Package not found");
                            // probably better to do this in a different function
                            // specific to compiling mlmaps
                            let compile_path = package.get_mlmap_compile_path();
                            let mlmap_hash = helpers::compute_file_hash(Path::new(&compile_path));
                            if let Err(err) = namespaces::compile_mlmap(
                                &build_state.build_state.project_context,
                                package,
                                &module_name,
                                &build_state.build_state.compiler_info.bsc_path,
                            ) {
                                has_failure = true;
                                stderr.push_str(&format!("{err}\n"));
                            }
                            let mlmap_hash_after = helpers::compute_file_hash(Path::new(&compile_path));

                            let suffix = package
                                .namespace
                                .to_suffix()
                                .expect("namespace should be set for mlmap module");
                            let base_build_path = package.get_build_path().join(&suffix);
                            let base_ocaml_build_path = package.get_ocaml_build_path().join(&suffix);
                            let _ = std::fs::copy(
                                base_build_path.with_extension("cmi"),
                                base_ocaml_build_path.with_extension("cmi"),
                            );
                            let _ = std::fs::copy(
                                base_build_path.with_extension("cmt"),
                                base_ocaml_build_path.with_extension("cmt"),
                            );
                            let _ = std::fs::copy(
                                base_build_path.with_extension("cmj"),
                                base_ocaml_build_path.with_extension("cmj"),
                            );
                            let _ = std::fs::copy(
                                base_build_path.with_extension("mlmap"),
                                base_ocaml_build_path.with_extension("mlmap"),
                            );
                            match (mlmap_hash, mlmap_hash_after) {
                                (Some(digest), Some(digest_after)) => !digest.eq(&digest_after),
                                _ => true,
                            }
                        }
                    } else {
                        false
                    }
                }
                _ => false,
            };
            if is_dirty {
                module.compile_dirty = is_dirty;
            }
        }
    }

    if has_failure {
        Err(anyhow!(stderr))
    } else {
        Ok(stderr)
    }
}

pub fn parser_args(
    project_context: &ProjectContext,
    package_config: &Config,
    filename: &Path,
    contents: &str,
    is_local_dep: bool,
    warn_error_override: Option<String>,
) -> anyhow::Result<(PathBuf, Vec<String>)> {
    let root_config = project_context.get_root_config();
    let file = &filename;
    let ast_path = helpers::get_ast_path(file);
    let ppx_flags = config::flatten_ppx_flags(
        project_context,
        package_config,
        &filter_ppx_flags(&package_config.ppx_flags, contents),
    )?;
    let jsx_args = root_config.get_jsx_args();
    let jsx_module_args = root_config.get_jsx_module_args();
    let jsx_mode_args = root_config.get_jsx_mode_args();
    let jsx_preserve_args = root_config.get_jsx_preserve_args();
    let experimental_features_args = root_config.get_experimental_features_args();
    let bsc_flags = config::flatten_flags(&package_config.compiler_flags);
    let warning_args = package_config.get_warning_args(is_local_dep, warn_error_override);

    let file = PathBuf::from("..").join("..").join(file);

    Ok((
        ast_path.to_owned(),
        [
            ppx_flags,
            jsx_args,
            jsx_module_args,
            jsx_mode_args,
            jsx_preserve_args,
            experimental_features_args,
            warning_args,
            bsc_flags,
            vec![
                "-absname".to_string(),
                "-bs-ast".to_string(),
                "-o".to_string(),
                ast_path.to_string_lossy().to_string(),
                file.to_string_lossy().to_string(),
            ],
        ]
        .concat(),
    ))
}

fn make_parse_file_span(
    filename: &Path,
    package: &Package,
    parser_args: &[String],
    build_state: &BuildState,
    parent: &tracing::Span,
) -> tracing::Span {
    let module_name = helpers::file_path_to_module_name(filename, &package.namespace);
    let mut ppx_names: Vec<String> = Vec::new();
    let mut experimental: Vec<String> = Vec::new();
    for pair in parser_args.windows(2) {
        if pair[0] == "-ppx" {
            // Use the PPX executable's file name so paths like
            // `node_modules/foo/ppx.exe` reduce to `ppx.exe` cross-platform.
            let name = Path::new(&pair[1])
                .file_name()
                .map(|s| s.to_string_lossy().into_owned())
                .unwrap_or_else(|| pair[1].clone());
            ppx_names.push(name);
        } else if pair[0] == "-enable-experimental" {
            experimental.push(pair[1].clone());
        }
    }
    let ppx = ppx_names.join(",");
    let experimental = experimental.join(",");
    let root_config = build_state.get_root_config();
    let jsx = root_config.get_jsx_args().get(1).cloned().unwrap_or_default();
    let bsc_flags = config::flatten_flags(&package.config.compiler_flags).join(" ");
    info_span!(
        parent: parent,
        "build.parse_file",
        module = %module_name,
        package = %package.name,
        ppx = %ppx,
        experimental = %experimental,
        jsx = %jsx,
        bsc_flags = %bsc_flags,
    )
}

/// Parse one source file of `package` as the in-process build does, for an
/// on-demand compile (editor tooling). Reads the file's current contents.
pub(crate) fn parse_for_tooling(
    package: &Package,
    filename: &Path,
    build_state: &BuildCommandState,
) -> anyhow::Result<super::build_types::StoredAst> {
    let generated = generate_ast(
        package,
        filename,
        build_state,
        build_state.get_warn_error_override(),
        true,
        true,
        true,
        &tracing::Span::none(),
    )?;
    generated
        .stored_ast
        .ok_or_else(|| anyhow!("no AST for {}", filename.display()))
}

fn generate_ast(
    package: &Package,
    filename: &Path,
    build_state: &BuildState,
    warn_error_override: Option<String>,
    use_rust_parser: bool,
    store_ast: bool,
    in_process: bool,
    parent_span: &tracing::Span,
) -> anyhow::Result<GeneratedAst> {
    let file_path = PathBuf::from(&package.path).join(filename);

    let build_path_abs = package.get_build_path();
    let ast_path = helpers::get_ast_path(filename);
    let ast_output_path = build_path_abs.join(&ast_path);
    // `bsc -absname` names the source by its normalized absolute path.
    let source_path_str = helpers::ocaml_absname(&file_path).to_string_lossy().to_string();
    let bsc_flags = config::flatten_flags(&package.config.compiler_flags);
    let open_deps = open_dependencies_from_bsc_flags(&bsc_flags);
    // The Rust parser reads the source once, for both the ppx filter and
    // parsing.
    let source_bytes = if use_rust_parser {
        Some(std::fs::read(&file_path).with_context(|| format!("Failed to read {}", file_path.display()))?)
    } else {
        None
    };

    // The Rust parser runs the same frontend as `bsc -bs-ast` in process, so it
    // reads the flags OCaml's `-bs-ast` would receive (see `parser_args`).
    // `-ppx` rewriters from `ppx-flags`, as `parser_args` passes them to
    // `bsc -bs-ast`.
    let mut external_ppxs: Vec<String> = match &package.config.ppx_flags {
        Some(flags) if use_rust_parser && !flags.is_empty() => {
            let contents =
                std::str::from_utf8(source_bytes.as_deref().unwrap_or_default()).unwrap_or_default();
            let ppx_args = config::flatten_ppx_flags(
                &build_state.project_context,
                &package.config,
                &filter_ppx_flags(&package.config.ppx_flags, contents),
            )?;
            ppx_args
                .chunks(2)
                .filter(|pair| pair[0] == "-ppx")
                .map(|pair| pair[1].clone())
                .collect()
        }
        _ => Vec::new(),
    };
    // The builtin spice mapper implements `ppx-spice`, so run it in process
    // instead of spawning the configured executable for every module.
    let spice_ppx = !external_ppxs.is_empty() && {
        let before = external_ppxs.len();
        external_ppxs.retain(|command| !command.contains("spice"));
        external_ppxs.len() != before
    };
    let frontend_options = use_rust_parser.then(|| {
        let root_config = build_state.project_context.get_root_config();
        let flags = [
            root_config.get_jsx_args(),
            root_config.get_jsx_module_args(),
            root_config.get_jsx_mode_args(),
            root_config.get_jsx_preserve_args(),
            root_config.get_experimental_features_args(),
            package
                .config
                .get_warning_args(package.is_local_dep, warn_error_override.clone()),
            bsc_flags.clone(),
        ]
        .concat();
        let parsed = super::compile::parse_in_process_compiler_flags(&flags);
        rescript_compiler::driver::CompilerOptions {
            warning_specs: parsed.warning_specs,
            warning_error_specs: parsed.warning_error_specs,
            jsx_version: parsed.jsx_version,
            jsx_module: parsed.jsx_module.clone(),
            jsx_preserve: parsed.jsx_preserve,
            experimental_let_unwrap: parsed.experimental_let_unwrap
                || rust_parser_let_unwrap_enabled(root_config, &package.config),
            no_builtin_ppx: parsed.no_builtin_ppx,
            spice_ppx,
            external_ppxs,
            ..Default::default()
        }
    });

    let parser_args = if use_rust_parser {
        Vec::new()
    } else {
        let contents = helpers::read_file(&file_path).expect("Error reading file");
        let (_expected_ast_path, parser_args) = parser_args(
            &build_state.project_context,
            &package.config,
            filename,
            &contents,
            package.is_local_dep,
            warn_error_override,
        )?;
        parser_args
    };

    let _parse_span = if tracing::enabled!(tracing::Level::INFO) {
        make_parse_file_span(filename, package, &parser_args, build_state, parent_span).entered()
    } else {
        tracing::Span::none().entered()
    };

    // generate the dir of the ast_path (it mirrors the source file dir)
    if !in_process {
        let ast_parent_path = package.get_build_path().join(ast_path.parent().unwrap());
        helpers::create_path(&ast_parent_path);
    }

    /* Create .ast */
    let result = if use_rust_parser {
        generate_ast_with_rust_parser(
            &file_path,
            source_bytes.expect("Rust parser source"),
            &ast_output_path,
            &source_path_str,
            &open_deps,
            frontend_options.as_ref().expect("Rust parser options"),
            store_ast,
            in_process,
        )
        .map_err(|err| anyhow!("Error in {}:\n{}", package.name, err))
        .map(|(stderr, stored_ast, deps)| GeneratedAst {
            path: ast_path.clone(),
            stderr,
            stored_ast,
            deps,
        })
    } else {
        match Some(
            Command::new(&build_state.compiler_info.bsc_path)
                .current_dir(&build_path_abs)
                .args(parser_args)
                .output()
                .map_err(|e| {
                    anyhow!(
                        "Error running bsc for parsing {}: {}",
                        filename.to_string_lossy(),
                        e
                    )
                })?,
        ) {
            Some(res_to_ast) => {
                let stderr = String::from_utf8_lossy(&res_to_ast.stderr).to_string();

                if helpers::contains_ascii_characters(&stderr) {
                    if res_to_ast.status.success() {
                        Ok(GeneratedAst {
                            path: ast_path.clone(),
                            stderr: Some(stderr.to_string()),
                            stored_ast: None,
                            deps: None,
                        })
                    } else {
                        Err(anyhow!("Error in {}:\n{}", package.name, stderr))
                    }
                } else {
                    Ok(GeneratedAst {
                        path: ast_path.clone(),
                        stderr: None,
                        stored_ast: None,
                        deps: None,
                    })
                }
            }
            _ => {
                log::info!("Parsing file {}...", filename.display());

                Err(anyhow!(
                    "Could not find canonicalize_string_path for file {} in package {}",
                    filename.display(),
                    package.name
                ))
            }
        }
    };
    if !in_process && let Ok(GeneratedAst { path: ast_path, .. }) = &result {
        let _ = std::fs::copy(
            Path::new(&build_path_abs).join(ast_path),
            package.get_ocaml_build_path().join(ast_path.file_name().unwrap()),
        );
    }
    result
}

fn include_ppx(flag: &str, contents: &str) -> bool {
    if flag.contains("bisect") {
        return std::env::var("BISECT_ENABLE").is_ok();
    }

    if ((flag.contains("graphql-ppx") || flag.contains("graphql_ppx")) && !contents.contains("%graphql"))
        || (flag.contains("spice") && !contents.contains("@spice"))
        || (flag.contains("rescript-relay") && !contents.contains("%relay"))
        || (flag.contains("re-formality") && !contents.contains("%form"))
    {
        return false;
    };

    true
}

fn open_dependencies_from_bsc_flags(flags: &[String]) -> Vec<String> {
    let mut deps = Vec::new();
    let mut seen = AHashSet::new();
    let mut i = 0;
    while i < flags.len() {
        if flags[i] == "-open" {
            if let Some(dep) = flags.get(i + 1) {
                if seen.insert(dep.clone()) {
                    deps.push(dep.clone());
                }
            }
            i += 1;
        }
        i += 1;
    }
    deps
}

fn rust_parser_let_unwrap_enabled(root_config: &Config, package_config: &Config) -> bool {
    package_config.has_experimental_feature(ExperimentalFeature::LetUnwrap)
        || root_config.has_experimental_feature(ExperimentalFeature::LetUnwrap)
}

fn source_bytes_to_latin1(bytes: Vec<u8>) -> String {
    if bytes.is_ascii() {
        String::from_utf8(bytes).expect("ASCII source bytes should always be valid UTF-8")
    } else {
        bytes.into_iter().map(|b| b as char).collect()
    }
}

fn generate_ast_with_rust_parser(
    source_file: &Path,
    bytes: Vec<u8>,
    ast_output_path: &Path,
    source_path_for_ast: &str,
    extra_deps: &[String],
    options: &rescript_compiler::driver::CompilerOptions,
    store_ast: bool,
    in_process: bool,
) -> anyhow::Result<(
    Option<helpers::StdErr>,
    Option<super::build_types::StoredAst>,
    Option<Dependencies>,
)> {
    rescript_compiler::timing::measure(rescript_compiler::timing::Phase::Parse, || {
        let source = source_bytes_to_latin1(bytes);
        let mut parser = Parser::new(source_path_for_ast.to_string(), &source);
        // Frontend warning reports, in the order `bsc -bs-ast` prints them.
        let mut warnings = String::new();

        let is_interface = source_file
            .extension()
            .and_then(|s| s.to_str())
            .is_some_and(|ext| ext == "resi" || ext == "mli");

        if is_interface {
            let signature = module::parse_signature(&mut parser);
            let frontend = rescript_compiler::driver::run_interface_frontend(
                &mut parser,
                signature,
                &source,
                source_path_for_ast,
                options,
                &mut warnings,
            );
            let frontend = match frontend {
                Ok(frontend) => frontend,
                Err(err) => return Err(anyhow!("{warnings}{err}")),
            };
            // `bsc -bs-ast` exits 2 when a frontend warning is an error.
            if frontend.warnings_fatal {
                return Err(anyhow!(warnings));
            }
            let signature = frontend.signature;

            let deps = if in_process {
                let mut deps = extract_signature_deps(parser.arena(), &signature);
                deps.extend(extra_deps.iter().cloned());
                Some(deps)
            } else {
                write_signature_ast_current_with_extra_deps_and_builtin_ppx(
                    ast_output_path,
                    source_path_for_ast,
                    parser.arena_mut(),
                    &signature,
                    extra_deps,
                    false,
                )
                .with_context(|| format!("Failed to write {}", ast_output_path.display()))?;
                None
            };

            let stored = if store_ast {
                let mut arena = parser.into_arena();
                rescript_compiler::types::typecore::prepare_typecheck_arena(&mut arena);
                Some(super::build_types::StoredAst::Signature(Arc::new(
                    super::build_types::StoredSignatureAst {
                        arena,
                        signature,
                        source_len: source.len(),
                    },
                )))
            } else {
                None
            };
            Ok(((!warnings.is_empty()).then_some(warnings), stored, deps))
        } else {
            let structure = module::parse_structure(&mut parser);
            let frontend = rescript_compiler::driver::run_implementation_frontend(
                &mut parser,
                structure,
                &source,
                source_path_for_ast,
                options,
                &mut warnings,
            );
            let frontend = match frontend {
                Ok(frontend) => frontend,
                Err(err) => return Err(anyhow!("{warnings}{err}")),
            };
            if frontend.warnings_fatal {
                return Err(anyhow!(warnings));
            }
            let structure = frontend.structure;

            let (structure, deps) = if in_process {
                // The frontend already applied `no_export` (js_implementation.ml:130).
                let mut deps = extract_structure_deps(parser.arena(), &structure);
                deps.extend(extra_deps.iter().cloned());
                (structure, Some(deps))
            } else {
                write_structure_ast_current_with_extra_deps_and_builtin_ppx(
                    ast_output_path,
                    source_path_for_ast,
                    parser.arena_mut(),
                    &structure,
                    extra_deps,
                    false,
                )
                .with_context(|| format!("Failed to write {}", ast_output_path.display()))?;
                (structure, None)
            };

            let stored = if store_ast {
                let mut arena = parser.into_arena();
                rescript_compiler::types::typecore::prepare_typecheck_arena(&mut arena);
                Some(super::build_types::StoredAst::Structure(Arc::new(
                    super::build_types::StoredStructureAst {
                        arena,
                        structure,
                        source_len: source.len(),
                    },
                )))
            } else {
                None
            };
            Ok(((!warnings.is_empty()).then_some(warnings), stored, deps))
        }
    })
}

fn filter_ppx_flags(
    ppx_flags: &Option<Vec<OneOrMore<String>>>,
    contents: &str,
) -> Option<Vec<OneOrMore<String>>> {
    // get the environment variable "BISECT_ENABLE" if it exists set the filter to "bisect"
    ppx_flags.as_ref().map(|flags| {
        flags
            .iter()
            .filter(|flag| match flag {
                config::OneOrMore::Single(str) => include_ppx(str, contents),
                config::OneOrMore::Multiple(str) => include_ppx(str.first().unwrap(), contents),
            })
            .map(|x| x.to_owned())
            .collect::<Vec<OneOrMore<String>>>()
    })
}

#[cfg(test)]
mod tests {
    use super::{open_dependencies_from_bsc_flags, rust_parser_let_unwrap_enabled};
    use crate::config::Config;

    #[test]
    fn open_dependencies_extracts_and_dedups() {
        let flags = vec![
            "-open".to_string(),
            "TellaStd".to_string(),
            "-w".to_string(),
            "+a".to_string(),
            "-open".to_string(),
            "Foo.Bar".to_string(),
            "-open".to_string(),
            "TellaStd".to_string(),
        ];

        let deps = open_dependencies_from_bsc_flags(&flags);
        assert_eq!(deps, vec!["TellaStd".to_string(), "Foo.Bar".to_string()]);
    }

    #[test]
    fn open_dependencies_ignores_missing_arg() {
        let flags = vec!["-open".to_string()];
        let deps = open_dependencies_from_bsc_flags(&flags);
        assert!(deps.is_empty());
    }

    #[test]
    fn rust_parser_let_unwrap_enabled_from_package_config() {
        let root = Config::new_from_json_string(
            r#"
            {
                "name": "root",
                "sources": ["src"]
            }
            "#,
        )
        .unwrap();
        let package = Config::new_from_json_string(
            r#"
            {
                "name": "pkg",
                "sources": ["src"],
                "experimental-features": { "LetUnwrap": true }
            }
            "#,
        )
        .unwrap();

        assert!(rust_parser_let_unwrap_enabled(&root, &package));
    }

    #[test]
    fn rust_parser_let_unwrap_enabled_from_root_config() {
        let root = Config::new_from_json_string(
            r#"
            {
                "name": "root",
                "sources": ["src"],
                "experimental-features": { "LetUnwrap": true }
            }
            "#,
        )
        .unwrap();
        let package = Config::new_from_json_string(
            r#"
            {
                "name": "pkg",
                "sources": ["src"]
            }
            "#,
        )
        .unwrap();

        assert!(rust_parser_let_unwrap_enabled(&root, &package));
    }
}
