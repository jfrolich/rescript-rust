use super::build_types::*;
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
    write_signature_ast_current_with_extra_deps, write_structure_ast_current_with_extra_deps,
};
use rescript_compiler::parser::{Parser, code_frame, jsx_ppx, let_unwrap_ppx, module};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::{env, io::IsTerminal};

pub fn generate_asts(
    build_state: &mut BuildCommandState,
    inc: impl Fn() + std::marker::Sync,
) -> anyhow::Result<String> {
    let mut has_failure = false;
    let mut stderr = "".to_string();
    let use_rust_parser = build_state.use_rust_parser();
    let store_ast = build_state.dump_typed_sexp() && use_rust_parser;

    build_state
        .modules
        .par_iter()
        .map(|(module_name, module)| {
            debug!("Generating AST for module: {module_name}");
            let package = build_state
                .get_package(&module.package_name)
                .expect("Package not found");
            match &module.source_type {
                SourceType::MlMap(_mlmap) => {
                    let path = package.get_mlmap_path();
                    (
                        module_name.to_owned(),
                        Ok((Path::new(&path).to_path_buf(), None, None)),
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
                        inc();
                        let ast_result = generate_ast(
                            package.to_owned(),
                            &source_file.implementation.path.to_owned(),
                            build_state,
                            build_state.get_warn_error_override(),
                            use_rust_parser,
                            store_ast,
                        )
                        .map_err(|e| e.to_string());

                        let iast_result = match source_file.interface.as_ref().map(|i| i.path.to_owned()) {
                            Some(interface_file_path) => {
                                match generate_ast(
                                    package.to_owned(),
                                    &interface_file_path.to_owned(),
                                    build_state,
                                    build_state.get_warn_error_override(),
                                    use_rust_parser,
                                    store_ast,
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
                            Ok((
                                PathBuf::from(helpers::get_basename(&source_file.implementation.path))
                                    .with_extension("ast"),
                                None,
                                None,
                            )),
                            Ok(source_file.interface.as_ref().map(|i| {
                                (
                                    PathBuf::from(helpers::get_basename(&i.path)).with_extension("iast"),
                                    None,
                                    None,
                                )
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
            Result<(PathBuf, Option<helpers::StdErr>, Option<super::build_types::StoredAst>), String>,
            Result<Option<(PathBuf, Option<helpers::StdErr>, Option<super::build_types::StoredAst>)>, String>,
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
                        Ok((_path, Some(stderr_warnings), stored_ast)) if package.is_local_dep => {
                            source_file.implementation.parse_state = ParseState::Warning;
                            source_file.implementation.parse_dirty = true;
                            logs::append(package, &stderr_warnings);
                            stderr.push_str(&stderr_warnings);
                            if let Some(ast) = stored_ast {
                                build_state.stored_asts.lock().unwrap().insert(format!("{module_name}:impl"), ast);
                            }
                        }
                        Ok((_path, Some(_), stored_ast)) | Ok((_path, None, stored_ast)) => {
                            source_file.implementation.parse_state = ParseState::Success;
                            source_file.implementation.parse_dirty = false;
                            if let Some(ast) = stored_ast {
                                build_state.stored_asts.lock().unwrap().insert(format!("{module_name}:impl"), ast);
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
                        Ok(Some((_path, Some(stderr_warnings), stored_ast))) if package.is_local_dep => {
                            if let Some(interface) = source_file.interface.as_mut() {
                                interface.parse_state = ParseState::Warning;
                                interface.parse_dirty = true;
                            }
                            logs::append(package, &stderr_warnings);
                            stderr.push_str(&stderr_warnings);
                            if let Some(ast) = stored_ast {
                                build_state.stored_asts.lock().unwrap().insert(format!("{module_name}:intf"), ast);
                            }
                        }
                        Ok(Some((_, None, stored_ast))) | Ok(Some((_, Some(_), stored_ast))) => {
                            if let Some(interface) = source_file.interface.as_mut() {
                                interface.parse_state = ParseState::Success;
                                interface.parse_dirty = false;
                            }
                            if let Some(ast) = stored_ast {
                                build_state.stored_asts.lock().unwrap().insert(format!("{module_name}:intf"), ast);
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

fn generate_ast(
    package: Package,
    filename: &Path,
    build_state: &BuildState,
    warn_error_override: Option<String>,
    use_rust_parser: bool,
    store_ast: bool,
) -> anyhow::Result<(PathBuf, Option<helpers::StdErr>, Option<super::build_types::StoredAst>)> {
    let file_path = PathBuf::from(&package.path).join(filename);
    let contents = helpers::read_file(&file_path).expect("Error reading file");

    let build_path_abs = package.get_build_path();
    let ast_path = helpers::get_ast_path(filename);
    let ast_output_path = build_path_abs.join(&ast_path);
    let source_path_str = file_path.to_string_lossy().to_string();
    let bsc_flags = config::flatten_flags(&package.config.compiler_flags);
    let open_deps = open_dependencies_from_bsc_flags(&bsc_flags);
    let jsx_version = rust_parser_effective_jsx_version(build_state.project_context.get_root_config());
    let let_unwrap_enabled = rust_parser_let_unwrap_enabled(
        build_state.project_context.get_root_config(),
        &package.config,
    );

    // generate the dir of the ast_path (it mirrors the source file dir)
    let ast_parent_path = package.get_build_path().join(ast_path.parent().unwrap());
    helpers::create_path(&ast_parent_path);

    /* Create .ast */
    let result = if use_rust_parser {
        generate_ast_with_rust_parser(
            &file_path,
            &ast_output_path,
            &source_path_str,
            &open_deps,
            jsx_version,
            let_unwrap_enabled,
            store_ast,
        )
        .map(|(stderr, stored)| (ast_path.clone(), stderr, stored))
    } else {
        let (_expected_ast_path, parser_args) = parser_args(
            &build_state.project_context,
            &package.config,
            filename,
            &contents,
            package.is_local_dep,
            warn_error_override,
        )?;

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
                        Ok((ast_path.clone(), Some(stderr.to_string()), None))
                    } else {
                        Err(anyhow!("Error in {}:\n{}", package.name, stderr))
                    }
                } else {
                    Ok((ast_path.clone(), None, None))
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
    if let Ok((ast_path, _, _)) = &result {
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

fn rust_parser_effective_jsx_version(root_config: &Config) -> i32 {
    let version = root_config
        .jsx
        .as_ref()
        .and_then(|jsx| jsx.version)
        .unwrap_or(-1);
    let preserve = root_config
        .jsx
        .as_ref()
        .and_then(|jsx| jsx.preserve)
        .unwrap_or(false);

    if preserve { -1 } else { version }
}

fn rust_parser_let_unwrap_enabled(root_config: &Config, package_config: &Config) -> bool {
    package_config.has_experimental_feature(ExperimentalFeature::LetUnwrap)
        || root_config.has_experimental_feature(ExperimentalFeature::LetUnwrap)
}

fn diagnostics_to_stderr(parser: &Parser<'_>, source: &str, filename: &str) -> String {
    parser
        .diagnostics()
        .iter()
        .map(|diag| {
            code_frame::format_error(
                filename,
                source,
                &diag.start_pos,
                &diag.end_pos,
                &diag.explain_with_source(Some(source)),
            )
        })
        .collect::<Vec<String>>()
        .join("")
}

fn append_jsx_preprocessor_warnings(
    output: &mut String,
    source: &str,
    filename: &str,
    warnings: &[jsx_ppx::JsxPreprocessorWarning],
) {
    let use_color = should_enable_color();
    for warning in warnings {
        if use_color {
            output.push_str("\x1b[1;33mWarning number 22\x1b[0m\n  ");
        } else {
            output.push_str("Warning number 22\n  ");
        }

        let location = code_frame::format_location(filename, &warning.start_pos, &warning.end_pos);
        if use_color {
            output.push_str(&colorize_location(&location));
        } else {
            output.push_str(&location);
        }
        output.push_str("\n\n");
        output.push_str(&code_frame::print_warning(
            source,
            &warning.start_pos,
            &warning.end_pos,
        ));
        output.push_str("\n  ");
        output.push_str(&warning.message);
        output.push_str("\n\n");
    }
}

fn should_enable_color() -> bool {
    let term = env::var("TERM").unwrap_or_default();
    term != "dumb" && !term.is_empty() && std::io::stderr().is_terminal()
}

fn colorize_location(location: &str) -> String {
    if let Some((file, rest)) = location.split_once(':') {
        format!("\x1b[36m{}\x1b[0m:\x1b[2m{}\x1b[0m", file, rest)
    } else {
        location.to_string()
    }
}

fn source_bytes_to_latin1(bytes: &[u8]) -> String {
    bytes.iter().map(|&b| b as char).collect()
}

fn generate_ast_with_rust_parser(
    source_file: &Path,
    ast_output_path: &Path,
    source_path_for_ast: &str,
    extra_deps: &[String],
    jsx_version: i32,
    let_unwrap_enabled: bool,
    store_ast: bool,
) -> anyhow::Result<(Option<helpers::StdErr>, Option<super::build_types::StoredAst>)> {
    let bytes =
        std::fs::read(source_file).with_context(|| format!("Failed to read {}", source_file.display()))?;
    let source = source_bytes_to_latin1(&bytes);
    let mut parser = Parser::new(source_path_for_ast.to_string(), &source);
    let mut warnings = String::new();

    let is_interface = source_file
        .extension()
        .and_then(|s| s.to_str())
        .is_some_and(|ext| ext == "resi" || ext == "mli");

    if is_interface {
        let signature = module::parse_signature(&mut parser);
        if parser.has_errors() {
            let stderr = diagnostics_to_stderr(&parser, &source, source_path_for_ast);
            return if stderr.is_empty() {
                Err(anyhow!(
                    "Parse failed with {} error(s) in {}",
                    parser.diagnostics().len(),
                    source_file.display()
                ))
            } else {
                Err(anyhow!(stderr))
            };
        }

        // Apply per-file @@config({flags: [...]}) overrides
        let file_config =
            rescript_compiler::driver::extract_file_config_from_signature(&signature, parser.arena());
        let let_unwrap_enabled = let_unwrap_enabled || file_config.let_unwrap;
        let jsx_version = file_config.jsx_version.unwrap_or(jsx_version);

        let (signature, jsx_warnings) =
            jsx_ppx::transform_signature_with_warnings(signature, jsx_version, parser.arena_mut());
        append_jsx_preprocessor_warnings(
            &mut warnings,
            &source,
            source_path_for_ast,
            &jsx_warnings,
        );
        let signature = let_unwrap_ppx::rewrite_signature(
            &signature,
            parser.arena_mut(),
            let_unwrap_enabled,
        )
        .map_err(|e| anyhow!(e))?;

        write_signature_ast_current_with_extra_deps(
            ast_output_path,
            source_path_for_ast,
            parser.arena_mut(),
            &signature,
            extra_deps,
        )
        .with_context(|| format!("Failed to write {}", ast_output_path.display()))?;

        let stored = if store_ast {
            Some(super::build_types::StoredAst::Signature(parser.into_arena(), signature))
        } else {
            None
        };
        Ok(((!warnings.is_empty()).then_some(warnings), stored))
    } else {
        let structure = module::parse_structure(&mut parser);
        if parser.has_errors() {
            let stderr = diagnostics_to_stderr(&parser, &source, source_path_for_ast);
            return if stderr.is_empty() {
                Err(anyhow!(
                    "Parse failed with {} error(s) in {}",
                    parser.diagnostics().len(),
                    source_file.display()
                ))
            } else {
                Err(anyhow!(stderr))
            };
        }

        // Apply per-file @@config({flags: [...]}) overrides
        let file_config =
            rescript_compiler::driver::extract_file_config_from_structure(&structure, parser.arena());
        let let_unwrap_enabled = let_unwrap_enabled || file_config.let_unwrap;
        let jsx_version = file_config.jsx_version.unwrap_or(jsx_version);

        let (structure, jsx_warnings) =
            jsx_ppx::transform_structure_with_warnings(structure, jsx_version, parser.arena_mut());
        append_jsx_preprocessor_warnings(
            &mut warnings,
            &source,
            source_path_for_ast,
            &jsx_warnings,
        );
        let structure = let_unwrap_ppx::rewrite_structure(
            &structure,
            parser.arena_mut(),
            let_unwrap_enabled,
        )
        .map_err(|e| anyhow!(e))?;

        write_structure_ast_current_with_extra_deps(
            ast_output_path,
            source_path_for_ast,
            parser.arena_mut(),
            &structure,
            extra_deps,
        )
        .with_context(|| format!("Failed to write {}", ast_output_path.display()))?;

        let stored = if store_ast {
            Some(super::build_types::StoredAst::Structure(parser.into_arena(), structure))
        } else {
            None
        };
        Ok(((!warnings.is_empty()).then_some(warnings), stored))
    }
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
    use super::{
        open_dependencies_from_bsc_flags, rust_parser_effective_jsx_version,
        rust_parser_let_unwrap_enabled,
    };
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
    fn rust_parser_effective_jsx_version_uses_rescript_json_version() {
        let config = Config::new_from_json_string(
            r#"
            {
                "name": "demo",
                "sources": ["src"],
                "jsx": { "version": 4, "mode": "automatic" }
            }
            "#,
        )
        .unwrap();

        assert_eq!(rust_parser_effective_jsx_version(&config), 4);
    }

    #[test]
    fn rust_parser_effective_jsx_version_respects_preserve_flag() {
        let config = Config::new_from_json_string(
            r#"
            {
                "name": "demo",
                "sources": ["src"],
                "jsx": { "version": 4, "mode": "automatic", "preserve": true }
            }
            "#,
        )
        .unwrap();

        assert_eq!(rust_parser_effective_jsx_version(&config), -1);
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
