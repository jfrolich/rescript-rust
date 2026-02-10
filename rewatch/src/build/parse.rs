use super::build_types::*;
use super::logs;
use super::namespaces;
use crate::build::packages::Package;
use crate::config;
use crate::config::{Config, OneOrMore};
use crate::helpers;
use crate::project_context::ProjectContext;
use ahash::AHashSet;
use anyhow::{Context, anyhow};
use log::debug;
use rayon::prelude::*;
use rescript_compiler::binary_ast::{
    write_signature_ast_current_with_extra_deps, write_structure_ast_current_with_extra_deps,
};
use rescript_compiler::parser::{Parser, code_frame, module};
use std::path::{Path, PathBuf};
use std::process::Command;

pub fn generate_asts(
    build_state: &mut BuildCommandState,
    inc: impl Fn() + std::marker::Sync,
) -> anyhow::Result<String> {
    let mut has_failure = false;
    let mut stderr = "".to_string();
    let use_rust_parser = build_state.use_rust_parser();

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
                        Ok((Path::new(&path).to_path_buf(), None)),
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
                            )),
                            Ok(source_file.interface.as_ref().map(|i| {
                                (
                                    PathBuf::from(helpers::get_basename(&i.path)).with_extension("iast"),
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
            Result<(PathBuf, Option<helpers::StdErr>), String>,
            Result<Option<(PathBuf, Option<helpers::StdErr>)>, String>,
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
                        Ok((_path, Some(stderr_warnings))) if package.is_local_dep => {
                            source_file.implementation.parse_state = ParseState::Warning;
                            source_file.implementation.parse_dirty = true;
                            logs::append(package, &stderr_warnings);
                            stderr.push_str(&stderr_warnings);
                        }
                        Ok((_path, Some(_))) | Ok((_path, None)) => {
                            source_file.implementation.parse_state = ParseState::Success;
                            source_file.implementation.parse_dirty = false;
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
                        Ok(Some((_path, Some(stderr_warnings)))) if package.is_local_dep => {
                            if let Some(interface) = source_file.interface.as_mut() {
                                interface.parse_state = ParseState::Warning;
                                interface.parse_dirty = true;
                            }
                            logs::append(package, &stderr_warnings);
                            stderr.push_str(&stderr_warnings);
                        }
                        Ok(Some((_, None))) | Ok(Some((_, Some(_)))) => {
                            if let Some(interface) = source_file.interface.as_mut() {
                                interface.parse_state = ParseState::Success;
                                interface.parse_dirty = false;
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
) -> anyhow::Result<(PathBuf, Option<helpers::StdErr>)> {
    let file_path = PathBuf::from(&package.path).join(filename);
    let contents = helpers::read_file(&file_path).expect("Error reading file");

    let build_path_abs = package.get_build_path();
    let ast_path = helpers::get_ast_path(filename);
    let ast_output_path = build_path_abs.join(&ast_path);
    let source_path = source_file_for_bsc_ast(filename);
    let source_path_str = source_path.to_string_lossy().to_string();
    let bsc_flags = config::flatten_flags(&package.config.compiler_flags);
    let open_deps = open_dependencies_from_bsc_flags(&bsc_flags);

    // generate the dir of the ast_path (it mirrors the source file dir)
    let ast_parent_path = package.get_build_path().join(ast_path.parent().unwrap());
    helpers::create_path(&ast_parent_path);

    /* Create .ast */
    let result = if use_rust_parser {
        let filtered_ppx_flags = filter_ppx_flags(&package.config.ppx_flags, &contents);
        let warning = first_unsupported_ppx_for_rust_parser(&filtered_ppx_flags).map(|unsupported_ppx| {
            format!(
                "Warning: Rust parser mode (--rust) does not run external ppx `{}` for {} in package {}. Continuing with Rust parser output.\n",
                unsupported_ppx,
                filename.display(),
                package.name
            )
        });
        generate_ast_with_rust_parser(&file_path, &ast_output_path, &source_path_str, &open_deps)
            .map(|stderr| (ast_path.clone(), merge_warning_with_stderr(warning, stderr)))
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
                        Ok((ast_path.clone(), Some(stderr.to_string())))
                    } else {
                        Err(anyhow!("Error in {}:\n{}", package.name, stderr))
                    }
                } else {
                    Ok((ast_path.clone(), None))
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
    if let Ok((ast_path, _)) = &result {
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

fn source_file_for_bsc_ast(filename: &Path) -> PathBuf {
    PathBuf::from("..").join("..").join(filename)
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

fn first_unsupported_ppx_for_rust_parser(
    filtered_ppx_flags: &Option<Vec<OneOrMore<String>>>,
) -> Option<String> {
    filtered_ppx_flags.as_ref().and_then(|flags| {
        flags.iter().find_map(|flag| {
            let ppx_name = match flag {
                OneOrMore::Single(s) => Some(s.as_str()),
                OneOrMore::Multiple(xs) => xs.first().map(String::as_str),
            };
            match ppx_name {
                Some(name) if name.contains("spice") => None,
                Some(name) => Some(name.to_string()),
                None => None,
            }
        })
    })
}

fn merge_warning_with_stderr(
    warning: Option<helpers::StdErr>,
    stderr: Option<helpers::StdErr>,
) -> Option<helpers::StdErr> {
    match (warning, stderr) {
        (Some(mut warning), Some(stderr)) => {
            warning.push_str(&stderr);
            Some(warning)
        }
        (Some(warning), None) => Some(warning),
        (None, Some(stderr)) => Some(stderr),
        (None, None) => None,
    }
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

fn source_bytes_to_latin1(bytes: &[u8]) -> String {
    bytes.iter().map(|&b| b as char).collect()
}

fn generate_ast_with_rust_parser(
    source_file: &Path,
    ast_output_path: &Path,
    source_path_for_ast: &str,
    extra_deps: &[String],
) -> anyhow::Result<Option<helpers::StdErr>> {
    let bytes =
        std::fs::read(source_file).with_context(|| format!("Failed to read {}", source_file.display()))?;
    let source = source_bytes_to_latin1(&bytes);
    let mut parser = Parser::new(source_path_for_ast.to_string(), &source);

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

        write_signature_ast_current_with_extra_deps(
            ast_output_path,
            source_path_for_ast,
            parser.arena_mut(),
            &signature,
            extra_deps,
        )
        .with_context(|| format!("Failed to write {}", ast_output_path.display()))?;
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

        write_structure_ast_current_with_extra_deps(
            ast_output_path,
            source_path_for_ast,
            parser.arena_mut(),
            &structure,
            extra_deps,
        )
        .with_context(|| format!("Failed to write {}", ast_output_path.display()))?;
    }

    Ok(None)
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
    use super::open_dependencies_from_bsc_flags;

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
}
