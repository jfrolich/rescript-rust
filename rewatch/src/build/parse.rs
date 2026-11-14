use super::build_types::ParseWarnings;
use super::build_types::*;
use super::compile::retain_critical_external_warnings;
use super::logs;
use crate::build::packages::Package;
use crate::config;
use crate::config::{Config, ExperimentalFeature, OneOrMore};
use crate::helpers;
use crate::project_context::ProjectContext;
use ahash::AHashSet;
use anyhow::{Context, anyhow};
use log::debug;
use rayon::prelude::*;
use rescript_compiler::binary_ast::{Dependencies, extract_signature_deps, extract_structure_deps};
use rescript_compiler::parser::{Parser, module};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use tracing::info_span;

struct GeneratedAst {
    stderr: Option<helpers::StdErr>,
    stored_ast: Option<super::build_types::StoredAst>,
    deps: Option<Dependencies>,
    gentype_annotations: Option<bool>,
}

/// Whether parsing appends a source's warnings to its package log.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ParseWarningLog {
    Append,
    /// The sources' saved warnings were already reported this build: parsing
    /// only records them.
    AlreadyWritten,
}

pub fn generate_asts(
    build_state: &mut BuildCommandState,
    inc: impl Fn() + std::marker::Sync,
    warning_log: ParseWarningLog,
) -> anyhow::Result<String> {
    let mut has_failure = false;
    let mut stderr = "".to_string();
    // `bsc` defaults to `-color always` (compiler/bsc/rescript_compiler_main.ml:494),
    // and the in-process frontend stands in for `bsc -bs-ast`.
    rescript_compiler::parser::code_frame::set_color_mode(
        rescript_compiler::parser::code_frame::ColorMode::Always,
    );

    // Count dirty modules for the span attribute only when a subscriber is
    // listening. Otherwise iterating every module every parse phase is pure
    // waste on the hot path.
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
    let parse_span = if tracing::enabled!(tracing::Level::INFO) {
        info_span!("build.parse", dirty_modules = dirty_modules)
    } else {
        tracing::Span::none()
    };
    let _span = parse_span.enter();

    let state: &BuildCommandState = build_state;
    let parsed = super::pools::with_pool_for(dirty_modules, || {
        state
            .modules
            .par_iter()
            .map(|(module_name, module)| {
                let package = state
                    .get_package(&module.package_name)
                    .expect("Package not found");
                match &module.source_type {
                    SourceType::MlMap(_mlmap) => (
                        module_name.to_owned(),
                        Ok(GeneratedAst {
                            stderr: None,
                            stored_ast: None,
                            deps: None,
                            gentype_annotations: None,
                        }),
                        Ok(None),
                        false,
                    ),

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
                                &source_file.implementation.path,
                                state,
                                state.get_warn_error_override(),
                                &parse_span,
                                ParseFor::build(state),
                            )
                            .map_err(|e| e.to_string());

                            let iast_result = match source_file.interface.as_ref() {
                                Some(interface) => {
                                    match generate_ast(
                                        package,
                                        &interface.path,
                                        state,
                                        state.get_warn_error_override(),
                                        &parse_span,
                                        ParseFor::build(state),
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
                                    stderr: None,
                                    stored_ast: None,
                                    deps: None,
                                    gentype_annotations: None,
                                }),
                                Ok(source_file.interface.as_ref().map(|_| GeneratedAst {
                                    stderr: None,
                                    stored_ast: None,
                                    deps: None,
                                    gentype_annotations: None,
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
    });
    parsed
        .into_iter()
        .for_each(|(module_name, ast_result, iast_result, is_dirty)| {
            let Some(module) = build_state.build_state.modules.get_mut(&module_name) else {
                eprintln!("Module not found: {module_name}");
                return;
            };
            let package = build_state
                .build_state
                .packages
                .get(&module.package_name)
                .expect("Package not found");
            // if the module is dirty, mark it also compile_dirty
            // do NOT set to false if the module is not parse_dirty, it needs to keep
            // the compile_dirty flag if it was set before
            if is_dirty {
                module.compile_dirty = true;
                module.deps_dirty = true;
                // Re-parsed: its warnings, if any, are recorded below.
                let mut parse_warnings = build_state.parse_warnings.lock().unwrap();
                parse_warnings.remove(&format!("{module_name}:impl"));
                parse_warnings.remove(&format!("{module_name}:intf"));
            }
            if let SourceType::SourceFile(ref mut source_file) = module.source_type {
                let sinks = ParseSinks {
                    stored_asts: &build_state.stored_asts,
                    in_memory_deps: &build_state.in_memory_deps,
                    parse_warnings: &build_state.parse_warnings,
                    warning_log,
                };
                if let Ok(generated) = &ast_result
                    && let Some(flag) = generated.gentype_annotations
                {
                    source_file.gentype_annotations[0] = Some(flag);
                }
                let (parse_state, parse_dirty) = sinks.apply(
                    package,
                    format!("{module_name}:impl"),
                    ast_result,
                    &mut stderr,
                    &mut has_failure,
                );
                source_file.implementation.parse_state = parse_state;
                source_file.implementation.parse_dirty = parse_dirty;

                // `None` when the file has no interface file associated.
                if let Some(iast_result) = iast_result.transpose() {
                    if let Ok(generated) = &iast_result
                        && let Some(flag) = generated.gentype_annotations
                    {
                        source_file.gentype_annotations[1] = Some(flag);
                    }
                    let (parse_state, parse_dirty) = sinks.apply(
                        package,
                        format!("{module_name}:intf"),
                        iast_result,
                        &mut stderr,
                        &mut has_failure,
                    );
                    if let Some(interface) = source_file.interface.as_mut() {
                        interface.parse_state = parse_state;
                        interface.parse_dirty = parse_dirty;
                    }
                }
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
                        // In-process builds synthesize namespace signatures directly into
                        // the module registry during compilation.
                        true
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
    let ppx_flags = if filter_ppx_flags(package_config, contents)
        .is_some_and(|flags| !flags.is_empty())
    {
        vec!["-bs-builtin-spice-ppx".to_string()]
    } else {
        Vec::new()
    };
    let jsx_args = root_config.get_jsx_args();
    let jsx_module_args = root_config.get_jsx_module_args();
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
    build_state: &BuildState,
    parent: &tracing::Span,
) -> tracing::Span {
    let module_name = helpers::file_path_to_module_name(filename, &package.namespace);
    let root_config = build_state.get_root_config();
    let jsx = root_config.get_jsx_args().get(1).cloned().unwrap_or_default();
    let bsc_flags = config::flatten_flags(&package.config.compiler_flags).join(" ");
    info_span!(
        parent: parent,
        "build.parse_file",
        module = %module_name,
        package = %package.name,
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
        &tracing::Span::none(),
        ParseFor::Tooling,
    )?;
    generated
        .stored_ast
        .ok_or_else(|| anyhow!("no AST for {}", filename.display()))
}

/// What a parse is for.
#[derive(Clone, Copy)]
enum ParseFor {
    /// A build compiles the tree in this process.
    Build { omit_locations: bool },
    /// Editor tooling reads the tree and its typed bodies: locations are
    /// kept and derived code is syntax.
    Tooling,
}

impl ParseFor {
    /// What a build of `state` parses its modules for.
    fn build(state: &BuildCommandState) -> ParseFor {
        if state.typed_trees.is_some() {
            return ParseFor::Tooling;
        }
        ParseFor::Build {
            omit_locations: !state.parses_with_locations(),
        }
    }
}

fn generate_ast(
    package: &Package,
    filename: &Path,
    build_state: &BuildState,
    warn_error_override: Option<String>,
    parent_span: &tracing::Span,
    parse_for: ParseFor,
) -> anyhow::Result<GeneratedAst> {
    let omit_locations = match parse_for {
        ParseFor::Build { omit_locations } => omit_locations,
        ParseFor::Tooling => false,
    };
    let file_path = PathBuf::from(&package.path).join(filename);

    // `bsc -absname` names the source by its normalized absolute path.
    let source_path_str = helpers::ocaml_absname(&file_path).to_string_lossy().to_string();
    let bsc_flags = config::flatten_flags(&package.config.compiler_flags);
    let open_deps = open_dependencies_from_bsc_flags(&bsc_flags);
    // The source is read once, for both the ppx filter and parsing.
    let source_bytes =
        std::fs::read(&file_path).with_context(|| format!("Failed to read {}", file_path.display()))?;

    // Configuration validation has already rejected all non-spice rewriters.
    // The built-in mapper needs neither executable resolution nor a v0 AST.
    let contents = std::str::from_utf8(&source_bytes).unwrap_or_default();
    let spice_ppx = filter_ppx_flags(&package.config, contents)
        .is_some_and(|flags| !flags.is_empty());
    let mut frontend_options = {
        let root_config = build_state.project_context.get_root_config();
        let flags = [
            root_config.get_jsx_args(),
            root_config.get_jsx_module_args(),
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
            ..Default::default()
        }
    };
    if matches!(parse_for, ParseFor::Tooling) {
        frontend_options.derived_path = rescript_compiler::driver::DerivedPath::General;
    }

    let _parse_span = if tracing::enabled!(tracing::Level::INFO) {
        make_parse_file_span(filename, package, build_state, parent_span).entered()
    } else {
        tracing::Span::none().entered()
    };

    // A source map explicitly asks for source coordinates as generated output.
    let locations = !omit_locations
        || build_state
            .get_root_config()
            .effective_source_map_mode(build_state.source_map_command)
            .is_some();
    let source = Arc::new(ParseSource {
        file_path,
        source: source_bytes,
        source_path_for_ast: source_path_str,
        open_deps,
        options: frontend_options,
    });
    let mut result = parse_saved_source(&source, locations);
    // The first pass reports nothing with invented positions. Parse failures
    // and frontend warnings are regenerated against the exact same bytes.
    // A unit whose generated code embeds source coordinates (`__LOC__`,
    // `assert`, `module rec`) is parsed with locations now, rather than type
    // checked location-free and then compiled again.
    if !locations
        && result.as_ref().map_or(true, |(stderr, ast, _)| {
            stderr.is_some() || ast.arena().locations_required()
        })
    {
        log::debug!("Parsing {} with source locations", source.file_path.display());
        let prior = result.as_ref().ok().and_then(|(_, ast, _)| ast.arena().derived_census.as_ref()).map(|c| c.parse_work());
        result = parse_saved_source(&source, true);
        if let (Some(prior), Ok((_, ast, _))) = (prior, &mut result) {
            if let Some(census) = census_mut(ast) { census.add_parse_work(prior); }
        }
    }
    let (stderr, mut stored_ast, deps) = result.map_err(|err| anyhow!("{err}"))?;
    // The source is kept for a compile that may have to parse it again: for
    // its locations, or because a plan of the unit cannot be used.
    if !stored_ast.arena().stores_locations() || stored_ast.arena().plans().item_count() > 0 {
        match &mut stored_ast {
            StoredAst::Structure(ast) => Arc::get_mut(ast).unwrap().retry_source = Some(source),
            StoredAst::Signature(ast) => Arc::get_mut(ast).unwrap().retry_source = Some(source),
        }
    }
    let gentype_annotations = Some(parsed_gentype_annotations(&stored_ast));
    Ok(GeneratedAst {
        gentype_annotations,
        stderr,
        stored_ast: Some(stored_ast),
        deps: Some(deps),
    })
}

/// The frontend's derived genType accessors inherit an existing annotation
/// (binary_ast/ppx.rs::gentype_attrs_for_derived_accessors). It does not invent
/// annotations in previously unannotated source, so the parser flag suffices.
fn parsed_gentype_annotations(ast: &StoredAst) -> bool {
    ast.arena().has_gentype_annotations()
}

fn parse_saved_source(
    source: &ParseSource,
    locations: bool,
) -> anyhow::Result<(Option<helpers::StdErr>, StoredAst, Dependencies)> {
    parse_source(
        &source.file_path,
        source.source.clone(),
        &source.source_path_for_ast,
        &source.open_deps,
        &source.options,
        locations,
    )
}

/// Recreate the AST with location side tables only when compilation needs them.
pub(crate) fn reparse_with_locations(ast: &StoredAst) -> anyhow::Result<StoredAst> {
    let source = ast
        .retry_source()
        .ok_or_else(|| anyhow!("missing source for location retry"))?;
    let (_, mut located, _) = parse_saved_source(source, true)?;
    if let (Some(prior), Some(census)) = (ast.arena().derived_census.as_ref(), census_mut(&mut located)) {
        census.add_parse_work(prior.parse_work());
    }
    Ok(located)
}

/// Parse the source of `ast` again with its derived code as syntax, for a
/// unit whose plan could not be used, with location tables when
/// `locations`. The result keeps a source that parses the same way, for
/// placing its warnings.
/// Cost: one frontend run of the unit, and one copy of its source.
pub(crate) fn reparse_without_plans(ast: &StoredAst, locations: bool) -> anyhow::Result<StoredAst> {
    let source = ast
        .retry_source()
        .ok_or_else(|| anyhow!("missing source for a parse without plans"))?;
    let source = Arc::new(ParseSource {
        file_path: source.file_path.clone(),
        source: source.source.clone(),
        source_path_for_ast: source.source_path_for_ast.clone(),
        open_deps: source.open_deps.clone(),
        options: rescript_compiler::driver::CompilerOptions {
            derived_path: rescript_compiler::driver::DerivedPath::Fallback,
            ..source.options.clone()
        },
    });
    let (_, mut general, _) = parse_saved_source(&source, locations)?;
    if let (Some(prior), Some(census)) = (ast.arena().derived_census.as_ref(), census_mut(&mut general)) {
        census.add_parse_work(prior.parse_work());
    }
    match &mut general {
        StoredAst::Structure(ast) => Arc::get_mut(ast).unwrap().retry_source = Some(source),
        StoredAst::Signature(ast) => Arc::get_mut(ast).unwrap().retry_source = Some(source),
    }
    Ok(general)
}

/// O(1): borrow the record of a newly parsed, uniquely owned AST. No lock or clone.
fn census_mut(ast: &mut StoredAst) -> Option<&mut rescript_compiler::derived_census::Census> {
    let arena = match ast {
        StoredAst::Structure(ast) => &mut Arc::get_mut(ast)?.arena,
        StoredAst::Signature(ast) => &mut Arc::get_mut(ast)?.arena,
    };
    arena.derived_census.as_deref_mut()
}

/// The general form of the unit `source` holds, for the reference compile of
/// `RESCRIPT_DERIVED_PATH=check`: its tree with every derived item as
/// syntax, with location tables when the checked compile has them. Errors
/// name the file.
/// Cost: one frontend run of the unit, and one copy of its source.
pub(crate) fn general_form(
    source: &ParseSource,
    locations: bool,
) -> anyhow::Result<(
    rescript_compiler::parse_arena::ParseArena,
    rescript_compiler::parser::ast::Structure,
)> {
    let path = source.file_path.display();
    let general = ParseSource {
        file_path: source.file_path.clone(),
        source: source.source.clone(),
        source_path_for_ast: source.source_path_for_ast.clone(),
        open_deps: source.open_deps.clone(),
        options: rescript_compiler::driver::CompilerOptions {
            derived_path: rescript_compiler::driver::DerivedPath::General,
            // The reference compile is not part of the measured build.
            derived_census: None,
            ..source.options.clone()
        },
    };
    let (_, ast, _) = parse_saved_source(&general, locations)
        .map_err(|error| anyhow!("parsing {path} again failed: {error}"))?;
    match ast {
        StoredAst::Structure(ast) => {
            let ast = Arc::try_unwrap(ast).map_err(|_| anyhow!("the parse of {path} is shared"))?;
            Ok((ast.arena, ast.structure))
        }
        StoredAst::Signature(_) => Err(anyhow!("{path} is an interface")),
    }
}

/// The located arena of a fresh parse of `source`, for placing the warnings
/// of a location-free compile (`CompilerOptions::warning_locations`).
pub(crate) fn reparse_arena_with_locations(
    source: &ParseSource,
) -> Option<rescript_compiler::parse_arena::ParseArena> {
    let (_, ast, _) = parse_saved_source(source, true).ok()?;
    match ast {
        StoredAst::Structure(ast) => Arc::try_unwrap(ast).ok().map(|ast| ast.arena),
        StoredAst::Signature(ast) => Arc::try_unwrap(ast).ok().map(|ast| ast.arena),
    }
}

fn should_run_ppx(config: &Config, flag: &str, contents: &str) -> bool {
    config.is_spice_ppx(flag) && contents.contains("@spice")
}

fn open_dependencies_from_bsc_flags(flags: &[String]) -> Vec<String> {
    let mut deps = Vec::new();
    let mut seen = AHashSet::new();
    let mut i = 0;
    while i < flags.len() {
        if flags[i] == "-open" {
            if let Some(dep) = flags.get(i + 1)
                && seen.insert(dep.clone())
            {
                deps.push(dep.clone());
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

/// Frontend warning reports as `bsc -bs-ast` writes them: the parser keeps
/// one `char` per source byte, so names and messages taken from the source
/// are turned back into their UTF-8 bytes, as the compiler's own stderr
/// writer does (`driver::write_stderr`).
fn frontend_output(warnings: &str) -> String {
    rescript_compiler::source_text::decode_internal_utf8_runs(warnings).into_owned()
}

fn parse_source(
    source_file: &Path,
    bytes: Vec<u8>,
    source_path_for_ast: &str,
    extra_deps: &[String],
    options: &rescript_compiler::driver::CompilerOptions,
    locations: bool,
) -> anyhow::Result<(
    Option<helpers::StdErr>,
    super::build_types::StoredAst,
    Dependencies,
)> {
    let census_start = rescript_compiler::derived_census::start(options.derived_census.is_some());
    let mut result = rescript_compiler::timing::measure(rescript_compiler::timing::Phase::Parse, || {
        let source = source_bytes_to_latin1(bytes);
        let mut parser = Parser::with_locations(source_path_for_ast.to_string(), &source, locations);
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
                Err(err) => return Err(anyhow!("{}{err}", frontend_output(&warnings))),
            };
            // `bsc -bs-ast` exits 2 when a frontend warning is an error.
            if frontend.warnings_fatal {
                return Err(anyhow!(frontend_output(&warnings)));
            }
            let signature = frontend.signature;

            let mut deps = extract_signature_deps(parser.arena(), &signature);
            deps.extend(extra_deps.iter().cloned());

            let mut arena = parser.into_arena();
            rescript_compiler::types::typecore::prepare_typecheck_arena(&mut arena);
            arena.finish_parse_locations();
            let stored =
                super::build_types::StoredAst::Signature(Arc::new(super::build_types::StoredSignatureAst {
                    arena,
                    signature,
                    source_len: source.len(),
                    retry_source: None,
                }));
            Ok((
                (!warnings.is_empty()).then(|| frontend_output(&warnings)),
                stored,
                deps,
            ))
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
                Err(err) => return Err(anyhow!("{}{err}", frontend_output(&warnings))),
            };
            if frontend.warnings_fatal {
                return Err(anyhow!(frontend_output(&warnings)));
            }
            let structure = frontend.structure;

            // The frontend already applied `no_export` (js_implementation.ml:130).
            let mut deps = extract_structure_deps(parser.arena(), &structure);
            deps.extend(extra_deps.iter().cloned());

            let mut arena = parser.into_arena();
            rescript_compiler::types::typecore::prepare_typecheck_arena(&mut arena);
            arena.finish_parse_locations();
            let stored =
                super::build_types::StoredAst::Structure(Arc::new(super::build_types::StoredStructureAst {
                    arena,
                    structure,
                    source_len: source.len(),
                    retry_source: None,
                }));
            Ok((
                (!warnings.is_empty()).then(|| frontend_output(&warnings)),
                stored,
                deps,
            ))
        }
    });
    if let (Some(start), Ok((_, stored, _))) = (census_start, &mut result) {
        let arena = match stored {
            super::build_types::StoredAst::Structure(ast) => Arc::get_mut(ast).map(|ast| &mut ast.arena),
            super::build_types::StoredAst::Signature(ast) => Arc::get_mut(ast).map(|ast| &mut ast.arena),
        };
        if let Some(arena) = arena && let Some(census) = &mut arena.derived_census {
            census.account_parse(rescript_compiler::derived_census::nanos(start.elapsed()));
        }
    }
    result
}

fn filter_ppx_flags(
    config: &Config,
    contents: &str,
) -> Option<Vec<OneOrMore<String>>> {
    config.ppx_flags.as_ref().map(|flags| {
        flags
            .iter()
            .filter(|flag| match flag {
                config::OneOrMore::Single(str) => should_run_ppx(config, str, contents),
                config::OneOrMore::Multiple(str) => str
                    .first()
                    .is_some_and(|command| should_run_ppx(config, command, contents)),
            })
            .map(|x| x.to_owned())
            .collect::<Vec<OneOrMore<String>>>()
    })
}

/// Record a source file's parse warnings (keyed `Module:impl` or
/// `Module:intf`) for the in-process manifest.
/// Where a parsed source's warnings, stored AST and dependencies go.
struct ParseSinks<'a> {
    stored_asts: &'a std::sync::Mutex<ahash::AHashMap<String, super::build_types::StoredAst>>,
    in_memory_deps: &'a std::sync::Mutex<ahash::AHashMap<String, Dependencies>>,
    parse_warnings: &'a ParseWarnings,
    warning_log: ParseWarningLog,
}

impl ParseSinks<'_> {
    /// Records the result of parsing one source (`key` is `Module:impl` or
    /// `Module:intf`) and returns its parse state and `parse_dirty` flag.
    ///
    /// We get Err(x) when there is a parse error. When the AST has stderr, the
    /// outputs are warnings.
    fn apply(
        &self,
        package: &Package,
        key: String,
        result: Result<GeneratedAst, String>,
        stderr: &mut String,
        has_failure: &mut bool,
    ) -> (ParseState, bool) {
        let generated = match result {
            Ok(generated) => generated,
            Err(err) => {
                // Some compilation error
                logs::append(package, &err);
                *has_failure = true;
                stderr.push_str(&err);
                return (ParseState::ParseError, true);
            }
        };
        let state = match generated.stderr {
            // In case of an internal dependency, we want to keep on
            // propagating the warning with every compile. So we mark it as
            // dirty for the next round
            Some(warnings) if package.is_local_dep => {
                if self.warning_log == ParseWarningLog::Append {
                    logs::append(package, &warnings);
                }
                stderr.push_str(&warnings);
                record_parse_warnings(self.parse_warnings, key.clone(), &package.name, &warnings);
                (ParseState::Warning, true)
            }
            Some(warnings) => {
                // External dep: surface only the critical warnings
                // (e.g. legacy `(. ...)` uncurried syntax) so
                // downstream users can report breakage upstream.
                if let Some(kept) = retain_critical_external_warnings(&warnings) {
                    if self.warning_log == ParseWarningLog::Append {
                        logs::append(package, &kept);
                    }
                    stderr.push_str(&kept);
                    record_parse_warnings(self.parse_warnings, key.clone(), &package.name, &kept);
                }
                (ParseState::Success, false)
            }
            None => (ParseState::Success, false),
        };
        if let Some(ast) = generated.stored_ast {
            self.stored_asts.lock().unwrap().insert(key.clone(), ast);
        }
        if let Some(deps) = generated.deps {
            self.in_memory_deps.lock().unwrap().insert(key, deps);
        }
        state
    }
}

fn record_parse_warnings(parse_warnings: &ParseWarnings, key: String, package_name: &str, warnings: &str) {
    parse_warnings
        .lock()
        .unwrap()
        .insert(key, (package_name.to_string(), warnings.to_string()));
}

#[cfg(test)]
mod tests {
    use super::{
        Arc, Parser, StoredAst, StoredSignatureAst, StoredStructureAst, module,
        parsed_gentype_annotations,
    };
    use super::{
        filter_ppx_flags, open_dependencies_from_bsc_flags, rust_parser_let_unwrap_enabled, should_run_ppx,
    };
    use crate::config::Config;

    #[test]
    fn parsed_gentype_flags_cover_all_names_and_nested_attributes() {
        for prefix in ["genType", "gentype"] {
            for suffix in ["", ".as", ".import", ".opaque", ".ignoreInterface", ".future"] {
                for source in [
                    format!("@{prefix}{suffix} type t = int"),
                    format!("@@{prefix}{suffix}\ntype t = int"),
                    format!("module M = {{type t = {{@{prefix}{suffix} field: int}}}}"),
                ] {
                    let mut parser = Parser::new("Flags.res", &source);
                    let structure = module::parse_structure(&mut parser);
                    assert!(!parser.has_errors(), "{source}");
                    let ast = StoredAst::Structure(Arc::new(StoredStructureAst {
                        arena: parser.into_arena(),
                        structure,
                        source_len: source.len(),
                        retry_source: None,
                    }));
                    assert!(parsed_gentype_annotations(&ast), "{source}");
                }
                let source = format!("@{prefix}{suffix} type t = int");
                let mut parser = Parser::new("Flags.resi", &source);
                let signature = module::parse_signature(&mut parser);
                assert!(!parser.has_errors());
                assert!(parsed_gentype_annotations(&StoredAst::Signature(Arc::new(
                    StoredSignatureAst {
                        arena: parser.into_arena(),
                        signature,
                        source_len: source.len(),
                        retry_source: None,
                    }
                ))));
            }
        }
        let mut parser = Parser::new("Plain.res", "type t = int\nlet x = `genType` // @gentype");
        let structure = module::parse_structure(&mut parser);
        assert!(!parsed_gentype_annotations(&StoredAst::Structure(
            Arc::new(StoredStructureAst {
                arena: parser.into_arena(),
                structure,
                source_len: 0,
                retry_source: None,
            })
        )));
    }

    #[test]
    fn location_free_frontend_keeps_ast_and_dependencies_for_compilation() {
        let (tx, rx) = std::sync::mpsc::channel();
        std::thread::Builder::new()
            .stack_size(16 * 1024 * 1024)
            .spawn(move || {
                let source = std::sync::Arc::new(super::ParseSource {
                    file_path: std::path::PathBuf::from("Example.res"),
                    source: b"@genType type t = {value: int}\nlet f = x => Other.apply(x)\nlet view = () => <div />".to_vec(),
                    source_path_for_ast: "Example.res".to_string(),
                    open_deps: vec!["Implicit".to_string()],
                    options: rescript_compiler::driver::CompilerOptions {
                        spice_ppx: true,
                        jsx_version: Some(4),
                        ..Default::default()
                    },
                });
                let (warnings, mut ast, deps) = super::parse_saved_source(&source, false).unwrap();
                assert!(warnings.is_none());
                assert!(!ast.arena().stores_locations());
                assert_eq!(ast.arena().location_count(), 0);
                assert_eq!(ast.arena().position_count(), 0);
                let super::StoredAst::Structure(stored) = &mut ast else {
                    panic!("expected structure")
                };
                std::sync::Arc::get_mut(stored).unwrap().retry_source = Some(source.clone());
                let located = super::reparse_with_locations(&ast).unwrap();
                assert!(located.arena().stores_locations());
                assert!(located.arena().location_count() > 0);
                assert!(located.retry_source().is_none());
                let (_, _, full_deps) = super::parse_saved_source(&source, true).unwrap();
                assert_eq!(deps, full_deps);
                assert!(deps.iter().any(|name| name == "Other"));
                tx.send(()).unwrap();
            })
            .unwrap();
        rx.recv_timeout(std::time::Duration::from_secs(5))
            .expect("frontend timed out or failed");
    }

    /// Frontend warnings are written like `bsc` writes them: the message of
    /// `%todo("...")` comes from the source, which the parser keeps one
    /// `char` per byte, and is shown as its UTF-8 text.
    #[test]
    fn frontend_warnings_show_source_text_as_utf8() {
        let (tx, rx) = std::sync::mpsc::channel();
        std::thread::Builder::new()
            .stack_size(16 * 1024 * 1024)
            .spawn(move || {
                let source = std::sync::Arc::new(super::ParseSource {
                    file_path: std::path::PathBuf::from("Todo.res"),
                    source: "let f = () => %todo(\"m\u{e9}ssage \u{20ac}\")\n"
                        .as_bytes()
                        .to_vec(),
                    source_path_for_ast: "Todo.res".to_string(),
                    open_deps: vec![],
                    options: Default::default(),
                });
                for locations in [false, true] {
                    let (warnings, _, _) = super::parse_saved_source(&source, locations).unwrap();
                    let warnings = warnings.expect("warning 110");
                    assert!(
                        warnings.contains("Todo found: m\u{e9}ssage \u{20ac}"),
                        "{warnings}"
                    );
                }
                tx.send(()).unwrap();
            })
            .unwrap();
        rx.recv_timeout(std::time::Duration::from_secs(5))
            .expect("frontend timed out or failed");
    }

    /// Warnings of a location-free compile are placed in a located parse by
    /// identity, which needs both parses to issue the same location slots.
    #[test]
    fn location_free_parse_issues_the_located_parse_slots() {
        let (tx, rx) = std::sync::mpsc::channel();
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(move || {
                let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../tests/tests/src");
                let mut sources: Vec<_> = std::fs::read_dir(&root)
                    .unwrap()
                    .map(|entry| entry.unwrap().path())
                    .filter(|path| path.extension().is_some_and(|ext| ext == "res" || ext == "resi"))
                    .collect();
                sources.sort();
                assert!(sources.len() > 100, "{}", root.display());
                let mut checked = 0;
                for path in sources {
                    let name = path.file_name().unwrap().to_string_lossy().to_string();
                    let source = super::ParseSource {
                        file_path: path.clone(),
                        source: std::fs::read(&path).unwrap(),
                        source_path_for_ast: name,
                        open_deps: Vec::new(),
                        options: rescript_compiler::driver::CompilerOptions {
                            jsx_version: Some(4),
                            ..Default::default()
                        },
                    };
                    let Ok((_, free, _)) = super::parse_saved_source(&source, false) else {
                        continue;
                    };
                    let located = super::reparse_arena_with_locations(&source).unwrap();
                    assert!(!free.arena().stores_locations());
                    assert_eq!(
                        free.arena().parse_location_slot_count(),
                        located.parse_location_slot_count(),
                        "{}",
                        path.display()
                    );
                    checked += 1;
                }
                assert!(checked > 100);
                tx.send(()).unwrap();
            })
            .unwrap();
        rx.recv_timeout(std::time::Duration::from_secs(60))
            .expect("parsing the runtime test sources timed out or failed");
    }

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

    #[test]
    fn spice_only_runs_for_matching_sources() {
        let config = Config::new_from_json_string(r#"{"name":"example","sources":[]}"#).unwrap();
        assert!(!should_run_ppx(&config, "ppx-spice", "let value = 1"));
        assert!(should_run_ppx(&config, "ppx-spice", "@spice type t = int"));
    }

    #[test]
    fn relative_spice_command_enables_builtin_mapper() {
        let config = Config::new_from_json_string(
            r#"{"name":"@jfrolich/ppx-spice","sources":[],"ppx-flags":["./ppx"]}"#,
        ).unwrap();
        assert!(filter_ppx_flags(&config, "let value = 1").unwrap().is_empty());
        assert_eq!(filter_ppx_flags(&config, "@spice type t = int").unwrap().len(), 1);
    }

    #[test]
    fn empty_ppx_commands_are_ignored() {
        let config = Config::new_from_json_string(
            r#"{"name":"example","sources":[],"ppx-flags":[[],"ppx-spice"]}"#,
        ).unwrap();
        assert_eq!(filter_ppx_flags(&config, "@spice").unwrap().len(), 1);
    }
}
