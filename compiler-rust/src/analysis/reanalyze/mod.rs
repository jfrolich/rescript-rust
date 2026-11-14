//! `rescript-tools reanalyze` on the Rust typed tree: a port of
//! analysis/reanalyze (the dead code, exception and termination analyses).
//!
//! The OCaml tool reads the `.cmt` and `.cmti` files of a build. Builds
//! write none, so the analyses read each module's typed tree as a
//! check-only build type-checks it ([`Analysis`]), and print what the OCaml
//! tool prints.
//!
//! The analyses refer to declarations of other modules by position, so the
//! project must be built with source locations, which a watcher's builds
//! leave out: this is no watcher command.

pub mod annotation;
pub mod arnold;
pub mod common;
pub mod dce;
pub mod dce_solve;
pub mod exception;
pub mod exn_lib;
pub mod log;
pub mod ocaml_hash;
pub mod traverse;

use crate::driver::{TypedModule, TypedTree, TypedTreeReader};
use common::{Config, FileContext, Files, Tree};
use log::{Log, Logged, filename_concat, has_prefix, is_relative};
use std::collections::HashMap;
use std::path::Path;
use std::sync::{Arc, Mutex, PoisonError};

/// `Version.version` (analysis/reanalyze/src/version.ml).
const VERSION: &str = "2.22.0";

/// The command line's options, as `Arg.usage` lists them.
const OPTIONS: &[(&str, &str)] = &[
    ("-all", "Run all the analyses."),
    ("-ci", "Internal flag for use in CI"),
    ("-config", "Read the analysis mode from rescript.json"),
    (
        "-transitive",
        "Force transitive reporting (overrides rescript.json reanalyze.transitive)",
    ),
    (
        "-no-transitive",
        "Disable transitive reporting (overrides rescript.json reanalyze.transitive)",
    ),
    ("-dce", "Eperimental DCE"),
    ("-debug", "Print debug information"),
    ("-exception", "Experimental exception analysis"),
    (
        "-exclude-paths",
        "comma-separated-path-prefixes Exclude from analysis files whose path has a prefix in the list",
    ),
    (
        "-experimental",
        "Turn on experimental analyses (this option is currently unused)",
    ),
    ("-externals", "Report on externals in dead code analysis"),
    ("-json", "Print reports in json format"),
    (
        "-live-names",
        "comma-separated-names Consider all values with the given names as live",
    ),
    (
        "-live-paths",
        "comma-separated-path-prefixes Consider all values whose path has a prefix in the list as live",
    ),
    (
        "-suppress",
        "comma-separated-path-prefixes Don't report on files whose path has a prefix in the list",
    ),
    ("-termination", "Experimental termination analysis"),
    (
        "-unsuppress",
        "comma-separated-path-prefixes Report on files whose path has a prefix in the list, overriding -suppress (no-op if -suppress is not specified)",
    ),
    (
        "-test-shuffle",
        "Test flag: shuffle file processing order to verify order-independence",
    ),
    ("-timing", "Report internal timing of analysis phases"),
    ("-mermaid", "Output Mermaid diagram of reactive pipeline"),
    (
        "-runs",
        "n Run analysis n times (for benchmarking cache effectiveness)",
    ),
    (
        "-churn",
        "n Remove and re-add n random files between runs (tests incremental correctness)",
    ),
    ("-version", "Show version information and exit"),
    ("--version", "Show version information and exit"),
    ("-help", " Display this list of options"),
    ("--help", " Display this list of options"),
];

/// `Arg.usage_string`.
fn usage() -> String {
    let mut out = format!("reanalyze version {VERSION}\n");
    for (key, doc) in OPTIONS {
        out.push_str(&format!("  {key} {doc}\n"));
    }
    out
}

/// What a command line asks for.
enum Command {
    /// Run the analyses, after printing the text.
    Analyze(Config, String),
    /// Print this and stop.
    Print(String),
}

/// `Paths.find_project_root`: the nearest directory with a `rescript.json`.
fn find_project_root(dir: &Path) -> Option<&Path> {
    dir.ancestors()
        .find(|dir| dir.join("rescript.json").is_file())
}

fn json_strings(value: Option<&serde_json::Value>) -> Vec<String> {
    match value {
        Some(serde_json::Value::Array(elements)) => elements
            .iter()
            .filter_map(|x| x.as_str().map(str::to_string))
            .collect(),
        _ => Vec::new(),
    }
}

/// `Paths.Config.process_config`: the `reanalyze` settings of the project's
/// `rescript.json`.
fn process_config(config: &mut Config) {
    let rescript_json = filename_concat(&config.run.project_root, "rescript.json");
    let Ok(text) = std::fs::read_to_string(rescript_json) else {
        return;
    };
    let Ok(json) = serde_json::from_str::<serde_json::Value>(&text) else {
        return;
    };
    let Some(conf) = json.get("reanalyze") else {
        // No settings: the dead code analysis.
        config.run.dce = true;
        return;
    };
    let run = &mut config.run;
    prepend(&mut run.suppress, json_strings(conf.get("suppress")));
    prepend(&mut run.unsuppress, json_strings(conf.get("unsuppress")));
    match conf.get("analysis") {
        Some(serde_json::Value::Array(elements)) => {
            for element in elements {
                match element.as_str() {
                    Some("all") => {
                        run.dce = true;
                        run.exception = true;
                        run.termination = true;
                    }
                    Some("dce") => run.dce = true,
                    Some("exception") => run.exception = true,
                    Some("termination") => run.termination = true,
                    _ => {}
                }
            }
        }
        _ => run.dce = true,
    }
    if let Some(serde_json::Value::Bool(transitive)) = conf.get("transitive") {
        run.transitive = *transitive;
    }
}

/// `names @ list`.
fn prepend(list: &mut Vec<String>, mut names: Vec<String>) {
    names.append(list);
    *list = names;
}

fn split_commas(s: &str) -> Vec<String> {
    s.split(',').map(str::to_string).collect()
}

/// The options that take a value.
const VALUED_OPTIONS: &[&str] = &[
    "-exclude-paths",
    "-live-names",
    "-live-paths",
    "-suppress",
    "-unsuppress",
    "-runs",
    "-churn",
];

/// What a command line that asks for the version or the options prints,
/// which needs no project: `Arg.parse_argv` stops at `-version` and `-help`
/// when it reaches them, after printing the arguments before them that are
/// no options.
pub fn output_without_project(args: &[String]) -> Option<String> {
    let mut printed = String::new();
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "-version" | "--version" => {
                return Some(format!("{printed}reanalyze version {VERSION}\n"));
            }
            "-help" | "--help" => return Some(format!("{printed}{}", usage())),
            option if VALUED_OPTIONS.contains(&option) => {
                args.next();
            }
            other if !other.starts_with('-') => {
                printed.push_str(other);
                printed.push('\n');
            }
            _ => {}
        }
    }
    None
}

/// `Reanalyze.parse_argv`.
fn parse_argv(cwd: &Path, args: &[String]) -> Result<Command, String> {
    let project_root = find_project_root(cwd)
        .ok_or_else(|| "Error: cannot find project root containing rescript.json.".to_string())?;
    let mut config = Config {
        cwd: cwd.to_string_lossy().into_owned(),
        ..Config::default()
    };
    config.run.project_root = project_root.to_string_lossy().into_owned();
    let mut analysis_kind_set = false;
    let mut transitive_override = None;
    // `Arg.parse_argv` calls its anonymous function, `print_endline` here,
    // on each argument that is no option.
    let mut printed = String::new();
    let mut args = args.iter();
    while let Some(arg) = args.next() {
        let mut value = |what: &str| {
            args.next()
                .cloned()
                .ok_or_else(|| format!("reanalyze: option '{arg}' needs an argument.\n{what}"))
        };
        match arg.as_str() {
            "-all" => {
                config.run.dce = true;
                config.run.exception = true;
                config.run.termination = true;
                analysis_kind_set = true;
            }
            "-ci" => config.cli.ci = true,
            "-config" => {
                process_config(&mut config);
                analysis_kind_set = true;
            }
            "-transitive" => transitive_override = Some(true),
            "-no-transitive" => transitive_override = Some(false),
            "-dce" => {
                config.run.dce = true;
                analysis_kind_set = true;
            }
            "-debug" => config.cli.debug = true,
            "-exception" => {
                config.run.exception = true;
                analysis_kind_set = true;
            }
            "-exclude-paths" => {
                let paths = split_commas(&value(&usage())?);
                prepend(&mut config.cli.exclude_paths, paths);
            }
            "-experimental" => {}
            "-externals" => config.cli.analyze_externals = true,
            "-json" => config.cli.json = true,
            "-live-names" => {
                let names = split_commas(&value(&usage())?);
                prepend(&mut config.cli.live_names, names);
            }
            "-live-paths" => {
                let paths = split_commas(&value(&usage())?);
                prepend(&mut config.cli.live_paths, paths);
            }
            "-suppress" => {
                let names = split_commas(&value(&usage())?);
                prepend(&mut config.run.suppress, names);
            }
            "-termination" => {
                config.run.termination = true;
                analysis_kind_set = true;
            }
            "-unsuppress" => {
                let names = split_commas(&value(&usage())?);
                prepend(&mut config.run.unsuppress, names);
            }
            // These measure or test the OCaml tool's incremental engine,
            // which a run that reads every typed tree once does not have.
            "-test-shuffle" | "-timing" | "-mermaid" => {}
            "-runs" | "-churn" => {
                let n = value(&usage())?;
                n.parse::<i64>().map_err(|_| {
                    format!(
                        "reanalyze: wrong argument '{n}'; option '{arg}' expects an integer.\n{}",
                        usage()
                    )
                })?;
            }
            "-version" | "--version" => {
                return Ok(Command::Print(format!(
                    "{printed}reanalyze version {VERSION}\n"
                )));
            }
            "-help" | "--help" => return Ok(Command::Print(format!("{printed}{}", usage()))),
            "-all-cmt" | "-dce-cmt" | "-exception-cmt" | "-termination-cmt" => {
                return Err(format!(
                    "reanalyze: option '{arg}' reads the .cmt files under a directory, which builds do not write."
                ));
            }
            other if !other.starts_with('-') => {
                printed.push_str(other);
                printed.push('\n');
            }
            other => return Err(format!("reanalyze: unknown option '{other}'.\n{}", usage())),
        }
    }
    if !analysis_kind_set {
        process_config(&mut config);
    }
    if let Some(transitive) = transitive_override {
        config.run.transitive = transitive;
    }
    // tools/bin/main.ml:167-174 shifts `reanalyze` out of the command line
    // and leaves an empty last argument, which is printed as well.
    printed.push('\n');
    Ok(Command::Analyze(config, printed))
}

/// `Paths.get_module_name` of a source file: its base name, without its
/// extension or a `-Namespace` suffix.
fn module_name_of_source(source: &str) -> String {
    let base = common::basename(source);
    let base = match base.rfind('.') {
        Some(i) if i > 0 => &base[..i],
        _ => base,
    };
    match base.find('-') {
        Some(i) => base[..i].to_string(),
        None => base.to_string(),
    }
}

/// What the analyses collect from one file.
#[derive(Default)]
struct Collected {
    dce: Option<dce::FileData>,
    exception: Option<exception::FileResult>,
    termination: arnold::Stats,
}

/// A package whose modules the analyses read.
#[derive(Debug, Clone)]
pub struct Package {
    /// The package's build directory, where the OCaml compiler writes its
    /// `.cmt` files.
    pub build_root: String,
    /// The package's modules.
    pub modules: Vec<Module>,
}

/// A module of a [`Package`].
#[derive(Debug, Clone)]
pub struct Module {
    /// The module's name, as the build names it to [`TypedTreeReader::read`].
    pub name: String,
    /// The base name of the artifacts the OCaml compiler writes for the
    /// module: its source file's, with the package's namespace
    /// (`foo-Namespace`), not capitalized.
    pub artifact: String,
    /// Whether the module has an interface file.
    pub has_interface: bool,
}

/// A file to read: the `.cmt` or `.cmti` file the OCaml compiler would
/// write for a module's implementation or interface.
struct Artifact {
    path: String,
    has_interface: bool,
    /// What the file's analyses logged and collected, once the build has
    /// type-checked the module.
    read: Mutex<Option<(Logged, Collected)>>,
}

/// `Reanalyze.collect_cmt_file_paths`: the artifacts of `packages`, each
/// package's in the order of their file names, and where each module's are.
fn artifacts(packages: &[Package]) -> (Vec<Artifact>, HashMap<(String, bool), usize>) {
    let mut artifacts = Vec::new();
    let mut by_module = HashMap::new();
    for package in packages {
        let mut names: Vec<(String, &Module, bool)> = Vec::new();
        for module in &package.modules {
            names.push((format!("{}.cmt", module.artifact), module, false));
            if module.has_interface {
                names.push((format!("{}.cmti", module.artifact), module, true));
            }
        }
        names.sort_by(|(a, module_a, _), (b, module_b, _)| {
            a.cmp(b).then_with(|| module_a.name.cmp(&module_b.name))
        });
        for (name, module, interface) in names {
            by_module.insert((module.name.clone(), interface), artifacts.len());
            artifacts.push(Artifact {
                path: filename_concat(&package.build_root, &name),
                has_interface: module.has_interface,
                read: Mutex::new(None),
            });
        }
    }
    (artifacts, by_module)
}

/// `Find_source_file.cmt`: the file of the first item whose file exists.
fn find_source_file(
    config: &Config,
    log: &mut Log<'_>,
    module: &TypedModule<'_>,
) -> Option<Arc<str>> {
    let arena = module.arena;
    let ta = module.typed_arena;
    let (locs, what): (Vec<crate::parse_arena::LocIdx>, &str) = match module.typed {
        TypedTree::Implementation(structure) => (
            ta.structure_items(structure.str_items)
                .iter()
                .map(|item| item.str_loc)
                .collect(),
            "Implementation",
        ),
        TypedTree::Interface(signature) => (
            ta.signature_items(signature.sig_items)
                .iter()
                .map(|item| item.sig_loc)
                .collect(),
            "Interface",
        ),
    };
    if config.cli.debug && locs.is_empty() {
        log.item(&format!("{what} 0\n"));
    }
    locs.into_iter().find_map(|loc| {
        let location = arena.to_location(loc);
        let name = arena.get_string(location.loc_start.file_name);
        Path::new(name).exists().then(|| Arc::from(name))
    })
}

/// One run of `rescript-tools reanalyze`: the analyses read each module of
/// the project's packages as a check-only build type-checks it
/// ([`TypedTreeReader`]), on the build's threads, and [`Analysis::report`]
/// puts together what they found once the build is done. So a module is
/// parsed and type-checked once.
pub struct Analysis {
    config: Config,
    files: Files,
    color: bool,
    /// What the command line printed before the analyses ran.
    printed: String,
    /// The files to read, in the order the OCaml tool reads them.
    artifacts: Vec<Artifact>,
    /// The index in `artifacts` of a module's implementation (`false`) or
    /// interface (`true`).
    by_module: HashMap<(String, bool), usize>,
}

/// What a command line asks for.
pub enum Start {
    /// Type-check the project with this as the reader of its typed trees
    /// ([`crate::driver::CompilerOptions::typed_trees`]), which the build's
    /// threads share, then print its [`Analysis::report`], once.
    Analyze(Arc<Analysis>),
    /// Print these bytes and stop.
    Print(Vec<u8>),
}

/// Start `rescript-tools reanalyze` with `args` (the command line after
/// `reanalyze`) in `cwd`, for the modules of `packages`, given in the order
/// of their build directories. `color` says standard output is a terminal.
pub fn start(
    cwd: &Path,
    args: &[String],
    color: bool,
    packages: &[Package],
) -> Result<Start, String> {
    let (config, printed) = match parse_argv(cwd, args)? {
        Command::Analyze(config, printed) => (config, printed),
        Command::Print(text) => return Ok(Start::Print(super::text_bytes(&text))),
    };
    let (artifacts, by_module) = artifacts(packages);
    Ok(Start::Analyze(Arc::new(Analysis {
        config,
        files: Files::new(),
        color,
        printed,
        artifacts,
        by_module,
    })))
}

impl TypedTreeReader for Analysis {
    /// Run the analyses on a module the build type-checked. A build checks
    /// more modules than the analyses read: dependencies that are no local
    /// packages are not read.
    fn read(&self, module: &TypedModule<'_>) {
        let interface = matches!(module.typed, TypedTree::Interface(_));
        let Some(index) = self
            .by_module
            .get(&(module.module_name.to_string(), interface))
        else {
            return;
        };
        let artifact = &self.artifacts[*index];
        let mut log = Log::new(&self.config, &self.files, self.color);
        let mut collected = Collected::default();
        self.process_module(artifact, module, &mut log, &mut collected);
        *artifact.read.lock().unwrap_or_else(PoisonError::into_inner) =
            Some((log.into_logged(), collected));
    }
}

impl Analysis {
    /// `Reactive_analysis.process_cmt_infos`: run the analyses on a module's
    /// implementation or interface.
    fn process_module(
        &self,
        artifact: &Artifact,
        module: &TypedModule<'_>,
        log: &mut Log<'_>,
        collected: &mut Collected,
    ) {
        // OCaml writes no `.cmt` for a file compiled with
        // `-bs-no-bin-annot`, so its tool does not read the file.
        if !module.binary_annotations {
            return;
        }
        let config = &self.config;
        let Some(source_file) = find_source_file(config, log, module) else {
            return;
        };
        let excluded = config.cli.exclude_paths.iter().any(|prefix| {
            let prefix = if is_relative(&source_file) {
                prefix.clone()
            } else {
                filename_concat(&config.cwd, prefix)
            };
            has_prefix(&source_file, &prefix)
        });
        if excluded {
            return;
        }
        let interface = matches!(module.typed, TypedTree::Interface(_));
        let file = FileContext {
            source_file: self.files.intern(&source_file),
            module_name: module_name_of_source(&source_file),
            is_interface: interface || source_file.ends_with('i'),
            source_path: source_file.clone(),
        };
        if config.cli.debug {
            let shown = |path: &str| {
                if config.cli.ci && !is_relative(path) {
                    common::basename(path).to_string()
                } else {
                    path.to_string()
                }
            };
            log.item(&format!(
                "Scanning {} Source:{}\n",
                shown(&artifact.path),
                shown(&source_file)
            ));
        }
        let tree = Tree::new(
            module.arena,
            module.type_ctx,
            module.typed_arena,
            &self.files,
        );
        if config.run.dce {
            let annots = match module.typed {
                TypedTree::Implementation(structure) => dce::Annots::Implementation(structure),
                TypedTree::Interface(signature) => dce::Annots::Interface(signature),
            };
            collected.dce = Some(dce::process_file(
                &tree,
                log,
                config,
                &file,
                annots,
                artifact.has_interface,
            ));
        }
        if config.run.exception
            && let TypedTree::Implementation(structure) = module.typed
        {
            collected.exception = Some(exception::process_structure(
                &tree, log, config, &file, structure,
            ));
        }
        if config.run.termination
            && let TypedTree::Implementation(structure) = module.typed
        {
            arnold::process_structure(&tree, log, config, &mut collected.termination, structure);
        }
    }

    /// `Reanalyze.run_analysis`: what the command prints, once the build
    /// has type-checked the project. What each file's analyses logged and
    /// collected is put together in the files' order, so the report does
    /// not depend on the order the build checked them in.
    ///
    /// Fails when the build did not show a module to the analyses: a report
    /// without it would call what only that module uses dead.
    pub fn report(&self) -> Result<Vec<u8>, String> {
        let (config, files) = (&self.config, &self.files);
        let mut log = Log::new(config, files, self.color);
        log.print(&self.printed);
        if config.cli.json {
            log.json_start();
        }
        let mut dce = Vec::new();
        let mut exception = Vec::new();
        let mut termination = arnold::Stats::default();
        for artifact in &self.artifacts {
            let read = artifact
                .read
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .take();
            let Some((logged, collected)) = read else {
                return Err(format!(
                    "reanalyze: the build did not type-check {}",
                    artifact.path
                ));
            };
            log.append(logged);
            dce.extend(collected.dce);
            exception.extend(collected.exception);
            termination.add(&collected.termination);
        }
        if config.run.dce {
            for issue in dce_solve::solve(config, files, dce) {
                log.warning(issue.loc, issue.description);
            }
        }
        if config.run.exception {
            exception::run_checks(config, files, &mut log, exception);
        }
        if config.run.termination && config.cli.debug {
            termination.report(&mut log);
        }
        log.report();
        if config.cli.json {
            log.json_finish();
        }
        Ok(super::text_bytes(&log.into_output()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::IdGenerator;
    use crate::parser::{Parser, module};
    use crate::types::{TypeCheckContext, TypeContext, initial_env};

    /// A project directory with one module, `src/Test.res`.
    fn project(source: &str) -> (tempfile::TempDir, std::path::PathBuf) {
        let dir = tempfile::tempdir().expect("temporary directory");
        std::fs::write(dir.path().join("rescript.json"), "{}").expect("rescript.json");
        std::fs::create_dir(dir.path().join("src")).expect("src");
        let file = dir.path().join("src").join("Test.res");
        std::fs::write(&file, source).expect("Test.res");
        (dir, file)
    }

    fn test_package(dir: &Path) -> Package {
        Package {
            build_root: dir
                .join("lib")
                .join("rescript")
                .to_string_lossy()
                .into_owned(),
            modules: vec![Module {
                name: "Test".to_string(),
                artifact: "Test".to_string(),
                has_interface: false,
            }],
        }
    }

    fn analysis(dir: &Path, options: &str) -> Arc<Analysis> {
        let args: Vec<String> = options.split(' ').map(str::to_string).collect();
        match start(dir, &args, false, &[test_package(dir)]) {
            Ok(Start::Analyze(analysis)) => analysis,
            Ok(Start::Print(_)) => panic!("the options print"),
            Err(error) => panic!("{error}"),
        }
    }

    /// What `reanalyze <options>` prints for a project whose one module is
    /// `source`, read as a build shows it to the analyses. The module's
    /// path is printed as `Test.res`.
    fn report(options: &str, source: &str) -> String {
        let (dir, file) = project(source);
        let analysis = analysis(dir.path(), options);
        let type_ctx = TypeContext::new(std::sync::Arc::new(IdGenerator::new()));
        let mut parser = Parser::new(file.to_string_lossy(), source);
        let structure = module::parse_structure(&mut parser);
        assert!(!parser.has_errors(), "parse failed");
        crate::types::typecore::prepare_typecheck_arena(parser.arena_mut());
        let arena = parser.arena();
        let mut tctx = TypeCheckContext::new(&type_ctx, arena);
        let env = initial_env(&type_ctx);
        let (typed, _) = crate::types::typemod::type_structure(&mut tctx, &env, arena, &structure)
            .expect("typecheck");
        analysis.read(&TypedModule {
            module_name: "Test",
            arena,
            type_ctx: &type_ctx,
            typed_arena: &tctx.typed,
            typed: TypedTree::Implementation(&typed),
            binary_annotations: true,
        });
        let report = String::from_utf8(analysis.report().expect("report")).expect("UTF-8");
        report.replace(&*file.to_string_lossy(), "Test.res")
    }

    #[test]
    fn a_value_nothing_uses_is_dead_and_what_only_it_uses_is_too() {
        let report = report(
            "-dce -ci",
            "let used = 1\nlet unused = (used, 2)\nlet helper = 3\nlet _ = helper\n",
        );
        assert_eq!(
            report,
            "\n\n  Warning Dead Value\n  Test.res:2:1-22\n  unused is never used\n  \n  Analysis reported 1 issues (Warning Dead Value:1)\n"
        );
    }

    #[test]
    fn transitive_reporting_lists_what_only_dead_code_uses() {
        let report = report(
            "-dce -transitive -ci",
            "let used = 1\nlet unused = (used, 2)\nlet helper = 3\nlet _ = helper\n",
        );
        assert!(
            report.contains("  Test.res:1:1-12\n  used is never used\n"),
            "{report}"
        );
        assert!(
            report.contains("  Test.res:2:1-22\n  unused is never used\n"),
            "{report}"
        );
        assert!(!report.contains("helper"), "{report}");
    }

    #[test]
    fn labels_never_read_and_cases_never_constructed_are_dead_types() {
        let report = report(
            "-dce -ci",
            "type point = {x: int, y: int}\ntype shape = Circle | Square\nlet p = {x: 1, y: 2}\nlet s = Circle\nlet _ = (p.x, s)\n",
        );
        assert!(
            report.contains(
                "  Test.res:1:23-28\n  point.y is a record label never used to read a value\n"
            ),
            "{report}"
        );
        assert!(
            report.contains("  shape.Square is a variant case which is never constructed\n"),
            "{report}"
        );
        assert!(!report.contains("point.x"), "{report}");
        assert!(!report.contains("shape.Circle"), "{report}");
    }

    #[test]
    fn annotations_keep_a_value_live_or_claim_it_dead() {
        let report = report(
            "-dce -ci",
            "@live\nlet kept = 1\n@dead\nlet claimed = 2\nlet _ = claimed\n",
        );
        assert!(!report.contains("kept"), "{report}");
        assert!(
            report.contains("  claimed  is annotated @dead but is live\n"),
            "{report}"
        );
    }

    #[test]
    fn the_debug_log_names_the_artifact_the_ocaml_compiler_would_write() {
        let report = report("-dce -ci -debug", "let a = 1\n");
        assert!(
            report.contains("  Scanning Test.cmt Source:Test.res\n"),
            "{report}"
        );
    }

    #[test]
    fn a_report_needs_every_module_the_build_was_to_show() {
        let (dir, _) = project("let a = 1\n");
        let error = analysis(dir.path(), "-dce -ci")
            .report()
            .expect_err("no module read");
        assert!(
            error.starts_with("reanalyze: the build did not type-check ")
                && error.ends_with("Test.cmt"),
            "{error}"
        );
    }

    #[test]
    fn artifacts_are_read_in_the_order_of_their_file_names() {
        let module = |name: &str, artifact: &str, has_interface| Module {
            name: name.to_string(),
            artifact: artifact.to_string(),
            has_interface,
        };
        let packages = [
            Package {
                build_root: "/p/a/lib/rescript".to_string(),
                modules: vec![
                    module("Zed", "Zed", false),
                    // The file `lower.res` is module `Lower`: uppercase
                    // names sort before it.
                    module("Lower", "lower", true),
                    module("Mid", "Mid-Ns", false),
                ],
            },
            Package {
                build_root: "/p/b/lib/rescript".to_string(),
                modules: vec![module("Abc", "Abc", false)],
            },
        ];
        let (artifacts, by_module) = artifacts(&packages);
        let paths: Vec<&str> = artifacts.iter().map(|a| a.path.as_str()).collect();
        assert_eq!(
            paths,
            [
                "/p/a/lib/rescript/Mid-Ns.cmt",
                "/p/a/lib/rescript/Zed.cmt",
                "/p/a/lib/rescript/lower.cmt",
                "/p/a/lib/rescript/lower.cmti",
                "/p/b/lib/rescript/Abc.cmt",
            ]
        );
        assert_eq!(by_module[&("Lower".to_string(), true)], 3);
        assert_eq!(by_module[&("Abc".to_string(), false)], 4);
        assert!(!by_module.contains_key(&("Zed".to_string(), true)));
    }

    #[test]
    fn module_names_drop_extension_and_namespace() {
        assert_eq!(module_name_of_source("/p/src/Foo.res"), "Foo");
        assert_eq!(module_name_of_source("/p/src/Foo.resi"), "Foo");
        assert_eq!(module_name_of_source("Foo-Ns.res"), "Foo");
    }

    #[test]
    fn the_version_and_the_options_print_without_a_project() {
        let args = |line: &str| -> Vec<String> { line.split(' ').map(str::to_string).collect() };
        assert_eq!(
            output_without_project(&args("-version")).as_deref(),
            Some("reanalyze version 2.22.0\n")
        );
        // Arguments that are no options are printed first; an option's
        // value is not one of them.
        assert_eq!(
            output_without_project(&args("foo -suppress src --version")).as_deref(),
            Some("foo\nreanalyze version 2.22.0\n")
        );
        assert!(output_without_project(&args("-dce -help")).is_some_and(|text| text == usage()));
        assert_eq!(output_without_project(&args("-dce -json")), None);
    }

    #[test]
    fn usage_lists_the_options() {
        assert!(usage().starts_with("reanalyze version 2.22.0\n  -all Run all the analyses.\n"));
    }
}
