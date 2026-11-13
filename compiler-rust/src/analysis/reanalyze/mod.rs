//! `rescript-tools reanalyze` on the Rust typed tree: a port of
//! analysis/reanalyze (the dead code, exception and termination analyses).
//!
//! The OCaml tool reads the `.cmt` and `.cmti` files of a build. Builds
//! write none, so the analyses read each module's typed tree as the session
//! type-checks it, and print what the OCaml tool prints.

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

use super::session::{Project, TypedSource};
use crate::driver::ToolingTyped;
use common::{Config, FileContext, Files, SlotPositions, Tree};
use log::{Log, filename_concat, has_prefix, is_relative};
use std::cell::RefCell;
use std::collections::HashMap;
use std::path::Path;
use std::rc::Rc;
use std::sync::Arc;

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

/// The start of each location a parse allocates, by slot.
type SlotTable = Vec<(i32, i32, i32)>;

fn slot_table(arena: &crate::parse_arena::ParseArena) -> SlotTable {
    let count = arena.parse_location_slot_count().unwrap_or(0);
    (0..count)
        .map(|slot| {
            let location = arena.to_location(crate::parse_arena::LocIdx(slot));
            let start = location.loc_start;
            (start.line, start.bol, start.cnum)
        })
        .collect()
}

/// The located parses of the files declarations are imported from, by file
/// name.
struct Slots<'p> {
    project: &'p dyn Project,
    tables: RefCell<HashMap<String, Option<Rc<SlotTable>>>>,
}

impl SlotPositions for Slots<'_> {
    fn slot_start(&self, file: &str, slot: u32) -> Option<(i32, i32, i32)> {
        if let Some(table) = self.tables.borrow().get(file) {
            return table.as_ref()?.get(slot as usize).copied();
        }
        let table = self
            .project
            .module_for_path(Path::new(file))
            .and_then(|module_name| {
                self.project
                    .parse_located(&module_name, file.ends_with('i'))
            })
            .map(|parsed| Rc::new(slot_table(parsed.arena())));
        let start = table
            .as_ref()
            .and_then(|table| table.get(slot as usize).copied());
        self.tables.borrow_mut().insert(file.to_string(), table);
        start
    }
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

/// What a run collects from the files it reads.
#[derive(Default)]
struct Collected {
    dce: Vec<dce::FileData>,
    exception: Vec<exception::FileResult>,
    termination: arnold::Stats,
}

/// One analysis run: its configuration, output and the project it reads.
struct Run<'a> {
    config: &'a Config,
    files: &'a Files,
    slots: &'a Slots<'a>,
    project: &'a dyn Project,
    log: Log<'a>,
    collected: Collected,
}

impl Run<'_> {
    /// `Find_source_file.cmt`: the file of the first item whose file exists.
    fn find_source_file(&mut self, source: &TypedSource) -> Option<Arc<str>> {
        let arena = source.parsed.arena();
        let ta = &source.typed.typed_arena;
        let (locs, what): (Vec<crate::parse_arena::LocIdx>, &str) = match &source.typed.typed {
            ToolingTyped::Implementation(structure) => (
                ta.structure_items(structure.str_items)
                    .iter()
                    .map(|item| item.str_loc)
                    .collect(),
                "Implementation",
            ),
            ToolingTyped::Interface(signature) => (
                ta.signature_items(signature.sig_items)
                    .iter()
                    .map(|item| item.sig_loc)
                    .collect(),
                "Interface",
            ),
            ToolingTyped::Failed(_) => return None,
        };
        if self.config.cli.debug && locs.is_empty() {
            self.log.item(&format!("{what} 0\n"));
        }
        locs.into_iter().find_map(|loc| {
            let location = arena.to_location(loc);
            let name = arena.get_string(location.loc_start.file_name);
            Path::new(name).exists().then(|| Arc::from(name))
        })
    }

    /// `Reactive_analysis.process_cmt_infos`: run the analyses on a module's
    /// implementation or interface. `artifact` is the `.cmt` or `.cmti` file
    /// the OCaml compiler would write for it.
    fn process_module(
        &mut self,
        module_name: &str,
        interface: bool,
        has_interface: bool,
        artifact: &str,
    ) {
        let Some(source) = self.project.typecheck(module_name, interface) else {
            return;
        };
        // OCaml writes no `.cmt` for a file compiled with
        // `-bs-no-bin-annot`, so its tool does not read the file.
        if !source.typed.binary_annotations {
            return;
        }
        let arena = source.parsed.arena();
        let Some(source_file) = self.find_source_file(&source) else {
            return;
        };
        // Other files' declarations are located in this parse.
        self.slots
            .tables
            .borrow_mut()
            .entry(source_file.to_string())
            .or_insert_with(|| Some(Rc::new(slot_table(arena))));
        let config = self.config;
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
            self.log.item(&format!(
                "Scanning {} Source:{}\n",
                shown(artifact),
                shown(&source_file)
            ));
        }
        let tree = Tree::new(
            arena,
            &source.typed.type_ctx,
            &source.typed.typed_arena,
            self.files,
            self.slots,
        );
        let annots = match &source.typed.typed {
            ToolingTyped::Implementation(structure) => dce::Annots::Implementation(structure),
            ToolingTyped::Interface(signature) => dce::Annots::Interface(signature),
            ToolingTyped::Failed(_) => return,
        };
        if config.run.dce {
            let data =
                dce::process_file(&tree, &mut self.log, config, &file, annots, has_interface);
            self.collected.dce.push(data);
        }
        if config.run.exception
            && let ToolingTyped::Implementation(structure) = &source.typed.typed
        {
            let result =
                exception::process_structure(&tree, &mut self.log, config, &file, structure);
            self.collected.exception.push(result);
        }
        if config.run.termination
            && let ToolingTyped::Implementation(structure) = &source.typed.typed
        {
            arnold::process_structure(
                &tree,
                &mut self.log,
                config,
                &mut self.collected.termination,
                structure,
            );
        }
    }

    /// `Reanalyze.run_analysis`.
    fn run(&mut self) {
        for package in self.project.local_packages() {
            // `Reanalyze.collect_cmt_file_paths`: a package's artifacts, in
            // the order of their file names.
            let mut artifacts: Vec<(String, &str, bool, bool)> = Vec::new();
            for module in &package.modules {
                let Some(paths) = self.project.paths_for_module(&module.name) else {
                    continue;
                };
                let has_interface = paths.interface.is_some();
                if paths.implementation.is_some() {
                    artifacts.push((
                        format!("{}.cmt", module.artifact),
                        &module.name,
                        false,
                        has_interface,
                    ));
                }
                if has_interface {
                    artifacts.push((
                        format!("{}.cmti", module.artifact),
                        &module.name,
                        true,
                        has_interface,
                    ));
                }
            }
            artifacts.sort();
            for (artifact, module_name, interface, has_interface) in artifacts {
                let artifact = filename_concat(&package.build_root, &artifact);
                self.process_module(module_name, interface, has_interface, &artifact);
            }
        }
        if self.config.run.dce {
            let data = std::mem::take(&mut self.collected.dce);
            for issue in dce_solve::solve(self.config, self.files, data) {
                self.log.warning(issue.loc, issue.description);
            }
        }
        if self.config.run.exception {
            let results = std::mem::take(&mut self.collected.exception);
            exception::run_checks(self.config, self.files, &mut self.log, results);
        }
        if self.config.run.termination && self.config.cli.debug {
            self.collected.termination.report(&mut self.log);
        }
    }
}

/// Run `rescript-tools reanalyze` with `args` (the command line after
/// `reanalyze`) in `cwd` and return what it prints. `color` says standard
/// output is a terminal.
pub fn run(
    project: &dyn Project,
    cwd: &Path,
    args: &[String],
    color: bool,
) -> Result<String, String> {
    let (config, printed) = match parse_argv(cwd, args)? {
        Command::Analyze(config, printed) => (config, printed),
        Command::Print(text) => return Ok(text),
    };
    let files = Files::new();
    let slots = Slots {
        project,
        tables: RefCell::new(HashMap::new()),
    };
    let mut run = Run {
        config: &config,
        files: &files,
        slots: &slots,
        project,
        log: Log::new(&config, &files, color),
        collected: Collected::default(),
    };
    run.log.print(&printed);
    if config.cli.json {
        run.log.json_start();
    }
    run.run();
    run.log.report();
    if config.cli.json {
        run.log.json_finish();
    }
    Ok(run.log.into_output())
}

#[cfg(test)]
mod tests {
    use super::*;

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
