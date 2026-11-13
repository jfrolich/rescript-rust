//! The dead code analysis, project-wide: merge the files' data, compute
//! which declarations are live and report the dead ones (`Reactive_merge`,
//! `Reactive_type_deps`, `Reactive_exception_refs`, `Reactive_coercions`,
//! `Reactive_liveness`, `Reactive_solver`, `Dead_common`,
//! `Cross_file_items_store` and `Dead_optional_args.check` in
//! analysis/reanalyze/src).
//!
//! OCaml keeps these as incrementally updated collections; one run needs
//! their final values only, so each is computed once, in the order the
//! files were read.

use super::common::*;
use super::dce::*;
use super::log::{DeadOptional, DeadWarning, Description, Issue, Severity, dead_warning_name};
use indexmap::{IndexMap, IndexSet};
use std::collections::{HashMap, HashSet};

type Refs = IndexMap<Pos, IndexSet<Pos>>;

fn add_ref(refs: &mut Refs, pos_from: Pos, pos_to: Pos) {
    refs.entry(pos_from).or_default().insert(pos_to);
}

/// `Reactive_merge.t`: the files' data as one.
struct Merged {
    decls: IndexMap<Pos, Decl>,
    annotations: HashMap<Pos, AnnotatedAs>,
    value_refs_from: Refs,
    type_refs_from: Refs,
    cross_file: CrossFileItems,
}

fn merge(files: Vec<FileData>) -> Merged {
    let mut merged = Merged {
        decls: IndexMap::new(),
        annotations: HashMap::new(),
        value_refs_from: IndexMap::new(),
        type_refs_from: IndexMap::new(),
        cross_file: CrossFileItems::default(),
    };
    for file in files {
        merged.decls.extend(file.decls);
        merged.annotations.extend(file.annotations);
        for (pos_from, targets) in file.value_refs_from {
            merged
                .value_refs_from
                .entry(pos_from)
                .or_default()
                .extend(targets);
        }
        for (pos_from, targets) in file.type_refs_from {
            merged
                .type_refs_from
                .entry(pos_from)
                .or_default()
                .extend(targets);
        }
        let cross = file.cross_file;
        merged
            .cross_file
            .exception_refs
            .extend(cross.exception_refs);
        merged
            .cross_file
            .optional_arg_calls
            .extend(cross.optional_arg_calls);
        merged.cross_file.function_refs.extend(cross.function_refs);
        merged
            .cross_file
            .optional_arg_value_escapes
            .extend(cross.optional_arg_value_escapes);
        merged.cross_file.coercions.extend(cross.coercions);
    }
    merged
}

/// `Reactive_exception_refs`: a use of an exception another file declares
/// is a value reference to its declaration.
fn exception_refs(merged: &Merged, value_refs: &mut Refs) {
    let mut exception_decls: HashMap<&[Name], Pos> = HashMap::new();
    for decl in merged.decls.values() {
        if decl.decl_kind == DeclKind::Exception {
            exception_decls.insert(&decl.path, decl.pos);
        }
    }
    for (path, loc_from) in &merged.cross_file.exception_refs {
        if let Some(pos_to) = exception_decls.get(path.as_slice()) {
            add_ref(value_refs, loc_from.start, *pos_to);
        }
    }
}

/// `Reactive_type_deps`: labels and cases of one type declared more than
/// once (in an interface and its implementation, in a signature and its
/// structure, by a re-export) are live together.
fn type_deps(merged: &Merged, type_refs: &mut Refs) {
    let mut decl_by_path: IndexMap<&[Name], Vec<&Decl>> = IndexMap::new();
    for decl in merged.decls.values() {
        if decl.decl_kind.is_type() {
            decl_by_path.entry(&decl.path).or_default().push(decl);
        }
    }
    let mut link = |a: Pos, b: Pos| {
        add_ref(type_refs, a, b);
        add_ref(type_refs, b, a);
    };
    // Declarations at the same path.
    for decls in decl_by_path.values() {
        if let [first, rest @ ..] = decls.as_slice() {
            for other in rest {
                link(first.pos, other.pos);
            }
        }
    }
    let first_at = |path: &[Name]| decl_by_path.get(path).and_then(|decls| decls.first());
    for decl in merged.decls.values() {
        if !decl.decl_kind.is_type() {
            continue;
        }
        let [type_label_name, path_to_type @ ..] = decl.path.as_slice() else {
            continue;
        };
        let with_label = |path: DcePath| {
            let mut full = vec![type_label_name.clone()];
            full.extend(path);
            full
        };
        let is_interface = decl
            .path
            .last()
            .is_none_or(|module| !module.starts_with('+'));
        if !is_interface {
            // An implementation's declaration and its interface's.
            let path_1 = path_module_to_interface(path_to_type);
            let path_2 = path_type_to_interface(&path_1);
            let found = first_at(&with_label(path_1)).or_else(|| first_at(&with_label(path_2)));
            if let Some(interface) = found {
                link(decl.pos, interface.pos);
            }
        } else {
            let impl_path = with_label(path_module_to_implementation(path_to_type));
            if let Some(implementation) = first_at(&impl_path) {
                link(decl.pos, implementation.pos);
            }
        }
        // A re-exported type's label and the manifest type's.
        if let Some(manifest_type_path) = &decl.manifest_type_path
            && let Some(manifest) = first_at(&with_label(manifest_type_path.clone()))
            && manifest.pos != decl.pos
        {
            link(decl.pos, manifest.pos);
        }
    }
}

/// `Reactive_coercions`: reading a label of a coercion's target type reads
/// the source type's label of that name.
fn coercion_refs(merged: &Merged, type_refs: &mut Refs) {
    let mut labels_by_type_path: HashMap<&[Name], Vec<(&Name, Pos)>> = HashMap::new();
    for decl in merged.decls.values() {
        if decl.decl_kind == DeclKind::RecordLabel
            && let [label, type_path @ ..] = decl.path.as_slice()
        {
            labels_by_type_path
                .entry(type_path)
                .or_default()
                .push((label, decl.pos));
        }
    }
    let labels_of = |paths: &[DcePath]| -> Vec<(&Name, Pos)> {
        paths
            .iter()
            .filter_map(|path| labels_by_type_path.get(path.as_slice()))
            .flatten()
            .copied()
            .collect()
    };
    let coercions: IndexSet<&Coercion> = merged.cross_file.coercions.iter().collect();
    for coercion in coercions {
        let source_labels = labels_of(&coercion.source_type_paths);
        let target_labels = labels_of(&coercion.target_type_paths);
        // `Dead_type.pair_coercion_labels`.
        for (label, target) in &target_labels {
            if let Some((_, source)) = source_labels.iter().find(|(name, _)| name == label)
                && source != target
            {
                add_ref(type_refs, *target, *source);
            }
        }
    }
}

/// `Reactive_decl_refs`: for each declaration, what the references within
/// its range use.
fn decl_edges(decls: &IndexMap<Pos, Decl>, refs: [&Refs; 2]) -> HashMap<Pos, Vec<Pos>> {
    let mut decls_by_file: HashMap<FileId, Vec<&Decl>> = HashMap::new();
    for decl in decls.values() {
        decls_by_file.entry(decl.pos.file).or_default().push(decl);
    }
    let mut sources_by_file: HashMap<FileId, Vec<(i32, &IndexSet<Pos>)>> = HashMap::new();
    for refs in refs {
        for (pos_from, targets) in refs {
            sources_by_file
                .entry(pos_from.file)
                .or_default()
                .push((pos_from.cnum, targets));
        }
    }
    let mut edges: HashMap<Pos, Vec<Pos>> = HashMap::new();
    for (file, mut file_decls) in decls_by_file {
        let Some(sources) = sources_by_file.get_mut(&file) else {
            continue;
        };
        file_decls.sort_by_key(|decl| decl.pos_start.cnum);
        sources.sort_by_key(|(cnum, _)| *cnum);
        // Sweep the sources in order, keeping the declarations that started
        // and have not ended yet.
        let mut next = 0;
        let mut open: Vec<&Decl> = Vec::new();
        for (cnum, targets) in sources.iter() {
            while next < file_decls.len() && file_decls[next].pos_start.cnum <= *cnum {
                open.push(file_decls[next]);
                next += 1;
            }
            open.retain(|decl| decl.pos_end.cnum >= *cnum);
            for decl in &open {
                edges
                    .entry(decl.pos)
                    .or_default()
                    .extend(targets.iter().copied());
            }
        }
    }
    edges
}

/// `Reactive_liveness`: the positions reachable from the roots.
fn liveness(merged: &Merged, value_refs: &Refs, type_refs: &Refs) -> HashSet<Pos> {
    let edges = decl_edges(&merged.decls, [value_refs, type_refs]);
    let mut live: HashSet<Pos> = HashSet::new();
    let mut work: Vec<Pos> = Vec::new();
    let add = |pos: Pos, live: &mut HashSet<Pos>, work: &mut Vec<Pos>| {
        if live.insert(pos) {
            work.push(pos);
        }
    };
    // Roots: what a position that is no declaration uses, and annotated
    // declarations.
    for refs in [value_refs, type_refs] {
        for (pos_from, targets) in refs {
            if !merged.decls.contains_key(pos_from) {
                for target in targets {
                    add(*target, &mut live, &mut work);
                }
            }
        }
    }
    for pos in merged.decls.keys() {
        if matches!(
            merged.annotations.get(pos),
            Some(AnnotatedAs::Live | AnnotatedAs::GenType)
        ) {
            add(*pos, &mut live, &mut work);
        }
    }
    while let Some(pos) = work.pop() {
        if let Some(targets) = edges.get(&pos) {
            for target in targets {
                add(*target, &mut live, &mut work);
            }
        }
    }
    live
}

/// `Dead_common.decl_get_loc`.
fn decl_get_loc(decl: &Decl) -> Loc {
    let offset = match decl.pos_adjustment {
        PosAdjustment::FirstVariant | PosAdjustment::Nothing => 0,
        PosAdjustment::OtherVariant => 2,
    };
    let cnum_with_offset = decl.pos_start.cnum + offset;
    let start = if cnum_with_offset < decl.pos_end.cnum {
        Pos {
            cnum: cnum_with_offset,
            ..decl.pos_start
        }
    } else {
        decl.pos_start
    };
    Loc {
        start,
        end: decl.pos_end,
        ghost: false,
    }
}

/// `Dead_common.make_dead_issue`.
fn make_dead_issue(decl: &Decl, message: &str, dead_warning: DeadWarning) -> Issue {
    Issue {
        name: dead_warning_name(dead_warning),
        severity: Severity::Warning,
        loc: decl_get_loc(decl),
        description: Description::DeadWarning {
            dead_warning,
            path: path_without_head(&decl.path),
            message: message.to_string(),
        },
    }
}

/// `Analysis_result.make_dead_module_issue`.
fn make_dead_module_issue(loc: Loc, module_name: &Name) -> Issue {
    Issue {
        name: "Warning Dead Module",
        severity: Severity::Warning,
        loc,
        description: Description::DeadModule {
            message: format!(
                "{} is a dead module as all its items are dead.",
                name_to_interface(module_name)
            ),
        },
    }
}

/// `Reactive_solver.decl_module_name`.
fn decl_module_name(decl: &Decl) -> Name {
    path_to_module_name(decl.decl_kind.is_type(), &decl.path)
}

/// The location a dead module is reported at: a ghost location is the
/// start of the file.
fn dead_module_loc(loc: Loc, file: FileId) -> Loc {
    if loc.ghost {
        let pos = Pos {
            file,
            lnum: 0,
            bol: 0,
            cnum: 0,
        };
        Loc {
            start: pos,
            end: pos,
            ghost: false,
        }
    } else {
        loc
    }
}

/// `Dead_common.ref_is_below`.
fn ref_is_below(decl: &Decl, pos_from: &Pos) -> bool {
    decl.pos.file != pos_from.file
        || (decl.pos.cnum < pos_from.cnum
            // Not a function defined inside a function, such as a callback.
            && decl.pos_end.cnum < pos_from.cnum)
}

/// `Dead_common.report_declaration`: the issue of a dead declaration, if
/// one is reported. `max_end` is `Reporting_context`.
fn report_declaration(
    decl: &Decl,
    max_end: &mut Pos,
    should_report: bool,
    transitive: bool,
    has_ref_below: impl Fn(&Decl) -> bool,
    modules_with_values: &mut IndexSet<Name>,
) -> Option<Issue> {
    // `is_inside_reported_value`.
    let file_has_changed = max_end.file != decl.pos.file;
    let inside_reported_value =
        decl.is_value() && !file_has_changed && max_end.cnum > decl.pos.cnum;
    if !inside_reported_value
        && decl.is_value()
        && (file_has_changed || decl.pos_end.cnum > max_end.cnum)
    {
        *max_end = decl.pos_end;
    }
    // A re-exported type's labels are restated, not declared.
    let should_report =
        should_report && !(decl.decl_kind.is_type() && decl.manifest_type_path.is_some());
    if !should_report {
        return None;
    }
    let name = decl.path.first();
    let (dead_warning, message): (DeadWarning, String) = match &decl.decl_kind {
        DeclKind::Exception => (
            DeadWarning::Exception,
            "is never raised or passed as value".to_string(),
        ),
        DeclKind::Value { side_effects, .. } => {
            let no_side_effects_or_underscore =
                !side_effects || name.is_some_and(|name| name_starts_with_underscore(name));
            (
                if no_side_effects_or_underscore {
                    DeadWarning::Value
                } else {
                    DeadWarning::ValueWithSideEffects
                },
                if name.is_some_and(|name| name_is_underscore(name)) {
                    "has no side effects and can be removed".to_string()
                } else if no_side_effects_or_underscore {
                    "is never used".to_string()
                } else {
                    "is never used and could have side effects".to_string()
                },
            )
        }
        DeclKind::RecordLabel => (
            DeadWarning::Type,
            "is a record label never used to read a value".to_string(),
        ),
        DeclKind::VariantCase => (
            DeadWarning::Type,
            "is a variant case which is never constructed".to_string(),
        ),
    };
    let should_emit_warning = !inside_reported_value
        // `Config.report_underscore` is off.
        && !name.is_some_and(|name| name_is_underscore(name))
        && (transitive || !has_ref_below(decl));
    if !should_emit_warning {
        return None;
    }
    modules_with_values.insert(decl_module_name(decl));
    Some(make_dead_issue(decl, &message, dead_warning))
}

/// `Analysis_result.issue_sort_key`: issues are reported by position, on
/// the file's base name first so the order is the same wherever the project
/// is checked out.
fn sort_issues(files: &Files, issues: &mut [Issue]) {
    issues.sort_by_cached_key(|issue| {
        let pos = issue.loc.start;
        let name = files.name(pos.file);
        (
            basename(&name).to_string(),
            pos.lnum,
            pos.cnum - pos.bol,
            issue.name,
            name,
        )
    });
}

/// `Cross_file_items_store.compute_optional_args_state`.
fn optional_args_state(
    merged: &Merged,
    is_live: impl Fn(&Pos) -> bool,
) -> HashMap<Pos, OptionalArgs> {
    let mut state: HashMap<Pos, OptionalArgs> = HashMap::new();
    let initial = |pos: &Pos| match merged.decls.get(pos) {
        Some(Decl {
            decl_kind: DeclKind::Value { optional_args, .. },
            ..
        }) => optional_args.clone(),
        _ => OptionalArgs::default(),
    };
    for call in &merged.cross_file.optional_arg_calls {
        if is_live(&call.pos_from) {
            let current = state
                .get(&call.pos_to)
                .cloned()
                .unwrap_or_else(|| initial(&call.pos_to));
            state.insert(
                call.pos_to,
                current.apply_call(&call.arg_names, &call.arg_names_maybe),
            );
        }
    }
    for (pos_from, pos_to) in &merged.cross_file.function_refs {
        if is_live(pos_from) {
            let state_from = state
                .get(pos_from)
                .cloned()
                .unwrap_or_else(|| initial(pos_from));
            let state_to = state
                .get(pos_to)
                .cloned()
                .unwrap_or_else(|| initial(pos_to));
            if !state_to.is_empty() {
                let (updated_from, updated_to) = OptionalArgs::combine_pair(&state_from, &state_to);
                state.insert(*pos_from, updated_from);
                state.insert(*pos_to, updated_to);
            }
        }
    }
    state
}

/// `Cross_file_items_store.compute_live_optional_arg_value_escapes`: the
/// functions live code uses as values, and the functions standing for them.
fn live_optional_arg_value_escapes(
    merged: &Merged,
    is_live: impl Fn(&Pos) -> bool,
) -> HashSet<Pos> {
    let mut escapes: HashSet<Pos> = merged
        .cross_file
        .optional_arg_value_escapes
        .iter()
        .filter(|(pos_from, _)| is_live(pos_from))
        .map(|(_, pos_to)| *pos_to)
        .collect();
    let function_refs: Vec<(Pos, Pos)> = merged
        .cross_file
        .function_refs
        .iter()
        .filter(|(pos_from, _)| is_live(pos_from))
        .copied()
        .collect();
    loop {
        let before = escapes.len();
        for (pos_from, pos_to) in &function_refs {
            if escapes.contains(pos_from) {
                escapes.insert(*pos_to);
            } else if escapes.contains(pos_to) {
                escapes.insert(*pos_from);
            }
        }
        if escapes.len() == before {
            return escapes;
        }
    }
}

/// `Dead_optional_args.check`.
fn check_optional_args(
    decl: &Decl,
    state: &HashMap<Pos, OptionalArgs>,
    escapes: &HashSet<Pos>,
    annotations: &HashMap<Pos, AnnotatedAs>,
    issues: &mut Vec<Issue>,
) {
    let DeclKind::Value {
        reports_optional_args: true,
        optional_args,
        ..
    } = &decl.decl_kind
    else {
        return;
    };
    // A function live code uses as a value has callers the analysis does
    // not see, which may pass or omit any optional argument.
    if escapes.contains(&decl.pos)
        || matches!(
            annotations.get(&decl.pos),
            Some(AnnotatedAs::Live | AnnotatedAs::GenType)
        )
    {
        return;
    }
    let state = state.get(&decl.pos).unwrap_or(optional_args);
    let loc = decl_get_loc(decl);
    let function = path_without_head(&decl.path);
    for name in &state.unused {
        issues.push(Issue {
            name: "Warning Unused Argument",
            severity: Severity::Warning,
            loc,
            description: Description::DeadOptional {
                dead_optional: DeadOptional::UnusedArgument,
                message: format!("optional argument {name} of function {function} is never used"),
            },
        });
    }
    for name in &state.always_used {
        issues.push(Issue {
            name: "Warning Redundant Optional Argument",
            severity: Severity::Warning,
            loc,
            description: Description::DeadOptional {
                dead_optional: DeadOptional::RedundantOptionalArgument,
                message: format!(
                    "optional argument {name} of function {function} is always supplied ({} calls)",
                    state.count
                ),
            },
        });
    }
}

/// The dead code issues of a project, in the order they are reported
/// (`Reanalyze.run_analysis`, solving section).
pub fn solve(config: &Config, files: &Files, data: Vec<FileData>) -> Vec<Issue> {
    let merged = merge(data);
    let mut value_refs = merged.value_refs_from.clone();
    exception_refs(&merged, &mut value_refs);
    let mut type_refs = merged.type_refs_from.clone();
    type_deps(&merged, &mut type_refs);
    coercion_refs(&merged, &mut type_refs);
    let live = liveness(&merged, &value_refs, &type_refs);
    let transitive = config.run.transitive;

    let is_live_decl = |decl: &Decl| live.contains(&decl.pos);
    let mut issues: Vec<Issue> = Vec::new();

    // Dead modules: modules with a dead declaration and no live one. They
    // are reported in transitive mode only.
    let mut dead_modules: IndexMap<Name, (Loc, FileId)> = IndexMap::new();
    if transitive {
        let mut modules_with_live: HashSet<Name> = HashSet::new();
        for decl in merged.decls.values() {
            if is_live_decl(decl) {
                modules_with_live.insert(decl_module_name(decl));
            } else {
                dead_modules
                    .entry(decl_module_name(decl))
                    .or_insert((decl.module_loc, decl.pos.file));
            }
        }
        dead_modules.retain(|name, _| !modules_with_live.contains(name));
    }

    // Live declarations annotated `@dead`.
    let mut reported_modules: HashSet<Name> = HashSet::new();
    for decl in merged.decls.values() {
        if is_live_decl(decl) && merged.annotations.get(&decl.pos) == Some(&AnnotatedAs::Dead) {
            let module_name = decl_module_name(decl);
            if let Some((loc, file)) = dead_modules.get(&module_name)
                && reported_modules.insert(module_name.clone())
            {
                issues.push(make_dead_module_issue(
                    dead_module_loc(*loc, *file),
                    &module_name,
                ));
            }
            issues.push(make_dead_issue(
                decl,
                " is annotated @dead but is live",
                DeadWarning::IncorrectDeadAnnotation,
            ));
        }
    }

    // Dead declarations, by file.
    let mut dead_by_file: IndexMap<FileId, Vec<&Decl>> = IndexMap::new();
    for decl in merged.decls.values() {
        if !is_live_decl(decl) {
            dead_by_file.entry(decl.pos.file).or_default().push(decl);
        }
    }
    let has_ref_below = |decl: &Decl| {
        // Every reference counts: one from another file is below as well.
        merged
            .value_refs_from
            .iter()
            .any(|(pos_from, targets)| targets.contains(&decl.pos) && ref_is_below(decl, pos_from))
    };
    let mut modules_with_reported: IndexSet<Name> = IndexSet::new();
    let mut dead_issues: Vec<Issue> = Vec::new();
    for decls in dead_by_file.values_mut() {
        // `Decl.compare_for_reporting`: one file's declarations by position.
        decls.sort_by_key(|decl| (decl.pos.lnum, decl.pos.bol, decl.pos.cnum));
        let mut max_end = Pos::DUMMY;
        for decl in decls.iter() {
            let should_report = !merged.annotations.contains_key(&decl.pos);
            if let Some(issue) = report_declaration(
                decl,
                &mut max_end,
                should_report,
                transitive,
                has_ref_below,
                &mut modules_with_reported,
            ) {
                dead_issues.push(issue);
            }
        }
    }
    // A dead module is reported when one of its values is.
    for (module_name, (loc, file)) in &dead_modules {
        if modules_with_reported.contains(module_name) {
            issues.push(make_dead_module_issue(
                dead_module_loc(*loc, *file),
                module_name,
            ));
        }
    }
    issues.extend(dead_issues);

    // Optional arguments of live declarations, counting the calls live
    // code makes.
    let is_live = |pos: &Pos| !merged.decls.contains_key(pos) || live.contains(pos);
    let state = optional_args_state(&merged, is_live);
    let escapes = live_optional_arg_value_escapes(&merged, is_live);
    for decl in merged.decls.values() {
        if is_live_decl(decl) {
            check_optional_args(decl, &state, &escapes, &merged.annotations, &mut issues);
        }
    }

    sort_issues(files, &mut issues);
    issues
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pos(cnum: i32) -> Pos {
        Pos {
            file: FileId(2),
            lnum: 1,
            bol: 0,
            cnum,
        }
    }

    fn value(name: &str, start: i32, end: i32) -> Decl {
        Decl {
            decl_kind: DeclKind::Value {
                is_toplevel: true,
                reports_optional_args: false,
                optional_args: OptionalArgs::default(),
                side_effects: false,
            },
            module_loc: Loc::NONE,
            pos_adjustment: PosAdjustment::Nothing,
            path: vec![name_create(name, false), name_create("M", false)],
            manifest_type_path: None,
            pos: pos(start),
            pos_end: pos(end),
            pos_start: pos(start),
        }
    }

    #[test]
    fn a_value_only_dead_code_uses_is_dead() {
        let files = Files::new();
        files.intern("/p/M.res");
        let mut data = FileData::default();
        // `a` is used by `b`, `b` by nothing; `c` by a top-level expression.
        for decl in [value("a", 0, 5), value("b", 10, 20), value("c", 30, 35)] {
            data.decls.insert(decl.pos, decl);
        }
        add_ref(&mut data.value_refs_from, pos(10), pos(0));
        add_ref(&mut data.value_refs_from, pos(50), pos(30));
        let config = Config {
            run: RunConfig {
                transitive: true,
                ..RunConfig::default()
            },
            ..Config::default()
        };
        let issues = solve(&config, &files, vec![data]);
        let names: Vec<(&str, i32)> = issues.iter().map(|i| (i.name, i.loc.start.cnum)).collect();
        // The module has a live value, `c`, so it is not a dead module.
        assert_eq!(
            names,
            [("Warning Dead Value", 0), ("Warning Dead Value", 10)]
        );
    }

    #[test]
    fn a_module_whose_values_are_all_dead_is_reported_before_them() {
        let files = Files::new();
        files.intern("/p/M.res");
        let mut data = FileData::default();
        let decl = value("a", 0, 5);
        data.decls.insert(decl.pos, decl);
        let config = Config {
            run: RunConfig {
                transitive: true,
                ..RunConfig::default()
            },
            ..Config::default()
        };
        let issues = solve(&config, &files, vec![data]);
        let names: Vec<&str> = issues.iter().map(|i| i.name).collect();
        assert_eq!(names, ["Warning Dead Module", "Warning Dead Value"]);
    }

    #[test]
    fn a_value_used_from_below_is_not_reported_without_transitivity() {
        let files = Files::new();
        files.intern("/p/M.res");
        let mut data = FileData::default();
        for decl in [value("a", 0, 5), value("b", 10, 20)] {
            data.decls.insert(decl.pos, decl);
        }
        add_ref(&mut data.value_refs_from, pos(10), pos(0));
        let issues = solve(&Config::default(), &files, vec![data]);
        let reported: Vec<i32> = issues.iter().map(|i| i.loc.start.cnum).collect();
        assert_eq!(reported, [10]);
    }
}
