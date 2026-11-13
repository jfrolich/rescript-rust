//! Issues and how they are printed (`Issue`, `Log_`, `Emit_json`,
//! `Suppress`, `Exceptions.pp` in analysis/reanalyze/src).

use super::common::{Config, Files, Loc, Pos, basename};
use std::collections::{BTreeMap, BTreeSet};

/// `Exceptions.t`: a set of exception names.
pub type Exceptions = BTreeSet<String>;

/// `Issue.missing_throw_info`.
#[derive(Debug, Clone)]
pub struct MissingThrowInfo {
    /// The value that throws.
    pub exn_name: String,
    /// Where each exception is thrown.
    pub exn_table: BTreeMap<String, BTreeSet<LocKey>>,
    /// The location of the whole binding.
    pub loc_full: Loc,
    /// The exceptions no `@throws` names.
    pub missing_annotations: Exceptions,
    /// Every exception the value throws.
    pub throw_set: Exceptions,
}

/// A location ordered as OCaml's `compare` orders `Location.t`: by file
/// name, then coordinates.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct LocKey {
    start: (std::sync::Arc<str>, i32, i32, i32),
    end: (std::sync::Arc<str>, i32, i32, i32),
    ghost: bool,
}

impl LocKey {
    /// The key of `loc`.
    pub fn new(files: &Files, loc: &Loc) -> LocKey {
        let pos = |p: &Pos| (files.name(p.file), p.lnum, p.bol, p.cnum);
        LocKey {
            start: pos(&loc.start),
            end: pos(&loc.end),
            ghost: loc.ghost,
        }
    }

    /// `Pos.to_string` of the location's start.
    fn start_string(&self) -> String {
        format!(
            "{}:{}:{}",
            basename(&self.start.0),
            self.start.1,
            self.start.3 - self.start.2
        )
    }
}

/// `Issue.severity`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Severity {
    /// A warning.
    Warning,
    /// An error.
    Error,
}

/// `Issue.dead_optional`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeadOptional {
    /// An optional argument no call passes.
    UnusedArgument,
    /// An optional argument every call passes.
    RedundantOptionalArgument,
}

/// `Issue.termination`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Termination {
    /// A recursive function used in a way the analysis does not follow.
    ErrorHygiene,
    /// An expression the analysis does not handle.
    ErrorNotImplemented,
    /// A possible infinite loop.
    ErrorTermination,
    /// Debug output of the analysis.
    TerminationAnalysisInternal,
}

/// `Issue.dead_warning`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeadWarning {
    /// A dead exception.
    Exception,
    /// A dead record label or variant case.
    Type,
    /// A dead value.
    Value,
    /// A dead value whose definition may have side effects.
    ValueWithSideEffects,
    /// A live declaration annotated `@dead`.
    IncorrectDeadAnnotation,
}

/// `Issue.description`.
#[derive(Debug, Clone)]
pub enum Description {
    /// A finding of the exception analysis.
    ExceptionAnalysis {
        /// The finding.
        message: String,
    },
    /// A value that throws exceptions its `@throws` does not name.
    ExceptionAnalysisMissing(MissingThrowInfo),
    /// A module whose items are all dead.
    DeadModule {
        /// The finding.
        message: String,
    },
    /// An optional argument that is never or always passed.
    DeadOptional {
        /// Which of the two.
        dead_optional: DeadOptional,
        /// The finding.
        message: String,
    },
    /// A dead declaration.
    DeadWarning {
        /// What is dead.
        dead_warning: DeadWarning,
        /// The declaration's path.
        path: String,
        /// The finding, after the path.
        message: String,
    },
    /// A finding of the termination analysis.
    Termination {
        /// Its kind.
        termination: Termination,
        /// The finding.
        message: String,
    },
}

/// `Issue.t`.
#[derive(Debug, Clone)]
pub struct Issue {
    /// The issue's name, which the summary counts by.
    pub name: &'static str,
    /// Warning or error.
    pub severity: Severity,
    /// Where it is reported.
    pub loc: Loc,
    /// What is reported.
    pub description: Description,
}

/// `Exceptions.pp`.
pub fn pp_exceptions(
    exn_table: Option<&BTreeMap<String, BTreeSet<LocKey>>>,
    exceptions: &Exceptions,
) -> String {
    let mut out = String::new();
    let is_list = exceptions.len() > 1;
    if is_list {
        out.push('[');
    }
    for (i, name) in exceptions.iter().enumerate() {
        if i > 0 {
            out.push_str(", ");
        }
        out.push_str(name);
        if let Some(locs) = exn_table.and_then(|table| table.get(name)) {
            let positions: Vec<String> = locs.iter().map(LocKey::start_string).collect();
            out.push_str(" (");
            out.push_str(&positions.join(" "));
            out.push(')');
        }
    }
    if is_list {
        out.push(']');
    }
    out
}

/// `Log_.description_to_name`.
fn description_to_name(description: &Description) -> &'static str {
    match description {
        Description::DeadModule { .. } => "Warning Dead Module",
        Description::DeadOptional {
            dead_optional: DeadOptional::UnusedArgument,
            ..
        } => "Warning Unused Argument",
        Description::DeadOptional {
            dead_optional: DeadOptional::RedundantOptionalArgument,
            ..
        } => "Warning Redundant Optional Argument",
        Description::DeadWarning { dead_warning, .. } => dead_warning_name(*dead_warning),
        Description::ExceptionAnalysis { .. } | Description::ExceptionAnalysisMissing(_) => {
            "Exception Analysis"
        }
        Description::Termination { termination, .. } => match termination {
            Termination::ErrorHygiene => "Error Hygiene",
            Termination::ErrorNotImplemented => "Error Not Implemented",
            Termination::ErrorTermination => "Error Termination",
            Termination::TerminationAnalysisInternal => "Termination Analysis Internal",
        },
    }
}

/// The name of a dead code issue (`Analysis_result.make_dead_issue`).
pub fn dead_warning_name(dead_warning: DeadWarning) -> &'static str {
    match dead_warning {
        DeadWarning::Exception => "Warning Dead Exception",
        DeadWarning::Type => "Warning Dead Type",
        DeadWarning::Value => "Warning Dead Value",
        DeadWarning::ValueWithSideEffects => "Warning Dead Value With Side Effects",
        DeadWarning::IncorrectDeadAnnotation => "Incorrect Dead Annotation",
    }
}

/// `Log_.description_to_message`.
fn description_to_message(description: &Description) -> String {
    match description {
        Description::DeadModule { message }
        | Description::DeadOptional { message, .. }
        | Description::ExceptionAnalysis { message }
        | Description::Termination { message, .. } => message.clone(),
        Description::DeadWarning { path, message, .. } => format!("{path} {message}"),
        Description::ExceptionAnalysisMissing(info) => format!(
            "{} might throw {} and is not annotated with @throws({})",
            info.exn_name,
            pp_exceptions(Some(&info.exn_table), &info.throw_set),
            pp_exceptions(None, &info.missing_annotations)
        ),
    }
}

/// `Filename.concat`.
pub fn filename_concat(dir: &str, file: &str) -> String {
    if dir.is_empty() || dir.ends_with('/') {
        format!("{dir}{file}")
    } else {
        format!("{dir}/{file}")
    }
}

/// `Filename.is_relative`.
pub fn is_relative(path: &str) -> bool {
    !path.starts_with('/')
}

/// `Filename.is_implicit`.
fn is_implicit(path: &str) -> bool {
    is_relative(path) && !path.starts_with("./") && !path.starts_with("../")
}

/// Whether `s` starts with `prefix`, as `String.sub s 0 (length prefix) =
/// prefix` tests.
pub fn has_prefix(s: &str, prefix: &str) -> bool {
    s.as_bytes().starts_with(prefix.as_bytes())
}

fn split_on_slash(s: &str) -> Vec<&str> {
    s.split('/').filter(|seg| !seg.is_empty()).collect()
}

/// `Suppress.glob_segment`.
fn glob_segment(pattern: &[u8], segment: &[u8]) -> bool {
    fn aux(pattern: &[u8], segment: &[u8], pi: usize, si: usize) -> bool {
        if pi >= pattern.len() {
            si >= segment.len()
        } else if pattern[pi] == b'*' {
            (si..=segment.len()).any(|skip| aux(pattern, segment, pi + 1, skip))
        } else {
            si < segment.len()
                && pattern[pi] == segment[si]
                && aux(pattern, segment, pi + 1, si + 1)
        }
    }
    aux(pattern, segment, 0, 0)
}

/// `Suppress.glob_match`.
fn glob_match(pattern: &[&str], path: &[&str]) -> bool {
    match (pattern, path) {
        ([], _) => true,
        (["**", rest @ ..], _) => {
            glob_match(rest, path)
                || match path {
                    [_, path_rest @ ..] => glob_match(pattern, path_rest),
                    [] => false,
                }
        }
        ([_, ..], []) => false,
        ([pat, pat_rest @ ..], [seg, path_rest @ ..]) => {
            glob_segment(pat.as_bytes(), seg.as_bytes()) && glob_match(pat_rest, path_rest)
        }
    }
}

/// `Suppress.check_pattern`.
fn check_pattern(project_root: &str, pattern: &str, source: &str) -> bool {
    let is_glob = pattern.contains('*');
    let pattern = if project_root.is_empty() {
        pattern.to_string()
    } else {
        filename_concat(project_root, pattern)
    };
    if is_glob {
        glob_match(&split_on_slash(&pattern), &split_on_slash(source))
    } else {
        has_prefix(source, &pattern)
    }
}

/// What a run prints, and the issues it reports at its end.
pub struct Log<'a> {
    /// The run's configuration.
    pub config: &'a Config,
    /// The run's file names.
    pub files: &'a Files,
    out: String,
    issues: Vec<Issue>,
    json_items: usize,
    /// Whether standard output is a terminal, whose debug output is colored
    /// (`Log_.Color`).
    color: bool,
}

impl<'a> Log<'a> {
    /// An empty log.
    pub fn new(config: &'a Config, files: &'a Files, color: bool) -> Log<'a> {
        Log {
            config,
            files,
            out: String::new(),
            issues: Vec::new(),
            json_items: 0,
            color,
        }
    }

    /// What was printed.
    pub fn into_output(self) -> String {
        self.out
    }

    /// `print_string`.
    pub fn print(&mut self, s: &str) {
        self.out.push_str(s);
    }

    /// `Log_.item`: two spaces, then `text` (which ends its own line).
    pub fn item(&mut self, text: &str) {
        self.out.push_str("  ");
        self.out.push_str(text);
    }

    /// The opening of semantic tag `tag` on the standard formatter
    /// (`Log_.Color.ansi_of_tag`): nothing unless output is colored.
    pub fn tag(&self, tag: &str, text: &str) -> String {
        if !self.color {
            return text.to_string();
        }
        let code = match tag {
            "error" => "1;31",
            "warning" => "1;35",
            "info" => "1;33",
            "dim" => "2",
            "filename" => "36",
            _ => "",
        };
        format!("\x1b[{code}m{text}\x1b[0m")
    }

    /// `Pos.to_string`.
    pub fn pos_string(&self, pos: &Pos) -> String {
        let file = self.files.name(pos.file);
        format!("{}:{}:{}", basename(&file), pos.lnum, pos.col())
    }

    /// `Suppress.filter`: whether issues at `pos` are reported.
    fn filter(&self, pos: &Pos) -> bool {
        let source = self.files.name(pos.file);
        let run = &self.config.run;
        let suppressed = run
            .suppress
            .iter()
            .any(|pattern| check_pattern(&run.project_root, pattern, &source));
        !suppressed
            || run
                .unsuppress
                .iter()
                .any(|pattern| check_pattern(&run.project_root, pattern, &source))
    }

    fn log_issue(&mut self, severity: Severity, loc: Loc, description: Description) {
        if self.filter(&loc.start) {
            self.issues.push(Issue {
                name: description_to_name(&description),
                severity,
                loc,
                description,
            });
        }
    }

    /// `Log_.warning`.
    pub fn warning(&mut self, loc: Loc, description: Description) {
        self.log_issue(Severity::Warning, loc, description);
    }

    /// `Log_.error`.
    pub fn error(&mut self, loc: Loc, description: Description) {
        self.log_issue(Severity::Error, loc, description);
    }

    /// `Emit_json.start`.
    pub fn json_start(&mut self) {
        self.json_items = 0;
        self.out.push('[');
    }

    /// `Emit_json.finish`.
    pub fn json_finish(&mut self) {
        self.out.push_str("\n]\n");
    }

    /// `Log_.Loc.print`: the location on one line, as editors link it.
    fn loc_string(&self, loc: &Loc) -> String {
        let start_char = loc.start.cnum - loc.start.bol;
        let end_char = start_char + loc.end.cnum - loc.start.cnum;
        let line = loc.start.lnum;
        let name = self.files.name(loc.start.file);
        let file = if self.config.cli.ci {
            basename(&name).to_string()
        } else if is_implicit(&name) {
            filename_concat(&self.config.cwd, &name)
        } else {
            name.to_string()
        };
        // `Location.print_loc`: `_none_` prints as the input name, which a
        // tool never sets.
        let file = if file == "_none_" {
            String::new()
        } else {
            file
        };
        // `Location.normalize_range`.
        if start_char == -1 || end_char == -1 {
            file
        } else if start_char + 1 >= end_char {
            format!("{file}:{line}:{}", start_char + 1)
        } else {
            format!("{file}:{line}:{}-{end_char}", start_char + 1)
        }
    }

    /// `Log_.missing_raise_info_to_text`.
    fn additional_info(&self, description: &Description) -> String {
        match description {
            Description::ExceptionAnalysisMissing(info) if self.config.cli.json => {
                let missing = pp_exceptions(None, &info.missing_annotations);
                let line = info.loc_full.start.lnum - 1;
                let character = info.loc_full.start.cnum - info.loc_full.start.bol;
                format!(
                    ",\n  \"annotate\": {{ \"line\": {line}, \"character\": {character}, \"text\": {}, \"action\": {}}}",
                    json_string(&format!("@throws({missing})\\n")),
                    json_string("Add @throws annotation")
                )
            }
            _ => String::new(),
        }
    }

    /// `Log_.log_issue`: an issue as text or as a JSON object.
    fn issue_string(&mut self, issue: &Issue) -> String {
        let message = description_to_message(&issue.description);
        let additional = self.additional_info(&issue.description);
        if self.config.cli.json {
            let loc = &issue.loc;
            let file = self.files.name(loc.start.file);
            self.json_items += 1;
            let kind = match issue.severity {
                Severity::Warning => "warning",
                Severity::Error => "error",
            };
            format!(
                "{}{{\n  \"name\": {},\n  \"kind\": {},\n  \"file\": {},\n  \"range\": [{},{},{},{}],\n  \"message\": {}{additional}\n}}",
                if self.json_items == 1 { "\n" } else { ",\n" },
                json_string(issue.name),
                json_string(kind),
                json_string(&file),
                loc.start.lnum - 1,
                loc.start.cnum - loc.start.bol,
                loc.end.lnum - 1,
                loc.end.cnum - loc.start.bol,
                json_string(&message),
            )
        } else {
            format!(
                "\n  {}\n  {}\n  {message}{additional}\n",
                issue.name,
                self.loc_string(&issue.loc)
            )
        }
    }

    /// `Log_.Stats.report`, then `Log_.Stats.clear`.
    pub fn report(&mut self) {
        let issues = std::mem::take(&mut self.issues);
        let mut counters: BTreeMap<&'static str, usize> = BTreeMap::new();
        for issue in &issues {
            let text = self.issue_string(issue);
            self.out.push_str(&text);
            *counters.entry(issue.name).or_default() += 1;
        }
        if self.config.cli.json {
            return;
        }
        if !counters.is_empty() {
            self.item("\n");
        }
        let summary = if counters.is_empty() {
            String::new()
        } else {
            format!(
                " ({})",
                counters
                    .iter()
                    .map(|(name, count)| format!("{name}:{count}"))
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        };
        self.item(&format!(
            "Analysis reported {} issues{summary}\n",
            issues.len()
        ));
    }
}

/// `Emit_json.json_string`: `Yojson.Safe.to_string (`String text)`.
fn json_string(text: &str) -> String {
    super::super::json::escape_string(text)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn globs_match_path_prefixes() {
        assert!(check_pattern("/p", "src", "/p/src/A.res"));
        assert!(!check_pattern("/p", "src", "/p/lib/A.res"));
        assert!(check_pattern("/p", "src/*/gen", "/p/src/x/gen/A.res"));
        assert!(check_pattern("/p", "**/gen", "/p/src/x/gen/A.res"));
        assert!(!check_pattern("/p", "src/*/gen", "/p/src/x/y/gen/A.res"));
        assert!(check_pattern("/p", "src/A*.res", "/p/src/Abc.res"));
    }

    #[test]
    fn exceptions_print_as_ocaml_does() {
        let one: Exceptions = ["Not_found".to_string()].into();
        assert_eq!(pp_exceptions(None, &one), "Not_found");
        let two: Exceptions = ["B".to_string(), "A".to_string()].into();
        assert_eq!(pp_exceptions(None, &two), "[A, B]");
    }
}
