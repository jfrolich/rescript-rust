//! Editor tooling: a port of the OCaml analysis (analysis/src) that runs
//! inside the build system's watcher, on the Rust parse and typed trees.
//!
//! The watcher keeps the published interfaces in memory and type-checks the
//! module a command needs on demand; no typed artifacts are serialized. A
//! command gets its arguments as `rescript-editor-analysis` would (see
//! analysis/bin/main.ml) and returns what that binary prints.

pub mod commands;
pub mod docgen;
pub mod document_symbol;
pub mod hashtbl;
pub mod hover;
pub mod json;
pub mod process_attributes;
pub mod process_cmt;
pub mod process_extra;
pub mod reanalyze;
pub mod references;
pub mod resolve_path;
pub mod session;
pub mod shared;
pub mod shared_types;
pub mod uri;

use json::Json;
use std::path::{Path, PathBuf};

/// `Files.classify_source_file`, for the files analysis works on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FileKind {
    /// A `.res` implementation.
    Res,
    /// A `.resi` interface.
    Resi,
}

impl FileKind {
    /// The kind of the file at `path`, judged by its extension.
    pub fn of_path(path: &str) -> FileKind {
        if path.ends_with(".resi") {
            FileKind::Resi
        } else {
            FileKind::Res
        }
    }
}

/// An LSP position: 0-based line and character offset.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Position {
    /// The 0-based line.
    pub line: i32,
    /// The 0-based character offset within the line.
    pub character: i32,
}

impl Position {
    /// `Utils.cmt_pos_to_position`.
    pub fn of_lexing(pos: &crate::location::Position) -> Position {
        Position {
            line: pos.line - 1,
            character: pos.cnum - pos.bol,
        }
    }

    /// The position as an LSP `Position` object.
    pub fn to_json(self) -> Json {
        Json::assoc([
            ("character", Json::Int(self.character.into())),
            ("line", Json::Int(self.line.into())),
        ])
    }
}

/// An LSP range.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Range {
    /// Where the range starts.
    pub start: Position,
    /// Where the range ends.
    pub end: Position,
}

impl Range {
    /// `Utils.cmt_loc_to_range`.
    pub fn of_positions(
        start: &crate::location::Position,
        end: &crate::location::Position,
    ) -> Range {
        Range {
            start: Position::of_lexing(start),
            end: Position::of_lexing(end),
        }
    }

    /// The range as an LSP `Range` object.
    pub fn to_json(self) -> Json {
        Json::assoc([("end", self.end.to_json()), ("start", self.start.to_json())])
    }

    /// Start, then end, as `Document_symbol.compare_symbol` orders.
    pub fn key(&self) -> (Position, Position) {
        (self.start, self.end)
    }

    /// Whether `self` lies within `other`.
    pub fn is_inside(&self, other: &Range) -> bool {
        self.start >= other.start && self.end <= other.end
    }
}

/// A command for the analysis, as given to `rescript-editor-analysis`.
#[derive(Debug, Clone)]
pub struct Request {
    /// The client's working directory, which relative paths are resolved
    /// against (and printed as given, as the OCaml binary does).
    pub cwd: PathBuf,
    /// The command line after the program name, as `rescript-editor-analysis`
    /// receives it: the command name, then its arguments.
    pub args: Vec<String>,
}

/// Collects what a command prints (`print_string`/`print_endline`).
#[derive(Default)]
pub struct Output(String);

impl Output {
    /// `print_string`.
    pub fn print(&mut self, s: &str) {
        self.0.push_str(s);
    }

    /// `print_endline`.
    pub fn print_endline(&mut self, s: &str) {
        self.0.push_str(s);
        self.0.push('\n');
    }

    /// `print_newline`.
    pub fn print_newline(&mut self) {
        self.0.push('\n');
    }

    /// The printed bytes.
    pub fn into_bytes(self) -> Vec<u8> {
        text_bytes(&self.0)
    }
}

/// The bytes of analysis text. Source text is held as Latin-1 characters
/// standing for bytes; other characters are encoded as UTF-8.
fn text_bytes(text: &str) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(text.len());
    for c in text.chars() {
        if (c as u32) <= 0xFF {
            bytes.push(c as u8);
        } else {
            let mut buf = [0u8; 4];
            bytes.extend_from_slice(c.encode_utf8(&mut buf).as_bytes());
        }
    }
    bytes
}

fn resolve(cwd: &Path, path: &str) -> PathBuf {
    cwd.join(path)
}

/// `Files.read_file`, as the Latin-1 text the parser reads.
fn read_file(path: &Path) -> Option<String> {
    std::fs::read(path)
        .ok()
        .map(crate::source_text::latin1_bytes_to_string)
}

/// What commands run in: the project and how URIs print.
struct Cli<'p> {
    cwd: PathBuf,
    session: session::ProjectSession<'p>,
    uri_style: uri::UriStyle,
}

impl Cli<'_> {
    fn full(&self, path: &str) -> Option<&session::Loaded> {
        self.session.full_from_path(&resolve(&self.cwd, path))
    }

    /// `Cli.definition`.
    fn definition(&self, out: &mut Output, path: &str, pos: (i32, i32), debug: bool) {
        let full = self.full(path);
        match commands::definition(&self.session, self.uri_style, full, pos, debug, out) {
            None => print_json(out, &Json::Null),
            Some(location) => print_json(out, &location),
        }
    }

    /// `Cli.type_definition`.
    fn type_definition(&self, out: &mut Output, path: &str, pos: (i32, i32), debug: bool) {
        let full = self.full(path);
        match commands::type_definition(&self.session, self.uri_style, full, pos, debug, out) {
            None => print_json(out, &Json::Null),
            Some(location) => print_json(out, &location),
        }
    }

    /// `Cli.hover`.
    fn hover(
        &self,
        out: &mut Output,
        path: &str,
        pos: (i32, i32),
        supports_markdown_links: bool,
        debug: bool,
    ) {
        let full = self.full(path);
        match commands::hover(
            &self.session,
            self.uri_style,
            full,
            pos,
            supports_markdown_links,
            debug,
            out,
        ) {
            None => print_json(out, &Json::Null),
            Some(hover) => print_json(out, &hover),
        }
    }

    /// `Cli.rename`.
    fn rename(&self, out: &mut Output, path: &str, pos: (i32, i32), new_name: &str, debug: bool) {
        let full = self.full(path);
        match commands::rename(
            &self.session,
            self.uri_style,
            full,
            pos,
            new_name,
            debug,
            out,
        ) {
            Some(changes) => print_json(out, &Json::List(changes)),
            None => print_json(out, &Json::Null),
        }
    }

    /// `Cli.prepare_rename`.
    fn prepare_rename(&self, out: &mut Output, path: &str, pos: (i32, i32), debug: bool) {
        let full = self.full(path);
        match commands::prepare_rename(full, pos, debug, out) {
            Some(result) => print_json(out, &result),
            None => print_json(out, &Json::Null),
        }
    }

    /// `Cli.references`.
    fn references(&self, out: &mut Output, path: &str, pos: (i32, i32), debug: bool) {
        let full = self.full(path);
        let all_locs = commands::references(&self.session, self.uri_style, full, pos, debug, out);
        if all_locs.is_empty() {
            print_json(out, &Json::Null);
        } else {
            print_json(out, &Json::List(all_locs));
        }
    }
}

fn parse_pos(line: &str, col: &str) -> Result<(i32, i32), String> {
    let int = |s: &str| s.parse::<i32>().map_err(|_| format!("not a number: {s}"));
    Ok((int(line)?, int(col)?))
}

/// Run a command; the error is a usage problem, reported instead of output.
pub fn run(request: &Request, project: &dyn session::Project) -> Result<Vec<u8>, String> {
    let mut out = Output::default();
    let mut cli = Cli {
        cwd: request.cwd.clone(),
        session: session::ProjectSession::new(project),
        uri_style: uri::UriStyle::default(),
    };
    let args: Vec<&str> = request.args.iter().map(String::as_str).collect();
    match args.as_slice() {
        ["documentSymbol", path] => document_symbol(&mut out, &request.cwd, path),
        ["definition", path, line, col] => {
            cli.definition(&mut out, path, parse_pos(line, col)?, false)
        }
        ["typeDefinition", path, line, col] => {
            cli.type_definition(&mut out, path, parse_pos(line, col)?, false)
        }
        [
            "hover",
            path,
            line,
            col,
            _current_file,
            supports_markdown_links,
        ] => cli.hover(
            &mut out,
            path,
            parse_pos(line, col)?,
            *supports_markdown_links == "true",
            false,
        ),
        ["prepareRename", path, line, col] => {
            cli.prepare_rename(&mut out, path, parse_pos(line, col)?, false)
        }
        ["rename", path, line, col, new_name] => {
            cli.rename(&mut out, path, parse_pos(line, col)?, new_name, false)
        }
        ["references", path, line, col] => {
            cli.references(&mut out, path, parse_pos(line, col)?, false)
        }
        ["test", path] => test(&mut out, &mut cli, path)?,
        [command, ..] => {
            return Err(format!(
                "`{command}` is not available inside the watcher yet"
            ));
        }
        [] => return Err("no command".to_string()),
    }
    if let Some(failure) = cli.session.failure() {
        return Err(failure);
    }
    Ok(out.into_bytes())
}

/// `rescript-tools doc <path>` (tools/bin/main.ml): what it prints, the
/// documentation of the module at `path` as JSON and a newline, or why there
/// is none. `project` must be built with source locations (see [`docgen`]),
/// which a watcher's builds leave out, so this is no watcher command.
pub fn doc(cwd: &Path, path: &str, project: &dyn session::Project) -> Result<Vec<u8>, String> {
    let session = session::ProjectSession::new(project);
    let docs = docgen::extract_docs(&session, cwd, path)?;
    if let Some(failure) = session.failure() {
        return Err(failure);
    }
    let mut out = Output::default();
    out.print_endline(&docs);
    Ok(out.into_bytes())
}

/// `Cli.print_string`: the pretty JSON and a newline.
fn print_json(out: &mut Output, json: &Json) {
    out.print_endline(&json.pretty());
}

/// `Cli.document_symbol`.
fn document_symbol(out: &mut Output, cwd: &Path, path: &str) {
    match read_file(&resolve(cwd, path)) {
        None => print_json(out, &Json::Null),
        Some(source) => print_json(
            out,
            &document_symbol::get_symbols(&source, FileKind::of_path(path)),
        ),
    }
}

/// The length of `^ *//[ ]*\^` at the start of `line`, if it matches.
fn test_marker_length(line: &str) -> Option<usize> {
    let bytes = line.as_bytes();
    let mut i = 0;
    while bytes.get(i) == Some(&b' ') {
        i += 1;
    }
    if bytes.get(i..i + 2) != Some(b"//") {
        return None;
    }
    i += 2;
    while bytes.get(i) == Some(&b' ') {
        i += 1;
    }
    (bytes.get(i) == Some(&b'^')).then_some(i + 1)
}

/// `Cli.test`: run the command each `//^xxx` comment names, at the position
/// of the `^` on the line above.
fn test(out: &mut Output, cli: &mut Cli<'_>, path: &str) -> Result<(), String> {
    cli.uri_style.strip_path = true;
    let cwd = cli.cwd.clone();
    let cwd = cwd.as_path();
    let text = read_file(&resolve(cwd, path)).ok_or_else(|| format!("cannot read {path}"))?;
    for (i, line) in text.split('\n').enumerate() {
        let Some(mlen) = test_marker_length(line) else {
            continue;
        };
        if mlen < 3 {
            continue;
        }
        let rest = &line[mlen..];
        let pos = (i as i32 - 1, mlen as i32 - 1);
        let position = format!("{path} {}:{}", pos.0, pos.1);
        let command = rest
            .get(..3)
            .ok_or_else(|| format!("{path}:{}: truncated test command", i + 1))?;
        match command {
            "def" => {
                out.print_endline(&format!("Definition {position}"));
                cli.definition(out, path, pos, true);
            }
            "hov" => {
                out.print_endline(&format!("Hover {position}"));
                cli.hover(out, path, pos, true, true);
            }
            "pre" => {
                out.print_endline(&format!("PrepareRename {position}"));
                cli.prepare_rename(out, path, pos, true);
            }
            "ren" => {
                let new_name = line.get(mlen + 4..).unwrap_or("");
                out.print_endline(&format!("Rename {position} {new_name}"));
                cli.rename(out, path, pos, new_name, true);
            }
            "ref" => {
                out.print_endline(&format!("References {position}"));
                cli.references(out, path, pos, true);
            }
            "typ" => {
                out.print_endline(&format!("TypeDefinition {position}"));
                cli.type_definition(out, path, pos, true);
            }
            "doc" => {
                out.print_endline(&format!("DocumentSymbol {path}"));
                document_symbol(out, cwd, path);
            }
            "db+" | "db-" | "dv+" | "dv-" | "in+" | "in-" | "ve+" | "ve-" => {}
            other => out.print_endline(&format!(
                "`{other}` is not available inside the watcher yet"
            )),
        }
        out.print_newline();
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn matches_test_markers() {
        assert_eq!(test_marker_length("//^doc"), Some(3));
        assert_eq!(test_marker_length("  //  ^hov"), Some(7));
        assert_eq!(test_marker_length("// ^"), Some(4));
        assert_eq!(test_marker_length("let x = 1 //^doc"), None);
        assert_eq!(Json::Null.pretty(), "null");
    }
}
