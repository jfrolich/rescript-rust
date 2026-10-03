//! Editor tooling: a port of the OCaml analysis (analysis/src) that runs
//! inside the build system's watcher, on the Rust parse and typed trees.
//!
//! The watcher keeps the published interfaces in memory and type-checks the
//! module a command needs on demand; no typed artifacts are serialized. A
//! command gets its arguments as `rescript-editor-analysis` would (see
//! analysis/bin/main.ml) and returns what that binary prints.

pub mod document_symbol;
pub mod hashtbl;
pub mod json;
pub mod process_attributes;
pub mod process_cmt;
pub mod process_extra;
pub mod resolve_path;
pub mod session;
pub mod shared_types;

use json::Json;
use std::path::{Path, PathBuf};

/// `Files.classify_source_file`, for the files analysis works on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FileKind {
    Res,
    Resi,
}

impl FileKind {
    pub fn of_path(path: &str) -> FileKind {
        if path.ends_with(".resi") { FileKind::Resi } else { FileKind::Res }
    }
}

/// An LSP position: 0-based line and character offset.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Position {
    pub line: i32,
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

    pub fn to_json(self) -> Json {
        Json::assoc([("character", Json::Int(self.character.into())), ("line", Json::Int(self.line.into()))])
    }
}

/// An LSP range.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Range {
    pub start: Position,
    pub end: Position,
}

impl Range {
    /// `Utils.cmt_loc_to_range`.
    pub fn of_positions(start: &crate::location::Position, end: &crate::location::Position) -> Range {
        Range {
            start: Position::of_lexing(start),
            end: Position::of_lexing(end),
        }
    }

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
    pub args: Vec<String>,
}

/// Collects what a command prints (`print_string`/`print_endline`).
#[derive(Default)]
pub struct Output(String);

impl Output {
    pub fn print(&mut self, s: &str) {
        self.0.push_str(s);
    }

    pub fn print_endline(&mut self, s: &str) {
        self.0.push_str(s);
        self.0.push('\n');
    }

    pub fn print_newline(&mut self) {
        self.0.push('\n');
    }

    /// The printed bytes. Source text is held as Latin-1 characters standing
    /// for bytes; other characters are encoded as UTF-8.
    pub fn into_bytes(self) -> Vec<u8> {
        let mut bytes = Vec::with_capacity(self.0.len());
        for c in self.0.chars() {
            if (c as u32) <= 0xFF {
                bytes.push(c as u8);
            } else {
                let mut buf = [0u8; 4];
                bytes.extend_from_slice(c.encode_utf8(&mut buf).as_bytes());
            }
        }
        bytes
    }
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

/// Run a command; the error is a usage problem, reported instead of output.
pub fn run(request: &Request) -> Result<Vec<u8>, String> {
    let mut out = Output::default();
    let args: Vec<&str> = request.args.iter().map(String::as_str).collect();
    match args.as_slice() {
        ["documentSymbol", path] => document_symbol(&mut out, &request.cwd, path),
        ["test", path] => test(&mut out, &request.cwd, path)?,
        [command, ..] => return Err(format!("`{command}` is not available inside the watcher yet")),
        [] => return Err("no command".to_string()),
    }
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
        Some(source) => print_json(out, &document_symbol::get_symbols(&source, FileKind::of_path(path))),
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
fn test(out: &mut Output, cwd: &Path, path: &str) -> Result<(), String> {
    let text = read_file(&resolve(cwd, path)).ok_or_else(|| format!("cannot read {path}"))?;
    for (i, line) in text.split('\n').enumerate() {
        let Some(mlen) = test_marker_length(line) else {
            continue;
        };
        if mlen < 3 {
            continue;
        }
        let rest = &line[mlen..];
        let command = rest.get(..3).ok_or_else(|| format!("{path}:{}: truncated test command", i + 1))?;
        match command {
            "doc" => {
                out.print_endline(&format!("DocumentSymbol {path}"));
                document_symbol(out, cwd, path);
            }
            "db+" | "db-" | "dv+" | "dv-" | "in+" | "in-" | "ve+" | "ve-" => {}
            other => out.print_endline(&format!("`{other}` is not available inside the watcher yet")),
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
