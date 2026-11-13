//! JSON values and Yojson's pretty printer.
//!
//! The analysis prints its results with `Yojson.Safe.pretty_to_string`
//! (yojson 3.0.0 `safe.ml` `format`/`pp`), whose layout comes from OCaml's
//! `Format` boxes. This is a port onto the same box engine
//! ([`crate::parser::formatter`]), so the output is identical.

use crate::parser::formatter::{BoxKind, Formatter};

/// A JSON value (`Yojson.Safe.t` without the literal variants).
#[derive(Debug, Clone, PartialEq)]
pub enum Json {
    /// `null`.
    Null,
    /// A boolean.
    Bool(bool),
    /// An integer.
    Int(i64),
    /// A string, escaped when printed.
    String(String),
    /// An array.
    List(Vec<Json>),
    /// An object, with its fields in this order.
    Assoc(Vec<(String, Json)>),
}

impl Json {
    /// A string value.
    pub fn str(s: impl Into<String>) -> Json {
        Json::String(s.into())
    }

    /// An object with `fields`, in this order.
    pub fn assoc<const N: usize>(fields: [(&str, Json); N]) -> Json {
        Json::Assoc(
            fields
                .into_iter()
                .map(|(k, v)| (k.to_string(), v))
                .collect(),
        )
    }

    /// `Yojson.Safe.pretty_to_string`.
    pub fn pretty(&self) -> String {
        let mut out = Vec::new();
        {
            let mut f = Formatter::new(&mut out);
            // `pp`: `@[<hv2>%a@]` with `format ~inside_box:true`.
            f.open_box(BoxKind::HV, 2);
            format(&mut f, self, true);
            f.close_box();
            f.flush();
        }
        String::from_utf8(out).expect("the formatter writes the strings it is given")
    }
}

/// `json_string_of_string` (safe.ml `write_string`). Works on the Latin-1
/// characters the compiler represents source bytes with, escaping like
/// Yojson escapes bytes.
pub fn escape_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\u{8}' => out.push_str("\\b"),
            '\u{c}' => out.push_str("\\f"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\u{0}'..='\u{1f}' | '\u{7f}' => out.push_str(&format!("\\u00{:02x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

/// Print `s` with the width OCaml's `Format` gives it (format.ml
/// `utf_8_scalar_width`): the number of UTF-8 scalar values of its bytes,
/// an ill-formed sequence counting as one. The layout breaks lines by it.
fn string(f: &mut Formatter<&mut Vec<u8>>, s: &str) {
    let width = if s.is_ascii() {
        s.len()
    } else {
        String::from_utf8_lossy(&super::text_bytes(s))
            .chars()
            .count()
    };
    f.string_as(width, s);
}

fn is_atom(x: &Json) -> bool {
    match x {
        Json::Null | Json::Bool(_) | Json::Int(_) | Json::String(_) => true,
        Json::List(l) => l.is_empty(),
        Json::Assoc(l) => l.is_empty(),
    }
}

/// `pp_list sep ppx`: elements separated by `sep` and a space break.
fn pp_list<T>(
    f: &mut Formatter<&mut Vec<u8>>,
    items: &[T],
    mut ppx: impl FnMut(&mut Formatter<&mut Vec<u8>>, &T),
) {
    for (i, item) in items.iter().enumerate() {
        if i > 0 {
            f.string(",");
            f.break_(1, 0);
        }
        ppx(f, item);
    }
}

/// safe.ml `format ~inside_box`.
fn format(f: &mut Formatter<&mut Vec<u8>>, x: &Json, inside_box: bool) {
    match x {
        Json::Null => f.string("null"),
        Json::Bool(b) => f.string(if *b { "true" } else { "false" }),
        Json::Int(i) => f.string(&i.to_string()),
        Json::String(s) => string(f, &escape_string(s)),
        Json::List(l) if l.is_empty() => f.string("[]"),
        Json::List(l) => {
            if !inside_box {
                f.open_box(BoxKind::HV, 2);
            }
            // Atom lists wrap like a paragraph (`hov`); other lists are all
            // on one line or one element per line (`hv`).
            let kind = if l.iter().all(is_atom) {
                BoxKind::HOV
            } else {
                BoxKind::HV
            };
            f.string("[");
            f.break_(1, 0);
            f.open_box(kind, 0);
            pp_list(f, l, |f, x| format(f, x, false));
            f.close_box();
            f.break_(1, -2);
            f.string("]");
            if !inside_box {
                f.close_box();
            }
        }
        Json::Assoc(l) if l.is_empty() => f.string("{}"),
        Json::Assoc(l) => {
            if !inside_box {
                f.open_box(BoxKind::HV, 2);
            }
            f.string("{");
            f.break_(1, 0);
            pp_list(f, l, |f, (name, x)| {
                // `format_field`: `@[<hv2>%s: %a@]`.
                f.open_box(BoxKind::HV, 2);
                string(f, &escape_string(name));
                f.string(": ");
                format(f, x, true);
                f.close_box();
            });
            f.break_(1, -2);
            f.string("}");
            if !inside_box {
                f.close_box();
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn prints_like_yojson() {
        let pos = |line, character| {
            Json::assoc([
                ("character", Json::Int(character)),
                ("line", Json::Int(line)),
            ])
        };
        let range = Json::assoc([("end", pos(31, 12)), ("start", pos(31, 0))]);
        let symbol = Json::assoc([
            ("kind", Json::Int(16)),
            ("name", Json::str("zzz")),
            ("range", range.clone()),
            ("selectionRange", range),
        ]);
        assert_eq!(
            Json::List(vec![symbol]).pretty(),
            r#"[
  {
    "kind": 16,
    "name": "zzz",
    "range": {
      "end": { "character": 12, "line": 31 },
      "start": { "character": 0, "line": 31 }
    },
    "selectionRange": {
      "end": { "character": 12, "line": 31 },
      "start": { "character": 0, "line": 31 }
    }
  }
]"#
        );
        assert_eq!(escape_string("a\"\n\u{1}"), r#""a\"\n\u0001""#);
    }

    /// The layout counts a multi-byte character once, as OCaml's `Format`
    /// does: text fits on a line by its characters, not its bytes.
    #[test]
    fn measures_strings_in_characters() {
        let fits = |text: String| {
            let json = Json::assoc([("docs", Json::List(vec![Json::String(text)]))]);
            !json.pretty().contains('\n')
        };
        let widest = (1..200)
            .take_while(|n| fits("x".repeat(*n)))
            .last()
            .unwrap();
        let text = format!("{}é—🎉", "x".repeat(widest - 3));
        assert_eq!(text.chars().count(), widest);
        // As the analysis holds source text: one character per byte.
        let latin1: String = text.bytes().map(char::from).collect();
        assert!(fits(latin1.clone()));
        assert!(!fits(format!("{latin1}x")));
    }
}
