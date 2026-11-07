// Port of compiler/gentype/Log_.ml:1-101.

use crate::location::Location;

pub mod color {
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub enum Color {
        Red,
        Yellow,
        Magenta,
        Cyan,
    }

    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub enum Style {
        FG(Color),
        Bold,
        Dim,
    }

    pub fn code_of_style(style: Style) -> &'static str {
        match style {
            Style::FG(Color::Red) => "31",
            Style::FG(Color::Yellow) => "33",
            Style::FG(Color::Magenta) => "35",
            Style::FG(Color::Cyan) => "36",
            Style::Bold => "1",
            Style::Dim => "2",
        }
    }

    pub fn style_of_stag(s: &str) -> Vec<Style> {
        match s {
            "error" => vec![Style::Bold, Style::FG(Color::Red)],
            "warning" => vec![Style::Bold, Style::FG(Color::Magenta)],
            "info" => vec![Style::Bold, Style::FG(Color::Yellow)],
            "dim" => vec![Style::Dim],
            "filename" => vec![Style::FG(Color::Cyan)],
            _ => vec![],
        }
    }

    pub fn ansi_of_stag(s: &str) -> String {
        let codes = style_of_stag(s)
            .into_iter()
            .map(code_of_style)
            .collect::<Vec<_>>()
            .join(";");
        format!("\u{1b}[{codes}m")
    }

    pub const RESET_LIT: &str = "\u{1b}[0m";

    pub fn setup() {
        // OCaml installs formatter tag functions here. Rust logging can apply
        // tags at render time, so setup is intentionally a no-op in this port.
    }

    pub fn error(s: &str) -> String {
        format!("{}{}{}", ansi_of_stag("error"), s, RESET_LIT)
    }

    pub fn info(s: &str) -> String {
        format!("{}{}{}", ansi_of_stag("info"), s, RESET_LIT)
    }
}

pub mod loc {
    use super::Location;

    pub type NormalizedRange = Option<((i32, i32), (i32, i32))>;

    pub fn print_filename(file: &str) -> String {
        match file {
            "_none_" | "" => "(No file name)".to_string(),
            real_file => real_file.to_string(),
        }
    }

    pub fn print_loc(normalized_range: NormalizedRange, loc: &Location) -> String {
        // OCaml compiler/gentype/Log_.ml:54-77 gets the filename from
        // Location.get_pos_info. Rust Location stores an interned filename id;
        // callers that know the file use `print_in_file`.
        let file = if loc.is_none() { "" } else { "<source>" };
        print_loc_in_file(file, normalized_range, loc)
    }

    /// `print_loc` of a location in `file`.
    pub fn print_loc_in_file(
        file: &str,
        normalized_range: NormalizedRange,
        loc: &Location,
    ) -> String {
        if file == "//toplevel//" {
            format!("Characters {}-{}", loc.loc_start.cnum, loc.loc_end.cnum)
        } else {
            let dim_loc = match normalized_range {
                None => String::new(),
                Some(((start_line, start_line_start_char), (end_line, end_line_end_char))) => {
                    if start_line == end_line {
                        if start_line_start_char == end_line_end_char {
                            format!(":{start_line}:{start_line_start_char}")
                        } else {
                            format!(":{start_line}:{start_line_start_char}-{end_line_end_char}")
                        }
                    } else {
                        format!(
                            ":{start_line}:{start_line_start_char}-{end_line}:{end_line_end_char}"
                        )
                    }
                }
            };
            format!("{}{}", print_filename(file), dim_loc)
        }
    }

    fn normalized_range(loc: &Location) -> NormalizedRange {
        loc.normalize_range()
            .map(|(start_line, start_char, end_line, end_char)| {
                ((start_line, start_char), (end_line, end_char))
            })
    }

    pub fn print(loc: &Location) -> String {
        print_loc(normalized_range(loc), loc)
    }

    /// Log_.ml:79-87 `Loc.print` of a location in `file`.
    pub fn print_in_file(file: &str, loc: &Location) -> String {
        print_loc_in_file(file, normalized_range(loc), loc)
    }
}

pub fn item(message: &str) {
    print!("  ");
    print!("{message}");
}

pub fn log_kind<F>(body: F, color: fn(&str) -> String, loc: &Location, name: &str)
where
    F: FnOnce() -> String,
{
    print!("{}", log_kind_text(&color(name), &loc::print(loc), &body()));
}

/// Log_.ml:99-102: `@[<v 2>@,%a@,%a@,%a@]@.`, the name, location and body on
/// lines indented by two after an empty line; the box indents the body's own
/// line breaks too.
pub fn log_kind_text(name: &str, loc: &str, body: &str) -> String {
    let body = body.replace('\n', "\n  ");
    format!("\n  {name}\n  {loc}\n  {body}\n")
}

pub fn info<F>(body: F, loc: &Location, name: &str)
where
    F: FnOnce() -> String,
{
    log_kind(body, color::info, loc, name);
}

/// The genType warnings (Log_.ml:99-104) one translation prints, in order.
/// A compile replays them once GenType runs (after the unit's JavaScript is
/// written); a translation cached for importers keeps its own and the
/// importer that reads it replays them.
#[derive(Debug, Default)]
pub struct Notes(std::cell::RefCell<Vec<String>>);

impl Notes {
    /// `Log_.info ~loc ~name body` of a location in `file`.
    pub fn info(&self, file: &str, loc: &Location, name: &str, body: &str) {
        color::setup();
        self.0.borrow_mut().push(log_kind_text(
            &color::info(name),
            &loc::print_in_file(file, loc),
            body,
        ));
    }

    pub fn extend(&self, notes: impl IntoIterator<Item = String>) {
        self.0.borrow_mut().extend(notes);
    }

    pub fn take(&self) -> Vec<String> {
        std::mem::take(&mut *self.0.borrow_mut())
    }
}
