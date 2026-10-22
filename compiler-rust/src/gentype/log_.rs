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

    pub const reset_lit: &str = "\u{1b}[0m";

    pub fn setup() {
        // OCaml installs formatter tag functions here. Rust logging can apply
        // tags at render time, so setup is intentionally a no-op in this port.
    }

    pub fn error(s: &str) -> String {
        format!("{}{}{}", ansi_of_stag("error"), s, reset_lit)
    }

    pub fn info(s: &str) -> String {
        format!("{}{}{}", ansi_of_stag("info"), s, reset_lit)
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
        // Location.get_pos_info. Rust Location stores an interned filename id,
        // so the eventual integrated port must pass the arena/source resolver
        // here to recover the exact filename string.
        let file = if loc.is_none() { "" } else { "<source>" };
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

    pub fn print(loc: &Location) -> String {
        let normalized_range =
            loc.normalize_range()
                .map(|(start_line, start_char, end_line, end_char)| {
                    ((start_line, start_char), (end_line, end_char))
                });
        print_loc(normalized_range, loc)
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
    println!("\n{}\n{}\n{}", color(name), loc::print(loc), body());
}

pub fn info<F>(body: F, loc: &Location, name: &str)
where
    F: FnOnce() -> String,
{
    log_kind(body, color::info, loc, name);
}
