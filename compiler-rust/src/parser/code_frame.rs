//! Code frame formatting for error messages.
//!
//! This module provides functions to format source code snippets with
//! line numbers and highlighting for error reporting, matching the
//! OCaml implementation in `compiler/ml/code_frame.ml`.

use crate::location::Position;
use std::borrow::Cow;
use std::io::IsTerminal;
use std::sync::atomic::{AtomicBool, AtomicU8, Ordering};

/// Count the number of digits in a number.
fn digits_count(n: i32) -> usize {
    if n == 0 {
        return 1;
    }
    let mut count = 0;
    let mut n = n.abs();
    while n > 0 {
        count += 1;
        n /= 10;
    }
    count
}

/// Seek backwards to find the start position for showing 2 lines before the error.
/// Returns (char_offset, line_number) of where to start.
fn seek_2_lines_before(src: &str, pos: &Position) -> (usize, i32) {
    let original_line = pos.line;
    let mut current_line = 1i32;
    let mut current_char = 0usize;

    let bytes = src.as_bytes();
    while current_char < bytes.len() {
        if current_line + 2 >= original_line {
            return (current_char, current_line);
        }
        if bytes[current_char] == b'\n' {
            current_line += 1;
        }
        current_char += 1;
    }
    (current_char, current_line)
}

/// Seek forward to find the end position for showing 2 lines after the error.
/// Returns (char_offset, line_number) of where to end.
fn seek_2_lines_after(src: &str, pos: &Position) -> (usize, i32) {
    let original_line = pos.line;
    let mut current_line = original_line;
    let mut current_char = pos.cnum as usize;

    let bytes = src.as_bytes();
    while current_char < bytes.len() {
        if bytes[current_char] == b'\n' {
            if current_line == original_line + 2 {
                return (current_char, current_line);
            }
            current_line += 1;
        }
        current_char += 1;
    }
    (current_char, current_line)
}

/// Count leading spaces in a byte string (`leading_space_count`).
fn leading_space_count(s: &[u8]) -> usize {
    s.iter().take_while(|&&c| c == b' ').count()
}

/// `String.get_utf_8_uchar line pos |> Uchar.utf_decode_length`: the length
/// of the UTF-8 sequence at `pos`, or of the invalid prefix that decoding
/// consumed.
fn utf_8_decode_length(s: &[u8], pos: usize) -> usize {
    let rest = &s[pos..];
    match std::str::from_utf8(&rest[..rest.len().min(4)]) {
        Ok(text) => text.chars().next().map_or(1, char::len_utf8),
        Err(err) if err.valid_up_to() > 0 => std::str::from_utf8(&rest[..err.valid_up_to()])
            .ok()
            .and_then(|text| text.chars().next())
            .map_or(1, char::len_utf8),
        Err(err) => err.error_len().unwrap_or(rest.len()).max(1),
    }
}

/// Break a long line into chunks of `max_width` characters
/// (compiler/ml/code_frame.ml `break_long_line`).
fn break_long_line(max_width: usize, line: &[u8]) -> Vec<&[u8]> {
    let line_length = line.len();
    let mut result = Vec::new();
    let mut pos = 0;
    while pos < line_length {
        let mut chunk_end = pos;
        let mut remaining_width = max_width;
        while chunk_end < line_length && remaining_width > 0 {
            chunk_end += utf_8_decode_length(line, chunk_end);
            remaining_width -= 1;
        }
        let chunk_end = chunk_end.min(line_length);
        result.push(&line[pos..chunk_end]);
        pos = chunk_end;
    }
    result
}

/// Gutter content - either a line number or elided marker.
#[derive(Clone)]
enum Gutter {
    Number(i32),
    Elided,
}

/// A highlighted portion of a line. `start`/`end_` are byte indices into `s`
/// computed from `pos_cnum - pos_bol` (UTF-16 columns), exactly as OCaml does.
struct HighlightedString<'a> {
    s: &'a [u8],
    start: isize,
    end_: isize,
}

/// A line with gutter and content.
struct Line<'a> {
    gutter: Gutter,
    content: Vec<HighlightedString<'a>>,
}

#[derive(Clone, Copy)]
enum Emphasis {
    Error,
    Warning,
}

const ANSI_DIM: &str = "\x1b[2m";
const ANSI_ERR: &str = "\x1b[1;31m";
const ANSI_WARN: &str = "\x1b[1;33m";
const ANSI_FILENAME: &str = "\x1b[36m";
const ANSI_RESET: &str = "\x1b[0m";

#[derive(Clone, Copy, Debug, Eq, PartialEq, Default)]
pub enum ColorMode {
    #[default]
    Auto = 0,
    Always = 1,
    Never = 2,
}

static COLOR_MODE: AtomicU8 = AtomicU8::new(ColorMode::Auto as u8);

/// OCaml `Misc.Color.color_enabled` (compiler/ext/misc.ml:337-392) starts as
/// `true` and takes the configured `-color` value at the first
/// `Location.setup_colors`, which printing a located warning triggers. Error
/// messages are formatted before the error itself is printed, so their
/// embedded styles depend on whether a warning was printed first.
static COLOR_SETUP: AtomicBool = AtomicBool::new(false);

/// Record that a located report was printed (`Location.setup_colors`).
pub fn mark_color_setup() {
    COLOR_SETUP.store(true, Ordering::Relaxed);
}

/// Whether styles embedded in a formatted message are emitted.
pub fn message_styles_enabled() -> bool {
    !COLOR_SETUP.load(Ordering::Relaxed) || should_enable_color()
}

/// Remove SGR escape sequences from a formatted message when
/// `message_styles_enabled` is false.
pub fn apply_message_styles(message: &str) -> std::borrow::Cow<'_, str> {
    if message_styles_enabled() || !message.contains('\x1b') {
        return std::borrow::Cow::Borrowed(message);
    }
    let mut out = String::with_capacity(message.len());
    let mut chars = message.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '\x1b' && chars.peek() == Some(&'[') {
            chars.next();
            for c in chars.by_ref() {
                if c == 'm' {
                    break;
                }
            }
        } else {
            out.push(c);
        }
    }
    std::borrow::Cow::Owned(out)
}

pub fn parse_color_mode(value: &str) -> Option<ColorMode> {
    match value {
        "auto" => Some(ColorMode::Auto),
        "always" => Some(ColorMode::Always),
        "never" => Some(ColorMode::Never),
        _ => None,
    }
}

pub fn set_color_mode(mode: ColorMode) {
    COLOR_MODE.store(mode as u8, Ordering::Relaxed);
}

fn color_mode() -> ColorMode {
    match COLOR_MODE.load(Ordering::Relaxed) {
        1 => ColorMode::Always,
        2 => ColorMode::Never,
        _ => ColorMode::Auto,
    }
}

pub fn should_enable_color() -> bool {
    // OCaml compiler/bsc/rescript_compiler_main.ml:349-358 parses `-color`,
    // rescript_compiler_main.ml:494 makes `bsc` default to `always`, and
    // compiler/ext/misc.ml:512-529 plus compiler/ml/code_frame.ml:83-91
    // choose between always, never, and the stderr TTY heuristic.
    match color_mode() {
        ColorMode::Always => true,
        ColorMode::Never => false,
        ColorMode::Auto => should_auto_enable_color(),
    }
}

fn should_auto_enable_color() -> bool {
    let term = std::env::var("TERM").unwrap_or_default();
    term != "dumb" && !term.is_empty() && std::io::stderr().is_terminal()
}

pub fn colorize_intro(intro: &str, is_error: bool) -> String {
    if !should_enable_color() {
        return intro.to_string();
    }
    let color = if is_error { ANSI_ERR } else { ANSI_WARN };
    format!("{color}{intro}{ANSI_RESET}")
}

/// `@{<filename>%s@}` (compiler/ext/misc.ml:334).
pub fn colorize_filename(file: &str) -> String {
    if !should_enable_color() {
        return file.to_string();
    }
    format!("{ANSI_FILENAME}{file}{ANSI_RESET}")
}

pub fn colorize_location(location: &str) -> String {
    if !should_enable_color() {
        return location.to_string();
    }
    if let Some((file, rest)) = location.split_once(':') {
        format!("{ANSI_FILENAME}{file}{ANSI_RESET}:{ANSI_DIM}{rest}{ANSI_RESET}")
    } else {
        format!("{ANSI_FILENAME}{location}{ANSI_RESET}")
    }
}

fn emphasis_ansi(emphasis: Emphasis) -> &'static str {
    match emphasis {
        Emphasis::Error => ANSI_ERR,
        Emphasis::Warning => ANSI_WARN,
    }
}

fn source_for_display(src: &str) -> Cow<'_, str> {
    if src.is_ascii() {
        return Cow::Borrowed(src);
    }

    let mut bytes = Vec::with_capacity(src.len());
    for ch in src.chars() {
        let value = ch as u32;
        if value > u8::MAX as u32 {
            return Cow::Borrowed(src);
        }
        bytes.push(value as u8);
    }

    // OCaml compiler/ml/code_frame.ml:120-143 slices the source byte string
    // and writes those bytes back to the terminal. Rust keeps parser input in a
    // Latin-1 byte-preserving string, so recover valid UTF-8 for display only.
    match String::from_utf8(bytes) {
        Ok(display) => Cow::Owned(display),
        Err(_) => Cow::Borrowed(src),
    }
}

/// Print a code frame with source context around an error.
///
/// This formats source code with:
/// - 2 lines of context before and after the error
/// - Line numbers in a gutter
/// - Highlighting of the error region (when colors enabled)
/// - Elision of middle lines for large error spans
pub fn print(src: &str, start_pos: &Position, end_pos: &Position) -> String {
    print_impl(src, start_pos, end_pos, Emphasis::Error)
}

/// Print a code frame with warning highlighting.
pub fn print_warning(src: &str, start_pos: &Position, end_pos: &Position) -> String {
    mark_color_setup();
    print_impl(src, start_pos, end_pos, Emphasis::Warning)
}

fn print_impl(src: &str, start_pos: &Position, end_pos: &Position, emphasis: Emphasis) -> String {
    let display_src = source_for_display(src);
    let src = display_src.as_ref();
    let indent = 2;
    let highlight_line_start = start_pos.line;
    let highlight_line_end = end_pos.line;
    let use_color = should_enable_color();

    let (start_offset, first_shown_line) = seek_2_lines_before(src, start_pos);
    let (end_offset, last_shown_line) = seek_2_lines_after(src, end_pos);

    let more_than_5_highlighted_lines = highlight_line_end - highlight_line_start + 1 > 5;
    let max_line_digits = digits_count(last_shown_line);

    // 3 for separator + the 2 spaces around it
    let line_width = 78 - max_line_digits - indent - 3;

    // `String.sub src start (end - start) |> String.split_on_char '\n'`.
    let bytes = src.as_bytes();
    let lines: Vec<(Gutter, &[u8])> = if start_offset <= end_offset && end_offset <= bytes.len() {
        bytes[start_offset..end_offset]
            .split(|&c| c == b'\n')
            .enumerate()
            .filter_map(|(i, line)| {
                let line_number = first_shown_line + i as i32;
                if more_than_5_highlighted_lines {
                    if line_number == highlight_line_start + 2 {
                        Some((Gutter::Elided, line))
                    } else if line_number > highlight_line_start + 2
                        && line_number < highlight_line_end - 1
                    {
                        None
                    } else {
                        Some((Gutter::Number(line_number), line))
                    }
                } else {
                    Some((Gutter::Number(line_number), line))
                }
            })
            .collect()
    } else {
        vec![]
    };

    let leading_space_to_cut = lines.iter().fold(99999usize, |current_max, (_, line)| {
        let leading_spaces = leading_space_count(line);
        if line.len() == leading_spaces {
            // the line's nothing but spaces. Doesn't count
            current_max
        } else {
            current_max.min(leading_spaces)
        }
    });

    let separator = if leading_space_to_cut == 0 {
        "│"
    } else {
        "┆"
    };

    let highlight_line_start_offset = start_pos.cnum as isize - start_pos.bol as isize;
    let highlight_line_end_offset = end_pos.cnum as isize - end_pos.bol as isize;
    let leading_cut = leading_space_to_cut as isize;
    let processed_lines: Vec<Line<'_>> = lines
        .iter()
        .map(|(gutter, line)| {
            let content: Vec<HighlightedString<'_>> = if line.len() <= leading_space_to_cut {
                vec![HighlightedString {
                    s: &[],
                    start: 0,
                    end_: 0,
                }]
            } else {
                break_long_line(line_width, &line[leading_space_to_cut..])
                    .into_iter()
                    .enumerate()
                    .map(|(i, chunk)| match gutter {
                        Gutter::Elided => HighlightedString {
                            s: chunk,
                            start: 0,
                            end_: 0,
                        },
                        Gutter::Number(line_number) => {
                            let line_number = *line_number;
                            // OCaml measures `String.length line` of the
                            // chunk here.
                            let chunk_len = chunk.len() as isize;
                            let start = if i == 0 && line_number == highlight_line_start {
                                highlight_line_start_offset - leading_cut
                            } else {
                                0
                            };
                            let end_ = if line_number < highlight_line_start {
                                0
                            } else if line_number == highlight_line_start
                                && line_number == highlight_line_end
                            {
                                highlight_line_end_offset - leading_cut
                            } else if line_number == highlight_line_start
                                || (line_number > highlight_line_start
                                    && line_number < highlight_line_end)
                            {
                                chunk_len
                            } else if line_number == highlight_line_end {
                                highlight_line_end_offset - leading_cut
                            } else {
                                0
                            };
                            HighlightedString {
                                s: chunk,
                                start,
                                end_,
                            }
                        }
                    })
                    .collect()
            };
            Line {
                gutter: gutter.clone(),
                content,
            }
        })
        .collect();

    // `Code_frame.print`'s drawing (compiler/ml/code_frame.ml:222-298): every
    // byte goes through `add_ch`, which emits an ANSI sequence only when the
    // color differs from the previous byte's (across lines).
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum FrameColor {
        NoColor,
        Dim,
        Emphasis,
    }
    struct Frame {
        buf: Vec<u8>,
        last: FrameColor,
        use_color: bool,
        emphasis: &'static str,
    }
    impl Frame {
        fn add_ch(&mut self, color: FrameColor, ch: u8) {
            if !self.use_color || self.last == color {
                self.buf.push(ch);
                return;
            }
            let ansi: &[&str] = match (self.last, color) {
                (FrameColor::NoColor, FrameColor::Dim) => &[ANSI_DIM],
                (FrameColor::NoColor, FrameColor::Emphasis) => &[self.emphasis],
                (_, FrameColor::NoColor) => &[ANSI_RESET],
                (_, FrameColor::Dim) => &[ANSI_RESET, ANSI_DIM],
                (_, FrameColor::Emphasis) => &[ANSI_RESET, self.emphasis],
            };
            for part in ansi {
                self.buf.extend_from_slice(part.as_bytes());
            }
            self.buf.push(ch);
            self.last = color;
        }

        fn add_str(&mut self, color: FrameColor, s: &str) {
            for &ch in s.as_bytes() {
                self.add_ch(color, ch);
            }
        }

        fn draw_gutter(&mut self, width: usize, color: FrameColor, s: &str, separator: &str) {
            for _ in 0..width.saturating_sub(s.len()) {
                self.add_ch(FrameColor::NoColor, b' ');
            }
            self.add_str(color, s);
            self.add_ch(FrameColor::NoColor, b' ');
            self.add_str(FrameColor::Dim, separator);
            self.add_ch(FrameColor::NoColor, b' ');
        }
    }

    let mut frame = Frame {
        buf: Vec::with_capacity(1024),
        last: FrameColor::NoColor,
        use_color,
        emphasis: emphasis_ansi(emphasis),
    };
    let gutter_width = max_line_digits + indent;
    for line in &processed_lines {
        match &line.gutter {
            Gutter::Elided => {
                frame.draw_gutter(gutter_width, FrameColor::Dim, ".", separator);
                frame.add_str(FrameColor::Dim, "...");
                frame.add_ch(FrameColor::NoColor, b'\n');
            }
            Gutter::Number(line_number) => {
                for (i, hs) in line.content.iter().enumerate() {
                    let gutter_content = if i == 0 {
                        line_number.to_string()
                    } else {
                        String::new()
                    };
                    let gutter_color = if i == 0
                        && *line_number >= highlight_line_start
                        && *line_number <= highlight_line_end
                    {
                        FrameColor::Emphasis
                    } else {
                        FrameColor::NoColor
                    };
                    frame.draw_gutter(gutter_width, gutter_color, &gutter_content, separator);
                    for (ii, &ch) in hs.s.iter().enumerate() {
                        let ii = ii as isize;
                        let color = if ii >= hs.start && ii < hs.end_ {
                            FrameColor::Emphasis
                        } else {
                            FrameColor::NoColor
                        };
                        frame.add_ch(color, ch);
                    }
                    frame.add_ch(FrameColor::NoColor, b'\n');
                }
            }
        }
    }

    // OCaml writes these bytes as-is; a highlight boundary can fall inside a
    // multi-byte character. A Rust `String` cannot carry the split sequence,
    // so such bytes decode to U+FFFD.
    match String::from_utf8(frame.buf) {
        Ok(text) => text,
        Err(err) => String::from_utf8_lossy(err.as_bytes()).into_owned(),
    }
}

/// Format a location as "filename:line:col" or "filename:line:col-endcol"
/// Whether `Location.normalize_range` (location.ml:53-73) gives a range: a
/// column of -1 (a dummy position) prints the file name alone, with no code
/// frame.
pub fn has_printable_range(start_pos: &Position, end_pos: &Position) -> bool {
    // Rust's `Location::none()` (line 0) stands for OCaml's `Location.none`,
    // whose `pos_cnum = -1` makes the range unprintable (location.ml).
    start_pos.line != 0 && start_pos.cnum - start_pos.bol != -1 && end_pos.cnum - end_pos.bol != -1
}

pub fn format_location(filename: &str, start_pos: &Position, end_pos: &Position) -> String {
    if !has_printable_range(start_pos, end_pos) {
        return filename.to_string();
    }
    // OCaml uses 1-indexed columns: col = pos_cnum - pos_bol + 1
    let start_col = start_pos.cnum - start_pos.bol + 1;
    let end_col = end_pos.cnum - end_pos.bol; // OCaml doesn't add +1 for end (it's exclusive)

    if start_pos.line == end_pos.line && end_col > start_col {
        format!("{}:{}:{}-{}", filename, start_pos.line, start_col, end_col)
    } else if start_pos.line == end_pos.line {
        format!("{}:{}:{}", filename, start_pos.line, start_col)
    } else {
        format!(
            "{}:{}:{}-{}:{}",
            filename, start_pos.line, start_col, end_pos.line, end_col
        )
    }
}

/// Format a complete error report with header, location, code frame, and message.
pub fn format_error(
    filename: &str,
    src: &str,
    start_pos: &Position,
    end_pos: &Position,
    message: &str,
) -> String {
    let mut result = String::new();

    // Header (OCaml `Res_diagnostics_printing_utils` colors it like other errors).
    result.push_str("\n  ");
    result.push_str(&colorize_intro("Syntax error!", true));
    result.push('\n');

    // Location
    result.push_str("  ");
    result.push_str(&colorize_location(&format_location(
        filename, start_pos, end_pos,
    )));
    result.push_str("\n\n");

    // Code frame, printed only for a normalized range (location.ml:95-120).
    if has_printable_range(start_pos, end_pos) {
        result.push_str(&print(src, start_pos, end_pos));
        // Extra blank line after code frame
        result.push('\n');
    }

    // Message
    result.push_str("  ");
    result.push_str(message);
    // Extra blank line after message
    result.push_str("\n\n");

    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_digits_count() {
        assert_eq!(digits_count(0), 1);
        assert_eq!(digits_count(1), 1);
        assert_eq!(digits_count(9), 1);
        assert_eq!(digits_count(10), 2);
        assert_eq!(digits_count(99), 2);
        assert_eq!(digits_count(100), 3);
        assert_eq!(digits_count(1000), 4);
    }

    #[test]
    fn test_leading_space_count() {
        assert_eq!(leading_space_count(b""), 0);
        assert_eq!(leading_space_count(b"hello"), 0);
        assert_eq!(leading_space_count(b"  hello"), 2);
        assert_eq!(leading_space_count(b"    "), 4);
    }

    #[test]
    fn test_format_location() {
        let start = Position {
            line: 5,
            bol: 100,
            cnum: 110,
            ..Default::default()
        };
        let end = Position {
            line: 5,
            bol: 100,
            cnum: 115,
            ..Default::default()
        };
        assert_eq!(
            format_location("test.res", &start, &end),
            "test.res:5:11-15"
        );
    }

    #[test]
    fn test_simple_code_frame() {
        let src = "let x = 1\nlet y = 2\nlet z = 3\n";
        let start = Position {
            line: 2,
            bol: 10,
            cnum: 14,
            ..Default::default()
        };
        let end = Position {
            line: 2,
            bol: 10,
            cnum: 15,
            ..Default::default()
        };
        let frame = print(src, &start, &end);
        assert!(frame.contains("1 │ let x = 1"));
        assert!(frame.contains("2 │ let y = 2"));
        assert!(frame.contains("3 │ let z = 3"));
    }
}
