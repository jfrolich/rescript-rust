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

/// Count leading spaces in a string.
fn leading_space_count(s: &str) -> usize {
    s.chars().take_while(|&c| c == ' ').count()
}

fn char_len(s: &str) -> usize {
    s.chars().count()
}

fn char_slice(s: &str, start: usize, end: usize) -> &str {
    let start_byte = char_to_byte_idx(s, start);
    let end_byte = char_to_byte_idx(s, end);
    &s[start_byte..end_byte]
}

/// Break a long line into chunks of max_width characters.
/// Matches OCaml's `break_long_line` in code_frame.ml.
fn break_long_line(max_width: usize, line: &str) -> Vec<&str> {
    if max_width == 0 || line.is_empty() {
        return vec![line];
    }
    let mut result = Vec::new();
    let mut pos = 0;
    let len = char_len(line);
    while pos < len {
        let chunk_length = max_width.min(len - pos);
        result.push(char_slice(line, pos, pos + chunk_length));
        pos += chunk_length;
    }
    if result.is_empty() {
        result.push(line);
    }
    result
}

/// Gutter content - either a line number or elided marker.
#[derive(Clone)]
enum Gutter {
    Number(i32),
    Elided,
}

/// A highlighted portion of a line.
struct HighlightedString {
    s: String,
    start: usize,
    end: usize,
}

/// A line with gutter and content.
struct Line {
    gutter: Gutter,
    content: Vec<HighlightedString>,
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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ColorMode {
    Auto = 0,
    Always = 1,
    Never = 2,
}

impl Default for ColorMode {
    fn default() -> Self {
        Self::Auto
    }
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

fn char_to_byte_idx(s: &str, char_idx: usize) -> usize {
    if char_idx == 0 {
        return 0;
    }
    s.char_indices()
        .nth(char_idx)
        .map(|(idx, _)| idx)
        .unwrap_or(s.len())
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

    // Extract the relevant portion of source
    let lines: Vec<(Gutter, &str)> = if start_offset < end_offset && end_offset <= src.len() {
        let snippet = &src[start_offset..end_offset];
        snippet
            .split('\n')
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

    // Calculate leading space to strip (minimum non-empty line indentation)
    let leading_space_to_cut = lines
        .iter()
        .filter_map(|(_, line)| {
            let spaces = leading_space_count(line);
            if char_len(line) == spaces {
                None // Line is all spaces, don't count
            } else {
                Some(spaces)
            }
        })
        .min()
        .unwrap_or(0);

    let separator = if leading_space_to_cut == 0 {
        "│"
    } else {
        "┆"
    };

    // Process lines with highlighting info, breaking long lines into chunks
    let processed_lines: Vec<Line> = lines
        .iter()
        .map(|(gutter, line)| {
            let stripped = if char_len(line) > leading_space_to_cut {
                char_slice(line, leading_space_to_cut, char_len(line))
            } else {
                ""
            };

            // Break long lines into chunks matching OCaml's break_long_line
            let chunks = break_long_line(line_width, stripped);

            let content: Vec<HighlightedString> = chunks
                .iter()
                .enumerate()
                .map(|(chunk_idx, chunk)| match gutter {
                    Gutter::Elided => HighlightedString {
                        s: chunk.to_string(),
                        start: 0,
                        end: 0,
                    },
                    Gutter::Number(line_number) => {
                        // Keep this policy aligned with compiler/ml/code_frame.ml.
                        let highlight_line_start_offset =
                            start_pos.cnum.saturating_sub(start_pos.bol) as isize;
                        let highlight_line_end_offset =
                            end_pos.cnum.saturating_sub(end_pos.bol) as isize;
                        let leading_cut = leading_space_to_cut as isize;
                        let chunk_len = chunk.chars().count() as isize;

                        let start = if chunk_idx == 0 && *line_number == highlight_line_start {
                            highlight_line_start_offset - leading_cut
                        } else {
                            0
                        };

                        let end = if *line_number < highlight_line_start {
                            0
                        } else if *line_number == highlight_line_start
                            && *line_number == highlight_line_end
                        {
                            highlight_line_end_offset - leading_cut
                        } else if *line_number == highlight_line_start {
                            chunk_len
                        } else if *line_number > highlight_line_start
                            && *line_number < highlight_line_end
                        {
                            chunk_len
                        } else if *line_number == highlight_line_end {
                            highlight_line_end_offset - leading_cut
                        } else {
                            0
                        };

                        let start = start.clamp(0, chunk_len) as usize;
                        let end = end.clamp(0, chunk_len) as usize;

                        HighlightedString {
                            s: chunk.to_string(),
                            start,
                            end,
                        }
                    }
                })
                .collect();

            Line {
                gutter: gutter.clone(),
                content,
            }
        })
        .collect();

    // `Code_frame.print`'s drawing (compiler/ml/code_frame.ml:222-298): every
    // character goes through `add_ch`, which emits an ANSI sequence only
    // when the color differs from the previous character's (across lines).
    #[derive(Clone, Copy, PartialEq, Eq)]
    enum FrameColor {
        NoColor,
        Dim,
        Emphasis,
    }
    struct Frame {
        buf: String,
        last: FrameColor,
        use_color: bool,
        emphasis: &'static str,
    }
    impl Frame {
        fn add_ch(&mut self, color: FrameColor, ch: char) {
            if !self.use_color || self.last == color {
                self.buf.push(ch);
                return;
            }
            match (self.last, color) {
                (FrameColor::NoColor, FrameColor::Dim) => self.buf.push_str(ANSI_DIM),
                (FrameColor::NoColor, FrameColor::Emphasis) => self.buf.push_str(self.emphasis),
                (_, FrameColor::NoColor) => self.buf.push_str(ANSI_RESET),
                (_, FrameColor::Dim) => {
                    self.buf.push_str(ANSI_RESET);
                    self.buf.push_str(ANSI_DIM);
                }
                (_, FrameColor::Emphasis) => {
                    self.buf.push_str(ANSI_RESET);
                    self.buf.push_str(self.emphasis);
                }
            }
            self.buf.push(ch);
            self.last = color;
        }

        fn add_str(&mut self, color: FrameColor, s: &str) {
            for ch in s.chars() {
                self.add_ch(color, ch);
            }
        }

        fn draw_gutter(&mut self, width: usize, color: FrameColor, s: &str, separator: &str) {
            for _ in 0..width.saturating_sub(s.len()) {
                self.add_ch(FrameColor::NoColor, ' ');
            }
            self.add_str(color, s);
            self.add_ch(FrameColor::NoColor, ' ');
            self.add_str(FrameColor::Dim, separator);
            self.add_ch(FrameColor::NoColor, ' ');
        }
    }

    let mut frame = Frame {
        buf: String::with_capacity(1024),
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
                frame.add_ch(FrameColor::NoColor, '\n');
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
                    for (ii, ch) in hs.s.chars().enumerate() {
                        let color = if ii >= hs.start && ii < hs.end {
                            FrameColor::Emphasis
                        } else {
                            FrameColor::NoColor
                        };
                        frame.add_ch(color, ch);
                    }
                    frame.add_ch(FrameColor::NoColor, '\n');
                }
            }
        }
    }

    frame.buf
}

/// Format a location as "filename:line:col" or "filename:line:col-endcol"
pub fn format_location(filename: &str, start_pos: &Position, end_pos: &Position) -> String {
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
    result.push_str(&colorize_location(&format_location(filename, start_pos, end_pos)));
    result.push_str("\n\n");

    // Code frame
    result.push_str(&print(src, start_pos, end_pos));
    // Extra blank line after code frame
    result.push_str("\n");

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
        assert_eq!(leading_space_count(""), 0);
        assert_eq!(leading_space_count("hello"), 0);
        assert_eq!(leading_space_count("  hello"), 2);
        assert_eq!(leading_space_count("    "), 4);
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
