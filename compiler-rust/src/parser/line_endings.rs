//! Line endings of formatted sources (`compiler/syntax/src/res_line_endings.ml`).
//!
//! The printer writes its own line breaks with the newline it is given, and
//! copies comments and literals with their bytes unchanged. Formatting a file
//! with the newline of its source keeps a CRLF file CRLF without touching the
//! line breaks inside its string literals, which are part of the program.
//!
//! Sources are Latin-1 strings (one `char` per byte), so CR and LF are the
//! same characters as the bytes they stand for.

/// The newline of `source`: CRLF when its first line break is CRLF, LF
/// otherwise (`Res_line_endings.newline`).
pub fn newline(source: &str) -> &'static str {
    match source.find('\n') {
        Some(index) if index > 0 && source.as_bytes()[index - 1] == b'\r' => "\r\n",
        _ => "\n",
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn first_line_break_decides() {
        assert_eq!(newline("a\r\nb\n"), "\r\n");
        assert_eq!(newline("a\nb\r\n"), "\n");
        assert_eq!(newline("\n"), "\n");
        assert_eq!(newline("no break\r"), "\n");
    }
}
