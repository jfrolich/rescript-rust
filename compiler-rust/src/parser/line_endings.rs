//! Line endings of formatted sources (`compiler/syntax/src/res_line_endings.ml`).
//!
//! The printer emits LF line endings, but the scanner keeps a CRLF source's
//! CRs inside comments, template literals and raw JS. Printed as is, those
//! lines end in CR LF next to plain LF lines, and an editor or a text-mode
//! channel that turns each LF into CRLF makes them CR CR LF.
//!
//! Sources are Latin-1 strings (one `char` per byte), so CR and LF are the
//! same characters as the bytes they stand for.

use std::borrow::Cow;

/// Whether the first line break of `source` is CRLF
/// (`Res_line_endings.uses_crlf`).
pub fn uses_crlf(source: &str) -> bool {
    match source.find('\n') {
        Some(index) => index > 0 && source.as_bytes()[index - 1] == b'\r',
        None => false,
    }
}

/// Replaces each CRLF with LF; a lone CR stays (`Res_line_endings.to_lf`).
pub fn to_lf(source: &str) -> Cow<'_, str> {
    if !source.contains('\r') {
        return Cow::Borrowed(source);
    }
    let mut converted = String::with_capacity(source.len());
    let mut chars = source.chars().peekable();
    while let Some(character) = chars.next() {
        if !(character == '\r' && chars.peek() == Some(&'\n')) {
            converted.push(character);
        }
    }
    Cow::Owned(converted)
}

/// Replaces each LF with CRLF (`Res_line_endings.to_crlf`).
pub fn to_crlf(text: &str) -> String {
    let mut converted = String::with_capacity(text.len());
    for character in text.chars() {
        if character == '\n' {
            converted.push('\r');
        }
        converted.push(character);
    }
    converted
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn first_line_break_decides() {
        assert!(uses_crlf("a\r\nb\n"));
        assert!(!uses_crlf("a\nb\r\n"));
        assert!(!uses_crlf("\n"));
        assert!(!uses_crlf("no break\r"));
    }

    #[test]
    fn lone_cr_stays() {
        assert_eq!(to_lf("a\r\nb\rc\r\n"), "a\nb\rc\n");
        assert!(matches!(to_lf("a\nb"), Cow::Borrowed(_)));
        assert_eq!(to_crlf("a\nb\n"), "a\r\nb\r\n");
    }
}
