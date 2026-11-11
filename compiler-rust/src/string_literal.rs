//! Port of `compiler/ml/string_literal.ml`: JavaScript string-literal
//! representation and conversion utilities.
//!
//! A literal has two related values: `source` is the text between its source
//! delimiters, including escape spelling, while `semantic` is the UTF-8 text
//! observed at runtime after JavaScript escape decoding.
//!
//! The compiler keeps OCaml's byte-string model: a string holds one `char` per
//! byte (`U+0000..=U+00FF`, see `source_text::latin1_bytes_to_string`). The
//! algorithms below work on those bytes exactly as the OCaml ones do and
//! return strings in the same representation.

use std::borrow::Cow;

/// OCaml `String_literal.payload`: `source` is the original literal body and
/// `semantic` is exactly what JavaScript evaluates that body to.
/// `InvalidSource` is confined to ordinary-string parser recovery.
#[derive(Debug, Clone, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum StringLiteral {
    /// A literal with valid source spelling and its decoded runtime value.
    Valid {
        /// Literal body as written, excluding delimiters.
        source: Cow<'static, str>,
        /// Decoded runtime value in the compiler byte-string representation.
        semantic: Cow<'static, str>,
    },
    /// Malformed ordinary-string spelling retained during parser recovery.
    InvalidSource(Cow<'static, str>),
}

/// OCaml `String_literal.template_segment` (the same payload).
pub type TemplateSegment = StringLiteral;

impl StringLiteral {
    /// OCaml `string_source` / `template_source`.
    pub fn source(&self) -> &str {
        match self {
            StringLiteral::Valid { source, .. } | StringLiteral::InvalidSource(source) => source,
        }
    }

    /// OCaml `string_semantic` / `template_semantic`. Invalid ordinary strings
    /// retained for parser recovery return the empty placeholder value.
    pub fn semantic(&self) -> &str {
        match self {
            StringLiteral::Valid { semantic, .. } => semantic,
            StringLiteral::InvalidSource(_) => "",
        }
    }
}

/// The bytes of a compiler string. Strings that hold a character above
/// `U+00FF` were not produced from source bytes; their UTF-8 encoding is
/// their byte content (as in `source_text::decode_internal_utf8`).
pub fn bytes_of(s: &str) -> Cow<'_, [u8]> {
    if s.is_ascii() || s.chars().any(|ch| ch as u32 > 0xff) {
        Cow::Borrowed(s.as_bytes())
    } else {
        Cow::Owned(s.chars().map(|ch| ch as u8).collect())
    }
}

/// A compiler string holding `bytes`, one `char` per byte.
pub fn string_of_bytes(bytes: Vec<u8>) -> String {
    crate::source_text::latin1_bytes_to_string(bytes)
}

/// OCaml `String.get_utf_8_uchar`: decode the UTF-8 sequence at `index`.
/// Returns whether it is valid, its scalar value (meaningful when valid) and
/// the number of bytes it spans; an invalid decode spans the maximal subpart
/// of an ill-formed sequence.
pub(crate) fn get_utf_8_uchar(s: &[u8], index: usize) -> (bool, u32, usize) {
    let b0 = s[index];
    if b0 < 0x80 {
        return (true, b0 as u32, 1);
    }
    let (len, lo, hi) = match b0 {
        0xc2..=0xdf => (2, 0x80, 0xbf),
        0xe0 => (3, 0xa0, 0xbf),
        0xe1..=0xec | 0xee..=0xef => (3, 0x80, 0xbf),
        0xed => (3, 0x80, 0x9f),
        0xf0 => (4, 0x90, 0xbf),
        0xf1..=0xf3 => (4, 0x80, 0xbf),
        0xf4 => (4, 0x80, 0x8f),
        _ => return (false, 0, 1),
    };
    let mut codepoint = (b0 as u32) & (0x7f >> len);
    for k in 1..len {
        let (lo, hi) = if k == 1 { (lo, hi) } else { (0x80, 0xbf) };
        match s.get(index + k) {
            Some(&byte) if (lo..=hi).contains(&byte) => {
                codepoint = (codepoint << 6) | (byte as u32 & 0x3f);
            }
            _ => return (false, 0, k),
        }
    }
    (true, codepoint, len)
}

fn add_utf_8_uchar(buf: &mut Vec<u8>, codepoint: u32) {
    let ch = char::from_u32(codepoint).expect("valid Unicode scalar value");
    let mut tmp = [0u8; 4];
    buf.extend_from_slice(ch.encode_utf8(&mut tmp).as_bytes());
}

fn is_valid_scalar(codepoint: u32) -> bool {
    char::from_u32(codepoint).is_some()
}

fn hex_value(byte: u8) -> i32 {
    match byte {
        b'0'..=b'9' => (byte - b'0') as i32,
        b'a'..=b'f' => (byte - b'a') as i32 + 10,
        b'A'..=b'F' => (byte - b'A') as i32 + 10,
        _ => -1,
    }
}

fn is_high_surrogate(codepoint: u32) -> bool {
    (0xd800..=0xdbff).contains(&codepoint)
}

fn is_low_surrogate(codepoint: u32) -> bool {
    (0xdc00..=0xdfff).contains(&codepoint)
}

fn combine_surrogate_pair(high: u32, low: u32) -> u32 {
    0x10000 + ((high - 0xd800) << 10) + (low - 0xdc00)
}

fn is_valid_utf8_bytes(s: &[u8]) -> bool {
    std::str::from_utf8(s).is_ok()
}

/// OCaml `String_literal.is_valid_utf8`.
pub fn is_valid_utf8(s: &str) -> bool {
    is_valid_utf8_bytes(&bytes_of(s))
}

/// OCaml `String_literal.replace_invalid_utf8`: replace each malformed UTF-8
/// sequence with U+FFFD.
pub fn replace_invalid_utf8(s: &str) -> String {
    let bytes = bytes_of(s);
    let mut buf = Vec::with_capacity(bytes.len());
    let mut index = 0;
    while index < bytes.len() {
        let (valid, _, len) = get_utf_8_uchar(&bytes, index);
        if valid {
            buf.extend_from_slice(&bytes[index..index + len]);
        } else {
            add_utf_8_uchar(&mut buf, 0xfffd);
        }
        index += len;
    }
    string_of_bytes(buf)
}

/// OCaml `String_literal.normalize_semantic`: convert each malformed byte to
/// the code point with the same value, keeping valid UTF-8 sequences.
pub fn normalize_semantic(semantic: &str) -> Cow<'_, str> {
    let bytes = bytes_of(semantic);
    if is_valid_utf8_bytes(&bytes) {
        return Cow::Borrowed(semantic);
    }
    let mut buf = Vec::with_capacity(bytes.len());
    let mut index = 0;
    while index < bytes.len() {
        let (valid, _, len) = get_utf_8_uchar(&bytes, index);
        if valid {
            buf.extend_from_slice(&bytes[index..index + len]);
            index += len;
        } else {
            add_utf_8_uchar(&mut buf, bytes[index] as u32);
            index += 1;
        }
    }
    Cow::Owned(string_of_bytes(buf))
}

fn decode_js_escapes_with(normalize_template_line_endings: bool, s: &[u8]) -> Option<Vec<u8>> {
    let len = s.len();
    let mut buf = Vec::with_capacity(len);
    let decode_fixed_hex = |start: usize, count: usize| -> Option<u32> {
        let mut value = 0u32;
        for &byte in s.get(start..start.checked_add(count)?)? {
            let digit = hex_value(byte);
            if digit < 0 {
                return None;
            }
            value = value * 16 + digit as u32;
        }
        Some(value)
    };
    let decode_braced_hex = |start: usize| -> Option<(u32, usize)> {
        let mut index = start;
        let mut value = 0u32;
        let mut has_digit = false;
        loop {
            if index >= len {
                return None;
            }
            if s[index] == b'}' && has_digit {
                return Some((value, index + 1));
            }
            let digit = hex_value(s[index]);
            if digit < 0 || value > (0x10ffff - digit as u32) / 16 {
                return None;
            }
            value = value * 16 + digit as u32;
            has_digit = true;
            index += 1;
        }
    };
    let copy_utf8 = |buf: &mut Vec<u8>, index: usize| -> Option<usize> {
        let (valid, _, length) = get_utf_8_uchar(s, index);
        if valid {
            buf.extend_from_slice(&s[index..index + length]);
            Some(index + length)
        } else {
            None
        }
    };
    let add_codepoint = |buf: &mut Vec<u8>, codepoint: u32| -> bool {
        if is_valid_scalar(codepoint) {
            add_utf_8_uchar(buf, codepoint);
            true
        } else {
            false
        }
    };
    let mut index = 0;
    while index < len {
        match s[index] {
            b'\\' if index + 1 >= len => return None,
            b'\\'
                if index + 3 < len
                    && s[index + 1] == 0xe2
                    && s[index + 2] == 0x80
                    && (s[index + 3] == 0xa8 || s[index + 3] == 0xa9) =>
            {
                // U+2028 and U+2029 are JavaScript line terminators, so a
                // preceding backslash makes them line continuations.
                index += 4;
            }
            b'\\' => match s[index + 1] {
                b'b' => {
                    buf.push(0x08);
                    index += 2;
                }
                b'f' => {
                    buf.push(0x0c);
                    index += 2;
                }
                b'n' => {
                    buf.push(b'\n');
                    index += 2;
                }
                b'r' => {
                    buf.push(b'\r');
                    index += 2;
                }
                b't' => {
                    buf.push(b'\t');
                    index += 2;
                }
                b'v' => {
                    buf.push(0x0b);
                    index += 2;
                }
                b'0' if normalize_template_line_endings
                    && index + 2 < len
                    && s[index + 2].is_ascii_digit() =>
                {
                    return None;
                }
                b'0' => {
                    buf.push(0);
                    index += 2;
                }
                b'1'..=b'9' if normalize_template_line_endings => return None,
                b'\n' => index += 2,
                b'\r' => {
                    if index + 2 < len && s[index + 2] == b'\n' {
                        index += 3;
                    } else {
                        index += 2;
                    }
                }
                b'x' => match decode_fixed_hex(index + 2, 2) {
                    Some(codepoint) if add_codepoint(&mut buf, codepoint) => index += 4,
                    _ => return None,
                },
                b'u' if index + 2 < len && s[index + 2] == b'{' => {
                    match decode_braced_hex(index + 3) {
                        Some((codepoint, next)) if add_codepoint(&mut buf, codepoint) => {
                            index = next
                        }
                        _ => return None,
                    }
                }
                b'u' => match decode_fixed_hex(index + 2, 4) {
                    Some(high) if is_high_surrogate(high) => {
                        if index + 7 < len && s[index + 6] == b'\\' && s[index + 7] == b'u' {
                            match decode_fixed_hex(index + 8, 4) {
                                Some(low) if is_low_surrogate(low) => {
                                    let codepoint = combine_surrogate_pair(high, low);
                                    if add_codepoint(&mut buf, codepoint) {
                                        index += 12;
                                    } else {
                                        return None;
                                    }
                                }
                                _ => return None,
                            }
                        } else {
                            return None;
                        }
                    }
                    Some(codepoint) if add_codepoint(&mut buf, codepoint) => index += 6,
                    _ => return None,
                },
                // JavaScript non-escape characters evaluate to the character
                // following the backslash.
                _ => index = copy_utf8(&mut buf, index + 1)?,
            },
            b'\r' if normalize_template_line_endings => {
                // Template values normalize literal CR and CRLF to LF.
                buf.push(b'\n');
                if index + 1 < len && s[index + 1] == b'\n' {
                    index += 2;
                } else {
                    index += 1;
                }
            }
            // An unescaped interpolation opener cannot occur inside one
            // template segment.
            b'$' if normalize_template_line_endings && index + 1 < len && s[index + 1] == b'{' => {
                return None;
            }
            _ => index = copy_utf8(&mut buf, index)?,
        }
    }
    Some(buf)
}

/// OCaml `String_literal.decode_js_escapes`.
pub fn decode_js_escapes(s: &str) -> Option<String> {
    decode_js_escapes_with(false, &bytes_of(s)).map(string_of_bytes)
}

/// OCaml `String_literal.decode_js_template_escapes`.
pub fn decode_js_template_escapes(s: &str) -> Option<String> {
    decode_js_escapes_with(true, &bytes_of(s)).map(string_of_bytes)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum EncodeJsMode {
    String,
    Template,
}

fn encode_js(mode: EncodeJsMode, s: &str) -> String {
    let bytes = bytes_of(s);
    let mut buf = Vec::with_capacity(bytes.len());
    for &byte in bytes.iter() {
        match byte {
            0x08 => buf.extend_from_slice(b"\\b"),
            0x0c => buf.extend_from_slice(b"\\f"),
            b'\n' => buf.extend_from_slice(b"\\n"),
            b'\r' => buf.extend_from_slice(b"\\r"),
            b'\t' => buf.extend_from_slice(b"\\t"),
            0x0b => buf.extend_from_slice(b"\\v"),
            b'\\' => buf.extend_from_slice(b"\\\\"),
            0x00..=0x1f | 0x7f => {
                const HEX: &[u8; 16] = b"0123456789ABCDEF";
                buf.extend_from_slice(b"\\x");
                buf.push(HEX[usize::from(byte >> 4)]);
                buf.push(HEX[usize::from(byte & 0x0f)]);
            }
            b'"' => match mode {
                EncodeJsMode::String => buf.extend_from_slice(b"\\\""),
                EncodeJsMode::Template => buf.push(byte),
            },
            b'`' | b'$' => match mode {
                EncodeJsMode::String => buf.push(byte),
                EncodeJsMode::Template => {
                    buf.push(b'\\');
                    buf.push(byte);
                }
            },
            _ => buf.push(byte),
        }
    }
    string_of_bytes(buf)
}

/// OCaml `String_literal.decode_raw_template_source`: the JavaScript code of a
/// `%raw` template. Escaped `\\`, `$` and `` ` `` lose their backslash; a
/// backslash line continuation (`\n`, `\r\n`, `\r`, U+2028, U+2029) is
/// dropped; every other escape is kept verbatim.
pub fn decode_raw_template_source(source: &str) -> String {
    let bytes = bytes_of(source);
    let utf8_native = matches!(bytes, Cow::Borrowed(_));
    let length = bytes.len();
    let mut buffer = Vec::with_capacity(length);
    let mut index = 0;
    while index < length {
        let character = bytes[index];
        if character == b'\\' && index + 1 < length {
            match bytes[index + 1] {
                escaped @ (b'\\' | b'$' | b'`') => {
                    buffer.push(escaped);
                    index += 2;
                }
                b'\n' => index += 2,
                b'\r' => {
                    if index + 2 < length && bytes[index + 2] == b'\n' {
                        index += 3
                    } else {
                        index += 2
                    }
                }
                0xe2 if index + 3 < length
                    && bytes[index + 2] == 0x80
                    && (bytes[index + 3] == 0xa8 || bytes[index + 3] == 0xa9) =>
                {
                    index += 4
                }
                escaped => {
                    buffer.push(b'\\');
                    buffer.push(escaped);
                    index += 2;
                }
            }
        } else {
            buffer.push(character);
            index += 1;
        }
    }
    if utf8_native {
        String::from_utf8(buffer).expect("removing escapes keeps UTF-8 boundaries")
    } else {
        string_of_bytes(buffer)
    }
}

/// OCaml `String_literal.encode_raw_template_source`, the inverse of
/// [`decode_raw_template_source`]: escape backquotes, `${` and the
/// backslashes that decoding would otherwise consume.
pub fn encode_raw_template_source(source: &str) -> String {
    let bytes = bytes_of(source);
    let utf8_native = matches!(bytes, Cow::Borrowed(_));
    let length = bytes.len();
    let mut buffer = Vec::with_capacity(length);
    for (index, &character) in bytes.iter().enumerate() {
        let next = bytes.get(index + 1).copied();
        match character {
            b'`' => buffer.extend_from_slice(b"\\`"),
            b'$' if next == Some(b'{') => buffer.extend_from_slice(b"\\$"),
            b'\\' => match next {
                None | Some(b'\\' | b'$' | b'`' | b'\n' | b'\r' | 0xe2) => {
                    buffer.extend_from_slice(b"\\\\")
                }
                Some(_) => buffer.push(character),
            },
            _ => buffer.push(character),
        }
    }
    if utf8_native {
        String::from_utf8(buffer).expect("adding escapes keeps UTF-8 boundaries")
    } else {
        string_of_bytes(buffer)
    }
}

/// OCaml `String_literal.encode_js_string`.
pub fn encode_js_string(s: &str) -> String {
    encode_js(EncodeJsMode::String, s)
}

/// OCaml `String_literal.encode_js_template`.
pub fn encode_js_template(s: &str) -> String {
    encode_js(EncodeJsMode::Template, s)
}

/// OCaml `String_literal.string_from_source`.
pub fn string_from_source(source: &str) -> Option<StringLiteral> {
    decode_js_escapes(source).map(|semantic| StringLiteral::Valid {
        source: Cow::Owned(source.to_string()),
        semantic: Cow::Owned(semantic),
    })
}

/// OCaml `String_literal.string_from_semantic`: an ordinary string payload
/// with canonical source spelling.
pub fn string_from_semantic(semantic: &str) -> StringLiteral {
    let semantic = normalize_semantic(semantic).into_owned();
    StringLiteral::Valid {
        source: Cow::Owned(encode_js_string(&semantic)),
        semantic: Cow::Owned(semantic),
    }
}

/// OCaml `String_literal.invalid_string_for_recovery`.
pub fn invalid_string_for_recovery(source: &str) -> StringLiteral {
    StringLiteral::InvalidSource(Cow::Owned(source.to_string()))
}

/// OCaml `String_literal.template_from_source`.
pub fn template_from_source(source: &str) -> Option<TemplateSegment> {
    decode_js_template_escapes(source).map(|semantic| StringLiteral::Valid {
        source: Cow::Owned(source.to_string()),
        semantic: Cow::Owned(semantic),
    })
}

/// OCaml `String_literal.template_from_semantic`.
pub fn template_from_semantic(semantic: &str) -> TemplateSegment {
    let semantic = normalize_semantic(semantic).into_owned();
    StringLiteral::Valid {
        source: Cow::Owned(encode_js_template(&semantic)),
        semantic: Cow::Owned(semantic),
    }
}

/// OCaml `String_literal.concat_template`: keep the joined spelling only if
/// it still decodes to the joined semantic value.
pub fn concat_template(segments: &[TemplateSegment]) -> TemplateSegment {
    let source: String = segments.iter().map(StringLiteral::source).collect();
    let semantic: String = segments.iter().map(StringLiteral::semantic).collect();
    match decode_js_template_escapes(&source) {
        Some(decoded) if decoded == semantic => StringLiteral::Valid {
            source: Cow::Owned(source),
            semantic: Cow::Owned(semantic),
        },
        _ => template_from_semantic(&semantic),
    }
}

/// OCaml `String_literal.encode_char_source`: a canonical character-literal
/// body for a code point.
pub fn encode_char_source(codepoint: i32) -> String {
    match codepoint {
        0x08 => "\\b".to_string(),
        0x09 => "\\t".to_string(),
        0x0a => "\\n".to_string(),
        0x0d => "\\r".to_string(),
        0x27 => "\\'".to_string(),
        0x5c => "\\\\".to_string(),
        0x00..=0x1f | 0x7f => format!("\\x{codepoint:02X}"),
        0x20..=0x7e => (codepoint as u8 as char).to_string(),
        _ if codepoint >= 0 && is_valid_scalar(codepoint as u32) => {
            let mut buf = Vec::with_capacity(4);
            add_utf_8_uchar(&mut buf, codepoint as u32);
            string_of_bytes(buf)
        }
        _ => format!("\\u{{{codepoint:X}}}"),
    }
}

/// OCaml `String_literal.utf16_length`: JavaScript's `String.length` of a
/// semantic UTF-8 string.
pub fn utf16_length(s: &str) -> Option<usize> {
    let bytes = bytes_of(s);
    let mut length = 0;
    let mut index = 0;
    while index < bytes.len() {
        let (valid, codepoint, len) = get_utf_8_uchar(&bytes, index);
        if !valid {
            return None;
        }
        length += if codepoint > 0xffff { 2 } else { 1 };
        index += len;
    }
    Some(length)
}

/// Invalid UTF-8 encountered while interpreting a compiler byte string.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
#[error("invalid UTF-8 in string literal")]
pub struct InvalidUtf8;

/// OCaml `String_literal.code_point_at_utf16_index`: JavaScript's
/// `String.codePointAt` for a UTF-16 code unit index. An error stands for
/// OCaml's `Invalid_utf8` exception.
pub fn code_point_at_utf16_index(s: &str, index: i64) -> Result<Option<u32>, InvalidUtf8> {
    if index < 0 {
        return Ok(None);
    }
    let bytes = bytes_of(s);
    let mut utf16_index: i64 = 0;
    let mut byte_index = 0;
    while byte_index < bytes.len() {
        let (valid, codepoint, len) = get_utf_8_uchar(&bytes, byte_index);
        if !valid {
            return Err(InvalidUtf8);
        }
        if utf16_index == index {
            return Ok(Some(codepoint));
        }
        if codepoint > 0xffff && utf16_index + 1 == index {
            return Ok(Some(0xdc00 + ((codepoint - 0x10000) & 0x3ff)));
        }
        utf16_index += if codepoint > 0xffff { 2 } else { 1 };
        byte_index += len;
    }
    Ok(None)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decodes_escapes_and_surrogate_pairs() {
        assert_eq!(decode_js_escapes("a\\n").as_deref(), Some("a\n"));
        assert_eq!(decode_js_escapes("\\u0041\\x42").as_deref(), Some("AB"));
        let emoji = decode_js_escapes("\\uD83D\\uDE00").unwrap();
        assert_eq!(&*bytes_of(&emoji), "\u{1F600}".as_bytes());
        assert_eq!(decode_js_escapes("\\uD83D"), None);
        assert_eq!(decode_js_escapes("\\u{}"), None);
        assert_eq!(decode_js_template_escapes("a${b"), None);
        assert_eq!(decode_js_template_escapes("\\1"), None);
        assert_eq!(
            decode_js_template_escapes("a\r\nb").as_deref(),
            Some("a\nb")
        );
    }

    #[test]
    fn encodes_semantic_values() {
        assert_eq!(encode_js_string("a\"b`$\n\u{1}"), "a\\\"b`$\\n\\x01");
        assert_eq!(encode_js_template("a\"b`$"), "a\"b\\`\\$");
        assert_eq!(encode_js_string("\u{1f}\u{7f}\u{0}"), "\\x1F\\x7F\\x00");
        assert_eq!(encode_char_source(0x27), "\\'");
        assert_eq!(encode_char_source(0x110000), "\\u{110000}");
    }

    #[test]
    fn rejects_invalid_utf8_for_code_point_lookup() {
        let invalid = string_of_bytes(vec![0xff]);
        assert_eq!(code_point_at_utf16_index(&invalid, 0), Err(InvalidUtf8));
        assert_eq!(code_point_at_utf16_index(&invalid, -1), Ok(None));
    }

    #[test]
    fn rejects_incomplete_or_non_hex_escapes() {
        for source in [r"\x", r"\x0", r"\xGG", r"\u000", r"\u000G"] {
            assert_eq!(decode_js_escapes(source), None, "{source}");
        }
    }

    #[test]
    fn measures_utf16() {
        let emoji = string_of_bytes("a\u{1F600}".as_bytes().to_vec());
        assert_eq!(utf16_length(&emoji), Some(3));
        assert_eq!(code_point_at_utf16_index(&emoji, 2), Ok(Some(0xde00)));
    }
}

/// OCaml `String.escaped`, as used by `Printf "%S"`.
pub fn ocaml_escaped(s: &str) -> String {
    let mut out = String::new();
    for byte in s.bytes() {
        match byte {
            b'"' => out.push_str("\\\""),
            b'\\' => out.push_str("\\\\"),
            b'\n' => out.push_str("\\n"),
            b'\t' => out.push_str("\\t"),
            b'\r' => out.push_str("\\r"),
            8 => out.push_str("\\b"),
            32..=126 => out.push(byte as char),
            _ => out.push_str(&format!("\\{byte:03}")),
        }
    }
    out
}
