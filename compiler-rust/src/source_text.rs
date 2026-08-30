//! Source text decoding helpers.

use std::borrow::Cow;

/// Convert source bytes to the compiler's Latin-1 string representation.
///
/// ASCII source can reuse the read buffer directly as UTF-8. Non-ASCII keeps the
/// OCaml byte-string model where every input byte maps to one `char` in the
/// range `0..=255`.
pub fn latin1_bytes_to_string(bytes: Vec<u8>) -> String {
    if bytes.is_ascii() {
        String::from_utf8(bytes).expect("ASCII source bytes should always be valid UTF-8")
    } else {
        bytes.iter().map(|&b| b as char).collect()
    }
}

/// Decode the compiler's Latin-1 view of source bytes for UTF-8 text output.
///
/// The parser deliberately keeps one Rust `char` per source byte to preserve
/// OCaml string identity and hashing. Text output must reconstruct those bytes
/// before interpreting them as UTF-8; writing the Latin-1 code points directly
/// would encode each one again and produce mojibake.
pub fn decode_internal_utf8(s: &str) -> Cow<'_, str> {
    if s.is_ascii() {
        return Cow::Borrowed(s);
    }

    let mut bytes = Vec::with_capacity(s.len());
    for ch in s.chars() {
        let codepoint = ch as u32;
        if codepoint > u8::MAX as u32 {
            return Cow::Borrowed(s);
        }
        bytes.push(codepoint as u8);
    }

    match String::from_utf8(bytes) {
        Ok(decoded) => Cow::Owned(decoded),
        Err(_) => Cow::Borrowed(s),
    }
}
