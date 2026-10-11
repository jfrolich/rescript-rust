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

/// `String.sub src start (end - start)` on the compiler's Latin-1 view of the
/// source: `start`/`end` are byte offsets (`pos_cnum`), which are char indices
/// of the Latin-1 string.
pub fn latin1_slice(source: &str, start: usize, end: usize) -> Option<&str> {
    if source.is_ascii() {
        return source.get(start..end);
    }
    if start > end {
        return None;
    }
    let mut indices = source
        .char_indices()
        .map(|(i, _)| i)
        .chain(std::iter::once(source.len()));
    let start_byte = indices.nth(start)?;
    let end_byte = if end == start {
        start_byte
    } else {
        indices.nth(end - start - 1)?
    };
    source.get(start_byte..end_byte)
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

/// Decode the byte-preserving Latin-1 runs of a diagnostic for UTF-8 output.
///
/// Diagnostics interleave static text with names taken from the source,
/// which the parser keeps as one `char` per byte. OCaml writes those names'
/// bytes unchanged, so each maximal run of `U+0080..=U+00FF` characters is
/// turned back into its bytes and shown as UTF-8 when the bytes are valid.
pub fn decode_internal_utf8_runs(s: &str) -> Cow<'_, str> {
    if s.is_ascii() || !s.chars().any(|ch| ('\u{80}'..='\u{ff}').contains(&ch)) {
        return Cow::Borrowed(s);
    }
    let mut out = String::with_capacity(s.len());
    let mut run: Vec<u8> = Vec::new();
    let flush = |run: &mut Vec<u8>, out: &mut String| {
        if run.is_empty() {
            return;
        }
        match std::str::from_utf8(run) {
            Ok(text) => out.push_str(text),
            Err(_) => out.extend(run.iter().map(|&b| b as char)),
        }
        run.clear();
    };
    for ch in s.chars() {
        if ('\u{80}'..='\u{ff}').contains(&ch) {
            run.push(ch as u32 as u8);
        } else {
            flush(&mut run, &mut out);
            out.push(ch);
        }
    }
    flush(&mut run, &mut out);
    Cow::Owned(out)
}
