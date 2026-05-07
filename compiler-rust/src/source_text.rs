//! Source text decoding helpers.

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
