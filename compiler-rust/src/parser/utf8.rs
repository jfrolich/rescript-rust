//! UTF-8 utilities for the ReScript parser.
//!
//! UTF-8 decoding and codepoint validation used by the scanner.

/// The Unicode replacement character (U+FFFD).
pub const REPLACEMENT_CHAR: i32 = 0xFFFD;

/// Maximum valid Unicode codepoint (U+10FFFF).
const MAX_CODEPOINT: i32 = 0x10FFFF;

/// Start of surrogate range.
const SURROGATE_MIN: i32 = 0xD800;

/// End of surrogate range.
const SURROGATE_MAX: i32 = 0xDFFF;

/// Classification of a UTF-8 byte.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ByteClass {
    /// Single-byte ASCII character (0x00-0x7F).
    Single(u8),
    /// Continuation byte (10xxxxxx).
    Cont(u8),
    /// Leading byte with number of continuation bytes and partial codepoint.
    Leading(u8, u8),
    /// Invalid byte.
    Invalid,
}

impl ByteClass {
    /// Classify a byte according to UTF-8 encoding rules.
    fn classify(byte: u8) -> Self {
        if byte & 0b1000_0000 == 0 {
            // 0xxxxxxx - ASCII
            ByteClass::Single(byte)
        } else if byte & 0b0100_0000 == 0 {
            // 10xxxxxx - continuation byte
            ByteClass::Cont(byte & 0b0011_1111)
        } else if byte & 0b0010_0000 == 0 {
            // 110xxxxx - 2-byte sequence
            ByteClass::Leading(1, byte & 0b0001_1111)
        } else if byte & 0b0001_0000 == 0 {
            // 1110xxxx - 3-byte sequence
            ByteClass::Leading(2, byte & 0b0000_1111)
        } else if byte & 0b0000_1000 == 0 {
            // 11110xxx - 4-byte sequence
            ByteClass::Leading(3, byte & 0b0000_0111)
        } else if byte & 0b0000_0100 == 0 {
            // 111110xx - 5-byte sequence (invalid UTF-8 but we handle it)
            ByteClass::Leading(4, byte & 0b0000_0011)
        } else if byte & 0b0000_0010 == 0 {
            // 1111110x - 6-byte sequence (invalid UTF-8 but we handle it)
            ByteClass::Leading(5, byte & 0b0000_0001)
        } else {
            ByteClass::Invalid
        }
    }
}

/// Check if a codepoint is valid Unicode (not a surrogate).
pub fn is_valid_codepoint(c: i32) -> bool {
    (0..SURROGATE_MIN).contains(&c) || ((SURROGATE_MAX + 1)..=MAX_CODEPOINT).contains(&c)
}

/// Decode a UTF-8 codepoint from a byte slice starting at the given offset.
///
/// Returns `(codepoint, length)` where length is the number of bytes consumed.
/// On error, returns `(REPLACEMENT_CHAR, 1)`.
pub fn decode_codepoint(bytes: &[u8], offset: usize) -> (i32, usize) {
    if offset >= bytes.len() {
        return (REPLACEMENT_CHAR, 1);
    }

    let first = bytes[offset];
    if first < 128 {
        return (first as i32, 1);
    }

    match ByteClass::classify(first) {
        ByteClass::Single(c) => (c as i32, 1),
        ByteClass::Cont(_) | ByteClass::Invalid => (REPLACEMENT_CHAR, 1),
        ByteClass::Leading(n, initial) => {
            let n = n as usize;
            if offset + n >= bytes.len() {
                return (REPLACEMENT_CHAR, 1);
            }

            let mut codepoint = initial as i32;
            for i in 1..=n {
                let byte = bytes[offset + i];
                match ByteClass::classify(byte) {
                    ByteClass::Cont(c) => {
                        codepoint = (codepoint << 6) | (c as i32);
                    }
                    _ => return (REPLACEMENT_CHAR, 1),
                }
            }

            // Validate the codepoint
            if !is_valid_codepoint(codepoint) {
                return (REPLACEMENT_CHAR, 1);
            }

            (codepoint, n + 1)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_classify_ascii() {
        assert_eq!(ByteClass::classify(b'a'), ByteClass::Single(b'a'));
        assert_eq!(ByteClass::classify(0x00), ByteClass::Single(0x00));
        assert_eq!(ByteClass::classify(0x7F), ByteClass::Single(0x7F));
    }

    #[test]
    fn test_classify_multibyte() {
        // 2-byte sequence: 110xxxxx
        assert!(matches!(
            ByteClass::classify(0b1100_0000),
            ByteClass::Leading(1, _)
        ));

        // 3-byte sequence: 1110xxxx
        assert!(matches!(
            ByteClass::classify(0b1110_0000),
            ByteClass::Leading(2, _)
        ));

        // 4-byte sequence: 11110xxx
        assert!(matches!(
            ByteClass::classify(0b1111_0000),
            ByteClass::Leading(3, _)
        ));

        // Continuation: 10xxxxxx
        assert!(matches!(
            ByteClass::classify(0b1000_0000),
            ByteClass::Cont(_)
        ));
    }

    #[test]
    fn test_decode_ascii() {
        let bytes = b"hello";
        let (cp, len) = decode_codepoint(bytes, 0);
        assert_eq!(cp, b'h' as i32);
        assert_eq!(len, 1);
    }

    #[test]
    fn test_decode_multibyte() {
        // "é" = U+00E9 = 0xC3 0xA9 in UTF-8
        let bytes = [0xC3, 0xA9];
        let (cp, len) = decode_codepoint(&bytes, 0);
        assert_eq!(cp, 0xE9);
        assert_eq!(len, 2);
    }

    #[test]
    fn test_decode_emoji() {
        // "😀" = U+1F600 = 0xF0 0x9F 0x98 0x80 in UTF-8
        let bytes = [0xF0, 0x9F, 0x98, 0x80];
        let (cp, len) = decode_codepoint(&bytes, 0);
        assert_eq!(cp, 0x1F600);
        assert_eq!(len, 4);
    }

    #[test]
    fn test_is_valid_codepoint() {
        assert!(is_valid_codepoint(0x0000));
        assert!(is_valid_codepoint(0x7F));
        assert!(is_valid_codepoint(0xFFFF));
        assert!(is_valid_codepoint(0x10FFFF));
        assert!(!is_valid_codepoint(0xD800)); // surrogate
        assert!(!is_valid_codepoint(0xDFFF)); // surrogate
        assert!(!is_valid_codepoint(0x110000)); // too large
    }
}
