//! Verbatim holes in otherwise canonical oxc output. Inserted text is never
//! scanned again, so a programmer's occurrence of our prefix remains untouched.
use super::Unsupported;
use std::ops::Range;

pub(super) const PREFIX: &str = "__rescript_raw$";

pub(super) struct Piece<'a> {
    pub token: &'a str,
    pub text: &'a str,
    pub before: &'static str,
    pub after: &'static str,
    pub remove_semicolon: bool,
}

/// Optional oracle evidence, copied directly from the raw IR payload, not from
/// reparsing the emitted output. Ranges are byte offsets in the complete file.
#[derive(Clone, Debug)]
pub struct RawSegment {
    /// Programmer text decoded from the compiler's internal byte-string form.
    pub text: String,
    /// The exact range occupied by that text, excluding legacy wrapping.
    pub text_range: Range<usize>,
    /// The entire substitution, including wrapping and statement termination.
    pub replacement_range: Range<usize>,
    /// Canonical oxc text to restore when masking this substitution.
    pub placeholder: String,
}

/// One left-to-right pass over codegen's buffer, never over inserted text.
/// Every registered hole must occur exactly once. A prefix appearing in a
/// non-raw string/comment/property is a specific fallback, not a replacement.
/// Namespace selection excludes all names produced by the naming pass.
pub(super) fn substitute(
    code: &str,
    prefix: &str,
    pieces: &[Piece<'_>],
    seen: &mut [bool],
    output: &mut String,
    mut audit: Option<&mut Vec<RawSegment>>,
) -> Result<(), Unsupported> {
    if pieces.is_empty() {
        output.push_str(code);
        return Ok(());
    }
    let collision = Unsupported("raw placeholder collision");
    let mut cursor = 0;
    while let Some(offset) = code[cursor..].find(prefix) {
        let start = cursor + offset;
        let digits_start = start + prefix.len();
        let digits_end = digits_start
            + code[digits_start..]
                .bytes()
                .take_while(u8::is_ascii_digit)
                .count();
        if code.as_bytes().get(digits_end) != Some(&b'$') {
            return Err(collision);
        }
        let id = code[digits_start..digits_end]
            .parse::<usize>()
            .map_err(|_| collision)?;
        let piece = pieces.get(id).ok_or(collision)?;
        let mut end = digits_end + 1;
        if seen[id] || &code[start..end] != piece.token {
            return Err(collision);
        }
        seen[id] = true;
        if piece.remove_semicolon {
            if code.as_bytes().get(end) != Some(&b';') {
                return Err(collision);
            }
            end += 1;
        }
        output.push_str(&code[cursor..start]);
        let replacement_start = output.len();
        output.push_str(piece.before);
        let text_start = output.len();
        output.push_str(piece.text);
        let text_end = output.len();
        output.push_str(piece.after);
        if let Some(audit) = audit.as_deref_mut() {
            audit.push(RawSegment {
                text: piece.text.into(),
                text_range: text_start..text_end,
                replacement_range: replacement_start..output.len(),
                placeholder: code[start..end].into(),
            });
        }
        cursor = end;
    }
    if seen.iter().any(|seen| !seen) {
        return Err(collision);
    }
    output.push_str(&code[cursor..]);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn substitution_never_scans_inserted_prefixes() {
        let pieces = [Piece {
            token: "__rescript_raw$0$",
            text: "/* __rescript_raw$0$ */ x(  1 )",
            before: "(",
            after: ")",
            remove_semicolon: false,
        }];
        let mut output = String::new();
        let mut audit = Vec::new();
        substitute(
            "let x = __rescript_raw$0$;",
            PREFIX,
            &pieces,
            &mut [false],
            &mut output,
            Some(&mut audit),
        )
        .unwrap();
        assert_eq!(output, "let x = (/* __rescript_raw$0$ */ x(  1 ));");
        assert_eq!(&output[audit[0].text_range.clone()], pieces[0].text);
    }

    #[test]
    fn missing_duplicate_and_invalid_holes_are_rejected() {
        let pieces = [Piece {
            token: "__rescript_raw$0$",
            text: "x",
            before: "",
            after: "",
            remove_semicolon: false,
        }];
        for code in [
            "missing;",
            "__rescript_raw$0$; __rescript_raw$0$;",
            "__rescript_raw$9$;",
            "__rescript_raw$not_a_hole",
        ] {
            assert_eq!(
                substitute(
                    code,
                    PREFIX,
                    &pieces,
                    &mut [false],
                    &mut String::new(),
                    None
                ),
                Err(Unsupported("raw placeholder collision"))
            );
        }
    }

    #[test]
    fn raw_utf8_decode_is_all_or_nothing_like_legacy() {
        let alloc = oxc_allocator::Allocator::default();
        assert_eq!(
            super::super::literal::arena_raw("caf\u{c3}\u{a9}", &alloc),
            "café"
        );
        let invalid = "caf\u{c3}\u{a9}\u{ff}";
        assert_eq!(super::super::literal::arena_raw(invalid, &alloc), invalid);
    }
}
