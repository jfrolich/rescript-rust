//! JS string values decode valid UTF-8 runs and map invalid bytes to Latin-1.
#[cfg(test)]
pub(super) fn string_value(s: &str) -> String {
    let bytes = crate::string_literal::bytes_of(s);
    let mut result = String::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        let (valid, _, len) = crate::string_literal::get_utf_8_uchar(&bytes, i);
        if valid {
            result.push_str(std::str::from_utf8(&bytes[i..i + len]).expect("valid UTF-8"));
            i += len;
        } else {
            result.push(char::from(bytes[i]));
            i += 1;
        }
    }
    result
}

/// Decode directly into the AST's string storage, without a temporary allocation
/// per quoted field. A four-byte window also avoids materializing Latin-1 bytes.
pub(super) fn arena_string<'a>(s: &str, alloc: &'a oxc_allocator::Allocator) -> &'a str {
    use oxc_allocator::StringBuilder;
    if s.is_ascii() || s.chars().any(|c| c as u32 > 0xff) {
        return alloc.alloc_str(s);
    }
    let mut out = StringBuilder::with_capacity_in(s.len(), alloc);
    let mut bytes = s.chars().map(|c| c as u8);
    let mut window = [0; 4];
    let mut len = 0;
    loop {
        while len < 4 {
            let Some(b) = bytes.next() else { break };
            window[len] = b;
            len += 1;
        }
        if len == 0 {
            break;
        }
        let (valid, codepoint, width) = crate::string_literal::get_utf_8_uchar(&window[..len], 0);
        let consumed = if valid {
            out.push(char::from_u32(codepoint).expect("valid UTF-8 scalar"));
            width
        } else {
            out.push(char::from(window[0]));
            1
        };
        window.copy_within(consumed..len, 0);
        len -= consumed;
    }
    out.into_str()
}

/// `printer::convert_ident_cow`, written into reusable block-local scratch.
pub(super) fn module_field<'a>(s: &str, out: &'a mut String) -> &'a str {
    out.clear();
    let (s, _) = super::walk::member_form(s);
    if crate::js_ir::printer::is_js_keyword_or_global(s) {
        out.push_str("$$");
    }
    for (i, c) in s.chars().enumerate() {
        if c.is_ascii_alphanumeric() || matches!(c, '_' | '$') {
            out.push(c);
        } else {
            out.push_str(match c {
                '*' => "$star",
                '\'' => "$p",
                '!' => "$bang",
                '>' => "$great",
                '<' => "$less",
                '=' => "$eq",
                '+' => "$plus",
                '-' if i == 0 => "$neg",
                '-' => "$",
                '@' => "$at",
                '^' => "$caret",
                '/' => "$slash",
                '|' => "$pipe",
                '.' => "$dot",
                '%' => "$percent",
                '~' => "$tilde",
                '#' => "$hash",
                ':' => "$colon",
                '?' => "$question",
                '&' => "$amp",
                '(' => "$lpar",
                ')' => "$rpar",
                '{' | '}' => "$lbrace",
                '[' => "$lbrack",
                ']' => "$rbrack",
                _ => "$unknown",
            });
        }
    }
    out.as_str()
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn arena_strings_match_byte_decoder() {
        let alloc = oxc_allocator::Allocator::default();
        for s in [
            "plain",
            "é",
            "Ã©",
            "ð\u{9f}\u{98}\u{80}",
            "ä¸",
            "💡",
            "__proto__",
        ] {
            assert_eq!(arena_string(s, &alloc), string_value(s));
        }
        for byte in 0..=255 {
            let s = char::from(byte).to_string();
            assert_eq!(arena_string(&s, &alloc), string_value(&s));
        }
    }
    #[test]
    fn module_fields_match_legacy_mangling() {
        let mut scratch = String::new();
        for s in [
            "default",
            "let",
            "Object",
            "value",
            "a-b",
            "-x",
            "*'!><=+@^/|.%~#:?&(){}[]é",
            "\\\"Foo\\\"",
        ] {
            assert_eq!(
                module_field(s, &mut scratch),
                crate::js_ir::printer::convert_ident_cow(s)
            );
        }
    }
}
