// Port of compiler/gentype/ModuleName.ml:1-28 and ModuleName.mli:1-13.

use std::cmp::Ordering;

pub type T = String;

pub const curry: &str = "Curry";
pub const rescript_pervasives: &str = "RescriptPervasives";

pub fn sanitize_id(s: &str) -> String {
    let s = if s.contains('.') || s.contains('[') || s.contains(']') {
        s.chars()
            .map(|c| match c {
                '.' | '[' | ']' => '_',
                c => c,
            })
            .collect::<String>()
    } else {
        s.to_string()
    };

    match s.as_bytes().first() {
        Some(first) if *first >= b'A' && *first <= b'z' => s,
        _ => format!("_{s}"),
    }
}

pub fn for_js_file(s: &str) -> T {
    format!("{}JS", sanitize_id(s))
}

pub fn for_inner_module(file_name: &str, inner_module_name: &str) -> T {
    format!("{}.{}", for_js_file(file_name), inner_module_name)
}

pub fn from_string_unsafe(s: &str) -> T {
    s.to_string()
}

pub fn to_string(s: &T) -> String {
    s.clone()
}

pub fn compare(s1: &T, s2: &T) -> Ordering {
    s1.cmp(s2)
}

pub fn uncapitalize(s: &T) -> T {
    // OCaml String.uncapitalize_ascii (module_name.ml:28): only an ASCII
    // first byte is lowercased.
    let mut s = s.clone();
    if let Some(first) = s.get_mut(0..1) {
        first.make_ascii_lowercase();
    }
    s
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn uncapitalize_lowercases_only_an_ascii_first_char() {
        assert_eq!(uncapitalize(&"Foo.cmt".to_string()), "foo.cmt");
        assert_eq!(uncapitalize(&"foo".to_string()), "foo");
        assert_eq!(uncapitalize(&String::new()), "");
        assert_eq!(uncapitalize(&"\u{c9}cole".to_string()), "\u{c9}cole");
        assert_eq!(
            uncapitalize(&"\u{c3}\u{89}cole".to_string()),
            "\u{c3}\u{89}cole"
        );
    }
}
