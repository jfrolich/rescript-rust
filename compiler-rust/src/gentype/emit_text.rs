// Port of compiler/gentype/EmitText.ml:1-13.
// This Stage 4 GenType port is intentionally not wired into the crate yet.

pub type NameGen = std::collections::HashMap<String, i32>;

pub fn parens(xs: &[String]) -> String {
    format!("({})", xs.join(", "))
}

pub fn comment(x: &str) -> String {
    format!("/* {x} */")
}

pub fn generics_string(type_vars: &[String]) -> String {
    match type_vars.is_empty() {
        true => String::new(),
        false => format!("<{}>", type_vars.join(",")),
    }
}

/// Mirrors compiler/gentype/emit_text.ml:11 (`String_literal.encode_js_string`).
pub fn escape_string_contents(s: &str) -> String {
    crate::string_literal::encode_js_string(s)
}

pub fn quotes(x: &str) -> String {
    format!("\"{x}\"")
}

pub fn field_access(_config: &crate::gentype::config::T, value: &str, label: &str) -> String {
    format!("{value}.{label}")
}
