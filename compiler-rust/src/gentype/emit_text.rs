// Port of compiler/gentype/EmitText.ml:1-13.

/// `xs` separated by commas, in parentheses.
pub fn parens(xs: &[String]) -> String {
    format!("({})", xs.join(", "))
}

/// `x` in a block comment.
pub fn comment(x: &str) -> String {
    format!("/* {x} */")
}

/// The type parameter list `<a,b>`, or nothing without parameters.
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

/// `x` in double quotes.
pub fn quotes(x: &str) -> String {
    format!("\"{x}\"")
}

/// The property access `value.label`.
pub fn field_access(_config: &crate::gentype::config::T, value: &str, label: &str) -> String {
    format!("{value}.{label}")
}
