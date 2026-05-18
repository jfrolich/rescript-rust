// Port of compiler/gentype/Indent.ml:1-23.
// This Stage 1 GenType port is intentionally not wired into the crate yet.

pub type T = Option<String>;

pub fn break_(indent: &T) -> String {
    match indent {
        None => String::new(),
        Some(s) => format!("\n{s}"),
    }
}

pub fn more(indent: &T) -> T {
    match indent {
        None => None,
        Some(s) => Some(format!("  {s}")),
    }
}

pub fn heuristic_fields<TField>(indent: &T, fields: &[TField]) -> T {
    let threshold = 2;
    match fields.len() > threshold && indent.is_none() {
        true => Some(String::new()),
        false => indent.clone(),
    }
}

pub fn heuristic_variants(indent: &T, rendered: &[String]) -> T {
    let threshold = 40;
    let break_ = rendered.join(" ").len() > threshold;
    match break_ && indent.is_none() {
        true => Some("  ".to_string()),
        false => indent.clone(),
    }
}
