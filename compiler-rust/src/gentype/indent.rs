// Port of compiler/gentype/Indent.ml:1-23.

/// The current indentation, or `None` to render on one line.
pub type T = Option<String>;

/// A line break followed by the indentation, or nothing on one line.
pub fn break_(indent: &T) -> String {
    match indent {
        None => String::new(),
        Some(s) => format!("\n{s}"),
    }
}

/// One level deeper.
pub fn more(indent: &T) -> T {
    indent.as_ref().map(|s| format!("  {s}"))
}

/// Start breaking lines when an object type has more than two fields.
pub fn heuristic_fields<TField>(indent: &T, fields: &[TField]) -> T {
    let threshold = 2;
    match fields.len() > threshold && indent.is_none() {
        true => Some(String::new()),
        false => indent.clone(),
    }
}

/// Start breaking lines when variant cases would take more than 40
/// characters on one line.
pub fn heuristic_variants(indent: &T, rendered: &[String]) -> T {
    let threshold = 40;
    let break_ = rendered.join(" ").len() > threshold;
    match break_ && indent.is_none() {
        true => Some("  ".to_string()),
        false => indent.clone(),
    }
}
