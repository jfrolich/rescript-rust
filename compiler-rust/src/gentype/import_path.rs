// Port of compiler/gentype/ImportPath.ml:1-32 and ImportPath.mli:1-11.

use std::path::Path;

/// An import path: a directory and a file name within it.
pub type T = (String, String);

/// The path of module `module_name` in `dir`, with `import_extension`.
pub fn from_module(
    dir: &str,
    import_extension: &str,
    module_name: &crate::gentype::module_name::T,
) -> T {
    let with_no_path = format!(
        "{}{}",
        crate::gentype::gen_type_common::scoped_package::remove_generated_module(
            &crate::gentype::module_name::to_string(module_name),
        ),
        import_extension
    );
    (dir.to_string(), with_no_path)
}

/// `s` as the path, unchecked.
pub fn from_string_unsafe(s: &str) -> T {
    (String::new(), s.to_string())
}

/// The path without its file name's extension.
pub fn chop_extension_safe((dir, s): &T) -> T {
    match s.rfind('.') {
        Some(idx) => (dir.clone(), s[..idx].to_string()),
        None => (dir.clone(), s.clone()),
    }
}

/// The path as a string.
pub fn dump((dir, s): &T) -> String {
    crate::gentype::gen_type_common::node_filename::concat(dir, s)
}

/// The `.cmt` file of the module imported by `path`, relative to the
/// directory of `output_file_relative`.
pub fn to_cmt(config: &crate::gentype::config::T, output_file_relative: &str, path: &T) -> String {
    let dirname = Path::new(output_file_relative)
        .parent()
        .map(|p| p.to_string_lossy().to_string())
        .unwrap_or_else(|| ".".to_string());
    let namespace = match &config.namespace {
        None => String::new(),
        Some(name) => format!("-{name}"),
    };
    format!(
        "{}{}{}",
        Path::new(&dirname)
            .join(dump(&chop_extension_safe(path)))
            .to_string_lossy(),
        namespace,
        ".cmt"
    )
}

/// The path as written in an import statement.
pub fn emit(path: &T) -> String {
    dump(path)
}
