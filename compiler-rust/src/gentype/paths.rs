// Port of compiler/gentype/Paths.ml:1-88.

use std::path::{Path, PathBuf};

/// `right` inside directory `left`.
pub fn concat(left: &str, right: &str) -> String {
    Path::new(left).join(right).to_string_lossy().to_string()
}

fn chop_extension(path: &str) -> String {
    match path.rfind('.') {
        Some(idx) => path[..idx].to_string(),
        None => path.to_string(),
    }
}

/// The path of a `.cmt` file without its extension and namespace suffix
/// (`-Namespace`).
pub fn handle_namespace(cmt: &str) -> String {
    fn cut_after_dash(s: &str) -> String {
        match s.find('-') {
            Some(n) => s[..n].to_string(),
            None => s.to_string(),
        }
    }

    let basename = Path::new(cmt)
        .file_name()
        .and_then(|s| s.to_str())
        .unwrap_or(cmt);
    let no_dir = basename == cmt;
    if no_dir {
        cut_after_dash(&chop_extension(cmt))
    } else {
        let dir = Path::new(cmt)
            .parent()
            .map(|p| p.to_string_lossy().to_string())
            .unwrap_or_default();
        let base = cut_after_dash(&chop_extension(basename));
        concat(&dir, &base)
    }
}

/// `path` relative to directory `prefix`, when it is inside it.
pub fn remove_path_prefix(prefix: &str, path: &str) -> String {
    let normalized_prefix = concat(prefix, "");
    path.strip_prefix(normalized_prefix.as_str())
        .unwrap_or(path)
        .to_string()
}

/// The generated file's path for `source_path`.
pub fn append_suffix(config: &crate::gentype::config::T, source_path: &str) -> String {
    format!(
        "{}{}",
        handle_namespace(source_path),
        crate::gentype::module_extension::ts_input_file_suffix(config)
    )
}

/// The generated file's path for `source_path`, relative to the project
/// root.
pub fn get_output_file_relative(config: &crate::gentype::config::T, source_path: &str) -> String {
    let relative_path = remove_path_prefix(&config.project_root, source_path);
    append_suffix(config, &relative_path)
}

/// The generated file's absolute path for `source_path`.
pub fn get_output_file(config: &crate::gentype::config::T, source_path: &str) -> String {
    let relative_output_path = get_output_file_relative(config, source_path);
    concat(&config.project_root, &relative_output_path)
}

/// The module name of a `.cmt` file.
pub fn get_module_name(cmt: &str) -> crate::gentype::module_name::T {
    let handled = handle_namespace(cmt);
    let basename = Path::new(&handled)
        .file_name()
        .and_then(|s| s.to_str())
        .unwrap_or(&handled);
    crate::gentype::module_name::from_string_unsafe(basename)
}

/// The module name of a source file.
pub fn get_module_name_from_source_path(source_path: &str) -> crate::gentype::module_name::T {
    // The in-process GenType hook has the source filename instead of the
    // outputprefix.cmt passed by compiler/core/js_implementation.ml:72 and
    // compiler/core/js_implementation.ml:170. Rebuild that cmt-shaped input
    // before applying compiler/gentype/Paths.ml:61-86 so lowercase source
    // basenames keep their OCaml GenType import name.
    get_module_name(&format!("{}.cmt", chop_extension(source_path)))
}

/// The typed artifact gentype reads for `cmt` (resolved against `cwd`):
/// the first that `exists` of the `.cmti` and `.cmt` files, with the
/// module name uncapitalized or not; empty when there is none.
pub fn get_cmt_file_from_cwd_with_exists(
    cwd: &Path,
    cmt: &str,
    exists: impl Fn(&Path) -> bool,
) -> String {
    // Mirrors compiler/gentype/Paths.ml:61-86. The caller supplies the
    // existence predicate so in-process GenType can expose the same saved-CMT
    // lookup order as OCaml while reading typed artifacts from memory.
    let path_cmt = if Path::new(cmt).is_relative() {
        cwd.join(cmt)
    } else {
        PathBuf::from(cmt)
    };
    let Some(path_cmt_str) = path_cmt.to_str() else {
        return String::new();
    };
    let cmt_file = if path_cmt_str.ends_with(".cmt") {
        let dir_name = path_cmt.parent().unwrap_or_else(|| Path::new(""));
        let base_name = path_cmt
            .file_name()
            .and_then(|s| s.to_str())
            .unwrap_or_default();
        let path_cmt_lower_case = dir_name.join(crate::gentype::module_name::uncapitalize(
            &base_name.to_string(),
        ));
        let path_cmti = PathBuf::from(format!("{}.cmti", chop_extension(path_cmt_str)));
        let path_cmti_lower_case = PathBuf::from(format!(
            "{}.cmti",
            chop_extension(path_cmt_lower_case.to_string_lossy().as_ref())
        ));

        if exists(&path_cmti_lower_case) {
            path_cmti_lower_case
        } else if exists(&path_cmti) {
            path_cmti
        } else if exists(&path_cmt_lower_case) {
            path_cmt_lower_case
        } else if exists(&path_cmt) {
            path_cmt
        } else {
            PathBuf::new()
        }
    } else {
        PathBuf::new()
    };

    cmt_file.to_string_lossy().to_string()
}
