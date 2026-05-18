// Port of compiler/gentype/Paths.ml:1-88.
// This Stage 2 GenType port is intentionally not wired into the crate yet.

use std::path::{Path, PathBuf};

pub fn concat(left: &str, right: &str) -> String {
    Path::new(left).join(right).to_string_lossy().to_string()
}

fn chop_extension(path: &str) -> String {
    match path.rfind('.') {
        Some(idx) => path[..idx].to_string(),
        None => path.to_string(),
    }
}

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

pub fn find_name_space(cmt: &str) -> Option<String> {
    fn keep_after_dash(s: &str) -> Option<String> {
        match s.find('-') {
            Some(n) => Some(s[n + 1..].to_string()),
            None => None,
        }
    }

    let basename = Path::new(cmt)
        .file_name()
        .and_then(|s| s.to_str())
        .unwrap_or(cmt);
    keep_after_dash(&chop_extension(basename))
}

pub fn remove_path_prefix(prefix: &str, path: &str) -> String {
    let normalized_prefix = concat(prefix, "");
    let prefix_len = normalized_prefix.len();
    let path_len = path.len();
    let is_prefix = prefix_len <= path_len && path[..prefix_len] == normalized_prefix;
    if is_prefix {
        path[prefix_len..].to_string()
    } else {
        path.to_string()
    }
}

pub fn append_suffix(config: &crate::gentype::config::T, source_path: &str) -> String {
    format!(
        "{}{}",
        handle_namespace(source_path),
        crate::gentype::module_extension::ts_input_file_suffix(config)
    )
}

pub fn get_output_file_relative(config: &crate::gentype::config::T, source_path: &str) -> String {
    let relative_path = remove_path_prefix(&config.project_root, source_path);
    append_suffix(config, &relative_path)
}

pub fn get_output_file(config: &crate::gentype::config::T, source_path: &str) -> String {
    let relative_output_path = get_output_file_relative(config, source_path);
    concat(&config.project_root, &relative_output_path)
}

pub fn get_module_name(cmt: &str) -> crate::gentype::module_name::T {
    let handled = handle_namespace(cmt);
    let basename = Path::new(&handled)
        .file_name()
        .and_then(|s| s.to_str())
        .unwrap_or(&handled);
    crate::gentype::module_name::from_string_unsafe(basename)
}

pub fn get_cmt_file(cmt: &str) -> String {
    let path_cmt = if Path::new(cmt).is_relative() {
        std::env::current_dir()
            .unwrap_or_else(|_| PathBuf::new())
            .join(cmt)
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

        if path_cmti_lower_case.exists() {
            path_cmti_lower_case
        } else if path_cmti.exists() {
            path_cmti
        } else if path_cmt_lower_case.exists() {
            path_cmt_lower_case
        } else if path_cmt.exists() {
            path_cmt
        } else {
            PathBuf::new()
        }
    } else {
        PathBuf::new()
    };

    cmt_file.to_string_lossy().to_string()
}

pub fn read_config(namespace: Option<String>) -> crate::gentype::config::T {
    crate::gentype::config::build_config(namespace)
}
