// Port of compiler/gentype/ModuleExtension.ml:1-28.
// This Stage 2 GenType port is intentionally not wired into the crate yet.

use crate::gentype::config::{ModuleResolution, T};

pub fn shim_ts_output_file_extension(config: &T) -> String {
    match config.module_resolution {
        ModuleResolution::Node => ".shim".to_string(),
        ModuleResolution::Node16 => ".shim.js".to_string(),
        ModuleResolution::Bundler => ".shim.ts".to_string(),
    }
}

fn remove_extension(s: &str) -> String {
    match s.rfind('.') {
        Some(idx) if idx > 0 => s[..idx].to_string(),
        None => s.to_string(),
        Some(_) => s.to_string(),
    }
}

fn extension(s: &str) -> String {
    match s.rfind('.') {
        Some(idx) if idx > 0 => s[idx..].to_string(),
        None => String::new(),
        Some(_) => String::new(),
    }
}

pub fn generated_files_extension(config: &T) -> String {
    match &config.generated_file_extension {
        Some(s) => remove_extension(s),
        None => ".gen".to_string(),
    }
}

pub fn ts_input_file_suffix(config: &T) -> String {
    match &config.generated_file_extension {
        Some(s) if !extension(s).is_empty() => s.clone(),
        _ => format!("{}.tsx", generated_files_extension(config)),
    }
}

pub fn ts_output_file_suffix(config: &T) -> String {
    format!("{}.js", generated_files_extension(config))
}

pub fn generated_module_extension(config: &T) -> String {
    match config.module_resolution {
        ModuleResolution::Node => generated_files_extension(config),
        ModuleResolution::Node16 => ts_output_file_suffix(config),
        ModuleResolution::Bundler => ts_input_file_suffix(config),
    }
}
