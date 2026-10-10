// Port of compiler/gentype/Runtime.ml:1-41 and Runtime.mli:1-16.
// This Stage 2 GenType port is intentionally not wired into the crate yet.

pub type ModuleItem = String;

#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum ModuleAccessPath {
    Root(String),
    Dot(Box<ModuleAccessPath>, ModuleItem),
}

pub fn new_module_item(name: &str) -> ModuleItem {
    name.to_string()
}

pub fn emit_module_access_path(
    config: &crate::gentype::config::T,
    module_access_path: &ModuleAccessPath,
) -> String {
    match module_access_path {
        ModuleAccessPath::Root(s) => s.clone(),
        ModuleAccessPath::Dot(p, module_item) => crate::gentype::emit_text::field_access(
            config,
            &emit_module_access_path(config, p),
            module_item,
        ),
    }
}

pub fn js_variant_tag(polymorphic: bool, tag: Option<&str>) -> String {
    match polymorphic {
        true => "NAME".to_string(),
        false => match tag {
            Some(tag) => tag.to_string(),
            None => "TAG".to_string(),
        },
    }
}

pub fn js_variant_payload_tag(n: i32) -> String {
    format!("_{n}")
}

pub fn js_variant_value(polymorphic: bool) -> String {
    match polymorphic {
        true => "VAL".to_string(),
        false => "value".to_string(),
    }
}

pub const default: &str = "$$default";
