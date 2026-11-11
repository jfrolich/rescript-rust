// Port of compiler/gentype/Runtime.ml:1-41 and Runtime.mli:1-16.

/// The name of a module item at runtime.
pub type ModuleItem = String;

/// How a value is reached in the compiled JavaScript module.
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub enum ModuleAccessPath {
    /// A toplevel binding.
    Root(String),
    /// An item of the module reached by the inner path.
    Dot(Box<ModuleAccessPath>, ModuleItem),
}

/// The runtime name of item `name`.
pub fn new_module_item(name: &str) -> ModuleItem {
    name.to_string()
}

/// The path as a JavaScript property access.
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

/// The field holding a variant's case: `NAME` for polymorphic variants,
/// else the `@tag` name or `TAG`.
pub fn js_variant_tag(polymorphic: bool, tag: Option<&str>) -> String {
    match polymorphic {
        true => "NAME".to_string(),
        false => match tag {
            Some(tag) => tag.to_string(),
            None => "TAG".to_string(),
        },
    }
}

/// The field holding a variant's `n`th payload.
pub fn js_variant_payload_tag(n: i32) -> String {
    format!("_{n}")
}

/// The field holding a variant's payload: `VAL` for polymorphic variants,
/// else `value`.
pub fn js_variant_value(polymorphic: bool) -> String {
    match polymorphic {
        true => "VAL".to_string(),
        false => "value".to_string(),
    }
}

/// The name the default export is bound to.
pub const DEFAULT: &str = "$$default";
