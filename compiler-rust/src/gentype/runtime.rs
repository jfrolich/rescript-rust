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

/// runtime.ml `js_field_name`: the JS backend renames bindings and module
/// fields that are JS keywords or globals, or that are not valid JS
/// identifiers (`Ext_ident.convert`), except the top-level `default` export.
pub fn js_field_name(name: &str) -> String {
    crate::js_ir::printer::convert_ident_name(name)
}

/// runtime.ml `js_export_name`.
pub fn js_export_name(name: &str) -> String {
    crate::js_ir::printer::js_export_name(name)
}

/// runtime.ml `ts_binding_name`: a name for a TS binding, renamed like the JS
/// backend does unless it is already a valid binding name, so that a value
/// named like a JS global such as `Array` keeps its name.
pub fn ts_binding_name(name: &str) -> String {
    let is_js_keyword = crate::js_ir::printer::is_js_keyword(name);
    let is_js_global = crate::js_ir::printer::is_js_keyword_or_global(name) && !is_js_keyword;
    if is_js_global {
        name.to_string()
    } else {
        crate::js_ir::printer::convert_ident_name(name)
    }
}

/// The path as a JavaScript property access.
pub fn emit_module_access_path(
    config: &crate::gentype::config::T,
    module_access_path: &ModuleAccessPath,
) -> String {
    match module_access_path {
        ModuleAccessPath::Root(s) => js_export_name(s),
        ModuleAccessPath::Dot(p, module_item) => crate::gentype::emit_text::field_access(
            config,
            &emit_module_access_path(config, p),
            &js_field_name(module_item),
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
