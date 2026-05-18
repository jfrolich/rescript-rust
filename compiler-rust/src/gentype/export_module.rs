// Port of compiler/gentype/ExportModule.ml:1-132.
// This Stage 2 GenType port is intentionally not wired into the crate yet.

use crate::gentype::gen_type_common::{
    doc_string, ident, ClosedFlag, Field, Mutable, Optional, Type,
};
use indexmap::IndexMap;

// OCaml uses Hashtbl here (compiler/gentype/ExportModule.ml:3-9), not a sorted
// map. Keep this order-sensitive instead of using BTreeMap; final integration
// must verify the exact OCaml Hashtbl fold order against generated output.
pub type ExportModuleItem = IndexMap<String, ExportModuleValue>;

#[derive(Debug, Clone)]
pub enum ExportModuleValue {
    S {
        name: String,
        type_: Type,
        doc_string: doc_string::T,
    },
    M {
        export_module_item: ExportModuleItem,
    },
}

pub type ExportModuleItems = IndexMap<String, ExportModuleItem>;

#[derive(Debug, Clone)]
pub struct Types {
    pub type_for_value: Type,
    pub type_for_type: Type,
    pub doc_string: doc_string::T,
}

#[derive(Debug, Clone)]
pub struct FieldInfo {
    pub field_for_value: Field,
    pub field_for_type: Field,
}

pub fn export_module_value_to_type(
    config: &crate::gentype::config::T,
    export_module_value: &ExportModuleValue,
) -> Types {
    match export_module_value {
        ExportModuleValue::S {
            name,
            type_,
            doc_string,
        } => Types {
            type_for_value: ident(name),
            type_for_type: type_.clone(),
            doc_string: doc_string.clone(),
        },
        ExportModuleValue::M { export_module_item } => {
            let fields_info = export_module_item_to_fields(config, export_module_item);
            let fields_for_value = fields_info
                .iter()
                .map(
                    |FieldInfo {
                         field_for_value, ..
                     }| field_for_value.clone(),
                )
                .collect();
            let fields_for_type = fields_info
                .iter()
                .map(|FieldInfo { field_for_type, .. }| field_for_type.clone())
                .collect();
            Types {
                type_for_value: Type::Object(ClosedFlag::Open, fields_for_value),
                type_for_type: Type::Object(ClosedFlag::Open, fields_for_type),
                doc_string: doc_string::empty,
            }
        }
    }
}

pub fn export_module_item_to_fields(
    config: &crate::gentype::config::T,
    export_module_item: &ExportModuleItem,
) -> Vec<FieldInfo> {
    export_module_item
        .iter()
        .rev()
        .map(|(field_name, export_module_value)| {
            let Types {
                type_for_value,
                type_for_type,
                doc_string,
            } = export_module_value_to_type(config, export_module_value);
            let field_for_type = Field {
                mutable_: Mutable::Mutable,
                name_js: field_name.clone(),
                optional: Optional::Mandatory,
                type_: type_for_type,
                doc_string,
            };
            let field_for_value = Field {
                type_: type_for_value,
                ..field_for_type.clone()
            };
            FieldInfo {
                field_for_value,
                field_for_type,
            }
        })
        .collect()
}

pub fn extend_export_module_item(
    x: &[String],
    doc_string: doc_string::T,
    export_module_item: &mut ExportModuleItem,
    type_: Type,
    value_name: &str,
) {
    match x {
        [] => {}
        [field_name] => {
            export_module_item.insert(
                field_name.clone(),
                ExportModuleValue::S {
                    name: value_name.to_string(),
                    type_,
                    doc_string,
                },
            );
        }
        [field_name, rest @ ..] => {
            let inner_export_module_item = match export_module_item.get_mut(field_name) {
                Some(ExportModuleValue::M { export_module_item }) => export_module_item,
                Some(ExportModuleValue::S { .. }) => panic!("assert false"),
                None => {
                    export_module_item.insert(
                        field_name.clone(),
                        ExportModuleValue::M {
                            export_module_item: IndexMap::new(),
                        },
                    );
                    match export_module_item.get_mut(field_name) {
                        Some(ExportModuleValue::M { export_module_item }) => export_module_item,
                        _ => unreachable!(),
                    }
                }
            };
            extend_export_module_item(
                rest,
                doc_string,
                inner_export_module_item,
                type_,
                value_name,
            );
        }
    }
}

pub fn extend_export_module_items(
    x: &[String],
    doc_string: doc_string::T,
    export_module_items: &mut ExportModuleItems,
    type_: Type,
    value_name: &str,
) {
    match x {
        [] => panic!("assert false"),
        [_value_name] => {}
        [module_name, rest @ ..] => {
            let export_module_item = export_module_items
                .entry(module_name.clone())
                .or_insert_with(IndexMap::new);
            extend_export_module_item(rest, doc_string, export_module_item, type_, value_name);
        }
    }
}

pub fn create_module_items_emitter() -> ExportModuleItems {
    IndexMap::new()
}

pub fn rev_fold<F, TBase>(f: F, tbl: &ExportModuleItems, base: TBase) -> TBase
where
    F: Fn(&String, &ExportModuleItem, TBase) -> TBase,
{
    tbl.iter().rev().fold(base, |x, (k, v)| f(k, v, x))
}

pub fn emit_all_module_items(
    config: &crate::gentype::config::T,
    emitters: crate::gentype::emitters::T,
    file_name: &crate::gentype::module_name::T,
    export_module_items: &ExportModuleItems,
) -> crate::gentype::emitters::T {
    rev_fold(
        |module_name, export_module_item, emitters| {
            let Types {
                type_for_type,
                doc_string,
                ..
            } = export_module_value_to_type(
                config,
                &ExportModuleValue::M {
                    export_module_item: export_module_item.clone(),
                },
            );
            if crate::gentype::debug::code_items.load(std::sync::atomic::Ordering::Relaxed) {
                crate::gentype::log_::item(&format!("EmitModule {module_name} @."));
            }
            let emitted_module_item =
                crate::gentype::module_name::for_inner_module(file_name, module_name);
            crate::gentype::emit_type::emit_export_const(
                &emitted_module_item,
                doc_string,
                false,
                config,
                emitters,
                module_name,
                type_for_type,
                |_name| false,
            )
        },
        export_module_items,
        emitters,
    )
}

pub fn extend_export_modules(
    module_items_emitter: &mut ExportModuleItems,
    doc_string: doc_string::T,
    type_: Type,
    resolved_name: &crate::gentype::resolved_name::T,
) {
    let list = crate::gentype::resolved_name::to_list(resolved_name);
    let value_name = crate::gentype::resolved_name::to_string(resolved_name);
    extend_export_module_items(&list, doc_string, module_items_emitter, type_, &value_name);
}
