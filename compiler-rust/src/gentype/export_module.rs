// Port of compiler/gentype/ExportModule.ml:1-132.

use crate::gentype::gen_type_common::{
    ClosedFlag, Field, Mutable, Optional, Type, doc_string, ident,
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

fn ocaml_hashtbl_power_2_above(mut x: usize, n: usize) -> usize {
    while x < n {
        if x > (isize::MAX as usize / 2) {
            break;
        }
        x *= 2;
    }
    x
}

fn ocaml_hash_mix_uint32(mut h: u32, mut d: u32) -> u32 {
    d = d.wrapping_mul(0xcc9e2d51);
    d = d.rotate_left(15);
    d = d.wrapping_mul(0x1b873593);
    h ^= d;
    h = h.rotate_left(13);
    h.wrapping_mul(5).wrapping_add(0xe6546b64)
}

fn ocaml_hash_final_mix(mut h: u32) -> u32 {
    h ^= h >> 16;
    h = h.wrapping_mul(0x85ebca6b);
    h ^= h >> 13;
    h = h.wrapping_mul(0xc2b2ae35);
    h ^= h >> 16;
    h
}

fn ocaml_hashtbl_hash_string(s: &str) -> u32 {
    let bytes = s.as_bytes();
    let len = bytes.len();
    let mut h = 0u32;
    let mut i = 0usize;

    while i + 4 <= len {
        let w = u32::from_le_bytes([bytes[i], bytes[i + 1], bytes[i + 2], bytes[i + 3]]);
        h = ocaml_hash_mix_uint32(h, w);
        i += 4;
    }

    let rem = len & 3;
    if rem != 0 {
        let mut w = 0u32;
        if rem >= 3 {
            w |= (bytes[i + 2] as u32) << 16;
        }
        if rem >= 2 {
            w |= (bytes[i + 1] as u32) << 8;
        }
        w |= bytes[i] as u32;
        h = ocaml_hash_mix_uint32(h, w);
    }

    h ^= len as u32;
    ocaml_hash_final_mix(h) & 0x3fff_ffff
}

fn ocaml_hashtbl_replace_fold_cons_order<'a>(
    keys_in_replace_order: impl Iterator<Item = &'a String>,
) -> Vec<String> {
    // GenType's OCaml ExportModule uses `Hashtbl.create 1`,
    // `Hashtbl.replace`, and `Hashtbl.fold (fun k v acc -> ... :: acc)`;
    // see compiler/gentype/ExportModule.ml:41-57 and 104-125. The table
    // mechanics here follow OCaml stdlib hashtbl.ml:73-78, 207-223,
    // 505-508, and 592-598 for string keys with the default seed.
    let keys: Vec<String> = keys_in_replace_order.cloned().collect();
    let mut buckets: Vec<Vec<usize>> = vec![Vec::new(); ocaml_hashtbl_power_2_above(16, 1)];
    let mut size = 0usize;

    for (entry_idx, key) in keys.iter().enumerate() {
        let bucket_idx = (ocaml_hashtbl_hash_string(key) as usize) & (buckets.len() - 1);
        if buckets[bucket_idx]
            .iter()
            .any(|&idx| keys[idx].as_str() == key.as_str())
        {
            continue;
        }
        buckets[bucket_idx].insert(0, entry_idx);
        size += 1;

        if size > (buckets.len() << 1) {
            let mut new_buckets = vec![Vec::new(); buckets.len() * 2];
            for bucket in &buckets {
                for &idx in bucket {
                    let new_idx =
                        (ocaml_hashtbl_hash_string(&keys[idx]) as usize) & (new_buckets.len() - 1);
                    new_buckets[new_idx].push(idx);
                }
            }
            buckets = new_buckets;
        }
    }

    let mut traversal = Vec::with_capacity(size);
    for bucket in &buckets {
        for &idx in bucket {
            traversal.push(keys[idx].clone());
        }
    }
    traversal.reverse();
    traversal
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
    ocaml_hashtbl_replace_fold_cons_order(export_module_item.keys())
        .into_iter()
        .filter_map(|field_name| {
            let export_module_value = export_module_item.get(&field_name)?;
            let Types {
                type_for_value,
                type_for_type,
                doc_string,
            } = export_module_value_to_type(config, export_module_value);
            let field_for_type = Field {
                mutable_: Mutable::Mutable,
                name_js: crate::gentype::runtime::js_field_name(&field_name),
                optional: Optional::Mandatory,
                type_: type_for_type,
                doc_string,
            };
            let field_for_value = Field {
                type_: type_for_value,
                ..field_for_type.clone()
            };
            Some(FieldInfo {
                field_for_value,
                field_for_type,
            })
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
            let export_module_item = export_module_items.entry(module_name.clone()).or_default();
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
    ocaml_hashtbl_replace_fold_cons_order(tbl.keys())
        .iter()
        .fold(base, |x, k| match tbl.get(k) {
            Some(v) => f(k, v, x),
            None => x,
        })
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
            let emitted_module_item = crate::gentype::module_name::for_inner_module(
                file_name,
                &crate::gentype::runtime::js_export_name(module_name),
            );
            crate::gentype::emit_type::emit_export_const(
                false,
                "",
                config,
                doc_string,
                emitters,
                &crate::gentype::runtime::ts_binding_name(module_name),
                &type_for_type,
                &|_name| false,
                &emitted_module_item,
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
    let value_name = crate::gentype::runtime::ts_binding_name(
        &crate::gentype::resolved_name::to_string(resolved_name),
    );
    extend_export_module_items(&list, doc_string, module_items_emitter, type_, &value_name);
}
