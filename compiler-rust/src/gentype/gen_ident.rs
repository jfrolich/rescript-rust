// Port of compiler/gentype/GenIdent.ml:1-23.
// This Stage 1 GenType port is intentionally not wired into the crate yet.

use std::collections::BTreeMap;

#[derive(Debug, Clone, Default)]
pub struct TypeVarsGen {
    // Generate fresh identifiers.
    pub type_name_map: BTreeMap<i32, String>,
    pub type_name_counter: i32,
}

pub fn create_type_vars_gen() -> TypeVarsGen {
    TypeVarsGen {
        type_name_map: BTreeMap::new(),
        type_name_counter: 0,
    }
}

pub fn js_type_name_for_anonymous_type_id(type_vars_gen: &mut TypeVarsGen, id: i32) -> String {
    match type_vars_gen.type_name_map.get(&id) {
        Some(name) => name.clone(),
        None => {
            type_vars_gen.type_name_counter += 1;
            let name = format!("T{}", type_vars_gen.type_name_counter);
            type_vars_gen.type_name_map.insert(id, name.clone());
            name
        }
    }
}
