// Port of compiler/gentype/GenIdent.ml:1-23.
// This Stage 1 GenType port is intentionally not wired into the crate yet.

use std::cell::{Cell, RefCell};
use std::collections::BTreeMap;

#[derive(Debug, Clone, Default)]
pub struct TypeVarsGen {
    // Generate fresh identifiers.
    pub type_name_map: RefCell<BTreeMap<i32, String>>,
    pub type_name_counter: Cell<i32>,
}

pub fn create_type_vars_gen() -> TypeVarsGen {
    TypeVarsGen {
        type_name_map: RefCell::new(BTreeMap::new()),
        type_name_counter: Cell::new(0),
    }
}

pub fn js_type_name_for_anonymous_type_id(type_vars_gen: &TypeVarsGen, id: i32) -> String {
    // Mirrors compiler/gentype/GenIdent.ml:16-23: lookup first, then mutate
    // the map only after the failed lookup path. Drop Rust's immutable borrow
    // before taking the mutable one.
    if let Some(name) = type_vars_gen.type_name_map.borrow().get(&id).cloned() {
        return name;
    }
    let next = type_vars_gen.type_name_counter.get() + 1;
    type_vars_gen.type_name_counter.set(next);
    let name = format!("T{}", next);
    type_vars_gen
        .type_name_map
        .borrow_mut()
        .insert(id, name.clone());
    name
}
