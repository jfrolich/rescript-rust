// Port of compiler/gentype/Debug.ml:1-37.
// This Stage 1 GenType port is intentionally not wired into the crate yet.

#![allow(non_upper_case_globals)]

use std::sync::atomic::{AtomicBool, Ordering};

pub static basic: AtomicBool = AtomicBool::new(false);
pub static code_items: AtomicBool = AtomicBool::new(false);
pub static config: AtomicBool = AtomicBool::new(false);
pub static converter: AtomicBool = AtomicBool::new(false);
pub static dependencies: AtomicBool = AtomicBool::new(false);
pub static module_resolution: AtomicBool = AtomicBool::new(false);
pub static not_implemented: AtomicBool = AtomicBool::new(false);
pub static translation: AtomicBool = AtomicBool::new(false);
pub static type_env: AtomicBool = AtomicBool::new(false);
pub static type_resolution: AtomicBool = AtomicBool::new(false);

pub fn set_all() {
    basic.store(true, Ordering::Relaxed);
    code_items.store(true, Ordering::Relaxed);
    config.store(true, Ordering::Relaxed);
    converter.store(true, Ordering::Relaxed);
    dependencies.store(true, Ordering::Relaxed);
    module_resolution.store(true, Ordering::Relaxed);
    not_implemented.store(true, Ordering::Relaxed);
    translation.store(true, Ordering::Relaxed);
    type_env.store(true, Ordering::Relaxed);
    type_resolution.store(true, Ordering::Relaxed);
}

pub fn set_item(debug_item: &str) {
    match debug_item {
        "all" => set_all(),
        "basic" => basic.store(true, Ordering::Relaxed),
        "codeItems" => code_items.store(true, Ordering::Relaxed),
        "config" => config.store(true, Ordering::Relaxed),
        "converter" => converter.store(true, Ordering::Relaxed),
        "dependencies" => dependencies.store(true, Ordering::Relaxed),
        "moduleResolution" => module_resolution.store(true, Ordering::Relaxed),
        "notImplemented" => not_implemented.store(true, Ordering::Relaxed),
        "translation" => translation.store(true, Ordering::Relaxed),
        "typeEnv" => type_env.store(true, Ordering::Relaxed),
        "typeResolution" => type_resolution.store(true, Ordering::Relaxed),
        _ => {}
    }
}
