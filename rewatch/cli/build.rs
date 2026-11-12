//! Compile the runtime package of this repository into the executable (see
//! `rescript::build::snapshot`), so builds that use it need not
//! compile it. Without the package, or when it does not compile, the
//! executable embeds nothing and compiles the runtime at run time.

use std::path::{Path, PathBuf};

fn main() {
    let manifest_dir = PathBuf::from(std::env::var_os("CARGO_MANIFEST_DIR").expect("set by cargo"));
    let out = PathBuf::from(std::env::var_os("OUT_DIR").expect("set by cargo")).join("runtime.bin");
    println!("cargo:rerun-if-changed=build.rs");
    let runtime_root = manifest_dir
        .parent()
        .and_then(Path::parent)
        .map(|repo| repo.join("packages").join("@rescript").join("runtime"));
    let bytes = match runtime_root.filter(|root| root.join("rescript.json").is_file()) {
        Some(root) => {
            watch_sources(&root);
            let belt = root.parent().expect("package parent").join("belt");
            if belt.join("rescript.json").is_file() {
                watch_sources(&belt);
                watch_sources(&belt.join("src"));
            }
            rescript::build::snapshot::produce(&root).unwrap_or_else(|err| {
                if rescript::build::snapshot::is_belt_proof_failure(&err) {
                    panic!("snapshot production and proof builds: {err:#}");
                }
                println!("cargo:warning=not embedding the runtime, which failed to compile: {err:#}");
                Vec::new()
            })
        }
        None => {
            println!("cargo:warning=not embedding the runtime: packages/@rescript/runtime not found");
            Vec::new()
        }
    };
    std::fs::write(&out, bytes).expect("failed to write the embedded runtime");
}

/// Watch directory membership as well as existing sources. Cargo watches
/// directory descendants recursively: it has no exclusion for generated lib
/// outputs, even though those outputs are not explicitly listed here.
fn watch_sources(root: &Path) {
    println!("cargo:rerun-if-changed={}", root.display());
    if root.join("rescript.json").is_file() {
        println!("cargo:rerun-if-changed={}", root.join("rescript.json").display());
    }
    let entries = std::fs::read_dir(root).expect("failed to list package sources");
    for entry in entries.flatten() {
        let path = entry.path();
        if path.extension().is_some_and(|ext| ext == "res" || ext == "resi") {
            println!("cargo:rerun-if-changed={}", path.display());
        }
    }
}
