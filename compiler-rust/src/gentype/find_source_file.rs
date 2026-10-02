// Port of compiler/gentype/FindSourceFile.ml:1-30 and FindSourceFile.mli:1-8.
// This Stage 2 GenType port is intentionally not wired into the crate yet.

use std::path::{Path, PathBuf};

use crate::parse_arena::ParseArena;
use crate::types::typedtree::{StructureItem, TypedSignatureItem};

pub fn interface(arena: &ParseArena, items: &[TypedSignatureItem]) -> Option<String> {
    for item in items {
        let loc = arena.to_location(item.sig_loc);
        let file = arena.get_string(loc.loc_start.file_name);
        match !Path::new(file).exists() {
            true => continue,
            false => return Some(file.to_string()),
        }
    }
    None
}

pub fn implementation(arena: &ParseArena, items: &[StructureItem]) -> Option<String> {
    for item in items {
        let loc = arena.to_location(item.str_loc);
        let file = arena.get_string(loc.loc_start.file_name);
        match !Path::new(file).exists() {
            true => continue,
            false => return Some(file.to_string()),
        }
    }
    None
}

pub fn transform_to_absolute_path(path: Option<String>) -> Option<String> {
    path.map(|path| {
        if Path::new(&path).is_relative() {
            crate::process_cwd::current_dir()
                .unwrap_or_else(|_| PathBuf::new())
                .join(path)
                .to_string_lossy()
                .to_string()
        } else {
            path
        }
    })
}

pub fn cmt(arena: &ParseArena, cmt_annots: &crate::gentype::main::BinaryAnnots) -> Option<String> {
    match cmt_annots {
        crate::gentype::main::BinaryAnnots::Interface(signature) => {
            transform_to_absolute_path(interface(arena, &signature.sig_items))
        }
        crate::gentype::main::BinaryAnnots::Implementation(structure) => {
            transform_to_absolute_path(implementation(arena, &structure.str_items))
        }
        _ => None,
    }
}
