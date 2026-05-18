// Port of compiler/gentype/GenTypeMain.ml:1-175.
// This Stage 4 GenType port is intentionally not wired into the crate yet.

use std::cell::Cell;
use std::path::Path;

use crate::parse_arena::{LocIdx, ParseArena};
use crate::parser::ast::Attributes;
use crate::types::typedtree::{
    Structure, StructureItem, StructureItemDesc, TypedSignature, TypedSignatureItem,
    TypedSignatureItemDesc,
};

pub enum BinaryAnnots {
    Implementation(Structure),
    Interface(TypedSignature),
    Packed,
    PartialImplementation,
    PartialInterface,
}

pub struct InputCmt {
    pub cmt_annots: BinaryAnnots,
    pub arena: ParseArena,
}

pub fn cmt_check_annotations(
    check_annotation: &impl Fn(&ParseArena, LocIdx, &Attributes) -> bool,
    input_cmt: &InputCmt,
) -> bool {
    // Mirrors compiler/gentype/GenTypeMain.ml:3-10.
    match &input_cmt.cmt_annots {
        BinaryAnnots::Implementation(structure) => {
            crate::gentype::annotation::structure_check_annotation(
                &input_cmt.arena,
                &|loc, attributes| check_annotation(&input_cmt.arena, loc, attributes),
                structure,
            )
        }
        BinaryAnnots::Interface(signature) => {
            crate::gentype::annotation::signature_check_annotation(
                &input_cmt.arena,
                &|loc, attributes| check_annotation(&input_cmt.arena, loc, attributes),
                signature,
            )
        }
        BinaryAnnots::Packed
        | BinaryAnnots::PartialImplementation
        | BinaryAnnots::PartialInterface => false,
    }
}

pub fn cmt_has_type_errors(input_cmt: &InputCmt) -> bool {
    // Mirrors compiler/gentype/GenTypeMain.ml:11-14.
    matches!(
        &input_cmt.cmt_annots,
        BinaryAnnots::PartialImplementation | BinaryAnnots::PartialInterface
    )
}

pub fn structure_item_is_declaration(struct_item: &StructureItem) -> bool {
    // Mirrors compiler/gentype/GenTypeMain.ml:16-20.
    matches!(
        &struct_item.str_desc,
        StructureItemDesc::Tstr_type(_, _)
            | StructureItemDesc::Tstr_modtype(_)
            | StructureItemDesc::Tstr_module(_)
    )
}

pub fn signature_item_is_declaration(signature_item: &TypedSignatureItem) -> bool {
    // Mirrors compiler/gentype/GenTypeMain.ml:21-24.
    matches!(
        &signature_item.sig_desc,
        TypedSignatureItemDesc::Tsig_type(_, _) | TypedSignatureItemDesc::Tsig_modtype(_)
    )
}

pub fn input_cmt_translate_type_declarations_from_cmt(
    config: &crate::gentype::config::T,
    output_file_relative: &str,
    resolver: &crate::gentype::module_resolver::Resolver,
    input_cmt: &InputCmt,
) -> crate::gentype::translation::T {
    // Mirrors compiler/gentype/GenTypeMain.ml:26-52.
    let type_env = crate::gentype::type_env::root();
    let translations = match &input_cmt.cmt_annots {
        BinaryAnnots::Implementation(structure) => {
            let mut structure = structure.clone();
            structure
                .str_items
                .retain(|item| structure_item_is_declaration(item));
            crate::gentype::translate_structure::translate_structure(
                &input_cmt.arena,
                config,
                output_file_relative,
                resolver,
                &type_env,
                &structure,
            )
        }
        BinaryAnnots::Interface(signature) => {
            let mut signature = signature.clone();
            signature
                .sig_items
                .retain(|item| signature_item_is_declaration(item));
            crate::gentype::translate_signature::translate_signature(
                &input_cmt.arena,
                config,
                output_file_relative,
                resolver,
                &type_env,
                &signature,
            )
        }
        BinaryAnnots::Packed
        | BinaryAnnots::PartialImplementation
        | BinaryAnnots::PartialInterface => {
            vec![]
        }
    };
    crate::gentype::translation::add_type_declarations_from_module_equations(
        &type_env,
        crate::gentype::translation::combine(&translations),
    )
}

pub fn input_cmt_translate_type_declarations(
    config: &mut crate::gentype::config::T,
    output_file_relative: &str,
    resolver: &crate::gentype::module_resolver::Resolver,
    cmt_file: &str,
) -> crate::gentype::translation::T {
    // This is the Rust callback boundary used by emit_js.rs for
    // compiler/gentype/EmitJs.ml:449-453.
    let input_cmt = read_cmt(cmt_file);
    input_cmt_translate_type_declarations_from_cmt(
        config,
        output_file_relative,
        resolver,
        &input_cmt,
    )
}

pub fn translate_c_m_t(
    config: &crate::gentype::config::T,
    output_file_relative: &str,
    resolver: &crate::gentype::module_resolver::Resolver,
    input_cmt: &InputCmt,
) -> crate::gentype::translation::T {
    // Mirrors compiler/gentype/GenTypeMain.ml:53-70.
    let type_env = crate::gentype::type_env::root();
    let translations = match &input_cmt.cmt_annots {
        BinaryAnnots::Implementation(structure) => {
            crate::gentype::translate_structure::translate_structure(
                &input_cmt.arena,
                config,
                output_file_relative,
                resolver,
                &type_env,
                structure,
            )
        }
        BinaryAnnots::Interface(signature) => {
            crate::gentype::translate_signature::translate_signature(
                &input_cmt.arena,
                config,
                output_file_relative,
                resolver,
                &type_env,
                signature,
            )
        }
        BinaryAnnots::Packed
        | BinaryAnnots::PartialImplementation
        | BinaryAnnots::PartialInterface => {
            vec![]
        }
    };
    crate::gentype::translation::add_type_declarations_from_module_equations(
        &type_env,
        crate::gentype::translation::combine(&translations),
    )
}

pub fn emit_translation(
    config: &mut crate::gentype::config::T,
    file_name: &crate::gentype::module_name::T,
    output_file: &str,
    output_file_relative: &str,
    resolver: &crate::gentype::module_resolver::Resolver,
    source_file: &str,
    translation: &crate::gentype::translation::T,
) -> std::io::Result<()> {
    // Mirrors compiler/gentype/GenTypeMain.ml:72-83.
    let code_text = crate::gentype::emit_js::emit_translation_as_string(
        config,
        file_name,
        &input_cmt_translate_type_declarations,
        output_file_relative,
        resolver,
        translation,
    );
    let source_file = Path::new(source_file)
        .file_name()
        .and_then(|s| s.to_str())
        .unwrap_or(source_file);
    let file_contents = format!(
        "{}\n{}\n",
        crate::gentype::emit_type::file_header(source_file),
        code_text
    );
    crate::gentype::generated_files::write_file_if_required(output_file, &file_contents)
}

pub fn read_cmt(cmt_file: &str) -> InputCmt {
    // Mirrors compiler/gentype/GenTypeMain.ml:85-91. Actual CMT decoding is
    // wired later; this staged port preserves the stale-artifact error boundary.
    match std::fs::read(cmt_file) {
        Ok(data) if data.starts_with(b"Caml1999T022") => {
            unimplemented!("Cmt_format.read_cmt typedtree decoding is wired in Phase 3")
        }
        Ok(data) if data.starts_with(b"Caml1999I022") => {
            panic!("Fatal error: exception Cmt_format.Error(_)")
        }
        _ => {
            crate::gentype::log_::item(&format!("Error loading {cmt_file}\n\n"));
            crate::gentype::log_::item(
                "It looks like you might have stale compilation artifacts.\n",
            );
            crate::gentype::log_::item("Try to clean and rebuild.\n\n");
            panic!(
                "Fatal error: exception File \"compiler/gentype/GenTypeMain.ml\", line 91, characters 4-10: Assertion failed"
            )
        }
    }
}

fn chop_extension(path: &str) -> String {
    match path.rfind('.') {
        Some(idx) => path[..idx].to_string(),
        None => path.to_string(),
    }
}

pub fn read_input_cmt(is_interface: bool, cmt_file: &str) -> (InputCmt, bool) {
    // Mirrors compiler/gentype/GenTypeMain.ml:93-134.
    let input_cmt = read_cmt(cmt_file);
    let ignore_interface = Cell::new(false);
    let check_annotation = |arena: &ParseArena, _loc: LocIdx, attributes: &Attributes| {
        if crate::gentype::annotation::get_attribute_payload(
            arena,
            crate::gentype::annotation::tag_is_gentype_ignore_interface,
            attributes,
        )
        .is_some()
        {
            ignore_interface.set(true);
        }
        crate::gentype::annotation::get_attribute_payload(
            arena,
            crate::gentype::annotation::tag_is_one_of_the_gentype_annotations,
            attributes,
        )
        .is_some()
    };
    let has_gentype_annotations = cmt_check_annotations(&check_annotation, &input_cmt);

    if is_interface {
        let cmt_file_impl = format!("{}.cmt", chop_extension(cmt_file));
        let input_cmt_impl = read_cmt(&cmt_file_impl);
        let has_gentype_annotations_impl = cmt_check_annotations(
            &|arena, loc, attributes| {
                if check_annotation(arena, loc, attributes) {
                    if !ignore_interface.get() {
                        crate::gentype::log_::color::setup();
                        let loc = arena.to_location(loc);
                        crate::gentype::log_::info(
                            || "Annotation is ignored as there's a .resi file".to_string(),
                            &loc,
                            "Warning genType",
                        );
                    }
                    true
                } else {
                    false
                }
            },
            &input_cmt_impl,
        );
        if ignore_interface.get() {
            (input_cmt_impl, has_gentype_annotations_impl)
        } else {
            (input_cmt, has_gentype_annotations)
        }
    } else {
        (input_cmt, has_gentype_annotations)
    }
}

pub fn process_cmt_file(cmt: &str) -> std::io::Result<()> {
    // Mirrors compiler/gentype/GenTypeMain.ml:136-175.
    let mut config =
        crate::gentype::paths::read_config(crate::gentype::paths::find_name_space(cmt));
    if crate::gentype::debug::basic.load(std::sync::atomic::Ordering::Relaxed) {
        crate::gentype::log_::item(&format!("Cmt {cmt}\n"));
    }
    let cmt_file = crate::gentype::paths::get_cmt_file(cmt);
    if !cmt_file.is_empty() {
        let file_name = crate::gentype::paths::get_module_name(cmt);
        let is_interface = cmt_file.ends_with(".cmti");
        let (input_cmt, has_gentype_annotations) = read_input_cmt(is_interface, &cmt_file);
        let source_file =
            match crate::gentype::find_source_file::cmt(&input_cmt.arena, &input_cmt.cmt_annots) {
                Some(source_file) => source_file,
                None => format!(
                    "{}{}",
                    crate::gentype::module_name::to_string(&file_name),
                    match is_interface {
                        true => ".resi",
                        false => ".res",
                    }
                ),
            };
        let output_file = crate::gentype::paths::get_output_file(&config, &source_file);
        let output_file_relative =
            crate::gentype::paths::get_output_file_relative(&config, &source_file);
        let resolver = crate::gentype::module_resolver::create_lazy_resolver(
            &config,
            &[".res".to_string(), ".shim.ts".to_string()],
            |fname| fname == "React.res" || fname == "ReasonReact.res",
        );
        if has_gentype_annotations {
            let translation =
                translate_c_m_t(&config, &output_file_relative, &resolver, &input_cmt);
            emit_translation(
                &mut config,
                &file_name,
                &output_file,
                &output_file_relative,
                &resolver,
                &source_file,
                &translation,
            )?;
        } else if cmt_has_type_errors(&input_cmt) {
            crate::gentype::generated_files::log_file_action(
                crate::gentype::generated_files::FileAction::TypeError,
                &output_file,
            );
        } else {
            crate::gentype::generated_files::log_file_action(
                crate::gentype::generated_files::FileAction::NoMatch,
                &output_file,
            );
            if Path::new(&output_file).exists() {
                std::fs::remove_file(&output_file)?;
            }
        }
    }
    Ok(())
}
