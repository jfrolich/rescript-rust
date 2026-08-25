// Port of compiler/gentype/GenTypeMain.ml:1-175.

use std::cell::Cell;
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::{Mutex, OnceLock};

use crate::parse_arena::{LocIdx, ParseArena};
use crate::parser::ast::Attributes;
use crate::types::context::TypeContext;
use crate::types::typedtree::{
    Structure, StructureItem, StructureItemDesc, TypedSignature, TypedSignatureItem,
    TypedSignatureItemDesc,
};

type InProcessTypeDeclarations = Vec<crate::gentype::code_item::TypeDeclaration>;
type InProcessTypeDeclarationsCache = Mutex<HashMap<String, InProcessTypeDeclarations>>;

pub enum BinaryAnnots {
    Implementation(Structure),
    Interface(TypedSignature),
    Packed,
    PartialImplementation,
    PartialInterface,
}

pub struct InputCmt<'a> {
    pub cmt_annots: BinaryAnnots,
    pub arena: ParseArena,
    pub ctx: &'a TypeContext,
}

pub enum TypedArtifactAnnots<'a> {
    Implementation(&'a Structure),
    Interface(&'a TypedSignature),
    Packed,
    PartialImplementation,
    PartialInterface,
}

pub struct TypedArtifact<'a> {
    pub annots: TypedArtifactAnnots<'a>,
    pub arena: &'a ParseArena,
    pub ctx: &'a TypeContext,
    pub source_file: Option<&'a str>,
    pub compiler_module_name: crate::gentype::module_name::T,
    pub file_name: crate::gentype::module_name::T,
    pub is_interface: bool,
}

fn in_process_type_declarations_cache() -> &'static InProcessTypeDeclarationsCache {
    static CACHE: OnceLock<InProcessTypeDeclarationsCache> = OnceLock::new();
    CACHE.get_or_init(|| Mutex::new(HashMap::new()))
}

fn normalize_cmt_path_lexically(path: PathBuf) -> PathBuf {
    path.components()
        .filter(|component| !matches!(component, std::path::Component::CurDir))
        .fold(PathBuf::new(), |mut normalized, component| {
            normalized.push(component.as_os_str());
            normalized
        })
}

fn normalize_cmt_cache_key(cmt_file: &str) -> String {
    // Keep the in-process cache key on the same absolute path base that
    // compiler/gentype/Paths.ml:61-64 applies before selecting .cmti/.cmt
    // artifacts. OCaml then checks physical files at
    // compiler/gentype/Paths.ml:79-83, where `./` segments are resolved by
    // the filesystem; the virtual in-process CMT cache has to remove those
    // lexical no-op segments before comparing keys.
    let path = PathBuf::from(cmt_file);
    let path = if path.is_relative() {
        std::env::current_dir()
            .unwrap_or_else(|_| PathBuf::new())
            .join(path)
    } else {
        path
    };
    std::fs::canonicalize(&path)
        .unwrap_or_else(|_| normalize_cmt_path_lexically(path))
        .to_string_lossy()
        .to_string()
}

fn has_in_process_type_declarations(cmt_file: &Path) -> bool {
    let Some(cmt_file) = cmt_file.to_str() else {
        return false;
    };
    let key = normalize_cmt_cache_key(cmt_file);
    in_process_type_declarations_cache()
        .lock()
        .map(|cache| cache.contains_key(&key))
        .unwrap_or(false)
}

fn lookup_in_process_type_declarations(cmt_file: &str) -> Option<InProcessTypeDeclarations> {
    in_process_type_declarations_cache()
        .lock()
        .ok()
        .and_then(|cache| cache.get(&normalize_cmt_cache_key(cmt_file)).cloned())
}

fn register_in_process_type_declarations(
    cmt_file: &str,
    type_declarations: InProcessTypeDeclarations,
) {
    if let Ok(mut cache) = in_process_type_declarations_cache().lock() {
        cache.insert(normalize_cmt_cache_key(cmt_file), type_declarations);
    }
}

fn get_cmt_file_for_typed_artifact_import(project_root: &str, cmt: &str) -> String {
    // OCaml saves CMTs before GenType reads imports through
    // compiler/ml/typemod.ml:1763-1764 and compiler/ml/typemod.ml:1785-1787;
    // EmitJs then selects the artifact at compiler/gentype/EmitJs.ml:438-453
    // using the path order in compiler/gentype/Paths.ml:61-86. Rewatch's
    // in-process Rust path keeps those typed artifacts in memory and compiles
    // from the workspace root, so use Config.project_root as the package cwd
    // that compiler/gentype/GenTypeConfig.ml:124-131 gives OCaml GenType.
    crate::gentype::paths::get_cmt_file_from_cwd_with_exists(Path::new(project_root), cmt, |path| {
        path.exists() || has_in_process_type_declarations(path)
    })
}

pub fn cmt_check_annotations(
    check_annotation: &impl Fn(&ParseArena, LocIdx, &Attributes) -> bool,
    input_cmt: &InputCmt<'_>,
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

pub fn cmt_has_type_errors(input_cmt: &InputCmt<'_>) -> bool {
    // Mirrors compiler/gentype/GenTypeMain.ml:11-14.
    matches!(
        &input_cmt.cmt_annots,
        BinaryAnnots::PartialImplementation | BinaryAnnots::PartialInterface
    )
}

pub fn typed_artifact_check_annotations(
    check_annotation: &impl Fn(&ParseArena, LocIdx, &Attributes) -> bool,
    artifact: &TypedArtifact<'_>,
) -> bool {
    // Mirrors compiler/gentype/GenTypeMain.ml:3-10 for in-memory typed
    // artifacts, using the same Annotation traversal that CMT decoding feeds.
    match artifact.annots {
        TypedArtifactAnnots::Implementation(structure) => {
            crate::gentype::annotation::structure_check_annotation(
                artifact.arena,
                &|loc, attributes| check_annotation(artifact.arena, loc, attributes),
                structure,
            )
        }
        TypedArtifactAnnots::Interface(signature) => {
            crate::gentype::annotation::signature_check_annotation(
                artifact.arena,
                &|loc, attributes| check_annotation(artifact.arena, loc, attributes),
                signature,
            )
        }
        TypedArtifactAnnots::Packed
        | TypedArtifactAnnots::PartialImplementation
        | TypedArtifactAnnots::PartialInterface => false,
    }
}

pub fn typed_artifact_has_type_errors(artifact: &TypedArtifact<'_>) -> bool {
    // Mirrors compiler/gentype/GenTypeMain.ml:11-14 for the in-memory path.
    matches!(
        artifact.annots,
        TypedArtifactAnnots::PartialImplementation | TypedArtifactAnnots::PartialInterface
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

pub fn translate_typed_artifact(
    config: &crate::gentype::config::T,
    output_file_relative: &str,
    resolver: &crate::gentype::module_resolver::Resolver,
    artifact: &TypedArtifact<'_>,
) -> crate::gentype::translation::T {
    // Mirrors compiler/gentype/GenTypeMain.ml:53-70 for in-memory artifacts.
    let type_env = crate::gentype::type_env::root_for_current_module_names(
        current_module_names_for_typed_artifact(artifact),
    );
    let translations = match artifact.annots {
        TypedArtifactAnnots::Implementation(structure) => {
            crate::gentype::translate_structure::translate_structure(
                artifact.ctx,
                artifact.arena,
                config,
                output_file_relative,
                resolver,
                &type_env,
                structure,
            )
        }
        TypedArtifactAnnots::Interface(signature) => {
            crate::gentype::translate_signature::translate_signature(
                artifact.ctx,
                artifact.arena,
                config,
                output_file_relative,
                resolver,
                &type_env,
                signature,
            )
        }
        TypedArtifactAnnots::Packed
        | TypedArtifactAnnots::PartialImplementation
        | TypedArtifactAnnots::PartialInterface => {
            vec![]
        }
    };
    crate::gentype::translation::add_type_declarations_from_module_equations(
        &type_env,
        crate::gentype::translation::combine(&translations),
    )
}

fn current_module_names_for_typed_artifact(artifact: &TypedArtifact<'_>) -> Vec<String> {
    // The OCaml GenType entry point reads CMT/CMTI files selected by
    // compiler/gentype/Paths.ml:61-86. Rust's in-process hook receives the
    // typedtree before that file boundary, so keep both the compiler module
    // name from compiler/core/js_implementation.ml:51/142 and the GenType
    // file name from compiler/gentype/GenTypeMain.ml:141 available for
    // current-unit path stripping.
    let mut names = vec![crate::gentype::module_name::to_string(
        &artifact.compiler_module_name,
    )];
    let file_name = crate::gentype::module_name::to_string(&artifact.file_name);
    if !file_name.is_empty() && !names.contains(&file_name) {
        names.push(file_name);
    }
    if let Some(source_file) = artifact.source_file {
        if let Some(stem) = std::path::Path::new(source_file)
            .file_stem()
            .and_then(|stem| stem.to_str())
        {
            let mut chars = stem.chars();
            let source_module_name = match chars.next() {
                None => String::new(),
                Some(first) => first.to_uppercase().collect::<String>() + chars.as_str(),
            };
            if !source_module_name.is_empty() && !names.contains(&source_module_name) {
                names.push(source_module_name);
            }
        }
    }
    names
}

pub fn input_cmt_translate_type_declarations_from_cmt(
    config: &crate::gentype::config::T,
    output_file_relative: &str,
    resolver: &crate::gentype::module_resolver::Resolver,
    input_cmt: &InputCmt<'_>,
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
                input_cmt.ctx,
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
                input_cmt.ctx,
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

pub fn typed_artifact_translate_type_declarations(
    config: &crate::gentype::config::T,
    output_file_relative: &str,
    resolver: &crate::gentype::module_resolver::Resolver,
    artifact: &TypedArtifact<'_>,
) -> crate::gentype::translation::T {
    // Mirrors compiler/gentype/GenTypeMain.ml:26-52 for Rust's in-process
    // typedtree path. OCaml reopens the imported CMT at EmitJs.ml:437-453;
    // Rust already has the typed artifact here, so cache the same declaration
    // translation under the CMT path before EmitJs asks for it recursively.
    let type_env = crate::gentype::type_env::root();
    let translations = match artifact.annots {
        TypedArtifactAnnots::Implementation(structure) => {
            let mut structure = structure.clone();
            structure
                .str_items
                .retain(|item| structure_item_is_declaration(item));
            crate::gentype::translate_structure::translate_structure(
                artifact.ctx,
                artifact.arena,
                config,
                output_file_relative,
                resolver,
                &type_env,
                &structure,
            )
        }
        TypedArtifactAnnots::Interface(signature) => {
            let mut signature = signature.clone();
            signature
                .sig_items
                .retain(|item| signature_item_is_declaration(item));
            crate::gentype::translate_signature::translate_signature(
                artifact.ctx,
                artifact.arena,
                config,
                output_file_relative,
                resolver,
                &type_env,
                &signature,
            )
        }
        TypedArtifactAnnots::Packed
        | TypedArtifactAnnots::PartialImplementation
        | TypedArtifactAnnots::PartialInterface => {
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
    if let Some(type_declarations) = lookup_in_process_type_declarations(cmt_file) {
        return crate::gentype::translation::T {
            import_types: vec![],
            code_items: vec![],
            type_declarations,
        };
    }
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
    input_cmt: &InputCmt<'_>,
) -> crate::gentype::translation::T {
    // Mirrors compiler/gentype/GenTypeMain.ml:53-70.
    let type_env = crate::gentype::type_env::root();
    let translations = match &input_cmt.cmt_annots {
        BinaryAnnots::Implementation(structure) => {
            crate::gentype::translate_structure::translate_structure(
                input_cmt.ctx,
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
                input_cmt.ctx,
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
    get_cmt_file: &crate::gentype::emit_js::GetCmtFile<'_>,
    source_file: &str,
    translation: &crate::gentype::translation::T,
) -> std::io::Result<()> {
    // Mirrors compiler/gentype/GenTypeMain.ml:72-83.
    let code_text = crate::gentype::emit_js::emit_translation_as_string(
        config,
        file_name,
        get_cmt_file,
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

pub fn read_cmt(cmt_file: &str) -> InputCmt<'static> {
    // Mirrors compiler/gentype/GenTypeMain.ml:85-91. Actual CMT decoding is
    // wired later; this staged port preserves the stale-artifact error boundary.
    match std::fs::read(cmt_file) {
        Ok(data) if data.starts_with(b"Caml1999T022") => {
            crate::gentype::log_::item(&format!("Error loading {cmt_file}\n\n"));
            crate::gentype::log_::item(
                "Standalone CMT decoding is not available in the Rust GenType path yet.\n",
            );
            panic!("Fatal error: exception Cmt_format.Error(_)")
        }
        Ok(data) if data.starts_with(b"Caml1999I024") => {
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

pub fn read_input_cmt(is_interface: bool, cmt_file: &str) -> (InputCmt<'static>, bool) {
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
                &crate::gentype::paths::get_cmt_file,
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

pub fn process_typed_artifact(
    config: &crate::gentype::config::T,
    artifact: TypedArtifact<'_>,
) -> std::io::Result<()> {
    // Mirrors compiler/gentype/GenTypeMain.ml:136-175, but starts from the
    // typedtree already produced in-process instead of re-reading a .cmt/.cmti.
    // The OCaml call site is compiler/core/js_implementation.ml:33-34 and
    // compiler/core/js_implementation.ml:170 after Typemod saved the CMT at
    // compiler/ml/typemod.ml:1763-1764 or compiler/ml/typemod.ml:1785-1787.
    let mut config = config.clone();
    if crate::gentype::debug::basic.load(std::sync::atomic::Ordering::Relaxed) {
        crate::gentype::log_::item(&format!(
            "Typed artifact {}\n",
            crate::gentype::module_name::to_string(&artifact.file_name)
        ));
    }
    let source_file = artifact
        .source_file
        .map(|s| s.to_string())
        .unwrap_or_else(|| {
            format!(
                "{}{}",
                crate::gentype::module_name::to_string(&artifact.file_name),
                match artifact.is_interface {
                    true => ".resi",
                    false => ".res",
                }
            )
        });
    let output_file = crate::gentype::paths::get_output_file(&config, &source_file);
    let output_file_relative =
        crate::gentype::paths::get_output_file_relative(&config, &source_file);
    let resolver = crate::gentype::module_resolver::create_lazy_resolver(
        &config,
        &[".res".to_string(), ".shim.ts".to_string()],
        |fname| fname == "React.res" || fname == "ReasonReact.res",
    );
    let type_declaration_translation = typed_artifact_translate_type_declarations(
        &config,
        &output_file_relative,
        &resolver,
        &artifact,
    );
    if let Some(cmt_file) =
        cmt_file_for_typed_artifact(&config, &source_file, artifact.is_interface)
    {
        register_in_process_type_declarations(
            &cmt_file,
            type_declaration_translation.type_declarations,
        );
    }
    let has_gentype_annotations = typed_artifact_check_annotations(
        &|arena, _loc, attributes| {
            crate::gentype::annotation::get_attribute_payload(
                arena,
                crate::gentype::annotation::tag_is_one_of_the_gentype_annotations,
                attributes,
            )
            .is_some()
        },
        &artifact,
    );
    if has_gentype_annotations {
        let translation =
            translate_typed_artifact(&config, &output_file_relative, &resolver, &artifact);
        let project_root = config.project_root.clone();
        let get_cmt_file = |cmt: &str| get_cmt_file_for_typed_artifact_import(&project_root, cmt);
        emit_translation(
            &mut config,
            &artifact.file_name,
            &output_file,
            &output_file_relative,
            &resolver,
            &get_cmt_file,
            &source_file,
            &translation,
        )?;
    } else if typed_artifact_has_type_errors(&artifact) {
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
    Ok(())
}

fn cmt_file_for_typed_artifact(
    config: &crate::gentype::config::T,
    source_file: &str,
    is_interface: bool,
) -> Option<String> {
    // OCaml passes outputprefix.cmt/cmt_file through compiler/gentype/Paths.ml:61-86
    // before GenTypeMain.ml:136-175. Rust starts from the source path, so rebuild
    // the CMT-shaped path used by ImportPath.to_cmt at compiler/gentype/ImportPath.ml:24-32.
    let source_path = Path::new(source_file);
    let parent = source_path.parent().unwrap_or_else(|| Path::new(""));
    let stem = source_path.file_stem()?.to_str()?;
    let namespace = config
        .namespace
        .as_ref()
        .map(|namespace| format!("-{namespace}"))
        .unwrap_or_default();
    let extension = match is_interface {
        true => "cmti",
        false => "cmt",
    };
    Some(
        parent
            .join(format!("{stem}{namespace}.{extension}"))
            .to_string_lossy()
            .to_string(),
    )
}
