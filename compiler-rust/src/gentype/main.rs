// Port of compiler/gentype/GenTypeMain.ml:1-175.

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

type InProcessTypeDeclarations = crate::gentype::code_item::TypeDeclarations;

/// The GenType type declarations of one typed artifact, encoded. Every
/// compiled module registers its declarations, but only modules importing its
/// types from a GenType-annotated module read them, and the encoded form is a
/// small fraction of the decoded one. It is stored as is with the module's
/// interface, so restoring a stored module decodes nothing either.
pub type EncodedTypeDeclarations = crate::binser::Encoded<InProcessTypeDeclarations>;

/// Type declarations of the typed artifacts processed in this process, by
/// normalized `.cmt`/`.cmti` path (OCaml GenType reads them from those files,
/// which in-process builds do not write), and the paths each module owns.
#[derive(Default)]
struct InProcessTypeDeclarationsTables {
    by_cmt: HashMap<String, EncodedTypeDeclarations>,
    by_module: HashMap<String, Vec<String>>,
}

type InProcessTypeDeclarationsCache = Mutex<InProcessTypeDeclarationsTables>;

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
    /// Only register the artifact's type declarations, for modules that
    /// import its types; generate no output (a module compiled only for its
    /// interface).
    pub declarations_only: bool,
}

fn in_process_type_declarations_cache() -> &'static InProcessTypeDeclarationsCache {
    static CACHE: OnceLock<InProcessTypeDeclarationsCache> = OnceLock::new();
    CACHE.get_or_init(|| Mutex::new(InProcessTypeDeclarationsTables::default()))
}

fn normalize_cmt_path_lexically(path: PathBuf) -> PathBuf {
    path.components()
        .filter(|component| !matches!(component, std::path::Component::CurDir))
        .fold(PathBuf::new(), |mut normalized, component| {
            normalized.push(component.as_os_str());
            normalized
        })
}

/// `std::fs::canonicalize(path).ok()`, resolving the parent directory once
/// per thread. For an existing file that is not a symlink, the canonical path
/// is the canonical parent joined with the file name.
fn canonicalize_with_cached_parent(path: &Path) -> Option<PathBuf> {
    thread_local! {
        static CANONICAL_DIRS: std::cell::RefCell<HashMap<PathBuf, PathBuf>> =
            std::cell::RefCell::new(HashMap::new());
    }
    let (Some(parent), Some(name)) = (path.parent(), path.file_name()) else {
        return std::fs::canonicalize(path).ok();
    };
    // The key is the canonical directory plus the file name, whether or not
    // the file exists (in-process builds write no .cmt): registration and
    // lookup both go through here, so it only has to be stable.
    if let Some(dir) = CANONICAL_DIRS.with(|dirs| dirs.borrow().get(parent).cloned()) {
        return Some(dir.join(name));
    }
    let dir = std::fs::canonicalize(parent).ok()?;
    CANONICAL_DIRS.with(|dirs| {
        dirs.borrow_mut().insert(parent.to_path_buf(), dir.clone());
    });
    Some(dir.join(name))
}

fn normalize_cmt_cache_key(cmt_file: &str) -> String {
    // The key is requested several times per artifact; remember the keys that
    // resolved through an existing directory (a missing directory may appear
    // later, so its lexical fallback is not remembered).
    thread_local! {
        static RESOLVED_KEYS: std::cell::RefCell<HashMap<String, String>> =
            std::cell::RefCell::new(HashMap::new());
    }
    if let Some(key) = RESOLVED_KEYS.with(|keys| keys.borrow().get(cmt_file).cloned()) {
        return key;
    }
    let path = PathBuf::from(cmt_file);
    let path = if path.is_relative() {
        crate::process_cwd::current_dir()
            .unwrap_or_else(|_| Path::new(""))
            .join(path)
    } else {
        path
    };
    match canonicalize_with_cached_parent(&path) {
        Some(resolved) => {
            let key = resolved.to_string_lossy().to_string();
            RESOLVED_KEYS.with(|keys| {
                keys.borrow_mut().insert(cmt_file.to_string(), key.clone());
            });
            key
        }
        None => normalize_cmt_path_lexically(path)
            .to_string_lossy()
            .to_string(),
    }
}

fn has_in_process_type_declarations(cmt_file: &Path) -> bool {
    let Some(cmt_file) = cmt_file.to_str() else {
        return false;
    };
    // Resolve the key (a filesystem canonicalize) before taking the shared
    // lock, so parallel GenType workers do not serialize on the syscall.
    let key = normalize_cmt_cache_key(cmt_file);
    in_process_type_declarations_cache()
        .lock()
        .map(|cache| cache.by_cmt.contains_key(&key))
        .unwrap_or(false)
}

fn lookup_in_process_type_declarations(
    cmt_file: &str,
) -> Option<std::sync::Arc<InProcessTypeDeclarations>> {
    let key = normalize_cmt_cache_key(cmt_file);
    in_process_type_declarations_cache()
        .lock()
        .ok()
        .and_then(|cache| cache.by_cmt.get(&key).cloned())
        .and_then(|encoded| encoded.try_decode())
        .map(std::sync::Arc::new)
}

fn register_in_process_type_declarations(
    module_name: &str,
    cmt_file: &str,
    type_declarations: InProcessTypeDeclarations,
) {
    let key = normalize_cmt_cache_key(cmt_file);
    let type_declarations = EncodedTypeDeclarations::encode(&type_declarations);
    let replaced = in_process_type_declarations_cache()
        .lock()
        .ok()
        .and_then(|mut cache| {
            let keys = cache.by_module.entry(module_name.to_string()).or_default();
            if !keys.contains(&key) {
                keys.push(key.clone());
            }
            cache.by_cmt.insert(key, type_declarations)
        });
    drop(replaced);
}

/// The type declarations `module_name`'s typed artifacts registered, by
/// normalized `.cmt`/`.cmti` path, for an incremental build to store with the
/// module's interface: a later build that does not compile the module
/// restores them with [`restore_type_declarations`], so modules that import
/// its types translate them as when it was compiled.
pub fn type_declarations_of_module(module_name: &str) -> Vec<(String, EncodedTypeDeclarations)> {
    let Ok(cache) = in_process_type_declarations_cache().lock() else {
        return Vec::new();
    };
    let Some(keys) = cache.by_module.get(module_name) else {
        return Vec::new();
    };
    let mut entries: Vec<_> = keys
        .iter()
        .filter_map(|key| Some((key.clone(), cache.by_cmt.get(key)?.clone())))
        .collect();
    entries.sort_by(|(a, _), (b, _)| a.cmp(b));
    entries
}

/// Register type declarations stored by [`type_declarations_of_module`].
pub fn restore_type_declarations(
    module_name: &str,
    entries: Vec<(String, EncodedTypeDeclarations)>,
) {
    if entries.is_empty() {
        return;
    }
    let Ok(mut cache) = in_process_type_declarations_cache().lock() else {
        return;
    };
    let keys = entries.iter().map(|(key, _)| key.clone()).collect();
    cache.by_module.insert(module_name.to_string(), keys);
    for (key, declarations) in entries {
        cache.by_cmt.insert(key, declarations);
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
        // In-process builds write no .cmt; ask the registry before the disk.
        has_in_process_type_declarations(path) || path.exists()
    })
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
        crate::gentype::translation::combine(translations),
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
        TypedArtifactAnnots::Implementation(structure) => structure
            .str_items
            .iter()
            .filter(|item| structure_item_is_declaration(item))
            .map(|item| {
                crate::gentype::translate_structure::translate_structure_item(
                    artifact.ctx,
                    artifact.arena,
                    config,
                    output_file_relative,
                    resolver,
                    &type_env,
                    item,
                )
            })
            .collect(),
        TypedArtifactAnnots::Interface(signature) => signature
            .sig_items
            .iter()
            .filter(|item| signature_item_is_declaration(item))
            .map(|item| {
                crate::gentype::translate_signature::translate_signature_item(
                    artifact.ctx,
                    artifact.arena,
                    config,
                    output_file_relative,
                    resolver,
                    &type_env,
                    item,
                )
            })
            .collect(),
        TypedArtifactAnnots::Packed
        | TypedArtifactAnnots::PartialImplementation
        | TypedArtifactAnnots::PartialInterface => {
            vec![]
        }
    };
    crate::gentype::translation::add_type_declarations_from_module_equations(
        &type_env,
        crate::gentype::translation::combine(translations),
    )
}

pub fn input_cmt_translate_type_declarations(
    _config: &mut crate::gentype::config::T,
    _output_file_relative: &str,
    _resolver: &crate::gentype::module_resolver::Resolver,
    cmt_file: &str,
) -> std::sync::Arc<InProcessTypeDeclarations> {
    // This is the Rust callback boundary used by emit_js.rs for
    // compiler/gentype/EmitJs.ml:449-453.
    match lookup_in_process_type_declarations(cmt_file) {
        Some(type_declarations) => type_declarations,
        None => read_cmt(cmt_file),
    }
}

pub fn emit_translation(
    locs: &dyn crate::types::DeclLocs,
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
        locs,
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
    // Source-derived text (names, string literals, doc comments) holds one
    // `char` per source byte; OCaml writes those bytes unchanged, so turn
    // them back into the UTF-8 they spell.
    let code_text = crate::source_text::decode_internal_utf8_runs(&code_text);
    let file_contents = format!(
        "{}\n{}\n",
        crate::gentype::emit_type::file_header(source_file),
        code_text
    );
    crate::gentype::generated_files::write_file_if_required(output_file, &file_contents)
}

fn read_cmt(cmt_file: &str) -> ! {
    // Mirrors the error boundary of compiler/gentype/GenTypeMain.ml:85-91.
    // Rust has no standalone CMT decoder: imported declarations come from the
    // in-process registry, so a .cmt that is only on disk is a fatal error.
    match std::fs::read(cmt_file) {
        Ok(data) if data.starts_with(b"Caml1999T039") => {
            crate::gentype::log_::item(&format!("Error loading {cmt_file}\n\n"));
            crate::gentype::log_::item(
                "Standalone CMT decoding is not available in the Rust GenType path yet.\n",
            );
            panic!("Fatal error: exception Cmt_format.Error(_)")
        }
        Ok(data) if data.starts_with(b"Caml1999I035") => {
            panic!("Fatal error: exception Cmt_format.Error(_)")
        }
        _ => {
            crate::gentype::log_::item(&format!("Error loading {cmt_file}\n\n"));
            crate::gentype::log_::item(
                "It looks like you might have stale compilation artifacts.\n",
            );
            crate::gentype::log_::item("Try to clean and rebuild.\n\n");
            panic!(
                "Fatal error: exception File \"compiler/gentype/gentype_main.ml\", line 89, characters 4-10: Assertion failed"
            )
        }
    }
}

pub fn process_typed_artifact(
    config: &crate::gentype::config::T,
    shared_resolver: Option<&crate::gentype::module_resolver::Resolver>,
    artifact: TypedArtifact<'_>,
) -> std::io::Result<()> {
    // Mirrors compiler/gentype/GenTypeMain.ml:136-175, but starts from the
    // typedtree already produced in-process instead of re-reading a .cmt/.cmti.
    // The OCaml call site is compiler/core/js_implementation.ml:33-34 and
    // compiler/core/js_implementation.ml:170 after Typemod saved the CMT at
    // compiler/ml/typemod.ml:1763-1764 or compiler/ml/typemod.ml:1785-1787.
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
    let output_file = crate::gentype::paths::get_output_file(config, &source_file);
    let output_file_relative =
        crate::gentype::paths::get_output_file_relative(config, &source_file);
    let local_resolver = shared_resolver.is_none().then(|| {
        crate::gentype::module_resolver::create_lazy_resolver(
            config,
            &[".res".to_string(), ".shim.ts".to_string()],
            |fname| fname == "React.res" || fname == "ReasonReact.res",
        )
    });
    let resolver = shared_resolver
        .or(local_resolver.as_ref())
        .expect("GenType resolver must be available");
    let type_declaration_translation = typed_artifact_translate_type_declarations(
        config,
        &output_file_relative,
        resolver,
        &artifact,
    );
    if let Some(cmt_file) = cmt_file_for_typed_artifact(config, &source_file, artifact.is_interface)
    {
        register_in_process_type_declarations(
            &artifact.compiler_module_name,
            &cmt_file,
            crate::gentype::code_item::TypeDeclarations::portable(
                type_declaration_translation.type_declarations,
                artifact.ctx,
            ),
        );
    }
    if artifact.declarations_only {
        return Ok(());
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
            translate_typed_artifact(config, &output_file_relative, resolver, &artifact);
        let project_root = config.project_root.clone();
        let get_cmt_file = |cmt: &str| get_cmt_file_for_typed_artifact_import(&project_root, cmt);
        // Only emitting mutates the config; modules without GenType
        // annotations skip the copy.
        let mut config = config.clone();
        emit_translation(
            artifact.ctx,
            &mut config,
            &artifact.file_name,
            &output_file,
            &output_file_relative,
            resolver,
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
