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

/// One typed artifact's GenType type declarations, or the report of the
/// exception their translation raised. OCaml translates them only when an
/// importing module's output needs them (EmitJs.ml:437-453), so an invalid
/// string escape (Ast_payload.ml:39-51) in them fails that importer's
/// compile, not the declaring module's.
/// The warnings their translation prints go with them: an importer that
/// reads them prints them (they are not printed when nothing reads them).
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct InProcessTypeDeclarations {
    notes: Vec<String>,
    result: Result<crate::gentype::code_item::TypeDeclarations, String>,
}

/// What GenType does for a compile. OCaml runs GenType after the unit's
/// JavaScript is written (js_implementation.ml:164-171), so the compile
/// computes this where it has the typed tree and applies it after writing
/// the JavaScript; a compile that fails before then never applies it.
#[derive(Debug, Clone)]
pub struct Outcome {
    /// The genType warnings the run prints (Log_.ml:99-104), in order.
    pub notes: Vec<String>,
    /// The generated file's action, or the report of the exception GenType
    /// raises after printing `notes`, which fails the compile (an invalid
    /// string escape in an annotation payload, Ast_payload.ml:39-51).
    pub result: Result<Option<Output>, String>,
    /// A note was rendered from a location-free parse: the compile must be
    /// retried with locations, as for its warnings.
    pub needs_locations: bool,
}

impl Default for Outcome {
    /// Nothing to print or write.
    fn default() -> Self {
        Outcome {
            notes: Vec::new(),
            result: Ok(None),
            needs_locations: false,
        }
    }
}

/// Whether notes rendered from `artifact`'s parse need it to have locations.
fn needs_locations(artifact: &TypedArtifact<'_>, noted: bool) -> bool {
    noted && !artifact.arena.stores_locations()
}

impl Outcome {
    fn raised(report: String) -> Self {
        Outcome {
            notes: Vec::new(),
            result: Err(report),
            needs_locations: false,
        }
    }

    /// `result`, after the warnings `notes` collected.
    fn after(notes: &crate::gentype::log_::Notes, result: Result<Output, String>) -> Self {
        Outcome {
            notes: notes.take(),
            result: result.map(Some),
            needs_locations: false,
        }
    }

    /// Write the file. Returns the text GenType prints (its notes), then
    /// `Err(report)` when it raised after printing them. The caller prints
    /// the text where the compile's output goes.
    pub fn apply(self) -> std::io::Result<(String, Result<(), String>)> {
        let printed = self.notes.concat();
        Ok(match self.result {
            Ok(Some(output)) => {
                // File actions happen after the driver's GenType scope.
                crate::timing::measure(crate::timing::Phase::Gentype, || {
                    crate::timing::measure(crate::timing::Phase::GentypeFiles, || output.apply())
                })?;
                (printed, Ok(()))
            }
            Ok(None) => (printed, Ok(())),
            Err(report) => (printed, Err(report)),
        })
    }
}

/// Renders an invalid string escape GenType read in the artifact's file as
/// the compiler error bsc prints for it.
pub type RenderEscape<'a> = dyn Fn(crate::gentype::annotation::InvalidEscape) -> String + 'a;

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
    skipped: crate::fast_hash::AHashSet<String>,
    #[cfg(debug_assertions)]
    skipped_requests: Vec<(String, String)>,
}

type InProcessTypeDeclarationsCache = Mutex<InProcessTypeDeclarationsTables>;

/// The typed tree of an artifact (`Cmt_format.binary_annots`).
pub enum TypedArtifactAnnots<'a> {
    /// A `.res` file's typed structure.
    Implementation(&'a Structure),
    /// A `.resi` file's typed signature.
    Interface(&'a TypedSignature),
    /// A packed module, which gentype does not translate.
    Packed,
    /// The partial structure of a `.res` file with type errors.
    PartialImplementation,
    /// The partial signature of a `.resi` file with type errors.
    PartialInterface,
}

/// A type-checked module, as the compiler hands it to gentype.
pub struct TypedArtifact<'a> {
    /// The module's typed tree.
    pub annots: TypedArtifactAnnots<'a>,
    /// The parse arena the typed tree's attributes and locations point into.
    pub arena: &'a ParseArena,
    /// Node storage of the typed tree in `annots`.
    pub ta: &'a crate::types::typedtree::TypedArena,
    /// The type state the typed tree's types live in.
    pub ctx: &'a TypeContext,
    /// The source file's path, when known.
    pub source_file: Option<&'a str>,
    /// The module's name as the compiler knows it.
    pub compiler_module_name: crate::gentype::module_name::T,
    /// The module name gentype derives from the source file's path.
    pub file_name: crate::gentype::module_name::T,
    /// Whether the artifact is an interface.
    pub is_interface: bool,
    /// Only register the artifact's type declarations, for modules that
    /// import its types; generate no output (a module compiled only for its
    /// interface).
    pub declarations_only: bool,
    /// False only when whole-build reachability proves no output can read this artifact.
    pub declarations_needed: bool,
    /// Renders an invalid string escape read in the artifact's file.
    pub render_escape: &'a RenderEscape<'a>,
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
        .map(|cache| cache.by_cmt.contains_key(&key) || skipped_module(&cache, cmt_file).is_some())
        .unwrap_or(false)
}

fn lookup_in_process_type_declarations(cmt_file: &str) -> Option<InProcessTypeDeclarations> {
    let key = normalize_cmt_cache_key(cmt_file);
    in_process_type_declarations_cache()
        .lock()
        .ok()
        .and_then(|cache| cache.by_cmt.get(&key).cloned())
        .and_then(|encoded| encoded.try_decode())
}

fn register_in_process_type_declarations(
    module_name: &str,
    cmt_file: &str,
    type_declarations: InProcessTypeDeclarations,
) {
    let key = normalize_cmt_cache_key(cmt_file);
    let type_declarations = crate::timing::measure(crate::timing::Phase::GentypeEncoding, || {
        EncodedTypeDeclarations::encode(&type_declarations)
    });
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

/// Replace the skipped-module set once per build plan. Keep names only:
/// paths are inspected only when a declaration lookup misses its cache.
pub fn set_skipped_modules(modules: impl Iterator<Item = String>) {
    let skipped: crate::fast_hash::AHashSet<_> = modules.collect();
    let mut cache = in_process_type_declarations_cache().lock().unwrap();
    // Normally nothing was cached for a skipped module. Watch updates can
    // remove modules from the needed closure; discard those old entries.
    if !cache.by_module.is_empty() {
        for module in &skipped {
            if let Some(keys) = cache.by_module.remove(module) {
                for key in keys {
                    cache.by_cmt.remove(&key);
                }
            }
        }
    }
    cache.skipped = skipped;
}

fn skipped_module(cache: &InProcessTypeDeclarationsTables, cmt_file: &str) -> Option<String> {
    let stem = Path::new(cmt_file).file_stem()?.to_str()?;
    let mut module = stem.to_string();
    if let Some(first) = module.get_mut(..1) {
        first.make_ascii_uppercase();
    }
    cache.skipped.contains(&module).then_some(module)
}

/// Additional debug-build audit; a skipped lookup is an error in release too.
pub fn verify_skipped_declarations() -> Result<(), String> {
    #[cfg(debug_assertions)]
    if std::env::var_os("RESCRIPT_VERIFY_GENTYPE_CLOSURE").is_some() {
        let cache = in_process_type_declarations_cache().lock().unwrap();
        if !cache.skipped_requests.is_empty() {
            return Err(format!(
                "Internal genType closure error: skipped requests {:?}",
                cache.skipped_requests
            ));
        }
        assert!(
            cache
                .skipped
                .iter()
                .all(|name| !cache.by_module.contains_key(name))
        );
    }
    Ok(())
}

fn skipped_declaration_error(cmt_file: &str, importer: &str) -> Option<String> {
    let cache = in_process_type_declarations_cache().lock().unwrap();
    let module = skipped_module(&cache, cmt_file)?;
    #[cfg(debug_assertions)]
    {
        drop(cache);
        in_process_type_declarations_cache()
            .lock()
            .unwrap()
            .skipped_requests
            .push((importer.to_string(), module.clone()));
    }
    Some(format!(
        "Internal genType dependency-closure error: module {importer} requested skipped declarations of module {module}"
    ))
}

/// Whether this process has translated declarations for a module (including
/// an empty translation). Does not decode the cached result.
pub fn has_type_declarations_for_module(module_name: &str) -> bool {
    in_process_type_declarations_cache()
        .lock()
        .unwrap()
        .by_module
        .get(module_name)
        .is_some_and(|keys| !keys.is_empty())
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
    // using the path order in compiler/gentype/paths.ml `get_cmt_file`.
    // OCaml's bsc runs in the package's artifact directory, where
    // Import_path.to_cmt names the file; Rewatch's in-process Rust path keeps
    // those typed artifacts in memory under the same paths, below
    // Config.project_root (compiler/gentype/GenTypeConfig.ml:124-131).
    let artifact_dir = Path::new(project_root).join("lib").join("rescript");
    crate::gentype::paths::get_cmt_file_from_cwd_with_exists(&artifact_dir, cmt, |path| {
        // In-process builds write no .cmt; ask the registry before the disk.
        has_in_process_type_declarations(path) || path.exists()
    })
}

/// `GenTypeMain.signature_check_annotations` / `structure_check_annotations`:
/// whether any item of the artifact is accepted by `check_annotation`.
pub fn typed_artifact_check_annotations(
    check_annotation: &impl Fn(
        &ParseArena,
        LocIdx,
        &Attributes,
    ) -> crate::gentype::annotation::Read<bool>,
    artifact: &TypedArtifact<'_>,
) -> crate::gentype::annotation::Read<bool> {
    crate::timing::measure(crate::timing::Phase::GentypeAnnotations, || {
        // Mirrors compiler/gentype/GenTypeMain.ml:3-10 for in-memory typed
        // artifacts, using the same Annotation traversal that CMT decoding feeds.
        match artifact.annots {
            TypedArtifactAnnots::Implementation(structure) => {
                crate::gentype::annotation::structure_check_annotation(
                    artifact.arena,
                    artifact.ta,
                    &|loc, attributes| check_annotation(artifact.arena, loc, attributes),
                    structure,
                )
            }
            TypedArtifactAnnots::Interface(signature) => {
                crate::gentype::annotation::signature_check_annotation(
                    artifact.arena,
                    artifact.ta,
                    &|loc, attributes| check_annotation(artifact.arena, loc, attributes),
                    signature,
                )
            }
            TypedArtifactAnnots::Packed
            | TypedArtifactAnnots::PartialImplementation
            | TypedArtifactAnnots::PartialInterface => Ok(false),
        }
    })
}

/// Whether the artifact is the partial tree of a module with type errors.
pub fn typed_artifact_has_type_errors(artifact: &TypedArtifact<'_>) -> bool {
    // Mirrors compiler/gentype/GenTypeMain.ml:11-14 for the in-memory path.
    matches!(
        artifact.annots,
        TypedArtifactAnnots::PartialImplementation | TypedArtifactAnnots::PartialInterface
    )
}

impl TypedArtifact<'_> {
    /// The artifact's trees as a translation reads them, with imports
    /// resolved for `output_file_relative`.
    fn translation_input<'s>(
        &'s self,
        output_file_relative: &'s str,
        resolver: &'s crate::gentype::module_resolver::Resolver,
    ) -> crate::gentype::translation::Input<'s> {
        crate::gentype::translation::Input {
            ta: self.ta,
            ctx: self.ctx,
            arena: self.arena,
            output_file_relative,
            resolver,
        }
    }
}

/// Whether a structure item declares types or modules, whose type
/// declarations importers may need.
pub fn structure_item_is_declaration(struct_item: &StructureItem) -> bool {
    // Mirrors compiler/gentype/GenTypeMain.ml:16-20.
    matches!(
        &struct_item.str_desc,
        StructureItemDesc::Tstr_type(_, _)
            | StructureItemDesc::Tstr_modtype(_)
            | StructureItemDesc::Tstr_module(_)
    )
}

/// Whether a signature item declares types or module types, whose type
/// declarations importers may need.
pub fn signature_item_is_declaration(signature_item: &TypedSignatureItem) -> bool {
    // Mirrors compiler/gentype/GenTypeMain.ml:21-24.
    matches!(
        &signature_item.sig_desc,
        TypedSignatureItemDesc::Tsig_type(_, _) | TypedSignatureItemDesc::Tsig_modtype(_)
    )
}

/// `GenTypeMain.translateCMT`: translate the artifact for the generated file
/// at `output_file_relative`.
pub fn translate_typed_artifact(
    config: &crate::gentype::config::T,
    output_file_relative: &str,
    resolver: &crate::gentype::module_resolver::Resolver,
    notes: &std::rc::Rc<crate::gentype::log_::Notes>,
    artifact: &TypedArtifact<'_>,
) -> crate::gentype::annotation::Read<crate::gentype::translation::T> {
    // Mirrors compiler/gentype/GenTypeMain.ml:53-70 for in-memory artifacts.
    let input = artifact.translation_input(output_file_relative, resolver);
    let type_env = crate::gentype::type_env::root_for_current_module_names(
        current_module_names_for_typed_artifact(artifact),
    );
    type_env.borrow_mut().notes = notes.clone();
    let translations = match artifact.annots {
        TypedArtifactAnnots::Implementation(structure) => {
            crate::gentype::translate_structure::translate_structure(
                input, config, &type_env, structure,
            )?
        }
        TypedArtifactAnnots::Interface(signature) => {
            crate::gentype::translate_signature::translate_signature(
                input,
                config,
                &type_env,
                artifact.ta.signature_items(signature.sig_items),
            )?
        }
        TypedArtifactAnnots::Packed
        | TypedArtifactAnnots::PartialImplementation
        | TypedArtifactAnnots::PartialInterface => {
            vec![]
        }
    };
    Ok(
        crate::gentype::translation::add_type_declarations_from_module_equations(
            &type_env,
            crate::gentype::translation::combine(translations),
        ),
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

/// Translate only the type declarations of the artifact, as importers of its
/// types need them.
pub fn typed_artifact_translate_type_declarations(
    config: &crate::gentype::config::T,
    output_file_relative: &str,
    resolver: &crate::gentype::module_resolver::Resolver,
    notes: &std::rc::Rc<crate::gentype::log_::Notes>,
    artifact: &TypedArtifact<'_>,
) -> crate::gentype::annotation::Read<crate::gentype::translation::T> {
    // Mirrors compiler/gentype/GenTypeMain.ml:26-52 for Rust's in-process
    // typedtree path. OCaml reopens the imported CMT at EmitJs.ml:437-453;
    // Rust already has the typed artifact here, so cache the same declaration
    // translation under the CMT path before EmitJs asks for it recursively.
    let input = artifact.translation_input(output_file_relative, resolver);
    let type_env = crate::gentype::type_env::root();
    type_env.borrow_mut().notes = notes.clone();
    let translations = match artifact.annots {
        TypedArtifactAnnots::Implementation(structure) => artifact
            .ta
            .structure_items(structure.str_items)
            .iter()
            .filter(|item| structure_item_is_declaration(item))
            .map(|item| {
                crate::gentype::translate_structure::translate_structure_item(
                    input, config, &type_env, item,
                )
            })
            .collect::<crate::gentype::annotation::Read<_>>()?,
        TypedArtifactAnnots::Interface(signature) => artifact
            .ta
            .signature_items(signature.sig_items)
            .iter()
            .filter(|item| signature_item_is_declaration(item))
            .map(|item| {
                crate::gentype::translate_signature::translate_signature_item(
                    input, config, &type_env, item,
                )
            })
            .collect::<crate::gentype::annotation::Read<_>>()?,
        TypedArtifactAnnots::Packed
        | TypedArtifactAnnots::PartialImplementation
        | TypedArtifactAnnots::PartialInterface => {
            vec![]
        }
    };
    Ok(
        crate::gentype::translation::add_type_declarations_from_module_equations(
            &type_env,
            crate::gentype::translation::combine(translations),
        ),
    )
}

/// The type declarations translated from the `.cmt` file `cmt_file`, from
/// the registry of artifacts this process has translated; reading a `.cmt`
/// from disk is a fatal error.
pub fn input_cmt_translate_type_declarations(
    notes: &crate::gentype::log_::Notes,
    _config: &mut crate::gentype::config::T,
    _output_file_relative: &str,
    _resolver: &crate::gentype::module_resolver::Resolver,
    cmt_file: &str,
) -> Result<std::sync::Arc<crate::gentype::code_item::TypeDeclarations>, String> {
    // This is the Rust callback boundary used by emit_js.rs for
    // compiler/gentype/EmitJs.ml:449-453: the declarations are translated
    // here in OCaml, so the warnings their translation prints are printed,
    // and an exception it raised is raised, here.
    match lookup_in_process_type_declarations(cmt_file) {
        Some(InProcessTypeDeclarations {
            notes: translation_notes,
            result,
        }) => {
            notes.extend(translation_notes);
            result.map(std::sync::Arc::new)
        }
        None => match skipped_declaration_error(cmt_file, _output_file_relative) {
            Some(error) => Err(error),
            None => read_cmt(cmt_file),
        },
    }
}

/// The generated file's contents, or the report of the exception emitting
/// raised (an imported module's declarations, `InProcessTypeDeclarations`).
pub fn emit_translation_contents(
    locs: &dyn crate::types::DeclLocs,
    config: &mut crate::gentype::config::T,
    target: crate::gentype::emit_js::EmitTarget<'_>,
    source_file: &str,
    translation: &crate::gentype::translation::T,
) -> Result<String, String> {
    // Mirrors compiler/gentype/GenTypeMain.ml:72-83, up to the write.
    let code_text =
        crate::gentype::emit_js::emit_translation_as_string(target, locs, config, translation)?;
    let source_file = Path::new(source_file)
        .file_name()
        .and_then(|s| s.to_str())
        .unwrap_or(source_file);
    // Source-derived text (names, string literals, doc comments) holds one
    // `char` per source byte; OCaml writes those bytes unchanged, so turn
    // them back into the UTF-8 they spell.
    let code_text = crate::source_text::decode_internal_utf8_runs(&code_text);
    Ok(format!(
        "{}\n{}\n",
        crate::gentype::emit_type::file_header(source_file),
        code_text
    ))
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
        Ok(data) if data.starts_with(crate::cmi::cmi_format::CMI_MAGIC) => {
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

/// What GenType does with a typed artifact's generated file
/// (GenTypeMain.ml:165-175).
#[derive(Debug, Clone)]
pub enum Output {
    /// Write `contents` unless the file already has them.
    Write {
        /// The generated file's path.
        output_file: String,
        /// The generated file's contents.
        contents: String,
    },
    /// The artifact has type errors: log, keep the file.
    TypeError {
        /// The generated file's path.
        output_file: String,
    },
    /// No annotations and the build's directory inventory proves no file exists.
    Absent {
        /// The generated file's path, retained for the normal NoMatch debug log.
        output_file: String,
    },
    /// No annotations: log and remove the file.
    NoMatch {
        /// The generated file's path.
        output_file: String,
    },
}

impl Output {
    fn apply(self) -> std::io::Result<()> {
        match self {
            Output::Write {
                output_file,
                contents,
            } => crate::timing::measure(crate::timing::Phase::GentypeFileWrite, || {
                crate::gentype::generated_files::write_file_if_required(&output_file, &contents)
            }),
            Output::TypeError { output_file } => {
                crate::gentype::generated_files::log_file_action(
                    crate::gentype::generated_files::FileAction::TypeError,
                    &output_file,
                );
                Ok(())
            }
            Output::Absent { output_file } => {
                crate::gentype::generated_files::log_file_action(
                    crate::gentype::generated_files::FileAction::NoMatch,
                    &output_file,
                );
                Ok(())
            }
            Output::NoMatch { output_file } => {
                crate::timing::measure(crate::timing::Phase::GentypeFileNoMatch, || {
                    crate::gentype::generated_files::log_file_action(
                        crate::gentype::generated_files::FileAction::NoMatch,
                        &output_file,
                    );
                    if crate::gentype::generated_files::file_exists(&output_file) {
                        crate::gentype::generated_files::remove_file(&output_file)?;
                    }
                    Ok(())
                })
            }
        }
    }
}

/// GenType's reading of a module's interface (GenTypeMain.ml:91-107). OCaml
/// reads it in the implementation's compile, where `Paths.get_cmt_file`
/// selects the `.cmti` (an interface compile's `.cmti` selects nothing,
/// Paths.ml:59-85), so nothing here is raised or written: the
/// implementation's compile does that, in OCaml's order
/// ([`process_implementation_with_interface`]).
#[derive(Debug, Clone)]
pub enum InterfaceRead {
    /// Only the type declarations were registered (`declarations_only`).
    DeclarationsOnly {
        /// Notes were rendered from a location-free parse of the interface.
        needs_locations: bool,
    },
    /// The report of the exception the annotation walk raised.
    Raised(String),
    /// The annotation walk read the interface.
    Read {
        /// `@genType.ignoreInterface` seen by the walk, which stops at the
        /// first annotated item.
        ignore_interface: bool,
        /// Notes were rendered from a location-free parse of the interface.
        needs_locations: bool,
        /// The interface's output, planned when the walk did not select
        /// the implementation: what to write, or the report of the
        /// exception translating or emitting raised. `None` when the walk
        /// selected the implementation, or when the caller read only the
        /// interface's source (whose output is then not this compile's).
        output: Option<Outcome>,
    },
}

/// The paths and resolver GenType derives for one typed artifact
/// (GenTypeMain.ml:136-163).
struct Prepared {
    source_file: String,
    output_file: String,
    output_file_relative: String,
    local_resolver: Option<crate::gentype::module_resolver::Resolver>,
}

fn prepare(
    config: &crate::gentype::config::T,
    shared_resolver: Option<&crate::gentype::module_resolver::Resolver>,
    artifact: &TypedArtifact<'_>,
) -> Prepared {
    crate::timing::measure(crate::timing::Phase::GentypePrepare, || {

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
                |fname| fname == "React.res",
            )
        });
        Prepared {
            source_file,
            output_file,
            output_file_relative,
            local_resolver,
        }
    })
}

/// Register the artifact's type declarations for importers. An exception
/// their translation raises is raised where OCaml translates them: in an
/// importer's EmitJs (see `InProcessTypeDeclarations`), or in this module's
/// own translation.
fn register_type_declarations(
    config: &crate::gentype::config::T,
    prepared: &Prepared,
    resolver: &crate::gentype::module_resolver::Resolver,
    artifact: &TypedArtifact<'_>,
) -> bool {
    let notes = std::rc::Rc::new(crate::gentype::log_::Notes::default());
    let result = crate::timing::measure(crate::timing::Phase::GentypeDeclarations, || {
        typed_artifact_translate_type_declarations(
            config, &prepared.output_file_relative, resolver, &notes, artifact,
        )
    })
    .map(|translation| {
        if crate::perf_counters::enabled() || cfg!(test) {
            let ignore_interface = std::cell::Cell::new(false);
            let annotated = typed_artifact_check_annotations(
                &|arena, _loc, attributes| {
                    read_input_check_annotation(&ignore_interface, arena, attributes)
                },
                artifact,
            )
            .unwrap_or(true);
            crate::perf_counters::record_gentype_translation(
                artifact.ctx,
                annotated,
                translation.type_declarations.len(),
            );
        }
        crate::timing::measure(crate::timing::Phase::GentypePortable, || {
            crate::gentype::code_item::TypeDeclarations::portable(
                translation.type_declarations, artifact.ctx,
            )
        })
    })
    .map_err(artifact.render_escape);
    let type_declarations = InProcessTypeDeclarations {
        notes: notes.take(),
        result,
    };
    let noted = !type_declarations.notes.is_empty();
    if let Some(cmt_file) =
        cmt_file_for_typed_artifact(config, &prepared.source_file, artifact.is_interface)
    {
        register_in_process_type_declarations(
            &artifact.compiler_module_name,
            &cmt_file,
            type_declarations,
        );
    }
    noted
}

/// GenTypeMain.ml:165-175 up to the write: the output of an artifact whose
/// annotation walk found `has_gentype_annotations`.
fn plan_output(
    config: &crate::gentype::config::T,
    prepared: &Prepared,
    resolver: &crate::gentype::module_resolver::Resolver,
    artifact: &TypedArtifact<'_>,
    notes: &std::rc::Rc<crate::gentype::log_::Notes>,
    has_gentype_annotations: bool,
) -> Result<Output, String> {
    let output_file = prepared.output_file.clone();
    if has_gentype_annotations {
        crate::timing::measure(crate::timing::Phase::GentypeEmission, || {
            let translation = translate_typed_artifact(
                config,
                &prepared.output_file_relative,
                resolver,
                notes,
                artifact,
            )
            .map_err(artifact.render_escape)?;
            let decl_file = |loc: crate::types::DeclLoc| {
                crate::gentype::annotation::decl_file(artifact.ctx, artifact.arena, loc)
            };
            let emit_notes = crate::gentype::emit_js::EmitNotes {
                notes,
                file: &decl_file,
            };
            let project_root = config.project_root.clone();
            let get_cmt_file = |cmt: &str| get_cmt_file_for_typed_artifact_import(&project_root, cmt);
            let read_declarations = |notes: &crate::gentype::log_::Notes,
                                     config: &mut crate::gentype::config::T,
                                     _output: &str,
                                     resolver: &crate::gentype::module_resolver::Resolver,
                                     cmt: &str| {
                // The callback uses this argument only to name a failed importer.
                input_cmt_translate_type_declarations(
                    notes, config, &artifact.compiler_module_name, resolver, cmt,
                )
            };
            // Only emitting mutates the config; modules without GenType
            // annotations skip the copy.
            let mut config = config.clone();
            let contents = emit_translation_contents(
                artifact.ctx,
                &mut config,
                crate::gentype::emit_js::EmitTarget {
                    notes: &emit_notes,
                    file_name: &artifact.file_name,
                    output_file_relative: &prepared.output_file_relative,
                    resolver,
                    get_cmt_file: &get_cmt_file,
                    input_cmt_translate_type_declarations: &read_declarations,
                },
                &prepared.source_file,
                &translation,
            )?;
            Ok(Output::Write {
                output_file,
                contents,
            })
        })
    } else if typed_artifact_has_type_errors(artifact) {
        Ok(Output::TypeError { output_file })
    } else {
        Ok(Output::NoMatch { output_file })
    }
}

/// GenTypeMain.ml:94-104: the annotation check of `read_input_cmt`, which
/// reads each attribute list's `ignoreInterface` payload, then its
/// annotation payload; either read raises on an invalid escape.
pub fn read_input_check_annotation(
    ignore_interface: &std::cell::Cell<bool>,
    arena: &ParseArena,
    attributes: &Attributes,
) -> crate::gentype::annotation::Read<bool> {
    if crate::gentype::annotation::get_attribute_payload(
        arena,
        crate::gentype::annotation::tag_is_gentype_ignore_interface,
        attributes,
    )?
    .is_some()
    {
        ignore_interface.set(true);
    }
    Ok(crate::gentype::annotation::get_attribute_payload(
        arena,
        crate::gentype::annotation::tag_is_one_of_the_gentype_annotations,
        attributes,
    )?
    .is_some())
}

/// Discard stale declarations when an unneeded module is recompiled, while
/// retaining the normal removal of an obsolete generated file. No resolver,
/// annotation walk, translation or declaration encoding is needed here.
fn unneeded_artifact(config: &crate::gentype::config::T, artifact: &TypedArtifact<'_>) -> Outcome {
    if artifact.declarations_only {
        return Outcome::default();
    }
    let source = artifact.source_file.map(str::to_owned).unwrap_or_else(|| {
        format!(
            "{}{}",
            artifact.file_name,
            if artifact.is_interface {
                ".resi"
            } else {
                ".res"
            }
        )
    });
    Outcome {
        result: Ok(Some(Output::NoMatch {
            output_file: crate::gentype::paths::get_output_file(config, &source),
        })),
        ..Outcome::default()
    }
}

/// GenType for a module without an interface (GenTypeMain.ml:136-175, with
/// `read_input_cmt`'s implementation case).
pub fn process_typed_artifact(
    config: &crate::gentype::config::T,
    shared_resolver: Option<&crate::gentype::module_resolver::Resolver>,
    artifact: TypedArtifact<'_>,
) -> Outcome {
    if !artifact.declarations_needed {
        return unneeded_artifact(config, &artifact);
    }
    // Mirrors compiler/gentype/GenTypeMain.ml:136-175, but starts from the
    // typedtree already produced in-process instead of re-reading a .cmt.
    // The OCaml call site is compiler/core/js_implementation.ml:170 after
    // Typemod saved the CMT at compiler/ml/typemod.ml:1785-1787.
    let prepared = prepare(config, shared_resolver, &artifact);
    let resolver = shared_resolver
        .or(prepared.local_resolver.as_ref())
        .expect("GenType resolver must be available");
    let noted = register_type_declarations(config, &prepared, resolver, &artifact);
    if artifact.declarations_only {
        return Outcome {
            needs_locations: needs_locations(&artifact, noted),
            ..Outcome::default()
        };
    }
    let ignore_interface = std::cell::Cell::new(false);
    let has_gentype_annotations = match typed_artifact_check_annotations(
        &|arena, _loc, attributes| {
            read_input_check_annotation(&ignore_interface, arena, attributes)
        },
        &artifact,
    ) {
        Ok(has_gentype_annotations) => has_gentype_annotations,
        Err(escape) => return Outcome::raised((artifact.render_escape)(escape)),
    };
    let notes = std::rc::Rc::new(crate::gentype::log_::Notes::default());
    let result = plan_output(
        config,
        &prepared,
        resolver,
        &artifact,
        &notes,
        has_gentype_annotations,
    );
    let outcome = Outcome::after(&notes, result);
    Outcome {
        needs_locations: needs_locations(&artifact, noted || !outcome.notes.is_empty()),
        ..outcome
    }
}

/// Read a module's typed interface for its implementation's compile
/// (GenTypeMain.ml:91-107): register its type declarations, walk its
/// annotations, and plan its output unless the walk selected the
/// implementation. Nothing is raised or written here.
pub fn read_interface_artifact(
    config: &crate::gentype::config::T,
    shared_resolver: Option<&crate::gentype::module_resolver::Resolver>,
    artifact: TypedArtifact<'_>,
) -> InterfaceRead {
    if !artifact.declarations_needed {
        return InterfaceRead::Read {
            ignore_interface: false,
            needs_locations: false,
            output: Some(unneeded_artifact(config, &artifact)),
        };
    }
    let prepared = prepare(config, shared_resolver, &artifact);
    let resolver = shared_resolver
        .or(prepared.local_resolver.as_ref())
        .expect("GenType resolver must be available");
    let noted = register_type_declarations(config, &prepared, resolver, &artifact);
    if artifact.declarations_only {
        return InterfaceRead::DeclarationsOnly {
            needs_locations: needs_locations(&artifact, noted),
        };
    }
    let ignore_interface = std::cell::Cell::new(false);
    let has_gentype_annotations = match typed_artifact_check_annotations(
        &|arena, _loc, attributes| {
            read_input_check_annotation(&ignore_interface, arena, attributes)
        },
        &artifact,
    ) {
        Ok(has_gentype_annotations) => has_gentype_annotations,
        Err(escape) => return InterfaceRead::Raised((artifact.render_escape)(escape)),
    };
    let ignore_interface = ignore_interface.get();
    let output = (!ignore_interface).then(|| {
        let notes = std::rc::Rc::new(crate::gentype::log_::Notes::default());
        let result = plan_output(
            config,
            &prepared,
            resolver,
            &artifact,
            &notes,
            has_gentype_annotations,
        );
        Outcome::after(&notes, result)
    });
    let noted = noted
        || output
            .as_ref()
            .is_some_and(|output| !output.notes.is_empty());
    InterfaceRead::Read {
        ignore_interface,
        needs_locations: needs_locations(&artifact, noted),
        output,
    }
}

impl InterfaceRead {
    /// Notes were rendered from a location-free parse of the interface.
    pub fn needs_locations(&self) -> bool {
        match self {
            InterfaceRead::DeclarationsOnly { needs_locations }
            | InterfaceRead::Read {
                needs_locations, ..
            } => *needs_locations,
            InterfaceRead::Raised(_) => false,
        }
    }
}

/// GenType for a module with an interface, in its implementation's compile
/// (GenTypeMain.ml:108-134, then 165-175): raise what reading the interface
/// raised, walk the implementation's annotations (warning that each is
/// ignored while no `@genType.ignoreInterface` was seen), then write the
/// selected artifact's output.
pub fn process_implementation_with_interface(
    config: &crate::gentype::config::T,
    shared_resolver: Option<&crate::gentype::module_resolver::Resolver>,
    interface: InterfaceRead,
    artifact: TypedArtifact<'_>,
) -> Outcome {
    if !artifact.declarations_needed {
        return unneeded_artifact(config, &artifact);
    }
    let (ignore_interface, interface_output) = match interface {
        InterfaceRead::DeclarationsOnly { .. } => {
            return process_typed_artifact(config, shared_resolver, artifact);
        }
        InterfaceRead::Raised(report) => return Outcome::raised(report),
        InterfaceRead::Read {
            ignore_interface,
            output,
            ..
        } => (ignore_interface, output),
    };
    if artifact.declarations_only {
        return process_typed_artifact(config, shared_resolver, artifact);
    }
    let ignore_interface = std::cell::Cell::new(ignore_interface);
    let notes = crate::gentype::log_::Notes::default();
    let walked = typed_artifact_check_annotations(
        &|arena, loc, attributes| {
            let annotated = read_input_check_annotation(&ignore_interface, arena, attributes)?;
            if annotated && !ignore_interface.get() {
                // GenTypeMain.ml:116-121.
                let loc = arena.to_location(loc);
                notes.info(
                    &crate::gentype::annotation::parsed_file(arena, &loc),
                    &loc,
                    "Warning genType",
                    "Annotation is ignored as there's a .resi file",
                );
            }
            Ok(annotated)
        },
        &artifact,
    );
    let notes = notes.take();
    let walk_needs_locations = needs_locations(&artifact, !notes.is_empty());
    let outcome = match walked {
        Err(escape) => Outcome::raised((artifact.render_escape)(escape)),
        // The implementation's annotations were read above; its own walk
        // reads the same payloads again.
        Ok(_) if ignore_interface.get() => {
            process_typed_artifact(config, shared_resolver, artifact)
        }
        Ok(_) => interface_output.unwrap_or_default(),
    };
    Outcome {
        needs_locations: outcome.needs_locations || walk_needs_locations,
        notes: notes.into_iter().chain(outcome.notes).collect(),
        result: outcome.result,
    }
}

fn cmt_file_for_typed_artifact(
    config: &crate::gentype::config::T,
    source_file: &str,
    is_interface: bool,
) -> Option<String> {
    // OCaml passes outputprefix.cmt/cmt_file through compiler/gentype/Paths.ml:61-86
    // before GenTypeMain.ml:136-175. Rust starts from the source path, so rebuild
    // the path Import_path.to_cmt names the module's typed tree by: flat in the
    // package's artifact directory (lib/rescript) below the project root,
    // where [`get_cmt_file_for_typed_artifact_import`] looks it up.
    let source_path = Path::new(source_file);
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
        Path::new(&config.project_root)
            .join("lib")
            .join("rescript")
            .join(format!("{stem}{namespace}.{extension}"))
            .to_string_lossy()
            .to_string(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::context::IdGenerator;
    use crate::parser::{Parser, module};
    use crate::types::{TypeCheckContext, initial_env};

    /// Run GenType on `source`, compiled as `src/{module}.res` of the project
    /// at `root`, with every `"BAD"` string replaced by the one-segment
    /// template `Fo\xo` a PPX can produce (its `\x` escape is invalid). An
    /// invalid escape renders as `Invalid string escape sequence at <cnum>`.
    fn gentype_with_bad_strings(root: &Path, module: &str, source: &str) -> Result<(), String> {
        gentype_outcome(root, module, source)
            .apply()
            .expect("GenType I/O")
            .1
    }

    /// What GenType does for `source` (see `gentype_with_bad_strings`), not
    /// yet applied.
    fn gentype_outcome(root: &Path, module: &str, source: &str) -> Outcome {
        gentype_outcome_with_needed(root, module, source, true)
    }

    fn gentype_outcome_with_needed(
        root: &Path,
        module: &str,
        source: &str,
        needed: bool,
    ) -> Outcome {
        let id_gen = IdGenerator::with_start_stamp(999);
        let type_ctx = TypeContext::new(std::sync::Arc::new(id_gen));
        let source_file = format!("src/{module}.res");
        let mut parser = Parser::new(&source_file, source);
        let structure = module::parse_structure(&mut parser);
        assert!(!parser.has_errors(), "parse failed");
        let mut arena = parser.into_arena();
        struct BadStrings(Vec<crate::parse_arena::ExprIdx>);
        impl crate::binary_ast::ast_iter::AstIter for BadStrings {
            fn expr(&mut self, arena: &ParseArena, idx: crate::parse_arena::ExprIdx) {
                if let crate::parser::ast::ExpressionDesc::Pexp_constant(constant) =
                    &arena.get_expr(idx).pexp_desc
                    && let crate::parser::ast::Constant::String(value) = constant
                    && value.semantic(arena) == "BAD"
                {
                    self.0.push(idx);
                }
                crate::binary_ast::ast_iter::walk_expr(self, arena, idx);
            }
        }
        let mut found = BadStrings(Vec::new());
        crate::binary_ast::ast_iter::walk_structure(&mut found, &arena, &structure);
        let source_idx = arena.intern("Fo\\xo");
        for expr_idx in found.0 {
            let loc = arena.get_expr(expr_idx).pexp_loc;
            arena.get_expr_mut(expr_idx).pexp_desc =
                crate::parser::ast::ExpressionDesc::Pexp_template(Box::new(
                    crate::parser::ast::PexpTemplate {
                        source_segments: vec![crate::parser::ast::Loc {
                            txt: source_idx,
                            loc,
                        }],
                        values: vec![],
                    },
                ));
        }
        crate::types::typecore::prepare_typecheck_arena(&mut arena);
        let mut tctx = TypeCheckContext::new(&type_ctx, &arena);
        let env = initial_env(&type_ctx);
        let (typed, _) = crate::types::typemod::type_structure(&mut tctx, &env, &arena, &structure)
            .unwrap_or_else(|error| panic!("{module} type checks: {error:?}"));
        let config = crate::gentype::config::build_config_from_cli_args(
            None,
            &[
                "-bs-project-root".to_string(),
                root.to_string_lossy().into_owned(),
                "-bs-gentype".to_string(),
            ],
        );
        let render_escape = |escape| match escape {
            crate::gentype::annotation::InvalidEscape::Parsed(loc) => format!(
                "Invalid string escape sequence at {}",
                arena.to_location(loc).loc_start.cnum
            ),
            crate::gentype::annotation::InvalidEscape::Decl(loc) => format!(
                "Invalid string escape sequence at {}",
                type_ctx.resolve_loc(loc).loc_start.cnum
            ),
        };
        process_typed_artifact(
            &config,
            None,
            TypedArtifact {
                annots: TypedArtifactAnnots::Implementation(&typed),
                ta: &tctx.typed,
                arena: &arena,
                ctx: &type_ctx,
                source_file: Some(&source_file),
                compiler_module_name: module.to_string(),
                file_name: crate::gentype::paths::get_module_name_from_source_path(&source_file),
                is_interface: false,
                declarations_only: false,
                declarations_needed: needed,
                render_escape: &render_escape,
            },
        )
    }

    #[test]
    fn unreachable_artifact_translates_zero_declarations() {
        let root = project("unreachable");
        let before = crate::perf_counters::gentype_counts_for_test();
        let outcome = gentype_outcome_with_needed(&root, "Unreachable", "type t = int", false);
        assert!(outcome.result.is_ok());
        assert_eq!(crate::perf_counters::gentype_counts_for_test(), before);
        assert!(type_declarations_of_module("Unreachable").is_empty());
        let outcome = gentype_outcome_with_needed(&root, "Reachable", "type t = int", true);
        assert!(outcome.result.is_ok());
        let after = crate::perf_counters::gentype_counts_for_test();
        assert_eq!(after[0], before[0] + 1);
        assert_eq!(after[1], before[1] + 1);
    }

    #[test]
    fn skipped_artifact_lookup_fails_with_importer_and_owner() {
        let root = project("closure-error");
        let path = root.join("Missing.cmt").to_string_lossy().into_owned();
        set_skipped_modules(std::iter::once("Missing".to_string()));
        assert!(has_in_process_type_declarations(Path::new(&path)));
        let error = skipped_declaration_error(&path, "Importer").unwrap();
        assert!(error.contains("module Importer"), "{error}");
        assert!(error.contains("module Missing"), "{error}");
        assert!(type_declarations_of_module("Missing").is_empty());
        #[cfg(debug_assertions)]
        in_process_type_declarations_cache()
            .lock()
            .unwrap()
            .skipped_requests
            .retain(|(importer, owner)| importer != "Importer" || owner != "Missing");
    }

    fn project(name: &str) -> PathBuf {
        let root =
            std::env::temp_dir().join(format!("gentype-escape-{name}-{}", std::process::id()));
        std::fs::create_dir_all(root.join("src")).expect("create project");
        root
    }

    fn generated(root: &Path, module: &str) -> Option<String> {
        std::fs::read_to_string(root.join(format!("src/{module}.gen.tsx"))).ok()
    }

    /// GenTypeMain.ml:93-107 and Translation.ml read annotation payloads
    /// with Ast_payload.semantic_string_of_expression, which raises on an
    /// invalid escape: the compile fails at the template and writes no
    /// output. A valid backquoted or braced payload reads as its string.
    #[test]
    fn gentype_payload_readers_raise_on_an_invalid_template() {
        let root = project("readers");
        for (module, source, raised) in [
            // The annotation check reads the first annotation's payload.
            (
                "EscCheck",
                "@genType.as(\"BAD\") @genType\nlet x = 1\n",
                Some(12),
            ),
            // Annotation.ml:54-62: a tuple payload reads its last element first.
            (
                "EscTuple",
                "@genType.import((\"BAD\", \"BAD\")) external x: int => int = \"x\"\n",
                Some(24),
            ),
            // TranslateTypeDeclarations.ml:56: a field's unsupported
            // `@genType.as` (its `@as` is read by the type checker).
            (
                "EscField",
                "@genType\ntype t = {@genType.as(\"BAD\") a: int}\n",
                Some(31),
            ),
            (
                "EscOk",
                "@genType.as(`ok`) @genType\nlet x = 1\n@genType.as({\"fine\"}) @genType\nlet y = 2\n",
                None,
            ),
        ] {
            let result = gentype_with_bad_strings(&root, module, source);
            match raised {
                Some(cnum) => {
                    assert_eq!(
                        result,
                        Err(format!("Invalid string escape sequence at {cnum}")),
                        "{module}"
                    );
                    assert_eq!(generated(&root, module), None, "{module} writes no output");
                }
                None => {
                    assert_eq!(result, Ok(()), "{module}");
                    let output = generated(&root, module).expect("EscOk output");
                    assert!(output.contains("export const ok"), "{output}");
                    assert!(output.contains("export const fine"), "{output}");
                }
            }
        }
    }

    /// EmitJs.ml:437-453 translates a module's type declarations only when an
    /// importer's output needs them, so an invalid escape there does not fail
    /// the declaring module (without GenType annotations of its own) and is
    /// raised by the importer's lookup.
    #[test]
    fn gentype_declaration_escapes_raise_where_an_importer_reads_them() {
        let root = project("lazy");
        let declaring = "type t = {@genType.as(\"BAD\") a: int}\n";
        assert_eq!(
            gentype_with_bad_strings(&root, "EscDecls", declaring),
            Ok(())
        );
        let config = crate::gentype::config::build_config_from_cli_args(
            None,
            &[
                "-bs-project-root".to_string(),
                root.to_string_lossy().into_owned(),
            ],
        );
        let cmt_file = cmt_file_for_typed_artifact(&config, "src/EscDecls.res", false).unwrap();
        let resolver =
            crate::gentype::module_resolver::create_lazy_resolver(&config, &[], |_| false);
        let mut config = config;
        let notes = crate::gentype::log_::Notes::default();
        assert_eq!(
            input_cmt_translate_type_declarations(&notes, &mut config, "", &resolver, &cmt_file)
                .err(),
            Some("Invalid string escape sequence at 22".to_string())
        );
    }

    /// GenType's warnings (Log_.info) are part of the outcome, which prints
    /// them and writes the file only when applied: after the JavaScript, as
    /// js_implementation.ml:164-171 runs GenType, so a compile that fails or
    /// is retried before then prints and writes nothing.
    #[test]
    fn gentype_warnings_and_output_wait_for_the_outcome_to_be_applied() {
        let root = project("notes");
        // Annotation.ml:170-176: a `@genType` payload is ignored, with a note.
        let outcome = gentype_outcome(&root, "EscNote", "@genType(`x`) let x = 1\n");
        assert_eq!(outcome.notes.len(), 1, "{:?}", outcome.notes);
        let note = &outcome.notes[0];
        assert!(note.contains("Annotation payload is ignored"), "{note}");
        assert!(note.contains("src/EscNote.res:1:"), "{note}");
        assert!(!note.contains("<source>"), "{note}");
        assert_eq!(generated(&root, "EscNote"), None);
        let (printed, result) = outcome.apply().expect("GenType I/O");
        assert!(
            printed.contains("Annotation payload is ignored"),
            "{printed}"
        );
        assert_eq!(result, Ok(()));
        assert!(generated(&root, "EscNote").is_some());
        // A raise keeps the notes printed before it.
        let outcome = gentype_outcome(
            &root,
            "EscNoteBad",
            "@genType(`x`) let x = 1\n@genType.as(\"BAD\") @genType let y = 2\n",
        );
        assert_eq!(outcome.notes.len(), 1, "{:?}", outcome.notes);
        assert!(outcome.result.is_err());
    }

    /// A module's cached declaration translation keeps its warnings: the
    /// declaring module without annotations prints none, and an importer's
    /// EmitJs lookup (EmitJs.ml:437-453) prints them, each time it reads.
    #[test]
    fn gentype_declaration_warnings_wait_for_an_importer_to_read_them() {
        let root = project("lazynotes");
        let declaring = "type t = {@genType.as(`y`) a: int}\n";
        let outcome = gentype_outcome(&root, "EscDeclNotes", declaring);
        assert!(outcome.notes.is_empty(), "{:?}", outcome.notes);
        let config = crate::gentype::config::build_config_from_cli_args(
            None,
            &[
                "-bs-project-root".to_string(),
                root.to_string_lossy().into_owned(),
            ],
        );
        let cmt_file = cmt_file_for_typed_artifact(&config, "src/EscDeclNotes.res", false).unwrap();
        let resolver =
            crate::gentype::module_resolver::create_lazy_resolver(&config, &[], |_| false);
        let mut config = config;
        for _ in 0..2 {
            let notes = crate::gentype::log_::Notes::default();
            assert!(
                input_cmt_translate_type_declarations(
                    &notes,
                    &mut config,
                    "",
                    &resolver,
                    &cmt_file
                )
                .is_ok()
            );
            let notes = notes.take();
            assert_eq!(notes.len(), 1, "{notes:?}");
            assert!(
                notes[0].contains("@genType.as is not supported anymore"),
                "{notes:?}"
            );
            assert!(notes[0].contains("src/EscDeclNotes.res:1:"), "{notes:?}");
            // Log_.ml:99-102's box indents the body's leading line break.
            assert!(notes[0].contains("\n  \n  @genType.as is not"), "{notes:?}");
        }
    }

    /// The error is the compiling file's own: files compiled in parallel,
    /// each with its own context, keep their output.
    #[test]
    fn gentype_escape_errors_stay_with_their_file_under_parallel_compiles() {
        let root = project("parallel");
        let results = std::thread::scope(|scope| {
            let handles: Vec<_> = (0..8)
                .map(|i| {
                    let root = &root;
                    scope.spawn(move || {
                        let (module, source) = match i % 2 {
                            0 => (
                                format!("EscBad{i}"),
                                "@genType.as(\"BAD\") @genType\nlet x = 1\n",
                            ),
                            _ => (
                                format!("EscGood{i}"),
                                "@genType.as(`ok`) @genType\nlet x = 1\n",
                            ),
                        };
                        (
                            module.clone(),
                            gentype_with_bad_strings(root, &module, source),
                        )
                    })
                })
                .collect();
            handles
                .into_iter()
                .map(|h| h.join().unwrap())
                .collect::<Vec<_>>()
        });
        for (module, result) in results {
            if module.starts_with("EscBad") {
                assert_eq!(
                    result,
                    Err("Invalid string escape sequence at 12".to_string())
                );
                assert_eq!(generated(&root, &module), None, "{module}");
            } else {
                assert_eq!(result, Ok(()), "{module}");
                assert!(
                    generated(&root, &module)
                        .unwrap()
                        .contains("export const ok")
                );
            }
        }
    }
}

#[cfg(test)]
mod file_inventory_tests {
    use super::Output;
    use crate::gentype::generated_files::take_file_operations;

    #[test]
    fn absent_outputs_perform_zero_file_operations() {
        take_file_operations();
        for module in 0..512 {
            Output::Absent {
                output_file: format!("not-created/M{module}.gen.tsx"),
            }
            .apply()
            .unwrap();
        }
        assert_eq!(take_file_operations(), 0);
    }

    #[test]
    fn unknown_and_existing_outputs_keep_the_original_operations() {
        let dir = tempfile::tempdir().unwrap();
        let file = dir.path().join("M.gen.tsx").to_string_lossy().into_owned();
        take_file_operations();
        Output::NoMatch {
            output_file: file.clone(),
        }
        .apply()
        .unwrap();
        assert_eq!(take_file_operations(), 1);
        std::fs::write(&file, "handwritten").unwrap();
        Output::NoMatch {
            output_file: file.clone(),
        }
        .apply()
        .unwrap();
        assert_eq!(take_file_operations(), 2);
        assert!(!std::path::Path::new(&file).exists());
        Output::Write {
            output_file: file.clone(),
            contents: "new".to_string(),
        }
        .apply()
        .unwrap();
        assert_eq!(take_file_operations(), 2);
        Output::Write {
            output_file: file,
            contents: "new".to_string(),
        }
        .apply()
        .unwrap();
        assert_eq!(take_file_operations(), 2); // exists + read, no rewrite
    }
}
