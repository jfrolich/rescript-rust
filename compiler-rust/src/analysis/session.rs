//! The modules a command works on, type-checked on demand: what OCaml's
//! `state`, `package` and `.cmt` loading (cmt.ml, process_cmt.ml) provide.

use super::process_cmt::{self, Annots, Ctx};
use super::process_extra;
use super::resolve_path::Session;
use super::shared_types::{Extra, File, ModuleId};
use crate::driver::{ToolingTyped, ToolingTypedModule};
use crate::parse_arena::ParseArena;
use std::cell::OnceCell;
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;

/// A parsed source, kept alive while its typed tree is used (typed-tree
/// locations and attributes point into its arena).
pub trait ParsedSource {
    fn arena(&self) -> &ParseArena;
}

/// One module's source, type-checked.
pub struct TypedSource {
    pub parsed: Arc<dyn ParsedSource>,
    pub typed: ToolingTypedModule,
    /// The absolute path of the source.
    pub path: PathBuf,
}

/// The absolute source paths of a module (OCaml's `paths`).
#[derive(Debug, Clone, Default)]
pub struct SourcePaths {
    pub implementation: Option<PathBuf>,
    pub interface: Option<PathBuf>,
}

/// The project a command runs in: its modules, including those of
/// dependencies and the runtime, and on-demand type-checking.
pub trait Project {
    /// Every module a command may load.
    fn module_names(&self) -> Vec<String>;
    /// The module whose implementation or interface is at `path`.
    fn module_for_path(&self, path: &Path) -> Option<String>;
    /// `Hashtbl.find_opt package.paths_for_module`.
    fn paths_for_module(&self, module_name: &str) -> Option<SourcePaths>;
    /// `package.project_files`: the package's own modules, sorted.
    fn project_files(&self) -> Vec<String>;
    /// `package.namespace`.
    fn namespace(&self) -> Option<String>;
    /// Type-check a module's interface or implementation from its current
    /// source.
    fn typecheck(&self, module_name: &str, interface: bool) -> Option<TypedSource>;
}

/// A loaded module: OCaml's `full` (a `File.t` and its `extra`).
pub struct Loaded {
    pub source: TypedSource,
    pub file: File,
    pub extra: Extra,
    /// An attribute reader's error raised by a command reading this module.
    pub raised: super::process_attributes::Raised,
}

impl Loaded {
    /// The error a command's attribute reader raised on this module.
    fn raised_error(&self) -> Option<String> {
        let error = self.raised.get()?;
        Some(invalid_escape_message(&self.ctx(), error))
    }

    pub fn ctx(&self) -> Ctx<'_> {
        Ctx {
            arena: self.source.parsed.arena(),
            types: &self.source.typed.type_ctx,
            raised: &self.raised,
            ta: &self.source.typed.typed_arena,
        }
    }
}

/// The modules of one command, each loaded at most once.
pub struct ProjectSession<'p> {
    project: &'p dyn Project,
    ids: HashMap<String, usize>,
    /// Two slots per module: implementation, then interface.
    slots: Vec<OnceCell<Option<Loaded>>>,
    /// The first error an attribute reader raised loading a module, which
    /// ends the command (OCaml's raise is not caught).
    failure: std::cell::RefCell<Option<String>>,
}

impl<'p> ProjectSession<'p> {
    pub fn new(project: &'p dyn Project) -> Self {
        let names = project.module_names();
        let ids = names
            .iter()
            .enumerate()
            .map(|(i, name)| (name.clone(), i))
            .collect();
        let slots = (0..names.len() * 2).map(|_| OnceCell::new()).collect();
        ProjectSession {
            project,
            ids,
            slots,
            failure: std::cell::RefCell::new(None),
        }
    }

    pub fn project(&self) -> &'p dyn Project {
        self.project
    }

    /// Load a module's implementation or interface.
    pub fn load(&self, module_name: &str, interface: bool) -> Option<&Loaded> {
        let id = self.ids.get(module_name)? * 2 + usize::from(interface);
        self.slots[id]
            .get_or_init(|| {
                let source = self.project.typecheck(module_name, interface)?;
                match load_source(source, module_name, id) {
                    Ok(loaded) => Some(loaded),
                    Err(error) => {
                        self.failure.borrow_mut().get_or_insert(error);
                        None
                    }
                }
            })
            .as_ref()
    }

    /// The error that ends the command: the first an attribute reader
    /// raised loading a module, then one raised reading a loaded module.
    pub fn failure(&self) -> Option<String> {
        if let Some(failure) = self.failure.borrow().clone() {
            return Some(failure);
        }
        self.slots
            .iter()
            .filter_map(|slot| slot.get().and_then(Option::as_ref))
            .find_map(Loaded::raised_error)
    }

    /// The module loaded as `id`, when it is.
    pub fn loaded(&self, id: ModuleId) -> &Loaded {
        self.slots[id]
            .get()
            .and_then(Option::as_ref)
            .expect("a file's module id names a loaded module")
    }

    /// The type context of module `id`'s types.
    pub fn types(&self, id: ModuleId) -> &crate::types::TypeContext {
        &self.loaded(id).source.typed.type_ctx
    }

    /// `Cmt.full_from_module`: the interface when there is one.
    pub fn full_from_module(&self, module_name: &str) -> Option<&Loaded> {
        let paths = self.project.paths_for_module(module_name)?;
        self.load(module_name, paths.interface.is_some())
    }

    /// `Cmt.fulls_from_module`: the implementation, then the interface.
    pub fn fulls_from_module(&self, module_name: &str) -> Vec<&Loaded> {
        let Some(paths) = self.project.paths_for_module(module_name) else {
            return Vec::new();
        };
        let mut fulls = Vec::new();
        if paths.implementation.is_some() {
            fulls.extend(self.load(module_name, false));
        }
        if paths.interface.is_some() {
            fulls.extend(self.load(module_name, true));
        }
        fulls
    }

    /// `Cmt.full_from_path`: the module whose source is at `path`, loaded
    /// from that source.
    pub fn full_from_path(&self, path: &Path) -> Option<&Loaded> {
        let module_name = self.project.module_for_path(path)?;
        let interface = path.to_string_lossy().ends_with('i');
        self.load(&module_name, interface)
    }
}

/// "Invalid string escape sequence" at the template an attribute reader
/// raised on (ast_payload.ml:39-51).
fn invalid_escape_message(
    ctx: &Ctx<'_>,
    error: super::process_attributes::InvalidEscape,
) -> String {
    let (loc, file) = match error {
        super::process_attributes::InvalidEscape::Parsed(loc) => {
            let loc = ctx.arena.to_location(loc);
            let file = ctx.arena.get_string(loc.loc_start.file_name).to_string();
            (loc, file)
        }
        super::process_attributes::InvalidEscape::Decl(loc) => {
            let loc = ctx.types.resolve_loc(loc);
            let file = ctx
                .types
                .resolve_cmi_longident_component(loc.loc_start.file_name)
                .unwrap_or_default();
            (loc, file)
        }
    };
    format!(
        "File \"{file}\", line {}, characters {}-{}:\nInvalid string escape sequence",
        loc.loc_start.line,
        loc.loc_start.cnum - loc.loc_start.bol,
        loc.loc_end.cnum - loc.loc_start.bol,
    )
}

/// Load a module, failing where an attribute reader raises.
fn load_source(source: TypedSource, module_name: &str, id: ModuleId) -> Result<Loaded, String> {
    let uri = source.path.to_string_lossy().into_owned();
    let raised = super::process_attributes::Raised::default();
    let ctx = Ctx {
        arena: source.parsed.arena(),
        types: &source.typed.type_ctx,
        raised: &raised,
        ta: &source.typed.typed_arena,
    };
    let annots = match &source.typed.typed {
        ToolingTyped::Implementation(structure) => Some(Annots::Implementation(
            ctx.ta.structure_items(structure.str_items),
        )),
        ToolingTyped::Interface(signature) => Some(Annots::Interface(
            ctx.ta.signature_items(signature.sig_items),
        )),
        ToolingTyped::Failed(_) => None,
    };
    let (file, extra) = match annots {
        Some(annots) => {
            let mut file = process_cmt::file_for_annots(ctx, id, module_name, uri, annots);
            let extra = process_extra::get_extra(ctx, &mut file, annots);
            (file, extra)
        }
        None => (File::create(module_name, uri, id), Extra::default()),
    };
    if let Some(error) = raised.get() {
        return Err(invalid_escape_message(&ctx, error));
    }
    Ok(Loaded {
        source,
        file,
        extra,
        raised,
    })
}

impl Session for ProjectSession<'_> {
    fn file(&self, id: ModuleId) -> &File {
        &self.loaded(id).file
    }

    fn file_for_module(&self, module_name: &str) -> Option<&File> {
        self.full_from_module(module_name)
            .map(|loaded| &loaded.file)
    }
}
