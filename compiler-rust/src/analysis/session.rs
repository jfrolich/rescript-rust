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
}

impl Loaded {
    pub fn ctx(&self) -> Ctx<'_> {
        Ctx {
            arena: self.source.parsed.arena(),
            types: &self.source.typed.type_ctx,
        }
    }
}

/// The modules of one command, each loaded at most once.
pub struct ProjectSession<'p> {
    project: &'p dyn Project,
    ids: HashMap<String, usize>,
    /// Two slots per module: implementation, then interface.
    slots: Vec<OnceCell<Option<Loaded>>>,
}

impl<'p> ProjectSession<'p> {
    pub fn new(project: &'p dyn Project) -> Self {
        let names = project.module_names();
        let ids = names.iter().enumerate().map(|(i, name)| (name.clone(), i)).collect();
        let slots = (0..names.len() * 2).map(|_| OnceCell::new()).collect();
        ProjectSession { project, ids, slots }
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
                Some(load_source(source, module_name, id))
            })
            .as_ref()
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

fn load_source(source: TypedSource, module_name: &str, id: ModuleId) -> Loaded {
    let uri = source.path.to_string_lossy().into_owned();
    let ctx = Ctx {
        arena: source.parsed.arena(),
        types: &source.typed.type_ctx,
    };
    let annots = match &source.typed.typed {
        ToolingTyped::Implementation(structure) => Some(Annots::Implementation(&structure.str_items)),
        ToolingTyped::Interface(signature) => Some(Annots::Interface(&signature.sig_items)),
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
    Loaded { source, file, extra }
}

impl Session for ProjectSession<'_> {
    fn file(&self, id: ModuleId) -> &File {
        &self.loaded(id).file
    }

    fn file_for_module(&self, module_name: &str) -> Option<&File> {
        let paths = self.project.paths_for_module(module_name)?;
        self.load(module_name, paths.interface.is_some()).map(|loaded| &loaded.file)
    }
}
