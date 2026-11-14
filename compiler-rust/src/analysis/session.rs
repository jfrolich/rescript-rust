//! The modules a command works on, type-checked on demand: what OCaml's
//! `state`, `package` and `.cmt` loading (cmt.ml, process_cmt.ml) provide.

use super::process_cmt::{self, Annots, Ctx};
use super::process_extra;
use super::resolve_path::Session;
use super::shared_types::{
    Declared, ExportedKind, Extra, File, Loc, Located, Module, ModuleId, ModuleItem,
    ModuleItemKind, ModulePath,
};
use crate::driver::{ToolingTyped, ToolingTypedModule};
use crate::parse_arena::ParseArena;
use std::cell::OnceCell;
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;

/// A parsed source, kept alive while its typed tree is used (typed-tree
/// locations and attributes point into its arena).
pub trait ParsedSource {
    /// The arena holding the parsed tree.
    fn arena(&self) -> &ParseArena;
}

/// One module's source, type-checked.
pub struct TypedSource {
    /// The parsed source the typed tree was checked from.
    pub parsed: Arc<dyn ParsedSource>,
    /// The typed tree and the type state it refers to.
    pub typed: ToolingTypedModule,
    /// The absolute path of the source.
    pub path: PathBuf,
}

/// The absolute source paths of a module (OCaml's `paths`).
#[derive(Debug, Clone, Default)]
pub struct SourcePaths {
    /// The `.res` file, if any.
    pub implementation: Option<PathBuf>,
    /// The `.resi` file, if any.
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
    /// The `(alias, module)` pairs of a namespace module. A build generates
    /// the namespace's aliases (`module Foo = Foo-MyNamespace`) instead of
    /// compiling a source; OCaml reads the `.cmt` its `.mlmap` compiles to
    /// (packages.ml:104-109).
    fn namespace_aliases(&self, module_name: &str) -> Option<Vec<(String, String)>>;
    /// Type-check a module's interface or implementation from its current
    /// source.
    fn typecheck(&self, module_name: &str, interface: bool) -> Option<TypedSource>;
}

/// A loaded module: OCaml's `full` (a `File.t` and its `extra`).
pub struct Loaded {
    /// The type-checked source.
    pub source: TypedSource,
    /// What processing the typed tree found.
    pub file: File,
    /// The references and locations in the typed tree.
    pub extra: Extra,
    /// An attribute reader's error raised by a command reading this module.
    pub raised: super::process_attributes::Raised,
    /// The file names of the module's locations.
    files: process_cmt::FileNames,
}

impl Loaded {
    /// The error a command's attribute reader raised on this module.
    fn raised_error(&self) -> Option<String> {
        let error = self.raised.get()?;
        Some(invalid_escape_message(&self.ctx(), error))
    }

    /// What the module's typed tree is read with.
    pub fn ctx(&self) -> Ctx<'_> {
        Ctx {
            arena: self.source.parsed.arena(),
            types: &self.source.typed.type_ctx,
            raised: &self.raised,
            ta: &self.source.typed.typed_arena,
            files: &self.files,
        }
    }
}

/// The modules of one command, each loaded at most once.
pub struct ProjectSession<'p> {
    project: &'p dyn Project,
    ids: HashMap<String, usize>,
    /// Two slots per module: implementation, then interface.
    slots: Vec<OnceCell<Option<Loaded>>>,
    /// One slot per module: the file of a namespace module, which has no
    /// source to load. It takes the module's implementation id.
    namespaces: Vec<OnceCell<Option<File>>>,
    /// The first error an attribute reader raised loading a module, which
    /// ends the command (OCaml's raise is not caught).
    failure: std::cell::RefCell<Option<String>>,
}

impl<'p> ProjectSession<'p> {
    /// An empty session over the modules of `project`.
    pub fn new(project: &'p dyn Project) -> Self {
        let names = project.module_names();
        let ids = names
            .iter()
            .enumerate()
            .map(|(i, name)| (name.clone(), i))
            .collect();
        let slots = (0..names.len() * 2).map(|_| OnceCell::new()).collect();
        let namespaces = (0..names.len()).map(|_| OnceCell::new()).collect();
        ProjectSession {
            project,
            ids,
            slots,
            namespaces,
            failure: std::cell::RefCell::new(None),
        }
    }

    /// The project the session loads modules from.
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

    /// The file of a namespace module: its aliases, as `Process_cmt` reads
    /// them from the namespace's `.cmt`.
    fn namespace_file(&self, module_name: &str) -> Option<&File> {
        let index = *self.ids.get(module_name)?;
        self.namespaces[index]
            .get_or_init(|| {
                let aliases = self.project.namespace_aliases(module_name)?;
                Some(namespace_file(module_name, index * 2, &aliases))
            })
            .as_ref()
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
    let files = process_cmt::FileNames::default();
    let ctx = Ctx {
        arena: source.parsed.arena(),
        types: &source.typed.type_ctx,
        raised: &raised,
        ta: &source.typed.typed_arena,
        files: &files,
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
        files,
    })
}

/// The file of namespace module `module_name`, which exports each alias as
/// a module standing for its target.
fn namespace_file(module_name: &str, id: ModuleId, aliases: &[(String, String)]) -> File {
    let mut file = File::create(module_name, String::new(), id);
    let mut structure = (*file.structure).clone();
    let mut exported = (*structure.exported).clone();
    // `Location.none`'s file name.
    let none_file: Arc<str> = Arc::from(process_cmt::NONE_FILE);
    for (stamp, (alias, target)) in (1..).zip(aliases) {
        let item = Module::Ident(crate::types::Path::pident(
            crate::ident::Ident::create_persistent(target.as_str()),
        ));
        file.stamps.add_module(
            stamp,
            Declared {
                name: Located {
                    txt: alias.clone(),
                    loc: Loc::none(),
                },
                extent_loc: Loc::none(),
                extent_file: none_file.clone(),
                stamp,
                module_path: ModulePath::File {
                    uri: file.uri.clone(),
                    module_name: module_name.to_string(),
                },
                is_exported: true,
                deprecated: None,
                docstring: Vec::new(),
                item: item.clone(),
            },
        );
        exported.add(ExportedKind::Module, alias, stamp);
        structure.items.push(ModuleItem {
            kind: ModuleItemKind::Module {
                type_: item,
                is_module_type: false,
            },
            name: alias.clone(),
            loc: Loc::none(),
            file: none_file.clone(),
            docstring: Vec::new(),
            deprecated: None,
        });
    }
    structure.exported = Arc::new(exported);
    file.structure = Arc::new(structure);
    file
}

impl Session for ProjectSession<'_> {
    fn file(&self, id: ModuleId) -> &File {
        match self.slots[id].get().and_then(Option::as_ref) {
            Some(loaded) => &loaded.file,
            None => self.namespaces[id / 2]
                .get()
                .and_then(Option::as_ref)
                .expect("a file's module id names a loaded module"),
        }
    }

    fn file_for_module(&self, module_name: &str) -> Option<&File> {
        match self.full_from_module(module_name) {
            Some(loaded) => Some(&loaded.file),
            None => self.namespace_file(module_name),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_namespace_file_exports_its_aliases() {
        let aliases = [("Foo".to_string(), "Foo-MyNamespace".to_string())];
        let file = namespace_file("MyNamespace", 4, &aliases);
        let stamp = file
            .structure
            .exported
            .find(ExportedKind::Module, "Foo")
            .unwrap();
        let declared = file.stamps.find_module(stamp).unwrap();
        let Module::Ident(path) = &declared.item else {
            panic!("an alias is a module path");
        };
        assert_eq!(
            super::super::shared::path_ident_to_string(path),
            "Foo-MyNamespace"
        );
        assert_eq!(file.module, 4);
    }
}
