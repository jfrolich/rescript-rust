//! What the analyses share: names, paths, positions, the run configuration
//! and how a typed tree's locations are read.

use crate::parse_arena::{LocIdx, ParseArena};
use crate::types::context::TypeContext;
use crate::types::typedtree as tt;
use crate::types::{DeclLoc, Path as TypePath};
use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::{Arc, PoisonError, RwLock, RwLockReadGuard};

/// `Name.t`: a name, with a leading `+` when it is an implementation's.
pub type Name = Arc<str>;

/// `Name.create`.
pub fn name_create(s: &str, is_interface: bool) -> Name {
    if is_interface {
        Arc::from(s)
    } else {
        Arc::from(format!("+{s}"))
    }
}

/// `Name.is_interface`.
pub fn name_is_interface(s: &str) -> bool {
    match s.as_bytes().first() {
        Some(c) => *c != b'+',
        None => false,
    }
}

/// `Name.is_underscore`.
pub fn name_is_underscore(s: &str) -> bool {
    s == "_" || s == "+_"
}

/// `Name.starts_with_underscore`.
pub fn name_starts_with_underscore(s: &str) -> bool {
    let b = s.as_bytes();
    b.len() >= 2 && (b[0] == b'_' || (b[0] == b'+' && b[1] == b'_'))
}

/// `Name.to_interface`.
pub fn name_to_interface(s: &Name) -> Name {
    if name_is_interface(s) || s.is_empty() {
        s.clone()
    } else {
        Arc::from(&s[1..])
    }
}

/// `Name.to_implementation`.
pub fn name_to_implementation(s: &Name) -> Name {
    if name_is_interface(s) {
        Arc::from(format!("+{s}"))
    } else {
        s.clone()
    }
}

/// `Dce_path.t`: the names from the innermost one out to the file's module.
pub type DcePath = Vec<Name>;

/// `Dce_path.to_name`/`to_string`.
pub fn path_to_string(path: &[Name]) -> String {
    let mut out = String::new();
    for (i, name) in path.iter().rev().enumerate() {
        if i > 0 {
            out.push('.');
        }
        out.push_str(name);
    }
    out
}

/// `Dce_path.without_head`.
pub fn path_without_head(path: &[Name]) -> String {
    let mut names: Vec<Name> = path.iter().rev().map(name_to_interface).collect();
    if names.is_empty() {
        return String::new();
    }
    names.remove(0);
    names.iter().map(|n| &**n).collect::<Vec<_>>().join(".")
}

/// `Dce_path.from_path_t`.
pub fn path_from_type_path(path: &TypePath) -> DcePath {
    match path.flatten() {
        Ok((id, mods)) => {
            let mut names: Vec<Name> = Vec::with_capacity(mods.len() + 1);
            names.push(Arc::from(id.name()));
            names.extend(mods.iter().map(|m| Arc::from(*m)));
            names.reverse();
            names
        }
        Err(_) => Vec::new(),
    }
}

/// `Dce_path.on_ok_path`'s string: the dotted path, unless it has a functor
/// application.
pub fn type_path_dotted(path: &TypePath) -> Option<String> {
    let (id, mods) = path.flatten().ok()?;
    let mut out = id.name().to_string();
    for m in mods {
        out.push('.');
        out.push_str(m);
    }
    Some(out)
}

/// `Dce_path.module_to_implementation`.
pub fn path_module_to_implementation(path: &[Name]) -> DcePath {
    let mut path = path.to_vec();
    if let Some(last) = path.last_mut() {
        *last = name_to_implementation(last);
    }
    path
}

/// `Dce_path.module_to_interface`.
pub fn path_module_to_interface(path: &[Name]) -> DcePath {
    let mut path = path.to_vec();
    if let Some(last) = path.last_mut() {
        *last = name_to_interface(last);
    }
    path
}

/// `Dce_path.type_to_interface`.
pub fn path_type_to_interface(path: &[Name]) -> DcePath {
    let mut path = path.to_vec();
    if let Some(first) = path.first_mut() {
        *first = name_to_interface(first);
    }
    path
}

/// `Dce_path.to_module_name`.
pub fn path_to_module_name(is_type: bool, path: &[Name]) -> Name {
    let rest: &[Name] = if !is_type {
        match path {
            [_, tl @ ..] => tl,
            [] => return Arc::from(""),
        }
    } else {
        match path {
            [_, _, tl @ ..] => tl,
            _ => return Arc::from(""),
        }
    };
    Arc::from(path_to_string(rest))
}

/// A file name, interned for the run. Files are read in parallel, so which
/// file gets which number differs from run to run: identities are compared
/// for equality only, and files are ordered by their names.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FileId(pub u32);

/// The file names of a run: `pos_fname` values, compared by identity. The
/// threads reading the project's files share them.
#[derive(Default)]
pub struct Files {
    names: RwLock<indexmap::IndexSet<Arc<str>>>,
}

impl Files {
    /// The files of a run: `_none_` (0) and the empty name (1).
    pub fn new() -> Files {
        let files = Files::default();
        files.intern("_none_");
        files.intern("");
        files
    }

    /// The identity of file name `name`.
    pub fn intern(&self, name: &str) -> FileId {
        if let Some(index) = self.read().get_index_of(name) {
            return FileId(index as u32);
        }
        let mut names = self.names.write().unwrap_or_else(PoisonError::into_inner);
        let index = match names.get_index_of(name) {
            Some(index) => index,
            None => names.insert_full(Arc::from(name)).0,
        };
        FileId(index as u32)
    }

    /// The name of `file`.
    pub fn name(&self, file: FileId) -> Arc<str> {
        self.read()[file.0 as usize].clone()
    }

    fn read(&self) -> RwLockReadGuard<'_, indexmap::IndexSet<Arc<str>>> {
        self.names.read().unwrap_or_else(PoisonError::into_inner)
    }
}

/// The file of `Location.none`.
pub const NONE_FILE: FileId = FileId(0);
/// The file of `Lexing.dummy_pos`.
pub const DUMMY_FILE: FileId = FileId(1);

/// `Lexing.position`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Pos {
    /// `pos_fname`.
    pub file: FileId,
    /// `pos_lnum`.
    pub lnum: i32,
    /// `pos_bol`.
    pub bol: i32,
    /// `pos_cnum`.
    pub cnum: i32,
}

impl Pos {
    /// The start of `Location.none`.
    pub const NONE: Pos = Pos {
        file: NONE_FILE,
        lnum: 1,
        bol: 0,
        cnum: -1,
    };
    /// `Lexing.dummy_pos`.
    pub const DUMMY: Pos = Pos {
        file: DUMMY_FILE,
        lnum: 0,
        bol: 0,
        cnum: -1,
    };

    /// The column.
    pub fn col(&self) -> i32 {
        self.cnum - self.bol
    }
}

/// `Location.t`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Loc {
    /// `loc_start`.
    pub start: Pos,
    /// `loc_end`.
    pub end: Pos,
    /// `loc_ghost`.
    pub ghost: bool,
}

impl Loc {
    /// `Location.none`.
    pub const NONE: Loc = Loc {
        start: Pos::NONE,
        end: Pos::NONE,
        ghost: true,
    };

    /// Whether this is `Location.none` (`loc = Location.none`).
    pub fn is_none(&self) -> bool {
        *self == Loc::NONE
    }
}

/// `Filename.basename` for the `/`-separated paths positions hold.
pub fn basename(path: &str) -> &str {
    if path.is_empty() {
        return ".";
    }
    let trimmed = path.trim_end_matches('/');
    if trimmed.is_empty() {
        return "/";
    }
    match trimmed.rfind('/') {
        Some(i) => &trimmed[i + 1..],
        None => trimmed,
    }
}

/// `Run_config.t`.
#[derive(Debug, Clone, Default)]
pub struct RunConfig {
    /// Run the dead code analysis.
    pub dce: bool,
    /// Run the exception analysis.
    pub exception: bool,
    /// The root of the project: the directory of its `rescript.json`.
    pub project_root: String,
    /// Path prefixes whose files are not reported on.
    pub suppress: Vec<String>,
    /// Run the termination analysis.
    pub termination: bool,
    /// Report a dead value's dead dependencies too.
    pub transitive: bool,
    /// Path prefixes reported on although they are suppressed.
    pub unsuppress: Vec<String>,
}

/// `Dce_config.cli_config` and the other flags of `Cli`.
#[derive(Debug, Clone, Default)]
pub struct CliConfig {
    /// `-debug`.
    pub debug: bool,
    /// `-ci`.
    pub ci: bool,
    /// `-json`.
    pub json: bool,
    /// `-live-names`.
    pub live_names: Vec<String>,
    /// `-live-paths`.
    pub live_paths: Vec<String>,
    /// `-exclude-paths`.
    pub exclude_paths: Vec<String>,
    /// `-externals`.
    pub analyze_externals: bool,
}

/// `Dce_config.t`.
#[derive(Debug, Clone, Default)]
pub struct Config {
    /// What to run and report.
    pub run: RunConfig,
    /// The command line's flags.
    pub cli: CliConfig,
    /// The client's working directory (`Sys.getcwd ()`).
    pub cwd: String,
}

/// `Dead_common.File_context.t`.
#[derive(Debug, Clone)]
pub struct FileContext {
    /// The source's path, as its locations name it.
    pub source_path: Arc<str>,
    /// The source's file identity.
    pub source_file: FileId,
    /// The module's name: the source's base name.
    pub module_name: String,
    /// Whether the source is an interface.
    pub is_interface: bool,
}

impl FileContext {
    /// `File_context.module_name_tagged`.
    pub fn module_name_tagged(&self) -> Name {
        name_create(&self.module_name, self.is_interface)
    }
}

/// A typed tree and what its locations are read with.
pub struct Tree<'a> {
    /// The parsed tree the typed tree was checked from.
    pub arena: &'a ParseArena,
    /// The module's type context.
    pub types: &'a TypeContext,
    /// Node storage of the typed tree.
    pub ta: &'a tt::TypedArena,
    /// The run's file names.
    pub files: &'a Files,
    file_ids: RefCell<HashMap<crate::intern::StrIdx, FileId>>,
}

impl<'a> Tree<'a> {
    /// A typed tree read with `files`.
    pub fn new(
        arena: &'a ParseArena,
        types: &'a TypeContext,
        ta: &'a tt::TypedArena,
        files: &'a Files,
    ) -> Tree<'a> {
        Tree {
            arena,
            types,
            ta,
            files,
            file_ids: RefCell::new(HashMap::new()),
        }
    }

    fn own_file(&self, file_name: crate::intern::StrIdx) -> FileId {
        if let Some(id) = self.file_ids.borrow().get(&file_name) {
            return *id;
        }
        let id = self.files.intern(self.arena.get_string(file_name));
        self.file_ids.borrow_mut().insert(file_name, id);
        id
    }

    fn own_pos(&self, pos: &crate::location::Position) -> Pos {
        Pos {
            file: self.own_file(pos.file_name),
            lnum: pos.line,
            bol: pos.bol,
            cnum: pos.cnum,
        }
    }

    /// The location at `idx` of the parsed tree.
    pub fn loc(&self, idx: LocIdx) -> Loc {
        let location = self.arena.to_location(idx);
        Loc {
            start: self.own_pos(&location.loc_start),
            end: self.own_pos(&location.loc_end),
            ghost: location.loc_ghost,
        }
    }

    /// Whether the location at `idx` is a ghost.
    pub fn loc_ghost(&self, idx: LocIdx) -> bool {
        self.arena.loc_ghost(idx)
    }

    /// A declaration's location, in this file or in the file another
    /// module declares it in. The project is built with source locations
    /// (see [`super::Analysis`]), so every declaration carries its position, as in
    /// OCaml's `.cmi`.
    pub fn decl_loc(&self, loc: DeclLoc) -> Loc {
        let location = self.types.resolve_loc(loc);
        if location.is_none() {
            return Loc::NONE;
        }
        let file_name = location.loc_start.file_name;
        let file = match self.types.resolve_cmi_longident_component(file_name) {
            Some(name) => self.files.intern(&name),
            None => self.own_file(file_name),
        };
        let pos = |p: &crate::location::Position| Pos {
            file,
            lnum: p.line,
            bol: p.bol,
            cnum: p.cnum,
        };
        Loc {
            start: pos(&location.loc_start),
            end: pos(&location.loc_end),
            ghost: location.loc_ghost,
        }
    }

    /// The text of a longident of the typed tree (`Longident.flatten`,
    /// joined with dots).
    pub fn lid_string(&self, lid: crate::parse_arena::LidentIdx) -> String {
        self.longident_string(self.arena.get_longident(lid))
    }

    /// The dotted text of `lid`.
    pub fn longident_string(&self, lid: &crate::parser::longident::Longident) -> String {
        lid.flatten_idx()
            .into_iter()
            .map(|s| self.types.resolve_longident_component(self.arena, s))
            .collect::<Vec<_>>()
            .join(".")
    }
}

/// `Module_path.t`.
#[derive(Debug, Clone)]
pub struct ModulePath {
    /// Module aliases in scope: a name and the path it stands for.
    pub aliases: std::collections::BTreeMap<Name, DcePath>,
    /// The location of the enclosing module.
    pub loc: Loc,
    /// The enclosing modules, innermost first.
    pub path: DcePath,
}

impl ModulePath {
    /// `Module_path.initial`.
    pub fn initial() -> ModulePath {
        ModulePath {
            aliases: Default::default(),
            loc: Loc::NONE,
            path: Vec::new(),
        }
    }

    /// `Module_path.enter_module`.
    pub fn enter_module(&self, name: Name, loc: Loc) -> ModulePath {
        let mut path = Vec::with_capacity(self.path.len() + 1);
        path.push(name);
        path.extend(self.path.iter().cloned());
        ModulePath {
            aliases: self.aliases.clone(),
            loc,
            path,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{DUMMY_FILE, Files, NONE_FILE};

    #[test]
    fn concurrent_interning_preserves_file_identity() {
        let files = Files::new();
        std::thread::scope(|scope| {
            for _ in 0..8 {
                scope.spawn(|| {
                    for index in 0..100 {
                        let name = format!("Module{index}.res");
                        let id = files.intern(&name);
                        assert_eq!(files.intern(&name), id);
                        assert_eq!(&*files.name(id), name);
                    }
                });
            }
        });
        assert_eq!(files.intern("_none_"), NONE_FILE);
        assert_eq!(files.intern(""), DUMMY_FILE);
        assert_eq!(files.read().len(), 102);
    }
}
