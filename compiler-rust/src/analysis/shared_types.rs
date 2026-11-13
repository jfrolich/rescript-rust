//! The analysis data model: a port of analysis/src/shared_types.ml.
//!
//! Types are `TypeExprRef`s into the `TypeContext` of the module they come
//! from; a [`File`] records which module that is ([`File::module`]), and
//! everything reached through a file is read in that module's context.

use super::hashtbl::Hashtbl;
use crate::types::decl::{RecStatus, TypeDeclaration};
use crate::types::{Path, TypeExprRef};
use std::sync::Arc;

/// A module path as its names, outermost first.
pub type ModulePathList = Vec<String>;

/// A source position (`Lexing.position` without the file name).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Pos {
    /// The 1-based line.
    pub line: i32,
    /// The offset of the line's first character.
    pub bol: i32,
    /// The offset of the position.
    pub cnum: i32,
}

impl Pos {
    /// The position of a lexer position.
    pub fn of_lexing(pos: &crate::location::Position) -> Pos {
        Pos {
            line: pos.line,
            bol: pos.bol,
            cnum: pos.cnum,
        }
    }

    /// `Pos.of_lexing`: 0-based line and column.
    pub fn line_col(self) -> (i32, i32) {
        (self.line - 1, self.cnum - self.bol)
    }
}

/// A source location (`Location.t`). The derived order is OCaml's
/// polymorphic compare on the record, file names aside.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Loc {
    /// Where the location starts.
    pub start: Pos,
    /// Where the location ends.
    pub end: Pos,
    /// Whether the location is synthesized rather than in the source.
    pub ghost: bool,
}

impl Loc {
    /// `Location.none`.
    pub fn none() -> Loc {
        let pos = Pos {
            line: 1,
            bol: 0,
            cnum: -1,
        };
        Loc {
            start: pos,
            end: pos,
            ghost: true,
        }
    }

    /// The location of a compiler location.
    pub fn of_location(loc: &crate::location::Location) -> Loc {
        Loc {
            start: Pos::of_lexing(&loc.loc_start),
            end: Pos::of_lexing(&loc.loc_end),
            ghost: loc.loc_ghost,
        }
    }

    /// The location at `idx` in `arena`.
    pub fn of_idx(arena: &crate::parse_arena::ParseArena, idx: crate::parse_arena::LocIdx) -> Loc {
        let location = arena.get_location(idx);
        Loc {
            start: Pos::of_lexing(arena.get_position(location.loc_start)),
            end: Pos::of_lexing(arena.get_position(location.loc_end)),
            ghost: location.loc_ghost,
        }
    }

    /// `Utils.end_of_location`: the last `length` characters.
    pub fn end_of_location(&self, length: i32) -> Loc {
        Loc {
            start: Pos {
                cnum: self.end.cnum - length,
                ..self.end
            },
            ..*self
        }
    }

    /// `Utils.chop_location_end`: drop the last `length` characters.
    pub fn chop_location_end(&self, length: i32) -> Loc {
        Loc {
            end: Pos {
                cnum: self.end.cnum - length,
                ..self.end
            },
            ..*self
        }
    }

    /// `Utils.cmt_loc_to_range`: the location as an LSP range.
    pub fn range(&self) -> super::Range {
        let (sl, sc) = self.start.line_col();
        let (el, ec) = self.end.line_col();
        super::Range {
            start: super::Position {
                line: sl,
                character: sc,
            },
            end: super::Position {
                line: el,
                character: ec,
            },
        }
    }
}

/// `string Location.loc`.
#[derive(Debug, Clone, PartialEq)]
pub struct Located<T> {
    /// The value.
    pub txt: T,
    /// Where it is in the source.
    pub loc: Loc,
}

impl<T> Located<T> {
    /// `Location.mknoloc`.
    pub fn mknoloc(txt: T) -> Self {
        Located {
            txt,
            loc: Loc::none(),
        }
    }
}

/// Which module of a command's session a file, and its types, belong to.
pub type ModuleId = usize;

/// `Module_path.t`.
#[derive(Debug, Clone, PartialEq)]
pub enum ModulePath {
    /// The toplevel module of a file.
    File {
        /// The file's URI.
        uri: String,
        /// The module's name.
        module_name: String,
    },
    /// Not reachable by a path from the file's toplevel.
    NotVisible,
    /// Included into the module described by the inner path, from the module at the given path.
    IncludedModule(Path, Box<ModulePath>),
    /// A submodule or module type, exported by its enclosing module.
    ExportedModule {
        /// The submodule's name.
        name: String,
        /// Where the enclosing module is.
        module_path: Box<ModulePath>,
        /// Whether it is a module type rather than a module.
        is_type: bool,
    },
}

impl ModulePath {
    /// `Module_path.to_path`.
    pub fn to_path(&self, tip_name: &str) -> ModulePathList {
        let mut current = vec![tip_name.to_string()];
        let mut module_path = self;
        loop {
            match module_path {
                ModulePath::File { .. } | ModulePath::NotVisible => break,
                ModulePath::IncludedModule(_, inner) => module_path = inner,
                ModulePath::ExportedModule {
                    name,
                    module_path: inner,
                    ..
                } => {
                    current.insert(0, name.clone());
                    module_path = inner;
                }
            }
        }
        current
    }
}

/// `field`.
#[derive(Debug, Clone)]
pub struct Field {
    /// The field's identifier stamp.
    pub stamp: i32,
    /// The field's name.
    pub fname: Located<String>,
    /// The field's type.
    pub typ: TypeExprRef,
    /// Whether the field is optional (`?`).
    pub optional: bool,
    /// The field's doc comments.
    pub docstring: Vec<String>,
    /// The `@deprecated` reason, if the field is deprecated.
    pub deprecated: Option<String>,
}

/// `constructor_args`.
#[derive(Debug, Clone)]
pub enum ConstructorArgs {
    /// An inline record argument.
    InlineRecord(Vec<Field>),
    /// Positional arguments, each with its location.
    Args(Vec<(TypeExprRef, Loc)>),
}

/// `Constructor.t`.
#[derive(Debug, Clone)]
pub struct Constructor {
    /// The constructor's identifier stamp.
    pub stamp: i32,
    /// The constructor's name.
    pub cname: Located<String>,
    /// The constructor's arguments.
    pub args: ConstructorArgs,
    /// The result type of a GADT constructor.
    pub res: Option<TypeExprRef>,
    /// The name and declaration of the type the constructor belongs to.
    pub type_decl: (String, Arc<TypeDeclaration>),
    /// The constructor's doc comments.
    pub docstring: Vec<String>,
    /// The `@deprecated` reason, if the constructor is deprecated.
    pub deprecated: Option<String>,
}

/// `Type.kind`.
#[derive(Debug, Clone)]
pub enum TypeKind {
    /// An abstract type, with the constructor and arguments of its manifest
    /// when that is a type constructor.
    Abstract(Option<(Path, Vec<TypeExprRef>)>),
    /// An extensible variant (`..`).
    Open,
    /// An abbreviation of a tuple type, with its components.
    Tuple(Vec<TypeExprRef>),
    /// A record, with its fields.
    Record(Vec<Field>),
    /// A variant, with its constructors.
    Variant(Vec<Constructor>),
}

/// `Type.t`. OCaml keeps the declaration's attributes, which the analysis
/// only reads for `@editor.completeFrom`; that list is kept instead.
#[derive(Debug, Clone)]
pub struct Type {
    /// What the type defines.
    pub kind: TypeKind,
    /// The type's declaration.
    pub decl: Arc<TypeDeclaration>,
    /// The type's name.
    pub name: String,
    /// The module paths of its `@editor.completeFrom` attributes.
    pub editor_complete_from: Vec<ModulePathList>,
}

/// `Exported.kind`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExportedKind {
    /// A type, or a field or constructor of one.
    Type,
    /// A value.
    Value,
    /// A module or module type.
    Module,
}

/// `Exported.t`.
#[derive(Debug, Clone)]
pub struct Exported {
    /// The exported types' stamps, by name.
    pub types: Hashtbl<String, i32>,
    /// The exported values' stamps, by name.
    pub values: Hashtbl<String, i32>,
    /// The exported modules' stamps, by name.
    pub modules: Hashtbl<String, i32>,
}

impl Default for Exported {
    fn default() -> Self {
        Exported {
            types: Hashtbl::create(10),
            values: Hashtbl::create(10),
            modules: Hashtbl::create(10),
        }
    }
}

impl Exported {
    fn table(&self, kind: ExportedKind) -> &Hashtbl<String, i32> {
        match kind {
            ExportedKind::Type => &self.types,
            ExportedKind::Value => &self.values,
            ExportedKind::Module => &self.modules,
        }
    }

    /// `Exported.add`: false when the name is already exported.
    pub fn add(&mut self, kind: ExportedKind, name: &str, stamp: i32) -> bool {
        let table = match kind {
            ExportedKind::Type => &mut self.types,
            ExportedKind::Value => &mut self.values,
            ExportedKind::Module => &mut self.modules,
        };
        if table.mem(name) {
            false
        } else {
            table.add(name.to_string(), stamp);
            true
        }
    }

    /// `Exported.find`: the stamp of `name` exported as `kind`.
    pub fn find(&self, kind: ExportedKind, name: &str) -> Option<i32> {
        self.table(kind).find(name).copied()
    }

    /// `Exported.iter`: the names exported as `kind`, with their stamps.
    pub fn iter(&self, kind: ExportedKind) -> impl Iterator<Item = (&String, &i32)> {
        self.table(kind).iter()
    }
}

/// `Module.kind`.
#[derive(Debug, Clone)]
pub enum ModuleItemKind {
    /// A value, of this type.
    Value(TypeExprRef),
    /// A type declaration, and whether it is recursive.
    Type(Type, RecStatus),
    /// A module or module type.
    Module {
        /// The module.
        type_: Module,
        /// Whether it is a module type.
        is_module_type: bool,
    },
}

/// `Module.item`.
#[derive(Debug, Clone)]
pub struct ModuleItem {
    /// What the item is.
    pub kind: ModuleItemKind,
    /// The item's name.
    pub name: String,
    /// The item's location.
    pub loc: Loc,
    /// The name of the file the item's location is in (`pos_fname`): the
    /// declaring file for an item of an `include`, `_none_` for a generated
    /// one.
    pub file: Arc<str>,
    /// The item's doc comments.
    pub docstring: Vec<String>,
    /// The `@deprecated` reason, if the item is deprecated.
    pub deprecated: Option<String>,
}

/// `Module.structure`.
#[derive(Debug, Clone)]
pub struct Structure {
    /// The module's name.
    pub name: String,
    /// The module's doc comments.
    pub docstring: Vec<String>,
    /// The names the module exports.
    pub exported: Arc<Exported>,
    /// The module's items, in source order.
    pub items: Vec<ModuleItem>,
    /// The `@deprecated` reason, if the module is deprecated.
    pub deprecated: Option<String>,
}

/// `Module.t`.
#[derive(Debug, Clone)]
pub enum Module {
    /// A module given by its path.
    Ident(Path),
    /// A module given by its structure.
    Structure(Arc<Structure>),
    /// A module constrained by a module type: the module, then the type.
    Constraint(Box<Module>, Box<Module>),
}

/// A declaration's location and the name of the file it is in.
#[derive(Debug, Clone)]
pub struct Extent {
    /// The location.
    pub loc: Loc,
    /// The file name of its start (`pos_fname`).
    pub file: Arc<str>,
}

/// `Declared.t`.
#[derive(Debug, Clone)]
pub struct Declared<T> {
    /// The declared name and its location.
    pub name: Located<String>,
    /// The location of the whole declaration.
    pub extent_loc: Loc,
    /// The name of the file `extent_loc` is in.
    pub extent_file: Arc<str>,
    /// The identifier stamp.
    pub stamp: i32,
    /// Where the declaration is.
    pub module_path: ModulePath,
    /// Whether the declaration is exported (not shadowed by a later one).
    pub is_exported: bool,
    /// The `@deprecated` reason, if the declaration is deprecated.
    pub deprecated: Option<String>,
    /// The declaration's doc comments.
    pub docstring: Vec<String>,
    /// What is declared.
    pub item: T,
}

/// `Stamps.kind`.
#[derive(Debug, Clone)]
pub enum StampKind {
    /// A type declaration.
    Type(Declared<Type>),
    /// A value, with its type.
    Value(Declared<TypeExprRef>),
    /// A module.
    Module(Declared<Module>),
    /// A variant constructor.
    Constructor(Declared<Constructor>),
}

impl StampKind {
    /// `Stamps.loc_of_kind`.
    pub fn loc(&self) -> Loc {
        match self {
            StampKind::Type(d) => d.extent_loc,
            StampKind::Value(d) => d.extent_loc,
            StampKind::Module(d) => d.extent_loc,
            StampKind::Constructor(d) => d.extent_loc,
        }
    }
}

/// `Stamps.t`.
#[derive(Debug, Clone)]
pub struct Stamps(pub Hashtbl<i32, StampKind>);

impl Default for Stamps {
    fn default() -> Self {
        Stamps(Hashtbl::create(10))
    }
}

impl Stamps {
    /// `Stamps.add_constructor`.
    pub fn add_constructor(&mut self, stamp: i32, declared: Declared<Constructor>) {
        self.0.add(stamp, StampKind::Constructor(declared));
    }

    /// `Stamps.add_module`.
    pub fn add_module(&mut self, stamp: i32, declared: Declared<Module>) {
        self.0.add(stamp, StampKind::Module(declared));
    }

    /// `Stamps.add_type`.
    pub fn add_type(&mut self, stamp: i32, declared: Declared<Type>) {
        self.0.add(stamp, StampKind::Type(declared));
    }

    /// `Stamps.add_value`.
    pub fn add_value(&mut self, stamp: i32, declared: Declared<TypeExprRef>) {
        self.0.add(stamp, StampKind::Value(declared));
    }

    /// `Stamps.find_module`.
    pub fn find_module(&self, stamp: i32) -> Option<&Declared<Module>> {
        match self.0.find(&stamp) {
            Some(StampKind::Module(d)) => Some(d),
            _ => None,
        }
    }

    /// `Stamps.find_type`.
    pub fn find_type(&self, stamp: i32) -> Option<&Declared<Type>> {
        match self.0.find(&stamp) {
            Some(StampKind::Type(d)) => Some(d),
            _ => None,
        }
    }

    /// `Stamps.find_value`.
    pub fn find_value(&self, stamp: i32) -> Option<&Declared<TypeExprRef>> {
        match self.0.find(&stamp) {
            Some(StampKind::Value(d)) => Some(d),
            _ => None,
        }
    }

    /// Every stamp and its declaration, in the table's iteration order.
    pub fn iter(&self) -> impl Iterator<Item = (&i32, &StampKind)> {
        self.0.iter()
    }
}

/// `File.t`.
#[derive(Debug, Clone)]
pub struct File {
    /// The file's URI.
    pub uri: String,
    /// The file's declarations, by stamp.
    pub stamps: Stamps,
    /// The file's module name.
    pub module_name: String,
    /// The file's toplevel structure.
    pub structure: Arc<Structure>,
    /// The session module whose type context the file's types live in.
    pub module: ModuleId,
}

impl File {
    /// `File.create`.
    pub fn create(module_name: &str, uri: String, module: ModuleId) -> File {
        File {
            uri,
            stamps: Stamps::default(),
            module_name: module_name.to_string(),
            structure: Arc::new(Structure {
                name: module_name.to_string(),
                docstring: Vec::new(),
                exported: Arc::new(Exported::default()),
                items: Vec::new(),
                deprecated: None,
            }),
            module,
        }
    }
}

/// `Shared_types.Env.t`, used while processing a typed tree.
#[derive(Debug, Clone)]
pub struct ProcessEnv {
    /// Where the items being processed are.
    pub module_path: ModulePath,
}

impl ProcessEnv {
    /// `Env.add_exported_module`.
    pub fn add_exported_module(&self, name: &str, is_type: bool) -> ProcessEnv {
        ProcessEnv {
            module_path: ModulePath::ExportedModule {
                name: name.to_string(),
                module_path: Box::new(self.module_path.clone()),
                is_type,
            },
        }
    }

    /// `Env.add_module`: enter submodule `name`.
    pub fn add_module(&self, name: &str) -> ProcessEnv {
        self.add_exported_module(name, false)
    }

    /// `Env.add_module_type`: enter module type `name`.
    pub fn add_module_type(&self, name: &str) -> ProcessEnv {
        self.add_exported_module(name, true)
    }
}

/// `Tip.t`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Tip {
    /// A value.
    Value,
    /// A type.
    Type,
    /// A record field, by name.
    Field(String),
    /// A variant constructor, by name.
    Constructor(String),
    /// A module.
    Module,
}

/// `loc_kind`.
#[derive(Debug, Clone, PartialEq)]
pub enum LocKind {
    /// A reference to a declaration in this file, by stamp.
    LocalReference(i32, Tip),
    /// A reference into another module: its name, the path within it, and what
    /// is referenced.
    GlobalReference(String, ModulePathList, Tip),
    /// A reference that could not be resolved.
    NotFound,
    /// A declaration's own name, by stamp.
    Definition(i32, Tip),
}

/// `loc_type`.
#[derive(Debug, Clone)]
pub enum LocType {
    /// An expression, pattern or identifier: its name, type and what it refers to.
    Typed(String, TypeExprRef, LocKind),
    /// A constant.
    Constant(crate::types::typedtree::Constant),
    /// A module path.
    LModule(LocKind),
    /// A toplevel module, by name.
    TopLevelModule(String),
    /// A type declaration's name: the name, the declaration and its stamp.
    TypeDefinition(String, Arc<TypeDeclaration>, i32),
}

/// `loc_item`.
#[derive(Debug, Clone)]
pub struct LocItem {
    /// The location.
    pub loc: Loc,
    /// What is at the location.
    pub loc_type: LocType,
}

/// `Query_env.t`. The file is named by its session module id rather than
/// held, so a file's stamps can grow while environments over it exist (as
/// OCaml's mutable stamp tables do).
#[derive(Debug, Clone)]
pub struct QueryEnv {
    /// The session module of the file the environment is in.
    pub file: ModuleId,
    /// That file's module name.
    pub file_module_name: String,
    /// The names the current module exports.
    pub exported: Arc<Exported>,
    /// The path of the current module within the file, innermost first.
    pub path_rev: Vec<String>,
    /// The environment of the enclosing module.
    pub parent: Option<Box<QueryEnv>>,
}

impl QueryEnv {
    /// `Query_env.from_file`.
    pub fn from_file(file: &File) -> QueryEnv {
        QueryEnv {
            file: file.module,
            file_module_name: file.module_name.clone(),
            exported: file.structure.exported.clone(),
            path_rev: Vec::new(),
            parent: None,
        }
    }

    /// `prune_path`: `path_rev` is this env's path, or a suffix of it while
    /// walking up the parents.
    fn prune_path(path_rev: &[String], env: &QueryEnv, name: &str) -> (bool, Vec<String>) {
        if env.exported.find(ExportedKind::Module, name).is_some() {
            (true, path_rev.to_vec())
        } else {
            match (path_rev.split_first(), &env.parent) {
                (Some((_, rest)), Some(parent)) => QueryEnv::prune_path(rest, parent, name),
                _ => (false, Vec::new()),
            }
        }
    }

    /// `Query_env.path_from_env`.
    pub fn path_from_env(&self, path: &[String]) -> (bool, ModulePathList) {
        match path.first() {
            None => (true, self.path_rev.iter().rev().cloned().collect()),
            Some(name) => {
                let (found, pruned_path_rev) = QueryEnv::prune_path(&self.path_rev, self, name);
                let mut result: Vec<String> = pruned_path_rev.into_iter().rev().collect();
                result.extend(path.iter().cloned());
                (found, result)
            }
        }
    }

    /// `Query_env.enter_structure`.
    pub fn enter_structure(&self, structure: &Structure) -> QueryEnv {
        let mut path_rev = vec![structure.name.clone()];
        path_rev.extend(QueryEnv::prune_path(&self.path_rev, self, &structure.name).1);
        QueryEnv {
            file: self.file,
            file_module_name: self.file_module_name.clone(),
            exported: structure.exported.clone(),
            path_rev,
            parent: Some(Box::new(self.clone())),
        }
    }
}

/// `Query_env.to_string`.
impl std::fmt::Display for QueryEnv {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.file_module_name)?;
        for part in self.path_rev.iter().rev() {
            write!(f, ".{part}")?;
        }
        Ok(())
    }
}

/// `Location_set`: OCaml orders it by the reversed compare.
pub type LocationSet = std::collections::BTreeSet<std::cmp::Reverse<Loc>>;

/// `extra`.
#[derive(Debug, Clone)]
pub struct Extra {
    /// Each list oldest first: the reverse of OCaml's consed list.
    pub internal_references: Hashtbl<i32, Vec<Loc>>,
    /// Each list oldest first: the reverse of OCaml's consed list.
    pub external_references: Hashtbl<String, Vec<(ModulePathList, Tip, Loc)>>,
    /// For each module the file mentions, where it is mentioned.
    pub file_references: Hashtbl<String, LocationSet>,
    /// In insertion order: the reverse of OCaml's consed list.
    pub loc_items: Vec<LocItem>,
}

impl Default for Extra {
    /// `init_extra`.
    fn default() -> Self {
        Extra {
            internal_references: Hashtbl::create(10),
            external_references: Hashtbl::create(10),
            file_references: Hashtbl::create(10),
            loc_items: Vec::new(),
        }
    }
}
