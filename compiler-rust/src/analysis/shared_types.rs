//! The analysis data model: a port of analysis/src/shared_types.ml.
//!
//! Types are `TypeExprRef`s into the `TypeContext` of the module they come
//! from; a [`File`] records which module that is ([`File::module`]), and
//! everything reached through a file is read in that module's context.

use super::hashtbl::Hashtbl;
use crate::types::decl::{RecStatus, TypeDeclaration};
use crate::types::{Path, TypeExprRef};
use std::sync::Arc;

pub type ModulePathList = Vec<String>;

/// A source position (`Lexing.position` without the file name).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Pos {
    pub line: i32,
    pub bol: i32,
    pub cnum: i32,
}

impl Pos {
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

/// A source location (`Location.t`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Loc {
    pub start: Pos,
    pub end: Pos,
    pub ghost: bool,
}

impl Loc {
    /// `Location.none`.
    pub fn none() -> Loc {
        let pos = Pos { line: 1, bol: 0, cnum: -1 };
        Loc {
            start: pos,
            end: pos,
            ghost: true,
        }
    }

    pub fn of_location(loc: &crate::location::Location) -> Loc {
        Loc {
            start: Pos::of_lexing(&loc.loc_start),
            end: Pos::of_lexing(&loc.loc_end),
            ghost: loc.loc_ghost,
        }
    }

    pub fn of_idx(arena: &crate::parse_arena::ParseArena, idx: crate::parse_arena::LocIdx) -> Loc {
        let location = arena.get_location(idx);
        Loc {
            start: Pos::of_lexing(arena.get_position(location.loc_start)),
            end: Pos::of_lexing(arena.get_position(location.loc_end)),
            ghost: location.loc_ghost,
        }
    }

    pub fn range(&self) -> super::Range {
        let (sl, sc) = self.start.line_col();
        let (el, ec) = self.end.line_col();
        super::Range {
            start: super::Position { line: sl, character: sc },
            end: super::Position { line: el, character: ec },
        }
    }
}

/// `string Location.loc`.
#[derive(Debug, Clone, PartialEq)]
pub struct Located<T> {
    pub txt: T,
    pub loc: Loc,
}

impl<T> Located<T> {
    /// `Location.mknoloc`.
    pub fn mknoloc(txt: T) -> Self {
        Located { txt, loc: Loc::none() }
    }
}

/// Which module of a command's session a file, and its types, belong to.
pub type ModuleId = usize;

/// `Module_path.t`.
#[derive(Debug, Clone, PartialEq)]
pub enum ModulePath {
    File { uri: String, module_name: String },
    NotVisible,
    IncludedModule(Path, Box<ModulePath>),
    ExportedModule {
        name: String,
        module_path: Box<ModulePath>,
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
                ModulePath::ExportedModule { name, module_path: inner, .. } => {
                    current.insert(0, name.clone());
                    module_path = inner;
                }
            }
        }
        current
    }

    /// `Module_path.to_path_with_prefix`.
    pub fn to_path_with_prefix(&self, prefix: &str) -> ModulePathList {
        let mut path = self.to_path("");
        path.pop();
        path.insert(0, prefix.to_string());
        path
    }
}

/// `field`.
#[derive(Debug, Clone)]
pub struct Field {
    pub stamp: i32,
    pub fname: Located<String>,
    pub typ: TypeExprRef,
    pub optional: bool,
    pub docstring: Vec<String>,
    pub deprecated: Option<String>,
}

/// `constructor_args`.
#[derive(Debug, Clone)]
pub enum ConstructorArgs {
    InlineRecord(Vec<Field>),
    Args(Vec<(TypeExprRef, Loc)>),
}

/// `Constructor.t`.
#[derive(Debug, Clone)]
pub struct Constructor {
    pub stamp: i32,
    pub cname: Located<String>,
    pub args: ConstructorArgs,
    pub res: Option<TypeExprRef>,
    pub type_decl: (String, Arc<TypeDeclaration>),
    pub docstring: Vec<String>,
    pub deprecated: Option<String>,
}

/// `Type.kind`.
#[derive(Debug, Clone)]
pub enum TypeKind {
    Abstract(Option<(Path, Vec<TypeExprRef>)>),
    Open,
    Tuple(Vec<TypeExprRef>),
    Record(Vec<Field>),
    Variant(Vec<Constructor>),
}

/// `Type.t`. OCaml keeps the declaration's attributes, which the analysis
/// only reads for `@editor.completeFrom`; that list is kept instead.
#[derive(Debug, Clone)]
pub struct Type {
    pub kind: TypeKind,
    pub decl: Arc<TypeDeclaration>,
    pub name: String,
    pub editor_complete_from: Vec<ModulePathList>,
}

/// `Exported.kind`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExportedKind {
    Type,
    Value,
    Module,
}

/// `Exported.t`.
#[derive(Debug, Clone)]
pub struct Exported {
    pub types: Hashtbl<String, i32>,
    pub values: Hashtbl<String, i32>,
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
        let name = name.to_string();
        if table.mem(&name) {
            false
        } else {
            table.add(name, stamp);
            true
        }
    }

    pub fn find(&self, kind: ExportedKind, name: &str) -> Option<i32> {
        self.table(kind).find(&name.to_string()).copied()
    }

    pub fn iter(&self, kind: ExportedKind) -> impl Iterator<Item = (&String, &i32)> {
        self.table(kind).iter()
    }
}

/// `Module.kind`.
#[derive(Debug, Clone)]
pub enum ModuleItemKind {
    Value(TypeExprRef),
    Type(Type, RecStatus),
    Module { type_: Module, is_module_type: bool },
}

/// `Module.item`.
#[derive(Debug, Clone)]
pub struct ModuleItem {
    pub kind: ModuleItemKind,
    pub name: String,
    pub loc: Loc,
    pub docstring: Vec<String>,
    pub deprecated: Option<String>,
}

/// `Module.structure`.
#[derive(Debug, Clone)]
pub struct Structure {
    pub name: String,
    pub docstring: Vec<String>,
    pub exported: Exported,
    pub items: Vec<ModuleItem>,
    pub deprecated: Option<String>,
}

/// `Module.t`.
#[derive(Debug, Clone)]
pub enum Module {
    Ident(Path),
    Structure(Box<Structure>),
    Constraint(Box<Module>, Box<Module>),
}

/// `Declared.t`.
#[derive(Debug, Clone)]
pub struct Declared<T> {
    pub name: Located<String>,
    pub extent_loc: Loc,
    pub stamp: i32,
    pub module_path: ModulePath,
    pub is_exported: bool,
    pub deprecated: Option<String>,
    pub docstring: Vec<String>,
    pub item: T,
}

/// `Stamps.kind`.
#[derive(Debug, Clone)]
pub enum StampKind {
    Type(Declared<Type>),
    Value(Declared<TypeExprRef>),
    Module(Declared<Module>),
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
    pub fn add_constructor(&mut self, stamp: i32, declared: Declared<Constructor>) {
        self.0.add(stamp, StampKind::Constructor(declared));
    }

    pub fn add_module(&mut self, stamp: i32, declared: Declared<Module>) {
        self.0.add(stamp, StampKind::Module(declared));
    }

    pub fn add_type(&mut self, stamp: i32, declared: Declared<Type>) {
        self.0.add(stamp, StampKind::Type(declared));
    }

    pub fn add_value(&mut self, stamp: i32, declared: Declared<TypeExprRef>) {
        self.0.add(stamp, StampKind::Value(declared));
    }

    pub fn find_module(&self, stamp: i32) -> Option<&Declared<Module>> {
        match self.0.find(&stamp) {
            Some(StampKind::Module(d)) => Some(d),
            _ => None,
        }
    }

    pub fn find_type(&self, stamp: i32) -> Option<&Declared<Type>> {
        match self.0.find(&stamp) {
            Some(StampKind::Type(d)) => Some(d),
            _ => None,
        }
    }

    pub fn find_value(&self, stamp: i32) -> Option<&Declared<TypeExprRef>> {
        match self.0.find(&stamp) {
            Some(StampKind::Value(d)) => Some(d),
            _ => None,
        }
    }

    pub fn find_constructor(&self, stamp: i32) -> Option<&Declared<Constructor>> {
        match self.0.find(&stamp) {
            Some(StampKind::Constructor(d)) => Some(d),
            _ => None,
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = (&i32, &StampKind)> {
        self.0.iter()
    }
}

/// `File.t`.
#[derive(Debug, Clone)]
pub struct File {
    pub uri: String,
    pub stamps: Stamps,
    pub module_name: String,
    pub structure: Structure,
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
            structure: Structure {
                name: module_name.to_string(),
                docstring: Vec::new(),
                exported: Exported::default(),
                items: Vec::new(),
                deprecated: None,
            },
            module,
        }
    }
}

/// `Shared_types.Env.t`, used while processing a typed tree.
#[derive(Debug, Clone)]
pub struct ProcessEnv {
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

    pub fn add_module(&self, name: &str) -> ProcessEnv {
        self.add_exported_module(name, false)
    }

    pub fn add_module_type(&self, name: &str) -> ProcessEnv {
        self.add_exported_module(name, true)
    }
}

/// `Tip.t`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Tip {
    Value,
    Type,
    Field(String),
    Constructor(String),
    Module,
}

impl Tip {
    pub fn to_string(&self) -> String {
        match self {
            Tip::Value => "Value".to_string(),
            Tip::Type => "Type".to_string(),
            Tip::Field(f) => format!("Field({f})"),
            Tip::Constructor(a) => format!("Constructor({a})"),
            Tip::Module => "Module".to_string(),
        }
    }
}

/// `loc_kind`.
#[derive(Debug, Clone, PartialEq)]
pub enum LocKind {
    LocalReference(i32, Tip),
    GlobalReference(String, ModulePathList, Tip),
    NotFound,
    Definition(i32, Tip),
}

/// `loc_type`.
#[derive(Debug, Clone)]
pub enum LocType {
    Typed(String, TypeExprRef, LocKind),
    Constant(crate::types::typedtree::Constant),
    LModule(LocKind),
    TopLevelModule(String),
    TypeDefinition(String, Arc<TypeDeclaration>, i32),
}

/// `loc_item`.
#[derive(Debug, Clone)]
pub struct LocItem {
    pub loc: Loc,
    pub loc_type: LocType,
}
