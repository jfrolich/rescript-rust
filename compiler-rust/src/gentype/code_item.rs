// Port of compiler/gentype/CodeItem.ml:1-58.

use crate::gentype::gen_type_common::{StringMap, Type, doc_string};
/// A declaration exported to TypeScript. `loc` names the declaration in the
/// location table of its owner: the translating `TypeContext`, or the
/// [`TypeDeclarations`] table once cached past that context.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct ExportType {
    /// The declaration's location.
    pub loc: crate::types::DeclLoc,
    /// The name the type is also exported under, from `@genType.as`.
    pub name_as: Option<String>,
    /// Whether the type is exported as opaque; `None` leaves it to the declaration.
    pub opaque: Option<bool>,
    /// The type the declaration defines.
    pub type_: Type,
    /// The declaration's type parameters.
    pub type_vars: Vec<String>,
    /// The declared name, qualified by its enclosing submodules.
    pub resolved_type_name: crate::gentype::resolved_name::T,
    /// The declaration's doc comment.
    pub doc_string: doc_string::T,
}

/// A value imported with `@genType.import`.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct ImportValue {
    /// The path within the imported module, such as `default` or `Foo.bar`.
    pub as_path: String,
    /// Where the value is imported from.
    pub import_annotation: crate::gentype::annotation::Import,
    /// The value's type.
    pub type_: Type,
    /// The value's name in ReScript.
    pub value_name: String,
}

/// A value exported to TypeScript.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct ExportValue {
    /// The value's doc comment.
    pub doc_string: doc_string::T,
    /// How the value is reached in the compiled JavaScript module.
    pub module_access_path: crate::gentype::runtime::ModuleAccessPath,
    /// The value's name in ReScript.
    pub original_name: String,
    /// The exported name, qualified by its enclosing submodules.
    pub resolved_name: crate::gentype::resolved_name::T,
    /// The value's type.
    pub type_: Type,
}

/// A type declaration and how it is annotated.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct ExportFromTypeDeclaration {
    /// The exported type.
    pub export_type: ExportType,
    /// The declaration's annotation.
    pub annotation: crate::gentype::annotation::T,
}

/// A type imported into the generated file.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct ImportType {
    /// The type's name in the module it is imported from.
    pub type_name: String,
    /// The name it is imported as, when that differs.
    pub as_type_name: Option<String>,
    /// Where the type is imported from.
    pub import_path: crate::gentype::import_path::T,
}

/// An exported type as other code items see it.
#[derive(Debug, Clone)]
pub struct ExportTypeItem {
    /// The type's parameters.
    pub type_vars: Vec<String>,
    /// The type's definition.
    pub type_: Type,
    /// The declaration's annotation.
    pub annotation: crate::gentype::annotation::T,
}

/// The exported types of a file, by resolved name.
pub type ExportTypeMap = StringMap<ExportTypeItem>;

/// The type declarations of one typed artifact as GenType caches them for
/// importers, with the locations their export types name (portable handles).
#[derive(Debug, Clone, Default, serde::Serialize, serde::Deserialize)]
pub struct TypeDeclarations {
    /// The declarations.
    pub declarations: Vec<TypeDeclaration>,
    /// The locations the declarations' export types refer to.
    pub locations: crate::types::DeclLocTable,
}

impl TypeDeclarations {
    /// Move `declarations` past the lifetime of the context `locs` resolves.
    ///
    /// The locations' files are renumbered in order of first use: GenType
    /// reads these locations only to report a warning, which does not print
    /// the file name (`log_::loc::print_loc`), and the indices the compiling
    /// context named them by depend on the order in which worker threads
    /// interned them, so keeping them would make the stored declarations
    /// differ from build to build.
    pub fn portable(declarations: Vec<TypeDeclaration>, locs: &dyn crate::types::DeclLocs) -> Self {
        let mut locations = crate::types::DeclLocTable::default();
        let mut files: Vec<crate::intern::StrIdx> = Vec::new();
        let mut file_key = |file: crate::intern::StrIdx| {
            if file == crate::intern::StrIdx::default() {
                return file;
            }
            let index = files
                .iter()
                .position(|seen| *seen == file)
                .unwrap_or_else(|| {
                    files.push(file);
                    files.len() - 1
                });
            crate::intern::StrIdx::from_raw(index as u32 + 1)
        };
        let declarations = declarations
            .into_iter()
            .map(|mut declaration| {
                let export_type = &mut declaration.export_from_type_declaration.export_type;
                let mut loc = locs.resolve_loc(export_type.loc);
                loc.loc_start.file_name = file_key(loc.loc_start.file_name);
                loc.loc_end.file_name = file_key(loc.loc_end.file_name);
                export_type.loc = locations.intern(loc);
                declaration
            })
            .collect();
        TypeDeclarations {
            declarations,
            locations,
        }
    }
}

/// A translated type declaration.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct TypeDeclaration {
    /// The type the declaration exports.
    pub export_from_type_declaration: ExportFromTypeDeclaration,
    /// The types its definition imports.
    pub import_types: Vec<ImportType>,
}

/// A translated value.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub enum T {
    /// A value export.
    ExportValue(ExportValue),
    /// A value import.
    ImportValue(ImportValue),
}

/// What translating a module produces.
#[derive(Debug, Clone, Default)]
pub struct Translation {
    /// The types the generated file imports.
    pub import_types: Vec<ImportType>,
    /// The values the generated file exports or imports.
    pub code_items: Vec<T>,
    /// The type declarations the generated file exports.
    pub type_declarations: Vec<TypeDeclaration>,
}
