// Port of compiler/gentype/CodeItem.ml:1-58.

use crate::gentype::gen_type_common::{StringMap, Type, doc_string};
/// A declaration exported to TypeScript. `loc` names the declaration in the
/// location table of its owner: the translating `TypeContext`, or the
/// [`TypeDeclarations`] table once cached past that context.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct ExportType {
    pub loc: crate::types::DeclLoc,
    pub name_as: Option<String>,
    pub opaque: Option<bool>,
    pub type_: Type,
    pub type_vars: Vec<String>,
    pub resolved_type_name: crate::gentype::resolved_name::T,
    pub doc_string: doc_string::T,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct ImportValue {
    pub as_path: String,
    pub import_annotation: crate::gentype::annotation::Import,
    pub type_: Type,
    pub value_name: String,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct ExportValue {
    pub doc_string: doc_string::T,
    pub module_access_path: crate::gentype::runtime::ModuleAccessPath,
    pub original_name: String,
    pub resolved_name: crate::gentype::resolved_name::T,
    pub type_: Type,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct ExportFromTypeDeclaration {
    pub export_type: ExportType,
    pub annotation: crate::gentype::annotation::T,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct ImportType {
    pub type_name: String,
    pub as_type_name: Option<String>,
    pub import_path: crate::gentype::import_path::T,
}

#[derive(Debug, Clone)]
pub struct ExportTypeItem {
    pub type_vars: Vec<String>,
    pub type_: Type,
    pub annotation: crate::gentype::annotation::T,
}

pub type ExportTypeMap = StringMap<ExportTypeItem>;

/// The type declarations of one typed artifact as GenType caches them for
/// importers, with the locations their export types name (portable handles).
#[derive(Debug, Clone, Default, serde::Serialize, serde::Deserialize)]
pub struct TypeDeclarations {
    pub declarations: Vec<TypeDeclaration>,
    pub locations: crate::types::DeclLocTable,
}

impl TypeDeclarations {
    /// Move `declarations` past the lifetime of the context `locs` resolves.
    pub fn portable(declarations: Vec<TypeDeclaration>, locs: &dyn crate::types::DeclLocs) -> Self {
        let mut locations = crate::types::DeclLocTable::default();
        let declarations = declarations
            .into_iter()
            .map(|mut declaration| {
                let export_type = &mut declaration.export_from_type_declaration.export_type;
                export_type.loc = locations.intern(locs.resolve_loc(export_type.loc));
                declaration
            })
            .collect();
        TypeDeclarations {
            declarations,
            locations,
        }
    }
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct TypeDeclaration {
    pub export_from_type_declaration: ExportFromTypeDeclaration,
    pub import_types: Vec<ImportType>,
}

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub enum T {
    ExportValue(ExportValue),
    ImportValue(ImportValue),
}

#[derive(Debug, Clone, Default)]
pub struct Translation {
    pub import_types: Vec<ImportType>,
    pub code_items: Vec<T>,
    pub type_declarations: Vec<TypeDeclaration>,
}
