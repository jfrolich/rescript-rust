// Port of compiler/gentype/CodeItem.ml:1-58.
// This Stage 1 GenType port is intentionally not wired into the crate yet.

use crate::gentype::gen_type_common::{StringMap, Type, doc_string};
use crate::location::Location;

#[derive(Debug, Clone)]
pub struct ExportType {
    pub loc: Location,
    pub name_as: Option<String>,
    pub opaque: Option<bool>,
    pub type_: Type,
    pub type_vars: Vec<String>,
    pub resolved_type_name: crate::gentype::resolved_name::T,
    pub doc_string: doc_string::T,
}

#[derive(Debug, Clone)]
pub struct ImportValue {
    pub as_path: String,
    pub import_annotation: crate::gentype::annotation::Import,
    pub type_: Type,
    pub value_name: String,
}

#[derive(Debug, Clone)]
pub struct ExportValue {
    pub doc_string: doc_string::T,
    pub module_access_path: crate::gentype::runtime::ModuleAccessPath,
    pub original_name: String,
    pub resolved_name: crate::gentype::resolved_name::T,
    pub type_: Type,
}

#[derive(Debug, Clone)]
pub struct ExportFromTypeDeclaration {
    pub export_type: ExportType,
    pub annotation: crate::gentype::annotation::T,
}

#[derive(Debug, Clone)]
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

#[derive(Debug, Clone)]
pub struct TypeDeclaration {
    pub export_from_type_declaration: ExportFromTypeDeclaration,
    pub import_types: Vec<ImportType>,
}

#[derive(Debug, Clone)]
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
