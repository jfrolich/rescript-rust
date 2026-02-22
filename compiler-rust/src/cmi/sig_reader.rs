//! Signature reader: converts generic OCaml marshal values into Rust type structures.
//!
//! This module interprets the `Types.signature_item list` from a CMI file and
//! converts it into the Rust equivalents defined in `types/decl.rs`.
//!
//! # OCaml Type Tags
//!
//! Each OCaml variant constructor gets an integer tag assigned in definition order.
//! Records are blocks with tag 0. See the tag tables in the module-level comments below.

use crate::ident::Ident;
use crate::location::Location;
use crate::types::asttypes::{ArgLabel, Located, MutableFlag, PrivateFlag};
use crate::types::context::TypeContext;
use crate::types::decl::{
    AliasPresence, Attribute, ConstructorArguments, ConstructorDeclaration,
    ExtStatus, ExtensionConstructor, LabelDeclaration, ModtypeDeclaration, ModuleDeclaration,
    ModuleType, PrimitiveDescription, RecStatus, RecordRepresentation, Signature, SignatureItem,
    TypeDeclaration, TypeKind, UnboxedStatus, ValueDescription, ValueKind,
};
use crate::types::path::Path;
use crate::types::type_expr::{
    Commutable, FieldKind, RowDesc, RowField, TypeArg, TypeDesc, TypeExprRef,
    GENERIC_LEVEL,
};
use crate::types::variance::Variance;

use super::marshal_reader::OcamlValue;

use std::collections::HashMap;

/// Context for reading signatures, holding the type arena and a table for
/// resolving shared type_expr references.
pub struct SigReadContext<'a> {
    /// The type context for allocating type expressions.
    pub ctx: &'a TypeContext<'a>,
    /// Map from OCaml type_expr id to TypeExprRef, for shared type references.
    type_expr_cache: HashMap<i64, TypeExprRef>,
}

impl<'a> SigReadContext<'a> {
    /// Create a new signature reading context.
    pub fn new(ctx: &'a TypeContext<'a>) -> Self {
        SigReadContext {
            ctx,
            type_expr_cache: HashMap::new(),
        }
    }

    /// Read a complete signature (list of signature items).
    pub fn read_signature(&mut self, items: &[OcamlValue]) -> Signature {
        items.iter().map(|item| self.read_signature_item(item)).collect()
    }

    /// Read a signature item.
    ///
    /// All constructors take arguments (non-constant), so all are Block tags:
    /// Block(0): Sig_value(Ident.t, value_description)
    /// Block(1): Sig_type(Ident.t, type_declaration, rec_status)
    /// Block(2): Sig_typext(Ident.t, extension_constructor, ext_status)
    /// Block(3): Sig_module(Ident.t, module_declaration, rec_status)
    /// Block(4): Sig_modtype(Ident.t, modtype_declaration)
    /// Block(5): Sig_class(unit)
    /// Block(6): Sig_class_type(unit)
    fn read_signature_item(&mut self, value: &OcamlValue) -> SignatureItem {
        match value {
            OcamlValue::Block(tag, fields) => match tag {
                0 => {
                    let id = read_ident(&fields[0]);
                    let desc = self.read_value_description(&fields[1]);
                    SignatureItem::SigValue(id, desc)
                }
                1 => {
                    let id = read_ident(&fields[0]);
                    let decl = self.read_type_declaration(&fields[1]);
                    let rec_status = read_rec_status(&fields[2]);
                    SignatureItem::SigType(id, decl, rec_status)
                }
                2 => {
                    let id = read_ident(&fields[0]);
                    let ext = self.read_extension_constructor(&fields[1]);
                    let ext_status = read_ext_status(&fields[2]);
                    SignatureItem::SigTypext(id, ext, ext_status)
                }
                3 => {
                    let id = read_ident(&fields[0]);
                    let decl = self.read_module_declaration(&fields[1]);
                    let rec_status = read_rec_status(&fields[2]);
                    SignatureItem::SigModule(id, decl, rec_status)
                }
                4 => {
                    let id = read_ident(&fields[0]);
                    let decl = self.read_modtype_declaration(&fields[1]);
                    SignatureItem::SigModtype(id, decl)
                }
                5 => SignatureItem::SigClass,
                6 => SignatureItem::SigClassType,
                _ => panic!("unknown signature_item tag: {}", tag),
            },
            _ => panic!("unexpected signature_item format: {:?}", value),
        }
    }

    /// Read a value_description.
    ///
    /// Record fields (tag 0):
    /// 0: val_type: type_expr
    /// 1: val_kind: value_kind
    /// 2: val_loc: Location.t
    /// 3: val_attributes: attributes
    fn read_value_description(&mut self, value: &OcamlValue) -> ValueDescription {
        let fields = &value.as_block().1;
        let val_type = self.read_type_expr(&fields[0]);
        let val_kind = self.read_value_kind(&fields[1]);
        let _val_loc = read_location(&fields[2]);
        let _val_attributes = read_attributes(&fields[3]);

        ValueDescription {
            val_type,
            val_kind,
            val_loc: Location::none(), // Use none for CMI-loaded items
            val_attributes: vec![],    // Skip complex attribute deserialization for now
            val_path: None,
        }
    }

    /// Read a value_kind.
    ///
    /// Val_reg is constant (Int(0)), Val_prim is the only non-constant (Block(0)).
    fn read_value_kind(&mut self, value: &OcamlValue) -> ValueKind {
        match value {
            OcamlValue::Int(0) => ValueKind::ValReg,
            OcamlValue::Block(0, fields) => {
                let prim = read_primitive_description(&fields[0]);
                ValueKind::ValPrim(prim)
            }
            _ => ValueKind::ValReg, // fallback
        }
    }

    /// Read a type_declaration.
    ///
    /// Record fields (tag 0):
    ///  0: type_params: type_expr list
    ///  1: type_arity: int
    ///  2: type_kind: type_kind
    ///  3: type_private: private_flag
    ///  4: type_manifest: type_expr option
    ///  5: type_variance: Variance.t list (int list)
    ///  6: type_newtype_level: (int * int) option
    ///  7: type_loc: Location.t
    ///  8: type_attributes: attributes
    ///  9: type_immediate: bool
    /// 10: type_unboxed: unboxed_status
    /// 11: type_inlined_types: type_inlined_type list
    fn read_type_declaration(&mut self, value: &OcamlValue) -> TypeDeclaration {
        let fields = &value.as_block().1;

        let type_params: Vec<TypeExprRef> = fields[0]
            .as_list()
            .iter()
            .map(|te| self.read_type_expr(te))
            .collect();
        let type_arity = fields[1].as_int() as i32;
        let type_kind = self.read_type_kind(&fields[2]);
        let type_private = read_private_flag(&fields[3]);
        let type_manifest = fields[4].as_option().map(|te| self.read_type_expr(te));
        let type_variance: Vec<Variance> = fields[5]
            .as_list()
            .iter()
            .map(|v| Variance::from_bits(v.as_int() as u8))
            .collect();
        let type_newtype_level = fields[6].as_option().map(|tup| {
            let (_, f) = tup.as_block();
            (f[0].as_int() as i32, f[1].as_int() as i32)
        });
        let type_immediate = fields[9].as_bool();
        let type_unboxed = read_unboxed_status(&fields[10]);
        let type_inlined_types = self.read_type_inlined_types(&fields[11]);

        TypeDeclaration {
            type_params,
            type_arity,
            type_kind,
            type_private,
            type_manifest,
            type_variance,
            type_newtype_level,
            type_loc: Location::none(),
            type_attributes: vec![],
            type_immediate,
            type_unboxed,
            type_inlined_types,
            type_path: None,
        }
    }

    /// Read type_kind.
    ///
    /// OCaml type_kind has 4 constructors:
    ///   Type_abstract | Type_record(...) | Type_variant(...) | Type_open
    /// Constants and non-constants are numbered separately:
    /// Constants:     Type_abstract = 0, Type_open = 1
    /// Non-constants: Type_record = 0, Type_variant = 1
    fn read_type_kind(&mut self, value: &OcamlValue) -> TypeKind {
        match value {
            OcamlValue::Int(0) => TypeKind::TypeAbstract,
            OcamlValue::Int(1) => TypeKind::TypeOpen,
            OcamlValue::Block(0, fields) => {
                // Type_record(label_declaration list, record_representation)
                let labels: Vec<LabelDeclaration> = fields[0]
                    .as_list()
                    .iter()
                    .map(|ld| self.read_label_declaration(ld))
                    .collect();
                let repr = self.read_record_representation(&fields[1]);
                TypeKind::TypeRecord(labels, repr)
            }
            OcamlValue::Block(1, fields) => {
                // Type_variant(constructor_declaration list)
                let constrs: Vec<ConstructorDeclaration> = fields[0]
                    .as_list()
                    .iter()
                    .map(|cd| self.read_constructor_declaration(cd))
                    .collect();
                TypeKind::TypeVariant(constrs)
            }
            _ => TypeKind::TypeAbstract, // fallback
        }
    }

    /// Read record_representation.
    ///
    /// Constants and non-constants numbered separately:
    /// Constants:     Record_regular=0, Record_float_unused=1, Record_extension=2
    /// Non-constants: Record_unboxed=0, Record_inlined=1
    fn read_record_representation(&mut self, value: &OcamlValue) -> RecordRepresentation {
        match value {
            OcamlValue::Int(0) => RecordRepresentation::RecordRegular,
            OcamlValue::Int(1) => RecordRepresentation::RecordFloatUnused,
            OcamlValue::Int(2) => RecordRepresentation::RecordExtension,
            OcamlValue::Block(0, fields) => {
                RecordRepresentation::RecordUnboxed(fields[0].as_bool())
            }
            OcamlValue::Block(1, fields) => {
                // Record_inlined { tag, name, num_nonconsts, attrs }
                // The inner record is the single argument
                let (_, f) = fields[0].as_block();
                RecordRepresentation::RecordInlined {
                    tag: f[0].as_int() as i32,
                    name: f[1].as_string().to_string(),
                    num_nonconsts: f[2].as_int() as i32,
                    attrs: vec![], // Skip attribute deserialization
                }
            }
            _ => RecordRepresentation::RecordRegular, // fallback
        }
    }

    /// Read a label_declaration (record field).
    ///
    /// Record fields:
    /// 0: ld_id: Ident.t
    /// 1: ld_mutable: mutable_flag
    /// 2: ld_optional: bool
    /// 3: ld_type: type_expr
    /// 4: ld_loc: Location.t
    /// 5: ld_attributes: attributes
    fn read_label_declaration(&mut self, value: &OcamlValue) -> LabelDeclaration {
        let fields = &value.as_block().1;
        let ld_id = read_ident(&fields[0]);
        let ld_mutable = read_mutable_flag(&fields[1]);
        let ld_optional = fields[2].as_bool();
        let ld_type = self.read_type_expr(&fields[3]);

        LabelDeclaration {
            ld_id,
            ld_mutable,
            ld_optional,
            ld_type,
            ld_loc: Location::none(),
            ld_attributes: vec![],
        }
    }

    /// Read a constructor_declaration (variant constructor).
    ///
    /// Record fields:
    /// 0: cd_id: Ident.t
    /// 1: cd_args: constructor_arguments
    /// 2: cd_res: type_expr option
    /// 3: cd_loc: Location.t
    /// 4: cd_attributes: attributes
    fn read_constructor_declaration(&mut self, value: &OcamlValue) -> ConstructorDeclaration {
        let fields = &value.as_block().1;
        let cd_id = read_ident(&fields[0]);
        let cd_args = self.read_constructor_arguments(&fields[1]);
        let cd_res = fields[2].as_option().map(|te| self.read_type_expr(te));

        ConstructorDeclaration {
            cd_id,
            cd_args,
            cd_res,
            cd_loc: Location::none(),
            cd_attributes: vec![],
        }
    }

    /// Read constructor_arguments.
    ///
    /// Tags:
    /// - 0: Cstr_tuple(type_expr list)
    /// - 1: Cstr_record(label_declaration list)
    fn read_constructor_arguments(&mut self, value: &OcamlValue) -> ConstructorArguments {
        match value {
            OcamlValue::Block(0, fields) => {
                let types: Vec<TypeExprRef> = fields[0]
                    .as_list()
                    .iter()
                    .map(|te| self.read_type_expr(te))
                    .collect();
                ConstructorArguments::CstrTuple(types)
            }
            OcamlValue::Block(1, fields) => {
                let labels: Vec<LabelDeclaration> = fields[0]
                    .as_list()
                    .iter()
                    .map(|ld| self.read_label_declaration(ld))
                    .collect();
                ConstructorArguments::CstrRecord(labels)
            }
            _ => ConstructorArguments::CstrTuple(vec![]), // fallback
        }
    }

    /// Read an extension_constructor.
    ///
    /// Record fields:
    /// 0: ext_type_path: Path.t
    /// 1: ext_type_params: type_expr list
    /// 2: ext_args: constructor_arguments
    /// 3: ext_ret_type: type_expr option
    /// 4: ext_private: private_flag
    /// 5: ext_loc: Location.t
    /// 6: ext_attributes: attributes
    /// 7: ext_is_exception: bool
    fn read_extension_constructor(&mut self, value: &OcamlValue) -> ExtensionConstructor {
        let fields = &value.as_block().1;
        let ext_type_path = read_path(&fields[0]);
        let ext_type_params: Vec<TypeExprRef> = fields[1]
            .as_list()
            .iter()
            .map(|te| self.read_type_expr(te))
            .collect();
        let ext_args = self.read_constructor_arguments(&fields[2]);
        let ext_ret_type = fields[3].as_option().map(|te| self.read_type_expr(te));
        let ext_private = read_private_flag(&fields[4]);
        let ext_is_exception = fields[7].as_bool();

        ExtensionConstructor {
            ext_type_path,
            ext_type_params,
            ext_args,
            ext_ret_type,
            ext_private,
            ext_loc: Location::none(),
            ext_attributes: vec![],
            ext_is_exception,
        }
    }

    /// Read a module_declaration.
    ///
    /// Record fields:
    /// 0: md_type: module_type
    /// 1: md_attributes: attributes
    /// 2: md_loc: Location.t
    fn read_module_declaration(&mut self, value: &OcamlValue) -> ModuleDeclaration {
        let fields = &value.as_block().1;
        let md_type = self.read_module_type(&fields[0]);

        ModuleDeclaration {
            md_type,
            md_attributes: vec![],
            md_loc: Location::none(),
            md_path: None,
        }
    }

    /// Read a modtype_declaration.
    ///
    /// Record fields:
    /// 0: mtd_type: module_type option
    /// 1: mtd_attributes: attributes
    /// 2: mtd_loc: Location.t
    fn read_modtype_declaration(&mut self, value: &OcamlValue) -> ModtypeDeclaration {
        let fields = &value.as_block().1;
        let mtd_type = fields[0].as_option().map(|mt| self.read_module_type(mt));

        ModtypeDeclaration {
            mtd_type,
            mtd_attributes: vec![],
            mtd_loc: Location::none(),
        }
    }

    /// Read a module_type.
    ///
    /// Tags:
    /// - 0: Mty_ident(Path.t)
    /// - 1: Mty_signature(signature)
    /// - 2: Mty_functor(Ident.t, module_type option, module_type)
    /// - 3: Mty_alias(alias_presence, Path.t)
    fn read_module_type(&mut self, value: &OcamlValue) -> ModuleType {
        match value {
            OcamlValue::Block(0, fields) => {
                let path = read_path(&fields[0]);
                ModuleType::MtyIdent(path)
            }
            OcamlValue::Block(1, fields) => {
                let sig_items: Vec<OcamlValue> =
                    fields[0].as_list().into_iter().cloned().collect();
                let signature = self.read_signature(&sig_items);
                ModuleType::MtySignature(signature)
            }
            OcamlValue::Block(2, fields) => {
                let param = read_ident(&fields[0]);
                let param_type = fields[1]
                    .as_option()
                    .map(|mt| Box::new(self.read_module_type(mt)));
                let result = Box::new(self.read_module_type(&fields[2]));
                ModuleType::MtyFunctor {
                    param,
                    param_type,
                    result,
                }
            }
            OcamlValue::Block(3, fields) => {
                let presence = read_alias_presence(&fields[0]);
                let path = read_path(&fields[1]);
                ModuleType::MtyAlias(presence, path)
            }
            _ => {
                // Fallback: create an empty signature
                ModuleType::MtySignature(vec![])
            }
        }
    }

    /// Read type_inlined_types.
    fn read_type_inlined_types(
        &mut self,
        value: &OcamlValue,
    ) -> Vec<crate::types::decl::TypeInlinedType> {
        value
            .as_list()
            .iter()
            .filter_map(|item| {
                // type_inlined_type = Record { type_name, labels }  (tag 0)
                match item {
                    OcamlValue::Block(0, fields) => {
                        // Inline record: block with tag 0
                        // The inner block has fields: type_name (string), labels (label_decl list)
                        let inner_fields = &fields[0].as_block().1;
                        let type_name = inner_fields[0].as_string().to_string();
                        let labels: Vec<LabelDeclaration> = inner_fields[1]
                            .as_list()
                            .iter()
                            .map(|ld| self.read_label_declaration(ld))
                            .collect();
                        Some(crate::types::decl::TypeInlinedType::Record { type_name, labels })
                    }
                    _ => None,
                }
            })
            .collect()
    }

    /// Read a type_expr.
    ///
    /// type_expr is a record with 3 fields (tag 0):
    /// 0: desc: type_desc (mutable)
    /// 1: level: int (mutable)
    /// 2: id: int
    ///
    /// We use the `id` field to detect sharing: if we've already read a type_expr
    /// with the same id, we reuse the same TypeExprRef.
    fn read_type_expr(&mut self, value: &OcamlValue) -> TypeExprRef {
        let fields = &value.as_block().1;
        let id = fields[2].as_int();

        // Check cache for shared type expressions
        if let Some(&existing) = self.type_expr_cache.get(&id) {
            return existing;
        }

        let level = fields[1].as_int() as i32;
        // Allocate and cache a placeholder before reading the descriptor.
        // This preserves sharing/recursion when the descriptor references the
        // same type_expr id (OCaml Marshal shared references).
        let actual_level = if level >= GENERIC_LEVEL {
            GENERIC_LEVEL
        } else {
            level
        };
        let ty_ref = self.ctx.new_generic_var(None);
        if actual_level != GENERIC_LEVEL {
            self.ctx.set_level(ty_ref, actual_level);
        }
        self.type_expr_cache.insert(id, ty_ref);

        let desc = self.read_type_desc(&fields[0]);
        self.ctx.set_desc(ty_ref, desc);
        ty_ref
    }

    /// Read a type_desc.
    ///
    /// Tags:
    /// Read a type_desc.
    ///
    /// Constants and non-constants numbered separately:
    /// Constant:      Tnil = Int(0)
    /// Non-constants: Tvar=0, Tarrow=1, Ttuple=2, Tconstr=3, Tobject=4, Tfield=5,
    ///                Tlink=6, Tsubst=7, Tvariant=8, Tunivar=9, Tpoly=10, Tpackage=11
    fn read_type_desc(&mut self, value: &OcamlValue) -> TypeDesc {
        match value {
            // Tnil is the only constant constructor
            OcamlValue::Int(0) => TypeDesc::Tnil,

            // Block constructors (numbered without counting constants)
            OcamlValue::Block(tag, fields) => match tag {
                0 => {
                    // Tvar(string option)
                    let name = fields[0].as_option().map(|s| s.as_string().to_string());
                    TypeDesc::Tvar(name)
                }
                1 => {
                    // Tarrow(arg, type_expr, commutable, arity)
                    let arg = self.read_arg(&fields[0]);
                    let ret = self.read_type_expr(&fields[1]);
                    let commutable = read_commutable(&fields[2]);
                    let arity = fields[3].as_option().map(|n| n.as_int() as i32);

                    TypeDesc::Tarrow {
                        arg,
                        ret,
                        commutable,
                        arity,
                    }
                }
                2 => {
                    // Ttuple(type_expr list)
                    let types: Vec<TypeExprRef> = fields[0]
                        .as_list()
                        .iter()
                        .map(|te| self.read_type_expr(te))
                        .collect();
                    TypeDesc::Ttuple(types)
                }
                3 => {
                    // Tconstr(Path.t, type_expr list, abbrev_memo ref)
                    let path = read_path(&fields[0]);
                    let args: Vec<TypeExprRef> = fields[1]
                        .as_list()
                        .iter()
                        .map(|te| self.read_type_expr(te))
                        .collect();
                    let abbrev = self.ctx.alloc_abbrev_nil();

                    TypeDesc::Tconstr { path, args, abbrev }
                }
                4 => {
                    // Tobject(type_expr, (Path.t * type_expr list) option ref)
                    let obj_fields = self.read_type_expr(&fields[0]);
                    let name = None;
                    TypeDesc::Tobject {
                        fields: obj_fields,
                        name,
                    }
                }
                5 => {
                    // Tfield(string, field_kind, type_expr, type_expr)
                    let name = fields[0].as_string().to_string();
                    let kind = read_field_kind(&fields[1]);
                    let typ = self.read_type_expr(&fields[2]);
                    let rest = self.read_type_expr(&fields[3]);
                    TypeDesc::Tfield {
                        name,
                        kind,
                        typ,
                        rest,
                    }
                }
                6 => {
                    // Tlink(type_expr)
                    let target = self.read_type_expr(&fields[0]);
                    TypeDesc::Tlink(target)
                }
                7 => {
                    // Tsubst(type_expr)
                    let target = self.read_type_expr(&fields[0]);
                    TypeDesc::Tsubst(target)
                }
                8 => {
                    // Tvariant(row_desc)
                    let row = self.read_row_desc(&fields[0]);
                    TypeDesc::Tvariant(row)
                }
                9 => {
                    // Tunivar(string option)
                    let name = fields[0].as_option().map(|s| s.as_string().to_string());
                    TypeDesc::Tunivar(name)
                }
                10 => {
                    // Tpoly(type_expr, type_expr list)
                    let body = self.read_type_expr(&fields[0]);
                    let vars: Vec<TypeExprRef> = fields[1]
                        .as_list()
                        .iter()
                        .map(|te| self.read_type_expr(te))
                        .collect();
                    TypeDesc::Tpoly { body, vars }
                }
                11 => {
                    // Tpackage(Path.t, Longident.t list, type_expr list)
                    let path = read_path(&fields[0]);
                    let lids: Vec<crate::parser::longident::Longident> = fields[1]
                        .as_list()
                        .iter()
                        .map(|lid| self.read_longident(lid))
                        .collect();
                    let args: Vec<TypeExprRef> = fields[2]
                        .as_list()
                        .iter()
                        .map(|te| self.read_type_expr(te))
                        .collect();
                    TypeDesc::Tpackage { path, lids, args }
                }
                _ => {
                    // Unknown type_desc tag, treat as Tvar
                    TypeDesc::Tvar(None)
                }
            },
            _ => TypeDesc::Tvar(None), // fallback
        }
    }

    /// Read a Longident.t.
    ///
    /// Tags:
    /// - 0: Lident(string)
    /// - 1: Ldot(Longident.t, string)
    /// - 2: Lapply(Longident.t, Longident.t)
    fn read_longident(&self, value: &OcamlValue) -> crate::parser::longident::Longident {
        use crate::parser::longident::Longident;

        match value {
            OcamlValue::Block(0, fields) => {
                let name = fields[0].as_string();
                let idx = self.ctx.intern_cmi_longident_name(name);
                Longident::Lident(idx)
            }
            OcamlValue::Block(1, fields) => {
                let prefix = self.read_longident(&fields[0]);
                let name = fields[1].as_string();
                let idx = self.ctx.intern_cmi_longident_name(name);
                Longident::Ldot(Box::new(prefix), idx)
            }
            OcamlValue::Block(2, fields) => {
                let funct = self.read_longident(&fields[0]);
                let arg = self.read_longident(&fields[1]);
                Longident::Lapply(Box::new(funct), Box::new(arg))
            }
            _ => {
                let idx = self.ctx.intern_cmi_longident_name("");
                Longident::Lident(idx)
            }
        }
    }

    /// Read an arg record {lbl: arg_label; typ: type_expr}.
    fn read_arg(&mut self, value: &OcamlValue) -> TypeArg {
        let fields = &value.as_block().1;
        let lbl = read_arg_label(&fields[0]);
        let typ = self.read_type_expr(&fields[1]);
        TypeArg { lbl, typ }
    }

    /// Read a row_desc record.
    ///
    /// Record fields:
    /// 0: row_fields: (label * row_field) list
    /// 1: row_more: type_expr
    /// 2: row_closed: bool
    /// 3: row_fixed: bool
    /// 4: row_name: (Path.t * type_expr list) option
    fn read_row_desc(&mut self, value: &OcamlValue) -> RowDesc {
        let fields = &value.as_block().1;

        let row_fields: Vec<(String, RowField)> = fields[0]
            .as_list()
            .iter()
            .map(|pair| {
                let (_, pf) = pair.as_block();
                let label = pf[0].as_string().to_string();
                let rf = self.read_row_field(&pf[1]);
                (label, rf)
            })
            .collect();

        let row_more = self.read_type_expr(&fields[1]);
        let row_closed = fields[2].as_bool();
        let row_fixed = fields[3].as_bool();

        let row_name = fields[4].as_option().map(|tup| {
            let (_, f) = tup.as_block();
            let path = read_path(&f[0]);
            let args: Vec<TypeExprRef> = f[1]
                .as_list()
                .iter()
                .map(|te| self.read_type_expr(te))
                .collect();
            (path, args)
        });

        RowDesc {
            row_fields,
            row_more,
            row_closed,
            row_fixed,
            row_name,
        }
    }

    /// Read a row_field.
    ///
    /// Rabsent is the only constant (Int(0)).
    /// Non-constants: Rpresent = Block(0), Reither = Block(1).
    fn read_row_field(&mut self, value: &OcamlValue) -> RowField {
        match value {
            OcamlValue::Int(0) => RowField::Rabsent,
            OcamlValue::Block(0, fields) => {
                let ty = fields[0].as_option().map(|te| self.read_type_expr(te));
                RowField::Rpresent(ty)
            }
            OcamlValue::Block(1, fields) => {
                let constant = fields[0].as_bool();
                let types: Vec<TypeExprRef> = fields[1]
                    .as_list()
                    .iter()
                    .map(|te| self.read_type_expr(te))
                    .collect();
                let matched = fields[2].as_bool();
                // Skip the row_field option ref (fields[3])
                let link = crate::types::type_expr::RowFieldRef::null();
                RowField::Reither {
                    constant,
                    types,
                    matched,
                    link,
                }
            }
            _ => RowField::Rabsent, // fallback
        }
    }
}

// ============================================================================
// Pure functions (no context needed)
// ============================================================================

/// Read an Ident.t.
///
/// Record fields:
/// 0: stamp: int
/// 1: name: string
/// 2: flags: int (mutable)
/// Known predef type names that should be normalized to persistent idents.
/// OCaml creates these with small stamps (1-999) via Ident.create, but
/// Rust's initial_env uses persistent idents (stamp=0). Normalizing here
/// ensures CMI types unify with initial_env types.
fn is_predef_type_name(name: &str) -> bool {
    matches!(name,
        "int" | "char" | "float" | "bool" | "unit" | "exn" | "array" |
        "list" | "option" | "nativeint" | "int32" | "int64" | "lazy_t" |
        "bytes" | "string" | "ref" | "result" | "dict" | "promise" |
        "unknown" | "bigint" | "symbol" | "regexp"
    )
}

fn read_ident(value: &OcamlValue) -> Ident {
    let fields = &value.as_block().1;
    let stamp = fields[0].as_int() as i32;
    let name = fields[1].as_string();
    let flags = fields[2].as_int() as u8;

    if stamp == 0 {
        // Persistent identifier
        let id = Ident::create_persistent(name);
        if flags & 1 != 0 {
            id.with_global()
        } else {
            id
        }
    } else if stamp < 1000 && is_predef_type_name(name) {
        // Predef type: OCaml uses small stamps, Rust uses persistent idents.
        // Normalize to persistent so CMI types match initial_env types.
        Ident::create_persistent(name)
    } else {
        Ident::new(name, stamp, crate::ident::IdentFlags::from_bits_truncate(flags))
    }
}

/// Read a Path.t.
///
/// Tags:
/// - 0: Pident(Ident.t)
/// - 1: Pdot(Path.t, string, int)
/// - 2: Papply(Path.t, Path.t)
fn read_path(value: &OcamlValue) -> Path {
    match value {
        OcamlValue::Block(0, fields) => {
            let id = read_ident(&fields[0]);
            Path::Pident(id)
        }
        OcamlValue::Block(1, fields) => {
            let prefix = read_path(&fields[0]);
            let name = fields[1].as_string().to_string();
            let pos = fields[2].as_int() as i32;
            Path::Pdot(Box::new(prefix), name, pos)
        }
        OcamlValue::Block(2, fields) => {
            let f = read_path(&fields[0]);
            let a = read_path(&fields[1]);
            Path::Papply(Box::new(f), Box::new(a))
        }
        _ => Path::Pident(Ident::create_persistent("?")), // fallback
    }
}

/// Read a Location.t (we just skip it for now).
fn read_location(_value: &OcamlValue) -> Location {
    Location::none()
}

/// Read attributes (skip for now, just return empty).
fn read_attributes(_value: &OcamlValue) -> Vec<Attribute> {
    vec![]
}

/// Read a Primitive.description.
///
/// Record fields:
/// 0: prim_name: string
/// 1: prim_arity: int
/// 2: prim_alloc: bool
/// 3: prim_native_name: string
/// 4: prim_from_constructor: bool
/// 5: transformed_jsx: bool
fn read_primitive_description(value: &OcamlValue) -> PrimitiveDescription {
    let fields = &value.as_block().1;
    PrimitiveDescription {
        prim_name: fields[0].as_string().to_string(),
        prim_arity: fields[1].as_int() as i32,
        prim_native_name: if fields.len() > 3 {
            fields[3].as_string().to_string()
        } else {
            String::new()
        },
        prim_native_float: false,
    }
}

/// Read rec_status (int constant).
fn read_rec_status(value: &OcamlValue) -> RecStatus {
    match value.as_int() {
        0 => RecStatus::TrecNot,
        1 => RecStatus::TrecFirst,
        2 => RecStatus::TrecNext,
        _ => RecStatus::TrecNot,
    }
}

/// Read ext_status (int constant).
fn read_ext_status(value: &OcamlValue) -> ExtStatus {
    match value.as_int() {
        0 => ExtStatus::TextFirst,
        1 => ExtStatus::TextNext,
        2 => ExtStatus::TextException,
        _ => ExtStatus::TextFirst,
    }
}

/// Read private_flag (int constant).
fn read_private_flag(value: &OcamlValue) -> PrivateFlag {
    match value.as_int() {
        0 => PrivateFlag::Private,
        1 => PrivateFlag::Public,
        _ => PrivateFlag::Public,
    }
}

/// Read mutable_flag (int constant).
fn read_mutable_flag(value: &OcamlValue) -> MutableFlag {
    match value.as_int() {
        0 => MutableFlag::Immutable,
        1 => MutableFlag::Mutable,
        _ => MutableFlag::Immutable,
    }
}

/// Read arg_label.
///
/// Nolabel is constant (Int(0)).
/// Non-constants: Labelled = Block(0), Optional = Block(1).
fn read_arg_label(value: &OcamlValue) -> ArgLabel {
    match value {
        OcamlValue::Int(0) => ArgLabel::Nolabel,
        OcamlValue::Block(0, fields) => {
            // Labelled(string loc) - string loc is {txt: string; loc: Location.t}
            let loc_fields = &fields[0].as_block().1;
            let name = loc_fields[0].as_string().to_string();
            ArgLabel::Labelled(Located::new(name, Location::none()))
        }
        OcamlValue::Block(1, fields) => {
            // Optional(string loc) - string loc is {txt: string; loc: Location.t}
            let loc_fields = &fields[0].as_block().1;
            let name = loc_fields[0].as_string().to_string();
            ArgLabel::Optional(Located::new(name, Location::none()))
        }
        _ => ArgLabel::Nolabel,
    }
}

/// Read alias_presence.
fn read_alias_presence(value: &OcamlValue) -> AliasPresence {
    match value.as_int() {
        0 => AliasPresence::MtaPresent,
        1 => AliasPresence::MtaAbsent,
        _ => AliasPresence::MtaPresent,
    }
}

/// Read commutable.
fn read_commutable(_value: &OcamlValue) -> Commutable {
    // For CMI-loaded types, commutability doesn't matter.
    // Just use Cok.
    Commutable::Cok
}

/// Read field_kind.
fn read_field_kind(_value: &OcamlValue) -> FieldKind {
    // For CMI-loaded types, just use Fpresent.
    FieldKind::Fpresent
}

/// Read unboxed_status.
///
/// Record fields:
/// 0: unboxed: bool
/// 1: default: bool
fn read_unboxed_status(value: &OcamlValue) -> UnboxedStatus {
    let fields = &value.as_block().1;
    UnboxedStatus {
        unboxed: fields[0].as_bool(),
        default: fields[1].as_bool(),
    }
}
