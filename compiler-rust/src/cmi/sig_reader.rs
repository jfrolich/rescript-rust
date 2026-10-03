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
use crate::location::{Location, Position};
use crate::types::asttypes::{ArgLabel, Located, MutableFlag, PrivateFlag};
use crate::types::context::TypeContext;
use crate::types::decl::{
    AliasPresence, Attribute, AttributePayload, ConstructorArguments, ConstructorDeclaration,
    ExtStatus, ExtensionConstructor, LabelDeclaration, ModtypeDeclaration, ModuleDeclaration,
    ModuleType, PrimitiveDescription, RecStatus, RecordRepresentation, Signature, SignatureItem,
    TypeDeclaration, TypeKind, TypeRepresentation, ValueDescription, ValueKind,
};
use crate::types::path::Path;
use crate::types::type_expr::{
    FieldKind, GENERIC_LEVEL, RowDesc, RowField, TypeArg, TypeDesc, TypeExprRef,
};
use crate::types::variance::Variance;

use super::marshal_reader::OcamlValue;

use std::collections::{HashMap, HashSet};

/// Context for reading signatures, holding the type arena and a table for
/// resolving shared type_expr references.
pub struct SigReadContext<'a> {
    /// The type context for allocating type expressions.
    pub ctx: &'a TypeContext,
    /// Map from OCaml type_expr id to TypeExprRef, for shared type references.
    type_expr_cache: HashMap<i64, TypeExprRef>,
    /// OCaml layout refs are shared mutable blocks. Preserve that physical
    /// sharing by mapping their marshal block identity to one TypeContext slot.
    variant_layout_cache: HashMap<usize, crate::types::VariantLayoutRef>,
}

impl<'a> SigReadContext<'a> {
    /// Create a new signature reading context.
    pub fn new(ctx: &'a TypeContext) -> Self {
        SigReadContext {
            ctx,
            type_expr_cache: HashMap::new(),
            variant_layout_cache: HashMap::new(),
        }
    }

    /// Read a complete signature (list of signature items).
    pub fn read_signature(&mut self, items: &[OcamlValue]) -> Signature {
        items
            .iter()
            .map(|item| self.read_signature_item(item))
            .collect()
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
                    let debug_this_value = crate::debug_flags::debug_sig_value().is_some_and(|raw| {
                        raw.split(',')
                            .map(|part| part.trim())
                            .filter(|part| !part.is_empty())
                            .any(|target| target == id.name())
                    });
                    if debug_this_value {
                        eprintln!(
                            "[sig-read] raw value={} before read_type_expr ids={}",
                            id.name(),
                            debug_raw_type_expr_ids(&fields[1].field(0))
                        );
                    }
                    let desc = self.read_value_description(&fields[1]);
                    if debug_this_value {
                        eprintln!(
                            "[sig-read] loaded value={} refs={}",
                            id.name(),
                            debug_loaded_type_refs(self.ctx, desc.val_type)
                        );
                    }
                    SignatureItem::SigValue(id, desc)
                }
                1 => {
                    let id = read_ident(&fields[0]);
                    let decl = self.read_type_declaration(&fields[1]);
                    let rec_status = read_rec_status(&fields[2]);
                    SignatureItem::SigType(id, std::sync::Arc::new(decl), rec_status)
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
        let val_loc = read_location(self.ctx, &fields[2]);
        let val_attributes = read_attributes(self.ctx, &fields[3]);

        ValueDescription {
            val_type,
            val_kind,
            val_loc,
            val_attributes,
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
    /// 10: type_representation
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
        let type_loc = read_location(self.ctx, &fields[7]);
        let type_attributes = read_attributes(self.ctx, &fields[8]);
        let type_immediate = fields[9].as_bool();
        let type_representation = if fields[10].as_int() == 1 {
            TypeRepresentation::Unboxed
        } else {
            TypeRepresentation::Boxed
        };
        let type_inlined_types = self.read_type_inlined_types(&fields[11]);

        TypeDeclaration {
            type_params,
            type_arity,
            type_kind,
            type_private,
            type_manifest,
            type_variance,
            type_newtype_level,
            type_loc,
            type_attributes,
            type_immediate,
            type_representation,
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
                TypeKind::TypeRecord(crate::types::decl::SharedVec::from(labels), repr)
            }
            OcamlValue::Block(1, fields) => {
                // Type_variant(constructor_declaration list, layout_ref)
                let constrs: Vec<ConstructorDeclaration> = fields[0]
                    .as_list()
                    .iter()
                    .map(|cd| self.read_constructor_declaration(cd))
                    .collect();
                let layout = self.read_variant_layout_ref(
                    fields
                        .get(1)
                        .expect("variant type kind must carry a layout"),
                );
                TypeKind::TypeVariant(crate::types::decl::SharedVec::from(constrs), layout)
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
                // Record_inlined {name; representation}
                let (_, f) = fields[0].as_block();
                let representation = self.read_constructor_reference(&f[1]);
                RecordRepresentation::RecordInlined {
                    name: f[0].as_string().to_string(),
                    representation,
                }
            }
            _ => RecordRepresentation::RecordRegular, // fallback
        }
    }

    fn read_variant_layout_ref(&mut self, value: &OcamlValue) -> crate::types::VariantLayoutRef {
        let (_, fields) = value.as_block();
        let key = fields.as_ptr() as usize;
        if let Some(layout_ref) = self.variant_layout_cache.get(&key) {
            return *layout_ref;
        }
        let layout_ref = self.ctx.pending_variant_layout();
        self.variant_layout_cache.insert(key, layout_ref);
        let state = &fields[0];
        let OcamlValue::Block(0, complete) = state else {
            panic!("CMI contains pending variant layout")
        };
        let layout = self.read_variant_layout(&complete[0]);
        self.ctx.complete_variant_layout(layout_ref, layout);
        layout_ref
    }

    fn read_constructor_reference(
        &mut self,
        value: &OcamlValue,
    ) -> crate::types::ConstructorReference {
        let (_, fields) = value.as_block();
        crate::types::ConstructorReference {
            variant: self.read_variant_layout_ref(&fields[0]),
            position: fields[1].as_int() as usize,
        }
    }

    fn read_variant_layout(&mut self, value: &OcamlValue) -> crate::types::VariantLayout {
        let (_, fields) = value.as_block();
        let constructors = fields[1]
            .as_block()
            .1
            .iter()
            .map(|case| self.read_variant_case(case))
            .collect();
        crate::types::VariantLayout::new(
            crate::types::VariantConfiguration {
                unboxed: fields[0].as_bool(),
                tag_name: self.read_string_option(&fields[2].as_block().1[0]),
            },
            constructors,
        )
    }

    fn read_variant_case(&mut self, value: &OcamlValue) -> crate::types::VariantConstructorCase {
        let (tag, fields) = value.as_block();
        match tag {
            0 => crate::types::VariantConstructorCase::Constant(self.read_variant_tag(&fields[0])),
            1 => {
                let (_, block) = fields[0].as_block();
                let (_, runtime) = block[0].as_block();
                crate::types::VariantConstructorCase::Block(crate::types::VariantBlock {
                    runtime: crate::types::BlockRuntime {
                        tag: self.read_variant_tag(&runtime[0]),
                        tag_name: self.read_string_option(&runtime[1]),
                        untagged: runtime[2].as_bool(),
                    },
                    block_type: block[1]
                        .as_option()
                        .map(|v| self.read_variant_block_type(v)),
                })
            }
            _ => panic!("invalid variant constructor case tag {tag}"),
        }
    }

    fn read_variant_tag(&mut self, value: &OcamlValue) -> crate::types::VariantTag {
        let (_, fields) = value.as_block();
        crate::types::VariantTag {
            name: fields[0].as_string().to_string(),
            tag_type: fields[1].as_option().map(|v| self.read_variant_tag_type(v)),
        }
    }

    fn read_variant_tag_type(&mut self, value: &OcamlValue) -> crate::types::VariantTagType {
        use crate::types::VariantTagType as T;
        match value {
            OcamlValue::Int(0) => T::Null,
            OcamlValue::Int(1) => T::Undefined,
            OcamlValue::Block(tag, fields) => match tag {
                0 => T::String(fields[0].as_string().to_string()),
                1 => T::Int(fields[0].as_int() as i32),
                2 => T::Float(fields[0].as_string().to_string()),
                3 => T::BigInt(fields[0].as_string().to_string()),
                4 => T::Bool(fields[0].as_bool()),
                5 => T::Untagged(self.read_variant_block_type(&fields[0])),
                _ => panic!("invalid variant tag type {tag}"),
            },
            _ => panic!("invalid variant tag type"),
        }
    }

    fn read_variant_block_type(&mut self, value: &OcamlValue) -> crate::types::VariantBlockType {
        use crate::types::{VariantBlockType as B, VariantInstance as I};
        match value {
            OcamlValue::Int(0) => B::Int,
            OcamlValue::Int(1) => B::String,
            OcamlValue::Int(2) => B::Float,
            OcamlValue::Int(3) => B::Bigint,
            OcamlValue::Int(4) => B::Boolean,
            OcamlValue::Int(5) => B::Function,
            OcamlValue::Int(6) => B::Object,
            OcamlValue::Int(7) => B::Unknown,
            OcamlValue::Block(0, fields) => B::Instance(match fields[0].as_int() {
                0 => I::Array,
                1 => I::ArrayBuffer,
                2 => I::BigInt64Array,
                3 => I::BigUint64Array,
                4 => I::Blob,
                5 => I::DataView,
                6 => I::Date,
                7 => I::File,
                8 => I::Float32Array,
                9 => I::Float64Array,
                10 => I::Int16Array,
                11 => I::Int32Array,
                12 => I::Int8Array,
                13 => I::Promise,
                14 => I::RegExp,
                15 => I::Uint16Array,
                16 => I::Uint32Array,
                17 => I::Uint8Array,
                18 => I::Uint8ClampedArray,
                19 => I::Set,
                20 => I::Map,
                21 => I::WeakSet,
                22 => I::WeakMap,
                n => panic!("invalid variant instance {n}"),
            }),
            _ => panic!("invalid variant block type"),
        }
    }

    fn read_string_option(&self, value: &OcamlValue) -> Option<String> {
        value.as_option().map(|v| v.as_string().to_string())
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
        let ld_loc = read_location(self.ctx, &fields[4]);
        let ld_attributes = read_attributes(self.ctx, &fields[5]);

        LabelDeclaration {
            ld_id,
            ld_mutable,
            ld_optional,
            ld_type,
            ld_loc,
            ld_attributes,
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
        let cd_loc = read_location(self.ctx, &fields[3]);
        let cd_attributes = read_attributes(self.ctx, &fields[4]);

        ConstructorDeclaration {
            cd_id,
            cd_args,
            cd_res,
            cd_loc,
            cd_attributes,
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
        let ext_loc = read_location(self.ctx, &fields[5]);
        let ext_attributes = read_attributes(self.ctx, &fields[6]);
        let ext_is_exception = fields[7].as_bool();

        ExtensionConstructor {
            ext_type_path,
            ext_type_params,
            ext_args,
            ext_ret_type,
            ext_private,
            ext_loc,
            ext_attributes,
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
        let md_attributes = read_attributes(self.ctx, &fields[1]);
        let md_loc = read_location(self.ctx, &fields[2]);

        ModuleDeclaration {
            md_type,
            md_attributes,
            md_loc,
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
        let mtd_attributes = read_attributes(self.ctx, &fields[1]);
        let mtd_loc = read_location(self.ctx, &fields[2]);

        ModtypeDeclaration {
            mtd_type,
            mtd_attributes,
            mtd_loc,
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
                let sig_items: Vec<OcamlValue> = fields[0].as_list().into_iter().cloned().collect();
                let signature = self.read_signature(&sig_items);
                ModuleType::MtySignature(std::sync::Arc::new(signature))
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
                ModuleType::MtySignature(std::sync::Arc::new(vec![]))
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
                    // Caml1999I024 stores the complete parameter list directly;
                    // keep that allocation shape rather than rebuilding unary nodes.
                    let args = fields[0]
                        .as_list()
                        .iter()
                        .map(|arg| self.read_arg(arg))
                        .collect();
                    let ret = self.read_type_expr(&fields[1]);
                    TypeDesc::Tarrow { args, ret }
                }
                2 => {
                    // Ttuple(type_expr list)
                    let types: Vec<TypeExprRef> = fields[0]
                        .as_list()
                        .iter()
                        .map(|te| self.read_type_expr(te))
                        .collect();
                    TypeDesc::Ttuple(types.into())
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

                    TypeDesc::Tconstr { path, args: args.into(), abbrev }
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
                    TypeDesc::Tvariant(Box::new(row))
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
                    TypeDesc::Tpoly { body, vars: vars.into() }
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
                    TypeDesc::Tpackage { path, lids: Box::new(lids), args: args.into() }
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
        let lbl = read_arg_label(self.ctx, &fields[0]);
        let typ = self.read_type_expr(&fields[1]);
        TypeArg::new(lbl, typ)
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

        let row_fields: Vec<(crate::types::asttypes::Label, RowField)> = fields[0]
            .as_list()
            .iter()
            .map(|pair| {
                let (_, pf) = pair.as_block();
                let label = crate::types::asttypes::Label::from(pf[0].as_string());
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
            row_fields: row_fields.into(),
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

fn debug_raw_type_expr_ids(value: &OcamlValue) -> String {
    fn walk(value: &OcamlValue, out: &mut Vec<String>, seen: &mut HashSet<i64>) {
        let (_, fields) = value.as_block();
        let id = fields[2].as_int();
        if !seen.insert(id) {
            out.push(format!("id#{id}:<seen>"));
            return;
        }

        let head = match &fields[0] {
            OcamlValue::Int(0) => "Tnil".to_string(),
            OcamlValue::Block(tag, desc_fields) => match tag {
                0 => "Tvar".to_string(),
                1 => "Tarrow".to_string(),
                2 => "Ttuple".to_string(),
                3 => {
                    let path = read_path(&desc_fields[0]);
                    format!("Tconstr({})", path.name())
                }
                4 => "Tobject".to_string(),
                5 => "Tfield".to_string(),
                6 => "Tlink".to_string(),
                7 => "Tsubst".to_string(),
                8 => "Tvariant".to_string(),
                9 => "Tunivar".to_string(),
                10 => "Tpoly".to_string(),
                11 => "Tpackage".to_string(),
                other => format!("tag{other}"),
            },
            other => format!("{other:?}"),
        };
        let level = fields[1].as_int();
        out.push(format!("id#{id}@{level}:{head}"));

        match &fields[0] {
            OcamlValue::Block(tag, desc_fields) => match tag {
                1 => {
                    walk(&desc_fields[0].field(1), out, seen);
                    walk(&desc_fields[1], out, seen);
                }
                2 => {
                    for item in desc_fields[0].as_list() {
                        walk(item, out, seen);
                    }
                }
                3 => {
                    for item in desc_fields[1].as_list() {
                        walk(item, out, seen);
                    }
                }
                4 => walk(&desc_fields[0], out, seen),
                5 => {
                    walk(&desc_fields[2], out, seen);
                    walk(&desc_fields[3], out, seen);
                }
                6 | 7 => walk(&desc_fields[0], out, seen),
                8 => {
                    let row_fields = desc_fields[0].field(0);
                    for pair in row_fields.as_list() {
                        let (_, pf) = pair.as_block();
                        match &pf[1] {
                            OcamlValue::Block(0, rf) => {
                                if let Some(inner) = rf[0].as_option() {
                                    walk(inner, out, seen);
                                }
                            }
                            OcamlValue::Block(1, rf) => {
                                for item in rf[1].as_list() {
                                    walk(item, out, seen);
                                }
                            }
                            _ => {}
                        }
                    }
                    walk(&desc_fields[0].field(1), out, seen);
                }
                10 => {
                    walk(&desc_fields[0], out, seen);
                    for item in desc_fields[1].as_list() {
                        walk(item, out, seen);
                    }
                }
                11 => {
                    for item in desc_fields[2].as_list() {
                        walk(item, out, seen);
                    }
                }
                _ => {}
            },
            _ => {}
        }
    }

    let mut out = Vec::new();
    let mut seen = HashSet::new();
    walk(value, &mut out, &mut seen);
    out.join(", ")
}

fn debug_loaded_type_refs(ctx: &TypeContext, ty: TypeExprRef) -> String {
    fn walk(
        ctx: &TypeContext,
        ty: TypeExprRef,
        out: &mut Vec<String>,
        seen: &mut HashSet<TypeExprRef>,
    ) {
        let ty = ctx.repr(ty);
        if !seen.insert(ty) {
            out.push(format!("ref#{}:<seen>", ty.0));
            return;
        }
        let desc = ctx.get_desc(ty);
        let head = match &*desc {
            TypeDesc::Tconstr { path, .. } => format!("Tconstr({})", path.name()),
            TypeDesc::Tarrow { .. } => "Tarrow".to_string(),
            TypeDesc::Ttuple(_) => "Ttuple".to_string(),
            TypeDesc::Tvar(_) => "Tvar".to_string(),
            TypeDesc::Tunivar(_) => "Tunivar".to_string(),
            TypeDesc::Tobject { .. } => "Tobject".to_string(),
            TypeDesc::Tfield { .. } => "Tfield".to_string(),
            TypeDesc::Tlink(_) => "Tlink".to_string(),
            TypeDesc::Tsubst(_) => "Tsubst".to_string(),
            TypeDesc::Tvariant(_) => "Tvariant".to_string(),
            TypeDesc::Tpoly { .. } => "Tpoly".to_string(),
            TypeDesc::Tpackage { .. } => "Tpackage".to_string(),
            TypeDesc::Tnil => "Tnil".to_string(),
        };
        out.push(format!("ref#{}@{}:{head}", ty.0, ctx.get_level(ty)));
        drop(desc);

        match &*ctx.get_desc(ty) {
            TypeDesc::Tarrow { args, ret } => {
                for arg in args {
                    walk(ctx, arg.typ, out, seen);
                }
                walk(ctx, *ret, out, seen);
            }
            TypeDesc::Ttuple(items) => {
                for item in items {
                    walk(ctx, *item, out, seen);
                }
            }
            TypeDesc::Tconstr { args, .. } => {
                for item in args {
                    walk(ctx, *item, out, seen);
                }
            }
            TypeDesc::Tobject { fields, .. } => walk(ctx, *fields, out, seen),
            TypeDesc::Tfield { typ, rest, .. } => {
                walk(ctx, *typ, out, seen);
                walk(ctx, *rest, out, seen);
            }
            TypeDesc::Tlink(target) | TypeDesc::Tsubst(target) => walk(ctx, *target, out, seen),
            TypeDesc::Tvariant(row) => {
                walk(ctx, row.row_more, out, seen);
                for (_, field) in &row.row_fields {
                    match field {
                        RowField::Rpresent(Some(inner)) => walk(ctx, *inner, out, seen),
                        RowField::Reither { types, .. } => {
                            for inner in types {
                                walk(ctx, *inner, out, seen);
                            }
                        }
                        _ => {}
                    }
                }
            }
            TypeDesc::Tpoly { body, vars } => {
                walk(ctx, *body, out, seen);
                for inner in vars {
                    walk(ctx, *inner, out, seen);
                }
            }
            TypeDesc::Tpackage { args, .. } => {
                for inner in args {
                    walk(ctx, *inner, out, seen);
                }
            }
            TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) | TypeDesc::Tnil => {}
        }
    }

    let mut out = Vec::new();
    let mut seen = HashSet::new();
    walk(ctx, ty, &mut out, &mut seen);
    out.join(", ")
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
    matches!(
        name,
        "int"
            | "char"
            | "float"
            | "bool"
            | "unit"
            | "exn"
            | "array"
            | "list"
            | "option"
            | "nativeint"
            | "int32"
            | "int64"
            | "lazy_t"
            | "bytes"
            | "string"
            | "ref"
            | "result"
            | "dict"
            | "promise"
            | "unknown"
            | "bigint"
            | "symbol"
            | "regexp"
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
        if flags & 1 != 0 { id.with_global() } else { id }
    } else if stamp < 1000 {
        if let Some(predef_id) = crate::types::predef::find_predef_ident(name) {
            // Predef type: use matching predef ident with correct stamp.
            predef_id
        } else {
            // Non-predef with small stamp: preserve original.
            Ident::new(
                name,
                stamp,
                crate::ident::IdentFlags::from_bits_truncate(flags),
            )
        }
    } else {
        Ident::new(
            name,
            stamp,
            crate::ident::IdentFlags::from_bits_truncate(flags),
        )
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
            Path::Pdot(std::sync::Arc::new(prefix), name.into(), pos)
        }
        OcamlValue::Block(2, fields) => {
            let f = read_path(&fields[0]);
            let a = read_path(&fields[1]);
            Path::Papply(std::sync::Arc::new(f), std::sync::Arc::new(a))
        }
        _ => Path::Pident(Ident::create_persistent("?")), // fallback
    }
}

/// Read a Lexing.position.
fn read_position(ctx: &TypeContext, value: &OcamlValue) -> Position {
    let fields = &value.as_block().1;
    let file_name = ctx.intern_cmi_longident_name(fields[0].as_string());
    Position {
        file_name,
        line: fields[1].as_int() as i32,
        bol: fields[2].as_int() as i32,
        cnum: fields[3].as_int() as i32,
    }
}

/// Read a Location.t.
fn read_location(ctx: &TypeContext, value: &OcamlValue) -> Location {
    let fields = &value.as_block().1;
    Location {
        loc_start: read_position(ctx, &fields[0]),
        loc_end: read_position(ctx, &fields[1]),
        loc_ghost: fields[2].as_bool(),
    }
}

fn read_attribute_name(
    ctx: &TypeContext,
    value: &OcamlValue,
) -> crate::types::asttypes::Located<String> {
    match value {
        OcamlValue::String(name) => crate::types::asttypes::Located::noloc(name.clone()),
        OcamlValue::Block(_, fields) if !fields.is_empty() => match &fields[0] {
            // `string Asttypes.loc` = `{txt; loc}`.
            OcamlValue::String(name) if fields.len() == 2 => crate::types::asttypes::Located {
                txt: name.clone(),
                loc: read_location(ctx, &fields[1]),
            },
            OcamlValue::String(name) => crate::types::asttypes::Located::noloc(name.clone()),
            inner => crate::types::asttypes::Located::noloc(
                read_first_string(inner).unwrap_or_else(|| "?".to_string()),
            ),
        },
        other => crate::types::asttypes::Located::noloc(
            read_first_string(other).unwrap_or_else(|| "?".to_string()),
        ),
    }
}

fn read_first_string(value: &OcamlValue) -> Option<String> {
    match value {
        OcamlValue::String(s) => Some(s.clone()),
        OcamlValue::Block(_, fields) => fields.iter().find_map(read_first_string),
        _ => None,
    }
}

/// Read attributes from a CMI declaration.
///
/// The JS backend relies on simple constructor `@as(...)` payloads from loaded
/// interfaces, so preserve the payload forms the OCaml backend observes for
/// null/undefined identifiers and simple string literals.
/// Convert a marshalled `Parsetree.payload` into its portable form. The only
/// Parsetree record laid out as `{string; int; int; int}` is
/// `Lexing.position`, which is kept explicit for the writers' position
/// sharing. Returns `None` for values a payload cannot contain (floats).
pub(crate) fn payload_value_from_ocaml(
    value: &OcamlValue,
) -> Option<crate::types::decl::PayloadValue> {
    use crate::types::decl::PayloadValue;
    Some(match value {
        OcamlValue::Int(n) => PayloadValue::Int(*n),
        OcamlValue::String(s) => PayloadValue::Str(s.clone()),
        OcamlValue::Float(_) => return None,
        OcamlValue::Block(tag, fields) => match (&**fields, *tag) {
            (
                [
                    OcamlValue::String(file),
                    OcamlValue::Int(line),
                    OcamlValue::Int(bol),
                    OcamlValue::Int(cnum),
                ],
                0,
            ) => PayloadValue::Position {
                file: file.clone(),
                line: *line as i32,
                bol: *bol as i32,
                cnum: *cnum as i32,
            },
            _ => PayloadValue::Block(
                *tag,
                fields
                    .iter()
                    .map(payload_value_from_ocaml)
                    .collect::<Option<Vec<_>>>()?,
            ),
        },
    })
}

fn read_attributes(ctx: &TypeContext, value: &OcamlValue) -> Vec<Attribute> {
    value
        .as_list()
        .iter()
        .filter_map(|attr| match attr {
            OcamlValue::Block(_, fields) if !fields.is_empty() => {
                let attr_name = read_attribute_name(ctx, &fields[0]);
                let payload = if fields.len() > 1 {
                    if attr_name.txt == "deprecated" {
                        read_deprecated_attribute_payload(&fields[1])
                    } else {
                        read_attribute_payload(&fields[1])
                    }
                } else {
                    AttributePayload::Empty
                };
                Some(Attribute {
                    attr_name,
                    attr_payload: payload,
                    attr_loc: fields
                        .get(2)
                        .map(|loc| read_location(ctx, loc))
                        .unwrap_or_else(Location::none),
                    attr_payload_raw: fields
                        .get(1)
                        .and_then(payload_value_from_ocaml)
                        .map(Box::new),
                })
            }
            _ => None,
        })
        .collect()
}

/// Read an attribute payload from a CMI.
/// OCaml payload type: attribute_payload = PStr | PSig | PTyp | PPat
fn read_attribute_payload(value: &OcamlValue) -> AttributePayload {
    match value {
        // PStr(structure) — tag 0
        OcamlValue::Block(0, fields) if !fields.is_empty() => {
            let structure = &fields[0];
            if let Some(name) = extract_ident_payload_name(structure) {
                return match name.as_str() {
                    "true" => AttributePayload::Bool(true),
                    "false" => AttributePayload::Bool(false),
                    _ => AttributePayload::Ident(name),
                };
            }
            if let Some(s) = extract_str_payload_string(structure) {
                AttributePayload::Str(s)
            } else {
                AttributePayload::Empty
            }
        }
        _ => AttributePayload::Empty,
    }
}

fn read_deprecated_attribute_payload(value: &OcamlValue) -> AttributePayload {
    match value {
        OcamlValue::Block(0, fields) if !fields.is_empty() => {
            let structure = &fields[0];
            // `string_of_payload` (builtin_attributes.ml:23-26): a single
            // string constant is the plain `@deprecated("reason")` form.
            if let Some(reason) = plain_string_payload(structure) {
                return AttributePayload::Str(reason);
            }
            let Some(reason) = extract_str_payload_string(structure) else {
                return AttributePayload::Empty;
            };
            AttributePayload::Deprecated {
                reason,
                can_be_automigrated: deprecated_payload_has_migration_template(structure),
                migrate: None,
                migrate_in_pipe_chain: None,
            }
        }
        _ => AttributePayload::Empty,
    }
}

/// `PStr [{pstr_desc = Pstr_eval ({pexp_desc = Pexp_constant
/// (Pconst_string (s, _))}, _)}]`, given the marshaled structure list.
fn plain_string_payload(structure: &OcamlValue) -> Option<String> {
    let OcamlValue::Block(0, cons) = structure else {
        return None;
    };
    let [item, OcamlValue::Int(0)] = cons.as_ref() else {
        return None;
    };
    let OcamlValue::Block(0, item) = item else {
        return None;
    };
    // Pstr_eval (expression, attributes)
    let OcamlValue::Block(0, eval) = item.first()? else {
        return None;
    };
    let OcamlValue::Block(0, expr) = eval.first()? else {
        return None;
    };
    // Pexp_constant constant
    let OcamlValue::Block(1, constant) = expr.first()? else {
        return None;
    };
    // Pconst_string (string, delimiter)
    let OcamlValue::Block(2, string) = constant.first()? else {
        return None;
    };
    match string.first()? {
        OcamlValue::String(s) => Some(s.clone()),
        _ => None,
    }
}

fn deprecated_payload_has_migration_template(value: &OcamlValue) -> bool {
    fn visit(value: &OcamlValue, depth: usize) -> bool {
        if depth > 16 {
            return false;
        }
        match value {
            OcamlValue::String(value) => value == "migrate" || value == "migrateInPipeChain",
            OcamlValue::Block(_, fields) => fields.iter().any(|field| visit(field, depth + 1)),
            _ => false,
        }
    }
    visit(value, 0)
}

/// Try to extract an identifier-like payload from a marshaled PStr payload.
///
/// OCaml stores `@as(null)` / `@as(undefined)` inside the expression node as a
/// nested `Block(0, [String("null")])` / `Block(0, [String("undefined")])`.
fn extract_ident_payload_name(structure: &OcamlValue) -> Option<String> {
    fn find_ident_in_value(v: &OcamlValue, depth: usize) -> Option<String> {
        if depth > 12 {
            return None;
        }
        match v {
            OcamlValue::Block(0, fields)
                if fields.len() == 1
                    && matches!(
                        fields[0],
                        OcamlValue::String(ref name)
                            if matches!(
                                name.as_str(),
                                "null" | "undefined" | "true" | "false"
                            )
                    ) =>
            {
                match &fields[0] {
                    OcamlValue::String(name) => Some(name.clone()),
                    _ => None,
                }
            }
            OcamlValue::Block(_, fields) => fields
                .iter()
                .find_map(|field| find_ident_in_value(field, depth + 1)),
            _ => None,
        }
    }
    find_ident_in_value(structure, 0)
}

/// Try to extract a string constant from a PStr attribute payload.
///
/// For `@as("foo")`, the expression subtree contains a constant-string node
/// encoded as `Block(2, [String("foo"), ...])`.
fn extract_str_payload_string(structure: &OcamlValue) -> Option<String> {
    fn find_string_constant(v: &OcamlValue, depth: usize) -> Option<String> {
        if depth > 12 {
            return None;
        }
        match v {
            OcamlValue::Block(2, fields) if !fields.is_empty() => match &fields[0] {
                OcamlValue::String(value) => Some(value.clone()),
                _ => fields
                    .iter()
                    .find_map(|field| find_string_constant(field, depth + 1)),
            },
            OcamlValue::Block(_, fields) => fields
                .iter()
                .find_map(|field| find_string_constant(field, depth + 1)),
            _ => None,
        }
    }
    find_string_constant(structure, 0)
}

/// Read a Primitive.description.
///
/// Record fields (primitive.ml):
/// 0: prim_name: string
/// 1: prim_arity: int
/// 2: prim_alloc: bool
/// 3: prim_kind: prim_kind
/// 4: prim_from_constructor: bool
fn read_primitive_description(value: &OcamlValue) -> PrimitiveDescription {
    let fields = &value.as_block().1;
    PrimitiveDescription {
        prim_name: fields[0].as_string().to_string(),
        prim_arity: fields[1].as_int() as i32,
        prim_kind: super::ffi_decode::prim_kind(&fields[3])
            .unwrap_or(crate::types::decl::PrimKind::KindIntrinsic),
        prim_native_float: false,
        prim_from_constructor: fields[4].as_bool(),
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
fn read_arg_label(ctx: &TypeContext, value: &OcamlValue) -> ArgLabel {
    match value {
        OcamlValue::Int(0) => ArgLabel::Nolabel,
        OcamlValue::Block(0, fields) => {
            // Labelled(string loc) - string loc is {txt: string; loc: Location.t}
            let loc_fields = &fields[0].as_block().1;
            let name = loc_fields[0].as_string().to_string();
            ArgLabel::Labelled(Located::new(name, read_location(ctx, &loc_fields[1])))
        }
        OcamlValue::Block(1, fields) => {
            // Optional(string loc) - string loc is {txt: string; loc: Location.t}
            let loc_fields = &fields[0].as_block().1;
            let name = loc_fields[0].as_string().to_string();
            ArgLabel::Optional(Located::new(name, read_location(ctx, &loc_fields[1])))
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

/// Read field_kind.
fn read_field_kind(_value: &OcamlValue) -> FieldKind {
    // For CMI-loaded types, just use Fpresent.
    FieldKind::Fpresent
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    fn block(tag: u8, fields: Vec<OcamlValue>) -> OcamlValue {
        OcamlValue::Block(tag, Arc::from(fields))
    }

    fn cmi_ident_pstr(name: &str) -> OcamlValue {
        block(
            0,
            vec![block(
                0,
                vec![block(0, vec![OcamlValue::String(name.to_string())])],
            )],
        )
    }

    fn cmi_string_pstr(value: &str) -> OcamlValue {
        block(
            0,
            vec![block(
                0,
                vec![block(
                    1,
                    vec![block(
                        2,
                        vec![
                            OcamlValue::String(value.to_string()),
                            block(0, vec![OcamlValue::String("*j".to_string())]),
                        ],
                    )],
                )],
            )],
        )
    }

    #[test]
    fn reads_cmi_null_ident_payload_as_ident_not_string() {
        assert_eq!(
            read_attribute_payload(&cmi_ident_pstr("null")),
            AttributePayload::Ident("null".to_string())
        );
    }

    #[test]
    fn reads_cmi_undefined_ident_payload_as_ident_not_string() {
        assert_eq!(
            read_attribute_payload(&cmi_ident_pstr("undefined")),
            AttributePayload::Ident("undefined".to_string())
        );
    }

    #[test]
    fn keeps_cmi_string_literal_payload_distinct_from_identifier_payload() {
        assert_eq!(
            read_attribute_payload(&cmi_string_pstr("null")),
            AttributePayload::Str("null".to_string())
        );
        assert_eq!(
            read_attribute_payload(&cmi_string_pstr("fulfilled")),
            AttributePayload::Str("fulfilled".to_string())
        );
    }
}
