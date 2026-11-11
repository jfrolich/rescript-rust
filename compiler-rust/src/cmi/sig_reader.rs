//! Signature reader: converts generic OCaml marshal values into Rust type structures.
//!
//! This module interprets the `Types.signature_item list` from a CMI file and
//! converts it into the Rust equivalents defined in `types/decl.rs`.
//!
//! # OCaml Type Tags
//!
//! Each OCaml variant constructor gets an integer tag assigned in definition order.
//! Records are blocks with tag 0. See the tag tables in the module-level comments below.

use crate::ident::{Ident};
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
    FieldMutability, GENERIC_LEVEL, MutabilityRef, RowDesc, RowField, TypeArg, TypeDesc,
    TypeExprRef,
};
use crate::types::variance::Variance;
use std::sync::Arc;

use super::marshal_reader::OcamlValue;

use crate::fast_hash::AHashMap;

/// Context for reading signatures, holding the type arena and a table for
/// resolving shared type_expr references.
pub struct SigReadContext<'a> {
    /// The type context for allocating type expressions.
    pub ctx: &'a TypeContext,
    /// Map from OCaml type_expr id to TypeExprRef, for shared type references.
    type_expr_cache: AHashMap<i64, TypeExprRef>,
    /// OCaml layout refs are shared mutable blocks. Preserve that physical
    /// sharing by mapping their marshal block identity to one TypeContext slot.
    variant_layout_cache: AHashMap<usize, crate::types::VariantLayoutRef>,
    /// Object field mutability cells are shared `ref` blocks; keep their
    /// sharing by marshal block identity.
    mutability_cache: AHashMap<usize, MutabilityRef>,
    /// Scope of location allocation identities decoded from this graph.
    location_scope: u64,
    /// Retained marshal blocks keep pointer keys valid even if this reader
    /// is reused after the caller drops a previously decoded value tree.
    location_blocks: AHashMap<usize, (OcamlValue, u32)>,
    location_positions: AHashMap<u32, Position>,
    /// `Recognized_as` blocks and the cons cells of class ancestors.
    shape_blocks: AHashMap<usize, (OcamlValue, crate::types::ShapeAllocation)>,
    /// Class name strings, by string allocation.
    shape_strings: AHashMap<(u64, u32), crate::types::ShapeString>,
    /// The payload strings of `@instanceOf` attributes read so far, by
    /// string allocation: the class names they are.
    attribute_strings: AHashMap<(u64, u32), crate::types::ShapeString>,
}

/// The address of a marshalled block's fields, which identifies the block.
fn block_address(value: &OcamlValue) -> Option<usize> {
    match value {
        OcamlValue::Block(_, fields) => Some(fields.as_ptr() as usize),
        _ => None,
    }
}

impl<'a> SigReadContext<'a> {
    /// Create a new signature reading context.
    pub fn new(ctx: &'a TypeContext) -> Self {
        SigReadContext {
            ctx,
            type_expr_cache: AHashMap::new(),
            variant_layout_cache: AHashMap::new(),
            mutability_cache: AHashMap::new(),
            location_scope: ctx.fresh_location_scope(),
            location_blocks: AHashMap::new(),
            location_positions: AHashMap::new(),
            shape_blocks: AHashMap::new(),
            shape_strings: AHashMap::new(),
            attribute_strings: AHashMap::new(),
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
                    let id = self.read_ident(&fields[0]);
                    let desc = self.read_value_description(&fields[1]);
                    SignatureItem::SigValue(id, desc)
                }
                1 => {
                    let id = self.read_ident(&fields[0]);
                    let decl = self.read_type_declaration(&fields[1]);
                    let rec_status = read_rec_status(&fields[2]);
                    SignatureItem::SigType(id, std::sync::Arc::new(decl), rec_status)
                }
                2 => {
                    let id = self.read_ident(&fields[0]);
                    let ext = self.read_extension_constructor(&fields[1]);
                    let ext_status = read_ext_status(&fields[2]);
                    SignatureItem::SigTypext(id, ext, ext_status)
                }
                3 => {
                    let id = self.read_ident(&fields[0]);
                    let decl = self.read_module_declaration(&fields[1]);
                    let rec_status = read_rec_status(&fields[2]);
                    SignatureItem::SigModule(id, decl, rec_status)
                }
                4 => {
                    let id = self.read_ident(&fields[0]);
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
        let val_loc = self.read_decl_loc(&fields[2]);
        let val_attributes = self.read_attributes(&fields[3]);

        ValueDescription {
            val_type,
            val_kind,
            val_loc,
            val_attributes: val_attributes.into(),
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
                ValueKind::ValPrim(std::sync::Arc::new(prim))
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
    /// 11: type_shape: Variant_runtime.value_shape
    /// 12: type_inlined_types: type_inlined_type list
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
        let type_loc = self.read_decl_loc(&fields[7]);
        let type_attributes = self.read_attributes(&fields[8]);
        let type_immediate = fields[9].as_bool();
        let type_representation = if fields[10].as_int() == 1 {
            TypeRepresentation::Unboxed
        } else {
            TypeRepresentation::Boxed
        };
        let type_shape = self.read_value_shape(&fields[11]);
        let type_inlined_types = self.read_type_inlined_types(&fields[12]);

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
            type_shape,
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
    /// Constants:     Record_regular=0, Record_array=1, Record_extension=2
    /// Non-constants: Record_unboxed=0, Record_inlined=1
    fn read_record_representation(&mut self, value: &OcamlValue) -> RecordRepresentation {
        match value {
            OcamlValue::Int(0) => RecordRepresentation::RecordRegular,
            OcamlValue::Int(1) => RecordRepresentation::RecordArray,
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

    /// A `field_mutability ref` block (types.mli `field_mutability`).
    fn read_mutability_ref(&mut self, value: &OcamlValue) -> MutabilityRef {
        let (_, fields) = value.as_block();
        let key = fields.as_ptr() as usize;
        if let Some(r) = self.mutability_cache.get(&key) {
            return *r;
        }
        let r = match &fields[0] {
            // Mutability_value of mutable_flag
            OcamlValue::Block(0, flag) => {
                let flag = match flag[0].as_int() {
                    0 => crate::types::asttypes::MutableFlag::Immutable,
                    _ => crate::types::asttypes::MutableFlag::Mutable,
                };
                self.ctx.alloc_mutability(FieldMutability::Value(flag))
            }
            // Mutability_link of field_mutability ref
            OcamlValue::Block(1, link) => self.read_mutability_ref(&link[0]),
            other => panic!("unexpected field_mutability: {other:?}"),
        };
        self.mutability_cache.insert(key, r);
        r
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
                // `Tagged of tagged_block | Untagged of {tag; block_type}`.
                let (block_tag, block) = fields[0].as_block();
                let block = match block_tag {
                    0 => {
                        let (_, runtime) = block[0].as_block();
                        crate::types::VariantBlock::Tagged(crate::types::TaggedBlock {
                            tag: self.read_variant_tag(&runtime[0]),
                            tag_name: self.read_string_option(&runtime[1]),
                        })
                    }
                    1 => crate::types::VariantBlock::Untagged {
                        tag: self.read_variant_tag(&block[0]),
                        block_type: self.read_variant_block_type(&block[1]),
                    },
                    _ => panic!("invalid variant block tag {block_tag}"),
                };
                crate::types::VariantConstructorCase::Block(block)
            }
            _ => panic!("invalid variant constructor case tag {tag}"),
        }
    }

    fn read_variant_tag(&mut self, value: &OcamlValue) -> crate::types::VariantTag {
        let (_, fields) = value.as_block();
        crate::types::VariantTag {
            name: crate::name::Name::new(fields[0].as_string()),
            literal: self.read_variant_literal_tag(&fields[1]),
        }
    }

    /// `Variant_runtime.literal_tag`: `Null`/`Undefined` are the constant
    /// constructors, the others blocks with tags 0-4.
    fn read_variant_literal_tag(&mut self, value: &OcamlValue) -> crate::types::VariantLiteralTag {
        use crate::types::VariantLiteralTag as T;
        match value {
            OcamlValue::Int(0) => T::Null,
            OcamlValue::Int(1) => T::Undefined,
            OcamlValue::Block(tag, fields) => match tag {
                0 => T::String(fields[0].as_string().to_string()),
                1 => T::Int(fields[0].as_int()),
                2 => T::Float(fields[0].as_string().to_string()),
                3 => T::BigInt(fields[0].as_string().to_string()),
                4 => T::Bool(fields[0].as_bool()),
                _ => panic!("invalid variant literal tag {tag}"),
            },
            _ => panic!("invalid variant tag type"),
        }
    }

    /// Read a `Variant_runtime.block_type`, keeping which blocks and strings
    /// of a class are shared: a layout's payload kind is the block of the
    /// payload type's shape.
    fn read_variant_block_type(&mut self, value: &OcamlValue) -> crate::types::VariantBlockType {
        use crate::types::{VariantBlockType as B, VariantInstance as I};
        // `InstanceType (Class {name; ancestors})`
        let OcamlValue::Block(0, fields) = value else {
            return decode_variant_block_type(value);
        };
        let OcamlValue::Block(0, class) = &fields[0] else {
            return B::Instance(I::Array(self.shape_block(value)));
        };
        let block = self.shape_block(value);
        let name_string = self.shape_string(&class[0]);
        let mut ancestors = Vec::new();
        let mut ancestor_blocks = Vec::new();
        let mut cell = &class[1];
        while let OcamlValue::Block(0, cons) = cell {
            ancestors.push(cons[0].as_string().to_string());
            let allocation = self.shape_block(cell);
            ancestor_blocks.push((allocation, self.shape_string(&cons[0])));
            cell = &cons[1];
        }
        B::Instance(I::Class {
            name: class[0].as_string().to_string(),
            ancestors,
            blocks: crate::types::ClassBlocks {
                block,
                name: name_string,
                ancestors: ancestor_blocks,
            },
        })
    }

    fn read_string_option(&self, value: &OcamlValue) -> Option<String> {
        value.as_option().map(|v| v.as_string().to_string())
    }

    /// Read a label_declaration (record field).
    ///
    /// Record fields:
    /// 0: ld_id: Ident.t
    /// 1: ld_runtime_name: string option
    /// 2: ld_mutable: mutable_flag
    /// 3: ld_optional: bool
    /// 4: ld_type: type_expr
    /// 5: ld_loc: Location.t
    /// 6: ld_attributes: attributes
    fn read_label_declaration(&mut self, value: &OcamlValue) -> LabelDeclaration {
        let fields = &value.as_block().1;
        let ld_id = self.read_ident(&fields[0]);
        let ld_runtime_name = fields[1]
            .as_option()
            .map(|name| name.as_string().to_string());
        let ld_mutable = read_mutable_flag(&fields[2]);
        let ld_optional = fields[3].as_bool();
        let ld_type = self.read_type_expr(&fields[4]);
        let ld_loc = self.read_decl_loc(&fields[5]);
        let ld_attributes = self.read_attributes(&fields[6]);

        LabelDeclaration {
            ld_id,
            ld_runtime_name,
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
    /// 1: cd_runtime_tag: Variant_runtime.literal_tag option
    /// 2: cd_args: constructor_arguments
    /// 3: cd_res: type_expr option
    /// 4: cd_loc: Location.t
    /// 5: cd_attributes: attributes
    fn read_constructor_declaration(&mut self, value: &OcamlValue) -> ConstructorDeclaration {
        let fields = &value.as_block().1;
        let cd_id = self.read_ident(&fields[0]);
        let cd_runtime_tag = fields[1]
            .as_option()
            .map(|tag| self.read_variant_literal_tag(tag));
        let cd_args = self.read_constructor_arguments(&fields[2]);
        let cd_res = fields[3].as_option().map(|te| self.read_type_expr(te));
        let cd_loc = self.read_decl_loc(&fields[4]);
        let cd_attributes = self.read_attributes(&fields[5]);

        ConstructorDeclaration {
            cd_id,
            cd_runtime_tag,
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
        let ext_type_path = self.read_path(&fields[0]);
        let ext_type_params: Vec<TypeExprRef> = fields[1]
            .as_list()
            .iter()
            .map(|te| self.read_type_expr(te))
            .collect();
        let ext_args = self.read_constructor_arguments(&fields[2]);
        let ext_ret_type = fields[3].as_option().map(|te| self.read_type_expr(te));
        let ext_private = read_private_flag(&fields[4]);
        let ext_loc = self.read_decl_loc(&fields[5]);
        let ext_attributes = self.read_attributes(&fields[6]);
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
        let md_attributes = self.read_attributes(&fields[1]);
        let md_loc = self.read_decl_loc(&fields[2]);

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
        let mtd_attributes = self.read_attributes(&fields[1]);
        let mtd_loc = self.read_decl_loc(&fields[2]);

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
                let path = self.read_path(&fields[0]);
                ModuleType::MtyIdent(path)
            }
            OcamlValue::Block(1, fields) => {
                let sig_items: Vec<OcamlValue> = fields[0].as_list().into_iter().cloned().collect();
                let signature = self.read_signature(&sig_items);
                ModuleType::MtySignature(std::sync::Arc::new(signature))
            }
            OcamlValue::Block(2, fields) => {
                let param = self.read_ident(&fields[0]);
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
                // The decoded target block, shared by every declaration
                // holding it.
                let path = self.read_shared_path(&fields[1]);
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
                    let name = fields[0]
                        .as_option()
                        .map(|s| crate::name::Name::new(s.as_string()));
                    TypeDesc::Tvar(name)
                }
                1 => {
                    // Caml1999I024 stores the complete parameter list directly;
                    // keep that allocation shape rather than rebuilding unary nodes.
                    let args: crate::types::type_expr::TypeArgs = fields[0]
                        .as_list()
                        .iter()
                        .map(|arg| self.read_arg(arg))
                        .collect();
                    let args = self.ctx.new_type_args(&args);
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
                    TypeDesc::Ttuple(self.ctx.new_type_list(&types))
                }
                3 => {
                    // Tconstr(Path.t, type_expr list, abbrev_memo ref)
                    let path = self.read_path(&fields[0]);
                    let args: Vec<TypeExprRef> = fields[1]
                        .as_list()
                        .iter()
                        .map(|te| self.read_type_expr(te))
                        .collect();
                    let abbrev = self.ctx.alloc_abbrev_nil();

                    TypeDesc::Tconstr {
                        path,
                        args: self.ctx.new_type_list(&args),
                        abbrev,
                    }
                }
                4 => {
                    // Tobject of type_expr
                    TypeDesc::Tobject {
                        fields: self.read_type_expr(&fields[0]),
                    }
                }
                5 => {
                    // Tfield {name; mutability: field_mutability ref; typ; rest}
                    let name = crate::name::Name::new(fields[0].as_string());
                    let mutability = self.read_mutability_ref(&fields[1]);
                    let typ = self.read_type_expr(&fields[2]);
                    let rest = self.read_type_expr(&fields[3]);
                    TypeDesc::Tfield {
                        name,
                        mutability,
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
                    TypeDesc::Tvariant(self.ctx.new_row_desc(row))
                }
                9 => {
                    // Tunivar(string option)
                    let name = fields[0]
                        .as_option()
                        .map(|s| crate::name::Name::new(s.as_string()));
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
                    TypeDesc::Tpoly {
                        body,
                        vars: self.ctx.new_type_list(&vars),
                    }
                }
                11 => {
                    // Tpackage(Path.t, Longident.t list, type_expr list)
                    let path = self.read_path(&fields[0]);
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
                    TypeDesc::Tpackage {
                        path,
                        lids: self.ctx.new_package_lids(lids),
                        args: self.ctx.new_type_list(&args),
                    }
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
        let typ = self.read_type_expr(&fields[1]);
        TypeArg::new(self.read_arg_label(&fields[0]), typ)
    }

    fn read_ident(&mut self, value: &OcamlValue) -> Ident {
        read_ident_value(value)
    }

    fn read_path(&mut self, value: &OcamlValue) -> Path {
        match value {
            OcamlValue::Block(0, fields) => Path::pident(self.read_ident(&fields[0])),
            OcamlValue::Block(1, fields) => Path::pdot_pos(
                self.read_path(&fields[0]),
                fields[1].as_string(),
                fields[2].as_int() as i32,
            ),
            OcamlValue::Block(2, fields) => {
                Path::papply(self.read_path(&fields[0]), self.read_path(&fields[1]))
            }
            _ => Path::pident(Ident::create_persistent("?")),
        }
    }

    fn read_shared_path(&mut self, value: &OcamlValue) -> Arc<Path> {
        Arc::new(self.read_path(value))
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
            let path = self.read_path(&f[0]);
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

// ============================================================================
// Pure functions (no context needed)
// ============================================================================

/// The `Ident.t` value of a marshalled identifier.
fn read_ident_value(value: &OcamlValue) -> Ident {
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

impl SigReadContext<'_> {
    fn location_block(&mut self, value: &OcamlValue) -> u32 {
        let key = block_address(value).expect("location and position must be marshal blocks");
        let next = u32::try_from(self.location_blocks.len())
            .expect("decoded location block identities exhausted");
        self.location_blocks
            .entry(key)
            .or_insert_with(|| (value.clone(), next))
            .1
    }
    /// Decode a location without merging equal-coordinate allocations.
    fn read_decl_loc(&mut self, value: &OcamlValue) -> crate::types::DeclLoc {
        let fields = &value.as_block().1;
        let identity = crate::types::decl_loc::LocationIdentity {
            scope: self.location_scope,
            location: self.location_block(value),
            start: self.location_block(&fields[0]),
            end: self.location_block(&fields[1]),
        };
        let start = *self
            .location_positions
            .entry(identity.start)
            .or_insert_with(|| read_position(self.ctx, &fields[0]));
        let end = *self
            .location_positions
            .entry(identity.end)
            .or_insert_with(|| read_position(self.ctx, &fields[1]));
        self.ctx.intern_loc_with_identity(
            Location {
                loc_start: start,
                loc_end: end,
                loc_ghost: fields[2].as_bool(),
                origin: Default::default(),
            },
            identity,
        )
    }
    fn read_attribute_name(
        &mut self,
        value: &OcamlValue,
    ) -> crate::types::asttypes::Located<String, crate::types::DeclLoc> {
        match value {
            OcamlValue::String(name) => crate::types::asttypes::Located::noloc(name.to_string()),
            OcamlValue::Block(_, fields) if !fields.is_empty() => match &fields[0] {
                // `string Asttypes.loc` = `{txt; loc}`.
                OcamlValue::String(name) if fields.len() == 2 => crate::types::asttypes::Located {
                    txt: name.to_string(),
                    loc: self.read_decl_loc(&fields[1]),
                },
                OcamlValue::String(name) => {
                    crate::types::asttypes::Located::noloc(name.to_string())
                }
                inner => crate::types::asttypes::Located::noloc(
                    read_first_string(inner).unwrap_or_else(|| "?".to_string()),
                ),
            },
            other => crate::types::asttypes::Located::noloc(
                read_first_string(other).unwrap_or_else(|| "?".to_string()),
            ),
        }
    }
    /// Preserve the attribute payload forms observed by the JS backend.
    fn read_attributes(&mut self, value: &OcamlValue) -> Vec<Attribute> {
        value
            .as_list()
            .iter()
            .filter_map(|attr| match attr {
                OcamlValue::Block(_, fields) if !fields.is_empty() => {
                    let attr_name = self.read_attribute_name(&fields[0]);
                    if attr_name.txt == "instanceOf"
                        && let Some(allocation) = fields
                            .get(1)
                            .and_then(payload_semantic_string)
                            .and_then(|semantic| semantic.allocation())
                    {
                        let string = crate::types::ShapeString::attribute(self.ctx, attr_name.loc);
                        self.attribute_strings.insert(allocation, string);
                    }
                    let payload = if fields.len() > 1 {
                        if attr_name.txt == "deprecated" {
                            read_deprecated_attribute_payload(&fields[1], &mut |loc| {
                                self.read_decl_loc(loc)
                            })
                        } else {
                            read_attribute_payload(&fields[1], &mut |loc| self.read_decl_loc(loc))
                        }
                    } else {
                        AttributePayload::Empty
                    };
                    Some(Attribute {
                        attr_name,
                        attr_payload: payload,
                        attr_loc: fields
                            .get(2)
                            .map(|loc| self.read_decl_loc(loc))
                            .unwrap_or_default(),
                    })
                }
                _ => None,
            })
            .collect()
    }
    /// Read a `Variant_runtime.value_shape`, keeping which of its blocks
    /// are shared.
    fn read_value_shape(&mut self, value: &OcamlValue) -> crate::types::ValueShape {
        let OcamlValue::Block(0, fields) = value else {
            return decode_value_shape(value);
        };
        let block_type = self.read_variant_block_type(&fields[0]);
        let blocks = crate::types::ShapeBlocks {
            block: self.shape_block(value),
        };
        crate::types::ValueShape::recognized_as(block_type, blocks)
    }

    fn shape_block(&mut self, value: &OcamlValue) -> crate::types::ShapeAllocation {
        let address = block_address(value).expect("a shape block");
        self.shape_blocks
            .entry(address)
            .or_insert_with(|| (value.clone(), crate::types::ShapeAllocation::fresh()))
            .1
    }

    /// A class name: the payload string of an `@instanceOf` read before it,
    /// or a string of its own.
    fn shape_string(&mut self, value: &OcamlValue) -> crate::types::ShapeString {
        use crate::types::{ShapeAllocation, ShapeString};
        let OcamlValue::String(string) = value else {
            panic!("a class name string")
        };
        let Some(allocation) = string.allocation() else {
            return ShapeString::Allocation(ShapeAllocation::fresh());
        };
        if let Some(string) = self.attribute_strings.get(&allocation) {
            return *string;
        }
        *self
            .shape_strings
            .entry(allocation)
            .or_insert_with(|| ShapeString::Allocation(ShapeAllocation::fresh()))
    }

    fn read_arg_label(&mut self, value: &OcamlValue) -> ArgLabel {
        match value {
            OcamlValue::Int(0) => ArgLabel::Nolabel,
            OcamlValue::Block(0, fields) => {
                // Labelled(string loc) - string loc is {txt: string; loc: Location.t}
                let loc_fields = &fields[0].as_block().1;
                let name = loc_fields[0].as_string().to_string();
                ArgLabel::Labelled(Located::new(name, self.read_decl_loc(&loc_fields[1])))
            }
            OcamlValue::Block(1, fields) => {
                // Optional(string loc) - string loc is {txt: string; loc: Location.t}
                let loc_fields = &fields[0].as_block().1;
                let name = loc_fields[0].as_string().to_string();
                ArgLabel::Optional(Located::new(name, self.read_decl_loc(&loc_fields[1])))
            }
            _ => ArgLabel::Nolabel,
        }
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

fn read_first_string(value: &OcamlValue) -> Option<String> {
    match value {
        OcamlValue::String(s) => Some(s.to_string()),
        OcamlValue::Block(_, fields) => fields.iter().find_map(read_first_string),
        _ => None,
    }
}

/// Read an attribute payload from a CMI.
/// OCaml payload type: attribute_payload = PStr | PSig | PTyp | PPat
/// `read_loc` decodes the location of a template that fails to decode.
fn read_attribute_payload(
    value: &OcamlValue,
    read_loc: &mut dyn FnMut(&OcamlValue) -> crate::types::DeclLoc,
) -> AttributePayload {
    match value {
        // PStr(structure) — tag 0
        OcamlValue::Block(0, fields) if !fields.is_empty() => {
            let structure = &fields[0];
            if let Some(payload) = semantic_string_payload(structure, read_loc) {
                return AttributePayload::SemanticString(Box::new(payload));
            }
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

/// `PStr [{pstr_desc = Pstr_eval (e, _)}]` where `e` is braces around a
/// string constant, or a backquoted string without interpolation in braces
/// or not: the payloads `Ast_payload.semantic_string_of_payload` reads
/// besides a bare string constant (compiler/ml/ast_payload.ml:39-51).
fn semantic_string_payload(
    structure: &OcamlValue,
    read_loc: &mut dyn FnMut(&OcamlValue) -> crate::types::DeclLoc,
) -> Option<crate::types::decl::SemanticStringPayload> {
    // [item]
    let OcamlValue::Block(0, cons) = structure else {
        return None;
    };
    if !matches!(cons.get(1), Some(OcamlValue::Int(0))) {
        return None;
    }
    // {pstr_desc = Pstr_eval (e, _); pstr_loc}
    let OcamlValue::Block(0, item) = &cons[0] else {
        return None;
    };
    let OcamlValue::Block(0, eval) = &item[0] else {
        return None;
    };
    // {pexp_desc; pexp_loc; pexp_attributes}
    let mut expression = &eval[0];
    let mut braces = 0;
    loop {
        let OcamlValue::Block(0, record) = expression else {
            return None;
        };
        match &record[0] {
            // Pexp_braces {expr; braces_loc}
            OcamlValue::Block(0, inner) => {
                braces += 1;
                expression = &inner[0];
            }
            // Pexp_constant (Pconst_string literal)
            OcamlValue::Block(2, constant) if braces > 0 => {
                let OcamlValue::Block(2, literal) = &constant[0] else {
                    return None;
                };
                return Some(crate::types::decl::SemanticStringPayload {
                    semantic: Ok(string_literal_semantic(&literal[0])?),
                    braces,
                    template: false,
                });
            }
            // Pexp_template {source_segments = [{txt}]; values = []}
            OcamlValue::Block(38, template) => {
                let OcamlValue::Block(0, segments) = &template[0] else {
                    return None;
                };
                if !matches!(segments.get(1), Some(OcamlValue::Int(0)))
                    || !matches!(template.get(1), Some(OcamlValue::Int(0)))
                {
                    return None;
                }
                let OcamlValue::Block(0, segment) = &segments[0] else {
                    return None;
                };
                let source = segment[0].as_string_opt()?;
                // `Location.raise_errorf ~loc:pexp_loc` when it does not
                // decode (compiler/ml/ast_payload.ml:39-51).
                let semantic = crate::string_literal::decode_js_template_escapes(source)
                    .ok_or_else(|| read_loc(&record[1]));
                return Some(crate::types::decl::SemanticStringPayload {
                    semantic,
                    braces,
                    template: true,
                });
            }
            _ => return None,
        }
    }
}

/// A `@deprecated` payload: the record form `deprecated_of_attrs_with_migrate`
/// reads (builtin_attributes.ml:68-112), or the payload `string_of_payload`
/// reads.
fn read_deprecated_attribute_payload(
    value: &OcamlValue,
    read_loc: &mut dyn FnMut(&OcamlValue) -> crate::types::DeclLoc,
) -> AttributePayload {
    deprecated_record_payload(value, read_loc)
        .unwrap_or_else(|| read_attribute_payload(value, read_loc))
}

/// `PStr [{pstr_desc = Pstr_eval ({pexp_desc = Pexp_record (fields, _)}, _)}]`
/// after `Ast_payload.unwrap_payload_expression`, given the marshaled
/// `PStr` payload.
fn deprecated_record_payload(
    value: &OcamlValue,
    read_loc: &mut dyn FnMut(&OcamlValue) -> crate::types::DeclLoc,
) -> Option<AttributePayload> {
    // PStr structure
    let OcamlValue::Block(0, payload) = value else {
        return None;
    };
    let OcamlValue::Block(0, cons) = payload.first()? else {
        return None;
    };
    let [item, OcamlValue::Int(0)] = cons.as_ref() else {
        return None;
    };
    // {pstr_desc = Pstr_eval (e, _); pstr_loc}
    let OcamlValue::Block(0, item) = item else {
        return None;
    };
    let OcamlValue::Block(0, eval) = item.first()? else {
        return None;
    };
    // Pexp_record (fields, _), tag 11 in parsetree.ml `expression_desc`.
    let OcamlValue::Block(11, record) = &unwrap_braces_value(eval.first()?)?[0] else {
        return None;
    };
    let mut reason = Ok(None);
    let mut can_be_automigrated = false;
    let mut fields = record.first()?;
    // record_element list: {lid = {txt; loc}; x; opt}
    while let OcamlValue::Block(0, cell) = fields {
        if let OcamlValue::Block(0, field) = &cell[0] {
            match lident_name(&field[0]) {
                // builtin_attributes.ml:72-78: the first `reason` field that
                // is a string.
                Some("reason") if matches!(reason, Ok(None)) => {
                    reason = expression_semantic_string(&field[1], read_loc);
                }
                Some("migrate" | "migrateInPipeChain") => can_be_automigrated = true,
                _ => {}
            }
        }
        fields = &cell[1];
    }
    Some(AttributePayload::Deprecated {
        reason,
        can_be_automigrated,
        migrate: None,
        migrate_in_pipe_chain: None,
    })
}

/// The `Lident` name of a marshaled `Longident.t loc`.
fn lident_name(lid: &OcamlValue) -> Option<&str> {
    let OcamlValue::Block(0, lid) = lid else {
        return None;
    };
    let OcamlValue::Block(0, lident) = lid.first()? else {
        return None;
    };
    lident.first()?.as_string_opt()
}

/// The fields of a marshaled expression record under its `Pexp_braces`
/// (`Ast_payload.unwrap_braces`).
fn unwrap_braces_value(expression: &OcamlValue) -> Option<&[OcamlValue]> {
    let mut expression = expression;
    loop {
        let OcamlValue::Block(0, record) = expression else {
            return None;
        };
        match record.first()? {
            // Pexp_braces {expr; braces_loc}
            OcamlValue::Block(0, inner) => expression = inner.first()?,
            _ => return Some(record),
        }
    }
}

/// `Ast_payload.semantic_string_of_expression` (ast_payload.ml:39-51) of a
/// marshaled expression; `Err` is the template's `pexp_loc` where it raises.
fn expression_semantic_string(
    expression: &OcamlValue,
    read_loc: &mut dyn FnMut(&OcamlValue) -> crate::types::DeclLoc,
) -> Result<Option<String>, crate::types::DeclLoc> {
    let Some(record) = unwrap_braces_value(expression) else {
        return Ok(None);
    };
    match &record[0] {
        // Pexp_constant (Pconst_string literal)
        OcamlValue::Block(2, constant) => match constant.first() {
            Some(OcamlValue::Block(2, literal)) => {
                Ok(literal.first().and_then(string_literal_semantic))
            }
            _ => Ok(None),
        },
        // Pexp_template {source_segments = [{txt}]; values = []}
        OcamlValue::Block(38, template) => {
            let (Some(OcamlValue::Block(0, segments)), Some(OcamlValue::Int(0))) =
                (template.first(), template.get(1))
            else {
                return Ok(None);
            };
            let [OcamlValue::Block(0, segment), OcamlValue::Int(0)] = segments.as_ref() else {
                return Ok(None);
            };
            let Some(source) = segment.first().and_then(OcamlValue::as_string_opt) else {
                return Ok(None);
            };
            match crate::string_literal::decode_js_template_escapes(source) {
                Some(semantic) => Ok(Some(semantic)),
                None => Err(read_loc(&record[1])),
            }
        }
        _ => Ok(None),
    }
}

/// `String_literal.string_semantic` of a marshaled `String_literal.payload`:
/// `Valid {source; semantic}` (tag 0) or `Invalid_source source` (tag 1).
fn string_literal_semantic(payload: &OcamlValue) -> Option<String> {
    match payload {
        OcamlValue::Block(0, fields) => match fields.as_ref() {
            [OcamlValue::String(_), OcamlValue::String(semantic)] => Some(semantic.to_string()),
            _ => None,
        },
        OcamlValue::Block(1, fields) => match fields.as_ref() {
            [OcamlValue::String(_)] => Some(String::new()),
            _ => None,
        },
        _ => None,
    }
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
                    OcamlValue::String(name) => Some(name.to_string()),
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
/// For `@as("foo")`, the expression subtree contains a `Pconst_string`
/// node encoded as `Block(2, [payload])`, whose `String_literal.payload` holds
/// the source and semantic strings.
fn extract_str_payload_string(structure: &OcamlValue) -> Option<String> {
    fn find_string_constant(v: &OcamlValue, depth: usize) -> Option<String> {
        if depth > 12 {
            return None;
        }
        match v {
            OcamlValue::Block(2, fields)
                if fields.len() == 1 && string_literal_semantic(&fields[0]).is_some() =>
            {
                string_literal_semantic(&fields[0])
            }
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

/// Read alias_presence.
fn read_alias_presence(value: &OcamlValue) -> AliasPresence {
    match value.as_int() {
        0 => AliasPresence::MtaPresent,
        1 => AliasPresence::MtaAbsent,
        _ => AliasPresence::MtaPresent,
    }
}

/// Decode a marshalled `Variant_runtime.block_type`: the constant
/// constructors in declaration order, `InstanceType` the only block. A class
/// gets blocks of its own: the JS metadata of a `.cmj` is never sized.
pub(crate) fn decode_variant_block_type(value: &OcamlValue) -> crate::types::VariantBlockType {
    use crate::types::{VariantBlockType as B, VariantInstance as I};
    match value {
        OcamlValue::Int(0) => B::Number,
        OcamlValue::Int(1) => B::String,
        OcamlValue::Int(2) => B::Bigint,
        OcamlValue::Int(3) => B::Boolean,
        OcamlValue::Int(4) => B::Symbol,
        OcamlValue::Int(5) => B::Function,
        OcamlValue::Int(6) => B::Object,
        OcamlValue::Int(7) => B::Unknown,
        OcamlValue::Block(0, fields) => B::Instance(match &fields[0] {
            OcamlValue::Int(0) => I::Array(crate::types::ShapeAllocation::fresh()),
            OcamlValue::Block(0, class) => {
                let ancestors: Vec<String> = class[1]
                    .as_list()
                    .iter()
                    .map(|ancestor| ancestor.as_string().to_string())
                    .collect();
                I::Class {
                    name: class[0].as_string().to_string(),
                    blocks: crate::types::ClassBlocks::fresh(ancestors.len()),
                    ancestors,
                }
            }
            other => panic!("invalid variant instance {other:?}"),
        }),
        other => panic!("invalid variant block type {other:?}"),
    }
}

/// Decode a marshalled `Variant_runtime.value_shape` without a class.
fn decode_value_shape(value: &OcamlValue) -> crate::types::ValueShape {
    use crate::types::ValueShape;
    match value {
        OcamlValue::Int(0) => ValueShape::Unstated,
        OcamlValue::Int(1) => ValueShape::NeverUndefined,
        other => panic!("invalid value shape {other:?}"),
    }
}

/// The semantic string of a `PStr [Pstr_eval (Pexp_constant (Pconst_string
/// (Valid {source; semantic})), _)]` payload.
fn payload_semantic_string(payload: &OcamlValue) -> Option<&super::marshal_reader::OcamlString> {
    fn find(v: &OcamlValue, depth: usize) -> Option<&super::marshal_reader::OcamlString> {
        if depth > 12 {
            return None;
        }
        match v {
            OcamlValue::Block(2, fields) if fields.len() == 1 => match &fields[0] {
                OcamlValue::Block(0, literal) => match literal.as_ref() {
                    [OcamlValue::String(_), OcamlValue::String(semantic)] => Some(semantic),
                    _ => None,
                },
                other => find(other, depth + 1),
            },
            OcamlValue::Block(_, fields) => fields.iter().find_map(|field| find(field, depth + 1)),
            _ => None,
        }
    }
    find(payload, 0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Arc;

    fn block(tag: u8, fields: Vec<OcamlValue>) -> OcamlValue {
        OcamlValue::Block(tag, Arc::from(fields))
    }

    /// `Ast_payload.semantic_string_of_payload` reads braces and backquoted
    /// strings without interpolation; an interpolated one is no string.
    #[test]
    fn attribute_payloads_keep_semantic_strings_in_braces_and_templates() {
        use crate::types::decl::SemanticStringPayload;
        let loc = || OcamlValue::Int(0);
        let expression = |desc| block(0, vec![desc, loc(), OcamlValue::Int(0)]);
        let braces = |inner| expression(block(0, vec![inner, loc()]));
        let string = || {
            expression(block(
                2,
                vec![block(
                    2,
                    vec![block(
                        0,
                        vec![
                            OcamlValue::String("A\\x".into()),
                            OcamlValue::String("A\\x".into()),
                        ],
                    )],
                )],
            ))
        };
        let template = |source: &str, values| {
            let segment = block(0, vec![OcamlValue::String(source.into()), loc()]);
            expression(block(
                38,
                vec![block(0, vec![segment, OcamlValue::Int(0)]), values],
            ))
        };
        let payload = |e| {
            let item = block(0, vec![block(0, vec![e, OcamlValue::Int(0)]), loc()]);
            block(0, vec![block(0, vec![item, OcamlValue::Int(0)])])
        };
        let semantic =
            |e| match read_attribute_payload(&payload(e), &mut |_| crate::types::DeclLoc::none()) {
                AttributePayload::SemanticString(payload) => Some(*payload),
                _ => None,
            };
        assert_eq!(
            semantic(template("Intl\\u{2E}Locale", OcamlValue::Int(0))),
            Some(SemanticStringPayload {
                semantic: Ok("Intl.Locale".to_string()),
                braces: 0,
                template: true,
            })
        );
        assert_eq!(
            semantic(braces(braces(template("Foo", OcamlValue::Int(0))))),
            Some(SemanticStringPayload {
                semantic: Ok("Foo".to_string()),
                braces: 2,
                template: true,
            })
        );
        assert_eq!(
            semantic(braces(string())).map(|p| (p.braces, p.template)),
            Some((1, false))
        );
        assert!(matches!(
            read_attribute_payload(&payload(string()), &mut |_| crate::types::DeclLoc::none()),
            AttributePayload::Str(_)
        ));
        let interpolated = block(0, vec![string(), OcamlValue::Int(0)]);
        assert_eq!(semantic(template("F", interpolated)), None);
        // A template that does not decode keeps its location for readers
        // to raise at.
        assert!(matches!(
            semantic(template("Fo\\xo", OcamlValue::Int(0))),
            Some(SemanticStringPayload {
                semantic: Err(_),
                braces: 0,
                template: true,
            })
        ));
    }

    /// A class's blocks read twice are one value, and its name is the
    /// payload string of the `@instanceOf` attribute it was read from.
    #[test]
    fn decoded_shapes_keep_block_and_attribute_string_identity() {
        use crate::cmi::marshal_reader::OcamlString;
        use crate::types::{ShapeString, ValueShape, VariantBlockType, VariantInstance};
        let ctx = TypeContext::new(Arc::new(crate::context::IdGenerator::new()));
        let mut reader = SigReadContext::new(&ctx);
        let position = || {
            block(
                0,
                vec![
                    OcamlValue::String("source.res".into()),
                    OcamlValue::Int(1),
                    OcamlValue::Int(0),
                    OcamlValue::Int(2),
                ],
            )
        };
        let loc = block(0, vec![position(), position(), OcamlValue::Int(0)]);
        let name = OcamlValue::String(OcamlString::decoded("A", (3 << 32) | 1));
        // (({txt = "instanceOf"; loc}, PStr [Pstr_eval (Pexp_constant
        // (Pconst_string (Valid {source; semantic})))]), loc)
        let literal = block(0, vec![OcamlValue::String("A".into()), name.clone()]);
        let expression = block(0, vec![block(2, vec![block(2, vec![literal])])]);
        let payload = block(0, vec![block(0, vec![expression, OcamlValue::Int(0)])]);
        let attribute = block(
            0,
            vec![
                block(
                    0,
                    vec![OcamlValue::String("instanceOf".into()), loc.clone()],
                ),
                payload,
                loc,
            ],
        );
        let attrs = reader.read_attributes(&block(0, vec![attribute, OcamlValue::Int(0)]));
        let class = block(0, vec![block(0, vec![name, OcamlValue::Int(0)])]);
        let shape = block(0, vec![class.clone()]);
        let read = |reader: &mut SigReadContext<'_>, value| match reader.read_value_shape(value) {
            ValueShape::RecognizedAs(shape) => *shape,
            other => panic!("{other:?}"),
        };
        let first = read(&mut reader, &shape);
        let again = read(&mut reader, &shape);
        let other = read(&mut reader, &block(0, vec![class.clone()]));
        assert_eq!(first.blocks, again.blocks);
        assert_ne!(first.blocks, other.blocks);
        let blocks = |shape: &crate::types::RecognizedShape| match &shape.block_type {
            VariantBlockType::Instance(VariantInstance::Class { blocks, .. }) => blocks.clone(),
            other => panic!("{other:?}"),
        };
        assert_eq!(blocks(&first).block, blocks(&other).block);
        assert_eq!(
            blocks(&first).name,
            ShapeString::attribute(&ctx, attrs[0].attr_name.loc)
        );
        assert!(matches!(blocks(&first).name, ShapeString::Attribute { .. }));
    }

    /// An unmarshalled block is one heap block however many fields point to
    /// it (intern.c shares it); a block with equal contents is another.
    #[test]
    fn decoded_locations_keep_block_identity_and_retain_address_keys() {
        let ctx = TypeContext::new(Arc::new(crate::context::IdGenerator::new()));
        let mut reader = SigReadContext::new(&ctx);
        let position = || {
            block(
                0,
                vec![
                    OcamlValue::String("source.res".into()),
                    OcamlValue::Int(1),
                    OcamlValue::Int(0),
                    OcamlValue::Int(2),
                ],
            )
        };
        let start = position();
        let end = position();
        let location = || block(0, vec![start.clone(), end.clone(), OcamlValue::Int(0)]);
        let a = location();
        let b = location();
        let first = reader.read_decl_loc(&a);
        assert_eq!(first, reader.read_decl_loc(&a));
        let distinct = reader.read_decl_loc(&b);
        assert_ne!(first, distinct);
        assert_eq!(ctx.resolve_loc(first), ctx.resolve_loc(distinct));
        assert_eq!(ctx.local_decl_loc_count(), 1);
        assert_eq!(
            reader.location_blocks.len(),
            4,
            "two locations share their two positions"
        );
        assert_ne!(reader.location_block(&start), reader.location_block(&end));
        let OcamlValue::Block(_, fields) = &a else {
            unreachable!()
        };
        let retained = Arc::downgrade(fields);
        drop(a);
        assert!(
            retained.upgrade().is_some(),
            "cached address remains allocated"
        );
        let mut other = SigReadContext::new(&ctx);
        assert_ne!(
            distinct,
            other.read_decl_loc(&b),
            "separate decoded scopes remain distinct"
        );
        drop(reader);
        assert!(
            retained.upgrade().is_none(),
            "reader releases retained allocation"
        );
    }

    #[test]
    fn decoded_dotted_paths_keep_blocks_prefixes_and_name_strings() {
        use crate::cmi::marshal_reader::MarshalReader;
        let mut marshal = MarshalReader::new();
        let name = marshal
            .read_value(&mut std::io::Cursor::new([0x21, b'x']))
            .unwrap();
        let equal = marshal
            .read_value(&mut std::io::Cursor::new([0x21, b'x']))
            .unwrap();
        let id = block(
            0,
            vec![OcamlValue::Int(1001), name.clone(), OcamlValue::Int(0)],
        );
        let prefix = block(0, vec![id.clone()]);
        let dot = |name: OcamlValue| block(1, vec![prefix.clone(), name, OcamlValue::Int(0)]);
        let raw_a = dot(name.clone());
        let raw_b = dot(name);
        let raw_c = dot(equal);
        let ctx = TypeContext::new(Arc::new(crate::context::IdGenerator::new()));
        let mut reader = SigReadContext::new(&ctx);
        let a = reader.read_path(&raw_a);
        let copy = reader.read_path(&raw_a);
        let b = reader.read_path(&raw_b);
        let c = reader.read_path(&raw_c);
        assert_eq!(a, copy);
        assert_eq!(a, b);
        assert_eq!(a, c);
        assert_eq!(
            a,
            Path::pdot_pos(Path::pident(reader.read_ident(&id)), "x", 0)
        );
    }



    #[test]
    fn decoded_identifiers_and_paths_keep_their_marshal_block_identity() {
        let ctx = TypeContext::new(Arc::new(crate::context::IdGenerator::new()));
        let mut reader = SigReadContext::new(&ctx);
        let ident = |stamp| {
            block(
                0,
                vec![
                    OcamlValue::Int(stamp),
                    OcamlValue::String("int".into()),
                    OcamlValue::Int(0),
                ],
            )
        };
        let int = ident(1);
        let int_again = ident(1);
        let first = reader.read_ident(&int);
        let shared = reader.read_ident(&int.clone());
        let other = reader.read_ident(&int_again);
        assert_eq!(first, other, "the same identifier");

        let unit = block(
            0,
            vec![block(
                0,
                vec![
                    OcamlValue::Int(0),
                    OcamlValue::String("Unit".into()),
                    OcamlValue::Int(1),
                ],
            )],
        );
        let pdot = |prefix: &OcamlValue| {
            block(
                1,
                vec![
                    prefix.clone(),
                    OcamlValue::String("t".into()),
                    OcamlValue::Int(0),
                ],
            )
        };
        let unit_t = pdot(&unit);
        let a = reader.read_shared_path(&unit_t);
        let b = reader.read_shared_path(&unit_t.clone());
        let c = reader.read_shared_path(&pdot(&unit));
        assert_eq!(first, shared);
        assert_eq!(a, b);
        assert_eq!(a, c);
        assert_eq!(a.name(), "Unit.t");
    }

    fn cmi_ident_pstr(name: &str) -> OcamlValue {
        block(
            0,
            vec![block(
                0,
                vec![block(0, vec![OcamlValue::String(name.into())])],
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
                    // Pconst_string of a `String_literal.Valid {source; semantic}`
                    vec![block(
                        2,
                        vec![block(
                            0,
                            vec![
                                OcamlValue::String(value.into()),
                                OcamlValue::String(value.into()),
                            ],
                        )],
                    )],
                )],
            )],
        )
    }

    #[test]
    fn reads_cmi_null_ident_payload_as_ident_not_string() {
        assert_eq!(
            read_attribute_payload(&cmi_ident_pstr("null"), &mut |_| {
                crate::types::DeclLoc::none()
            }),
            AttributePayload::Ident("null".to_string())
        );
    }

    #[test]
    fn reads_cmi_undefined_ident_payload_as_ident_not_string() {
        assert_eq!(
            read_attribute_payload(&cmi_ident_pstr("undefined"), &mut |_| {
                crate::types::DeclLoc::none()
            }),
            AttributePayload::Ident("undefined".to_string())
        );
    }

    #[test]
    fn keeps_cmi_string_literal_payload_distinct_from_identifier_payload() {
        assert_eq!(
            read_attribute_payload(&cmi_string_pstr("null"), &mut |_| {
                crate::types::DeclLoc::none()
            }),
            AttributePayload::Str("null".to_string())
        );
        assert_eq!(
            read_attribute_payload(&cmi_string_pstr("fulfilled"), &mut |_| {
                crate::types::DeclLoc::none()
            }),
            AttributePayload::Str("fulfilled".to_string())
        );
    }
}
