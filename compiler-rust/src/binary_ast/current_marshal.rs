//! Marshal implementation for the current parsetree format.
//!
//! This module provides marshaling for the current Rust AST types to match
//! OCaml's `output_value` format for the parsetree. This is used for binary
//! AST output (`-bs-ast`).
//!
//! The current parsetree differs from parsetree0 in several ways:
//! - Ptyp_arrow uses inline record {arg; ret; arity} where arg is {attrs; lbl; typ}
//! - Pexp_fun uses inline record with 6 fields
//! - Pexp_apply uses inline record with 4 fields
//! - record_element is polymorphic {lid; x; opt}

use super::marshal::{EmptyPayloadShareKind, MarshalWriter};
use super::serialize::Marshal;
use crate::parse_arena::LocIdx;
use crate::parser::ast::{
    Arity, ArgLabel, Attribute, Attributes, Case, ClosedFlag, Constant, CoreType, CoreTypeDesc,
    DirectionFlag, Expression, ExpressionDesc, ExpressionRecordField, ExtensionConstructor,
    ExtensionConstructorKind, IncludeDeclaration, IncludeDescription, LabelDeclaration,
    ModuleBinding, ModuleDeclaration, ModuleExpr, ModuleExprDesc, ModuleType,
    ModuleTypeDeclaration, ModuleTypeDesc, MutableFlag, ObjectField, OpenDescription,
    OverrideFlag, Pattern, PatternDesc, PatternRecordField, Payload, PrivateFlag, RecFlag,
    RowField, SignatureItem, SignatureItemDesc, StructureItem, StructureItemDesc, TypeArg,
    TypeDeclaration, TypeExtension, TypeKind, ValueBinding, ValueDescription, Variance,
    WithConstraint, ConstructorArguments, ConstructorDeclaration,
};

// ========== Attribute list sharing ==========

fn marshal_attribute_payload(
    payload: &Payload,
    w: &mut MarshalWriter,
    share_empty_pstr: Option<EmptyPayloadShareKind>,
) {
    if let Some(kind) = share_empty_pstr {
        if matches!(payload, Payload::PStr(items) if items.is_empty()) {
            w.write_pstr_empty_shared(kind);
            return;
        }
    }
    payload.marshal(w);
}

fn marshal_attribute_list(
    attrs: &[Attribute],
    w: &mut MarshalWriter,
    share_empty_pstr: Option<EmptyPayloadShareKind>,
) {
    if let Some((head, tail)) = attrs.split_first() {
        let (name, payload) = head;
        // List cons cell
        w.write_block_header(0, 2);
        // Attribute tuple
        w.write_block_header(0, 2);
        name.marshal(w);
        marshal_attribute_payload(payload, w, share_empty_pstr);
        marshal_attribute_list(tail, w, share_empty_pstr);
    } else {
        // []
        w.write_int(0);
    }
}

/// Marshal an attribute list, optionally sharing singleton `[(name, PStr [])]` tuples.
///
/// In OCaml, certain parser attributes (`template_literal_attr`, etc.) are module-level
/// `let` bindings that create a single physical tuple object. When the PPX preserves
/// these attributes (early-return cases like `Pexp_constant(Pconst_string(_, Some _))`),
/// the marshal sees the same physical pointer and writes SHARED references.
///
/// For expressions that go through OCaml's default mapper, `sub.attributes sub attrs`
/// creates NEW attribute tuples, breaking physical sharing. We match this by only
/// enabling sharing when `share_singleton` is true (for early-return expression types).
///
/// When sharing is enabled and attrs match `[(name, PStr [])]` where name uses
/// `Location.none` (LocIdx::default()), the attribute tuple is shared via
/// `singleton_attr_list_table`.
fn marshal_attributes(
    attrs: &Attributes,
    w: &mut MarshalWriter,
    share_singleton: bool,
    share_empty_pstr: Option<EmptyPayloadShareKind>,
) {
    let attrs_slice = attrs.as_slice();

    let payload_is_empty_str =
        |payload: &Payload| matches!(payload, Payload::PStr(items) if items.is_empty());

    // Share singleton attribute TUPLES: [(name, PStr [])] with Location.none
    //
    // In OCaml, module-level constants like `template_literal_attr`, `ternary_attr` etc.
    // are single physical tuples `(Location.mknoloc "res.template", Parsetree.PStr [])`.
    // When used as `~attrs:[template_literal_attr]`, a FRESH cons cell wraps the tuple,
    // but the TUPLE INSIDE is the same physical pointer across all uses.
    //
    // We share at the TUPLE level (not cons cell level):
    // - The cons cell is always written fresh (each [attr] creates a new cons cell)
    // - The tuple inside is shared when share_singleton=true and a matching entry exists
    if share_singleton {
        if let [(name, payload)] = attrs_slice {
            if payload_is_empty_str(payload)
                && name.loc == LocIdx::default()
            {
                let key = (name.txt, name.loc);

                // Write the cons cell (list with one element): Block(tag=0, size=2) [tuple, nil]
                // OCaml cons cells use tag=0. The cons cell is always fresh.
                w.write_block_header(0, 2);

                // Check if we've seen this attribute tuple before
                if let Some(&obj_idx) = w.singleton_attr_list_table_get(&key) {
                    let d = w.obj_counter() - obj_idx;
                    w.write_shared_ref(d);
                } else {
                    // Record the object index for the tuple
                    let obj_idx = w.obj_counter();

                    // Write the attribute tuple: Block(tag=0, size=2) [name, payload]
                    w.write_block_header(0, 2);
                    name.marshal(w);
                    marshal_attribute_payload(payload, w, share_empty_pstr);

                    w.singleton_attr_list_table_insert(key, obj_idx);
                }

                // Write nil (end of list)
                w.write_int(0);
                return;
            }
        }
    }

    // Default: marshal normally without sharing
    if share_empty_pstr.is_some() {
        marshal_attribute_list(attrs_slice, w, share_empty_pstr);
    } else {
        attrs_slice.marshal(w);
    }
}

// ========== Flag implementations ==========

impl Marshal for RecFlag {
    fn marshal(&self, w: &mut MarshalWriter) {
        w.write_int(match self {
            RecFlag::Nonrecursive => 0,
            RecFlag::Recursive => 1,
        });
    }
}

impl Marshal for DirectionFlag {
    fn marshal(&self, w: &mut MarshalWriter) {
        w.write_int(match self {
            DirectionFlag::Upto => 0,
            DirectionFlag::Downto => 1,
        });
    }
}

impl Marshal for PrivateFlag {
    fn marshal(&self, w: &mut MarshalWriter) {
        w.write_int(match self {
            PrivateFlag::Private => 0,
            PrivateFlag::Public => 1,
        });
    }
}

impl Marshal for MutableFlag {
    fn marshal(&self, w: &mut MarshalWriter) {
        w.write_int(match self {
            MutableFlag::Immutable => 0,
            MutableFlag::Mutable => 1,
        });
    }
}

impl Marshal for OverrideFlag {
    fn marshal(&self, w: &mut MarshalWriter) {
        w.write_int(match self {
            OverrideFlag::Override => 0,
            OverrideFlag::Fresh => 1,
        });
    }
}

impl Marshal for ClosedFlag {
    fn marshal(&self, w: &mut MarshalWriter) {
        w.write_int(match self {
            ClosedFlag::Closed => 0,
            ClosedFlag::Open => 1,
        });
    }
}

impl Marshal for Variance {
    fn marshal(&self, w: &mut MarshalWriter) {
        w.write_int(match self {
            Variance::Covariant => 0,
            Variance::Contravariant => 1,
            Variance::Invariant => 2,
        });
    }
}

// ========== ArgLabel (with location for Labelled/Optional) ==========

impl Marshal for ArgLabel {
    fn marshal(&self, w: &mut MarshalWriter) {
        // In current parsetree, arg_label uses Located<String> for Labelled/Optional
        // But in Rust AST we have just String. For now, output without location.
        // OCaml's Asttypes.arg_label:
        // - Nolabel: int 0
        // - Labelled of string loc: block(tag=0, size=1) containing the string loc
        // - Optional of string loc: block(tag=1, size=1) containing the string loc
        match self {
            ArgLabel::Nolabel => w.write_int(0),
            ArgLabel::Labelled(s) => {
                // Labelled has a string loc, which is a record {txt; loc}
                w.write_block_header(0, 1);
                // Register for sharing: in OCaml's %obj PPX, the same {txt; loc}
                // record is shared between Labelled args and Otag labels. Since
                // Labelled is serialized before Otag in the arrow type, it must
                // register so Otag can share it. This is safe because different
                // parameters always have different (StrIdx, LocIdx) keys.
                w.write_string_loc_shared(s.txt, s.loc, true);
            }
            ArgLabel::Optional(s) => {
                w.write_block_header(1, 1);
                w.write_string_loc_shared(s.txt, s.loc, true);
            }
        }
    }
}

// ========== Arity ==========

// Arity is now a type alias for ArityIdx (see parser/ast.rs).
// Marshal implementation uses write_arity_idx which:
// - Looks up the actual arity value in the arena
// - Shares arities with the same ArityIdx (matching OCaml's constant folding)
impl Marshal for Arity {
    fn marshal(&self, w: &mut MarshalWriter) {
        // Arity is ArityIdx - use the arena-based sharing method
        w.write_arity_idx(*self);
    }
}

// Note: Position, Location, Located<T>, and Longident implementations
// are in types.rs - don't duplicate them here.

// ========== Constant ==========

impl Marshal for Constant {
    fn marshal(&self, w: &mut MarshalWriter) {
        match self {
            Constant::Integer(s, suffix) => {
                w.write_block_header(0, 2);
                w.write_str(s);
                suffix.marshal(w);
            }
            Constant::Char(c) => {
                w.write_block_header(1, 1);
                w.write_int(*c as i64);
            }
            Constant::String(s, delim) => {
                w.write_block_header(2, 2);
                w.write_str(s);
                // Use content-based sharing for string delimiters like Some("js")
                w.write_option_string(delim);
            }
            Constant::Float(s, suffix) => {
                w.write_block_header(3, 2);
                w.write_str(s);
                suffix.marshal(w);
            }
        }
    }
}

// Note: Option<T>, Vec<T>, and tuple implementations are in serialize.rs - don't duplicate them here.

// ========== TypeArg (arg record in current parsetree) ==========

impl Marshal for TypeArg {
    fn marshal(&self, w: &mut MarshalWriter) {
        // arg = { attrs: attributes; lbl: arg_label; typ: core_type }
        w.write_block_header(0, 3);
        self.attrs.marshal(w);
        self.lbl.marshal(w);
        self.typ.marshal(w);
    }
}

// ========== Core Types ==========

impl Marshal for CoreType {
    fn marshal(&self, w: &mut MarshalWriter) {
        let share_empty_pstr = match &self.ptyp_desc {
            CoreTypeDesc::Ptyp_object(_, _) => Some(EmptyPayloadShareKind::ObjectTypeAttr),
            _ => None,
        };

        // Share Ptyp_var core_types with empty attributes and matching (name, loc).
        // In OCaml's from_labels (handle_obj), the same tyvar CoreType is physically
        // shared between Otag fields and Labelled args. The first write creates the
        // object, subsequent writes with the same (name, loc) emit shared references.
        if let CoreTypeDesc::Ptyp_var(name) = &self.ptyp_desc {
            if self.ptyp_attributes.is_empty() {
                let key = (name.clone(), self.ptyp_loc);
                if let Some(&obj_idx) = w.tyvar_core_type_table_get(&key) {
                    let d = w.obj_counter() - obj_idx;
                    w.write_shared_ref(d);
                    return;
                }
                // First occurrence: record the object index, then write normally
                let obj_idx = w.obj_counter();
                // core_type = { ptyp_desc; ptyp_loc; ptyp_attributes }
                w.write_block_header(0, 3);
                self.ptyp_desc.marshal(w);
                self.ptyp_loc.marshal(w);
                marshal_attributes(&self.ptyp_attributes, w, false, share_empty_pstr);
                w.tyvar_core_type_table_insert(key, obj_idx);
                return;
            }
        }

        // core_type = { ptyp_desc; ptyp_loc; ptyp_attributes }
        w.write_block_header(0, 3);
        self.ptyp_desc.marshal(w);
        self.ptyp_loc.marshal(w);
        marshal_attributes(&self.ptyp_attributes, w, false, share_empty_pstr);
    }
}

impl Marshal for CoreTypeDesc {
    fn marshal(&self, w: &mut MarshalWriter) {
        // core_type_desc variants (counting non-constant constructors only):
        // Ptyp_any = int 0 (constant)
        // Ptyp_var = tag 0
        // Ptyp_arrow = tag 1
        // Ptyp_tuple = tag 2
        // Ptyp_constr = tag 3
        // Ptyp_object = tag 4
        // Ptyp_alias = tag 5
        // Ptyp_variant = tag 6
        // Ptyp_poly = tag 7
        // Ptyp_package = tag 8
        // Ptyp_extension = tag 9
        match self {
            CoreTypeDesc::Ptyp_any => w.write_int(0),
            CoreTypeDesc::Ptyp_var(s) => {
                w.write_block_header(0, 1);
                w.write_str(s);
            }
            CoreTypeDesc::Ptyp_arrow { arg, ret, arity } => {
                // Ptyp_arrow of { arg: arg; ret: core_type; arity: arity }
                // Inline record is encoded as block with 3 fields
                w.write_block_header(1, 3);
                arg.marshal(w);
                ret.marshal(w);
                arity.marshal(w);
            }
            CoreTypeDesc::Ptyp_tuple(types) => {
                w.write_block_header(2, 1);
                types.marshal(w);
            }
            CoreTypeDesc::Ptyp_constr(lid, types) => {
                w.write_block_header(3, 2);
                lid.marshal(w);
                types.marshal(w);
            }
            CoreTypeDesc::Ptyp_object(fields, flag) => {
                w.write_block_header(4, 2);
                fields.marshal(w);
                flag.marshal(w);
            }
            CoreTypeDesc::Ptyp_alias(ty, s) => {
                w.write_block_header(5, 2);
                ty.marshal(w);
                w.write_str(s);
            }
            CoreTypeDesc::Ptyp_variant(rows, flag, labels) => {
                w.write_block_header(6, 3);
                rows.marshal(w);
                flag.marshal(w);
                labels.marshal(w);
            }
            CoreTypeDesc::Ptyp_poly(vars, ty) => {
                w.write_block_header(7, 2);
                vars.marshal(w);
                ty.marshal(w);
            }
            CoreTypeDesc::Ptyp_package(pkg) => {
                w.write_block_header(8, 1);
                pkg.marshal(w);
            }
            CoreTypeDesc::Ptyp_extension(ext) => {
                w.write_block_header(9, 1);
                ext.marshal(w);
            }
        }
    }
}

impl Marshal for RowField {
    fn marshal(&self, w: &mut MarshalWriter) {
        match self {
            RowField::Rtag(label, attrs, b, types) => {
                w.write_block_header(0, 4);
                label.marshal(w);
                attrs.marshal(w);
                w.write_int(if *b { 1 } else { 0 });
                types.marshal(w);
            }
            RowField::Rinherit(ty) => {
                w.write_block_header(1, 1);
                ty.marshal(w);
            }
        }
    }
}

impl Marshal for ObjectField {
    fn marshal(&self, w: &mut MarshalWriter) {
        match self {
            ObjectField::Otag(label, attrs, ty) => {
                w.write_block_header(0, 3);
                // Write the label's {txt; loc} record with sharing support.
                // In PPX-generated code (e.g., %obj), the same {txt; loc} record
                // may be shared with an ArgLabel::Labelled label.
                w.write_string_loc_shared(label.txt, label.loc, true);
                marshal_attributes(
                    attrs,
                    w,
                    false,
                    Some(EmptyPayloadShareKind::ObjectFieldAttr),
                );
                ty.marshal(w);
            }
            ObjectField::Oinherit(ty) => {
                w.write_block_header(1, 1);
                ty.marshal(w);
            }
        }
    }
}

// ========== Patterns ==========

impl Marshal for Pattern {
    fn marshal(&self, w: &mut MarshalWriter) {
        w.write_block_header(0, 3);
        self.ppat_desc.marshal(w);
        self.ppat_loc.marshal(w);
        marshal_attributes(&self.ppat_attributes, w, false, None);
    }
}

impl Marshal for PatternDesc {
    fn marshal(&self, w: &mut MarshalWriter) {
        // Pattern_desc variants:
        // Ppat_any = int 0 (constant)
        // Ppat_var = tag 0
        // Ppat_alias = tag 1
        // Ppat_constant = tag 2
        // Ppat_interval = tag 3
        // Ppat_tuple = tag 4
        // Ppat_construct = tag 5
        // Ppat_variant = tag 6
        // Ppat_record = tag 7
        // Ppat_array = tag 8
        // Ppat_or = tag 9
        // Ppat_constraint = tag 10
        // Ppat_type = tag 11
        // Ppat_unpack = tag 12
        // Ppat_exception = tag 13
        // Ppat_extension = tag 14
        // Ppat_open = tag 15
        match self {
            PatternDesc::Ppat_any => w.write_int(0),
            PatternDesc::Ppat_var(s) => {
                w.write_block_header(0, 1);
                s.marshal(w);
            }
            PatternDesc::Ppat_alias(p, s) => {
                w.write_block_header(1, 2);
                p.marshal(w);
                s.marshal(w);
            }
            PatternDesc::Ppat_constant(c) => {
                w.write_block_header(2, 1);
                c.marshal(w);
            }
            PatternDesc::Ppat_interval(c1, c2) => {
                w.write_block_header(3, 2);
                c1.marshal(w);
                c2.marshal(w);
            }
            PatternDesc::Ppat_tuple(pats) => {
                w.write_block_header(4, 1);
                pats.marshal(w);
            }
            PatternDesc::Ppat_construct(lid, pat) => {
                w.write_block_header(5, 2);
                lid.marshal(w);
                pat.marshal(w);
            }
            PatternDesc::Ppat_variant(label, pat) => {
                w.write_block_header(6, 2);
                w.write_str(label);
                pat.marshal(w);
            }
            PatternDesc::Ppat_record(fields, flag) => {
                w.write_block_header(7, 2);
                fields.marshal(w);
                flag.marshal(w);
            }
            PatternDesc::Ppat_array(pats) => {
                w.write_block_header(8, 1);
                pats.marshal(w);
            }
            PatternDesc::Ppat_or(p1, p2) => {
                w.write_block_header(9, 2);
                p1.marshal(w);
                p2.marshal(w);
            }
            PatternDesc::Ppat_constraint(p, t) => {
                w.write_block_header(10, 2);
                p.marshal(w);
                t.marshal(w);
            }
            PatternDesc::Ppat_type(lid) => {
                w.write_block_header(11, 1);
                lid.marshal(w);
            }
            PatternDesc::Ppat_unpack(s) => {
                w.write_block_header(12, 1);
                s.marshal(w);
            }
            PatternDesc::Ppat_exception(p) => {
                w.write_block_header(13, 1);
                p.marshal(w);
            }
            PatternDesc::Ppat_extension(ext) => {
                w.write_block_header(14, 1);
                ext.marshal(w);
            }
            PatternDesc::Ppat_open(lid, p) => {
                w.write_block_header(15, 2);
                lid.marshal(w);
                p.marshal(w);
            }
        }
    }
}

// ========== Record Field Types ==========

impl Marshal for PatternRecordField {
    fn marshal(&self, w: &mut MarshalWriter) {
        // record_element = { lid: Longident.t loc; x: 'a; opt: bool }
        w.write_block_header(0, 3);
        self.lid.marshal(w);
        self.pat.marshal(w);
        w.write_int(if self.opt { 1 } else { 0 });
    }
}

impl Marshal for ExpressionRecordField {
    fn marshal(&self, w: &mut MarshalWriter) {
        // record_element = { lid: Longident.t loc; x: 'a; opt: bool }
        w.write_block_header(0, 3);
        self.lid.marshal(w);
        self.expr.marshal(w);
        w.write_int(if self.opt { 1 } else { 0 });
    }
}

// ========== Expressions ==========

impl Marshal for Expression {
    fn marshal(&self, w: &mut MarshalWriter) {
        w.write_block_header(0, 3);
        self.pexp_desc.marshal(w);
        self.pexp_loc.marshal(w);

        // In OCaml's PPX, certain expression types return early from expr_mapper
        // without going through the default mapper's attribute remapping. These
        // expressions preserve their original attribute tuples, enabling marshal
        // sharing of singleton `(mknoloc name, PStr [])` module-level constants.
        //
        // Early-return expression types (preserve attribute tuple pointers):
        // - Pexp_constant(Pconst_string(_, Some _)): template literals
        // - Pexp_constant(Pconst_integer(_, Some _)): int suffix stripping
        // - Pexp_extension: unknown extensions return unchanged
        // - Pexp_newtype: preserves attrs in record-with update
        //
        // Note: Pexp_constant(String(_, None)) and Pexp_letmodule are NOT included.
        // While PPX-created instances preserve attrs, user code instances go through
        // the default mapper which creates fresh tuples.
        let share_attrs = matches!(
            &self.pexp_desc,
            ExpressionDesc::Pexp_constant(Constant::String(_, Some(_)))
                | ExpressionDesc::Pexp_constant(Constant::Integer(_, Some(_)))
                | ExpressionDesc::Pexp_extension(_)
                | ExpressionDesc::Pexp_newtype(_, _)
        );
        marshal_attributes(&self.pexp_attributes, w, share_attrs, None);
    }
}

impl Marshal for ExpressionDesc {
    fn marshal(&self, w: &mut MarshalWriter) {
        // Expression_desc variants - count only non-constant constructors:
        // Pexp_ident = tag 0
        // Pexp_constant = tag 1
        // Pexp_let = tag 2
        // Pexp_fun = tag 3
        // Pexp_apply = tag 4
        // Pexp_match = tag 5
        // Pexp_try = tag 6
        // Pexp_tuple = tag 7
        // Pexp_construct = tag 8
        // Pexp_variant = tag 9
        // Pexp_record = tag 10
        // Pexp_field = tag 11
        // Pexp_setfield = tag 12
        // Pexp_array = tag 13
        // Pexp_ifthenelse = tag 14
        // Pexp_sequence = tag 15
        // Pexp_while = tag 16
        // Pexp_for = tag 17
        // Pexp_constraint = tag 18
        // Pexp_coerce = tag 19
        // Pexp_send = tag 20
        // Pexp_letmodule = tag 21
        // Pexp_letexception = tag 22
        // Pexp_assert = tag 23
        // Pexp_newtype = tag 24
        // Pexp_pack = tag 25
        // Pexp_open = tag 26
        // Pexp_extension = tag 27
        // Pexp_await = tag 28
        // Pexp_jsx_element = tag 29
        match self {
            ExpressionDesc::Pexp_ident(lid) => {
                w.write_block_header(0, 1);
                lid.marshal(w);
            }
            ExpressionDesc::Pexp_constant(c) => {
                w.write_block_header(1, 1);
                c.marshal(w);
            }
            ExpressionDesc::Pexp_let(flag, bindings, body) => {
                w.write_block_header(2, 3);
                flag.marshal(w);
                bindings.marshal(w);
                body.marshal(w);
            }
            ExpressionDesc::Pexp_fun {
                arg_label,
                default,
                lhs,
                rhs,
                arity,
                is_async,
            } => {
                // Pexp_fun of { arg_label; default; lhs; rhs; arity; async }
                // Inline record with 6 fields
                w.write_block_header(3, 6);
                arg_label.marshal(w);
                default.marshal(w);
                lhs.marshal(w);
                rhs.marshal(w);
                arity.marshal(w);
                w.write_int(if *is_async { 1 } else { 0 });
            }
            ExpressionDesc::Pexp_apply {
                funct,
                args,
                partial,
                transformed_jsx,
            } => {
                // Pexp_apply of { funct; args; partial; transformed_jsx }
                // Inline record with 4 fields
                w.write_block_header(4, 4);
                funct.marshal(w);
                args.marshal(w);
                w.write_int(if *partial { 1 } else { 0 });
                w.write_int(if *transformed_jsx { 1 } else { 0 });
            }
            ExpressionDesc::Pexp_match(e, cases) => {
                w.write_block_header(5, 2);
                e.marshal(w);
                cases.marshal(w);
            }
            ExpressionDesc::Pexp_try(e, cases) => {
                w.write_block_header(6, 2);
                e.marshal(w);
                cases.marshal(w);
            }
            ExpressionDesc::Pexp_tuple(exprs) => {
                w.write_block_header(7, 1);
                exprs.marshal(w);
            }
            ExpressionDesc::Pexp_construct(lid, expr) => {
                w.write_block_header(8, 2);
                lid.marshal(w);
                expr.marshal(w);
            }
            ExpressionDesc::Pexp_variant(label, expr) => {
                w.write_block_header(9, 2);
                w.write_str(label);
                expr.marshal(w);
            }
            ExpressionDesc::Pexp_record(fields, spread) => {
                w.write_block_header(10, 2);
                fields.marshal(w);
                spread.marshal(w);
            }
            ExpressionDesc::Pexp_field(e, lid) => {
                w.write_block_header(11, 2);
                e.marshal(w);
                lid.marshal(w);
            }
            ExpressionDesc::Pexp_setfield(e1, lid, e2) => {
                w.write_block_header(12, 3);
                e1.marshal(w);
                lid.marshal(w);
                e2.marshal(w);
            }
            ExpressionDesc::Pexp_array(exprs) => {
                w.write_block_header(13, 1);
                exprs.marshal(w);
            }
            ExpressionDesc::Pexp_ifthenelse(e1, e2, e3) => {
                w.write_block_header(14, 3);
                e1.marshal(w);
                e2.marshal(w);
                e3.marshal(w);
            }
            ExpressionDesc::Pexp_sequence(e1, e2) => {
                w.write_block_header(15, 2);
                e1.marshal(w);
                e2.marshal(w);
            }
            ExpressionDesc::Pexp_while(e1, e2) => {
                w.write_block_header(16, 2);
                e1.marshal(w);
                e2.marshal(w);
            }
            ExpressionDesc::Pexp_for(pat, e1, e2, dir, e3) => {
                w.write_block_header(17, 5);
                pat.marshal(w);
                e1.marshal(w);
                e2.marshal(w);
                dir.marshal(w);
                e3.marshal(w);
            }
            ExpressionDesc::Pexp_constraint(e, t) => {
                w.write_block_header(18, 2);
                e.marshal(w);
                t.marshal(w);
            }
            ExpressionDesc::Pexp_coerce(e, _middle, t) => {
                // Pexp_coerce of expression * unit * core_type
                // The middle field in Rust is Option<CoreType> but OCaml uses unit
                w.write_block_header(19, 3);
                e.marshal(w);
                w.write_int(0); // unit = ()
                t.marshal(w);
            }
            ExpressionDesc::Pexp_send(e, label) => {
                w.write_block_header(20, 2);
                e.marshal(w);
                label.marshal(w);
            }
            ExpressionDesc::Pexp_letmodule(name, me, body) => {
                w.write_block_header(21, 3);
                name.marshal(w);
                me.marshal(w);
                body.marshal(w);
            }
            ExpressionDesc::Pexp_letexception(ec, body) => {
                w.write_block_header(22, 2);
                ec.marshal(w);
                body.marshal(w);
            }
            ExpressionDesc::Pexp_assert(e) => {
                w.write_block_header(23, 1);
                e.marshal(w);
            }
            ExpressionDesc::Pexp_newtype(name, e) => {
                w.write_block_header(24, 2);
                name.marshal(w);
                e.marshal(w);
            }
            ExpressionDesc::Pexp_pack(me) => {
                w.write_block_header(25, 1);
                me.marshal(w);
            }
            ExpressionDesc::Pexp_open(flag, lid, e) => {
                w.write_block_header(26, 3);
                flag.marshal(w);
                lid.marshal(w);
                e.marshal(w);
            }
            ExpressionDesc::Pexp_extension(ext) => {
                w.write_block_header(27, 1);
                ext.marshal(w);
            }
            ExpressionDesc::Pexp_await(e) => {
                w.write_block_header(28, 1);
                e.marshal(w);
            }
            ExpressionDesc::Pexp_jsx_element(jsx) => {
                w.write_block_header(29, 1);
                jsx.marshal(w);
            }
        }
    }
}

// ========== Case ==========

impl Marshal for Case {
    fn marshal(&self, w: &mut MarshalWriter) {
        // case = { pc_bar; pc_lhs; pc_guard; pc_rhs }
        w.write_block_header(0, 4);
        self.pc_bar.marshal(w);
        self.pc_lhs.marshal(w);
        self.pc_guard.marshal(w);
        self.pc_rhs.marshal(w);
    }
}

// ========== Value Binding ==========

impl Marshal for ValueBinding {
    fn marshal(&self, w: &mut MarshalWriter) {
        // value_binding = { pvb_pat; pvb_expr; pvb_attributes; pvb_loc }
        w.write_block_header(0, 4);
        self.pvb_pat.marshal(w);
        self.pvb_expr.marshal(w);
        marshal_attributes(&self.pvb_attributes, w, false, None);
        self.pvb_loc.marshal(w);
    }
}

// ========== Payload ==========

impl Marshal for Payload {
    fn marshal(&self, w: &mut MarshalWriter) {
        match self {
            Payload::PStr(structure) => {
                w.write_block_header(0, 1);
                structure.marshal(w);
            }
            Payload::PSig(signature) => {
                w.write_block_header(1, 1);
                signature.marshal(w);
            }
            Payload::PTyp(ty) => {
                w.write_block_header(2, 1);
                ty.marshal(w);
            }
            Payload::PPat(pat, guard) => {
                w.write_block_header(3, 2);
                pat.marshal(w);
                guard.marshal(w);
            }
        }
    }
}

// ========== Module Types ==========

impl Marshal for ModuleType {
    fn marshal(&self, w: &mut MarshalWriter) {
        w.write_block_header(0, 3);
        self.pmty_desc.marshal(w);
        self.pmty_loc.marshal(w);
        marshal_attributes(&self.pmty_attributes, w, false, None);
    }
}

impl Marshal for ModuleTypeDesc {
    fn marshal(&self, w: &mut MarshalWriter) {
        match self {
            ModuleTypeDesc::Pmty_ident(lid) => {
                w.write_block_header(0, 1);
                lid.marshal(w);
            }
            ModuleTypeDesc::Pmty_signature(sig) => {
                w.write_block_header(1, 1);
                sig.marshal(w);
            }
            ModuleTypeDesc::Pmty_functor(name, mt1, mt2) => {
                w.write_block_header(2, 3);
                name.marshal(w);
                mt1.marshal(w);
                mt2.marshal(w);
            }
            ModuleTypeDesc::Pmty_with(mt, constraints) => {
                w.write_block_header(3, 2);
                mt.marshal(w);
                constraints.marshal(w);
            }
            ModuleTypeDesc::Pmty_typeof(me) => {
                w.write_block_header(4, 1);
                me.marshal(w);
            }
            ModuleTypeDesc::Pmty_extension(ext) => {
                w.write_block_header(5, 1);
                ext.marshal(w);
            }
            ModuleTypeDesc::Pmty_alias(lid) => {
                w.write_block_header(6, 1);
                lid.marshal(w);
            }
        }
    }
}

impl Marshal for WithConstraint {
    fn marshal(&self, w: &mut MarshalWriter) {
        match self {
            WithConstraint::Pwith_type(lid, td) => {
                w.write_block_header(0, 2);
                lid.marshal(w);
                td.marshal(w);
            }
            WithConstraint::Pwith_module(lid1, lid2) => {
                w.write_block_header(1, 2);
                lid1.marshal(w);
                lid2.marshal(w);
            }
            WithConstraint::Pwith_typesubst(lid, td) => {
                w.write_block_header(2, 2);
                lid.marshal(w);
                td.marshal(w);
            }
            WithConstraint::Pwith_modsubst(lid1, lid2) => {
                w.write_block_header(3, 2);
                lid1.marshal(w);
                lid2.marshal(w);
            }
        }
    }
}

// ========== Module Expressions ==========

impl Marshal for ModuleExpr {
    fn marshal(&self, w: &mut MarshalWriter) {
        w.write_block_header(0, 3);
        self.pmod_desc.marshal(w);
        self.pmod_loc.marshal(w);
        marshal_attributes(&self.pmod_attributes, w, false, None);
    }
}

impl Marshal for ModuleExprDesc {
    fn marshal(&self, w: &mut MarshalWriter) {
        match self {
            ModuleExprDesc::Pmod_ident(lid) => {
                w.write_block_header(0, 1);
                lid.marshal(w);
            }
            ModuleExprDesc::Pmod_structure(str) => {
                w.write_block_header(1, 1);
                str.marshal(w);
            }
            ModuleExprDesc::Pmod_functor(name, mt, me) => {
                w.write_block_header(2, 3);
                name.marshal(w);
                mt.marshal(w);
                me.marshal(w);
            }
            ModuleExprDesc::Pmod_apply(me1, me2) => {
                w.write_block_header(3, 2);
                me1.marshal(w);
                me2.marshal(w);
            }
            ModuleExprDesc::Pmod_constraint(me, mt) => {
                w.write_block_header(4, 2);
                me.marshal(w);
                mt.marshal(w);
            }
            ModuleExprDesc::Pmod_unpack(e) => {
                w.write_block_header(5, 1);
                e.marshal(w);
            }
            ModuleExprDesc::Pmod_extension(ext) => {
                w.write_block_header(6, 1);
                ext.marshal(w);
            }
        }
    }
}

// ========== Type Declarations ==========

impl Marshal for TypeDeclaration {
    fn marshal(&self, w: &mut MarshalWriter) {
        // type_declaration has 8 fields
        w.write_block_header(0, 8);
        self.ptype_name.marshal(w);
        self.ptype_params.marshal(w);
        self.ptype_cstrs.marshal(w);
        self.ptype_kind.marshal(w);
        self.ptype_private.marshal(w);
        self.ptype_manifest.marshal(w);
        marshal_attributes(&self.ptype_attributes, w, false, None);
        self.ptype_loc.marshal(w);
    }
}

impl Marshal for TypeKind {
    fn marshal(&self, w: &mut MarshalWriter) {
        match self {
            TypeKind::Ptype_abstract => w.write_int(0),
            TypeKind::Ptype_variant(ctors) => {
                w.write_block_header(0, 1);
                ctors.marshal(w);
            }
            TypeKind::Ptype_record(labels) => {
                w.write_block_header(1, 1);
                labels.marshal(w);
            }
            TypeKind::Ptype_open => w.write_int(1),
        }
    }
}

impl Marshal for ConstructorDeclaration {
    fn marshal(&self, w: &mut MarshalWriter) {
        w.write_block_header(0, 5);
        self.pcd_name.marshal(w);
        self.pcd_args.marshal(w);
        self.pcd_res.marshal(w);
        self.pcd_loc.marshal(w);
        marshal_attributes(&self.pcd_attributes, w, false, None);
    }
}

impl Marshal for ConstructorArguments {
    fn marshal(&self, w: &mut MarshalWriter) {
        match self {
            ConstructorArguments::Pcstr_tuple(types) => {
                w.write_block_header(0, 1);
                types.marshal(w);
            }
            ConstructorArguments::Pcstr_record(labels) => {
                w.write_block_header(1, 1);
                labels.marshal(w);
            }
        }
    }
}

impl Marshal for LabelDeclaration {
    fn marshal(&self, w: &mut MarshalWriter) {
        // OCaml field order: pld_name, pld_mutable, pld_optional, pld_type, pld_loc, pld_attributes
        w.write_block_header(0, 6);
        self.pld_name.marshal(w);
        self.pld_mutable.marshal(w);
        w.write_int(if self.pld_optional { 1 } else { 0 });
        self.pld_type.marshal(w);
        self.pld_loc.marshal(w);
        marshal_attributes(&self.pld_attributes, w, false, None);
    }
}

// ========== Type Extension ==========

impl Marshal for TypeExtension {
    fn marshal(&self, w: &mut MarshalWriter) {
        w.write_block_header(0, 5);
        self.ptyext_path.marshal(w);
        self.ptyext_params.marshal(w);
        self.ptyext_constructors.marshal(w);
        self.ptyext_private.marshal(w);
        marshal_attributes(&self.ptyext_attributes, w, false, None);
    }
}

impl Marshal for ExtensionConstructor {
    fn marshal(&self, w: &mut MarshalWriter) {
        w.write_block_header(0, 4);
        self.pext_name.marshal(w);
        self.pext_kind.marshal(w);
        self.pext_loc.marshal(w);
        marshal_attributes(&self.pext_attributes, w, false, None);
    }
}

impl Marshal for ExtensionConstructorKind {
    fn marshal(&self, w: &mut MarshalWriter) {
        match self {
            ExtensionConstructorKind::Pext_decl(args, ret) => {
                w.write_block_header(0, 2);
                args.marshal(w);
                ret.marshal(w);
            }
            ExtensionConstructorKind::Pext_rebind(lid) => {
                w.write_block_header(1, 1);
                lid.marshal(w);
            }
        }
    }
}

// ========== Value Description ==========

impl Marshal for ValueDescription {
    fn marshal(&self, w: &mut MarshalWriter) {
        w.write_block_header(0, 5);
        self.pval_name.marshal(w);
        self.pval_type.marshal(w);
        // pval_prim contains raw binary data (FFI encoding blobs) that must be
        // written as raw bytes, not Latin-1 converted. Use write_string directly.
        marshal_prim_list(&self.pval_prim, w);
        marshal_attributes(&self.pval_attributes, w, false, None);
        self.pval_loc.marshal(w);
    }
}

/// Write a list of pval_prim strings, converting from Latin-1 encoding back to raw bytes.
/// FFI binary data is stored using Latin-1 encoding (each byte 0-255 becomes Unicode U+0000-U+00FF),
/// so we need to convert back using chars().map(|c| c as u8) to get the original bytes.
fn marshal_prim_list(prims: &[String], w: &mut MarshalWriter) {
    if prims.is_empty() {
        w.write_int(0);
    } else {
        for (i, prim) in prims.iter().enumerate() {
            w.write_block_header(0, 2);
            // Convert Latin-1 encoded string back to raw bytes
            let bytes: Vec<u8> = prim.chars().map(|c| c as u8).collect();
            w.write_string(&bytes);
            if i == prims.len() - 1 {
                w.write_int(0);
            }
        }
    }
}

// ========== Module declarations ==========

impl Marshal for ModuleDeclaration {
    fn marshal(&self, w: &mut MarshalWriter) {
        w.write_block_header(0, 4);
        self.pmd_name.marshal(w);
        self.pmd_type.marshal(w);
        marshal_attributes(&self.pmd_attributes, w, false, None);
        self.pmd_loc.marshal(w);
    }
}

impl Marshal for ModuleTypeDeclaration {
    fn marshal(&self, w: &mut MarshalWriter) {
        w.write_block_header(0, 4);
        self.pmtd_name.marshal(w);
        self.pmtd_type.marshal(w);
        marshal_attributes(&self.pmtd_attributes, w, false, None);
        self.pmtd_loc.marshal(w);
    }
}

impl Marshal for ModuleBinding {
    fn marshal(&self, w: &mut MarshalWriter) {
        w.write_block_header(0, 4);
        self.pmb_name.marshal(w);
        self.pmb_expr.marshal(w);
        marshal_attributes(&self.pmb_attributes, w, false, None);
        self.pmb_loc.marshal(w);
    }
}

impl Marshal for OpenDescription {
    fn marshal(&self, w: &mut MarshalWriter) {
        w.write_block_header(0, 4);
        self.popen_lid.marshal(w);
        self.popen_override.marshal(w);
        self.popen_loc.marshal(w);
        marshal_attributes(&self.popen_attributes, w, false, None);
    }
}

impl Marshal for IncludeDescription {
    fn marshal(&self, w: &mut MarshalWriter) {
        w.write_block_header(0, 3);
        self.pincl_mod.marshal(w);
        self.pincl_loc.marshal(w);
        marshal_attributes(&self.pincl_attributes, w, false, None);
    }
}

impl Marshal for IncludeDeclaration {
    fn marshal(&self, w: &mut MarshalWriter) {
        w.write_block_header(0, 3);
        self.pincl_mod.marshal(w);
        self.pincl_loc.marshal(w);
        marshal_attributes(&self.pincl_attributes, w, false, None);
    }
}

// ========== Structure ==========

impl Marshal for StructureItem {
    fn marshal(&self, w: &mut MarshalWriter) {
        w.write_block_header(0, 2);
        self.pstr_desc.marshal(w);
        self.pstr_loc.marshal(w);
    }
}

impl Marshal for StructureItemDesc {
    fn marshal(&self, w: &mut MarshalWriter) {
        match self {
            StructureItemDesc::Pstr_eval(e, attrs) => {
                w.write_block_header(0, 2);
                e.marshal(w);
                attrs.marshal(w);
            }
            StructureItemDesc::Pstr_value(flag, bindings) => {
                w.write_block_header(1, 2);
                flag.marshal(w);
                bindings.marshal(w);
            }
            StructureItemDesc::Pstr_primitive(vd) => {
                w.write_block_header(2, 1);
                vd.marshal(w);
            }
            StructureItemDesc::Pstr_type(flag, decls) => {
                w.write_block_header(3, 2);
                flag.marshal(w);
                decls.marshal(w);
            }
            StructureItemDesc::Pstr_typext(te) => {
                w.write_block_header(4, 1);
                te.marshal(w);
            }
            StructureItemDesc::Pstr_exception(ec) => {
                w.write_block_header(5, 1);
                ec.marshal(w);
            }
            StructureItemDesc::Pstr_module(mb) => {
                w.write_block_header(6, 1);
                mb.marshal(w);
            }
            StructureItemDesc::Pstr_recmodule(mbs) => {
                w.write_block_header(7, 1);
                mbs.marshal(w);
            }
            StructureItemDesc::Pstr_modtype(mtd) => {
                w.write_block_header(8, 1);
                mtd.marshal(w);
            }
            StructureItemDesc::Pstr_open(od) => {
                w.write_block_header(9, 1);
                od.marshal(w);
            }
            StructureItemDesc::Pstr_include(id) => {
                w.write_block_header(10, 1);
                id.marshal(w);
            }
            StructureItemDesc::Pstr_attribute(attr) => {
                w.write_block_header(11, 1);
                attr.marshal(w);
            }
            StructureItemDesc::Pstr_extension(ext, attrs) => {
                w.write_block_header(12, 2);
                ext.marshal(w);
                attrs.marshal(w);
            }
        }
    }
}

// ========== Signature ==========

impl Marshal for SignatureItem {
    fn marshal(&self, w: &mut MarshalWriter) {
        w.write_block_header(0, 2);
        self.psig_desc.marshal(w);
        self.psig_loc.marshal(w);
    }
}

impl Marshal for SignatureItemDesc {
    fn marshal(&self, w: &mut MarshalWriter) {
        match self {
            SignatureItemDesc::Psig_value(vd) => {
                w.write_block_header(0, 1);
                vd.marshal(w);
            }
            SignatureItemDesc::Psig_type(flag, decls) => {
                w.write_block_header(1, 2);
                flag.marshal(w);
                decls.marshal(w);
            }
            SignatureItemDesc::Psig_typext(te) => {
                w.write_block_header(2, 1);
                te.marshal(w);
            }
            SignatureItemDesc::Psig_exception(ec) => {
                w.write_block_header(3, 1);
                ec.marshal(w);
            }
            SignatureItemDesc::Psig_module(md) => {
                w.write_block_header(4, 1);
                md.marshal(w);
            }
            SignatureItemDesc::Psig_recmodule(mds) => {
                w.write_block_header(5, 1);
                mds.marshal(w);
            }
            SignatureItemDesc::Psig_modtype(mtd) => {
                w.write_block_header(6, 1);
                mtd.marshal(w);
            }
            SignatureItemDesc::Psig_open(od) => {
                w.write_block_header(7, 1);
                od.marshal(w);
            }
            SignatureItemDesc::Psig_include(id) => {
                w.write_block_header(8, 1);
                id.marshal(w);
            }
            SignatureItemDesc::Psig_attribute(attr) => {
                w.write_block_header(9, 1);
                attr.marshal(w);
            }
            SignatureItemDesc::Psig_extension(ext, attrs) => {
                w.write_block_header(10, 2);
                ext.marshal(w);
                attrs.marshal(w);
            }
        }
    }
}

// ========== JSX types ==========

use crate::parser::ast::{JsxClosingTag, JsxContainerElement, JsxElement, JsxFragment, JsxProp, JsxTagName, JsxUnaryElement};

impl Marshal for JsxElement {
    fn marshal(&self, w: &mut MarshalWriter) {
        match self {
            JsxElement::Fragment(frag) => {
                w.write_block_header(0, 1);
                frag.marshal(w);
            }
            JsxElement::Unary(elem) => {
                w.write_block_header(1, 1);
                elem.marshal(w);
            }
            JsxElement::Container(elem) => {
                w.write_block_header(2, 1);
                elem.marshal(w);
            }
        }
    }
}

impl Marshal for JsxFragment {
    fn marshal(&self, w: &mut MarshalWriter) {
        // jsx_fragment = { jsx_fragment_opening; jsx_fragment_children; jsx_fragment_closing }
        w.write_block_header(0, 3);
        self.opening.marshal(w);
        self.children.marshal(w);
        self.closing.marshal(w);
    }
}

impl Marshal for JsxUnaryElement {
    fn marshal(&self, w: &mut MarshalWriter) {
        // jsx_unary_element = { jsx_unary_element_tag_name; jsx_unary_element_props }
        w.write_block_header(0, 2);
        self.tag_name.marshal(w);
        self.props.marshal(w);
    }
}

impl Marshal for JsxContainerElement {
    fn marshal(&self, w: &mut MarshalWriter) {
        // jsx_container_element = { tag_name_start; opening_tag_end; props; children; closing_tag }
        w.write_block_header(0, 5);
        self.tag_name_start.marshal(w);
        self.opening_end.marshal(w);
        self.props.marshal(w);
        self.children.marshal(w);
        self.closing_tag.marshal(w);
    }
}

impl Marshal for JsxClosingTag {
    fn marshal(&self, w: &mut MarshalWriter) {
        // jsx_closing_container_tag = { start; name; end }
        w.write_block_header(0, 3);
        self.start.marshal(w);
        self.name.marshal(w);
        self.end.marshal(w);
    }
}

impl Marshal for JsxTagName {
    fn marshal(&self, w: &mut MarshalWriter) {
        match self {
            JsxTagName::Lower(s) => {
                w.write_block_header(0, 1);
                w.write_str(s);
            }
            JsxTagName::QualifiedLower { path, name } => {
                w.write_block_header(1, 2);
                path.marshal(w);
                w.write_str(name);
            }
            JsxTagName::Upper(lid) => {
                w.write_block_header(2, 1);
                lid.marshal(w);
            }
            JsxTagName::Invalid(s) => {
                w.write_block_header(3, 1);
                w.write_str(s);
            }
        }
    }
}

impl Marshal for JsxProp {
    fn marshal(&self, w: &mut MarshalWriter) {
        match self {
            JsxProp::Punning { optional, name } => {
                w.write_block_header(0, 2);
                w.write_int(if *optional { 1 } else { 0 });
                name.marshal(w);
            }
            JsxProp::Value { name, optional, value } => {
                w.write_block_header(1, 3);
                name.marshal(w);
                w.write_int(if *optional { 1 } else { 0 });
                value.marshal(w);
            }
            JsxProp::Spreading { loc, expr } => {
                w.write_block_header(2, 2);
                loc.marshal(w);
                expr.marshal(w);
            }
        }
    }
}
