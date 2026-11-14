//! The `Debug` renderings types/canonical_sig.rs prints for declaration
//! metadata, written from segment rows. Each function names the old type
//! whose derived `Debug` it reproduces; the shapes are fixed by those
//! derives (compiler-rust/src/types/external_ffi_types.rs, decl.rs,
//! variant_runtime.rs, binary_ast/marshal.rs). Every function is O(output).

use std::fmt::Write as _;

use super::view::View;
use crate::tc::graph::NONE;
use crate::tc::segment::{
    AttributePayloadRow, BlockTypeRow, ConstantArgumentRow, ExternalKindRow, FfiAttributeRow,
    FfiLabelRow, FfiRow, InlineConstantRow, LiteralRow, LongidentRow, ModuleSourceRow, PrimitiveKindRow, Range,
    ReturnWrapperRow, RuntimeConstructorRow, SemanticStringValue, StringPair,
};

/// The two existing longident contracts differ only in unresolved spelling
/// and whether an application is accepted by the consumer.
#[derive(Clone, Copy)]
pub(super) enum LongidentStyle {
    Printed,
    Structural,
}

/// `{:?}` of a `&str`.
fn quoted(out: &mut String, text: &str) {
    let _ = write!(out, "{text:?}");
}

impl View<'_> {
    /// O(components + output bytes), one explicit stack shared by both sections.
    /// Printed follows Longident.flatten (no applications, raw #index names);
    /// structural follows canonical_sig.write_longident (<unresolved> names).
    pub(super) fn write_longident(&self, out: &mut String, lid: u32, style: LongidentStyle) {
        enum Step { Row(u32), Char(char), Name(u32), Unresolved(u32) }
        let mut work: smallvec::SmallVec<[Step; 8]> = smallvec::smallvec![Step::Row(lid)];
        while let Some(step) = work.pop() {
            match step {
                Step::Char(c) => out.push(c),
                Step::Name(name) => out.push_str(self.str(name)),
                Step::Unresolved(raw) => match style {
                    LongidentStyle::Printed => { write!(out, "#{raw}").expect("writing a string"); }
                    LongidentStyle::Structural => out.push_str("<unresolved>"),
                },
                Step::Row(row) => match self.longident(row) {
                    LongidentRow::Ident(name) => work.push(Step::Name(name)),
                    LongidentRow::Unresolved(raw) => work.push(Step::Unresolved(raw)),
                    LongidentRow::Dot { parent, name } => {
                        work.push(Step::Name(name));
                        work.push(Step::Char('.'));
                        work.push(Step::Row(parent));
                    }
                    LongidentRow::UnresolvedDot { parent, raw } => {
                        work.push(Step::Unresolved(raw));
                        work.push(Step::Char('.'));
                        work.push(Step::Row(parent));
                    }
                    LongidentRow::Apply { functor, argument } => {
                        assert!(matches!(style, LongidentStyle::Structural), "Longident.flat");
                        work.push(Step::Char(')'));
                        work.push(Step::Row(argument));
                        work.push(Step::Char('('));
                        work.push(Step::Row(functor));
                    }
                },
            }
        }
    }

    /// `{:?}` of a string of the pool.
    fn q(&self, out: &mut String, index: u32) {
        quoted(out, self.str(index));
    }

    /// `{:?}` of `Vec<String>` from a range of `indices`.
    pub(super) fn string_list_debug(&self, out: &mut String, range: Range) {
        out.push('[');
        for i in 0..range.len {
            if i > 0 {
                out.push_str(", ");
            }
            self.q(out, self.p.indices[(range.start + i) as usize]);
        }
        out.push(']');
    }

    /// `{:?}` of `Vec<(String, String)>`.
    fn pairs_debug(&self, out: &mut String, range: Range) {
        out.push('[');
        for i in 0..range.len {
            if i > 0 {
                out.push_str(", ");
            }
            let StringPair { first, second } = self.p.string_pairs[(range.start + i) as usize];
            out.push('(');
            self.q(out, first);
            out.push_str(", ");
            self.q(out, second);
            out.push(')');
        }
        out.push(']');
    }

    /// `{:?}` of `variant_runtime::LiteralTag`.
    pub(super) fn literal_debug(&self, out: &mut String, row: u32) {
        match self.p.literals[row as usize] {
            LiteralRow::String(s) => {
                out.push_str("String(");
                self.q(out, s);
                out.push(')');
            }
            LiteralRow::Int(value) => {
                let _ = write!(out, "Int({value})");
            }
            LiteralRow::Float(s) => {
                out.push_str("Float(");
                self.q(out, s);
                out.push(')');
            }
            LiteralRow::BigInt(s) => {
                out.push_str("BigInt(");
                self.q(out, s);
                out.push(')');
            }
            LiteralRow::Bool(value) => {
                let _ = write!(out, "Bool({value})");
            }
            LiteralRow::Null => out.push_str("Null"),
            LiteralRow::Undefined => out.push_str("Undefined"),
        }
    }

    /// `{:?}` of `Option<LiteralTag>`.
    pub(super) fn opt_literal_debug(&self, out: &mut String, row: u32) {
        if row == NONE {
            out.push_str("None");
        } else {
            out.push_str("Some(");
            self.literal_debug(out, row);
            out.push(')');
        }
    }

    /// `{:?}` of `Option<String>`.
    pub(super) fn opt_string_debug(&self, out: &mut String, index: u32) {
        if index == NONE {
            out.push_str("None");
        } else {
            out.push_str("Some(");
            self.q(out, index);
            out.push(')');
        }
    }

    /// types/canonical_sig.rs `block_type_text`.
    pub(super) fn block_type_text(&self, out: &mut String, row: u32) {
        match self.p.block_types[row as usize] {
            BlockTypeRow::Array => out.push_str("Instance(Array)"),
            BlockTypeRow::Class { name, ancestors } => {
                let _ = write!(out, "Instance({} extends ", self.str(name));
                self.string_list_debug(out, ancestors);
                out.push(')');
            }
            BlockTypeRow::Number => out.push_str("Number"),
            BlockTypeRow::String => out.push_str("String"),
            BlockTypeRow::Bigint => out.push_str("Bigint"),
            BlockTypeRow::Boolean => out.push_str("Boolean"),
            BlockTypeRow::Symbol => out.push_str("Symbol"),
            BlockTypeRow::Function => out.push_str("Function"),
            BlockTypeRow::Object => out.push_str("Object"),
            BlockTypeRow::Unknown => out.push_str("Unknown"),
        }
    }

    /// types/canonical_sig.rs `layout_text`.
    pub(super) fn layout_text(&self, out: &mut String, row: u32) {
        let layout = self.p.layouts[row as usize];
        let _ = write!(out, "unboxed={} tag_name=", layout.unboxed);
        self.opt_string_debug(out, layout.tag_name);
        out.push_str(" [");
        for i in 0..layout.constructors.len {
            if i > 0 {
                out.push_str(", ");
            }
            match self.p.runtime_constructors[(layout.constructors.start + i) as usize] {
                RuntimeConstructorRow::Constant { name, literal } => {
                    let _ = write!(out, "{}=Constant(", self.str(name));
                    self.literal_debug(out, literal);
                    out.push(')');
                }
                RuntimeConstructorRow::Tagged {
                    name,
                    literal,
                    tag_name,
                } => {
                    let _ = write!(out, "{}=Tagged(", self.str(name));
                    self.literal_debug(out, literal);
                    out.push_str(", tag_name=");
                    self.opt_string_debug(out, tag_name);
                    out.push(')');
                }
                RuntimeConstructorRow::Untagged {
                    name,
                    literal,
                    block_type,
                } => {
                    let _ = write!(out, "{}=Untagged(", self.str(name));
                    self.literal_debug(out, literal);
                    out.push_str(", ");
                    self.block_type_text(out, block_type);
                    out.push(')');
                }
            }
        }
        out.push(']');
    }

    /// `{:?}` of `decl::PrimKind`.
    pub(super) fn prim_kind_debug(&self, out: &mut String, kind: PrimitiveKindRow) {
        match kind {
            PrimitiveKindRow::Intrinsic => out.push_str("KindIntrinsic"),
            PrimitiveKindRow::External(ffi) => {
                out.push_str("KindExternal(");
                self.ffi_debug(out, ffi);
                out.push(')');
            }
            PrimitiveKindRow::Inline(constant) => {
                out.push_str("KindInlineConst(");
                self.inline_constant_debug(out, constant);
                out.push(')');
            }
        }
    }

    /// `{:?}` of `external_ffi_types::InlineConst`.
    fn inline_constant_debug(&self, out: &mut String, row: u32) {
        match self.p.inline_constants[row as usize] {
            InlineConstantRow::String(s) => {
                out.push_str("ConstString(");
                self.q(out, s);
                out.push(')');
            }
            InlineConstantRow::Bool(value) => {
                let _ = write!(out, "ConstBool({value})");
            }
            InlineConstantRow::Int(value) => {
                let _ = write!(out, "ConstInt({value})");
            }
            InlineConstantRow::Bigint { positive, digits } => {
                let _ = write!(out, "ConstBigint {{ positive: {positive}, digits: ");
                self.q(out, digits);
                out.push_str(" }");
            }
            InlineConstantRow::Float(s) => {
                out.push_str("ConstFloat(");
                self.q(out, s);
                out.push(')');
            }
        }
    }

    /// `{:?}` of `external_ffi_types::ExternalFfi`.
    fn ffi_debug(&self, out: &mut String, row: u32) {
        match self.p.ffi[row as usize] {
            FfiRow::Call {
                params,
                declaration,
                return_wrapper,
            } => {
                out.push_str("FfiBs([");
                for i in 0..params.len {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    let param = self.p.ffi_params[(params.start + i) as usize];
                    out.push_str("Param { arg_type: ");
                    self.ffi_attribute_debug(out, param.attribute);
                    out.push_str(", arg_label: ");
                    out.push_str(match param.label {
                        FfiLabelRow::Labelled => "ArgLabel",
                        FfiLabelRow::Optional => "ArgOptional",
                        _ => "ArgEmpty",
                    });
                    out.push_str(" }");
                }
                out.push_str("], ");
                out.push_str(return_wrapper_name(return_wrapper));
                out.push_str(", ");
                self.external_declaration_debug(out, declaration);
                out.push(')');
            }
            FfiRow::Object(params) => {
                out.push_str("FfiObjCreate([");
                for i in 0..params.len {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    let param = self.p.ffi_params[(params.start + i) as usize];
                    out.push_str("ObjParam { obj_arg_type: ");
                    self.ffi_attribute_debug(out, param.attribute);
                    out.push_str(", obj_arg_label: ");
                    match param.label {
                        FfiLabelRow::ObjectLabel(name) => {
                            out.push_str("ObjLabel { name: ");
                            self.q(out, name);
                            out.push_str(" }");
                        }
                        FfiLabelRow::ObjectOptional {
                            name,
                            no_nested_option,
                        } => {
                            out.push_str("ObjOptional { name: ");
                            self.q(out, name);
                            let _ =
                                write!(out, ", for_sure_no_nested_option: {no_nested_option} }}");
                        }
                        _ => out.push_str("ObjEmpty"),
                    }
                    out.push_str(" }");
                }
                out.push_str("])");
            }
        }
    }

    /// `{:?}` of `external_ffi_types::Attr`.
    fn ffi_attribute_debug(&self, out: &mut String, row: u32) {
        match self.p.ffi_attributes[row as usize] {
            FfiAttributeRow::PolyVarString(pairs) => {
                out.push_str("PolyVarString { descr: ");
                self.pairs_debug(out, pairs);
                out.push_str(" }");
            }
            FfiAttributeRow::PolyVar(range) => {
                out.push_str("PolyVar { descr: ");
                if range == NONE {
                    out.push_str("None");
                } else {
                    out.push_str("Some(");
                    self.pairs_debug(out, self.p.ranges[range as usize]);
                    out.push(')');
                }
                out.push_str(" }");
            }
            FfiAttributeRow::Int(range) => {
                out.push_str("Int([");
                for i in 0..range.len {
                    if i > 0 {
                        out.push_str(", ");
                    }
                    let pair = self.p.string_int_pairs[(range.start + i) as usize];
                    out.push('(');
                    self.q(out, pair.name);
                    let _ = write!(out, ", {})", pair.value);
                }
                out.push_str("])");
            }
            FfiAttributeRow::Constant(row) => {
                out.push_str("ArgCst(");
                match self.p.constant_arguments[row as usize] {
                    ConstantArgumentRow::Int(value) => {
                        let _ = write!(out, "ArgIntLit({value})");
                    }
                    ConstantArgumentRow::String(s) => {
                        out.push_str("ArgStringLit(");
                        self.q(out, s);
                        out.push(')');
                    }
                    ConstantArgumentRow::Json(s) => {
                        out.push_str("ArgJsonLit(");
                        self.q(out, s);
                        out.push(')');
                    }
                }
                out.push(')');
            }
            FfiAttributeRow::Unit => out.push_str("ExternUnit"),
            FfiAttributeRow::Nothing => out.push_str("Nothing"),
            FfiAttributeRow::Ignore => out.push_str("Ignore"),
            FfiAttributeRow::Unwrap => out.push_str("Unwrap"),
        }
    }

    /// `{:?}` of `external_ffi_types::ExternalDecl`, fields in declaration
    /// order (kind, module_, scopes, variadic, effective_arity).
    fn external_declaration_debug(&self, out: &mut String, row: u32) {
        let decl = self.p.external_declarations[row as usize];
        out.push_str("ExternalDecl { kind: ");
        let named = |out: &mut String, kind: &str, name: u32| {
            let _ = write!(out, "{kind} {{ name: ");
            self.q(out, name);
            out.push_str(" }");
        };
        match decl.kind {
            ExternalKindRow::Value(name) => named(out, "DeclVal", name),
            ExternalKindRow::Send(name) => named(out, "DeclSend", name),
            ExternalKindRow::New(name) => named(out, "DeclNew", name),
            ExternalKindRow::Get(name) => named(out, "DeclGet", name),
            ExternalKindRow::Set(name) => named(out, "DeclSet", name),
            ExternalKindRow::GetIndex => out.push_str("DeclGetIndex"),
            ExternalKindRow::SetIndex => out.push_str("DeclSetIndex"),
        }
        out.push_str(", module_: ");
        match decl.module {
            ModuleSourceRow::Absent => out.push_str("None"),
            ModuleSourceRow::Itself => out.push_str("Some(ModuleItself)"),
            ModuleSourceRow::Named(row) => {
                let module = self.p.external_modules[row as usize];
                out.push_str("Some(ModuleNamed(ExternalModuleName { bundle: ");
                self.q(out, module.bundle);
                out.push_str(", module_bind_name: ");
                if module.binding_hint == NONE {
                    out.push_str("PhintNothing");
                } else {
                    out.push_str("PhintName(");
                    self.q(out, module.binding_hint);
                    out.push(')');
                }
                out.push_str(", import_attributes: ");
                if module.import_attributes == NONE {
                    out.push_str("None");
                } else {
                    out.push_str("Some(");
                    self.pairs_debug(out, self.p.ranges[module.import_attributes as usize]);
                    out.push(')');
                }
                out.push_str(" }))");
            }
        }
        out.push_str(", scopes: ");
        self.string_list_debug(out, decl.scopes);
        let _ = write!(
            out,
            ", variadic: {}, effective_arity: {} }}",
            decl.variadic, decl.effective_arity
        );
    }

    /// types/canonical_sig.rs `attributes`: the payload text of one
    /// attribute (`{:?}` of `decl::AttributePayload`, `Deprecated` and
    /// `SemanticString` without locations).
    pub(super) fn attribute_payload_text(&self, out: &mut String, row: u32) {
        match self.p.attribute_payloads[row as usize] {
            AttributePayloadRow::Empty => out.push_str("Empty"),
            AttributePayloadRow::Str(s) => self.tagged(out, "Str", s),
            AttributePayloadRow::Int(value) => {
                let _ = write!(out, "Int({value})");
            }
            AttributePayloadRow::IntLiteral(s) => self.tagged(out, "IntLiteral", s),
            AttributePayloadRow::Float(s) => self.tagged(out, "Float", s),
            AttributePayloadRow::BigInt(s) => self.tagged(out, "BigInt", s),
            AttributePayloadRow::Bool(value) => {
                let _ = write!(out, "Bool({value})");
            }
            AttributePayloadRow::Ident(s) => self.tagged(out, "Ident", s),
            AttributePayloadRow::Structure(pairs) => {
                out.push_str("Structure(");
                self.pairs_debug(out, pairs);
                out.push(')');
            }
            AttributePayloadRow::StrTuple(range) => {
                out.push_str("StrTuple(");
                self.string_list_debug(out, range);
                out.push(')');
            }
            AttributePayloadRow::Deprecated(row) => {
                let deprecated = self.p.deprecations[row as usize];
                out.push_str("Deprecated reason=");
                match deprecated.reason {
                    SemanticStringValue::Missing => out.push_str("Ok(None)"),
                    SemanticStringValue::Valid(s) => {
                        out.push_str("Ok(Some(");
                        self.q(out, s);
                        out.push_str("))");
                    }
                    SemanticStringValue::Invalid(_) => out.push_str("Err(\"invalid\")"),
                }
                let _ = write!(
                    out,
                    " automigrate={} migrate=",
                    deprecated.can_be_automigrated
                );
                self.fragment_debug(out, deprecated.migrate);
                out.push_str(" migrate_in_pipe_chain=");
                self.fragment_debug(out, deprecated.migrate_in_pipe_chain);
            }
            AttributePayloadRow::SemanticString(row) => {
                let payload = self.p.semantic_strings[row as usize];
                out.push_str("SemanticString ");
                match payload.value {
                    SemanticStringValue::Valid(s) => {
                        out.push_str("Ok(");
                        self.q(out, s);
                        out.push(')');
                    }
                    // A `SemanticString` payload is never `Missing`.
                    SemanticStringValue::Missing | SemanticStringValue::Invalid(_) => {
                        out.push_str("Err(\"invalid\")");
                    }
                }
                let _ = write!(
                    out,
                    " braces={} template={}",
                    payload.braces, payload.template
                );
            }
        }
    }

    /// `Name("text")`.
    fn tagged(&self, out: &mut String, tag: &str, s: u32) {
        out.push_str(tag);
        out.push('(');
        self.q(out, s);
        out.push(')');
    }

    /// `{:?}` of `Option<binary_ast::marshal::MarshalFragment>`.
    fn fragment_debug(&self, out: &mut String, row: u32) {
        if row == NONE {
            out.push_str("None");
            return;
        }
        let fragment = self.p.marshal_fragments[row as usize];
        let bytes = &self.p.bytes
            [fragment.bytes.start as usize..(fragment.bytes.start + fragment.bytes.len) as usize];
        let _ = write!(
            out,
            "Some(MarshalFragment {{ bytes: {bytes:?}, objects: {}, size_32: {}, size_64: {} }})",
            fragment.objects, fragment.size_32, fragment.size_64
        );
    }
}

/// `{:?}` of `external_ffi_types::ReturnWrapper`.
fn return_wrapper_name(wrapper: ReturnWrapperRow) -> &'static str {
    match wrapper {
        ReturnWrapperRow::Unset => "ReturnUnset",
        ReturnWrapperRow::Identity => "ReturnIdentity",
        ReturnWrapperRow::NullToOption => "ReturnNullToOpt",
        ReturnWrapperRow::NullUndefinedToOption => "ReturnNullUndefinedToOpt",
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::tc::segment::Segment;

    #[test]
    fn shared_longident_walk_preserves_both_rendering_contracts() {
        let mut segment = Segment::default();
        segment.signature.bytes = Box::from(*b"AB");
        segment.signature.strings = Box::new([
            Range { start: 0, len: 1 }, Range { start: 1, len: 1 },
        ]);
        segment.signature.longidents = Box::new([
            LongidentRow::Ident(0),
            LongidentRow::Dot { parent: 0, name: 1 },
            LongidentRow::Unresolved(17),
            LongidentRow::UnresolvedDot { parent: 1, raw: 9 },
            LongidentRow::Apply { functor: 0, argument: 3 },
        ]);
        let view = View::new(&segment);
        for (row, style, expected) in [
            (1, LongidentStyle::Printed, "A.B"),
            (2, LongidentStyle::Printed, "#17"),
            (3, LongidentStyle::Printed, "A.B.#9"),
            (3, LongidentStyle::Structural, "A.B.<unresolved>"),
            (4, LongidentStyle::Structural, "A(A.B.<unresolved>)"),
        ] {
            let mut text = String::new();
            view.write_longident(&mut text, row, style);
            assert_eq!(text, expected);
        }
    }
}
