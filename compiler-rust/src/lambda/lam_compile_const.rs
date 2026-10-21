//! Constant compilation.
//!
//! Port of `lam_compile_const.ml`.
//! Extracted from `lam_compile.rs` for organization.

use ahash::AHashMap as HashMap;

use super::js_exp_make::{
    int_expr, js_expr_no_side_effects, poly_var_tag_access, poly_var_value_access,
    pure_indexed_block_item, pure_record_field_item,
};
use super::lam_compile::{LambdaCompiler, pointer_info_comment_text};
use crate::cmi::persistent_env::CmjExportConstant;
use crate::ident::Ident;
use crate::js_ir::op::{Kind, MutableFlag, Number};
use crate::js_ir::printer::convert_ident_name;
use crate::js_ir::{BinOp, Block, Expression, ExpressionDesc, ModuleId};
use crate::lambda::lam_compat::{FieldDbgInfo, SetFieldDbgInfo};
use crate::lambda::lam_constant::{Constant, ConstructorRuntimeTag, PointerInfo};
use crate::lambda::lam_primitive::Primitive;

impl LambdaCompiler {
    pub(crate) fn some_none_depth(cst: &Constant) -> Option<usize> {
        match cst {
            Constant::Some(inner) => Self::some_none_depth(inner).map(|depth| depth + 1),
            Constant::ModuleAlias | Constant::JsUndefined { .. } => Some(0),
            _ => None,
        }
    }

    pub(crate) fn nested_some_none(depth: usize, none: Expression) -> Expression {
        if depth == 0 {
            none
        } else {
            Self::nested_some_none(
                depth - 1,
                Expression::new(ExpressionDesc::OptionalBlock(Box::new(none), false)),
            )
        }
    }

    pub(crate) fn compile_some_constant(inner: &Constant) -> Expression {
        match Self::some_none_depth(inner) {
            Some(depth) => Self::nested_some_none(
                depth,
                Expression::new(ExpressionDesc::OptionalBlock(
                    Box::new(Expression::undefined(false)),
                    false,
                )),
            ),
            None => Expression::new(ExpressionDesc::OptionalBlock(
                Box::new(Self::compile_constant(inner)),
                true,
            )),
        }
    }

    fn compile_runtime_int(value: i64) -> Expression {
        match i32::try_from(value) {
            Ok(value) => Expression::number(Number::int(value)),
            Err(_) => Expression::number(Number::float(value.to_string())),
        }
    }

    pub(crate) fn compile_constant(cst: &Constant) -> Expression {
        match cst {
            Constant::JsNull => Expression::null(),
            Constant::JsUndefined { is_unit } => Expression::undefined(*is_unit),
            Constant::JsTrue => Expression::bool(true),
            Constant::JsFalse => Expression::bool(false),
            Constant::Int {
                i,
                comment: Some(info),
            } if matches!(**info, PointerInfo::Constructor(_)) => {
                let PointerInfo::Constructor(tag) = &**info else {
                    unreachable!()
                };
                match &tag.runtime_tag {
                    Some(ConstructorRuntimeTag::Int(value)) => Self::compile_runtime_int(*value),
                    // OCaml `Js_exp_make.tag_type`: `String s -> str s`.
                    Some(ConstructorRuntimeTag::String(value)) => {
                        Expression::new(ExpressionDesc::Str(value.clone()))
                    }
                    Some(ConstructorRuntimeTag::Float(value)) => {
                        Expression::number(Number::float(value.clone()))
                    }
                    Some(ConstructorRuntimeTag::BigInt(value)) => {
                        Expression::number(Number::bigint(true, value.clone()))
                    }
                    Some(ConstructorRuntimeTag::Bool(value)) => Expression::bool(*value),
                    Some(ConstructorRuntimeTag::Null) => Expression::null(),
                    Some(ConstructorRuntimeTag::Undefined) => Expression::undefined(false),
                    None if tag.name != "[]" => Expression::string(tag.name.clone()),
                    None => Expression::with_comment(
                        ExpressionDesc::Number(Number::int(*i)),
                        tag.name.clone(),
                    ),
                }
            }
            Constant::Int { i, comment } => {
                match pointer_info_comment_text(comment.as_ref().map(|v| &**v)) {
                    Some(comment) => {
                        Expression::with_comment(ExpressionDesc::Number(Number::int(*i)), comment)
                    }
                    None => Expression::number(Number::int(*i)),
                }
            }
            Constant::Constructor(tag) => match &tag.literal {
                Some(crate::types::VariantLiteralTag::Int(value)) => {
                    Expression::number(Number::int(*value as i32))
                }
                // lam_compile_const.ml `E.tag_type t`: `String s -> str s`.
                Some(crate::types::VariantLiteralTag::String(value)) => {
                    Expression::new(ExpressionDesc::Str(value.clone()))
                }
                Some(crate::types::VariantLiteralTag::Float(value)) => {
                    Expression::number(Number::float(value.clone()))
                }
                // js_exp_make.ml `literal_tag`: `Bigint_utils.parse_bigint`.
                Some(crate::types::VariantLiteralTag::BigInt(value)) => {
                    let (positive, digits) = crate::types::typecore::parse_bigint_literal(value);
                    Expression::number(Number::bigint(positive, digits))
                }
                Some(crate::types::VariantLiteralTag::Bool(value)) => Expression::bool(*value),
                Some(crate::types::VariantLiteralTag::Null) => Expression::null(),
                Some(crate::types::VariantLiteralTag::Undefined) => Expression::undefined(false),
                None if tag.name == "[]" => Expression::with_comment(
                    ExpressionDesc::Number(Number::int(0)),
                    tag.name.clone(),
                ),
                None => Expression::string(tag.name.clone()),
            },
            Constant::NativeInt { i, comment } => {
                match pointer_info_comment_text(comment.as_ref().map(|v| &**v)) {
                    Some(comment) => Expression::with_comment(
                        ExpressionDesc::Number(Number::float(i.to_string())),
                        comment,
                    ),
                    None => Expression::number(Number::float(i.to_string())),
                }
            }
            Constant::Char(c) => Expression::number(Number::Int { i: *c, c: Some(*c) }),
            Constant::String(s) => Expression::string(s.clone()),
            Constant::ImmString(s) => Expression::new(ExpressionDesc::Str(s.clone())),
            Constant::Float(f) => Expression::number(Number::float(f.clone())),
            Constant::BigInt { negative, value } => {
                Expression::number(Number::bigint(!negative, value.clone()))
            }
            Constant::Pointer(name) => Expression::string(name.clone()),
            Constant::Block { tag_info, elements } => {
                let elems = elements.iter().map(Self::compile_constant).collect();
                // OCaml's `Lam_compile_const.translate` (lam_compile_const.ml:67-69)
                // calls `Js_of_lam_block.make_block NA tag_info ...` — `NA`, not
                // `Immutable`. Downstream JS-pass rules that match
                // `Caml_block(_, Immutable, _, _)` (notably the binding-hoist rule
                // in `js_pass_flatten_and_mark_dead.ml:172-183`) deliberately skip
                // `NA`, so e.g. `let h = list{1,2,3,4}` (a `Lconst Const_block`)
                // stays inline as `{hd: 1, tl: {hd: 2, ...}}` while
                // `let CustomizeTags = Pmakeblock(...)` (which IS `Immutable`) gets
                // its inner `Caml_block(NA)` constants hoisted to
                // `let CustomizeTags_d = ...`. Mirror the OCaml convention here.
                Expression::new(ExpressionDesc::CamlBlock(
                    elems,
                    MutableFlag::NA,
                    tag_info.clone(),
                ))
            }
            Constant::Some(inner) => Self::compile_some_constant(inner),
            Constant::ModuleAlias => Expression::undefined(false),
        }
    }

    pub(crate) fn cmj_export_constant_expr(constant: CmjExportConstant) -> Expression {
        match constant {
            CmjExportConstant::Bool(value) => Expression::bool(value),
            CmjExportConstant::Null => Expression::null(),
            CmjExportConstant::Undefined { is_unit } => Expression::undefined(is_unit),
        }
    }

    pub(crate) fn resolve_cmj_module_field_constant(
        &mut self,
        module: &ModuleId,
        field_name: &str,
    ) -> Option<Expression> {
        if !matches!(module.kind, Kind::Ml) {
            return None;
        }

        if !self.cmj_constant_cache.contains_key(module.id.name()) {
            let constants = self
                .module_path_resolver
                .as_ref()
                .and_then(|resolver| resolver.module_cmj_export_constants(module.id.name()));
            self.cmj_constant_cache
                .insert(module.id.name().to_string(), constants);
        }

        let constants = self
            .cmj_constant_cache
            .get(module.id.name())
            .and_then(|constants| constants.as_ref())?;
        let constant = constants.get(field_name).copied()?;
        Some(Self::cmj_export_constant_expr(constant))
    }

    pub(crate) fn compile_field_access(
        &mut self,
        idx: i32,
        info: &FieldDbgInfo,
        target: &Expression,
    ) -> Expression {
        match info {
            FieldDbgInfo::Module { name } => match &target.desc {
                ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(module, None)) => {
                    if let Some(constant) = self.resolve_cmj_module_field_constant(module, name) {
                        return constant;
                    }
                    Expression::qualified(module.clone(), Some(name.clone()))
                }
                _ => pure_indexed_block_item(target, idx).unwrap_or_else(|| {
                    Expression::new(ExpressionDesc::StaticIndex(
                        Box::new(target.clone()),
                        convert_ident_name(name),
                        Some(idx),
                    ))
                }),
            },
            FieldDbgInfo::Record { name }
            | FieldDbgInfo::RecordInline { name }
            | FieldDbgInfo::RecordExtension { name } => pure_record_field_item(target, name, idx)
                .unwrap_or_else(|| {
                    // OCaml `record_access` keeps the field position in
                    // `Static_index` so `js_pass_flatten_and_mark_dead` can
                    // substitute projections from materialized blocks
                    // (compiler/core/js_exp_make.ml:399-409).
                    Expression::new(ExpressionDesc::StaticIndex(
                        Box::new(target.clone()),
                        name.clone(),
                        Some(idx),
                    ))
                }),
            FieldDbgInfo::Extension => pure_indexed_block_item(target, idx).unwrap_or_else(|| {
                Expression::new(ExpressionDesc::StaticIndex(
                    Box::new(target.clone()),
                    format!("_{}", idx),
                    Some(idx),
                ))
            }),
            FieldDbgInfo::Cons => pure_indexed_block_item(target, idx).unwrap_or_else(|| {
                // OCaml `cons_access` delegates to `record_access`, preserving
                // the position metadata (compiler/core/js_exp_make.ml:417-423).
                Expression::new(ExpressionDesc::StaticIndex(
                    Box::new(target.clone()),
                    match idx {
                        0 => "hd".to_string(),
                        1 => "tl".to_string(),
                        _ => format!("_{}", idx),
                    },
                    Some(idx),
                ))
            }),
            FieldDbgInfo::PolyVarTag => poly_var_tag_access(target),
            FieldDbgInfo::PolyVarContent => poly_var_value_access(target),
            FieldDbgInfo::VariantTag => pure_indexed_block_item(target, idx).unwrap_or_else(|| {
                Expression::new(ExpressionDesc::StaticIndex(
                    Box::new(target.clone()),
                    "TAG".to_string(),
                    None,
                ))
            }),
            FieldDbgInfo::Variant => pure_indexed_block_item(target, idx).unwrap_or_else(|| {
                // OCaml `variant_access` delegates to `record_access`, preserving
                // the position metadata (compiler/core/js_exp_make.ml:414-415).
                Expression::new(ExpressionDesc::StaticIndex(
                    Box::new(target.clone()),
                    format!("_{}", idx),
                    Some(idx),
                ))
            }),
            _ => pure_indexed_block_item(target, idx).unwrap_or_else(|| {
                Expression::new(ExpressionDesc::ArrayIndex(
                    Box::new(target.clone()),
                    Box::new(Expression::number(Number::int(idx))),
                ))
            }),
        }
    }

    pub(crate) fn compile_set_field(
        &self,
        idx: i32,
        info: &crate::lambda::lam_compat::SetFieldDbgInfo,
        target: &Expression,
        value: &Expression,
    ) -> Expression {
        if js_expr_no_side_effects(target)
            && matches!(
                target.desc,
                ExpressionDesc::Array(_, _) | ExpressionDesc::CamlBlock(_, _, _)
            )
        {
            return value.clone();
        }

        let field = match info {
            crate::lambda::lam_compat::SetFieldDbgInfo::RecordSet(name)
            | crate::lambda::lam_compat::SetFieldDbgInfo::RecordInlineSet(name)
            | crate::lambda::lam_compat::SetFieldDbgInfo::RecordExtensionSet(name) => {
                // OCaml record assignment keeps `Some(pos)` on the indexed
                // property (compiler/core/js_exp_make.ml:504-520).
                Expression::new(ExpressionDesc::StaticIndex(
                    Box::new(target.clone()),
                    name.clone(),
                    Some(idx),
                ))
            }
        };
        Expression::bin(BinOp::Eq, field, value.clone())
    }
}
