//! Constant compilation.
//!
//! Port of `lam_compile_const.ml`.
//! Extracted from `lam_compile.rs` for organization.

use super::js_exp_make::{
    js_expr_no_side_effects, poly_var_tag_access, poly_var_value_access, pure_indexed_block_item,
    pure_record_field_item,
};
use super::lam_compile::{LambdaCompiler, pointer_info_comment_text};
use crate::cmi::persistent_env::CmjExportConstant;
use crate::js_ir::arena::{Expr, ExprKind, JsArena};
use crate::js_ir::build::exp as E;
use crate::js_ir::op::{Kind, MutableFlag, Number};
use crate::js_ir::printer::convert_ident_name;
use crate::js_ir::{BinOp, ModuleId};
use crate::lambda::lam_compat::FieldDbgInfo;
use crate::lambda::lam_constant::{Constant, ConstructorRuntimeTag, PointerInfo};

impl LambdaCompiler {
    /// Keep in sync with `Constant::is_allocating`: a nested none is a new
    /// optional block.
    pub(crate) fn some_none_depth(cst: &Constant) -> Option<usize> {
        cst.some_none_depth()
    }

    pub(crate) fn nested_some_none(depth: usize, none: Expr, j: &mut JsArena) -> Expr {
        let mut none = none;
        for _ in 0..depth {
            none = E::new(ExprKind::OptionalBlock(none, false), j);
        }
        none
    }

    pub(crate) fn compile_some_constant(inner: &Constant, j: &mut JsArena) -> Expr {
        match Self::some_none_depth(inner) {
            Some(depth) => {
                let undefined = E::undefined(false, j);
                let none = E::new(ExprKind::OptionalBlock(undefined, false), j);
                Self::nested_some_none(depth, none, j)
            }
            None => {
                let value = Self::compile_constant(inner, j);
                E::new(ExprKind::OptionalBlock(value, true), j)
            }
        }
    }

    fn compile_runtime_int(value: i64, j: &mut JsArena) -> Expr {
        match i32::try_from(value) {
            Ok(value) => E::number(Number::int(value), j),
            Err(_) => E::number(Number::float(value.to_string()), j),
        }
    }

    fn commented_number(n: Number, comment: &str, j: &mut JsArena) -> Expr {
        let n = j.number_id(n);
        E::with_comment(ExprKind::Number(n), comment, j)
    }

    pub(crate) fn compile_constant(cst: &Constant, j: &mut JsArena) -> Expr {
        match cst {
            Constant::JsNull => E::null(j),
            Constant::JsUndefined { is_unit } => E::undefined(*is_unit, j),
            Constant::JsTrue => E::bool(true, j),
            Constant::JsFalse => E::bool(false, j),
            Constant::Int {
                i,
                comment: Some(info),
            } if matches!(**info, PointerInfo::Constructor(_)) => {
                let PointerInfo::Constructor(tag) = &**info else {
                    unreachable!()
                };
                match &tag.runtime_tag {
                    Some(ConstructorRuntimeTag::Int(value)) => Self::compile_runtime_int(*value, j),
                    // OCaml `Js_exp_make.tag_type`: `String s -> str s`.
                    Some(ConstructorRuntimeTag::String(value)) => E::string(value, j),
                    Some(ConstructorRuntimeTag::Float(value)) => {
                        E::number(Number::float(value.clone()), j)
                    }
                    Some(ConstructorRuntimeTag::BigInt(value)) => {
                        E::number(Number::bigint(true, value.clone()), j)
                    }
                    Some(ConstructorRuntimeTag::Bool(value)) => E::bool(*value, j),
                    Some(ConstructorRuntimeTag::Null) => E::null(j),
                    Some(ConstructorRuntimeTag::Undefined) => E::undefined(false, j),
                    None if tag.name != "[]" => E::string(&tag.name, j),
                    None => Self::commented_number(Number::int(*i), &tag.name, j),
                }
            }
            Constant::Int { i, comment } => {
                match pointer_info_comment_text(comment.as_ref().map(|v| &**v)) {
                    Some(comment) => Self::commented_number(Number::int(*i), &comment, j),
                    None => E::number(Number::int(*i), j),
                }
            }
            // lam_compile_const.ml: Const_constructor {name = "[]"}.
            Constant::Constructor(tag) if tag.name == "[]" => {
                Self::commented_number(Number::int(0), &tag.name, j)
            }
            Constant::Constructor(tag) => match &tag.literal {
                crate::types::VariantLiteralTag::Int(value) => {
                    E::number(Number::int(*value as i32), j)
                }
                // lam_compile_const.ml `E.tag_type t`: `String s -> str s`.
                crate::types::VariantLiteralTag::String(value) => E::string(value, j),
                crate::types::VariantLiteralTag::Float(value) => {
                    E::number(Number::float(value.clone()), j)
                }
                // js_exp_make.ml `literal_tag`: `Bigint_utils.parse_bigint`.
                crate::types::VariantLiteralTag::BigInt(value) => {
                    let (positive, digits) = crate::types::typecore::parse_bigint_literal(value);
                    E::number(Number::bigint(positive, digits), j)
                }
                crate::types::VariantLiteralTag::Bool(value) => E::bool(*value, j),
                crate::types::VariantLiteralTag::Null => E::null(j),
                crate::types::VariantLiteralTag::Undefined => E::undefined(false, j),
            },
            Constant::NativeInt { i, comment } => {
                match pointer_info_comment_text(comment.as_ref().map(|v| &**v)) {
                    Some(comment) => {
                        Self::commented_number(Number::float(i.to_string()), &comment, j)
                    }
                    None => E::number(Number::float(i.to_string()), j),
                }
            }
            Constant::Char(c) => E::number(Number::Int { i: *c, c: Some(*c) }, j),
            Constant::String(s) | Constant::ImmString(s) => E::string(s, j),
            Constant::Float(f) => E::number(Number::float(f.clone()), j),
            Constant::BigInt { negative, value } => {
                E::number(Number::bigint(!negative, value.clone()), j)
            }
            Constant::Pointer(name) => E::string(name, j),
            Constant::Block { tag_info, elements } => {
                let elems: Vec<Expr> = elements
                    .iter()
                    .map(|element| Self::compile_constant(element, j))
                    .collect();
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
                E::caml_block(&elems, MutableFlag::NA, (**tag_info).clone(), j)
            }
            Constant::Some(inner) => Self::compile_some_constant(inner, j),
            Constant::ModuleAlias => E::undefined(false, j),
        }
    }

    pub(crate) fn cmj_export_constant_expr(constant: CmjExportConstant, j: &mut JsArena) -> Expr {
        match constant {
            CmjExportConstant::Bool(value) => E::bool(value, j),
            CmjExportConstant::Null => E::null(j),
            CmjExportConstant::Undefined { is_unit } => E::undefined(is_unit, j),
        }
    }

    pub(crate) fn resolve_cmj_module_field_constant(
        &mut self,
        module: &ModuleId,
        field_name: &str,
    ) -> Option<Expr> {
        if !matches!(module.kind, Kind::Ml) {
            return None;
        }

        let resolver = &self.module_path_resolver;
        let constants = super::lam_compile::cached_cmj_table(
            &mut self.cmj_constant_cache,
            module.id.name(),
            || {
                resolver
                    .as_ref()
                    .and_then(|resolver| resolver.module_cmj_export_constants(module.id.name()))
            },
        )?;
        let constant = constants.get(field_name).copied()?;
        Some(Self::cmj_export_constant_expr(constant, &mut self.j))
    }

    pub(crate) fn compile_field_access(
        &mut self,
        idx: i32,
        info: &FieldDbgInfo,
        target: Expr,
    ) -> Expr {
        let indexed = |j: &mut JsArena, field: &str, pos: Option<i32>| {
            pure_indexed_block_item(j, target, idx)
                .unwrap_or_else(|| E::static_index(target, field, pos, j))
        };
        match info {
            FieldDbgInfo::Module { name } => match self.j.ek(target) {
                ExprKind::Qualified(q) if self.j.qual(q).1.is_none() => {
                    let module = self.j.qual(q).0.clone();
                    if let Some(constant) = self.resolve_cmj_module_field_constant(&module, name) {
                        return constant;
                    }
                    E::qualified(module, Some(name.clone()), &mut self.j)
                }
                _ => indexed(&mut self.j, &convert_ident_name(name), Some(idx)),
            },
            FieldDbgInfo::Record { name }
            | FieldDbgInfo::RecordInline { name }
            | FieldDbgInfo::RecordExtension { name } => {
                pure_record_field_item(&self.j, target, name, idx).unwrap_or_else(|| {
                    // OCaml `record_access` keeps the field position in
                    // `Static_index` so `js_pass_flatten_and_mark_dead` can
                    // substitute projections from materialized blocks
                    // (compiler/core/js_exp_make.ml:399-409).
                    E::static_index(target, name, Some(idx), &mut self.j)
                })
            }
            FieldDbgInfo::Extension => indexed(&mut self.j, &format!("_{}", idx), Some(idx)),
            // OCaml `cons_access` delegates to `record_access`, preserving
            // the position metadata (compiler/core/js_exp_make.ml:417-423).
            FieldDbgInfo::Cons => {
                let field = match idx {
                    0 => "hd".to_string(),
                    1 => "tl".to_string(),
                    _ => format!("_{}", idx),
                };
                indexed(&mut self.j, &field, Some(idx))
            }
            FieldDbgInfo::PolyVarTag => poly_var_tag_access(target, &mut self.j),
            FieldDbgInfo::PolyVarContent => poly_var_value_access(target, &mut self.j),
            FieldDbgInfo::VariantTag => indexed(&mut self.j, "TAG", None),
            // OCaml `variant_access` delegates to `record_access`, preserving
            // the position metadata (compiler/core/js_exp_make.ml:414-415).
            FieldDbgInfo::Variant => indexed(&mut self.j, &format!("_{}", idx), Some(idx)),
            _ => pure_indexed_block_item(&self.j, target, idx).unwrap_or_else(|| {
                let index = E::int(idx, &mut self.j);
                E::new(ExprKind::ArrayIndex(target, index), &mut self.j)
            }),
        }
    }

    pub(crate) fn compile_set_field(
        &mut self,
        idx: i32,
        info: &crate::lambda::lam_compat::SetFieldDbgInfo,
        target: Expr,
        value: Expr,
    ) -> Expr {
        let j = &mut self.j;
        if js_expr_no_side_effects(j, target)
            && matches!(
                j.ek(target),
                ExprKind::Array(_, _) | ExprKind::CamlBlock(_, _, _)
            )
        {
            return value;
        }

        let field = match info {
            crate::lambda::lam_compat::SetFieldDbgInfo::RecordSet(name)
            | crate::lambda::lam_compat::SetFieldDbgInfo::RecordInlineSet(name)
            | crate::lambda::lam_compat::SetFieldDbgInfo::RecordExtensionSet(name) => {
                // OCaml record assignment keeps `Some(pos)` on the indexed
                // property (compiler/core/js_exp_make.ml:504-520).
                E::static_index(target, name, Some(idx), j)
            }
        };
        E::bin(BinOp::Eq, field, value, j)
    }
}
