//! Internal `let.unwrap` (`let?`) rewrite pass.
//!
//! OCaml performs this in `bs_builtin_ppx.ml` before writing `.ast` files.
//! In Rust parser mode we need the same lowering so downstream compilation
//! observes the transformed tree.

use crate::parse_arena::{ExprIdx, Located, ModExprIdx, ParseArena, PatIdx};
use crate::parser::ast::{
    Attribute, Attributes, Case, Expression, ExpressionDesc, ExpressionRecordField, Extension,
    JsxContainerElement, JsxElement, JsxFragment, JsxProp, JsxUnaryElement, ModuleExpr,
    ModuleExprDesc, Pattern, PatternDesc, Payload, RecFlag, SignatureItem, SignatureItemDesc,
    StructureItem, StructureItemDesc, ValueBinding,
};
use crate::parser::longident::Longident;

const LET_UNWRAP_ATTR: &str = "let.unwrap";
const FEATURE_NOT_ENABLED_MSG: &str = "Experimental feature not enabled: LetUnwrap. Enable it by setting \"LetUnwrap\" to true under \"experimental-features\" in rescript.json.";
const TOPLEVEL_NOT_SUPPORTED_MSG: &str = "`let?` is not allowed for top-level bindings.";
const UNSUPPORTED_TYPE_MSG: &str =
    "`let?` is only supported in let bindings targeting the `result` or `option` type.";

#[derive(Debug, Clone, Copy)]
enum LetUnwrapKind {
    ResultOk,
    ResultError,
    OptionSome,
    OptionNone,
}

/// The rewrite only acts on `let.unwrap` attributes. When the arena holds no
/// such string, no node can carry one and the rewrite would only copy the tree.
fn arena_mentions_let_unwrap(arena: &ParseArena) -> bool {
    arena.find_string_idx(LET_UNWRAP_ATTR).is_some()
}

pub fn rewrite_structure(
    structure: &[StructureItem],
    arena: &mut ParseArena,
    let_unwrap_enabled: bool,
) -> Result<Vec<StructureItem>, String> {
    if !arena_mentions_let_unwrap(arena) {
        return Ok(structure.to_vec());
    }
    structure
        .iter()
        .map(|item| rewrite_structure_item(item, arena, let_unwrap_enabled))
        .collect()
}

pub fn rewrite_signature(
    signature: &[SignatureItem],
    arena: &mut ParseArena,
    let_unwrap_enabled: bool,
) -> Result<Vec<SignatureItem>, String> {
    if !arena_mentions_let_unwrap(arena) {
        return Ok(signature.to_vec());
    }
    signature
        .iter()
        .map(|item| rewrite_signature_item(item, arena, let_unwrap_enabled))
        .collect()
}

fn rewrite_signature_item(
    item: &SignatureItem,
    arena: &mut ParseArena,
    let_unwrap_enabled: bool,
) -> Result<SignatureItem, String> {
    let desc = match &*item.psig_desc {
        SignatureItemDesc::Psig_extension(inner) => {
            let (ext, attrs) = &**inner;
            let rewritten_ext = rewrite_extension(ext, arena, let_unwrap_enabled)?;
            SignatureItemDesc::Psig_extension(Box::new((rewritten_ext, attrs.clone())))
        }
        _ => (*item.psig_desc).clone(),
    };

    Ok(SignatureItem {
        psig_desc: Box::new(desc),
        psig_loc: item.psig_loc,
    })
}

fn rewrite_structure_item(
    item: &StructureItem,
    arena: &mut ParseArena,
    let_unwrap_enabled: bool,
) -> Result<StructureItem, String> {
    let desc = match &*item.pstr_desc {
        StructureItemDesc::Pstr_eval(inner) => {
            let (expr, attrs) = &**inner;
            let rewritten_expr = rewrite_expr_idx(*expr, arena, let_unwrap_enabled)?;
            StructureItemDesc::Pstr_eval(Box::new((rewritten_expr, attrs.clone())))
        }
        StructureItemDesc::Pstr_value(inner) => {
            let (rec_flag, bindings) = &**inner;
            if bindings
                .iter()
                .any(|vb| has_let_unwrap_attr(&vb.pvb_attributes, arena))
            {
                return if let_unwrap_enabled {
                    Err(TOPLEVEL_NOT_SUPPORTED_MSG.to_string())
                } else {
                    Err(FEATURE_NOT_ENABLED_MSG.to_string())
                };
            }

            let rewritten_bindings = bindings
                .iter()
                .map(|vb| rewrite_value_binding(vb, arena, let_unwrap_enabled))
                .collect::<Result<Vec<_>, _>>()?;
            StructureItemDesc::Pstr_value(Box::new((*rec_flag, rewritten_bindings)))
        }
        StructureItemDesc::Pstr_module(mb) => {
            let rewritten_expr = rewrite_mod_expr_idx(mb.pmb_expr, arena, let_unwrap_enabled)?;
            StructureItemDesc::Pstr_module(Box::new(crate::parser::ast::ModuleBinding {
                pmb_name: mb.pmb_name.clone(),
                pmb_expr: rewritten_expr,
                pmb_attributes: mb.pmb_attributes.clone(),
                pmb_loc: mb.pmb_loc,
            }))
        }
        StructureItemDesc::Pstr_recmodule(mbs) => {
            let rewritten = mbs
                .iter()
                .map(|mb| {
                    let rewritten_expr =
                        rewrite_mod_expr_idx(mb.pmb_expr, arena, let_unwrap_enabled)?;
                    Ok(crate::parser::ast::ModuleBinding {
                        pmb_name: mb.pmb_name.clone(),
                        pmb_expr: rewritten_expr,
                        pmb_attributes: mb.pmb_attributes.clone(),
                        pmb_loc: mb.pmb_loc,
                    })
                })
                .collect::<Result<Vec<_>, String>>()?;
            StructureItemDesc::Pstr_recmodule(Box::new(rewritten))
        }
        StructureItemDesc::Pstr_include(incl) => {
            let rewritten_mod = rewrite_mod_expr_idx(incl.pincl_mod, arena, let_unwrap_enabled)?;
            StructureItemDesc::Pstr_include(Box::new(crate::parser::ast::IncludeDeclaration {
                pincl_mod: rewritten_mod,
                pincl_attributes: incl.pincl_attributes.clone(),
                pincl_loc: incl.pincl_loc,
            }))
        }
        StructureItemDesc::Pstr_extension(inner) => {
            let (ext, attrs) = &**inner;
            let rewritten_ext = rewrite_extension(ext, arena, let_unwrap_enabled)?;
            StructureItemDesc::Pstr_extension(Box::new((rewritten_ext, attrs.clone())))
        }
        _ => (*item.pstr_desc).clone(),
    };

    Ok(StructureItem {
        pstr_desc: Box::new(desc),
        pstr_loc: item.pstr_loc,
    })
}

fn rewrite_extension(
    ext: &Extension,
    arena: &mut ParseArena,
    let_unwrap_enabled: bool,
) -> Result<Extension, String> {
    let (name, payload) = ext;
    let payload = rewrite_payload(payload, arena, let_unwrap_enabled)?;
    Ok((name.clone(), payload))
}

fn rewrite_payload(
    payload: &Payload,
    arena: &mut ParseArena,
    let_unwrap_enabled: bool,
) -> Result<Payload, String> {
    match payload {
        Payload::PStr(items) => Ok(Payload::PStr(Box::new(rewrite_structure(
            items,
            arena,
            let_unwrap_enabled,
        )?))),
        Payload::PSig(items) => Ok(Payload::PSig(Box::new(rewrite_signature(
            items,
            arena,
            let_unwrap_enabled,
        )?))),
        Payload::PTyp(idx) => Ok(Payload::PTyp(*idx)),
        Payload::PPat(inner) => {
            let (pat, guard) = &**inner;
            let rewritten_guard = guard
                .map(|idx| rewrite_expr_idx(idx, arena, let_unwrap_enabled))
                .transpose()?;
            Ok(Payload::PPat(Box::new((*pat, rewritten_guard))))
        }
    }
}

fn rewrite_expr_idx(
    idx: ExprIdx,
    arena: &mut ParseArena,
    let_unwrap_enabled: bool,
) -> Result<ExprIdx, String> {
    let expr = arena.get_expr(idx).clone();
    let rewritten = rewrite_expression(&expr, arena, let_unwrap_enabled)?;
    Ok(arena.push_expr(rewritten))
}

fn rewrite_mod_expr_idx(
    idx: ModExprIdx,
    arena: &mut ParseArena,
    let_unwrap_enabled: bool,
) -> Result<ModExprIdx, String> {
    let mod_expr = arena.get_mod_expr(idx).clone();
    let rewritten = rewrite_module_expr(&mod_expr, arena, let_unwrap_enabled)?;
    Ok(arena.push_mod_expr(rewritten))
}

fn rewrite_module_expr(
    mod_expr: &ModuleExpr,
    arena: &mut ParseArena,
    let_unwrap_enabled: bool,
) -> Result<ModuleExpr, String> {
    let desc = match &*mod_expr.pmod_desc {
        ModuleExprDesc::Pmod_structure(items) => ModuleExprDesc::Pmod_structure(Box::new(
            rewrite_structure(items, arena, let_unwrap_enabled)?,
        )),
        ModuleExprDesc::Pmod_functor(inner) => {
            let (name, mod_type, body) = &**inner;
            let rewritten_body = rewrite_mod_expr_idx(*body, arena, let_unwrap_enabled)?;
            ModuleExprDesc::Pmod_functor(Box::new((name.clone(), *mod_type, rewritten_body)))
        }
        ModuleExprDesc::Pmod_apply(lhs, rhs) => {
            let rewritten_lhs = rewrite_mod_expr_idx(*lhs, arena, let_unwrap_enabled)?;
            let rewritten_rhs = rewrite_mod_expr_idx(*rhs, arena, let_unwrap_enabled)?;
            ModuleExprDesc::Pmod_apply(rewritten_lhs, rewritten_rhs)
        }
        ModuleExprDesc::Pmod_constraint(expr, mod_type) => {
            let rewritten_expr = rewrite_mod_expr_idx(*expr, arena, let_unwrap_enabled)?;
            ModuleExprDesc::Pmod_constraint(rewritten_expr, *mod_type)
        }
        ModuleExprDesc::Pmod_unpack(expr) => {
            let rewritten_expr = rewrite_expr_idx(*expr, arena, let_unwrap_enabled)?;
            ModuleExprDesc::Pmod_unpack(rewritten_expr)
        }
        ModuleExprDesc::Pmod_extension(ext) => ModuleExprDesc::Pmod_extension(Box::new(
            rewrite_extension(ext, arena, let_unwrap_enabled)?,
        )),
        _ => (*mod_expr.pmod_desc).clone(),
    };

    Ok(ModuleExpr {
        pmod_desc: Box::new(desc),
        pmod_loc: mod_expr.pmod_loc,
        pmod_attributes: mod_expr.pmod_attributes.clone(),
    })
}

fn rewrite_value_binding(
    vb: &ValueBinding,
    arena: &mut ParseArena,
    let_unwrap_enabled: bool,
) -> Result<ValueBinding, String> {
    let rewritten_expr = rewrite_expr_idx(vb.pvb_expr, arena, let_unwrap_enabled)?;
    Ok(ValueBinding {
        pvb_pat: vb.pvb_pat,
        pvb_expr: rewritten_expr,
        pvb_attributes: vb.pvb_attributes.clone(),
        pvb_loc: vb.pvb_loc,
    })
}

fn rewrite_expression(
    expr: &Expression,
    arena: &mut ParseArena,
    let_unwrap_enabled: bool,
) -> Result<Expression, String> {
    let desc = match &*expr.pexp_desc {
        ExpressionDesc::Pexp_ident(_)
        | ExpressionDesc::Pexp_constant(_)
        | ExpressionDesc::Pexp_break
        | ExpressionDesc::Pexp_continue => (*expr.pexp_desc).clone(),
        ExpressionDesc::Pexp_let(inner) => {
            let (rec_flag, bindings, body) = &**inner;
            return rewrite_let_expression(
                expr,
                *rec_flag,
                bindings,
                *body,
                arena,
                let_unwrap_enabled,
            );
        }
        ExpressionDesc::Pexp_fun(inner) => {
            let rewritten_default = inner
                .default
                .map(|idx| rewrite_expr_idx(idx, arena, let_unwrap_enabled))
                .transpose()?;
            let rewritten_rhs = rewrite_expr_idx(inner.rhs, arena, let_unwrap_enabled)?;
            ExpressionDesc::Pexp_fun(Box::new(crate::parser::ast::PexpFun {
                arg_label: inner.arg_label.clone(),
                default: rewritten_default,
                lhs: inner.lhs,
                rhs: rewritten_rhs,
                arity: inner.arity,
                is_async: inner.is_async,
            }))
        }
        ExpressionDesc::Pexp_apply(inner) => {
            let rewritten_funct = rewrite_expr_idx(inner.funct, arena, let_unwrap_enabled)?;
            let rewritten_args = inner
                .args
                .iter()
                .map(|(lbl, arg)| {
                    let rewritten = rewrite_expr_idx(*arg, arena, let_unwrap_enabled)?;
                    Ok((lbl.clone(), rewritten))
                })
                .collect::<Result<Vec<_>, String>>()?;
            ExpressionDesc::Pexp_apply(Box::new(crate::parser::ast::PexpApply {
                funct: rewritten_funct,
                args: rewritten_args,
                partial: inner.partial,
                transformed_jsx: inner.transformed_jsx,
            }))
        }
        ExpressionDesc::Pexp_match(inner) => {
            let (scrutinee, cases) = &**inner;
            let rewritten_scrutinee = rewrite_expr_idx(*scrutinee, arena, let_unwrap_enabled)?;
            let rewritten_cases = rewrite_cases(cases, arena, let_unwrap_enabled)?;
            ExpressionDesc::Pexp_match(Box::new((rewritten_scrutinee, rewritten_cases)))
        }
        ExpressionDesc::Pexp_try(inner) => {
            let (body, cases) = &**inner;
            let rewritten_body = rewrite_expr_idx(*body, arena, let_unwrap_enabled)?;
            let rewritten_cases = rewrite_cases(cases, arena, let_unwrap_enabled)?;
            ExpressionDesc::Pexp_try(Box::new((rewritten_body, rewritten_cases)))
        }
        ExpressionDesc::Pexp_tuple(items) => {
            let rewritten = items
                .iter()
                .map(|idx| rewrite_expr_idx(*idx, arena, let_unwrap_enabled))
                .collect::<Result<Vec<_>, _>>()?;
            ExpressionDesc::Pexp_tuple(Box::new(rewritten))
        }
        ExpressionDesc::Pexp_construct(lid, args) => {
            let rewritten = args
                .txt
                .iter()
                .map(|idx| rewrite_expr_idx(*idx, arena, let_unwrap_enabled))
                .collect::<Result<Vec<_>, _>>()?;
            ExpressionDesc::Pexp_construct(*lid, crate::parser::ast::ctor_args(rewritten, args.loc))
        }
        ExpressionDesc::Pexp_variant(inner) => {
            let (label, args) = &**inner;
            let rewritten = args
                .txt
                .iter()
                .map(|idx| rewrite_expr_idx(*idx, arena, let_unwrap_enabled))
                .collect::<Result<Vec<_>, _>>()?;
            ExpressionDesc::Pexp_variant(Box::new((label.clone(), Located::new(rewritten, args.loc))))
        }
        ExpressionDesc::Pexp_record(inner) => {
            let (fields, spread) = &**inner;
            let rewritten_fields = fields
                .iter()
                .map(|field| {
                    let rewritten_expr = rewrite_expr_idx(field.expr, arena, let_unwrap_enabled)?;
                    Ok(ExpressionRecordField {
                        lid: field.lid,
                        expr: rewritten_expr,
                        opt: field.opt,
                    })
                })
                .collect::<Result<Vec<_>, String>>()?;
            let rewritten_spread = spread
                .map(|idx| rewrite_expr_idx(idx, arena, let_unwrap_enabled))
                .transpose()?;
            ExpressionDesc::Pexp_record(Box::new((rewritten_fields, rewritten_spread)))
        }
        ExpressionDesc::Pexp_field(owner, lid) => {
            let rewritten_owner = rewrite_expr_idx(*owner, arena, let_unwrap_enabled)?;
            ExpressionDesc::Pexp_field(rewritten_owner, *lid)
        }
        ExpressionDesc::Pexp_setfield(inner) => {
            let (owner, field, value) = &**inner;
            let rewritten_owner = rewrite_expr_idx(*owner, arena, let_unwrap_enabled)?;
            let rewritten_value = rewrite_expr_idx(*value, arena, let_unwrap_enabled)?;
            ExpressionDesc::Pexp_setfield(Box::new((rewritten_owner, *field, rewritten_value)))
        }
        ExpressionDesc::Pexp_array(items) => {
            let rewritten = items
                .iter()
                .map(|idx| rewrite_expr_idx(*idx, arena, let_unwrap_enabled))
                .collect::<Result<Vec<_>, _>>()?;
            ExpressionDesc::Pexp_array(Box::new(rewritten))
        }
        ExpressionDesc::Pexp_ifthenelse(inner) => {
            let (cond, then_expr, else_expr) = &**inner;
            let rewritten_cond = rewrite_expr_idx(*cond, arena, let_unwrap_enabled)?;
            let rewritten_then = rewrite_expr_idx(*then_expr, arena, let_unwrap_enabled)?;
            let rewritten_else = else_expr
                .map(|idx| rewrite_expr_idx(idx, arena, let_unwrap_enabled))
                .transpose()?;
            ExpressionDesc::Pexp_ifthenelse(Box::new((
                rewritten_cond,
                rewritten_then,
                rewritten_else,
            )))
        }
        ExpressionDesc::Pexp_sequence(lhs, rhs) => {
            let rewritten_lhs = rewrite_expr_idx(*lhs, arena, let_unwrap_enabled)?;
            let rewritten_rhs = rewrite_expr_idx(*rhs, arena, let_unwrap_enabled)?;
            ExpressionDesc::Pexp_sequence(rewritten_lhs, rewritten_rhs)
        }
        ExpressionDesc::Pexp_while(cond, body) => {
            let rewritten_cond = rewrite_expr_idx(*cond, arena, let_unwrap_enabled)?;
            let rewritten_body = rewrite_expr_idx(*body, arena, let_unwrap_enabled)?;
            ExpressionDesc::Pexp_while(rewritten_cond, rewritten_body)
        }
        ExpressionDesc::Pexp_for(inner) => {
            let (pat, start, end, dir, body) = &**inner;
            let rewritten_start = rewrite_expr_idx(*start, arena, let_unwrap_enabled)?;
            let rewritten_end = rewrite_expr_idx(*end, arena, let_unwrap_enabled)?;
            let rewritten_body = rewrite_expr_idx(*body, arena, let_unwrap_enabled)?;
            ExpressionDesc::Pexp_for(Box::new((
                *pat,
                rewritten_start,
                rewritten_end,
                *dir,
                rewritten_body,
            )))
        }
        ExpressionDesc::Pexp_for_of(inner) => {
            let (pat, iterable, body) = &**inner;
            let rewritten_iterable = rewrite_expr_idx(*iterable, arena, let_unwrap_enabled)?;
            let rewritten_body = rewrite_expr_idx(*body, arena, let_unwrap_enabled)?;
            ExpressionDesc::Pexp_for_of(Box::new((*pat, rewritten_iterable, rewritten_body)))
        }
        ExpressionDesc::Pexp_for_await_of(inner) => {
            let (pat, iterable, body) = &**inner;
            let rewritten_iterable = rewrite_expr_idx(*iterable, arena, let_unwrap_enabled)?;
            let rewritten_body = rewrite_expr_idx(*body, arena, let_unwrap_enabled)?;
            ExpressionDesc::Pexp_for_await_of(Box::new((*pat, rewritten_iterable, rewritten_body)))
        }
        ExpressionDesc::Pexp_constraint(inner) => {
            let (subject, typ) = &**inner;
            let rewritten_subject = rewrite_expr_idx(*subject, arena, let_unwrap_enabled)?;
            ExpressionDesc::Pexp_constraint(Box::new((rewritten_subject, *typ)))
        }
        ExpressionDesc::Pexp_coerce(inner) => {
            let (subject, from, to) = &**inner;
            let rewritten_subject = rewrite_expr_idx(*subject, arena, let_unwrap_enabled)?;
            ExpressionDesc::Pexp_coerce(Box::new((rewritten_subject, *from, *to)))
        }
        ExpressionDesc::Pexp_object_get(inner) => {
            let (subject, method) = &**inner;
            let rewritten_subject = rewrite_expr_idx(*subject, arena, let_unwrap_enabled)?;
            ExpressionDesc::Pexp_object_get(Box::new((rewritten_subject, method.clone())))
        }
        ExpressionDesc::Pexp_object_set(inner) => {
            let (subject, name, value) = &**inner;
            let rewritten_subject = rewrite_expr_idx(*subject, arena, let_unwrap_enabled)?;
            let rewritten_value = rewrite_expr_idx(*value, arena, let_unwrap_enabled)?;
            ExpressionDesc::Pexp_object_set(Box::new((rewritten_subject, name.clone(), rewritten_value)))
        }
        ExpressionDesc::Pexp_object_literal(fields) => {
            let mut rewritten = Vec::with_capacity(fields.len());
            for (name, value) in fields.iter() {
                rewritten.push((name.clone(), rewrite_expr_idx(*value, arena, let_unwrap_enabled)?));
            }
            ExpressionDesc::Pexp_object_literal(Box::new(rewritten))
        }
        ExpressionDesc::Pexp_letmodule(inner) => {
            let (name, mod_expr, body) = &**inner;
            let rewritten_mod = rewrite_mod_expr_idx(*mod_expr, arena, let_unwrap_enabled)?;
            let rewritten_body = rewrite_expr_idx(*body, arena, let_unwrap_enabled)?;
            ExpressionDesc::Pexp_letmodule(Box::new((name.clone(), rewritten_mod, rewritten_body)))
        }
        ExpressionDesc::Pexp_letexception(inner) => {
            let (ext, body) = &**inner;
            let rewritten_body = rewrite_expr_idx(*body, arena, let_unwrap_enabled)?;
            ExpressionDesc::Pexp_letexception(Box::new((ext.clone(), rewritten_body)))
        }
        ExpressionDesc::Pexp_assert(subject) => {
            let rewritten = rewrite_expr_idx(*subject, arena, let_unwrap_enabled)?;
            ExpressionDesc::Pexp_assert(rewritten)
        }
        ExpressionDesc::Pexp_newtype(inner) => {
            let (name, body) = &**inner;
            let rewritten_body = rewrite_expr_idx(*body, arena, let_unwrap_enabled)?;
            ExpressionDesc::Pexp_newtype(Box::new((name.clone(), rewritten_body)))
        }
        ExpressionDesc::Pexp_pack(mod_expr) => {
            let rewritten_mod = rewrite_mod_expr_idx(*mod_expr, arena, let_unwrap_enabled)?;
            ExpressionDesc::Pexp_pack(rewritten_mod)
        }
        ExpressionDesc::Pexp_open(inner) => {
            let (override_flag, lid, body) = &**inner;
            let rewritten_body = rewrite_expr_idx(*body, arena, let_unwrap_enabled)?;
            ExpressionDesc::Pexp_open(Box::new((*override_flag, *lid, rewritten_body)))
        }
        ExpressionDesc::Pexp_extension(ext) => ExpressionDesc::Pexp_extension(Box::new(
            rewrite_extension(ext, arena, let_unwrap_enabled)?,
        )),
        ExpressionDesc::Pexp_await(subject) => {
            let rewritten = rewrite_expr_idx(*subject, arena, let_unwrap_enabled)?;
            ExpressionDesc::Pexp_await(rewritten)
        }
        ExpressionDesc::Pexp_template(template) => {
            let values = template
                .values
                .iter()
                .map(|idx| rewrite_expr_idx(*idx, arena, let_unwrap_enabled))
                .collect::<Result<Vec<_>, _>>()?;
            ExpressionDesc::Pexp_template(Box::new(crate::parser::ast::PexpTemplate {
                source_segments: template.source_segments.clone(),
                values,
            }))
        }
        ExpressionDesc::Pexp_tagged_template(template) => {
            let tag = rewrite_expr_idx(template.tag, arena, let_unwrap_enabled)?;
            let values = template
                .values
                .iter()
                .map(|idx| rewrite_expr_idx(*idx, arena, let_unwrap_enabled))
                .collect::<Result<Vec<_>, _>>()?;
            ExpressionDesc::Pexp_tagged_template(Box::new(crate::parser::ast::PexpTaggedTemplate {
                tag,
                raw_sources: template.raw_sources.clone(),
                values,
            }))
        }
        ExpressionDesc::Pexp_jsx_element(element) => ExpressionDesc::Pexp_jsx_element(Box::new(
            rewrite_jsx_element(element, arena, let_unwrap_enabled)?,
        )),
        ExpressionDesc::Pexp_inline_for(inner) => {
            let (ref pat, ref collection, ref body) = **inner;
            let new_collection = rewrite_expr_idx(*collection, arena, let_unwrap_enabled)?;
            let new_body = rewrite_expr_idx(*body, arena, let_unwrap_enabled)?;
            ExpressionDesc::Pexp_inline_for(Box::new((*pat, new_collection, new_body)))
        }
        ExpressionDesc::Pexp_comptime_typeinfo(_) | ExpressionDesc::Pexp_comptime_typename(_) => {
            (*expr.pexp_desc).clone()
        }
        ExpressionDesc::Pexp_comptime_field(inner) => {
            let (ref value, ref field) = **inner;
            let new_value = rewrite_expr_idx(*value, arena, let_unwrap_enabled)?;
            let new_field = rewrite_expr_idx(*field, arena, let_unwrap_enabled)?;
            ExpressionDesc::Pexp_comptime_field(Box::new((new_value, new_field)))
        }
        ExpressionDesc::Pexp_comptime_compile_error(expr_idx) => {
            let new_expr = rewrite_expr_idx(*expr_idx, arena, let_unwrap_enabled)?;
            ExpressionDesc::Pexp_comptime_compile_error(new_expr)
        }
        ExpressionDesc::Pexp_comptime_record(inner) => {
            let (ref ct, ref fields_expr) = **inner;
            let new_fields = rewrite_expr_idx(*fields_expr, arena, let_unwrap_enabled)?;
            ExpressionDesc::Pexp_comptime_record(Box::new((*ct, new_fields)))
        }
        ExpressionDesc::Pexp_comptime_variant(inner) => {
            let (ref ct, ref expr_idx, ref opt_expr_idx) = **inner;
            let new_expr = rewrite_expr_idx(*expr_idx, arena, let_unwrap_enabled)?;
            let new_opt = opt_expr_idx
                .map(|e| rewrite_expr_idx(e, arena, let_unwrap_enabled))
                .transpose()?;
            ExpressionDesc::Pexp_comptime_variant(Box::new((*ct, new_expr, new_opt)))
        }
        ExpressionDesc::Pexp_comptime_build_variant(e) => {
            let new_e = rewrite_expr_idx(*e, arena, let_unwrap_enabled)?;
            ExpressionDesc::Pexp_comptime_build_variant(new_e)
        }
        ExpressionDesc::Pexp_comptime_variant_case(e) => {
            let new_e = rewrite_expr_idx(*e, arena, let_unwrap_enabled)?;
            ExpressionDesc::Pexp_comptime_variant_case(new_e)
        }
        ExpressionDesc::Pexp_comptime_build_record(e) => {
            let new_e = rewrite_expr_idx(*e, arena, let_unwrap_enabled)?;
            ExpressionDesc::Pexp_comptime_build_record(new_e)
        }
        ExpressionDesc::Pexp_comptime_record_field(e) => {
            let new_e = rewrite_expr_idx(*e, arena, let_unwrap_enabled)?;
            ExpressionDesc::Pexp_comptime_record_field(new_e)
        }
    };

    Ok(Expression {
        pexp_desc: Box::new(desc),
        pexp_loc: expr.pexp_loc,
        pexp_attributes: expr.pexp_attributes.clone(),
    })
}

fn rewrite_cases(
    cases: &[Case],
    arena: &mut ParseArena,
    let_unwrap_enabled: bool,
) -> Result<Vec<Case>, String> {
    cases
        .iter()
        .map(|case| {
            let rewritten_guard = case
                .pc_guard
                .map(|idx| rewrite_expr_idx(idx, arena, let_unwrap_enabled))
                .transpose()?;
            let rewritten_rhs = rewrite_expr_idx(case.pc_rhs, arena, let_unwrap_enabled)?;
            Ok(Case {
                pc_bar: case.pc_bar,
                pc_lhs: case.pc_lhs,
                pc_guard: rewritten_guard,
                pc_rhs: rewritten_rhs,
            })
        })
        .collect()
}

fn rewrite_let_expression(
    original_expr: &Expression,
    rec_flag: RecFlag,
    bindings: &[ValueBinding],
    body: ExprIdx,
    arena: &mut ParseArena,
    let_unwrap_enabled: bool,
) -> Result<Expression, String> {
    if rec_flag == RecFlag::Nonrecursive && bindings.len() == 1 {
        let vb = &bindings[0];
        if has_let_unwrap_attr(&vb.pvb_attributes, arena) {
            if !let_unwrap_enabled {
                return Err(FEATURE_NOT_ENABLED_MSG.to_string());
            }
            return rewrite_supported_let_unwrap(
                original_expr,
                vb,
                body,
                arena,
                let_unwrap_enabled,
            );
        }
    }

    if bindings
        .iter()
        .any(|vb| has_let_unwrap_attr(&vb.pvb_attributes, arena))
    {
        return if let_unwrap_enabled {
            Err(UNSUPPORTED_TYPE_MSG.to_string())
        } else {
            Err(FEATURE_NOT_ENABLED_MSG.to_string())
        };
    }

    let rewritten_bindings = bindings
        .iter()
        .map(|vb| rewrite_value_binding(vb, arena, let_unwrap_enabled))
        .collect::<Result<Vec<_>, _>>()?;
    let rewritten_body = rewrite_expr_idx(body, arena, let_unwrap_enabled)?;
    Ok(Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_let(Box::new((
            rec_flag,
            rewritten_bindings,
            rewritten_body,
        )))),
        pexp_loc: original_expr.pexp_loc,
        pexp_attributes: original_expr.pexp_attributes.clone(),
    })
}

fn rewrite_supported_let_unwrap(
    original_expr: &Expression,
    vb: &ValueBinding,
    body: ExprIdx,
    arena: &mut ParseArena,
    let_unwrap_enabled: bool,
) -> Result<Expression, String> {
    let pat = arena.get_pat(vb.pvb_pat).clone();
    let kind =
        classify_let_unwrap_pattern(&pat, arena).ok_or_else(|| UNSUPPORTED_TYPE_MSG.to_string())?;

    let source_expr = arena.get_expr(vb.pvb_expr).clone();
    if matches!(&*source_expr.pexp_desc, ExpressionDesc::Pexp_pack(_)) {
        let rewritten_binding = rewrite_value_binding(vb, arena, let_unwrap_enabled)?;
        let rewritten_body = rewrite_expr_idx(body, arena, let_unwrap_enabled)?;
        return Ok(Expression {
            pexp_desc: Box::new(ExpressionDesc::Pexp_let(Box::new((
                RecFlag::Nonrecursive,
                vec![rewritten_binding],
                rewritten_body,
            )))),
            pexp_loc: original_expr.pexp_loc,
            pexp_attributes: original_expr.pexp_attributes.clone(),
        });
    }

    let rewritten_source = rewrite_expression(&source_expr, arena, let_unwrap_enabled)?;
    let rewritten_body_idx = rewrite_expr_idx(body, arena, let_unwrap_enabled)?;
    let rewritten_source_idx = arena.push_expr(rewritten_source);

    let cont_case = Case {
        pc_bar: None,
        pc_lhs: vb.pvb_pat,
        pc_guard: None,
        pc_rhs: rewritten_body_idx,
    };

    let loc = arena.mk_ghost_loc(pat.ppat_loc);
    let alias_name = extract_binding_name(&pat, arena).unwrap_or_else(|| arena.intern_string("x"));
    let early_case = make_let_unwrap_early_case(kind, alias_name, loc, arena);

    let mut attrs = original_expr.pexp_attributes.clone();
    attrs.extend(vb.pvb_attributes.iter().cloned());

    Ok(Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_match(Box::new((
            rewritten_source_idx,
            vec![early_case, cont_case],
        )))),
        pexp_loc: original_expr.pexp_loc,
        pexp_attributes: attrs,
    })
}

fn make_let_unwrap_early_case(
    kind: LetUnwrapKind,
    alias_name: crate::intern::StrIdx,
    loc: crate::parse_arena::LocIdx,
    arena: &mut ParseArena,
) -> Case {
    let (ctor_name, needs_payload) = match kind {
        LetUnwrapKind::ResultOk => ("Error", true),
        LetUnwrapKind::ResultError => ("Ok", true),
        LetUnwrapKind::OptionSome => ("None", false),
        LetUnwrapKind::OptionNone => ("Some", true),
    };

    let ctor_pat = make_ctor_pattern(ctor_name, needs_payload, loc, arena);
    let ctor_pat_idx = arena.push_pat(ctor_pat);
    // OCaml's Ast_helper.Pat.alias (without ~loc) defaults to Location.none
    // The inner Ppat_construct keeps the source loc, but the alias wrapper uses none
    let none_loc = crate::parse_arena::LocIdx::none();
    let alias_pat = Pattern {
        ppat_desc: Box::new(PatternDesc::Ppat_alias(
            ctor_pat_idx,
            Located {
                txt: alias_name,
                loc,
            },
        )),
        ppat_loc: none_loc,
        ppat_attributes: Attributes::new(),
    };
    let alias_pat_idx = arena.push_pat(alias_pat);

    let alias_lid = arena.fresh_lident_from_idx(alias_name);
    let alias_expr = Expression {
        pexp_desc: Box::new(ExpressionDesc::Pexp_ident(Located {
            txt: alias_lid,
            loc,
        })),
        pexp_loc: loc,
        pexp_attributes: Attributes::new(),
    };
    let alias_expr_idx = arena.push_expr(alias_expr);

    Case {
        pc_bar: None,
        pc_lhs: alias_pat_idx,
        pc_guard: None,
        pc_rhs: alias_expr_idx,
    }
}

fn make_ctor_pattern(
    ctor_name: &str,
    with_payload: bool,
    loc: crate::parse_arena::LocIdx,
    arena: &mut ParseArena,
) -> Pattern {
    let ctor_name_idx = arena.intern_string(ctor_name);
    // The constructor is a static literal in bs_builtin_ppx.ml, so OCaml
    // reuses its Longident wrapper each time this rewrite branch runs.
    let ctor_lid_idx = arena.push_lident_from_idx(ctor_name_idx);
    let payload = if with_payload {
        let any_idx = arena.push_pat(Pattern {
            ppat_desc: Box::new(PatternDesc::Ppat_any),
            ppat_loc: loc,
            ppat_attributes: Attributes::new(),
        });
        vec![any_idx]
    } else {
        Vec::new()
    };
    Pattern {
        ppat_desc: Box::new(PatternDesc::Ppat_construct(
            Located {
                txt: ctor_lid_idx,
                loc,
            },
            crate::parser::ast::ctor_args(payload, loc),
        )),
        ppat_loc: loc,
        ppat_attributes: Attributes::new(),
    }
}

fn classify_let_unwrap_pattern(pat: &Pattern, arena: &ParseArena) -> Option<LetUnwrapKind> {
    let PatternDesc::Ppat_construct(lid, arg) = &*pat.ppat_desc else {
        return None;
    };
    let Longident::Lident(name_idx) = arena.get_longident(lid.txt) else {
        return None;
    };
    let name = arena.get_string(*name_idx);

    match (name, !arg.txt.is_empty()) {
        ("Ok", true) => Some(LetUnwrapKind::ResultOk),
        ("Error", true) => Some(LetUnwrapKind::ResultError),
        ("Some", true) => Some(LetUnwrapKind::OptionSome),
        ("None", false) => Some(LetUnwrapKind::OptionNone),
        _ => None,
    }
}

fn extract_binding_name(pat: &Pattern, arena: &ParseArena) -> Option<crate::intern::StrIdx> {
    let PatternDesc::Ppat_construct(_, args) = &*pat.ppat_desc else {
        return None;
    };
    let [inner] = args.txt.as_slice() else {
        return None;
    };
    extract_single_variable_name(*inner, arena)
}

fn extract_single_variable_name(
    pat_idx: PatIdx,
    arena: &ParseArena,
) -> Option<crate::intern::StrIdx> {
    let pat = arena.get_pat(pat_idx);
    match &*pat.ppat_desc {
        PatternDesc::Ppat_var(name) => Some(name.txt),
        PatternDesc::Ppat_constraint(inner) => extract_single_variable_name(inner.0, arena),
        _ => None,
    }
}

fn has_let_unwrap_attr(attrs: &Attributes, arena: &ParseArena) -> bool {
    attrs.iter().any(|attr| attr_is_let_unwrap(attr, arena))
}

fn attr_is_let_unwrap(attr: &Attribute, arena: &ParseArena) -> bool {
    arena.get_string(attr.0.txt) == LET_UNWRAP_ATTR
}

fn rewrite_jsx_element(
    element: &JsxElement,
    arena: &mut ParseArena,
    let_unwrap_enabled: bool,
) -> Result<JsxElement, String> {
    match element {
        JsxElement::Fragment(JsxFragment {
            opening,
            children,
            closing,
        }) => {
            let rewritten_children = children
                .iter()
                .map(|idx| rewrite_expr_idx(*idx, arena, let_unwrap_enabled))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(JsxElement::Fragment(JsxFragment {
                opening: *opening,
                children: rewritten_children,
                closing: *closing,
            }))
        }
        JsxElement::Unary(JsxUnaryElement { tag_name, props }) => {
            Ok(JsxElement::Unary(JsxUnaryElement {
                tag_name: tag_name.clone(),
                props: rewrite_jsx_props(props, arena, let_unwrap_enabled)?,
            }))
        }
        JsxElement::Container(JsxContainerElement {
            tag_name_start,
            opening_end,
            props,
            children,
            closing_tag,
        }) => {
            let rewritten_children = children
                .iter()
                .map(|idx| rewrite_expr_idx(*idx, arena, let_unwrap_enabled))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(JsxElement::Container(JsxContainerElement {
                tag_name_start: tag_name_start.clone(),
                opening_end: *opening_end,
                props: rewrite_jsx_props(props, arena, let_unwrap_enabled)?,
                children: rewritten_children,
                closing_tag: closing_tag.clone(),
            }))
        }
    }
}

fn rewrite_jsx_props(
    props: &[JsxProp],
    arena: &mut ParseArena,
    let_unwrap_enabled: bool,
) -> Result<Vec<JsxProp>, String> {
    props
        .iter()
        .map(|prop| match prop {
            JsxProp::Punning { optional, name } => Ok(JsxProp::Punning {
                optional: *optional,
                name: *name,
            }),
            JsxProp::Value {
                name,
                optional,
                value,
            } => {
                let rewritten_value = rewrite_expr_idx(*value, arena, let_unwrap_enabled)?;
                Ok(JsxProp::Value {
                    name: *name,
                    optional: *optional,
                    value: rewritten_value,
                })
            }
            JsxProp::Spreading { loc, expr } => {
                let rewritten_expr = rewrite_expr_idx(*expr, arena, let_unwrap_enabled)?;
                Ok(JsxProp::Spreading {
                    loc: *loc,
                    expr: rewritten_expr,
                })
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::{Parser, module};

    fn parse_structure(source: &str) -> (crate::parse_arena::ParseArena, Vec<StructureItem>) {
        let mut parser = Parser::new("test.res", source);
        let structure = module::parse_structure(&mut parser);
        assert!(
            !parser.has_errors(),
            "parser errors: {:?}",
            parser.diagnostics()
        );
        (parser.into_arena(), structure)
    }

    #[test]
    fn rewrites_expression_let_unwrap_when_enabled() {
        let source = r#"
let f = x => {
  let? Some(v) = x
  v
}
"#;
        let (mut arena, structure) = parse_structure(source);
        let rewritten =
            rewrite_structure(&structure, &mut arena, true).expect("rewrite should work");

        let StructureItemDesc::Pstr_value(inner) = &*rewritten[0].pstr_desc else {
            panic!("expected value item");
        };
        let (_, bindings) = &**inner;
        let vb = &bindings[0];
        let fun_expr = arena.get_expr(vb.pvb_expr);
        let ExpressionDesc::Pexp_fun(fun) = &*fun_expr.pexp_desc else {
            panic!("expected function expression");
        };
        let body = arena.get_expr(fun.rhs);
        let rewritten_to_match = match &*body.pexp_desc {
            ExpressionDesc::Pexp_match(_) => true,
            ExpressionDesc::Pexp_let(inner) => {
                let (_, _, wrapped_body) = &**inner;
                let wrapped = arena.get_expr(*wrapped_body);
                matches!(&*wrapped.pexp_desc, ExpressionDesc::Pexp_match(_))
            }
            _ => false,
        };
        assert!(
            rewritten_to_match,
            "expected let? to be rewritten into match"
        );
    }

    #[test]
    fn errors_when_feature_is_disabled() {
        let source = r#"
let f = x => {
  let? Some(v) = x
  v
}
"#;
        let (mut arena, structure) = parse_structure(source);
        let err =
            rewrite_structure(&structure, &mut arena, false).expect_err("rewrite should fail");
        assert!(err.contains("Experimental feature not enabled: LetUnwrap"));
    }

    #[test]
    fn errors_for_toplevel_let_unwrap() {
        let source = r#"
let? Some(v) = x
"#;
        let (mut arena, structure) = parse_structure(source);
        let err = rewrite_structure(&structure, &mut arena, true).expect_err("rewrite should fail");
        assert!(err.contains("not allowed for top-level bindings"));
    }
}
