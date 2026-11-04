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

use super::marshal::{EmptyPayloadShareKind, MarshalWriter, PrimListShareKind};
use super::serialize::Marshal;
use crate::parse_arena::LocIdx;
use crate::parser::ast::{
    ArgLabel, Arity, Attribute, Attributes, Case, ClosedFlag, Constant, ConstructorArguments,
    ConstructorDeclaration, ConstructorTag, CoreType, CoreTypeDesc, DirectionFlag, Expression,
    ExpressionDesc, ExpressionRecordField, Extension, ExtensionConstructor,
    ExtensionConstructorKind, FunParam, IncludeDeclaration, IncludeDescription, LabelDeclaration,
    ModuleBinding, ModuleDeclaration, ModuleExpr, ModuleExprDesc, ModuleType,
    ModuleTypeDeclaration, ModuleTypeDesc, MutableFlag, ObjectField, OpenDescription, OverrideFlag,
    Pattern, PatternDesc, PatternRecordField, Payload, PexpApply, PexpFun, PrimitiveRepr,
    PrivateFlag, RecFlag, RecordPatRest, RowField, SignatureItem, SignatureItemDesc, StringConst,
    StringLoc, StructureItem, StructureItemDesc, TypeArg, TypeDeclaration, TypeExtension, TypeKind,
    ValueBinding, ValueConstraint, ValueDescription, Variance, WithConstraint,
};
use crate::parser::longident::Longident;

// ========== Attribute list sharing ==========

fn is_symbolic_operator(name: &str) -> bool {
    name.chars()
        .all(|c| !c.is_ascii_alphanumeric() && c != '_' && c != '.')
}

fn is_pipe_application(expr: &Expression, w: &MarshalWriter<'_>) -> bool {
    let arena = w.get_arena();

    let ExpressionDesc::Pexp_apply(inner) = &expr.pexp_desc else {
        return false;
    };
    let PexpApply { ref funct, .. } = *inner;
    let args = arena.apply_args(inner.args);
    if args.is_empty() || !matches!(args[0].0, ArgLabel::Nolabel) {
        return false;
    }

    if expr
        .pexp_attributes
        .iter()
        .any(|(name, _)| arena.get_string(name.txt) == "res.taggedTemplate")
    {
        return false;
    }
    let funct_expr = arena.get_expr(*funct);
    let funct_loc = arena.get_location(funct_expr.pexp_loc);
    let arg_expr = arena.get_expr(args[0].1);
    let arg_loc = arena.get_location(arg_expr.pexp_loc);
    let funct_start = arena.get_position(funct_loc.loc_start).cnum;
    let arg_start = arena.get_position(arg_loc.loc_start).cnum;
    if funct_start <= arg_start {
        return false;
    }

    let ExpressionDesc::Pexp_ident(lid) = &funct_expr.pexp_desc else {
        return false;
    };
    let name = match arena.get_longident(lid.txt) {
        Longident::Lident(idx) => arena.get_string(*idx),
        Longident::Ldot(_, idx) => arena.get_string(*idx),
        Longident::Lapply(_, arg) => arena.get_string(arg.last_idx()),
    };

    !is_symbolic_operator(name)
}

fn marshal_ptyp_var_desc(name: &str, loc: LocIdx, w: &mut MarshalWriter<'_>) {
    w.write_block_header(0, 1);
    if let Some(source_idx) = w.get_arena().tyvar_source_str(loc) {
        w.write_str_idx(source_idx);
    } else if !is_none_loc_idx(loc, w) {
        w.write_tyvar_name_shared(name, loc);
    } else {
        w.write_str(name);
    }
}

/// Whether any attribute in `attrs` is named one of `names`.
fn has_attr(attrs: &Attributes, w: &MarshalWriter<'_>, names: &[&str]) -> bool {
    let arena = w.get_arena();
    attrs
        .iter()
        .any(|(name, _)| names.contains(&arena.get_string(name.txt)))
}

fn should_share_singleton_attr_list(name: &str) -> bool {
    matches!(
        name,
        "react.component" | "jsx.component" | "react.componentWithProps" | "jsx.componentWithProps"
    // `Typemod_hide.attrs` (compiler/frontend/typemod_hide.ml:26) is one global
    // list that `expand_reverse` puts on every `%%private` local module.
            | "internal.local"
    )
}

fn is_singleton_template_attr(attrs: &Attributes, w: &MarshalWriter<'_>) -> bool {
    let arena = w.get_arena();
    match attrs.as_slice() {
        [(name, payload)]
            if arena.get_string(name.txt) == "res.template"
                && name.loc == LocIdx::default()
                && matches!(payload, Payload::PStr(items) if items.is_empty()) =>
        {
            true
        }
        _ => false,
    }
}

fn is_none_loc_idx(loc: LocIdx, w: &MarshalWriter<'_>) -> bool {
    if loc.is_none() {
        return true;
    }
    let interned = w.get_arena().get_location(loc);
    interned.loc_ghost && interned.loc_start.0 == 0 && interned.loc_end.0 == 0
}

fn is_raw_expansion_expr(expr: &Expression, w: &MarshalWriter<'_>) -> bool {
    let ExpressionDesc::Pexp_letmodule(lm_inner) = &expr.pexp_desc else {
        return false;
    };
    let (ref module_name, ref mod_expr, ref body) = **lm_inner;

    let arena = w.get_arena();
    if arena.get_string(module_name.txt) != "J" {
        return false;
    }

    let mod_expr_ref = arena.get_mod_expr(*mod_expr);
    let ModuleExprDesc::Pmod_structure(items) = &*mod_expr_ref.pmod_desc else {
        return false;
    };
    if items.len() != 1 {
        return false;
    }

    let StructureItemDesc::Pstr_primitive(vd) = &*items[0].pstr_desc else {
        return false;
    };
    if arena.get_string(vd.pval_name.txt) != "unsafe_expr" {
        return false;
    }
    let Some(PrimitiveRepr::PrimName(prim)) = &vd.pval_prim else {
        return false;
    };
    let prim = arena.get_string(*prim);
    if prim != "#raw_expr" && prim != "#raw_stmt" {
        return false;
    }

    let body_expr = arena.get_expr(*body);
    let ExpressionDesc::Pexp_apply(inner) = &body_expr.pexp_desc else {
        return false;
    };
    let PexpApply { ref funct, .. } = *inner;
    let args = arena.apply_args(inner.args);
    if args.len() != 1 || !matches!(args[0].0, ArgLabel::Nolabel) {
        return false;
    }

    let funct_expr = arena.get_expr(*funct);
    let ExpressionDesc::Pexp_ident(lid) = &funct_expr.pexp_desc else {
        return false;
    };
    match arena.get_longident(lid.txt) {
        Longident::Ldot(prefix, idx) => {
            if arena.get_string(*idx) != "unsafe_expr" {
                return false;
            }
            matches!(&**prefix, Longident::Lident(p) if arena.get_string(*p) == "J")
        }
        _ => false,
    }
}

fn is_external_ext_expr(expr: &Expression, w: &MarshalWriter<'_>) -> bool {
    let arena = w.get_arena();

    let ExpressionDesc::Pexp_apply(inner) = &expr.pexp_desc else {
        return false;
    };
    let PexpApply {
        funct: ref outer_funct,
        ..
    } = *inner;
    let outer_args = arena.apply_args(inner.args);
    if outer_args.len() != 1 || !matches!(outer_args[0].0, ArgLabel::Nolabel) {
        return false;
    }
    let outer_funct_expr = arena.get_expr(*outer_funct);
    let ExpressionDesc::Pexp_ident(outer_lid) = &outer_funct_expr.pexp_desc else {
        return false;
    };
    if outer_lid.txt != arena.ppx_js_undefined_to_option_lid() {
        return false;
    }

    let outer_arg_expr = arena.get_expr(outer_args[0].1);
    let ExpressionDesc::Pexp_ifthenelse(ite_inner) = &outer_arg_expr.pexp_desc else {
        return false;
    };
    let (ref cond, ref then_expr, ref opt_else) = **ite_inner;
    let Some(else_expr) = opt_else else {
        return false;
    };
    let else_expr_ref = arena.get_expr(*else_expr);
    if !is_external_raw_expansion_expr(else_expr_ref, w) {
        return false;
    }
    let then_expr_ref = arena.get_expr(*then_expr);
    if !matches!(
        &then_expr_ref.pexp_desc,
        ExpressionDesc::Pexp_ident(then_lid) if then_lid.txt == arena.ppx_js_undefined_empty_lid()
    ) {
        return false;
    }

    let cond_expr = arena.get_expr(*cond);
    let ExpressionDesc::Pexp_apply(eq_inner) = &cond_expr.pexp_desc else {
        return false;
    };
    let PexpApply {
        funct: ref eq_funct,
        ..
    } = *eq_inner;
    let eq_args = arena.apply_args(eq_inner.args);
    if eq_args.len() != 2
        || !matches!(eq_args[0].0, ArgLabel::Nolabel)
        || !matches!(eq_args[1].0, ArgLabel::Nolabel)
    {
        return false;
    }
    let eq_funct_expr = arena.get_expr(*eq_funct);
    if !matches!(
        &eq_funct_expr.pexp_desc,
        ExpressionDesc::Pexp_ident(eq_lid)
            if matches!(arena.get_longident(eq_lid.txt), Longident::Lident(s) if *s == arena.ppx_eq_str())
    ) {
        return false;
    }

    let eq_arg0_expr = arena.get_expr(eq_args[0].1);
    let ExpressionDesc::Pexp_apply(typeof_inner) = &eq_arg0_expr.pexp_desc else {
        return false;
    };
    let PexpApply {
        funct: ref typeof_funct,
        ..
    } = *typeof_inner;
    let typeof_args = arena.apply_args(typeof_inner.args);
    if typeof_args.len() != 1 || !matches!(typeof_args[0].0, ArgLabel::Nolabel) {
        return false;
    }
    let typeof_funct_expr = arena.get_expr(*typeof_funct);
    if !matches!(
        &typeof_funct_expr.pexp_desc,
        ExpressionDesc::Pexp_ident(typeof_lid) if typeof_lid.txt == arena.ppx_js_typeof_lid()
    ) {
        return false;
    }
    let typeof_arg_expr = arena.get_expr(typeof_args[0].1);
    if !is_external_raw_expansion_expr(typeof_arg_expr, w) {
        return false;
    }

    let eq_arg1_expr = arena.get_expr(eq_args[1].1);
    matches!(
        &eq_arg1_expr.pexp_desc,
        ExpressionDesc::Pexp_constant(c) if matches!(&*c, Constant::String(s) if s.semantic(arena) == "undefined")
    )
}

fn is_external_raw_expansion_expr(expr: &Expression, w: &MarshalWriter<'_>) -> bool {
    is_raw_expansion_expr(expr, w) && is_external_raw_expansion_body(expr, w)
}

/// The `%external`-specific half of [`is_external_raw_expansion_expr`], for
/// callers that already know `expr` is a raw expansion.
fn is_external_raw_expansion_body(expr: &Expression, w: &MarshalWriter<'_>) -> bool {
    let ExpressionDesc::Pexp_letmodule(lm_inner) = &expr.pexp_desc else {
        return false;
    };
    let (_, _, ref body) = **lm_inner;
    let body_expr = w.get_arena().get_expr(*body);
    let ExpressionDesc::Pexp_apply(apply_inner) = &body_expr.pexp_desc else {
        return false;
    };
    let args = w.get_arena().apply_args(apply_inner.args);
    if args.len() != 1 || !matches!(args[0].0, ArgLabel::Nolabel) {
        return false;
    }
    let arg_expr = w.get_arena().get_expr(args[0].1);
    matches!(
        &arg_expr.pexp_desc,
        ExpressionDesc::Pexp_constant(c) if matches!(&*c, Constant::RawSource(_))
    )
}

fn should_share_empty_pstr(
    kind: EmptyPayloadShareKind,
    name: &StringLoc,
    w: &MarshalWriter<'_>,
) -> bool {
    if kind != EmptyPayloadShareKind::ParserAttr {
        return true;
    }

    let arena = w.get_arena();
    let name_str = arena.get_string(name.txt);
    if name_str == "res.braces" {
        true
    } else {
        name_str != "res.taggedTemplate"
    }
}

fn is_internal_expansive_attr(name: &StringLoc, payload: &Payload, w: &MarshalWriter<'_>) -> bool {
    matches!(payload, Payload::PStr(items) if items.is_empty())
        && name.loc == LocIdx::default()
        && w.get_arena().get_string(name.txt) == "internal.expansive"
}

fn should_share_attr_tuple(
    name: &StringLoc,
    payload: &Payload,
    share_empty_pstr: Option<EmptyPayloadShareKind>,
    w: &MarshalWriter<'_>,
) -> bool {
    if !matches!(payload, Payload::PStr(items) if items.is_empty()) {
        return false;
    }

    match w.get_arena().get_string(name.txt) {
        "res.await" => true,
        "res.template" => matches!(share_empty_pstr, Some(EmptyPayloadShareKind::ParserAttr)),
        "res.ternary" => matches!(share_empty_pstr, Some(EmptyPayloadShareKind::ParserAttr)),
        _ => false,
    }
}

fn marshal_attribute_payload(
    name: &StringLoc,
    payload: &Payload,
    w: &mut MarshalWriter<'_>,
    share_empty_pstr: Option<EmptyPayloadShareKind>,
) {
    if let Some(kind) = share_empty_pstr {
        if matches!(payload, Payload::PStr(items) if items.is_empty())
            && should_share_empty_pstr(kind, name, w)
        {
            w.write_pstr_empty_shared(kind);
            return;
        }
    }
    payload.marshal(w);
}

fn marshal_attribute_list(
    attrs: &[Attribute],
    w: &mut MarshalWriter<'_>,
    share_empty_pstr: Option<EmptyPayloadShareKind>,
) {
    // In raw expansion contexts, OCaml may build attribute lists by consing onto
    // a shared tail [res.template]. Our recursive marshalling must preserve that
    // tail sharing, not just singleton top-level lists.
    if w.in_raw_expansion() {
        if let [(name, payload)] = attrs {
            let arena = w.get_arena();
            if matches!(payload, Payload::PStr(items) if items.is_empty())
                && name.loc == LocIdx::default()
                && arena.get_string(name.txt) == "res.template"
            {
                if let Some(obj_idx) = w.raw_template_attr_list() {
                    let d = w.obj_counter() - obj_idx;
                    w.write_shared_ref(d);
                    return;
                }

                let obj_idx = w.obj_counter();
                w.set_raw_template_attr_list(obj_idx);
            }
        }
    }

    if let Some((head, tail)) = attrs.split_first() {
        let (name, payload) = head;
        let payload_is_empty = matches!(payload, Payload::PStr(items) if items.is_empty());
        let is_singleton_res_await = tail.is_empty()
            && payload_is_empty
            && w.get_arena().get_string(name.txt) == "res.await";

        // Even when we must serialize a fresh list cell (e.g. inside Pexp_pack),
        // remember the first singleton @res.await list so later non-pack sites can
        // share that exact list object when OCaml does.
        if is_singleton_res_await && !w.in_pack() {
            let key = (name.txt, name.loc);
            if w.singleton_attr_list_table_get(&key).is_none() {
                let list_obj_idx = w.obj_counter();
                w.singleton_attr_list_table_insert(key, list_obj_idx);
            }
        }

        // List cons cell
        w.write_block_header(0, 2);
        if is_internal_expansive_attr(name, payload, w) {
            if let Some(obj_idx) = w.internal_expansive_attr_tuple() {
                let d = w.obj_counter() - obj_idx;
                w.write_shared_ref(d);
            } else {
                let obj_idx = w.obj_counter();
                w.write_block_header(0, 2);
                name.marshal(w);
                marshal_attribute_payload(name, payload, w, share_empty_pstr);
                w.set_internal_expansive_attr_tuple(obj_idx);
            }
        } else {
            let key = (name.txt, name.loc);
            if should_share_attr_tuple(name, payload, share_empty_pstr, w) {
                if let Some(&obj_idx) = w.attr_tuple_table_get(&key) {
                    let d = w.obj_counter() - obj_idx;
                    w.write_shared_ref(d);
                } else {
                    let obj_idx = w.obj_counter();
                    w.write_block_header(0, 2);
                    name.marshal(w);
                    marshal_attribute_payload(name, payload, w, share_empty_pstr);
                    w.attr_tuple_table_insert(key, obj_idx);
                }
            } else {
                // Attribute tuple
                w.write_block_header(0, 2);
                name.marshal(w);
                marshal_attribute_payload(name, payload, w, share_empty_pstr);
            }
        }
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
/// Marshal an attribute list without any parser-specific sharing.
pub fn marshal_attributes_plain(attrs: &Attributes, w: &mut MarshalWriter<'_>) {
    marshal_attributes(attrs, w, false, false, None);
}

fn marshal_attributes(
    attrs: &Attributes,
    w: &mut MarshalWriter<'_>,
    share_singleton: bool,
    share_parser_singleton_attr: bool,
    share_empty_pstr: Option<EmptyPayloadShareKind>,
) {
    let attrs_slice = attrs.as_slice();

    let payload_is_empty_str =
        |payload: &Payload| matches!(payload, Payload::PStr(items) if items.is_empty());

    let mut raw_template_list = false;
    if w.in_raw_expansion() {
        if let [(name, payload)] = attrs_slice {
            if payload_is_empty_str(payload)
                && name.loc == LocIdx::default()
                && w.get_arena().get_string(name.txt) == "res.template"
            {
                raw_template_list = true;
                if let Some(obj_idx) = w.raw_template_attr_list() {
                    let d = w.obj_counter() - obj_idx;
                    w.write_shared_ref(d);
                    return;
                }

                let obj_idx = w.obj_counter();
                w.set_raw_template_attr_list(obj_idx);
            }
        }
    }

    let share_singleton = share_singleton || raw_template_list;
    // In OCaml raw-expression rewrites, `res.template` attributes come from a
    // shared module-level payload (`PStr []`). Keep parser-level empty payload
    // sharing enabled in this scope even when the expression-level caller did
    // not request it explicitly.
    let share_empty_pstr = if raw_template_list && share_empty_pstr.is_none() {
        Some(EmptyPayloadShareKind::ParserAttr)
    } else {
        share_empty_pstr
    };

    // Parser-generated `res.doc` attributes can be threaded through rewritten
    // nodes while preserving the singleton list identity in OCaml.
    if let [(name, payload)] = attrs_slice {
        if w.get_arena().get_string(name.txt) == "res.doc" {
            let key = (name.txt, name.loc);
            if let Some(&obj_idx) = w.singleton_attr_list_table_get(&key) {
                let d = w.obj_counter() - obj_idx;
                w.write_shared_ref(d);
                return;
            }

            let obj_idx = w.obj_counter();
            w.singleton_attr_list_table_insert(key, obj_idx);

            w.write_block_header(0, 2); // cons
            w.write_block_header(0, 2); // attribute tuple
            name.marshal(w);
            marshal_attribute_payload(name, payload, w, share_empty_pstr);
            w.write_int(0); // []
            return;
        }
    }

    // Some JSX transforms keep reusing the exact singleton attribute list object
    // (not just the tuple inside), notably for `@react.component` annotations.
    // Mirror that by sharing the whole `[attr]` list cell for those names.
    if let [(name, payload)] = attrs_slice {
        if payload_is_empty_str(payload) {
            let name_str = w.get_arena().get_string(name.txt);
            // In await rewrites, OCaml shares singleton [@res.await] lists across
            // record-update/module-typeof paths, but keeps fresh lists inside
            // `Pexp_pack` (List.filter creates new cons cells there).
            let share_res_await_list = name_str == "res.await" && !w.in_pack();
            if should_share_singleton_attr_list(name_str)
                || share_res_await_list
                || (share_parser_singleton_attr && matches!(name_str, "res.braces" | "res.ternary"))
            {
                let key = (name.txt, name.loc);
                if let Some(&obj_idx) = w.singleton_attr_list_table_get(&key) {
                    let d = w.obj_counter() - obj_idx;
                    w.write_shared_ref(d);
                    return;
                }

                let obj_idx = w.obj_counter();
                w.singleton_attr_list_table_insert(key, obj_idx);

                w.write_block_header(0, 2); // cons
                if share_res_await_list {
                    // OCaml can keep list cells fresh while reusing the inner
                    // tuple object between pack-filtered and outer attrs.
                    if let Some(&tuple_obj_idx) = w.attr_tuple_table_get(&key) {
                        let d = w.obj_counter() - tuple_obj_idx;
                        w.write_shared_ref(d);
                    } else {
                        let tuple_obj_idx = w.obj_counter();
                        w.write_block_header(0, 2); // attribute tuple
                        name.marshal(w);
                        marshal_attribute_payload(name, payload, w, share_empty_pstr);
                        w.attr_tuple_table_insert(key, tuple_obj_idx);
                    }
                } else {
                    w.write_block_header(0, 2); // attribute tuple
                    name.marshal(w);
                    marshal_attribute_payload(name, payload, w, share_empty_pstr);
                }
                w.write_int(0); // []
                return;
            }
        }
    }

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
            if payload_is_empty_str(payload) && is_none_loc_idx(name.loc, w) {
                let key = (name.txt, name.loc);

                // Write the cons cell (list with one element): Block(tag=0, size=2) [tuple, nil]
                // OCaml cons cells use tag=0. The cons cell is always fresh.
                w.write_block_header(0, 2);

                // Check if we've seen this attribute tuple before
                let share_attr_tuple = should_share_attr_tuple(name, payload, share_empty_pstr, w);
                if let Some(&obj_idx) = w.singleton_attr_list_table_get(&key) {
                    let d = w.obj_counter() - obj_idx;
                    w.write_shared_ref(d);
                } else if share_attr_tuple && w.get_arena().get_string(name.txt) == "res.template" {
                    // Some parser rewrites first materialize `res.template` via the
                    // generic attribute path (tracked in `attr_tuple_table`) and later
                    // hit this singleton fast path. Reuse that earlier tuple to match
                    // OCaml's pointer identity instead of creating a fresh equivalent.
                    if let Some(&obj_idx) = w.attr_tuple_table_get(&key) {
                        let d = w.obj_counter() - obj_idx;
                        w.write_shared_ref(d);
                        w.singleton_attr_list_table_insert(key, obj_idx);
                    } else {
                        // Record the object index for the tuple
                        let obj_idx = w.obj_counter();

                        // Write the attribute tuple: Block(tag=0, size=2) [name, payload]
                        w.write_block_header(0, 2);
                        name.marshal(w);
                        marshal_attribute_payload(name, payload, w, share_empty_pstr);

                        w.singleton_attr_list_table_insert(key, obj_idx);
                        w.attr_tuple_table_insert(key, obj_idx);
                    }
                } else {
                    // Record the object index for the tuple
                    let obj_idx = w.obj_counter();

                    // Write the attribute tuple: Block(tag=0, size=2) [name, payload]
                    w.write_block_header(0, 2);
                    name.marshal(w);
                    marshal_attribute_payload(name, payload, w, share_empty_pstr);

                    w.singleton_attr_list_table_insert(key, obj_idx);
                    if share_attr_tuple {
                        w.attr_tuple_table_insert(key, obj_idx);
                    }
                }

                // Write nil (end of list)
                w.write_int(0);
                return;
            }
        }
    }

    // Default: marshal normally (with optional payload sharing)
    marshal_attribute_list(attrs_slice, w, share_empty_pstr);
}

fn marshal_extension(
    ext: &Extension,
    w: &mut MarshalWriter<'_>,
    share_empty_pstr: Option<EmptyPayloadShareKind>,
) {
    let (name, payload) = ext;
    w.write_block_header(0, 2);
    name.marshal(w);
    marshal_attribute_payload(name, payload, w, share_empty_pstr);
}

// ========== Flag implementations ==========

impl Marshal for RecFlag {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        w.write_int(match self {
            RecFlag::Nonrecursive => 0,
            RecFlag::Recursive => 1,
        });
    }
}

impl Marshal for DirectionFlag {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        w.write_int(match self {
            DirectionFlag::Upto => 0,
            DirectionFlag::Downto => 1,
        });
    }
}

impl Marshal for PrivateFlag {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        w.write_int(match self {
            PrivateFlag::Private => 0,
            PrivateFlag::Public => 1,
        });
    }
}

impl Marshal for MutableFlag {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        w.write_int(match self {
            MutableFlag::Immutable => 0,
            MutableFlag::Mutable => 1,
        });
    }
}

impl Marshal for OverrideFlag {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        w.write_int(match self {
            OverrideFlag::Override => 0,
            OverrideFlag::Fresh => 1,
        });
    }
}

impl Marshal for ClosedFlag {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        w.write_int(match self {
            ClosedFlag::Closed => 0,
            ClosedFlag::Open => 1,
        });
    }
}

impl Marshal for Variance {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        w.write_int(match self {
            Variance::Covariant => 0,
            Variance::Contravariant => 1,
            Variance::Invariant => 2,
        });
    }
}

// ========== ArgLabel (with location for Labelled/Optional) ==========

impl Marshal for ArgLabel {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        // In current parsetree, arg_label uses Located<String> for Labelled/Optional
        // But in Rust AST we have just String. For now, output without location.
        // OCaml's Asttypes.arg_label:
        // - Nolabel: int 0
        // - Labelled of string loc: block(tag=0, size=1) containing the string loc
        // - Optional of string loc: block(tag=1, size=1) containing the string loc
        match self {
            ArgLabel::Nolabel => w.write_int(0),
            ArgLabel::Labelled(s) => {
                let key = (0u8, s.txt, s.loc);
                if let Some(&obj_idx) = w.arg_label_table_get(&key) {
                    let d = w.obj_counter() - obj_idx;
                    w.write_shared_ref(d);
                    return;
                }
                let obj_idx = w.obj_counter();
                // Labelled has a string loc, which is a record {txt; loc}
                w.write_block_header(0, 1);
                // Register for sharing: in OCaml's %obj PPX, the same {txt; loc}
                // record is shared between Labelled args and Otag labels. Since
                // Labelled is serialized before Otag in the arrow type, it must
                // register so Otag can share it. This is safe because different
                // parameters always have different (StrIdx, LocIdx) keys.
                w.write_string_loc_shared(s.txt, s.loc, true);
                w.arg_label_table_insert(key, obj_idx);
            }
            ArgLabel::Optional(s) => {
                let key = (1u8, s.txt, s.loc);
                if let Some(&obj_idx) = w.arg_label_table_get(&key) {
                    let d = w.obj_counter() - obj_idx;
                    w.write_shared_ref(d);
                    return;
                }
                let obj_idx = w.obj_counter();
                w.write_block_header(1, 1);
                w.write_string_loc_shared(s.txt, s.loc, true);
                w.arg_label_table_insert(key, obj_idx);
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
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        // Arity is ArityIdx - use the arena-based sharing method
        w.write_arity_idx(*self);
    }
}

// Note: Position, Location, Located<T>, and Longident implementations
// are in types.rs - don't duplicate them here.

// ========== Constant ==========

/// `String_literal.payload`: `Valid {source; semantic}` is tag 0, and
/// `Invalid_source of string` is tag 1.
fn marshal_string_literal(
    payload: &crate::string_literal::StringLiteral,
    w: &mut MarshalWriter<'_>,
) {
    match payload {
        crate::string_literal::StringLiteral::Valid { source, semantic } => {
            w.write_block_header(0, 2);
            w.write_str(source);
            w.write_str(semantic);
        }
        crate::string_literal::StringLiteral::InvalidSource(source) => {
            w.write_block_header(1, 1);
            w.write_str(source);
        }
    }
}

/// `String_literal.payload` of an interned literal, written by content.
fn marshal_string_const(payload: StringConst, w: &mut MarshalWriter<'_>) {
    let arena = w.get_arena();
    match payload {
        StringConst::Valid { source, semantic } => {
            w.write_block_header(0, 2);
            w.write_str(arena.get_string(source));
            w.write_str(arena.get_string(semantic));
        }
        StringConst::InvalidSource(source) => {
            w.write_block_header(1, 1);
            w.write_str(arena.get_string(source));
        }
    }
}

impl Marshal for Constant {
    /// Constant strings are written by content, never as shared references:
    /// each OCaml constant owns its string, and the arena may intern equal
    /// constant spellings to one `StrIdx`.
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        let arena = w.get_arena();
        match *self {
            Constant::Integer(s, suffix) => {
                w.write_block_header(0, 2);
                w.write_str(arena.get_string(s));
                suffix.marshal(w);
            }
            Constant::Char { source, semantic } => {
                // Pconst_char {source; semantic}: inline record, tag 1.
                w.write_block_header(1, 2);
                w.write_str(arena.get_string(source));
                w.write_int(semantic as i64);
            }
            Constant::String(payload) => {
                // Pconst_string of String_literal.payload, tag 2.
                w.write_block_header(2, 1);
                marshal_string_const(payload, w);
            }
            Constant::Json(source) => {
                w.write_block_header(3, 1);
                w.write_str(arena.get_string(source));
            }
            Constant::RawSource(source) => {
                w.write_block_header(4, 1);
                w.write_str(arena.get_string(source));
            }
            Constant::Float(s, suffix) => {
                w.write_block_header(5, 2);
                w.write_str(arena.get_string(s));
                suffix.marshal(w);
            }
        }
    }
}

// Note: Option<T>, Vec<T>, and tuple implementations are in serialize.rs - don't duplicate them here.

// ========== TypeArg (arg record in current parsetree) ==========

impl Marshal for TypeArg {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        // arg = { attrs: attributes; lbl: arg_label; typ: core_type }
        w.write_block_header(0, 3);
        // In parser-generated ES6 arrow type args, empty attribute payloads
        // (`[@attr]` -> `PStr []`) reuse a shared payload object in OCaml.
        // Restrict sharing to parser-shaped attrs (real, non-ghost locations)
        // to avoid over-sharing in PPX-generated paths.
        let share_parser_attr_payloads = !self.attrs.is_empty()
            && self.attrs.iter().all(|(name, payload)| {
                matches!(payload, Payload::PStr(items) if items.is_empty())
                    && name.loc != LocIdx::default()
                    && !w.get_arena().get_location(name.loc).loc_ghost
            });
        if share_parser_attr_payloads {
            marshal_attributes(
                &self.attrs,
                w,
                false,
                false,
                Some(EmptyPayloadShareKind::ParserAttr),
            );
        } else {
            self.attrs.marshal(w);
        }
        self.lbl.marshal(w);
        self.typ.marshal(w);
    }
}

// ========== FunParam (fun_param record in current parsetree) ==========

impl Marshal for FunParam {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        // fun_param = { p_attrs: attributes; p_lbl: arg_label;
        //               p_default: expression option; p_pat: pattern }
        w.write_block_header(0, 4);
        self.p_attrs.marshal(w);
        self.p_lbl.marshal(w);
        self.p_default.marshal(w);
        self.p_pat.marshal(w);
    }
}

// ========== Core Types ==========

impl Marshal for CoreType {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        let share_empty_pstr = match &self.ptyp_desc {
            CoreTypeDesc::Ptyp_object(_) => Some(EmptyPayloadShareKind::ObjectTypeAttr),
            _ => None,
        };

        // OCaml's Ast_literal.No_loc simple core_types are module-level constants.
        // Share only those dedicated lidents to avoid value-based over-sharing.
        if let CoreTypeDesc::Ptyp_constr(inner) = &self.ptyp_desc {
            let (ref lid, ref types) = *inner;
            let should_share_simple_type = self.ptyp_attributes.is_empty()
                && types.is_empty()
                && is_none_loc_idx(self.ptyp_loc, w)
                && is_none_loc_idx(lid.loc, w)
                && w.get_arena().is_ast_literal_simple_type_lident(lid.txt);

            if should_share_simple_type {
                if let Some(&obj_idx) = w.simple_core_type_table_get(&lid.txt) {
                    let d = w.obj_counter() - obj_idx;
                    w.write_shared_ref(d);
                    return;
                }

                let obj_idx = w.obj_counter();
                w.write_block_header(0, 3);
                self.ptyp_desc.marshal(w);
                self.ptyp_loc.marshal(w);
                marshal_attributes(&self.ptyp_attributes, w, false, false, share_empty_pstr);
                w.simple_core_type_table_insert(lid.txt, obj_idx);
                return;
            }
        }

        // Share Ptyp_var core_types with empty attributes and matching (name, loc).
        // In OCaml's from_labels (handle_obj), the same tyvar CoreType is physically
        // shared between Otag fields and Labelled args. The first write creates the
        // object, subsequent writes with the same (name, loc) emit shared references.
        if let CoreTypeDesc::Ptyp_var(name) = &self.ptyp_desc {
            // Most located tyvars are rebuilt as fresh nodes in OCaml and should not
            // be globally shared by value. Keep sharing narrow, but allow it in
            // letmodule/module_typeof scopes where OCaml reuses tyvar core_types in
            // primitive-wrapper rewrites.
            let allow_tyvar_share =
                is_none_loc_idx(self.ptyp_loc, w) || w.in_letmodule_expr() || w.in_module_typeof();
            if self.ptyp_attributes.is_empty() && allow_tyvar_share {
                if let Some(obj_idx) = w.tyvar_core_type_table_get(name, self.ptyp_loc) {
                    let d = w.obj_counter() - obj_idx;
                    w.write_shared_ref(d);
                    return;
                }
                // First occurrence: record the object index, then write normally
                let obj_idx = w.obj_counter();
                // core_type = { ptyp_desc; ptyp_loc; ptyp_attributes }
                w.write_block_header(0, 3);
                marshal_ptyp_var_desc(name, self.ptyp_loc, w);
                self.ptyp_loc.marshal(w);
                marshal_attributes(&self.ptyp_attributes, w, false, false, share_empty_pstr);
                w.tyvar_core_type_table_insert(name, self.ptyp_loc, obj_idx);
                return;
            }
        }

        if let CoreTypeDesc::Ptyp_var(name) = &self.ptyp_desc {
            w.write_block_header(0, 3);
            marshal_ptyp_var_desc(name, self.ptyp_loc, w);
            self.ptyp_loc.marshal(w);
            marshal_attributes(&self.ptyp_attributes, w, false, false, share_empty_pstr);
            return;
        }

        // core_type = { ptyp_desc; ptyp_loc; ptyp_attributes }
        w.write_block_header(0, 3);
        self.ptyp_desc.marshal(w);
        self.ptyp_loc.marshal(w);
        marshal_attributes(&self.ptyp_attributes, w, false, false, share_empty_pstr);
    }
}

impl Marshal for CoreTypeDesc {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
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
            CoreTypeDesc::Ptyp_arrow(inner) => {
                let (arg, ret, arity) = &**inner;
                // Ptyp_arrow of { params: arg list; ret: core_type }
                // Inline record is encoded as block with 2 fields
                let params = w.get_arena().nary_arrow_args(arg, *arity).into_owned();
                w.write_block_header(1, 2);
                params.marshal(w);
                ret.marshal(w);
            }
            CoreTypeDesc::Ptyp_tuple(types) => {
                w.write_block_header(2, 1);
                types.marshal(w);
            }
            CoreTypeDesc::Ptyp_constr(inner) => {
                let (ref lid, ref types) = *inner;
                w.write_block_header(3, 2);
                lid.marshal(w);
                types.marshal(w);
            }
            CoreTypeDesc::Ptyp_object(inner) => {
                let (ref fields, ref flag) = **inner;
                w.write_block_header(4, 2);
                fields.marshal(w);
                flag.marshal(w);
            }
            CoreTypeDesc::Ptyp_alias(inner) => {
                let (ref ty, ref s) = **inner;
                w.write_block_header(5, 2);
                ty.marshal(w);
                w.write_str(s);
            }
            CoreTypeDesc::Ptyp_variant(inner) => {
                let (ref rows, ref flag, ref labels) = **inner;
                w.write_block_header(6, 3);
                rows.marshal(w);
                flag.marshal(w);
                labels.marshal(w);
            }
            CoreTypeDesc::Ptyp_poly(inner) => {
                let (ref vars, ref ty) = **inner;
                w.write_block_header(7, 2);
                vars.marshal(w);
                ty.marshal(w);
            }
            CoreTypeDesc::Ptyp_package(pkg) => {
                w.write_block_header(8, 1);
                // In await-letmodule rewrites, OCaml reuses the same `Longident.t loc`
                // node between `Pmty_ident` and the generated package constraint.
                // Keep this narrowly scoped to the pack-inside-letmodule path.
                let (ref lid, ref constraints) = **pkg;
                w.write_block_header(0, 2);
                if w.in_letmodule_expr() {
                    w.write_lident_loc_shared(lid.txt, lid.loc);
                } else {
                    lid.marshal(w);
                }
                constraints.marshal(w);
            }
            CoreTypeDesc::Ptyp_extension(ext) => {
                w.write_block_header(9, 1);
                ext.marshal(w);
            }
        }
    }
}

impl Marshal for RowField {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
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
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
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
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        w.write_block_header(0, 3);
        if let PatternDesc::Ppat_record(inner) = &self.ppat_desc {
            let (fields, flag, rest) = &**inner;
            w.write_block_header(7, 3);
            fields.marshal(w);
            flag.marshal(w);
            rest.marshal(w);
        } else {
            self.ppat_desc.marshal(w);
        }
        let mut wrote_shared_ppat_loc = false;
        if let PatternDesc::Ppat_var(name) = &self.ppat_desc {
            if name.loc != self.ppat_loc {
                let arena = w.get_arena();
                if arena.get_location(name.loc) == arena.get_location(self.ppat_loc) {
                    if let Some(&obj_idx) = w.location_idx_table_get(&name.loc) {
                        let d = w.obj_counter() - obj_idx;
                        w.write_shared_ref(d);
                        wrote_shared_ppat_loc = true;
                    }
                }
            }
        }
        if !wrote_shared_ppat_loc {
            self.ppat_loc.marshal(w);
        }
        let share_singleton = is_singleton_template_attr(&self.ppat_attributes, w);
        marshal_attributes(&self.ppat_attributes, w, share_singleton, false, None);
    }
}

impl Marshal for PatternDesc {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
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
            PatternDesc::Ppat_interval(inner) => {
                let (ref c1, ref c2) = **inner;
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
            PatternDesc::Ppat_variant(inner) => {
                let (ref label, ref pat) = **inner;
                w.write_block_header(6, 2);
                w.write_str(label);
                pat.marshal(w);
            }
            PatternDesc::Ppat_record(inner) => {
                let (ref fields, ref flag, ref rest) = **inner;
                w.write_block_header(7, 3);
                fields.marshal(w);
                flag.marshal(w);
                rest.marshal(w);
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
            PatternDesc::Ppat_constraint(inner) => {
                let (ref p, ref t) = **inner;
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
        }
    }
}

// ========== Record Field Types ==========

impl Marshal for RecordPatRest {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        // record_pat_rest = {rest_loc; rest_name; rest_type}
        w.write_block_header(0, 3);
        self.rest_loc.marshal(w);
        self.rest_name.marshal(w);
        self.rest_type.marshal(w);
    }
}

impl Marshal for PatternRecordField {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        // record_element = { lid: Longident.t loc; x: 'a; opt: bool }
        w.write_block_header(0, 3);
        self.lid.marshal(w);
        self.pat.marshal(w);
        w.write_int(if self.opt { 1 } else { 0 });
    }
}

impl Marshal for ExpressionRecordField {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        // record_element = { lid: Longident.t loc; x: 'a; opt: bool }
        w.write_block_header(0, 3);
        self.lid.marshal(w);
        self.expr.marshal(w);
        w.write_int(if self.opt { 1 } else { 0 });
    }
}

// ========== Expressions ==========

impl Marshal for Expression {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        let is_raw_expansion = is_raw_expansion_expr(self, w);
        let is_external_raw_expansion =
            w.in_external_ext() && is_raw_expansion && is_external_raw_expansion_body(self, w);
        let is_external_ext = is_external_ext_expr(self, w);
        if is_external_raw_expansion {
            if let Some(obj_idx) = w.raw_expansion_expr(self.pexp_loc) {
                let d = w.obj_counter() - obj_idx;
                w.write_shared_ref(d);
                return;
            }
        }

        w.write_block_header(0, 3);
        if is_external_raw_expansion {
            w.set_raw_expansion_expr(self.pexp_loc, w.obj_counter() - 1);
        }
        let is_extension = matches!(self.pexp_desc, ExpressionDesc::Pexp_extension(_));
        if is_extension {
            w.enter_extension();
        }
        if is_external_ext {
            w.enter_external_ext();
        }
        if is_raw_expansion {
            w.enter_raw_expansion();
        }
        self.pexp_desc.marshal(w);
        self.pexp_loc.marshal(w);

        // In OCaml's PPX, certain expression types return early from expr_mapper
        // without going through the default mapper's attribute remapping. These
        // expressions preserve their original attribute tuples, enabling marshal
        // sharing of singleton `(mknoloc name, PStr [])` module-level constants.
        //
        // Early-return expression types (preserve attribute tuple pointers):
        // - Pexp_constant(Pconst_integer(_, Some _)): int suffix stripping
        // - Pexp_extension: unknown extensions return unchanged
        // - Pexp_newtype: preserves attrs in record-with update
        //
        // Note: Pexp_constant(String(_, None)) and Pexp_letmodule are NOT included.
        // While PPX-created instances preserve attrs, user code instances go through
        // the default mapper which creates fresh tuples.
        let share_attrs = matches!(
            &self.pexp_desc,
            ExpressionDesc::Pexp_constant(c) if matches!(&*c, Constant::Integer(_, Some(_)))
        ) || matches!(
            &self.pexp_desc,
            ExpressionDesc::Pexp_extension(_) | ExpressionDesc::Pexp_newtype(_)
        );
        let has_braces_or_ternary =
            has_attr(&self.pexp_attributes, w, &["res.braces", "res.ternary"]);
        let rewritten_await_letmodule = matches!(
            &self.pexp_desc,
            ExpressionDesc::Pexp_letmodule(inner) if has_attr(&w.get_arena().get_mod_expr((**inner).1).pmod_attributes, w, &["res.await"])
        );
        let rewritten_expr = w.get_arena().is_rewritten_expr_loc(self.pexp_loc);
        let share_singleton_attr_tuple = share_attrs;
        let suppress_rewritten_braces = rewritten_expr
            && has_braces_or_ternary
            && !w.in_extension()
            && !rewritten_await_letmodule;
        let share_empty_pstr = if !suppress_rewritten_braces
            && (is_pipe_application(self, w)
                || share_attrs
                || (has_braces_or_ternary && !w.in_pack())
                || (w.in_extension() && has_braces_or_ternary)
                || (rewritten_await_letmodule && has_braces_or_ternary))
        {
            Some(EmptyPayloadShareKind::ParserAttr)
        } else {
            None
        };
        marshal_attributes(
            &self.pexp_attributes,
            w,
            share_singleton_attr_tuple,
            matches!(&self.pexp_desc, ExpressionDesc::Pexp_open(_)),
            share_empty_pstr,
        );
        if is_raw_expansion {
            w.exit_raw_expansion();
        }
        if is_external_ext {
            w.exit_external_ext();
        }
        if is_extension {
            w.exit_extension();
        }
    }
}

impl Marshal for ExpressionDesc {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        // Expression_desc variants - count only non-constant constructors:
        // Pexp_braces = tag 0
        // Pexp_ident = tag 1
        // Pexp_constant = tag 2
        // Pexp_let = tag 3
        // Pexp_fun = tag 4
        // Pexp_apply = tag 5
        // Pexp_match = tag 6
        // Pexp_try = tag 7
        // Pexp_tuple = tag 8
        // Pexp_construct = tag 9
        // Pexp_variant = tag 10
        // Pexp_record = tag 11
        // Pexp_field = tag 12
        // Pexp_setfield = tag 13
        // Pexp_array = tag 14
        // Pexp_ifthenelse = tag 15
        // Pexp_ternary = tag 16
        // Pexp_sequence = tag 17
        // Pexp_while = tag 18
        // Pexp_for = tag 19
        // Pexp_constraint = tag 20
        // Pexp_coerce = tag 21
        // Pexp_object_get = tag 22
        // Pexp_object_set = tag 23
        // Pexp_object_literal = tag 24
        // Pexp_letmodule = tag 25
        // Pexp_letexception = tag 26
        // Pexp_assert = tag 27
        // Pexp_pack = tag 28
        // Pexp_open = tag 29
        // Pexp_extension = tag 30
        // Pexp_await = tag 31
        // Pexp_jsx_element = tag 32
        // Pexp_for_of = tag 33
        // Pexp_for_await_of = tag 34
        // Pexp_regexp = tag 35
        // Pexp_template = tag 36
        // Pexp_tagged_template = tag 37
        // Constant constructors (no payload):
        // Pexp_break = int 0
        // Pexp_continue = int 1
        match self {
            ExpressionDesc::Pexp_break => w.write_int(0),
            ExpressionDesc::Pexp_continue => w.write_int(1),
            ExpressionDesc::Pexp_braces(braces) => {
                w.write_block_header(0, 2);
                braces.expr.marshal(w);
                braces.braces_loc.marshal(w);
            }
            ExpressionDesc::Pexp_ternary(inner) => {
                w.write_block_header(16, 3);
                inner.0.marshal(w);
                inner.1.marshal(w);
                inner.2.marshal(w);
            }
            ExpressionDesc::Pexp_regexp(regexp) => {
                w.write_block_header(35, 2);
                w.write_str(&regexp.pattern);
                w.write_str(&regexp.flags);
            }
            ExpressionDesc::Pexp_ident(lid) => {
                w.write_block_header(1, 1);
                lid.marshal(w);
            }
            ExpressionDesc::Pexp_constant(c) => {
                w.write_block_header(2, 1);
                c.marshal(w);
            }
            ExpressionDesc::Pexp_let(inner) => {
                let (ref flag, ref bindings, ref body) = **inner;
                w.write_block_header(3, 3);
                flag.marshal(w);
                bindings.marshal(w);
                body.marshal(w);
            }
            ExpressionDesc::Pexp_fun(inner) => {
                let PexpFun {
                    ref arg_label,
                    ref default,
                    ref lhs,
                    ref rhs,
                    ref arity,
                    ref is_async,
                } = **inner;
                let params = w.get_arena().nary_fun_params(inner).into_owned();
                let newtypes = w.get_arena().nary_fun_newtypes(inner).to_vec();
                let body = w.get_arena().nary_fun_body(inner);
                // Pexp_fun of { newtypes; params; body; async }
                // Inline record with 4 fields
                w.write_block_header(4, 4);
                // OCaml serializes each newtype as a tuple
                // `(string loc * attributes)`; lists are cons cells.
                if newtypes.is_empty() {
                    w.write_int(0);
                } else {
                    for (i, (name, attrs)) in newtypes.iter().enumerate() {
                        w.write_block_header(0, 2);
                        w.write_block_header(0, 2);
                        name.marshal(w);
                        attrs.marshal(w);
                        if i == newtypes.len() - 1 {
                            w.write_int(0);
                        }
                    }
                }
                params.marshal(w);
                body.marshal(w);
                w.write_int(if *is_async { 1 } else { 0 });
                let _ = (arg_label, lhs, rhs, default, arity);
            }
            ExpressionDesc::Pexp_apply(inner) => {
                let PexpApply {
                    ref funct,
                    ref partial,
                    ref transformed_jsx,
                    ..
                } = *inner;
                let args = w.get_arena().apply_args(inner.args).to_vec();
                // Pexp_apply of { funct; args; partial; transformed_jsx }
                // Inline record with 4 fields
                w.write_block_header(5, 4);
                funct.marshal(w);
                args.marshal(w);
                w.write_int(if *partial { 1 } else { 0 });
                w.write_int(if *transformed_jsx { 1 } else { 0 });
            }
            ExpressionDesc::Pexp_match(inner) => {
                let (ref e, ref cases) = **inner;
                w.write_block_header(6, 2);
                e.marshal(w);
                if let Some(owner) = w.current_expr_idx() {
                    w.enter_case_owner(owner);
                    cases.marshal(w);
                    w.exit_case_owner();
                } else {
                    cases.marshal(w);
                }
            }
            ExpressionDesc::Pexp_try(inner) => {
                let (ref e, ref cases) = **inner;
                w.write_block_header(7, 2);
                e.marshal(w);
                if let Some(owner) = w.current_expr_idx() {
                    w.enter_case_owner(owner);
                    cases.marshal(w);
                    w.exit_case_owner();
                } else {
                    cases.marshal(w);
                }
            }
            ExpressionDesc::Pexp_tuple(exprs) => {
                w.write_block_header(8, 1);
                exprs.marshal(w);
            }
            ExpressionDesc::Pexp_construct(lid, args) => {
                w.write_block_header(9, 2);
                lid.marshal(w);
                args.marshal(w);
            }
            ExpressionDesc::Pexp_variant(inner) => {
                let (ref label, ref args) = **inner;
                w.write_block_header(10, 2);
                w.write_str(label);
                args.marshal(w);
            }
            ExpressionDesc::Pexp_record(inner) => {
                let (ref fields, ref spread) = **inner;
                let spread_idx = w
                    .current_expr_idx()
                    .and_then(|owner| w.get_arena().record_spread(owner))
                    .or(*spread);
                w.write_block_header(11, 2);
                fields.marshal(w);
                spread_idx.marshal(w);
            }
            ExpressionDesc::Pexp_field(e, lid) => {
                w.write_block_header(12, 2);
                e.marshal(w);
                lid.marshal(w);
            }
            ExpressionDesc::Pexp_setfield(inner) => {
                let (ref e1, ref lid, ref e2) = **inner;
                w.write_block_header(13, 3);
                e1.marshal(w);
                lid.marshal(w);
                e2.marshal(w);
            }
            ExpressionDesc::Pexp_array(exprs) => {
                w.write_block_header(14, 1);
                exprs.marshal(w);
            }
            ExpressionDesc::Pexp_ifthenelse(inner) => {
                let (ref e1, ref e2, ref e3) = **inner;
                let else_idx = w
                    .current_expr_idx()
                    .and_then(|owner| w.get_arena().if_else_branch(owner))
                    .or(*e3);
                w.write_block_header(15, 3);
                e1.marshal(w);
                e2.marshal(w);
                else_idx.marshal(w);
            }
            ExpressionDesc::Pexp_sequence(e1, e2) => {
                w.write_block_header(17, 2);
                e1.marshal(w);
                e2.marshal(w);
            }
            ExpressionDesc::Pexp_while(e1, e2) => {
                w.write_block_header(18, 2);
                e1.marshal(w);
                e2.marshal(w);
            }
            ExpressionDesc::Pexp_for(inner) => {
                let (ref pat, ref e1, ref e2, ref dir, ref e3) = **inner;
                w.write_block_header(19, 5);
                pat.marshal(w);
                e1.marshal(w);
                e2.marshal(w);
                dir.marshal(w);
                e3.marshal(w);
            }
            ExpressionDesc::Pexp_constraint(inner) => {
                let (ref e, ref t) = **inner;
                w.write_block_header(20, 2);
                e.marshal(w);
                t.marshal(w);
            }
            ExpressionDesc::Pexp_coerce(inner) => {
                let (ref e, ref _middle, ref t) = **inner;
                let _from_type = w
                    .current_expr_idx()
                    .and_then(|owner| w.get_arena().coerce_from_type(owner));
                // Pexp_coerce of expression * unit * core_type
                // The middle field in Rust is Option<CoreType> but OCaml uses unit
                w.write_block_header(21, 3);
                e.marshal(w);
                w.write_int(0); // unit = ()
                t.marshal(w);
            }
            ExpressionDesc::Pexp_object_get(inner) => {
                let (ref e, ref label) = **inner;
                w.write_block_header(22, 2);
                e.marshal(w);
                label.marshal(w);
            }
            ExpressionDesc::Pexp_object_set(inner) => {
                let (ref e, ref label, ref v) = **inner;
                w.write_block_header(23, 3);
                e.marshal(w);
                label.marshal(w);
                v.marshal(w);
            }
            ExpressionDesc::Pexp_object_literal(fields) => {
                w.write_block_header(24, 1);
                fields.marshal(w);
            }
            ExpressionDesc::Pexp_letmodule(inner) => {
                let (ref name, ref me, ref body) = **inner;
                w.write_block_header(25, 3);
                name.marshal(w);
                w.enter_letmodule_expr();
                me.marshal(w);
                w.exit_letmodule_expr();
                body.marshal(w);
            }
            ExpressionDesc::Pexp_letexception(inner) => {
                let (ref ec, ref body) = **inner;
                w.write_block_header(26, 2);
                ec.marshal(w);
                body.marshal(w);
            }
            ExpressionDesc::Pexp_assert(e) => {
                w.write_block_header(27, 1);
                e.marshal(w);
            }
            ExpressionDesc::Pexp_newtype(_) => {
                unreachable!("Pexp_newtype is eliminated from the current n-ary parsetree")
            }
            ExpressionDesc::Pexp_pack(me) => {
                w.write_block_header(28, 1);
                w.enter_pack();
                me.marshal(w);
                w.exit_pack();
            }
            ExpressionDesc::Pexp_open(inner) => {
                let (ref flag, ref lid, ref e) = **inner;
                w.write_block_header(29, 3);
                flag.marshal(w);
                w.write_lident_loc_shared(lid.txt, lid.loc);
                e.marshal(w);
            }
            ExpressionDesc::Pexp_extension(ext) => {
                w.write_block_header(30, 1);
                marshal_extension(ext, w, Some(EmptyPayloadShareKind::ParserAttr));
            }
            ExpressionDesc::Pexp_await(e) => {
                w.write_block_header(31, 1);
                e.marshal(w);
            }
            ExpressionDesc::Pexp_jsx_element(jsx) => {
                w.write_block_header(32, 1);
                jsx.marshal(w);
            }
            ExpressionDesc::Pexp_for_of(inner) => {
                let (ref pat, ref iterable, ref body) = **inner;
                w.write_block_header(33, 3);
                pat.marshal(w);
                iterable.marshal(w);
                body.marshal(w);
            }
            ExpressionDesc::Pexp_for_await_of(inner) => {
                let (ref pat, ref iterable, ref body) = **inner;
                w.write_block_header(34, 3);
                pat.marshal(w);
                iterable.marshal(w);
                body.marshal(w);
            }
            ExpressionDesc::Pexp_template(template) => {
                w.write_block_header(36, 2);
                template.source_segments.marshal(w);
                template.values.marshal(w);
            }
            ExpressionDesc::Pexp_tagged_template(template) => {
                w.write_block_header(37, 3);
                template.tag.marshal(w);
                template.raw_sources.marshal(w);
                template.values.marshal(w);
            }
        }
    }
}

// ========== Case ==========

impl Marshal for Case {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        // case = { pc_bar; pc_lhs; pc_guard; pc_rhs }
        let guard = w
            .next_case_owner_index()
            .and_then(|(owner, case_index)| w.get_arena().case_guard(owner, case_index))
            .or(self.pc_guard);
        w.write_block_header(0, 4);
        self.pc_bar.marshal(w);
        self.pc_lhs.marshal(w);
        guard.marshal(w);
        self.pc_rhs.marshal(w);
    }
}

// ========== Value Binding ==========

impl Marshal for ValueConstraint {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        // value_constraint = { pvc_newtypes; pvc_type }
        w.write_block_header(0, 2);
        self.pvc_newtypes.marshal(w);
        self.pvc_type.marshal(w);
    }
}

impl Marshal for ValueBinding {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        // value_binding = { pvb_pat; pvb_expr; pvb_constraint;
        //                   pvb_attributes; pvb_loc }
        w.write_block_header(0, 5);
        self.pvb_pat.marshal(w);
        self.pvb_expr.marshal(w);
        w.get_arena()
            .value_constraint(self.pvb_pat)
            .cloned()
            .marshal(w);
        let share_empty_pstr = if has_attr(&self.pvb_attributes, w, &["res.braces", "res.ternary"])
        {
            Some(EmptyPayloadShareKind::ParserAttr)
        } else {
            None
        };
        marshal_attributes(&self.pvb_attributes, w, false, false, share_empty_pstr);
        self.pvb_loc.marshal(w);
    }
}

// ========== Payload ==========

impl Marshal for Payload {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
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
            Payload::PPat(inner) => {
                let (ref pat, ref guard) = **inner;
                w.write_block_header(3, 2);
                pat.marshal(w);
                guard.marshal(w);
            }
        }
    }
}

// ========== Module Types ==========

impl Marshal for ModuleType {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        w.write_block_header(0, 3);
        self.pmty_desc.marshal(w);
        self.pmty_loc.marshal(w);
        marshal_attributes(&self.pmty_attributes, w, false, false, None);
    }
}

impl Marshal for ModuleTypeDesc {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        match self {
            ModuleTypeDesc::Pmty_ident(lid) => {
                w.write_block_header(0, 1);
                if w.in_pack() && w.in_letmodule_expr() {
                    w.write_lident_loc_shared(lid.txt, lid.loc);
                } else {
                    lid.marshal(w);
                }
            }
            ModuleTypeDesc::Pmty_signature(sig) => {
                w.write_block_header(1, 1);
                sig.marshal(w);
            }
            ModuleTypeDesc::Pmty_functor(inner) => {
                let (ref name, ref mt1, ref mt2) = **inner;
                w.write_block_header(2, 3);
                name.marshal(w);
                mt1.marshal(w);
                mt2.marshal(w);
            }
            ModuleTypeDesc::Pmty_with(inner) => {
                let (ref mt, ref constraints) = **inner;
                w.write_block_header(3, 2);
                mt.marshal(w);
                constraints.marshal(w);
            }
            ModuleTypeDesc::Pmty_typeof(me) => {
                w.write_block_header(4, 1);
                w.enter_module_typeof();
                me.marshal(w);
                w.exit_module_typeof();
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
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
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
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        w.write_block_header(0, 3);
        self.pmod_desc.marshal(w);
        self.pmod_loc.marshal(w);
        let share_empty_pstr = if has_attr(&self.pmod_attributes, w, &["res.await"])
            && (w.in_letmodule_expr() || w.in_module_typeof())
        {
            Some(EmptyPayloadShareKind::ParserAttr)
        } else {
            None
        };
        marshal_attributes(&self.pmod_attributes, w, false, false, share_empty_pstr);
    }
}

impl Marshal for ModuleExprDesc {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        match self {
            ModuleExprDesc::Pmod_ident(lid) => {
                let key = (lid.txt, lid.loc);
                if let Some(&obj_idx) = w.pmod_ident_table_get(&key) {
                    let d = w.obj_counter() - obj_idx;
                    w.write_shared_ref(d);
                    return;
                }
                let obj_idx = w.obj_counter();
                w.write_block_header(0, 1);
                w.write_lident_loc_shared(lid.txt, lid.loc);
                w.pmod_ident_table_insert(key, obj_idx);
            }
            ModuleExprDesc::Pmod_structure(str) => {
                w.write_block_header(1, 1);
                str.marshal(w);
            }
            ModuleExprDesc::Pmod_functor(inner) => {
                let (ref name, ref mt, ref me) = **inner;
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
                // Treat module-level unpack expression payload like pack context for
                // parser-attribute sharing decisions; OCaml does not consistently
                // reuse empty parser payload objects under unpack.
                w.enter_pack();
                e.marshal(w);
                w.exit_pack();
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
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        // type_declaration has 9 fields
        w.write_block_header(0, 9);
        self.ptype_name.marshal(w);
        self.ptype_params.marshal(w);
        self.ptype_cstrs.marshal(w);
        self.ptype_kind.marshal(w);
        self.ptype_private.marshal(w);
        self.ptype_manifest.marshal(w);
        w.write_int(match self.ptype_origin {
            crate::parser::ast::TypeDeclarationOrigin::Declared => 0,
            crate::parser::ast::TypeDeclarationOrigin::Inline_record_definition => 1,
        });
        marshal_attributes(&self.ptype_attributes, w, false, false, None);
        self.ptype_loc.marshal(w);
    }
}

impl Marshal for TypeKind {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
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

/// `Parsetree.constructor_tag`: the string, int, float, bigint and bool cases
/// are blocks with tags 0-4; `Pct_null` and `Pct_undefined` are the constant
/// constructors 0 and 1.
impl Marshal for ConstructorTag {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        let arena = w.get_arena();
        match self {
            ConstructorTag::Pct_string(s) => {
                w.write_block_header(0, 1);
                marshal_string_const(*s, w);
            }
            ConstructorTag::Pct_int(i) => {
                w.write_block_header(1, 1);
                w.write_str(arena.get_string(*i));
            }
            ConstructorTag::Pct_float(f) => {
                w.write_block_header(2, 1);
                w.write_str(arena.get_string(*f));
            }
            ConstructorTag::Pct_bigint(i) => {
                w.write_block_header(3, 1);
                w.write_str(arena.get_string(*i));
            }
            ConstructorTag::Pct_bool(b) => {
                w.write_block_header(4, 1);
                w.write_int(if *b { 1 } else { 0 });
            }
            ConstructorTag::Pct_null => w.write_int(0),
            ConstructorTag::Pct_undefined => w.write_int(1),
        }
    }
}

impl Marshal for ConstructorDeclaration {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        // OCaml field order: pcd_name, pcd_runtime_tag, pcd_args, pcd_res,
        // pcd_loc, pcd_attributes
        w.write_block_header(0, 6);
        self.pcd_name.marshal(w);
        self.pcd_runtime_tag.marshal(w);
        self.pcd_args.marshal(w);
        self.pcd_res.marshal(w);
        self.pcd_loc.marshal(w);
        marshal_attributes(&self.pcd_attributes, w, false, false, None);
    }
}

impl Marshal for ConstructorArguments {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
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
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        // OCaml field order: pld_name, pld_runtime_name, pld_mutable,
        // pld_optional, pld_type, pld_loc, pld_attributes
        w.write_block_header(0, 7);
        self.pld_name.marshal(w);
        match &self.pld_runtime_name {
            None => w.write_int(0),
            Some(name) => {
                w.write_block_header(0, 1);
                w.write_block_header(0, 2);
                marshal_string_const(name.txt, w);
                name.loc.marshal(w);
            }
        }
        self.pld_mutable.marshal(w);
        w.write_int(if self.pld_optional { 1 } else { 0 });
        self.pld_type.marshal(w);
        self.pld_loc.marshal(w);
        marshal_attributes(&self.pld_attributes, w, false, false, None);
    }
}

// ========== Type Extension ==========

impl Marshal for TypeExtension {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        w.write_block_header(0, 5);
        self.ptyext_path.marshal(w);
        self.ptyext_params.marshal(w);
        self.ptyext_constructors.marshal(w);
        self.ptyext_private.marshal(w);
        marshal_attributes(&self.ptyext_attributes, w, false, false, None);
    }
}

impl Marshal for ExtensionConstructor {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        w.write_block_header(0, 4);
        self.pext_name.marshal(w);
        self.pext_kind.marshal(w);
        self.pext_loc.marshal(w);
        marshal_attributes(&self.pext_attributes, w, false, false, None);
    }
}

impl Marshal for ExtensionConstructorKind {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
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
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        let key = (self.pval_name.txt, self.pval_name.loc, self.pval_loc);
        let shared_name_type = if self.pval_prim.is_none() {
            w.vd_name_type_table_get(&key).copied()
        } else {
            None
        };

        w.write_block_header(0, 5);

        let name_obj_idx = w.obj_counter();
        if let Some((obj_idx, _)) = shared_name_type {
            let d = w.obj_counter() - obj_idx;
            w.write_shared_ref(d);
        } else {
            self.pval_name.marshal(w);
        }

        let type_obj_idx = w.obj_counter();
        if let Some((_, obj_idx)) = shared_name_type {
            let d = w.obj_counter() - obj_idx;
            w.write_shared_ref(d);
        } else {
            self.pval_type.marshal(w);
        }

        if self.pval_prim.is_some() {
            w.vd_name_type_table_insert(key, (name_obj_idx, type_obj_idx));
        }

        marshal_prim(&self.pval_prim, w);
        marshal_attributes(&self.pval_attributes, w, false, false, None);
        self.pval_loc.marshal(w);
    }
}

/// Write `pval_prim : primitive_repr option`. The parser builds a fresh
/// `Some (Prim_name s)`; the frontend's `Prim_name "#raw_expr"` /
/// `Prim_name "#raw_stmt"` are static constants, so OCaml shares them.
fn marshal_prim(prim: &Option<PrimitiveRepr>, w: &mut MarshalWriter<'_>) {
    let Some(prim) = prim else {
        w.write_int(0);
        return;
    };
    // `bsc -bs-ast` writes the AST after the builtin PPX digested externals
    // (js_implementation.ml `after_parsing_impl`).
    let prim = match prim {
        PrimitiveRepr::PrimName(prim) => prim,
        PrimitiveRepr::PrimFfi { name, spec } => {
            w.write_block_header(0, 1);
            w.write_block_header(1, 2);
            w.write_str(name);
            super::ffi_types::marshal_external_ffi(w, spec);
            return;
        }
        PrimitiveRepr::PrimInlineConst(c) => {
            w.write_block_header(0, 1);
            w.write_block_header(2, 1);
            super::ffi_types::marshal_inline_const(w, c);
            return;
        }
    };
    let prim = *prim;
    w.write_block_header(0, 1);
    if prim == w.get_arena().prim_raw_expr() {
        w.write_prim_list_shared(PrimListShareKind::RawExpr, prim);
        return;
    }
    if prim == w.get_arena().prim_raw_stmt() {
        w.write_prim_list_shared(PrimListShareKind::RawStmt, prim);
        return;
    }
    w.write_block_header(0, 1);
    // OCaml keeps hyphenated JS prim names (e.g. "aria-details") fresh,
    // while many other prim strings are physically shared.
    let share_by_idx = {
        let prim_str = w.get_arena().get_string(prim);
        !prim_str.contains('-')
            && !matches!(prim_str, "open" | "type" | "begin" | "end" | "in" | "to")
    };
    if share_by_idx {
        w.write_str_idx(prim);
    } else {
        let prim_bytes: Vec<u8> = w
            .get_arena()
            .get_string(prim)
            .chars()
            .map(|c| c as u8)
            .collect();
        w.write_string(&prim_bytes);
    }
}

// ========== Module declarations ==========

impl Marshal for ModuleDeclaration {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        w.write_block_header(0, 4);
        self.pmd_name.marshal(w);
        self.pmd_type.marshal(w);
        marshal_attributes(&self.pmd_attributes, w, false, false, None);
        self.pmd_loc.marshal(w);
    }
}

impl Marshal for ModuleTypeDeclaration {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        w.write_block_header(0, 4);
        self.pmtd_name.marshal(w);
        self.pmtd_type.marshal(w);
        marshal_attributes(&self.pmtd_attributes, w, false, false, None);
        self.pmtd_loc.marshal(w);
    }
}

impl Marshal for ModuleBinding {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        w.write_block_header(0, 4);
        self.pmb_name.marshal(w);
        self.pmb_expr.marshal(w);
        marshal_attributes(&self.pmb_attributes, w, false, false, None);
        self.pmb_loc.marshal(w);
    }
}

impl Marshal for OpenDescription {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        w.write_block_header(0, 4);
        self.popen_lid.marshal(w);
        self.popen_override.marshal(w);
        self.popen_loc.marshal(w);
        marshal_attributes(&self.popen_attributes, w, false, false, None);
    }
}

impl Marshal for IncludeDescription {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        w.write_block_header(0, 3);
        self.pincl_mod.marshal(w);
        self.pincl_loc.marshal(w);
        marshal_attributes(&self.pincl_attributes, w, false, false, None);
    }
}

impl Marshal for IncludeDeclaration {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        w.write_block_header(0, 3);
        self.pincl_mod.marshal(w);
        self.pincl_loc.marshal(w);
        marshal_attributes(&self.pincl_attributes, w, false, false, None);
    }
}

// ========== Structure ==========

impl Marshal for StructureItem {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        w.write_block_header(0, 2);
        self.pstr_desc.marshal(w);
        self.pstr_loc.marshal(w);
    }
}

impl Marshal for StructureItemDesc {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        match self {
            StructureItemDesc::Pstr_eval(inner) => {
                let (ref e, ref attrs) = **inner;
                w.write_block_header(0, 2);
                e.marshal(w);
                let share_empty_pstr = if w.in_extension() {
                    Some(EmptyPayloadShareKind::ParserAttr)
                } else {
                    None
                };
                marshal_attributes(attrs, w, false, false, share_empty_pstr);
            }
            StructureItemDesc::Pstr_value(inner) => {
                let (ref flag, ref bindings) = **inner;
                w.write_block_header(1, 2);
                flag.marshal(w);
                bindings.marshal(w);
            }
            StructureItemDesc::Pstr_primitive(vd) => {
                w.write_block_header(2, 1);
                vd.marshal(w);
            }
            StructureItemDesc::Pstr_type(inner) => {
                let (ref flag, ref decls) = **inner;
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
            StructureItemDesc::Pstr_extension(inner) => {
                let (ref ext, ref attrs) = **inner;
                w.write_block_header(12, 2);
                ext.marshal(w);
                let share_empty_pstr = if w.in_extension() {
                    Some(EmptyPayloadShareKind::ParserAttr)
                } else {
                    None
                };
                marshal_attributes(attrs, w, false, false, share_empty_pstr);
            }
        }
    }
}

// ========== Signature ==========

impl Marshal for SignatureItem {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        w.write_block_header(0, 2);
        self.psig_desc.marshal(w);
        self.psig_loc.marshal(w);
    }
}

impl Marshal for SignatureItemDesc {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        match self {
            SignatureItemDesc::Psig_value(vd) => {
                w.write_block_header(0, 1);
                vd.marshal(w);
            }
            SignatureItemDesc::Psig_type(inner) => {
                let (ref flag, ref decls) = **inner;
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
            SignatureItemDesc::Psig_extension(inner) => {
                let (ref ext, ref attrs) = **inner;
                w.write_block_header(10, 2);
                ext.marshal(w);
                let share_empty_pstr = if w.in_extension() {
                    Some(EmptyPayloadShareKind::ParserAttr)
                } else {
                    None
                };
                marshal_attributes(attrs, w, false, false, share_empty_pstr);
            }
        }
    }
}

// ========== JSX types ==========

use crate::parser::ast::{
    JsxClosingTag, JsxContainerElement, JsxElement, JsxFragment, JsxProp, JsxTagName,
    JsxUnaryElement,
};

impl Marshal for JsxElement {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        w.enter_jsx();
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
        w.exit_jsx();
    }
}

impl Marshal for JsxFragment {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        // jsx_fragment = { jsx_fragment_opening; jsx_fragment_children; jsx_fragment_closing }
        w.write_block_header(0, 3);
        self.opening.marshal(w);
        self.children.marshal(w);
        self.closing.marshal(w);
    }
}

impl Marshal for JsxUnaryElement {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        // jsx_unary_element = { jsx_unary_element_tag_name; jsx_unary_element_props }
        w.write_block_header(0, 2);
        self.tag_name.marshal(w);
        self.props.marshal(w);
    }
}

impl Marshal for JsxContainerElement {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
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
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        // jsx_closing_container_tag = { start; name; end }
        w.write_block_header(0, 3);
        self.start.marshal(w);
        self.name.marshal(w);
        self.end.marshal(w);
    }
}

impl Marshal for JsxTagName {
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
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
    fn marshal(&self, w: &mut MarshalWriter<'_>) {
        match self {
            JsxProp::Punning { optional, name } => {
                w.write_block_header(0, 2);
                w.write_int(if *optional { 1 } else { 0 });
                name.marshal(w);
            }
            JsxProp::Value {
                name,
                optional,
                value,
            } => {
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
