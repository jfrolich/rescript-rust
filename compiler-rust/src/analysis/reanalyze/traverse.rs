//! The typed tree, visited in the order OCaml's `Tast_mapper.default` visits
//! it (compiler/ml/tast_mapper.ml).
//!
//! The analyses print what they find as they find it (`-debug`), so the
//! order is part of their output. `Tast_mapper` rebuilds each node from its
//! mapped children, and OCaml evaluates the arguments of a constructor and
//! the fields of a record from the last to the first: the else branch of a
//! conditional is visited before its condition, a function's arguments
//! before the function. `List.map` and explicit `let`s go first to last.
//! Core types are not visited: no analysis reads them.

use crate::parse_arena::LocIdx;
use crate::types::typedtree as tt;
use crate::types::typedtree::{TExprIdx, TModExprIdx, TModTypeIdx, TPatIdx};

/// The hooks of `Tast_mapper.mapper` the analyses override. Each default
/// visits the node's children.
pub trait Visitor<'t>: Sized {
    /// Node storage of the typed tree.
    fn ta(&self) -> &'t tt::TypedArena;

    /// `mapper.expr`.
    fn expr(&mut self, e: TExprIdx) {
        super_expr(self, e);
    }
    /// `mapper.pat`.
    fn pat(&mut self, p: TPatIdx) {
        super_pat(self, p);
    }
    /// `mapper.structure`.
    fn structure(&mut self, s: &'t tt::Structure) {
        super_structure(self, s);
    }
    /// `mapper.structure_item`.
    fn structure_item(&mut self, item: &'t tt::StructureItem) {
        super_structure_item(self, item);
    }
    /// `mapper.value_binding`.
    fn value_binding(&mut self, vb: &'t tt::ValueBinding) {
        super_value_binding(self, vb);
    }
    /// `mapper.value_bindings`.
    fn value_bindings(
        &mut self,
        _rec_flag: crate::parser::ast::RecFlag,
        vbs: &'t [tt::ValueBinding],
    ) {
        super_value_bindings(self, vbs);
    }
    /// `mapper.type_declaration`.
    fn type_declaration(&mut self, td: &'t tt::TypedTypeDeclaration) {
        self.type_kind(&td.typ_kind);
    }
    /// `mapper.type_kind`.
    fn type_kind(&mut self, _kind: &'t tt::TypedTypeKind) {}
    /// `mapper.value_description`. `item_loc` is the location of the item
    /// declaring the value, which is `val_val.val_loc` (typedecl.ml:1883-1889
    /// receives it from typemod.ml:755-757), not the description's own.
    fn value_description(&mut self, _vd: &'t tt::TypedValueDescription, _item_loc: LocIdx) {}
    /// `mapper.signature`.
    fn signature(&mut self, s: &'t tt::TypedSignature) {
        super_signature(self, s);
    }
    /// `mapper.signature_item`.
    fn signature_item(&mut self, item: &'t tt::TypedSignatureItem) {
        super_signature_item(self, item);
    }
    /// `mapper.module_expr`.
    fn module_expr(&mut self, m: TModExprIdx) {
        super_module_expr(self, m);
    }
}

/// `Tast_mapper.structure`.
pub fn super_structure<'t, V: Visitor<'t>>(v: &mut V, s: &'t tt::Structure) {
    for item in v.ta().structure_items(s.str_items) {
        v.structure_item(item);
    }
}

fn type_declarations<'t, V: Visitor<'t>>(v: &mut V, decls: &'t [tt::TypedTypeDeclaration]) {
    for decl in decls {
        v.type_declaration(decl);
    }
}

fn module_type_declaration<'t, V: Visitor<'t>>(v: &mut V, mtd: &'t tt::ModuleTypeDeclaration) {
    if let Some(mty) = mtd.mtd_type {
        module_type(v, mty);
    }
}

/// `Tast_mapper.structure_item`.
pub fn super_structure_item<'t, V: Visitor<'t>>(v: &mut V, item: &'t tt::StructureItem) {
    use tt::StructureItemDesc::*;
    let ta = v.ta();
    match &item.str_desc {
        Tstr_eval(e, _) => v.expr(*e),
        Tstr_value(rec_flag, vbs) => v.value_bindings(*rec_flag, ta.value_bindings(*vbs)),
        Tstr_primitive(vd) => v.value_description(ta.value_description(*vd), item.str_loc),
        Tstr_type(_, decls) => type_declarations(v, decls),
        // Their children are core types.
        Tstr_typext(_) | Tstr_exception(_) => {}
        Tstr_module(mb) => v.module_expr(mb.mb_expr),
        Tstr_recmodule(mbs) => {
            for mb in mbs {
                v.module_expr(mb.mb_expr);
            }
        }
        Tstr_modtype(mtd) => module_type_declaration(v, mtd),
        Tstr_include(incl) => v.module_expr(incl.incl_mod),
        Tstr_open(_) | Tstr_attribute(_) => {}
        // A derived item has no OCaml counterpart: its bindings are values
        // the checker entered without typing a body.
        Tstr_derived(_) => {}
    }
}

/// `Tast_mapper.pat`.
pub fn super_pat<'t, V: Visitor<'t>>(v: &mut V, p: TPatIdx) {
    use tt::PatternDesc::*;
    let ta = v.ta();
    match &ta.pattern(p).pat_desc {
        Tpat_any | Tpat_var(..) | Tpat_constant(_) | Tpat_interval(..) => {}
        Tpat_tuple(pats) | Tpat_construct(_, _, pats) | Tpat_array(pats) => {
            for p in ta.pattern_list(*pats) {
                v.pat(*p);
            }
        }
        Tpat_variant(_, po, _) => {
            if let Some(p) = po {
                v.pat(*p);
            }
        }
        Tpat_record(fields, _, _) => {
            for (_, _, p, _) in fields {
                v.pat(*p);
            }
        }
        Tpat_dict(entries) => {
            for entry in entries {
                v.pat(entry.tdp_pattern);
            }
        }
        Tpat_or(p1, p2, _) => {
            v.pat(*p2);
            v.pat(*p1);
        }
        Tpat_alias(p, _, _) => v.pat(*p),
    }
}

fn expr_opt<'t, V: Visitor<'t>>(v: &mut V, e: Option<TExprIdx>) {
    if let Some(e) = e {
        v.expr(e);
    }
}

fn exprs<'t, V: Visitor<'t>>(v: &mut V, list: tt::TExprList) {
    for e in v.ta().expr_list(list) {
        v.expr(*e);
    }
}

/// `Tast_mapper.cases`.
pub fn cases<'t, V: Visitor<'t>>(v: &mut V, list: tt::TCaseList) {
    for case in v.ta().cases(list) {
        v.expr(case.c_rhs);
        expr_opt(v, case.c_guard);
        v.pat(case.c_lhs);
    }
}

/// `Tast_mapper.expr`.
pub fn super_expr<'t, V: Visitor<'t>>(v: &mut V, e: TExprIdx) {
    use tt::ExpressionDesc::*;
    let ta = v.ta();
    match &ta.expr(e).exp_desc {
        Texp_ident(..) | Texp_constant(_) | Texp_break | Texp_continue => {}
        Texp_let(rec_flag, vbs, body) => {
            v.value_bindings(*rec_flag, ta.value_bindings(*vbs));
            v.expr(*body);
        }
        Texp_function { params, body, .. } => {
            v.expr(*body);
            for param in ta.function_params(*params) {
                v.pat(param.fp_pat);
            }
        }
        Texp_apply { funct, args, .. } => {
            for arg in ta.apply_args(*args) {
                expr_opt(v, arg.expression);
            }
            v.expr(*funct);
        }
        Texp_match(scrutinee, value_cases, exn_cases, _) => {
            cases(v, *exn_cases);
            cases(v, *value_cases);
            v.expr(*scrutinee);
        }
        Texp_try(body, handlers, finally) => {
            expr_opt(v, *finally);
            cases(v, *handlers);
            v.expr(*body);
        }
        Texp_tuple(list) | Texp_construct(_, _, list) | Texp_array(list) | Texp_spread(_, list) => {
            exprs(v, *list)
        }
        Texp_variant(_, e) => expr_opt(v, *e),
        Texp_record {
            fields,
            extended_expression,
            ..
        } => {
            for (_, _, e) in ta.record_fields(*fields) {
                v.expr(*e);
            }
            expr_opt(v, *extended_expression);
        }
        Texp_field(e, _, _) => v.expr(*e),
        Texp_setfield(e1, _, _, e2) => {
            v.expr(*e2);
            v.expr(*e1);
        }
        Texp_dict(entries) => {
            for entry in ta.dict_entries(*entries) {
                match entry {
                    tt::DictEntry::Tdict_entry(_, e) | tt::DictEntry::Tdict_spread(e) => v.expr(*e),
                }
            }
        }
        Texp_ifthenelse(e1, e2, e3) => {
            expr_opt(v, *e3);
            v.expr(*e2);
            v.expr(*e1);
        }
        Texp_sequence(e1, e2) | Texp_while(e1, e2) => {
            v.expr(*e2);
            v.expr(*e1);
        }
        Texp_for(_, _, e1, e2, _, e3) => {
            v.expr(*e3);
            v.expr(*e2);
            v.expr(*e1);
        }
        Texp_for_of(_, _, e1, e2) | Texp_for_await_of(_, _, e1, e2) => {
            v.expr(*e2);
            v.expr(*e1);
        }
        Texp_template { values, .. } => exprs(v, *values),
        Texp_tagged_template { tag, values, .. } => {
            exprs(v, *values);
            v.expr(*tag);
        }
        Texp_object_get(e, _) => v.expr(*e),
        Texp_object_set(e, _, value) => {
            v.expr(*value);
            v.expr(*e);
        }
        Texp_object_literal(fields) => {
            for (_, e) in fields {
                v.expr(*e);
            }
        }
        Texp_letmodule(_, _, m, body) => {
            v.expr(*body);
            v.module_expr(*m);
        }
        // The extension constructor's children are core types.
        Texp_letexception(_, body) => v.expr(*body),
        Texp_assert(e) => v.expr(*e),
        Texp_pack(m) => v.module_expr(*m),
    }
}

/// `Tast_mapper.signature`.
pub fn super_signature<'t, V: Visitor<'t>>(v: &mut V, s: &'t tt::TypedSignature) {
    for item in v.ta().signature_items(s.sig_items) {
        v.signature_item(item);
    }
}

/// `Tast_mapper.signature_item`.
pub fn super_signature_item<'t, V: Visitor<'t>>(v: &mut V, item: &'t tt::TypedSignatureItem) {
    use tt::TypedSignatureItemDesc::*;
    let ta = v.ta();
    match &item.sig_desc {
        Tsig_value(vd) => v.value_description(ta.value_description(*vd), item.sig_loc),
        Tsig_type(_, decls) => type_declarations(v, decls),
        Tsig_typext(_) | Tsig_exception(_) => {}
        Tsig_module(md) => module_type(v, md.md_type),
        Tsig_recmodule(mds) => {
            for md in mds {
                module_type(v, md.md_type);
            }
        }
        Tsig_modtype(mtd) => module_type_declaration(v, mtd),
        Tsig_include(incl) => module_type(v, incl.incl_mod),
        Tsig_open(_) | Tsig_attribute(_) => {}
    }
}

/// `Tast_mapper.module_type`.
pub fn module_type<'t, V: Visitor<'t>>(v: &mut V, m: TModTypeIdx) {
    use tt::ModuleTypeDesc::*;
    let ta = v.ta();
    match &ta.module_type(m).mty_desc {
        Tmty_ident(..) | Tmty_alias(..) => {}
        Tmty_signature(s) => v.signature(s),
        Tmty_functor(_, _, param, result) => {
            module_type(v, *result);
            if let Some(param) = param {
                module_type(v, *param);
            }
        }
        Tmty_with(base, constraints) => {
            for (_, _, constraint) in constraints {
                match constraint {
                    tt::WithConstraint::Twith_type(decl)
                    | tt::WithConstraint::Twith_typesubst(decl) => v.type_declaration(decl),
                    tt::WithConstraint::Twith_module(..)
                    | tt::WithConstraint::Twith_modsubst(..) => {}
                }
            }
            module_type(v, *base);
        }
        Tmty_typeof(m) => v.module_expr(*m),
    }
}

/// `Tast_mapper.module_expr`.
pub fn super_module_expr<'t, V: Visitor<'t>>(v: &mut V, m: TModExprIdx) {
    use tt::ModuleExprDesc::*;
    let ta = v.ta();
    match &ta.module_expr(m).mod_desc {
        Tmod_ident(..) => {}
        Tmod_structure(s) => v.structure(s),
        Tmod_functor(_, _, param, body) => {
            v.module_expr(*body);
            if let Some(param) = param {
                module_type(v, *param);
            }
        }
        Tmod_apply(m1, m2, _) => {
            v.module_expr(*m2);
            v.module_expr(*m1);
        }
        Tmod_constraint(m, _, constraint, _) => {
            if let tt::ModuleTypeConstraint::Tmodtype_explicit(mty) = constraint {
                module_type(v, *mty);
            }
            v.module_expr(*m);
        }
        Tmod_unpack(e, _) => v.expr(*e),
    }
}

/// `Tast_mapper.value_binding`.
pub fn super_value_binding<'t, V: Visitor<'t>>(v: &mut V, vb: &'t tt::ValueBinding) {
    v.pat(vb.vb_pat);
    v.expr(vb.vb_expr);
}

/// `Tast_mapper.value_bindings`.
pub fn super_value_bindings<'t, V: Visitor<'t>>(v: &mut V, vbs: &'t [tt::ValueBinding]) {
    for vb in vbs {
        v.value_binding(vb);
    }
}
