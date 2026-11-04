//! Port of OCaml's `Ast_iterator` (compiler/ml/ast_iterator.ml) for the Rust
//! parsetree.
//!
//! Each method defaults to the matching `walk_*` function, which visits the
//! children in the same order as OCaml's `default_iterator`. Implementors
//! override the hooks they need and call the `walk_*` function to continue the
//! traversal. Expression, pattern, type, and module nodes are visited by arena
//! index so the sparse side tables (function parameters, record spreads, case
//! guards, ...) can be resolved.

use crate::parse_arena::{CoreTypeIdx, ExprIdx, ModExprIdx, ModTypeIdx, ParseArena, PatIdx};
use crate::parser::ast::*;

pub trait AstIter {
    fn attribute(&mut self, arena: &ParseArena, attr: &Attribute) {
        walk_attribute(self, arena, attr);
    }
    fn attributes(&mut self, arena: &ParseArena, attrs: &[Attribute]) {
        for attr in attrs {
            self.attribute(arena, attr);
        }
    }
    fn case(&mut self, arena: &ParseArena, owner: ExprIdx, index: usize, case: &Case) {
        walk_case(self, arena, owner, index, case);
    }
    fn constructor_declaration(&mut self, arena: &ParseArena, cd: &ConstructorDeclaration) {
        walk_constructor_declaration(self, arena, cd);
    }
    fn expr(&mut self, arena: &ParseArena, idx: ExprIdx) {
        walk_expr(self, arena, idx);
    }
    fn extension(&mut self, arena: &ParseArena, ext: &Extension) {
        walk_extension(self, arena, ext);
    }
    fn extension_constructor(&mut self, arena: &ParseArena, ec: &ExtensionConstructor) {
        walk_extension_constructor(self, arena, ec);
    }
    fn label_declaration(&mut self, arena: &ParseArena, ld: &LabelDeclaration) {
        walk_label_declaration(self, arena, ld);
    }
    fn module_binding(&mut self, arena: &ParseArena, mb: &ModuleBinding) {
        walk_module_binding(self, arena, mb);
    }
    fn module_declaration(&mut self, arena: &ParseArena, md: &ModuleDeclaration) {
        walk_module_declaration(self, arena, md);
    }
    fn module_expr(&mut self, arena: &ParseArena, idx: ModExprIdx) {
        walk_module_expr(self, arena, idx);
    }
    fn module_type(&mut self, arena: &ParseArena, idx: ModTypeIdx) {
        walk_module_type(self, arena, idx);
    }
    fn module_type_declaration(&mut self, arena: &ParseArena, mtd: &ModuleTypeDeclaration) {
        walk_module_type_declaration(self, arena, mtd);
    }
    fn pat(&mut self, arena: &ParseArena, idx: PatIdx) {
        walk_pat(self, arena, idx);
    }
    fn payload(&mut self, arena: &ParseArena, payload: &Payload) {
        walk_payload(self, arena, payload);
    }
    fn signature_item(&mut self, arena: &ParseArena, item: &SignatureItem) {
        walk_signature_item(self, arena, item);
    }
    fn structure_item(&mut self, arena: &ParseArena, item: &StructureItem) {
        walk_structure_item(self, arena, item);
    }
    fn typ(&mut self, arena: &ParseArena, idx: CoreTypeIdx) {
        walk_typ(self, arena, idx);
    }
    fn type_declaration(&mut self, arena: &ParseArena, td: &TypeDeclaration) {
        walk_type_declaration(self, arena, td);
    }
    fn type_extension(&mut self, arena: &ParseArena, te: &TypeExtension) {
        walk_type_extension(self, arena, te);
    }
    fn value_binding(&mut self, arena: &ParseArena, vb: &ValueBinding) {
        walk_value_binding(self, arena, vb);
    }
    fn value_description(&mut self, arena: &ParseArena, vd: &ValueDescription) {
        walk_value_description(self, arena, vd);
    }
}

pub fn walk_structure<V: AstIter + ?Sized>(v: &mut V, arena: &ParseArena, items: &[StructureItem]) {
    for item in items {
        v.structure_item(arena, item);
    }
}

pub fn walk_signature<V: AstIter + ?Sized>(v: &mut V, arena: &ParseArena, items: &[SignatureItem]) {
    for item in items {
        v.signature_item(arena, item);
    }
}

pub fn walk_attribute<V: AstIter + ?Sized>(v: &mut V, arena: &ParseArena, attr: &Attribute) {
    v.payload(arena, &attr.1);
}

pub fn walk_extension<V: AstIter + ?Sized>(v: &mut V, arena: &ParseArena, ext: &Extension) {
    v.payload(arena, &ext.1);
}

pub fn walk_payload<V: AstIter + ?Sized>(v: &mut V, arena: &ParseArena, payload: &Payload) {
    match payload {
        Payload::PStr(items) => walk_structure(v, arena, items),
        Payload::PSig(items) => walk_signature(v, arena, items),
        Payload::PTyp(typ) => v.typ(arena, *typ),
        Payload::PPat(inner) => {
            let (pat, guard) = &**inner;
            v.pat(arena, *pat);
            if let Some(guard) = guard {
                v.expr(arena, *guard);
            }
        }
    }
}

pub fn walk_typ<V: AstIter + ?Sized>(v: &mut V, arena: &ParseArena, idx: CoreTypeIdx) {
    let typ = arena.get_core_type(idx);
    v.attributes(arena, typ.ptyp_attributes.as_slice());
    match &typ.ptyp_desc {
        CoreTypeDesc::Ptyp_any | CoreTypeDesc::Ptyp_var(_) => {}
        CoreTypeDesc::Ptyp_arrow(inner) => {
            // `Ptyp_arrow {params; ret}`: every parameter lives in the
            // arena's n-ary side table.
            let (arg, ret, arity) = &**inner;
            for param in arena.nary_arrow_args(arg, *arity).iter() {
                v.typ(arena, param.typ);
            }
            v.typ(arena, *ret);
        }
        CoreTypeDesc::Ptyp_tuple(types) => {
            for t in arena.type_list(*types).iter() {
                v.typ(arena, *t);
            }
        }
        CoreTypeDesc::Ptyp_constr(inner) => {
            for t in arena.type_list(inner.1).iter() {
                v.typ(arena, *t);
            }
        }
        CoreTypeDesc::Ptyp_object(inner) => {
            for field in inner.0.iter() {
                match field {
                    ObjectField::Otag(_, attrs, t) => {
                        v.attributes(arena, attrs.as_slice());
                        v.typ(arena, *t);
                    }
                    ObjectField::Oinherit(t) => v.typ(arena, *t),
                }
            }
        }
        CoreTypeDesc::Ptyp_alias(inner) => v.typ(arena, inner.0),
        CoreTypeDesc::Ptyp_variant(inner) => {
            for row in inner.0.iter() {
                match row {
                    RowField::Rtag(_, attrs, _, groups) => {
                        v.attributes(arena, attrs.as_slice());
                        for t in groups.iter().flat_map(|group| group.txt.iter()) {
                            v.typ(arena, *t);
                        }
                    }
                    RowField::Rinherit(t) => v.typ(arena, *t),
                }
            }
        }
        CoreTypeDesc::Ptyp_poly(inner) => v.typ(arena, inner.1),
        CoreTypeDesc::Ptyp_package(inner) => {
            for (_, t) in inner.1.iter() {
                v.typ(arena, *t);
            }
        }
        CoreTypeDesc::Ptyp_extension(ext) => v.extension(arena, ext),
    }
}

pub fn walk_type_declaration<V: AstIter + ?Sized>(
    v: &mut V,
    arena: &ParseArena,
    td: &TypeDeclaration,
) {
    for (t, _) in &td.ptype_params {
        v.typ(arena, *t);
    }
    for (t1, t2, _) in &td.ptype_cstrs {
        v.typ(arena, *t1);
        v.typ(arena, *t2);
    }
    match &td.ptype_kind {
        TypeKind::Ptype_abstract | TypeKind::Ptype_open => {}
        TypeKind::Ptype_variant(cds) => {
            for cd in cds {
                v.constructor_declaration(arena, cd);
            }
        }
        TypeKind::Ptype_record(lds) => {
            for ld in lds {
                v.label_declaration(arena, ld);
            }
        }
    }
    if let Some(manifest) = td.ptype_manifest {
        v.typ(arena, manifest);
    }
    v.attributes(arena, td.ptype_attributes.as_slice());
}

fn walk_constructor_arguments<V: AstIter + ?Sized>(
    v: &mut V,
    arena: &ParseArena,
    args: &ConstructorArguments,
) {
    match args {
        ConstructorArguments::Pcstr_tuple(types) => {
            for t in types {
                v.typ(arena, *t);
            }
        }
        ConstructorArguments::Pcstr_record(lds) => {
            for ld in lds {
                v.label_declaration(arena, ld);
            }
        }
    }
}

pub fn walk_constructor_declaration<V: AstIter + ?Sized>(
    v: &mut V,
    arena: &ParseArena,
    cd: &ConstructorDeclaration,
) {
    walk_constructor_arguments(v, arena, &cd.pcd_args);
    if let Some(res) = cd.pcd_res {
        v.typ(arena, res);
    }
    v.attributes(arena, cd.pcd_attributes.as_slice());
}

pub fn walk_label_declaration<V: AstIter + ?Sized>(
    v: &mut V,
    arena: &ParseArena,
    ld: &LabelDeclaration,
) {
    v.typ(arena, ld.pld_type);
    v.attributes(arena, ld.pld_attributes.as_slice());
}

pub fn walk_type_extension<V: AstIter + ?Sized>(v: &mut V, arena: &ParseArena, te: &TypeExtension) {
    for ec in &te.ptyext_constructors {
        v.extension_constructor(arena, ec);
    }
    for (t, _) in &te.ptyext_params {
        v.typ(arena, *t);
    }
    v.attributes(arena, te.ptyext_attributes.as_slice());
}

pub fn walk_extension_constructor<V: AstIter + ?Sized>(
    v: &mut V,
    arena: &ParseArena,
    ec: &ExtensionConstructor,
) {
    match &ec.pext_kind {
        ExtensionConstructorKind::Pext_decl(args, res) => {
            walk_constructor_arguments(v, arena, args);
            if let Some(res) = res {
                v.typ(arena, *res);
            }
        }
        ExtensionConstructorKind::Pext_rebind(_) => {}
    }
    v.attributes(arena, ec.pext_attributes.as_slice());
}

pub fn walk_module_type<V: AstIter + ?Sized>(v: &mut V, arena: &ParseArena, idx: ModTypeIdx) {
    let mty = arena.get_mod_type(idx);
    v.attributes(arena, mty.pmty_attributes.as_slice());
    match &*mty.pmty_desc {
        ModuleTypeDesc::Pmty_ident(_) | ModuleTypeDesc::Pmty_alias(_) => {}
        ModuleTypeDesc::Pmty_signature(items) => walk_signature(v, arena, items),
        ModuleTypeDesc::Pmty_functor(inner) => {
            let (_, arg, body) = &**inner;
            if let Some(arg) = arg {
                v.module_type(arena, *arg);
            }
            v.module_type(arena, *body);
        }
        ModuleTypeDesc::Pmty_with(inner) => {
            let (body, constraints) = &**inner;
            v.module_type(arena, *body);
            for constraint in constraints {
                match constraint {
                    WithConstraint::Pwith_type(_, td) | WithConstraint::Pwith_typesubst(_, td) => {
                        v.type_declaration(arena, td)
                    }
                    WithConstraint::Pwith_module(_, _) | WithConstraint::Pwith_modsubst(_, _) => {}
                }
            }
        }
        ModuleTypeDesc::Pmty_typeof(me) => v.module_expr(arena, *me),
        ModuleTypeDesc::Pmty_extension(ext) => v.extension(arena, ext),
    }
}

pub fn walk_signature_item<V: AstIter + ?Sized>(
    v: &mut V,
    arena: &ParseArena,
    item: &SignatureItem,
) {
    match &*item.psig_desc {
        SignatureItemDesc::Psig_value(vd) => v.value_description(arena, vd),
        SignatureItemDesc::Psig_type(inner) => {
            for td in &inner.1 {
                v.type_declaration(arena, td);
            }
        }
        SignatureItemDesc::Psig_typext(te) => v.type_extension(arena, te),
        SignatureItemDesc::Psig_exception(ec) => v.extension_constructor(arena, ec),
        SignatureItemDesc::Psig_module(md) => v.module_declaration(arena, md),
        SignatureItemDesc::Psig_recmodule(mds) => {
            for md in mds.iter() {
                v.module_declaration(arena, md);
            }
        }
        SignatureItemDesc::Psig_modtype(mtd) => v.module_type_declaration(arena, mtd),
        SignatureItemDesc::Psig_open(od) => v.attributes(arena, od.popen_attributes.as_slice()),
        SignatureItemDesc::Psig_include(incl) => {
            v.module_type(arena, incl.pincl_mod);
            v.attributes(arena, incl.pincl_attributes.as_slice());
        }
        SignatureItemDesc::Psig_extension(inner) => {
            let (ext, attrs) = &**inner;
            v.extension(arena, ext);
            v.attributes(arena, attrs.as_slice());
        }
        SignatureItemDesc::Psig_attribute(attr) => v.attribute(arena, attr),
    }
}

pub fn walk_module_expr<V: AstIter + ?Sized>(v: &mut V, arena: &ParseArena, idx: ModExprIdx) {
    let me = arena.get_mod_expr(idx);
    v.attributes(arena, me.pmod_attributes.as_slice());
    match &*me.pmod_desc {
        ModuleExprDesc::Pmod_ident(_) => {}
        ModuleExprDesc::Pmod_structure(items) => walk_structure(v, arena, items),
        ModuleExprDesc::Pmod_functor(inner) => {
            let (_, arg, body) = &**inner;
            if let Some(arg) = arg {
                v.module_type(arena, *arg);
            }
            v.module_expr(arena, *body);
        }
        ModuleExprDesc::Pmod_apply(m1, m2) => {
            v.module_expr(arena, *m1);
            v.module_expr(arena, *m2);
        }
        ModuleExprDesc::Pmod_constraint(m, mty) => {
            v.module_expr(arena, *m);
            v.module_type(arena, *mty);
        }
        ModuleExprDesc::Pmod_unpack(e) => v.expr(arena, *e),
        ModuleExprDesc::Pmod_extension(ext) => v.extension(arena, ext),
    }
}

pub fn walk_structure_item<V: AstIter + ?Sized>(
    v: &mut V,
    arena: &ParseArena,
    item: &StructureItem,
) {
    match &*item.pstr_desc {
        StructureItemDesc::Pstr_eval(inner) => {
            let (e, attrs) = &**inner;
            v.expr(arena, *e);
            v.attributes(arena, attrs.as_slice());
        }
        StructureItemDesc::Pstr_value(inner) => {
            for vb in &inner.1 {
                v.value_binding(arena, vb);
            }
        }
        StructureItemDesc::Pstr_primitive(vd) => v.value_description(arena, vd),
        StructureItemDesc::Pstr_type(inner) => {
            for td in &inner.1 {
                v.type_declaration(arena, td);
            }
        }
        StructureItemDesc::Pstr_typext(te) => v.type_extension(arena, te),
        StructureItemDesc::Pstr_exception(ec) => v.extension_constructor(arena, ec),
        StructureItemDesc::Pstr_module(mb) => v.module_binding(arena, mb),
        StructureItemDesc::Pstr_recmodule(mbs) => {
            for mb in mbs.iter() {
                v.module_binding(arena, mb);
            }
        }
        StructureItemDesc::Pstr_modtype(mtd) => v.module_type_declaration(arena, mtd),
        StructureItemDesc::Pstr_open(od) => v.attributes(arena, od.popen_attributes.as_slice()),
        StructureItemDesc::Pstr_include(incl) => {
            v.module_expr(arena, incl.pincl_mod);
            v.attributes(arena, incl.pincl_attributes.as_slice());
        }
        StructureItemDesc::Pstr_extension(inner) => {
            let (ext, attrs) = &**inner;
            v.extension(arena, ext);
            v.attributes(arena, attrs.as_slice());
        }
        StructureItemDesc::Pstr_attribute(attr) => v.attribute(arena, attr),
    }
}

fn walk_jsx_props<V: AstIter + ?Sized>(v: &mut V, arena: &ParseArena, props: &[JsxProp]) {
    for prop in props {
        match prop {
            JsxProp::Punning { .. } => {}
            JsxProp::Value { value, .. } => v.expr(arena, *value),
            JsxProp::Spreading { expr, .. } => v.expr(arena, *expr),
        }
    }
}

pub fn walk_expr<V: AstIter + ?Sized>(v: &mut V, arena: &ParseArena, idx: ExprIdx) {
    let expr = arena.get_expr(idx);
    v.attributes(arena, expr.pexp_attributes.as_slice());
    match &expr.pexp_desc {
        ExpressionDesc::Pexp_braces(braces) => v.expr(arena, braces.expr),
        ExpressionDesc::Pexp_ternary(inner) => {
            v.expr(arena, inner.0);
            v.expr(arena, inner.1);
            v.expr(arena, inner.2);
        }
        ExpressionDesc::Pexp_ident(_)
        | ExpressionDesc::Pexp_constant(_)
        | ExpressionDesc::Pexp_regexp(_)
        | ExpressionDesc::Pexp_break
        | ExpressionDesc::Pexp_continue => {}
        ExpressionDesc::Pexp_let(inner) => {
            let (_, vbs, body) = &**inner;
            for vb in vbs {
                v.value_binding(arena, vb);
            }
            v.expr(arena, *body);
        }
        ExpressionDesc::Pexp_fun(fun) => {
            for (_, attrs) in arena.nary_fun_newtypes(fun) {
                v.attributes(arena, attrs.as_slice());
            }
            let params = arena.nary_fun_params(fun);
            for param in params.iter() {
                if let Some(default) = param.p_default {
                    v.expr(arena, default);
                }
                v.pat(arena, param.p_pat);
            }
            v.expr(arena, arena.nary_fun_body(fun));
        }
        ExpressionDesc::Pexp_apply(apply) => {
            v.expr(arena, apply.funct);
            for (_, arg) in arena.apply_args(apply.args) {
                v.expr(arena, *arg);
            }
        }
        ExpressionDesc::Pexp_match(inner) | ExpressionDesc::Pexp_try(inner) => {
            let (scrutinee, cases) = &**inner;
            v.expr(arena, *scrutinee);
            for (index, case) in cases.iter().enumerate() {
                v.case(arena, idx, index, case);
            }
        }
        ExpressionDesc::Pexp_tuple(items) | ExpressionDesc::Pexp_array(items) => {
            for e in arena.expr_list(*items).iter() {
                v.expr(arena, *e);
            }
        }
        ExpressionDesc::Pexp_construct(_, args) => {
            for arg in arena.expr_list(args.txt) {
                v.expr(arena, *arg);
            }
        }
        ExpressionDesc::Pexp_variant(inner) => {
            for arg in arena.expr_list(inner.1.txt) {
                v.expr(arena, *arg);
            }
        }
        ExpressionDesc::Pexp_record(inner) => {
            for field in &inner.0 {
                v.expr(arena, field.expr);
            }
            if let Some(spread) = arena.record_spread(idx) {
                v.expr(arena, spread);
            }
        }
        ExpressionDesc::Pexp_field(e, _) => v.expr(arena, *e),
        ExpressionDesc::Pexp_setfield(inner) => {
            v.expr(arena, inner.0);
            v.expr(arena, inner.2);
        }
        ExpressionDesc::Pexp_ifthenelse(inner) => {
            v.expr(arena, inner.0);
            v.expr(arena, inner.1);
            if let Some(else_branch) = arena.if_else_branch(idx) {
                v.expr(arena, else_branch);
            }
        }
        ExpressionDesc::Pexp_sequence(e1, e2) | ExpressionDesc::Pexp_while(e1, e2) => {
            v.expr(arena, *e1);
            v.expr(arena, *e2);
        }
        ExpressionDesc::Pexp_for(inner) => {
            let (pat, e1, e2, _, e3) = &**inner;
            v.pat(arena, *pat);
            v.expr(arena, *e1);
            v.expr(arena, *e2);
            v.expr(arena, *e3);
        }
        ExpressionDesc::Pexp_for_of(inner) | ExpressionDesc::Pexp_for_await_of(inner) => {
            let (pat, e1, e2) = &**inner;
            v.pat(arena, *pat);
            v.expr(arena, *e1);
            v.expr(arena, *e2);
        }
        ExpressionDesc::Pexp_coerce(inner) => {
            let (e, _, to) = &**inner;
            v.expr(arena, *e);
            v.typ(arena, *to);
        }
        ExpressionDesc::Pexp_constraint(inner) => {
            v.expr(arena, inner.0);
            v.typ(arena, inner.1);
        }
        ExpressionDesc::Pexp_object_get(inner) => v.expr(arena, inner.0),
        ExpressionDesc::Pexp_object_set(inner) => {
            v.expr(arena, inner.0);
            v.expr(arena, inner.2);
        }
        ExpressionDesc::Pexp_object_literal(fields) => {
            for (_, e) in fields.iter() {
                v.expr(arena, *e);
            }
        }
        ExpressionDesc::Pexp_letmodule(inner) => {
            let (_, me, body) = &**inner;
            v.module_expr(arena, *me);
            v.expr(arena, *body);
        }
        ExpressionDesc::Pexp_letexception(inner) => {
            let (ec, body) = &**inner;
            v.extension_constructor(arena, ec);
            v.expr(arena, *body);
        }
        ExpressionDesc::Pexp_assert(e) | ExpressionDesc::Pexp_await(e) => v.expr(arena, *e),
        ExpressionDesc::Pexp_template(template) => {
            for value in &template.values {
                v.expr(arena, *value);
            }
        }
        ExpressionDesc::Pexp_tagged_template(template) => {
            v.expr(arena, template.tag);
            for value in &template.values {
                v.expr(arena, *value);
            }
        }
        ExpressionDesc::Pexp_newtype(inner) => v.expr(arena, inner.1),
        ExpressionDesc::Pexp_pack(me) => v.module_expr(arena, *me),
        ExpressionDesc::Pexp_open(inner) => v.expr(arena, inner.2),
        ExpressionDesc::Pexp_extension(ext) => v.extension(arena, ext),
        ExpressionDesc::Pexp_jsx_element(jsx) => match &**jsx {
            JsxElement::Fragment(fragment) => {
                for child in &fragment.children {
                    v.expr(arena, *child);
                }
            }
            JsxElement::Unary(element) => walk_jsx_props(v, arena, &element.props),
            JsxElement::Container(element) => {
                walk_jsx_props(v, arena, &element.props);
                for child in &element.children {
                    v.expr(arena, *child);
                }
            }
        },
    }
}

pub fn walk_case<V: AstIter + ?Sized>(
    v: &mut V,
    arena: &ParseArena,
    owner: ExprIdx,
    index: usize,
    case: &Case,
) {
    v.pat(arena, case.pc_lhs);
    if let Some(guard) = arena.case_guard(owner, index) {
        v.expr(arena, guard);
    }
    v.expr(arena, case.pc_rhs);
}

pub fn walk_pat<V: AstIter + ?Sized>(v: &mut V, arena: &ParseArena, idx: PatIdx) {
    let pat = arena.get_pat(idx);
    v.attributes(arena, pat.ppat_attributes.as_slice());
    match &pat.ppat_desc {
        PatternDesc::Ppat_any
        | PatternDesc::Ppat_var(_)
        | PatternDesc::Ppat_constant(_)
        | PatternDesc::Ppat_interval(_)
        | PatternDesc::Ppat_type(_)
        | PatternDesc::Ppat_unpack(_) => {}
        PatternDesc::Ppat_alias(p, _) | PatternDesc::Ppat_exception(p) => v.pat(arena, *p),
        PatternDesc::Ppat_tuple(pats) | PatternDesc::Ppat_array(pats) => {
            for p in arena.pat_list(*pats).iter() {
                v.pat(arena, *p);
            }
        }
        PatternDesc::Ppat_construct(_, args) => {
            for arg in arena.pat_list(args.txt) {
                v.pat(arena, *arg);
            }
        }
        PatternDesc::Ppat_variant(inner) => {
            for arg in arena.pat_list(inner.1.txt) {
                v.pat(arena, *arg);
            }
        }
        PatternDesc::Ppat_record(inner) => {
            for field in &inner.0 {
                v.pat(arena, field.pat);
            }
            if let Some(rest) = &inner.2
                && let Some(rest_type) = rest.rest_type
            {
                v.typ(arena, rest_type);
            }
        }
        PatternDesc::Ppat_or(p1, p2) => {
            v.pat(arena, *p1);
            v.pat(arena, *p2);
        }
        PatternDesc::Ppat_constraint(inner) => {
            v.pat(arena, inner.0);
            v.typ(arena, inner.1);
        }
        PatternDesc::Ppat_extension(ext) => v.extension(arena, ext),
    }
}

pub fn walk_value_binding<V: AstIter + ?Sized>(v: &mut V, arena: &ParseArena, vb: &ValueBinding) {
    v.pat(arena, vb.pvb_pat);
    if let Some(constraint) = arena.value_constraint(vb.pvb_pat) {
        v.typ(arena, constraint.pvc_type);
    }
    v.expr(arena, vb.pvb_expr);
    v.attributes(arena, vb.pvb_attributes.as_slice());
}

pub fn walk_value_description<V: AstIter + ?Sized>(
    v: &mut V,
    arena: &ParseArena,
    vd: &ValueDescription,
) {
    v.typ(arena, vd.pval_type);
    v.attributes(arena, vd.pval_attributes.as_slice());
}

pub fn walk_module_binding<V: AstIter + ?Sized>(v: &mut V, arena: &ParseArena, mb: &ModuleBinding) {
    v.module_expr(arena, mb.pmb_expr);
    v.attributes(arena, mb.pmb_attributes.as_slice());
}

pub fn walk_module_declaration<V: AstIter + ?Sized>(
    v: &mut V,
    arena: &ParseArena,
    md: &ModuleDeclaration,
) {
    v.module_type(arena, md.pmd_type);
    v.attributes(arena, md.pmd_attributes.as_slice());
}

pub fn walk_module_type_declaration<V: AstIter + ?Sized>(
    v: &mut V,
    arena: &ParseArena,
    mtd: &ModuleTypeDeclaration,
) {
    if let Some(mty) = mtd.pmtd_type {
        v.module_type(arena, mty);
    }
    v.attributes(arena, mtd.pmtd_attributes.as_slice());
}
