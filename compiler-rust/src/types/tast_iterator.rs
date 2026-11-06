//! A port of compiler/ml/tast_iterator.ml.
//!
//! OCaml's `iterator` record of open-recursive functions becomes a trait: a
//! method's default body is the `default_iterator` entry, and an override
//! calls the matching `walk_*` function to continue into the children (the
//! OCaml `Tast_iterator.default_iterator.<field> iter x` idiom). The `env`
//! and `module_coercion` callbacks only ever visit environments, which no
//! Rust consumer inspects, so they are not modelled.
//!
//! Children are stored in the typed tree's arena, so an iterator also
//! names the [`TypedArena`] it walks (`'t` is the arena's lifetime).

use super::typedtree::*;
use crate::parser::ast::RecFlag;

/// `Tast_iterator.iterator`.
pub trait TastIterator<'t> {
    /// The arena holding the nodes of the tree being walked.
    fn arena(&self) -> &'t TypedArena;
    fn case(&mut self, c: &Case) {
        walk_case(self, c)
    }
    fn cases(&mut self, cases: &[Case]) {
        for c in cases {
            self.case(c);
        }
    }
    fn expr(&mut self, e: &Expression) {
        walk_expr(self, e)
    }
    fn extension_constructor(&mut self, ext: &ExtensionConstructor) {
        walk_extension_constructor(self, ext)
    }
    fn module_binding(&mut self, mb: &ModuleBinding) {
        self.module_expr(&mb.mb_expr)
    }
    fn module_declaration(&mut self, md: &TypedModuleDeclaration) {
        self.module_type(&md.md_type)
    }
    fn module_expr(&mut self, m: &ModuleExpr) {
        walk_module_expr(self, m)
    }
    fn module_type(&mut self, m: &ModuleType) {
        walk_module_type(self, m)
    }
    fn module_type_declaration(&mut self, mtd: &ModuleTypeDeclaration) {
        if let Some(t) = &mtd.mtd_type {
            self.module_type(t);
        }
    }
    fn package_type(&mut self, pack: &PackageType) {
        for (_, t) in &pack.pack_fields {
            self.typ(t);
        }
    }
    fn pat(&mut self, p: &Pattern) {
        walk_pat(self, p)
    }
    fn row_field(&mut self, rf: &RowFieldType) {
        match &rf.rf_desc {
            RowFieldDesc::Rtag(_, _, types) => {
                for t in types {
                    self.typ(t);
                }
            }
            RowFieldDesc::Rinherit(t) => self.typ(t),
        }
    }
    fn object_field(&mut self, of: &ObjectField) {
        match &of.of_desc {
            ObjectFieldDesc::OTtag(_, t) | ObjectFieldDesc::OTinherit(t) => self.typ(t),
        }
    }
    fn signature(&mut self, s: &TypedSignature) {
        for item in &s.sig_items {
            self.signature_item(item);
        }
    }
    fn signature_item(&mut self, item: &TypedSignatureItem) {
        walk_signature_item(self, item)
    }
    fn structure(&mut self, s: &Structure) {
        for item in &s.str_items {
            self.structure_item(item);
        }
    }
    fn structure_item(&mut self, item: &StructureItem) {
        walk_structure_item(self, item)
    }
    fn typ(&mut self, t: &TypedCoreType) {
        walk_typ(self, t)
    }
    fn type_declaration(&mut self, td: &TypedTypeDeclaration) {
        walk_type_declaration(self, td)
    }
    fn type_declarations(&mut self, _rec_flag: &RecFlag, decls: &[TypedTypeDeclaration]) {
        for td in decls {
            self.type_declaration(td);
        }
    }
    fn type_extension(&mut self, te: &TypeExtension) {
        for (t, _) in &te.tyext_params {
            self.typ(t);
        }
        for c in &te.tyext_constructors {
            self.extension_constructor(c);
        }
    }
    fn type_kind(&mut self, kind: &TypedTypeKind) {
        match kind {
            TypedTypeKind::Ttype_abstract | TypedTypeKind::Ttype_open => {}
            TypedTypeKind::Ttype_variant(cds) => {
                for cd in cds {
                    match &cd.cd_args {
                        TypedConstructorArguments::Cstr_tuple(types) => {
                            for t in types {
                                self.typ(t);
                            }
                        }
                        TypedConstructorArguments::Cstr_record(lds) => {
                            for ld in lds {
                                self.typ(&ld.ld_type);
                            }
                        }
                    }
                    if let Some(res) = &cd.cd_res {
                        self.typ(res);
                    }
                }
            }
            TypedTypeKind::Ttype_record(lds) => {
                for ld in lds {
                    self.typ(&ld.ld_type);
                }
            }
        }
    }
    fn value_binding(&mut self, vb: &ValueBinding) {
        self.pat(&vb.vb_pat);
        let ta = self.arena();
        self.expr(ta.expr(vb.vb_expr));
    }
    fn value_bindings(&mut self, _rec_flag: &RecFlag, vbs: &[ValueBinding]) {
        for vb in vbs {
            self.value_binding(vb);
        }
    }
    fn value_description(&mut self, vd: &TypedValueDescription) {
        self.typ(&vd.val_desc)
    }
    fn with_constraint(&mut self, wc: &WithConstraint) {
        match wc {
            WithConstraint::Twith_type(td) | WithConstraint::Twith_typesubst(td) => {
                self.type_declaration(td)
            }
            WithConstraint::Twith_module(..) | WithConstraint::Twith_modsubst(..) => {}
        }
    }
}

pub fn walk_case<'t, I: TastIterator<'t> + ?Sized>(sub: &mut I, c: &Case) {
    let ta = sub.arena();
    sub.pat(&c.c_lhs);
    if let Some(g) = c.c_guard {
        sub.expr(ta.expr(g));
    }
    sub.expr(ta.expr(c.c_rhs));
}

pub fn walk_structure_item<'t, I: TastIterator<'t> + ?Sized>(sub: &mut I, item: &StructureItem) {
    match &item.str_desc {
        StructureItemDesc::Tstr_eval(e, _) => {
            let ta = sub.arena();
            sub.expr(ta.expr(*e))
        }
        StructureItemDesc::Tstr_value(rec_flag, vbs) => {
            sub.value_bindings(rec_flag, sub.arena().value_bindings(*vbs))
        }
        StructureItemDesc::Tstr_primitive(vd) => sub.value_description(vd),
        StructureItemDesc::Tstr_type(rec_flag, decls) => sub.type_declarations(rec_flag, decls),
        StructureItemDesc::Tstr_typext(te) => sub.type_extension(te),
        StructureItemDesc::Tstr_exception(ext) => sub.extension_constructor(ext),
        StructureItemDesc::Tstr_module(mb) => sub.module_binding(mb),
        StructureItemDesc::Tstr_recmodule(mbs) => {
            for mb in mbs {
                sub.module_binding(mb);
            }
        }
        StructureItemDesc::Tstr_modtype(mtd) => sub.module_type_declaration(mtd),
        StructureItemDesc::Tstr_include(incl) => sub.module_expr(&incl.incl_mod),
        StructureItemDesc::Tstr_open(_) | StructureItemDesc::Tstr_attribute(_) => {}
    }
}

fn walk_constructor_args<'t, I: TastIterator<'t> + ?Sized>(
    sub: &mut I,
    args: &ConstructorArgument,
) {
    match args {
        ConstructorArgument::Cstr_tuple(types) => {
            for t in types {
                sub.typ(t);
            }
        }
        ConstructorArgument::Cstr_record(lds) => {
            for ld in lds {
                sub.typ(&ld.ld_type);
            }
        }
    }
}

pub fn walk_type_declaration<'t, I: TastIterator<'t> + ?Sized>(
    sub: &mut I,
    td: &TypedTypeDeclaration,
) {
    for (c1, c2, _) in &td.typ_cstrs {
        sub.typ(c1);
        sub.typ(c2);
    }
    sub.type_kind(&td.typ_kind);
    if let Some(m) = &td.typ_manifest {
        sub.typ(m);
    }
    for (c, _) in &td.typ_params {
        sub.typ(c);
    }
}

pub fn walk_extension_constructor<'t, I: TastIterator<'t> + ?Sized>(
    sub: &mut I,
    ext: &ExtensionConstructor,
) {
    match &ext.ext_kind {
        ExtensionConstructorKind::Text_decl(args, res) => {
            walk_constructor_args(sub, args);
            if let Some(res) = res {
                sub.typ(res);
            }
        }
        ExtensionConstructorKind::Text_rebind(..) => {}
    }
}

pub fn walk_pat<'t, I: TastIterator<'t> + ?Sized>(sub: &mut I, p: &Pattern) {
    for (extra, _, _) in p.pat_extra.iter() {
        if let PatExtra::Tpat_constraint(ct) = extra {
            sub.typ(ct);
        }
    }
    match &p.pat_desc {
        PatternDesc::Tpat_any | PatternDesc::Tpat_var(..) | PatternDesc::Tpat_constant(_) => {}
        PatternDesc::Tpat_tuple(pats)
        | PatternDesc::Tpat_construct(_, _, pats)
        | PatternDesc::Tpat_array(pats) => {
            for p in pats {
                sub.pat(p);
            }
        }
        PatternDesc::Tpat_variant(_, po, _) => {
            if let Some(p) = po {
                sub.pat(p);
            }
        }
        PatternDesc::Tpat_record(fields, _, _) => {
            for (_, _, p, _) in fields {
                sub.pat(p);
            }
        }
        PatternDesc::Tpat_or(p1, p2, _) => {
            sub.pat(p1);
            sub.pat(p2);
        }
        PatternDesc::Tpat_alias(p, _, _) => sub.pat(p),
    }
}

fn walk_record_fields<'t, I: TastIterator<'t> + ?Sized>(
    sub: &mut I,
    fields: &[RecordField],
    extended: Option<TExprIdx>,
) {
    let ta = sub.arena();
    for (_, _, def, _) in fields {
        if let RecordLabelDefinition::Overridden(_, e) = def {
            sub.expr(ta.expr(*e));
        }
    }
    if let Some(e) = extended {
        sub.expr(ta.expr(e));
    }
}

pub fn walk_expr<'t, I: TastIterator<'t> + ?Sized>(sub: &mut I, e: &Expression) {
    for (extra, _, _) in e.exp_extra.iter() {
        match extra {
            ExpExtra::Texp_constraint(ct) | ExpExtra::Texp_coerce { target: ct, .. } => sub.typ(ct),
            ExpExtra::Texp_open(..) | ExpExtra::Texp_newtype(_) => {}
        }
    }
    let ta = sub.arena();
    match &e.exp_desc {
        ExpressionDesc::Texp_ident(..)
        | ExpressionDesc::Texp_constant(_)
        | ExpressionDesc::Texp_break
        | ExpressionDesc::Texp_continue
        | ExpressionDesc::Texp_extension_constructor(..) => {}
        ExpressionDesc::Texp_let(rec_flag, vbs, body) => {
            sub.value_bindings(rec_flag, sub.arena().value_bindings(*vbs));
            sub.expr(ta.expr(*body));
        }
        ExpressionDesc::Texp_function { params, body, .. } => {
            for param in ta.function_params(*params) {
                sub.pat(&param.fp_pat);
            }
            sub.expr(ta.expr(*body));
        }
        ExpressionDesc::Texp_apply { funct, args, .. } => {
            sub.expr(ta.expr(*funct));
            for arg in ta.apply_args(*args) {
                if let Some(e) = arg.expression {
                    sub.expr(ta.expr(e));
                }
            }
        }
        ExpressionDesc::Texp_match(e, cases, exn_cases, _) => {
            sub.expr(ta.expr(*e));
            sub.cases(ta.cases(*cases));
            sub.cases(ta.cases(*exn_cases));
        }
        ExpressionDesc::Texp_try(e, cases) => {
            sub.expr(ta.expr(*e));
            sub.cases(ta.cases(*cases));
        }
        ExpressionDesc::Texp_tuple(es)
        | ExpressionDesc::Texp_construct(_, _, es)
        | ExpressionDesc::Texp_array(es) => {
            for e in ta.exprs(*es) {
                sub.expr(e);
            }
        }
        ExpressionDesc::Texp_variant(_, eo) => {
            if let Some(e) = eo {
                sub.expr(ta.expr(*e));
            }
        }
        ExpressionDesc::Texp_record {
            fields,
            extended_expression,
            ..
        }
        | ExpressionDesc::Texp_record_sparse {
            fields,
            extended_expression,
            ..
        } => walk_record_fields(sub, ta.record_fields(*fields), *extended_expression),
        ExpressionDesc::Texp_field(e, _, _) | ExpressionDesc::Texp_assert(e) => {
            sub.expr(ta.expr(*e))
        }
        ExpressionDesc::Texp_setfield(e1, _, _, e2)
        | ExpressionDesc::Texp_sequence(e1, e2)
        | ExpressionDesc::Texp_while(e1, e2)
        | ExpressionDesc::Texp_for_of(_, _, e1, e2)
        | ExpressionDesc::Texp_for_await_of(_, _, e1, e2) => {
            sub.expr(ta.expr(*e1));
            sub.expr(ta.expr(*e2));
        }
        ExpressionDesc::Texp_tagged_template { tag, values, .. } => {
            sub.expr(ta.expr(*tag));
            for value in ta.exprs(*values) {
                sub.expr(value);
            }
        }
        ExpressionDesc::Texp_template { values, .. } => {
            for value in ta.exprs(*values) {
                sub.expr(value);
            }
        }
        ExpressionDesc::Texp_ifthenelse(e1, e2, e3) => {
            sub.expr(ta.expr(*e1));
            sub.expr(ta.expr(*e2));
            if let Some(e3) = e3 {
                sub.expr(ta.expr(*e3));
            }
        }
        ExpressionDesc::Texp_for(_, _, e1, e2, _, e3) => {
            sub.expr(ta.expr(*e1));
            sub.expr(ta.expr(*e2));
            sub.expr(ta.expr(*e3));
        }
        ExpressionDesc::Texp_object_get(e, _) => sub.expr(ta.expr(*e)),
        ExpressionDesc::Texp_object_set(e, _, v) => {
            sub.expr(ta.expr(*e));
            sub.expr(ta.expr(*v));
        }
        ExpressionDesc::Texp_object_literal(fields) => {
            for (_, e) in fields {
                sub.expr(ta.expr(*e));
            }
        }
        ExpressionDesc::Texp_letmodule(_, _, m, body) => {
            sub.module_expr(m);
            sub.expr(ta.expr(*body));
        }
        ExpressionDesc::Texp_letexception(cd, body) => {
            sub.extension_constructor(cd);
            sub.expr(ta.expr(*body));
        }
        ExpressionDesc::Texp_pack(m) => sub.module_expr(m),
    }
}

pub fn walk_signature_item<'t, I: TastIterator<'t> + ?Sized>(
    sub: &mut I,
    item: &TypedSignatureItem,
) {
    match &item.sig_desc {
        TypedSignatureItemDesc::Tsig_value(vd) => sub.value_description(vd),
        TypedSignatureItemDesc::Tsig_type(rec_flag, decls) => {
            sub.type_declarations(rec_flag, decls)
        }
        TypedSignatureItemDesc::Tsig_typext(te) => sub.type_extension(te),
        TypedSignatureItemDesc::Tsig_exception(ext) => sub.extension_constructor(ext),
        TypedSignatureItemDesc::Tsig_module(md) => sub.module_declaration(md),
        TypedSignatureItemDesc::Tsig_recmodule(mds) => {
            for md in mds {
                sub.module_declaration(md);
            }
        }
        TypedSignatureItemDesc::Tsig_modtype(mtd) => sub.module_type_declaration(mtd),
        TypedSignatureItemDesc::Tsig_include(incl) => sub.module_type(&incl.incl_mod),
        TypedSignatureItemDesc::Tsig_open(_) | TypedSignatureItemDesc::Tsig_attribute(_) => {}
    }
}

pub fn walk_module_type<'t, I: TastIterator<'t> + ?Sized>(sub: &mut I, m: &ModuleType) {
    match &m.mty_desc {
        ModuleTypeDesc::Tmty_ident(..) | ModuleTypeDesc::Tmty_alias(..) => {}
        ModuleTypeDesc::Tmty_signature(sg) => sub.signature(sg),
        ModuleTypeDesc::Tmty_functor(_, _, arg, res) => {
            if let Some(arg) = arg {
                sub.module_type(arg);
            }
            sub.module_type(res);
        }
        ModuleTypeDesc::Tmty_with(mt, constraints) => {
            sub.module_type(mt);
            for (_, _, c) in constraints {
                sub.with_constraint(c);
            }
        }
        ModuleTypeDesc::Tmty_typeof(me) => sub.module_expr(me),
    }
}

pub fn walk_module_expr<'t, I: TastIterator<'t> + ?Sized>(sub: &mut I, m: &ModuleExpr) {
    match &m.mod_desc {
        ModuleExprDesc::Tmod_ident(..) => {}
        ModuleExprDesc::Tmod_structure(st) => sub.structure(st),
        ModuleExprDesc::Tmod_functor(_, _, mt, me) => {
            if let Some(mt) = mt {
                sub.module_type(mt);
            }
            sub.module_expr(me);
        }
        ModuleExprDesc::Tmod_apply(m1, m2, _) => {
            sub.module_expr(m1);
            sub.module_expr(m2);
        }
        ModuleExprDesc::Tmod_constraint(me, _, constraint, _) => {
            sub.module_expr(me);
            if let ModuleTypeConstraint::Tmodtype_explicit(mt) = constraint {
                sub.module_type(mt);
            }
        }
        ModuleExprDesc::Tmod_unpack(e, _) => {
            let ta = sub.arena();
            sub.expr(ta.expr(*e))
        }
    }
}

pub fn walk_typ<'t, I: TastIterator<'t> + ?Sized>(sub: &mut I, t: &TypedCoreType) {
    match &t.ctyp_desc {
        TypedCoreTypeDesc::Ttyp_var(_) => {}
        TypedCoreTypeDesc::Ttyp_arrow(args, ret) => {
            for arg in args {
                sub.typ(&arg.typ);
            }
            sub.typ(ret);
        }
        TypedCoreTypeDesc::Ttyp_tuple(types) | TypedCoreTypeDesc::Ttyp_constr(_, _, types) => {
            for t in types {
                sub.typ(t);
            }
        }
        TypedCoreTypeDesc::Ttyp_object(fields, _) => {
            for f in fields {
                sub.object_field(f);
            }
        }
        TypedCoreTypeDesc::Ttyp_alias(ct, _) | TypedCoreTypeDesc::Ttyp_poly(_, ct) => sub.typ(ct),
        TypedCoreTypeDesc::Ttyp_variant(fields, _, _) => {
            for f in fields {
                sub.row_field(f);
            }
        }
        TypedCoreTypeDesc::Ttyp_package(pack) => sub.package_type(pack),
    }
}
