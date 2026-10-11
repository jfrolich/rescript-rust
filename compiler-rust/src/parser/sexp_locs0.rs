//! S-expression printer for parsetree0 AST with location information
//!
//! This module produces sexp output that includes location information for
//! parsetree0 types (the frozen PPX-compatible format).
//! Matches OCaml res_ast_debugger.ml SexpAst0WithLocs output exactly.
//! Used for debugging position parity between the Rust and OCaml parsers.

use crate::binary_ast::parsetree0::*;
use crate::location::{Located, Location};
use crate::parse_arena::ParseArena;
use crate::parser::longident::Longident;
use crate::parser::sexp::{Sexp, string_to_latin1_bytes};
use std::io::Write;

// ============================================================================
// Location helpers
// ============================================================================

fn location(loc: &Location) -> Sexp {
    let start_col = loc.loc_start.cnum - loc.loc_start.bol;
    let end_col = loc.loc_end.cnum - loc.loc_end.bol;
    let mut items = vec![
        Sexp::atom("loc"),
        Sexp::atom(&loc.loc_start.line.to_string()),
        Sexp::atom(&start_col.to_string()),
        Sexp::atom(&loc.loc_end.line.to_string()),
        Sexp::atom(&end_col.to_string()),
    ];
    if loc.loc_ghost {
        items.push(Sexp::atom("ghost"));
    }
    Sexp::list(items)
}

// ============================================================================
// String quoting
// ============================================================================

fn quote_string(s: &str) -> String {
    let mut result = String::with_capacity(s.len() + 2);
    result.push('"');
    result.push_str(s);
    result.push('"');
    result
}

fn quote_string_tagged(s: &str) -> String {
    quote_string(s)
}

/// `string`: `Ext_ident.unwrap_uppercase_exotic`, then quoted.
fn string(s: &str) -> Sexp {
    let bytes = s.as_bytes();
    let unwrapped =
        if bytes.len() >= 3 && bytes[0] == b'\\' && bytes[1] == b'"' && bytes[bytes.len() - 1] == b'"' {
            &s[2..s.len() - 1]
        } else {
            s
        };
    Sexp::atom(&quote_string(unwrapped))
}

fn some_or_none(value: Option<Sexp>) -> Sexp {
    match value {
        Some(v) => Sexp::list(vec![Sexp::atom("Some"), v]),
        None => Sexp::atom("None"),
    }
}

fn map_empty<T, F>(items: &[T], f: F) -> Vec<Sexp>
where
    F: Fn(&T) -> Sexp,
{
    if items.is_empty() {
        vec![Sexp::list(vec![])]
    } else {
        items.iter().map(f).collect()
    }
}

// ============================================================================
// Longident
// ============================================================================

fn longident_inner(arena: &crate::parse_arena::ParseArena, lid: &Longident) -> Sexp {
    match lid {
        Longident::Lident(name_idx) => {
            Sexp::list(vec![Sexp::atom("Lident"), string(arena.get_string(*name_idx))])
        }
        Longident::Ldot(prefix, name_idx) => {
            Sexp::list(vec![
                Sexp::atom("Ldot"),
                longident_inner(arena, prefix),
                string(arena.get_string(*name_idx)),
            ])
        }
        Longident::Lapply(l1, l2) => Sexp::list(vec![
            Sexp::atom("Lapply"),
            longident_inner(arena, l1),
            longident_inner(arena, l2),
        ]),
    }
}

fn longident(arena: &crate::parse_arena::ParseArena, lid: &Longident) -> Sexp {
    Sexp::list(vec![Sexp::atom("longident"), longident_inner(arena, lid)])
}

// ============================================================================
// Flags
// ============================================================================

fn rec_flag(flag: &RecFlag) -> Sexp {
    Sexp::atom(match flag {
        RecFlag::Recursive => "Recursive",
        RecFlag::Nonrecursive => "Nonrecursive",
    })
}

fn closed_flag(flag: &ClosedFlag) -> Sexp {
    Sexp::atom(match flag {
        ClosedFlag::Closed => "Closed",
        ClosedFlag::Open => "Open",
    })
}

fn direction_flag(flag: &DirectionFlag) -> Sexp {
    Sexp::atom(match flag {
        DirectionFlag::Upto => "Upto",
        DirectionFlag::Downto => "Downto",
    })
}

fn override_flag(flag: &OverrideFlag) -> Sexp {
    Sexp::atom(match flag {
        OverrideFlag::Override => "Override",
        OverrideFlag::Fresh => "Fresh",
    })
}

fn private_flag(flag: &PrivateFlag) -> Sexp {
    Sexp::atom(match flag {
        PrivateFlag::Private => "Private",
        PrivateFlag::Public => "Public",
    })
}

fn mutable_flag(flag: &MutableFlag) -> Sexp {
    Sexp::atom(match flag {
        MutableFlag::Mutable => "Mutable",
        MutableFlag::Immutable => "Immutable",
    })
}

fn variance(v: &Variance) -> Sexp {
    Sexp::atom(match v {
        Variance::Covariant => "Covariant",
        Variance::Contravariant => "Contravariant",
        Variance::Invariant => "Invariant",
    })
}

// parsetree0 ArgLabel has no location (unlike current parsetree)
fn arg_label(arena: &ParseArena, lbl: &ArgLabel) -> Sexp {
    match lbl {
        ArgLabel::Nolabel => Sexp::atom("Nolabel"),
        ArgLabel::Labelled(s) => Sexp::list(vec![
            Sexp::atom("Labelled"),
            Sexp::atom(&quote_string(arena.get_string(*s))),
        ]),
        ArgLabel::Optional(s) => Sexp::list(vec![
            Sexp::atom("Optional"),
            Sexp::atom(&quote_string(arena.get_string(*s))),
        ]),
    }
}

// ============================================================================
// Constants
// ============================================================================

fn opt_char(oc: &Option<char>) -> Sexp {
    match oc {
        None => Sexp::atom("None"),
        Some(c) => Sexp::list(vec![Sexp::atom("Some"), Sexp::atom(&format!("'{}'", c))]),
    }
}

fn constant_inner(c: &Constant) -> Sexp {
    match c {
        Constant::Integer(txt, tag) => Sexp::list(vec![
            Sexp::atom("Pconst_integer"),
            Sexp::atom(&quote_string(txt)),
            opt_char(tag),
        ]),
        Constant::Char(_) => Sexp::list(vec![Sexp::atom("Pconst_char")]),
        Constant::String(txt, tag) => {
            if tag.as_ref().map(|t| t.as_str()) == Some("INTERNAL_RES_CHAR_CONTENTS") {
                Sexp::list(vec![Sexp::atom("Pconst_char")])
            } else {
                let quoted = if tag.is_some() {
                    quote_string_tagged(txt)
                } else {
                    quote_string(txt)
                };
                Sexp::list(vec![
                    Sexp::atom("Pconst_string"),
                    Sexp::atom(&quoted),
                    match tag {
                        Some(t) => {
                            Sexp::list(vec![Sexp::atom("Some"), Sexp::atom(&quote_string(t))])
                        }
                        None => Sexp::atom("None"),
                    },
                ])
            }
        }
        Constant::Float(txt, tag) => Sexp::list(vec![
            Sexp::atom("Pconst_float"),
            Sexp::atom(&quote_string(txt)),
            opt_char(tag),
        ]),
    }
}

fn constant(c: &Constant) -> Sexp {
    Sexp::list(vec![Sexp::atom("constant"), constant_inner(c)])
}

// ============================================================================
// Attributes
// ============================================================================

fn payload(arena: &ParseArena, p: &Payload) -> Sexp {
    match p {
        Payload::PStr(items) => {
            let mut parts = vec![Sexp::atom("PStr")];
            parts.extend(map_empty(items, |si| structure_item(arena, si)));
            Sexp::list(parts)
        }
        Payload::PSig(items) => Sexp::list(vec![Sexp::atom("PSig"), signature(arena, items)]),
        Payload::PTyp(ct) => Sexp::list(vec![Sexp::atom("PTyp"), core_type(arena, ct)]),
        Payload::PPat(pat, opt_expr) => Sexp::list(vec![
            Sexp::atom("PPat"),
            pattern(arena, pat),
            match opt_expr {
                Some(e) => Sexp::list(vec![Sexp::atom("Some"), expression(arena, e)]),
                None => Sexp::atom("None"),
            },
        ]),
    }
}

fn attribute(arena: &ParseArena, attr: &Attribute) -> Sexp {
    let (name, p) = attr;
    Sexp::list(vec![
        Sexp::atom("attribute"),
        Sexp::atom(&name.txt),
        location(&name.loc),
        payload(arena, p),
    ])
}

fn extension(arena: &ParseArena, ext: &Extension) -> Sexp {
    let (name, p) = ext;
    Sexp::list(vec![
        Sexp::atom("extension"),
        Sexp::atom(&name.txt),
        location(&name.loc),
        payload(arena, p),
    ])
}

fn attributes(arena: &ParseArena, attrs: &[Attribute]) -> Sexp {
    let mut parts = vec![Sexp::atom("attributes")];
    parts.extend(map_empty(attrs, |a| attribute(arena, a)));
    Sexp::list(parts)
}

// ============================================================================
// AST (res_ast_debugger.ml SexpAst0WithLocs)
// ============================================================================

fn structure(arena: &ParseArena, s: &Structure) -> Sexp {
    let mut parts = vec![Sexp::atom("structure")];
    parts.extend(s.iter().map(|si| structure_item(arena, si)));
    Sexp::list(parts)
}

fn structure_item(arena: &ParseArena, si: &StructureItem) -> Sexp {
    let desc = match &si.pstr_desc {
        StructureItemDesc::Eval(expr, attrs) => Sexp::list(vec![
            Sexp::atom("Pstr_eval"),
            expression(arena, expr),
            attributes(arena, attrs),
        ]),
        StructureItemDesc::Value(flag, vbs) => Sexp::list(vec![
            Sexp::atom("Pstr_value"),
            rec_flag(flag),
            Sexp::list(map_empty(vbs, |vb| value_binding(arena, vb))),
        ]),
        StructureItemDesc::Primitive(vd) => {
            Sexp::list(vec![Sexp::atom("Pstr_primitive"), value_description(arena, vd)])
        }
        StructureItemDesc::Type(flag, tds) => Sexp::list(vec![
            Sexp::atom("Pstr_type"),
            rec_flag(flag),
            Sexp::list(map_empty(tds, |td| type_declaration(arena, td))),
        ]),
        StructureItemDesc::Typext(te) => {
            Sexp::list(vec![Sexp::atom("Pstr_type"), type_extension(arena, te)])
        }
        StructureItemDesc::Exception(ec) => {
            Sexp::list(vec![Sexp::atom("Pstr_exception"), extension_constructor(arena, ec)])
        }
        StructureItemDesc::Module(mb) => {
            Sexp::list(vec![Sexp::atom("Pstr_module"), module_binding(arena, mb)])
        }
        StructureItemDesc::Recmodule(mbs) => Sexp::list(vec![
            Sexp::atom("Pstr_recmodule"),
            Sexp::list(map_empty(mbs, |mb| module_binding(arena, mb))),
        ]),
        StructureItemDesc::Modtype(mtd) => Sexp::list(vec![
            Sexp::atom("Pstr_modtype"),
            module_type_declaration(arena, mtd),
        ]),
        StructureItemDesc::Open(od) => {
            Sexp::list(vec![Sexp::atom("Pstr_open"), open_description(arena, od)])
        }
        StructureItemDesc::Include(id) => {
            Sexp::list(vec![Sexp::atom("Pstr_include"), include_declaration(arena, id)])
        }
        StructureItemDesc::Attribute(attr) => {
            Sexp::list(vec![Sexp::atom("Pstr_attribute"), attribute(arena, attr)])
        }
        StructureItemDesc::Extension(ext, attrs) => Sexp::list(vec![
            Sexp::atom("Pstr_extension"),
            extension(arena, ext),
            attributes(arena, attrs),
        ]),
        StructureItemDesc::Class => Sexp::atom("Pstr_class"),
        StructureItemDesc::ClassType => Sexp::atom("Pstr_class_type"),
    };
    Sexp::list(vec![Sexp::atom("structure_item"), location(&si.pstr_loc), desc])
}

fn include_declaration(arena: &ParseArena, id: &IncludeDeclaration) -> Sexp {
    Sexp::list(vec![
        Sexp::atom("include_declaration"),
        location(&id.pincl_loc),
        module_expression(arena, &id.pincl_mod),
        attributes(arena, &id.pincl_attributes),
    ])
}

fn open_description(arena: &ParseArena, od: &OpenDescription) -> Sexp {
    Sexp::list(vec![
        Sexp::atom("open_description"),
        location(&od.popen_loc),
        longident(arena, &od.popen_lid.txt),
        location(&od.popen_lid.loc),
        override_flag(&od.popen_override),
        attributes(arena, &od.popen_attributes),
    ])
}

fn module_type_declaration(arena: &ParseArena, mtd: &ModuleTypeDeclaration) -> Sexp {
    Sexp::list(vec![
        Sexp::atom("module_type_declaration"),
        location(&mtd.pmtd_loc),
        string(&mtd.pmtd_name.txt),
        location(&mtd.pmtd_name.loc),
        some_or_none(mtd.pmtd_type.as_ref().map(|mt| module_type(arena, mt))),
        attributes(arena, &mtd.pmtd_attributes),
    ])
}

fn module_binding(arena: &ParseArena, mb: &ModuleBinding) -> Sexp {
    Sexp::list(vec![
        Sexp::atom("module_binding"),
        location(&mb.pmb_loc),
        string(&mb.pmb_name.txt),
        location(&mb.pmb_name.loc),
        module_expression(arena, &mb.pmb_expr),
        attributes(arena, &mb.pmb_attributes),
    ])
}

fn module_expression(arena: &ParseArena, me: &ModuleExpr) -> Sexp {
    let desc = match &me.pmod_desc {
        ModuleExprDesc::Ident(lid) => Sexp::list(vec![
            Sexp::atom("Pmod_ident"),
            longident(arena, &lid.txt),
            location(&lid.loc),
        ]),
        ModuleExprDesc::Structure(s) => {
            Sexp::list(vec![Sexp::atom("Pmod_structure"), structure(arena, s)])
        }
        ModuleExprDesc::Functor(lbl, mt, body) => Sexp::list(vec![
            Sexp::atom("Pmod_functor"),
            string(&lbl.txt),
            location(&lbl.loc),
            some_or_none(mt.as_ref().map(|mt| module_type(arena, mt))),
            module_expression(arena, body),
        ]),
        ModuleExprDesc::Apply(f, arg) => Sexp::list(vec![
            Sexp::atom("Pmod_apply"),
            module_expression(arena, f),
            module_expression(arena, arg),
        ]),
        ModuleExprDesc::Constraint(me, mt) => Sexp::list(vec![
            Sexp::atom("Pmod_constraint"),
            module_expression(arena, me),
            module_type(arena, mt),
        ]),
        ModuleExprDesc::Unpack(e) => Sexp::list(vec![Sexp::atom("Pmod_unpack"), expression(arena, e)]),
        ModuleExprDesc::Extension(ext) => {
            Sexp::list(vec![Sexp::atom("Pmod_extension"), extension(arena, ext)])
        }
    };
    Sexp::list(vec![
        Sexp::atom("module_expr"),
        location(&me.pmod_loc),
        desc,
        attributes(arena, &me.pmod_attributes),
    ])
}

fn module_type(arena: &ParseArena, mt: &ModuleType) -> Sexp {
    let desc = match &mt.pmty_desc {
        ModuleTypeDesc::Ident(lid) => Sexp::list(vec![
            Sexp::atom("Pmty_ident"),
            longident(arena, &lid.txt),
            location(&lid.loc),
        ]),
        ModuleTypeDesc::Signature(s) => {
            Sexp::list(vec![Sexp::atom("Pmty_signature"), signature(arena, s)])
        }
        ModuleTypeDesc::Functor(lbl, arg, body) => Sexp::list(vec![
            Sexp::atom("Pmty_functor"),
            string(&lbl.txt),
            location(&lbl.loc),
            some_or_none(arg.as_ref().map(|mt| module_type(arena, mt))),
            module_type(arena, body),
        ]),
        ModuleTypeDesc::Alias(lid) => Sexp::list(vec![
            Sexp::atom("Pmty_alias"),
            longident(arena, &lid.txt),
            location(&lid.loc),
        ]),
        ModuleTypeDesc::Extension(ext) => {
            Sexp::list(vec![Sexp::atom("Pmty_extension"), extension(arena, ext)])
        }
        ModuleTypeDesc::Typeof(me) => {
            Sexp::list(vec![Sexp::atom("Pmty_typeof"), module_expression(arena, me)])
        }
        ModuleTypeDesc::With(mt, constraints) => Sexp::list(vec![
            Sexp::atom("Pmty_with"),
            module_type(arena, mt),
            Sexp::list(map_empty(constraints, |wc| with_constraint(arena, wc))),
        ]),
    };
    Sexp::list(vec![
        Sexp::atom("module_type"),
        location(&mt.pmty_loc),
        desc,
        attributes(arena, &mt.pmty_attributes),
    ])
}

fn with_constraint(arena: &ParseArena, wc: &WithConstraint) -> Sexp {
    match wc {
        // res_ast_debugger.ml prints `Pmty_with` for `Pwith_type`.
        WithConstraint::Type(lid, td) => Sexp::list(vec![
            Sexp::atom("Pmty_with"),
            longident(arena, &lid.txt),
            location(&lid.loc),
            type_declaration(arena, td),
        ]),
        WithConstraint::Module(l1, l2) => Sexp::list(vec![
            Sexp::atom("Pwith_module"),
            longident(arena, &l1.txt),
            location(&l1.loc),
            longident(arena, &l2.txt),
            location(&l2.loc),
        ]),
        WithConstraint::TypeSubst(lid, td) => Sexp::list(vec![
            Sexp::atom("Pwith_typesubst"),
            longident(arena, &lid.txt),
            location(&lid.loc),
            type_declaration(arena, td),
        ]),
        WithConstraint::ModSubst(l1, l2) => Sexp::list(vec![
            Sexp::atom("Pwith_modsubst"),
            longident(arena, &l1.txt),
            location(&l1.loc),
            longident(arena, &l2.txt),
            location(&l2.loc),
        ]),
    }
}

fn signature(arena: &ParseArena, s: &Signature) -> Sexp {
    let mut parts = vec![Sexp::atom("signature")];
    parts.extend(s.iter().map(|si| signature_item(arena, si)));
    Sexp::list(parts)
}

fn signature_item(arena: &ParseArena, si: &SignatureItem) -> Sexp {
    let desc = match &si.psig_desc {
        SignatureItemDesc::Value(vd) => {
            Sexp::list(vec![Sexp::atom("Psig_value"), value_description(arena, vd)])
        }
        SignatureItemDesc::Type(flag, tds) => Sexp::list(vec![
            Sexp::atom("Psig_type"),
            rec_flag(flag),
            Sexp::list(map_empty(tds, |td| type_declaration(arena, td))),
        ]),
        SignatureItemDesc::Typext(te) => {
            Sexp::list(vec![Sexp::atom("Psig_typext"), type_extension(arena, te)])
        }
        SignatureItemDesc::Exception(ec) => {
            Sexp::list(vec![Sexp::atom("Psig_exception"), extension_constructor(arena, ec)])
        }
        SignatureItemDesc::Module(md) => {
            Sexp::list(vec![Sexp::atom("Psig_module"), module_declaration(arena, md)])
        }
        SignatureItemDesc::Recmodule(mds) => Sexp::list(vec![
            Sexp::atom("Psig_recmodule"),
            Sexp::list(map_empty(mds, |md| module_declaration(arena, md))),
        ]),
        SignatureItemDesc::Modtype(mtd) => Sexp::list(vec![
            Sexp::atom("Psig_modtype"),
            module_type_declaration(arena, mtd),
        ]),
        SignatureItemDesc::Open(od) => {
            Sexp::list(vec![Sexp::atom("Psig_open"), open_description(arena, od)])
        }
        SignatureItemDesc::Include(id) => {
            Sexp::list(vec![Sexp::atom("Psig_include"), include_description(arena, id)])
        }
        SignatureItemDesc::Attribute(attr) => {
            Sexp::list(vec![Sexp::atom("Psig_attribute"), attribute(arena, attr)])
        }
        SignatureItemDesc::Extension(ext, attrs) => Sexp::list(vec![
            Sexp::atom("Psig_extension"),
            extension(arena, ext),
            attributes(arena, attrs),
        ]),
        SignatureItemDesc::Class => Sexp::atom("Psig_class"),
        SignatureItemDesc::ClassType => Sexp::atom("Psig_class_type"),
    };
    Sexp::list(vec![Sexp::atom("signature_item"), location(&si.psig_loc), desc])
}

fn include_description(arena: &ParseArena, id: &IncludeDescription) -> Sexp {
    Sexp::list(vec![
        Sexp::atom("include_description"),
        location(&id.pincl_loc),
        module_type(arena, &id.pincl_mod),
        attributes(arena, &id.pincl_attributes),
    ])
}

fn module_declaration(arena: &ParseArena, md: &ModuleDeclaration) -> Sexp {
    Sexp::list(vec![
        Sexp::atom("module_declaration"),
        location(&md.pmd_loc),
        string(&md.pmd_name.txt),
        location(&md.pmd_name.loc),
        module_type(arena, &md.pmd_type),
        attributes(arena, &md.pmd_attributes),
    ])
}

fn value_binding(arena: &ParseArena, vb: &ValueBinding) -> Sexp {
    Sexp::list(vec![
        Sexp::atom("value_binding"),
        location(&vb.pvb_loc),
        pattern(arena, &vb.pvb_pat),
        expression(arena, &vb.pvb_expr),
        attributes(arena, &vb.pvb_attributes),
    ])
}

fn value_description(arena: &ParseArena, vd: &ValueDescription) -> Sexp {
    Sexp::list(vec![
        Sexp::atom("value_description"),
        location(&vd.pval_loc),
        string(&vd.pval_name.txt),
        location(&vd.pval_name.loc),
        core_type(arena, &vd.pval_type),
        Sexp::list(map_empty(&vd.pval_prim, |p| string(p))),
        attributes(arena, &vd.pval_attributes),
    ])
}

fn type_declaration(arena: &ParseArena, td: &TypeDeclaration) -> Sexp {
    Sexp::list(vec![
        Sexp::atom("type_declaration"),
        location(&td.ptype_loc),
        string(&td.ptype_name.txt),
        location(&td.ptype_name.loc),
        Sexp::list(vec![
            Sexp::atom("ptype_params"),
            Sexp::list(map_empty(&td.ptype_params, |(t, v)| {
                Sexp::list(vec![core_type(arena, t), variance(v)])
            })),
        ]),
        Sexp::list(vec![
            Sexp::atom("ptype_cstrs"),
            Sexp::list(map_empty(&td.ptype_cstrs, |(t1, t2, loc)| {
                Sexp::list(vec![core_type(arena, t1), core_type(arena, t2), location(loc)])
            })),
        ]),
        Sexp::list(vec![Sexp::atom("ptype_kind"), type_kind(arena, &td.ptype_kind)]),
        Sexp::list(vec![
            Sexp::atom("ptype_manifest"),
            some_or_none(td.ptype_manifest.as_ref().map(|t| core_type(arena, t))),
        ]),
        Sexp::list(vec![Sexp::atom("ptype_private"), private_flag(&td.ptype_private)]),
        attributes(arena, &td.ptype_attributes),
    ])
}

fn extension_constructor(arena: &ParseArena, ec: &ExtensionConstructor) -> Sexp {
    Sexp::list(vec![
        Sexp::atom("extension_constructor"),
        location(&ec.pext_loc),
        string(&ec.pext_name.txt),
        location(&ec.pext_name.loc),
        extension_constructor_kind(arena, &ec.pext_kind),
        attributes(arena, &ec.pext_attributes),
    ])
}

fn extension_constructor_kind(arena: &ParseArena, kind: &ExtensionConstructorKind) -> Sexp {
    match kind {
        ExtensionConstructorKind::Decl(args, res) => Sexp::list(vec![
            Sexp::atom("Pext_decl"),
            constructor_arguments(arena, args),
            some_or_none(res.as_ref().map(|t| core_type(arena, t))),
        ]),
        ExtensionConstructorKind::Rebind(lid) => Sexp::list(vec![
            Sexp::atom("Pext_rebind"),
            longident(arena, &lid.txt),
            location(&lid.loc),
        ]),
    }
}

fn type_extension(arena: &ParseArena, te: &TypeExtension) -> Sexp {
    Sexp::list(vec![
        Sexp::atom("type_extension"),
        Sexp::list(vec![
            Sexp::atom("ptyext_path"),
            longident(arena, &te.ptyext_path.txt),
            location(&te.ptyext_path.loc),
        ]),
        Sexp::list(vec![
            Sexp::atom("ptyext_parms"),
            Sexp::list(map_empty(&te.ptyext_params, |(t, v)| {
                Sexp::list(vec![core_type(arena, t), variance(v)])
            })),
        ]),
        Sexp::list(vec![
            Sexp::atom("ptyext_constructors"),
            Sexp::list(map_empty(&te.ptyext_constructors, |ec| extension_constructor(arena, ec))),
        ]),
        Sexp::list(vec![Sexp::atom("ptyext_private"), private_flag(&te.ptyext_private)]),
        attributes(arena, &te.ptyext_attributes),
    ])
}

fn type_kind(arena: &ParseArena, kind: &TypeKind) -> Sexp {
    match kind {
        TypeKind::Abstract => Sexp::atom("Ptype_abstract"),
        TypeKind::Variant(cds) => Sexp::list(vec![
            Sexp::atom("Ptype_variant"),
            Sexp::list(map_empty(cds, |cd| constructor_declaration(arena, cd))),
        ]),
        TypeKind::Record(lds) => Sexp::list(vec![
            Sexp::atom("Ptype_record"),
            Sexp::list(map_empty(lds, |ld| label_declaration(arena, ld))),
        ]),
        TypeKind::Open => Sexp::atom("Ptype_open"),
    }
}

fn constructor_declaration(arena: &ParseArena, cd: &ConstructorDeclaration) -> Sexp {
    Sexp::list(vec![
        Sexp::atom("constructor_declaration"),
        location(&cd.pcd_loc),
        string(&cd.pcd_name.txt),
        location(&cd.pcd_name.loc),
        Sexp::list(vec![Sexp::atom("pcd_args"), constructor_arguments(arena, &cd.pcd_args)]),
        Sexp::list(vec![
            Sexp::atom("pcd_res"),
            some_or_none(cd.pcd_res.as_ref().map(|t| core_type(arena, t))),
        ]),
        attributes(arena, &cd.pcd_attributes),
    ])
}

fn constructor_arguments(arena: &ParseArena, args: &ConstructorArguments) -> Sexp {
    match args {
        ConstructorArguments::Tuple(types) => Sexp::list(vec![
            Sexp::atom("Pcstr_tuple"),
            Sexp::list(map_empty(types, |t| core_type(arena, t))),
        ]),
        ConstructorArguments::Record(lds) => Sexp::list(vec![
            Sexp::atom("Pcstr_record"),
            Sexp::list(map_empty(lds, |ld| label_declaration(arena, ld))),
        ]),
    }
}

fn label_declaration(arena: &ParseArena, ld: &LabelDeclaration) -> Sexp {
    Sexp::list(vec![
        Sexp::atom("label_declaration"),
        location(&ld.pld_loc),
        string(&ld.pld_name.txt),
        location(&ld.pld_name.loc),
        mutable_flag(&ld.pld_mutable),
        core_type(arena, &ld.pld_type),
        attributes(arena, &ld.pld_attributes),
    ])
}

fn expression(arena: &ParseArena, expr: &Expression) -> Sexp {
    let opt_expr = |e: &Option<Box<Expression>>| some_or_none(e.as_ref().map(|e| expression(arena, e)));
    let desc = match &expr.pexp_desc {
        ExpressionDesc::Ident(lid) => Sexp::list(vec![
            Sexp::atom("Pexp_ident"),
            longident(arena, &lid.txt),
            location(&lid.loc),
        ]),
        ExpressionDesc::Constant(c) => Sexp::list(vec![Sexp::atom("Pexp_constant"), constant(c)]),
        ExpressionDesc::Let(flag, vbs, body) => Sexp::list(vec![
            Sexp::atom("Pexp_let"),
            rec_flag(flag),
            Sexp::list(map_empty(vbs, |vb| value_binding(arena, vb))),
            expression(arena, body),
        ]),
        ExpressionDesc::Function(cases) => Sexp::list(vec![
            Sexp::atom("Pexp_function"),
            Sexp::list(map_empty(cases, |c| case(arena, c))),
        ]),
        ExpressionDesc::Fun(lbl, default, pat, body) => Sexp::list(vec![
            Sexp::atom("Pexp_fun"),
            arg_label(arena, lbl),
            opt_expr(default),
            pattern(arena, pat),
            expression(arena, body),
        ]),
        ExpressionDesc::Apply(funct, args) => Sexp::list(vec![
            Sexp::atom("Pexp_apply"),
            expression(arena, funct),
            Sexp::list(map_empty(args, |(lbl, e)| {
                Sexp::list(vec![arg_label(arena, lbl), expression(arena, e)])
            })),
        ]),
        ExpressionDesc::New(_) => Sexp::atom("Pexp_new"),
        ExpressionDesc::Setinstvar(..) => Sexp::atom("Pexp_setinstvar"),
        ExpressionDesc::Override(_) => Sexp::atom("Pexp_override"),
        ExpressionDesc::Lazy(e) => Sexp::list(vec![Sexp::atom("Pexp_lazy"), expression(arena, e)]),
        ExpressionDesc::Poly(..) => Sexp::atom("Pexp_poly"),
        ExpressionDesc::Object => Sexp::atom("Pexp_object"),
        ExpressionDesc::Match(e, cases) => Sexp::list(vec![
            Sexp::atom("Pexp_match"),
            expression(arena, e),
            Sexp::list(map_empty(cases, |c| case(arena, c))),
        ]),
        ExpressionDesc::Try(e, cases) => Sexp::list(vec![
            Sexp::atom("Pexp_try"),
            expression(arena, e),
            Sexp::list(map_empty(cases, |c| case(arena, c))),
        ]),
        ExpressionDesc::Tuple(es) => Sexp::list(vec![
            Sexp::atom("Pexp_tuple"),
            Sexp::list(map_empty(es, |e| expression(arena, e))),
        ]),
        ExpressionDesc::Construct(lid, arg) => Sexp::list(vec![
            Sexp::atom("Pexp_construct"),
            longident(arena, &lid.txt),
            location(&lid.loc),
            opt_expr(arg),
        ]),
        ExpressionDesc::Variant(lbl, arg) => Sexp::list(vec![
            Sexp::atom("Pexp_variant"),
            string(lbl),
            opt_expr(arg),
        ]),
        ExpressionDesc::Record(rows, spread) => Sexp::list(vec![
            Sexp::atom("Pexp_record"),
            Sexp::list(map_empty(rows, |(lid, e)| {
                Sexp::list(vec![longident(arena, &lid.txt), location(&lid.loc), expression(arena, e)])
            })),
            opt_expr(spread),
        ]),
        ExpressionDesc::Field(e, lid) => Sexp::list(vec![
            Sexp::atom("Pexp_field"),
            expression(arena, e),
            longident(arena, &lid.txt),
            location(&lid.loc),
        ]),
        ExpressionDesc::Setfield(e1, lid, e2) => Sexp::list(vec![
            Sexp::atom("Pexp_setfield"),
            expression(arena, e1),
            longident(arena, &lid.txt),
            location(&lid.loc),
            expression(arena, e2),
        ]),
        ExpressionDesc::Array(es) => Sexp::list(vec![
            Sexp::atom("Pexp_array"),
            Sexp::list(map_empty(es, |e| expression(arena, e))),
        ]),
        ExpressionDesc::Ifthenelse(e1, e2, e3) => Sexp::list(vec![
            Sexp::atom("Pexp_ifthenelse"),
            expression(arena, e1),
            expression(arena, e2),
            opt_expr(e3),
        ]),
        ExpressionDesc::Sequence(e1, e2) => Sexp::list(vec![
            Sexp::atom("Pexp_sequence"),
            expression(arena, e1),
            expression(arena, e2),
        ]),
        ExpressionDesc::While(e1, e2) => Sexp::list(vec![
            Sexp::atom("Pexp_while"),
            expression(arena, e1),
            expression(arena, e2),
        ]),
        ExpressionDesc::For(pat, e1, e2, flag, e3) => Sexp::list(vec![
            Sexp::atom("Pexp_for"),
            pattern(arena, pat),
            expression(arena, e1),
            expression(arena, e2),
            direction_flag(flag),
            expression(arena, e3),
        ]),
        ExpressionDesc::Constraint(e, t) => Sexp::list(vec![
            Sexp::atom("Pexp_constraint"),
            expression(arena, e),
            core_type(arena, t),
        ]),
        ExpressionDesc::Coerce(e, (), t) => Sexp::list(vec![
            Sexp::atom("Pexp_coerce"),
            expression(arena, e),
            core_type(arena, t),
        ]),
        ExpressionDesc::Send(e, method) => Sexp::list(vec![
            Sexp::atom("Pexp_send"),
            string(&method.txt),
            location(&method.loc),
            expression(arena, e),
        ]),
        ExpressionDesc::Letmodule(name, me, body) => Sexp::list(vec![
            Sexp::atom("Pexp_letmodule"),
            string(&name.txt),
            location(&name.loc),
            module_expression(arena, me),
            expression(arena, body),
        ]),
        ExpressionDesc::Letexception(ec, body) => Sexp::list(vec![
            Sexp::atom("Pexp_letexception"),
            extension_constructor(arena, ec),
            expression(arena, body),
        ]),
        ExpressionDesc::Assert(e) => Sexp::list(vec![Sexp::atom("Pexp_assert"), expression(arena, e)]),
        ExpressionDesc::Pack(me) => {
            Sexp::list(vec![Sexp::atom("Pexp_pack"), module_expression(arena, me)])
        }
        ExpressionDesc::Open(flag, lid, body) => Sexp::list(vec![
            Sexp::atom("Pexp_open"),
            override_flag(flag),
            longident(arena, &lid.txt),
            location(&lid.loc),
            expression(arena, body),
        ]),
        ExpressionDesc::Extension(ext) => {
            Sexp::list(vec![Sexp::atom("Pexp_extension"), extension(arena, ext)])
        }
        ExpressionDesc::Newtype(name, body) => Sexp::list(vec![
            Sexp::atom("Pexp_newtype"),
            string(&name.txt),
            location(&name.loc),
            expression(arena, body),
        ]),
        ExpressionDesc::Unreachable => Sexp::atom("Pexp_unreachable"),
    };
    Sexp::list(vec![
        Sexp::atom("expression"),
        location(&expr.pexp_loc),
        desc,
        attributes(arena, &expr.pexp_attributes),
    ])
}

fn case(arena: &ParseArena, c: &Case) -> Sexp {
    Sexp::list(vec![
        Sexp::atom("case"),
        Sexp::list(vec![Sexp::atom("pc_lhs"), pattern(arena, &c.pc_lhs)]),
        Sexp::list(vec![
            Sexp::atom("pc_guard"),
            some_or_none(c.pc_guard.as_ref().map(|e| expression(arena, e))),
        ]),
        Sexp::list(vec![Sexp::atom("pc_rhs"), expression(arena, &c.pc_rhs)]),
    ])
}

fn pattern(arena: &ParseArena, p: &Pattern) -> Sexp {
    let opt_pat = |p: &Option<Box<Pattern>>, some: &str| match p {
        Some(p) => Sexp::list(vec![Sexp::atom(some), pattern(arena, p)]),
        None => Sexp::atom("None"),
    };
    let desc = match &p.ppat_desc {
        PatternDesc::Any => Sexp::atom("Ppat_any"),
        PatternDesc::Var(v) => {
            Sexp::list(vec![Sexp::atom("Ppat_var"), string(&v.txt), location(&v.loc)])
        }
        PatternDesc::Alias(p, alias) => Sexp::list(vec![
            Sexp::atom("Ppat_alias"),
            pattern(arena, p),
            string(&alias.txt),
            location(&alias.loc),
        ]),
        PatternDesc::Constant(c) => Sexp::list(vec![Sexp::atom("Ppat_constant"), constant(c)]),
        PatternDesc::Interval(lo, hi) => {
            Sexp::list(vec![Sexp::atom("Ppat_interval"), constant(lo), constant(hi)])
        }
        PatternDesc::Tuple(ps) => Sexp::list(vec![
            Sexp::atom("Ppat_tuple"),
            Sexp::list(map_empty(ps, |p| pattern(arena, p))),
        ]),
        PatternDesc::Construct(lid, arg) => Sexp::list(vec![
            Sexp::atom("Ppat_construct"),
            longident(arena, &lid.txt),
            location(&lid.loc),
            opt_pat(arg, "some"),
        ]),
        PatternDesc::Variant(lbl, arg) => Sexp::list(vec![
            Sexp::atom("Ppat_variant"),
            string(lbl),
            opt_pat(arg, "Some"),
        ]),
        PatternDesc::Record(rows, flag) => Sexp::list(vec![
            Sexp::atom("Ppat_record"),
            closed_flag(flag),
            Sexp::list(map_empty(rows, |(lid, p)| {
                Sexp::list(vec![longident(arena, &lid.txt), location(&lid.loc), pattern(arena, p)])
            })),
        ]),
        PatternDesc::Array(ps) => Sexp::list(vec![
            Sexp::atom("Ppat_array"),
            Sexp::list(map_empty(ps, |p| pattern(arena, p))),
        ]),
        PatternDesc::Or(p1, p2) => {
            Sexp::list(vec![Sexp::atom("Ppat_or"), pattern(arena, p1), pattern(arena, p2)])
        }
        PatternDesc::Constraint(p, t) => Sexp::list(vec![
            Sexp::atom("Ppat_constraint"),
            pattern(arena, p),
            core_type(arena, t),
        ]),
        PatternDesc::Type(lid) => Sexp::list(vec![
            Sexp::atom("Ppat_type"),
            longident(arena, &lid.txt),
            location(&lid.loc),
        ]),
        PatternDesc::Lazy(p) => Sexp::list(vec![Sexp::atom("Ppat_lazy"), pattern(arena, p)]),
        PatternDesc::Unpack(s) => {
            Sexp::list(vec![Sexp::atom("Ppat_unpack"), string(&s.txt), location(&s.loc)])
        }
        PatternDesc::Exception(p) => {
            Sexp::list(vec![Sexp::atom("Ppat_exception"), pattern(arena, p)])
        }
        PatternDesc::Extension(ext) => {
            Sexp::list(vec![Sexp::atom("Ppat_extension"), extension(arena, ext)])
        }
        PatternDesc::Open(lid, p) => Sexp::list(vec![
            Sexp::atom("Ppat_open"),
            longident(arena, &lid.txt),
            location(&lid.loc),
            pattern(arena, p),
        ]),
    };
    Sexp::list(vec![
        Sexp::atom("pattern"),
        location(&p.ppat_loc),
        desc,
        attributes(arena, &p.ppat_attributes),
    ])
}

fn object_field(arena: &ParseArena, field: &ObjectField) -> Sexp {
    match field {
        ObjectField::Otag(lbl, attrs, t) => Sexp::list(vec![
            Sexp::atom("Otag"),
            string(&lbl.txt),
            location(&lbl.loc),
            attributes(arena, attrs),
            core_type(arena, t),
        ]),
        ObjectField::Oinherit(t) => Sexp::list(vec![Sexp::atom("Oinherit"), core_type(arena, t)]),
    }
}

fn row_field(arena: &ParseArena, field: &RowField) -> Sexp {
    match field {
        RowField::Rtag(lbl, attrs, truth, types) => Sexp::list(vec![
            Sexp::atom("Rtag"),
            string(&lbl.txt),
            location(&lbl.loc),
            attributes(arena, attrs),
            Sexp::atom(if *truth { "true" } else { "false" }),
            Sexp::list(map_empty(types, |t| core_type(arena, t))),
        ]),
        RowField::Rinherit(t) => Sexp::list(vec![Sexp::atom("Rinherit"), core_type(arena, t)]),
    }
}

fn package_type(arena: &ParseArena, (lid, constraints): &PackageType) -> Sexp {
    Sexp::list(vec![
        Sexp::atom("package_type"),
        longident(arena, &lid.txt),
        location(&lid.loc),
        Sexp::list(map_empty(constraints, |(lid, t)| {
            Sexp::list(vec![longident(arena, &lid.txt), location(&lid.loc), core_type(arena, t)])
        })),
    ])
}

fn core_type(arena: &ParseArena, t: &CoreType) -> Sexp {
    let desc = match &t.ptyp_desc {
        CoreTypeDesc::Any => Sexp::atom("Ptyp_any"),
        CoreTypeDesc::Var(v) => Sexp::list(vec![Sexp::atom("Ptyp_var"), string(v)]),
        CoreTypeDesc::Arrow(lbl, arg, ret) => Sexp::list(vec![
            Sexp::atom("Ptyp_arrow"),
            arg_label(arena, lbl),
            core_type(arena, arg),
            core_type(arena, ret),
        ]),
        CoreTypeDesc::Tuple(ts) => Sexp::list(vec![
            Sexp::atom("Ptyp_tuple"),
            Sexp::list(map_empty(ts, |t| core_type(arena, t))),
        ]),
        CoreTypeDesc::Constr(lid, ts) => Sexp::list(vec![
            Sexp::atom("Ptyp_constr"),
            longident(arena, &lid.txt),
            location(&lid.loc),
            Sexp::list(map_empty(ts, |t| core_type(arena, t))),
        ]),
        CoreTypeDesc::Alias(t, alias) => {
            Sexp::list(vec![Sexp::atom("Ptyp_alias"), core_type(arena, t), string(alias)])
        }
        CoreTypeDesc::Object(fields, flag) => Sexp::list(vec![
            Sexp::atom("Ptyp_object"),
            closed_flag(flag),
            Sexp::list(map_empty(fields, |f| object_field(arena, f))),
        ]),
        CoreTypeDesc::Class => Sexp::atom("Ptyp_class"),
        CoreTypeDesc::Variant(rows, flag, labels) => Sexp::list(vec![
            Sexp::atom("Ptyp_variant"),
            Sexp::list(map_empty(rows, |r| row_field(arena, r))),
            closed_flag(flag),
            match labels {
                None => Sexp::atom("None"),
                Some(labels) => Sexp::list(map_empty(labels, |l| string(l))),
            },
        ]),
        CoreTypeDesc::Poly(vars, t) => Sexp::list(vec![
            Sexp::atom("Ptyp_poly"),
            Sexp::list(map_empty(vars, |v| Sexp::list(vec![string(&v.txt), location(&v.loc)]))),
            core_type(arena, t),
        ]),
        CoreTypeDesc::Package(pkg) => {
            Sexp::list(vec![Sexp::atom("Ptyp_package"), package_type(arena, pkg)])
        }
        CoreTypeDesc::Extension(ext) => {
            Sexp::list(vec![Sexp::atom("Ptyp_extension"), extension(arena, ext)])
        }
    };
    Sexp::list(vec![
        Sexp::atom("core_type"),
        location(&t.ptyp_loc),
        desc,
        attributes(arena, &t.ptyp_attributes),
    ])
}

// ============================================================================
// Public API
// ============================================================================

/// Print a structure (parsetree0) to sexp format with locations
pub fn print_structure(arena: &ParseArena, str: &Structure, out: &mut impl Write) {
    let sexp = structure(arena, str);
    let bytes = string_to_latin1_bytes(&sexp.to_string());
    let _ = out.write_all(&bytes);
}

/// Print a signature (parsetree0) to sexp format with locations
pub fn print_signature(arena: &ParseArena, sig: &Signature, out: &mut impl Write) {
    let sexp = signature(arena, sig);
    let bytes = string_to_latin1_bytes(&sexp.to_string());
    let _ = out.write_all(&bytes);
}
