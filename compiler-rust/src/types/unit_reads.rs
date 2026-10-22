//! What a compiled module read of other units, from its typed tree: every
//! path rooted at a unit (values, constructors, labels, types, module types,
//! modules used as a whole), and every type the typed tree carries. Paired
//! with [`crate::cmi::item_deps::resolve_reads`], which closes these over the
//! declarations they reach.

use super::context::TypeContext;
use super::decl::{ConstructorDescription, ConstructorKind, LabelDescription};
use super::tast_iterator::{self as ti, TastIterator};
use super::type_expr::{TypeDesc, TypeExprRef};
use super::typedtree::*;
use crate::cmi::item_deps::{Kind, UnitRead, read_of_path};
use crate::types::path::Path;

struct Collector<'a> {
    ctx: &'a TypeContext,
    seen: ahash::AHashSet<TypeExprRef>,
    out: Vec<UnitRead>,
}

impl Collector<'_> {
    fn path(&mut self, path: &Path, kind: Kind) {
        read_of_path(path, kind, None, &mut self.out);
    }

    fn ty(&mut self, root: TypeExprRef) {
        let mut stack = vec![root];
        while let Some(ty) = stack.pop() {
            if !self.seen.insert(ty) {
                continue;
            }
            {
                let desc = self.ctx.borrow_desc(ty);
                match &*desc {
                    TypeDesc::Tconstr { path, .. } => {
                        read_of_path(path, Kind::Type, None, &mut self.out)
                    }
                    TypeDesc::Tpackage { path, .. } => {
                        read_of_path(path, Kind::Modtype, None, &mut self.out)
                    }
                    TypeDesc::Tvariant(row) => {
                        // `iter_type_expr` visits the row fields.
                        if let Some((path, _)) = &row.row_name {
                            read_of_path(path, Kind::Type, None, &mut self.out);
                        }
                    }
                    _ => {}
                }
            }
            super::btype::iter_type_expr(self.ctx, ty, |child| stack.push(child));
        }
    }

    fn constructor(&mut self, cd: &ConstructorDescription) {
        if let ConstructorKind::Extension(path) = &cd.cstr_kind {
            self.path(path, Kind::Extension);
        }
        self.ty(cd.cstr_res);
        for arg in &cd.cstr_args {
            self.ty(*arg);
        }
    }

    fn label(&mut self, ld: &LabelDescription) {
        self.ty(ld.lbl_res);
        self.ty(ld.lbl_arg);
    }
}

impl TastIterator for Collector<'_> {
    fn expr(&mut self, e: &Expression) {
        for (extra, _, _) in e.exp_extra.iter() {
            if let ExpExtra::Texp_open(_, path, _, _) = extra {
                self.path(path, Kind::Module);
            }
        }
        match &e.exp_desc {
            ExpressionDesc::Texp_ident(path, _, _) => self.path(path, Kind::Value),
            ExpressionDesc::Texp_construct(_, cd, _) => self.constructor(cd),
            ExpressionDesc::Texp_field(_, _, ld) | ExpressionDesc::Texp_setfield(_, _, ld, _) => {
                self.label(ld)
            }
            ExpressionDesc::Texp_record { fields, .. }
            | ExpressionDesc::Texp_record_sparse { fields, .. } => {
                for (_, ld, _, _) in fields {
                    self.label(ld);
                }
            }
            ExpressionDesc::Texp_extension_constructor(_, path) => self.path(path, Kind::Extension),
            _ => {}
        }
        self.ty(e.exp_type);
        ti::walk_expr(self, e);
    }

    fn pat(&mut self, p: &Pattern) {
        for (extra, _, _) in p.pat_extra.iter() {
            if let PatExtra::Tpat_type(path, _) = extra {
                self.path(path, Kind::Type);
            }
        }
        match &p.pat_desc {
            PatternDesc::Tpat_construct(_, cd, _) => self.constructor(cd),
            PatternDesc::Tpat_record(fields, _, rest) => {
                for (_, ld, _, _) in fields {
                    self.label(ld);
                }
                if let Some(rest) = rest {
                    self.ty(rest.rest_type);
                }
            }
            _ => {}
        }
        self.ty(p.pat_type);
        ti::walk_pat(self, p);
    }

    fn typ(&mut self, t: &TypedCoreType) {
        match &t.ctyp_desc {
            TypedCoreTypeDesc::Ttyp_constr(path, _, _) => self.path(path, Kind::Type),
            TypedCoreTypeDesc::Ttyp_package(pack) => self.path(&pack.pack_path, Kind::Modtype),
            _ => {}
        }
        self.ty(t.ctyp_type);
        ti::walk_typ(self, t);
    }

    fn module_expr(&mut self, m: &ModuleExpr) {
        if let ModuleExprDesc::Tmod_ident(path, _) = &m.mod_desc {
            self.path(path, Kind::Module);
        }
        ti::walk_module_expr(self, m);
    }

    fn module_type(&mut self, m: &ModuleType) {
        match &m.mty_desc {
            ModuleTypeDesc::Tmty_ident(path, _) => self.path(path, Kind::Modtype),
            ModuleTypeDesc::Tmty_alias(path, _) => self.path(path, Kind::Module),
            ModuleTypeDesc::Tmty_with(_, constraints) => {
                for (_, _, constraint) in constraints {
                    if let WithConstraint::Twith_module(path, _)
                    | WithConstraint::Twith_modsubst(path, _) = constraint
                    {
                        self.path(path, Kind::Module);
                    }
                }
            }
            _ => {}
        }
        ti::walk_module_type(self, m);
    }

    fn structure_item(&mut self, item: &StructureItem) {
        match &item.str_desc {
            StructureItemDesc::Tstr_open(od) => self.path(&od.open_path, Kind::Module),
            StructureItemDesc::Tstr_typext(te) => self.path(&te.tyext_path, Kind::Type),
            _ => {}
        }
        ti::walk_structure_item(self, item);
    }

    fn signature_item(&mut self, item: &TypedSignatureItem) {
        match &item.sig_desc {
            TypedSignatureItemDesc::Tsig_open(od) => self.path(&od.open_path, Kind::Module),
            TypedSignatureItemDesc::Tsig_typext(te) => self.path(&te.tyext_path, Kind::Type),
            _ => {}
        }
        ti::walk_signature_item(self, item);
    }

    fn extension_constructor(&mut self, ext: &ExtensionConstructor) {
        if let ExtensionConstructorKind::Text_rebind(path, _) = &ext.ext_kind {
            self.path(path, Kind::Extension);
        }
        ti::walk_extension_constructor(self, ext);
    }
}

fn opened(opens: &[String]) -> impl Iterator<Item = UnitRead> + '_ {
    opens.iter().map(|unit| UnitRead {
        unit: unit.clone(),
        segs: Vec::new(),
        kind: Kind::Module,
    })
}

/// The reads of an implementation; `opens` are the units opened by the
/// command line (read as whole modules).
pub fn structure_reads(
    ctx: &TypeContext,
    structure: &Structure,
    opens: &[String],
) -> Vec<UnitRead> {
    let mut collector = Collector {
        ctx,
        seen: ahash::AHashSet::new(),
        out: opened(opens).collect(),
    };
    collector.structure(structure);
    collector.out
}

/// The reads of an interface.
pub fn signature_reads(
    ctx: &TypeContext,
    signature: &TypedSignature,
    opens: &[String],
) -> Vec<UnitRead> {
    let mut collector = Collector {
        ctx,
        seen: ahash::AHashSet::new(),
        out: opened(opens).collect(),
    };
    collector.signature(signature);
    collector.out
}
