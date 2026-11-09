//! What a compiled module read of other units, from its typed tree: every
//! path rooted at a unit (values, constructors, labels, types, module types,
//! modules used as a whole), and every type the typed tree carries. Paired
//! with [`crate::cmi::item_deps::resolve_reads`], which closes these over the
//! declarations they reach.

use super::context::TypeContext;
use super::decl::{ConstructorDescription, ConstructorKind, LabelDescription};
use super::tast_iterator::{self as ti, TastIterator};
use super::type_expr::{SHARED_REF_BITS, SHARED_REF_TAG, STORE_REF_TAG, TypeDesc, TypeExprRef};
use super::typedtree::*;
use crate::cmi::item_deps::{Kind, UnitRead, read_of_path};
use crate::types::path::Path;

/// Visited type nodes: one bitset per reference space (local arena,
/// per-thread store, shared store), indexed by node index.
#[derive(Default)]
struct SeenTypes {
    spaces: [Vec<u64>; 3],
}

impl SeenTypes {
    /// Mark `ty`; false when it was already marked.
    #[inline]
    fn insert(&mut self, ty: TypeExprRef) -> bool {
        let raw = ty.0;
        let (space, index) = if raw & STORE_REF_TAG == 0 {
            (0, raw)
        } else if raw & SHARED_REF_TAG == 0 {
            (1, raw & !SHARED_REF_BITS)
        } else {
            (2, raw & !SHARED_REF_BITS)
        };
        let index = index as usize;
        let bits = &mut self.spaces[space];
        let word = index / 64;
        if word >= bits.len() {
            bits.resize((word + 1).max(bits.len() * 2), 0);
        }
        let mask = 1u64 << (index % 64);
        let fresh = bits[word] & mask == 0;
        bits[word] |= mask;
        fresh
    }
}

struct Collector<'a> {
    ctx: &'a TypeContext,
    ta: &'a TypedArena,
    seen: SeenTypes,
    out: Vec<UnitRead>,
}

impl Collector<'_> {
    fn path(&mut self, path: &Path, kind: Kind) {
        read_of_path(path, kind, None, &mut self.out);
    }

    fn ty(&mut self, root: TypeExprRef) {
        let ctx = self.ctx;
        let mut stack = vec![root];
        while let Some(ty) = stack.pop() {
            if !self.seen.insert(ty) {
                continue;
            }
            // The children are those `btype::iter_type_expr` visits; only a
            // variant goes through it, for its row walk.
            let desc = ctx.borrow_desc(ty);
            match &*desc {
                TypeDesc::Tconstr { path, args, .. } => {
                    read_of_path(path, Kind::Type, None, &mut self.out);
                    stack.extend(ctx.type_list(args).iter());
                }
                TypeDesc::Tpackage { path, args, .. } => {
                    read_of_path(path, Kind::Modtype, None, &mut self.out);
                    stack.extend(ctx.type_list(args).iter());
                }
                TypeDesc::Tarrow { args, ret } => {
                    stack.extend(ctx.type_args(args).iter().map(|arg| arg.typ));
                    stack.push(*ret);
                }
                TypeDesc::Ttuple(types) => stack.extend(ctx.type_list(types).iter()),
                TypeDesc::Tobject { fields } => stack.push(*fields),
                TypeDesc::Tfield { typ, rest, .. } => {
                    stack.push(*typ);
                    stack.push(*rest);
                }
                TypeDesc::Tlink(t) | TypeDesc::Tsubst(t) => stack.push(*t),
                TypeDesc::Tpoly { body, vars } => {
                    stack.push(*body);
                    stack.extend(ctx.type_list(vars).iter());
                }
                TypeDesc::Tvar(_) | TypeDesc::Tunivar(_) | TypeDesc::Tnil => {}
                TypeDesc::Tvariant(row) => {
                    let row = &ctx.row_desc(row);
                    if let Some((path, _)) = &row.row_name {
                        read_of_path(path, Kind::Type, None, &mut self.out);
                    }
                    drop(desc);
                    super::btype::iter_type_expr(ctx, ty, |child| stack.push(child));
                }
            }
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

impl<'a> TastIterator<'a> for Collector<'a> {
    fn arena(&self) -> &'a TypedArena {
        self.ta
    }

    fn expr(&mut self, e: &Expression) {
        for (extra, _, _) in self.ta.exp_extra(e).iter() {
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
                for (_, ld, _, _) in self.ta.record_fields(*fields) {
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
        for (extra, _, _) in self.ta.pat_extra(p).iter() {
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
    ta: &TypedArena,
    structure: &Structure,
    opens: &[String],
) -> Vec<UnitRead> {
    let mut collector = Collector {
        ctx,
        ta,
        seen: SeenTypes::default(),
        out: opened(opens).collect(),
    };
    collector.structure(structure);
    collector.out
}

/// The reads of an interface.
pub fn signature_reads(
    ctx: &TypeContext,
    ta: &TypedArena,
    signature: &TypedSignature,
    opens: &[String],
) -> Vec<UnitRead> {
    let mut collector = Collector {
        ctx,
        ta,
        seen: SeenTypes::default(),
        out: opened(opens).collect(),
    };
    collector.signature(signature);
    collector.out
}
