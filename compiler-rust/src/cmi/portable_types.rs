//! Portable type graph for cross-context type re-internalization.
//!
//! When modules are compiled in-process, their signatures contain `TypeExprRef`
//! indices into the compilation's `TypeArena`. These indices become invalid once
//! the compilation's `TypeContext` is dropped. This module provides a portable
//! representation that can be stored in `ModuleRegistry` and re-internalized
//! into any future `TypeContext`.
//!
//! The flow is:
//! 1. After compilation, `serialize_pers_struct` walks the signature's type graph
//!    and produces a `PortablePersStruct` with self-contained type indices.
//! 2. The `PortablePersStruct` is stored in `ModuleRegistry`.
//! 3. When a later compilation needs this module, `internalize_pers_struct` walks
//!    the portable graph, allocates fresh `TypeExprRef`s in the current arena,
//!    and produces a valid `PersStruct`.

use std::collections::HashMap;
use std::hash::{Hash, Hasher};

use crate::parser::longident::Longident;
use crate::types::asttypes::ArgLabel;
use crate::types::context::TypeContext;
use crate::types::decl::{
    ConstructorArguments, ConstructorDeclaration, ExtensionConstructor, LabelDeclaration,
    ModtypeDeclaration, ModuleDeclaration, ModuleType, Signature, SignatureItem, TypeDeclaration,
    TypeKind, ValueDescription,
};
use crate::types::path::Path;
use crate::types::type_expr::{
    Commutable, FieldKind, RowDesc, RowField, RowFieldRef, TypeArg, TypeDesc, TypeExprRef,
};

use super::persistent_env::PersStruct;

// ============================================================================
// Portable type graph types
// ============================================================================

/// A self-contained type graph that can be loaded into any TypeContext.
#[derive(Clone, Debug)]
pub struct PortableTypeGraph {
    /// Type entries indexed by position. TypeExprRef values in the associated
    /// signature are indices into this vec.
    pub entries: Vec<PortableTypeEntry>,
}

/// One type expression in portable form.
#[derive(Clone, Debug)]
pub struct PortableTypeEntry {
    pub desc: PortableTypeDesc,
    pub level: i32,
}

/// TypeDesc with indices into `PortableTypeGraph.entries` instead of arena refs.
#[derive(Clone, Debug)]
pub enum PortableTypeDesc {
    Tvar(Option<String>),
    Tarrow {
        arg_label: ArgLabel,
        arg: usize,
        ret: usize,
        arity: Option<i32>,
    },
    Ttuple(Vec<usize>),
    Tconstr {
        path: Path,
        args: Vec<usize>,
    },
    Tobject {
        fields: usize,
        name: Option<(Path, Vec<usize>)>,
    },
    Tfield {
        name: String,
        typ: usize,
        rest: usize,
    },
    Tnil,
    Tlink(usize),
    Tsubst(usize),
    Tvariant(PortableRowDesc),
    Tunivar(Option<String>),
    Tpoly {
        body: usize,
        vars: Vec<usize>,
    },
    Tpackage {
        path: Path,
        lids: Vec<Longident>,
        args: Vec<usize>,
    },
}

/// Portable row description for polymorphic variants.
#[derive(Clone, Debug)]
pub struct PortableRowDesc {
    pub row_fields: Vec<(String, PortableRowField)>,
    pub row_more: usize,
    pub row_closed: bool,
    pub row_fixed: bool,
    pub row_name: Option<(Path, Vec<usize>)>,
}

/// Portable row field.
#[derive(Clone, Debug)]
pub enum PortableRowField {
    Rpresent(Option<usize>),
    Reither {
        constant: bool,
        types: Vec<usize>,
        matched: bool,
    },
    Rabsent,
}

/// A PersStruct with types stored portably, independent of any TypeArena.
#[derive(Clone, Debug)]
pub struct PortablePersStruct {
    pub ps_name: String,
    pub ps_filename: String,
    /// Signature with TypeExprRef values being indices into `type_graph.entries`.
    pub ps_sig: Signature,
    /// Self-contained type graph.
    pub type_graph: PortableTypeGraph,
    /// Stamp-independent structural fingerprint of the type graph.
    /// Computed during serialization by hashing type structure with name-based
    /// path identity (ignoring stamps). Two compilations producing the same
    /// logical interface will have the same fingerprint even if internal stamps
    /// differ due to dependency changes.
    pub fingerprint: u64,
}

// ============================================================================
// Fingerprinting: stamp-independent structural hash
// ============================================================================

/// Compute a stamp-independent structural fingerprint of a portable type graph
/// and signature. Uses name-based identity for Paths (ignoring stamps) so that
/// recompilations producing the same logical interface get the same fingerprint
/// even if internal stamps shift due to dependency changes.
/// Public API for computing a fingerprint outside of `serialize_pers_struct`
/// (e.g., for namespace signatures synthesized directly).
pub fn compute_type_graph_fingerprint_pub(entries: &[PortableTypeEntry], sig: &Signature) -> u64 {
    compute_type_graph_fingerprint(entries, sig)
}

fn compute_type_graph_fingerprint(entries: &[PortableTypeEntry], sig: &Signature) -> u64 {
    use std::collections::hash_map::DefaultHasher;
    let mut hasher = DefaultHasher::new();

    // Hash the signature structure (item names and kinds)
    hash_signature(&mut hasher, sig);

    // Hash the type graph entries
    entries.len().hash(&mut hasher);
    for entry in entries {
        entry.level.hash(&mut hasher);
        hash_portable_desc(&mut hasher, &entry.desc);
    }

    hasher.finish()
}

/// Hash a Path using only names, not stamps. This makes the fingerprint stable
/// across recompilations where dependency stamps may shift.
fn hash_path_by_name(hasher: &mut impl Hasher, path: &Path) {
    use crate::types::path::Path as P;
    match path {
        P::Pident(ident) => {
            0u8.hash(hasher);
            ident.name().hash(hasher);
        }
        P::Pdot(base, field, _pos) => {
            1u8.hash(hasher);
            hash_path_by_name(hasher, base);
            field.hash(hasher);
        }
        P::Papply(f, x) => {
            2u8.hash(hasher);
            hash_path_by_name(hasher, f);
            hash_path_by_name(hasher, x);
        }
    }
}

fn hash_portable_desc(hasher: &mut impl Hasher, desc: &PortableTypeDesc) {
    std::mem::discriminant(desc).hash(hasher);
    match desc {
        PortableTypeDesc::Tvar(name) => name.hash(hasher),
        PortableTypeDesc::Tarrow {
            arg_label,
            arg,
            ret,
            arity,
        } => {
            arg_label.hash(hasher);
            arg.hash(hasher);
            ret.hash(hasher);
            arity.hash(hasher);
        }
        PortableTypeDesc::Ttuple(elems) => elems.hash(hasher),
        PortableTypeDesc::Tconstr { path, args } => {
            hash_path_by_name(hasher, path);
            args.hash(hasher);
        }
        PortableTypeDesc::Tobject { fields, name } => {
            fields.hash(hasher);
            if let Some((p, args)) = name {
                true.hash(hasher);
                hash_path_by_name(hasher, p);
                args.hash(hasher);
            } else {
                false.hash(hasher);
            }
        }
        PortableTypeDesc::Tfield { name, typ, rest } => {
            name.hash(hasher);
            typ.hash(hasher);
            rest.hash(hasher);
        }
        PortableTypeDesc::Tnil => {}
        PortableTypeDesc::Tlink(idx) => idx.hash(hasher),
        PortableTypeDesc::Tsubst(idx) => idx.hash(hasher),
        PortableTypeDesc::Tvariant(rd) => hash_portable_row_desc(hasher, rd),
        PortableTypeDesc::Tunivar(name) => name.hash(hasher),
        PortableTypeDesc::Tpoly { body, vars } => {
            body.hash(hasher);
            vars.hash(hasher);
        }
        PortableTypeDesc::Tpackage { path, lids, args } => {
            hash_path_by_name(hasher, path);
            // Longident contains StrIdx; hash raw discriminant + index.
            // Same-session comparisons are correct; cross-session is best-effort.
            lids.hash(hasher);
            args.hash(hasher);
        }
    }
}

fn hash_portable_row_desc(hasher: &mut impl Hasher, rd: &PortableRowDesc) {
    rd.row_fields.len().hash(hasher);
    for (label, field) in &rd.row_fields {
        label.hash(hasher);
        hash_portable_row_field(hasher, field);
    }
    rd.row_more.hash(hasher);
    rd.row_closed.hash(hasher);
    rd.row_fixed.hash(hasher);
    if let Some((p, args)) = &rd.row_name {
        true.hash(hasher);
        hash_path_by_name(hasher, p);
        args.hash(hasher);
    } else {
        false.hash(hasher);
    }
}

fn hash_portable_row_field(hasher: &mut impl Hasher, rf: &PortableRowField) {
    std::mem::discriminant(rf).hash(hasher);
    match rf {
        PortableRowField::Rpresent(opt) => opt.hash(hasher),
        PortableRowField::Reither {
            constant,
            types,
            matched,
        } => {
            constant.hash(hasher);
            types.hash(hasher);
            matched.hash(hasher);
        }
        PortableRowField::Rabsent => {}
    }
}

/// Hash the signature structure: item names and kinds.
/// Uses name-based identity for all paths.
fn hash_signature(hasher: &mut impl Hasher, sig: &Signature) {
    sig.len().hash(hasher);
    for item in sig {
        hash_sig_item(hasher, item);
    }
}

fn hash_sig_item(hasher: &mut impl Hasher, item: &SignatureItem) {
    std::mem::discriminant(item).hash(hasher);
    match item {
        SignatureItem::SigValue(ident, _vd) => {
            ident.name().hash(hasher);
        }
        SignatureItem::SigType(ident, _td, _rec) => {
            ident.name().hash(hasher);
        }
        SignatureItem::SigTypext(ident, _ext, _es) => {
            ident.name().hash(hasher);
        }
        SignatureItem::SigModule(ident, md, _rec) => {
            ident.name().hash(hasher);
            hash_module_type(hasher, &md.md_type);
        }
        SignatureItem::SigModtype(ident, _mtd) => {
            ident.name().hash(hasher);
        }
        SignatureItem::SigClass | SignatureItem::SigClassType => {}
    }
}

fn hash_module_type(hasher: &mut impl Hasher, mty: &ModuleType) {
    std::mem::discriminant(mty).hash(hasher);
    match mty {
        ModuleType::MtyIdent(path) => hash_path_by_name(hasher, path),
        ModuleType::MtySignature(sig) => hash_signature(hasher, sig),
        ModuleType::MtyFunctor {
            param,
            param_type,
            result,
        } => {
            param.name().hash(hasher);
            if let Some(pt) = param_type {
                hash_module_type(hasher, pt);
            }
            hash_module_type(hasher, result);
        }
        ModuleType::MtyAlias(_presence, path) => hash_path_by_name(hasher, path),
    }
}

// ============================================================================
// Serialization: PersStruct + TypeContext -> PortablePersStruct
// ============================================================================

/// Serialize a PersStruct's type graph into portable form while the TypeContext
/// is still alive. All TypeExprRef values in the signature are replaced with
/// indices into the returned PortableTypeGraph.
pub fn serialize_pers_struct(ps: &PersStruct, ctx: &TypeContext<'_>) -> PortablePersStruct {
    let mut ser = TypeGraphSerializer {
        ctx,
        entries: Vec::new(),
        cache: HashMap::new(),
    };
    let mut sig = ps.ps_sig.clone();
    ser.remap_signature(&mut sig);
    let entries = ser.entries;
    let fingerprint = compute_type_graph_fingerprint(&entries, &sig);
    PortablePersStruct {
        ps_name: ps.ps_name.clone(),
        ps_filename: ps.ps_filename.clone(),
        ps_sig: sig,
        type_graph: PortableTypeGraph { entries },
        fingerprint,
    }
}

struct TypeGraphSerializer<'a, 'b> {
    ctx: &'a TypeContext<'b>,
    entries: Vec<PortableTypeEntry>,
    cache: HashMap<TypeExprRef, usize>,
}

impl<'a, 'b> TypeGraphSerializer<'a, 'b> {
    /// Serialize a TypeExprRef, returning the portable index.
    fn serialize_type(&mut self, r: TypeExprRef) -> usize {
        if let Some(&idx) = self.cache.get(&r) {
            return idx;
        }

        // Allocate placeholder first to handle recursive types.
        let idx = self.entries.len();
        self.cache.insert(r, idx);
        self.entries.push(PortableTypeEntry {
            desc: PortableTypeDesc::Tvar(None),
            level: 0,
        });

        let desc_snapshot = self.ctx.get_desc(r);
        let level = self.ctx.get_level(r);
        let portable_desc = self.serialize_desc(&desc_snapshot);
        self.entries[idx] = PortableTypeEntry {
            desc: portable_desc,
            level,
        };
        idx
    }

    fn serialize_desc(&mut self, desc: &TypeDesc) -> PortableTypeDesc {
        match desc {
            TypeDesc::Tvar(name) => PortableTypeDesc::Tvar(name.clone()),
            TypeDesc::Tarrow {
                arg, ret, arity, ..
            } => PortableTypeDesc::Tarrow {
                arg_label: arg.lbl.clone(),
                arg: self.serialize_type(arg.typ),
                ret: self.serialize_type(*ret),
                arity: *arity,
            },
            TypeDesc::Ttuple(types) => {
                PortableTypeDesc::Ttuple(types.iter().map(|t| self.serialize_type(*t)).collect())
            }
            TypeDesc::Tconstr { path, args, .. } => PortableTypeDesc::Tconstr {
                path: path.clone(),
                args: args.iter().map(|t| self.serialize_type(*t)).collect(),
            },
            TypeDesc::Tobject { fields, name } => PortableTypeDesc::Tobject {
                fields: self.serialize_type(*fields),
                name: name.as_ref().map(|(p, args)| {
                    (
                        p.clone(),
                        args.iter().map(|t| self.serialize_type(*t)).collect(),
                    )
                }),
            },
            TypeDesc::Tfield {
                name, typ, rest, ..
            } => PortableTypeDesc::Tfield {
                name: name.clone(),
                typ: self.serialize_type(*typ),
                rest: self.serialize_type(*rest),
            },
            TypeDesc::Tnil => PortableTypeDesc::Tnil,
            TypeDesc::Tlink(r) => PortableTypeDesc::Tlink(self.serialize_type(*r)),
            TypeDesc::Tsubst(r) => PortableTypeDesc::Tsubst(self.serialize_type(*r)),
            TypeDesc::Tvariant(row_desc) => {
                PortableTypeDesc::Tvariant(self.serialize_row_desc(row_desc))
            }
            TypeDesc::Tunivar(name) => PortableTypeDesc::Tunivar(name.clone()),
            TypeDesc::Tpoly { body, vars } => PortableTypeDesc::Tpoly {
                body: self.serialize_type(*body),
                vars: vars.iter().map(|t| self.serialize_type(*t)).collect(),
            },
            TypeDesc::Tpackage { path, lids, args } => PortableTypeDesc::Tpackage {
                path: path.clone(),
                lids: lids.clone(),
                args: args.iter().map(|t| self.serialize_type(*t)).collect(),
            },
        }
    }

    fn serialize_row_desc(&mut self, rd: &RowDesc) -> PortableRowDesc {
        PortableRowDesc {
            row_fields: rd
                .row_fields
                .iter()
                .map(|(label, field)| (label.to_string(), self.serialize_row_field(field)))
                .collect(),
            row_more: self.serialize_type(rd.row_more),
            row_closed: rd.row_closed,
            row_fixed: rd.row_fixed,
            row_name: rd.row_name.as_ref().map(|(p, args)| {
                (
                    p.clone(),
                    args.iter().map(|t| self.serialize_type(*t)).collect(),
                )
            }),
        }
    }

    fn serialize_row_field(&mut self, rf: &RowField) -> PortableRowField {
        match rf {
            RowField::Rpresent(opt) => {
                PortableRowField::Rpresent(opt.map(|t| self.serialize_type(t)))
            }
            RowField::Reither {
                constant,
                types,
                matched,
                ..
            } => PortableRowField::Reither {
                constant: *constant,
                types: types.iter().map(|t| self.serialize_type(*t)).collect(),
                matched: *matched,
            },
            RowField::Rabsent => PortableRowField::Rabsent,
        }
    }

    // ========================================================================
    // Signature remapping: replace TypeExprRef with portable indices
    // ========================================================================

    fn remap_signature(&mut self, sig: &mut Signature) {
        for item in sig.iter_mut() {
            self.remap_sig_item(item);
        }
    }

    fn remap_sig_item(&mut self, item: &mut SignatureItem) {
        match item {
            SignatureItem::SigValue(_, vd) => self.remap_value_desc(vd),
            SignatureItem::SigType(_, td, _) => self.remap_type_decl(td),
            SignatureItem::SigTypext(_, ec, _) => self.remap_ext_ctor(ec),
            SignatureItem::SigModule(_, md, _) => self.remap_module_decl(md),
            SignatureItem::SigModtype(_, mtd) => self.remap_modtype_decl(mtd),
            SignatureItem::SigClass | SignatureItem::SigClassType => {}
        }
    }

    fn remap_value_desc(&mut self, vd: &mut ValueDescription) {
        vd.val_type = TypeExprRef(self.serialize_type(vd.val_type));
    }

    fn remap_type_decl(&mut self, td: &mut TypeDeclaration) {
        for p in td.type_params.iter_mut() {
            *p = TypeExprRef(self.serialize_type(*p));
        }
        if let Some(ref mut m) = td.type_manifest {
            *m = TypeExprRef(self.serialize_type(*m));
        }
        match &mut td.type_kind {
            TypeKind::TypeAbstract | TypeKind::TypeOpen => {}
            TypeKind::TypeRecord(labels, _) => {
                for label in labels.iter_mut() {
                    self.remap_label_decl(label);
                }
            }
            TypeKind::TypeVariant(ctors) => {
                for ctor in ctors.iter_mut() {
                    self.remap_ctor_decl(ctor);
                }
            }
        }
        for inlined in td.type_inlined_types.iter_mut() {
            match inlined {
                crate::types::decl::TypeInlinedType::Record { labels, .. } => {
                    for label in labels.iter_mut() {
                        self.remap_label_decl(label);
                    }
                }
            }
        }
    }

    fn remap_label_decl(&mut self, ld: &mut LabelDeclaration) {
        ld.ld_type = TypeExprRef(self.serialize_type(ld.ld_type));
    }

    fn remap_ctor_decl(&mut self, cd: &mut ConstructorDeclaration) {
        match &mut cd.cd_args {
            ConstructorArguments::CstrTuple(types) => {
                for t in types.iter_mut() {
                    *t = TypeExprRef(self.serialize_type(*t));
                }
            }
            ConstructorArguments::CstrRecord(labels) => {
                for label in labels.iter_mut() {
                    self.remap_label_decl(label);
                }
            }
        }
        if let Some(ref mut res) = cd.cd_res {
            *res = TypeExprRef(self.serialize_type(*res));
        }
    }

    fn remap_ext_ctor(&mut self, ec: &mut ExtensionConstructor) {
        for p in ec.ext_type_params.iter_mut() {
            *p = TypeExprRef(self.serialize_type(*p));
        }
        match &mut ec.ext_args {
            ConstructorArguments::CstrTuple(types) => {
                for t in types.iter_mut() {
                    *t = TypeExprRef(self.serialize_type(*t));
                }
            }
            ConstructorArguments::CstrRecord(labels) => {
                for label in labels.iter_mut() {
                    self.remap_label_decl(label);
                }
            }
        }
        if let Some(ref mut ret) = ec.ext_ret_type {
            *ret = TypeExprRef(self.serialize_type(*ret));
        }
    }

    fn remap_module_decl(&mut self, md: &mut ModuleDeclaration) {
        self.remap_module_type(&mut md.md_type);
    }

    fn remap_modtype_decl(&mut self, mtd: &mut ModtypeDeclaration) {
        if let Some(ref mut mt) = mtd.mtd_type {
            self.remap_module_type(mt);
        }
    }

    fn remap_module_type(&mut self, mt: &mut ModuleType) {
        match mt {
            ModuleType::MtySignature(sig) => self.remap_signature(sig),
            ModuleType::MtyFunctor {
                param_type, result, ..
            } => {
                if let Some(pt) = param_type.as_mut() {
                    self.remap_module_type(pt);
                }
                self.remap_module_type(result);
            }
            ModuleType::MtyIdent(_) | ModuleType::MtyAlias(_, _) => {}
        }
    }
}

// ============================================================================
// Deserialization: PortablePersStruct + TypeContext -> PersStruct
// ============================================================================

/// Load a PortablePersStruct into the current TypeContext, producing a PersStruct
/// with valid TypeExprRefs.
pub fn internalize_pers_struct(pps: &PortablePersStruct, ctx: &TypeContext<'_>) -> PersStruct {
    let graph = &pps.type_graph;

    // Phase 1: allocate placeholder TypeExprRefs for all entries.
    let remap: Vec<TypeExprRef> = graph
        .entries
        .iter()
        .map(|entry| ctx.alloc_type_at_level(TypeDesc::Tvar(None), entry.level))
        .collect();

    // Phase 2: set descriptors using remapped refs.
    for (i, entry) in graph.entries.iter().enumerate() {
        let desc = internalize_desc(&entry.desc, &remap, ctx);
        ctx.set_desc(remap[i], desc);
    }

    // Phase 3: clone and remap the signature.
    let mut sig = pps.ps_sig.clone();
    remap_signature_refs(&mut sig, &remap);

    PersStruct {
        ps_name: pps.ps_name.clone(),
        ps_sig: sig,
        ps_filename: pps.ps_filename.clone(),
    }
}

fn internalize_desc(
    desc: &PortableTypeDesc,
    remap: &[TypeExprRef],
    ctx: &TypeContext<'_>,
) -> TypeDesc {
    match desc {
        PortableTypeDesc::Tvar(name) => TypeDesc::Tvar(name.clone()),
        PortableTypeDesc::Tarrow {
            arg_label,
            arg,
            ret,
            arity,
        } => TypeDesc::Tarrow {
            arg: TypeArg {
                lbl: arg_label.clone(),
                typ: remap[*arg],
            },
            ret: remap[*ret],
            commutable: Commutable::Cok,
            arity: *arity,
        },
        PortableTypeDesc::Ttuple(types) => {
            TypeDesc::Ttuple(types.iter().map(|&i| remap[i]).collect())
        }
        PortableTypeDesc::Tconstr { path, args } => TypeDesc::Tconstr {
            path: path.clone(),
            args: args.iter().map(|&i| remap[i]).collect(),
            abbrev: ctx.alloc_abbrev_nil(),
        },
        PortableTypeDesc::Tobject { fields, name } => TypeDesc::Tobject {
            fields: remap[*fields],
            name: name
                .as_ref()
                .map(|(p, args)| (p.clone(), args.iter().map(|&i| remap[i]).collect())),
        },
        PortableTypeDesc::Tfield { name, typ, rest } => TypeDesc::Tfield {
            name: name.clone(),
            kind: FieldKind::Fpresent,
            typ: remap[*typ],
            rest: remap[*rest],
        },
        PortableTypeDesc::Tnil => TypeDesc::Tnil,
        PortableTypeDesc::Tlink(i) => TypeDesc::Tlink(remap[*i]),
        PortableTypeDesc::Tsubst(i) => TypeDesc::Tsubst(remap[*i]),
        PortableTypeDesc::Tvariant(prd) => {
            TypeDesc::Tvariant(internalize_row_desc(prd, remap, ctx))
        }
        PortableTypeDesc::Tunivar(name) => TypeDesc::Tunivar(name.clone()),
        PortableTypeDesc::Tpoly { body, vars } => TypeDesc::Tpoly {
            body: remap[*body],
            vars: vars.iter().map(|&i| remap[i]).collect(),
        },
        PortableTypeDesc::Tpackage { path, lids, args } => TypeDesc::Tpackage {
            path: path.clone(),
            lids: lids.clone(),
            args: args.iter().map(|&i| remap[i]).collect(),
        },
    }
}

fn internalize_row_desc(
    prd: &PortableRowDesc,
    remap: &[TypeExprRef],
    ctx: &TypeContext<'_>,
) -> RowDesc {
    RowDesc {
        row_fields: prd
            .row_fields
            .iter()
            .map(|(label, field)| {
                (
                    label.as_str().into(),
                    internalize_row_field(field, remap, ctx),
                )
            })
            .collect(),
        row_more: remap[prd.row_more],
        row_closed: prd.row_closed,
        row_fixed: prd.row_fixed,
        row_name: prd
            .row_name
            .as_ref()
            .map(|(p, args)| (p.clone(), args.iter().map(|&i| remap[i]).collect())),
    }
}

fn internalize_row_field(
    prf: &PortableRowField,
    remap: &[TypeExprRef],
    _ctx: &TypeContext<'_>,
) -> RowField {
    match prf {
        PortableRowField::Rpresent(opt) => RowField::Rpresent(opt.map(|i| remap[i])),
        PortableRowField::Reither {
            constant,
            types,
            matched,
        } => RowField::Reither {
            constant: *constant,
            types: types.iter().map(|&i| remap[i]).collect(),
            matched: *matched,
            link: RowFieldRef::null(),
        },
        PortableRowField::Rabsent => RowField::Rabsent,
    }
}

// ============================================================================
// Signature ref remapping (portable index -> real TypeExprRef)
// ============================================================================

fn remap_signature_refs(sig: &mut Signature, remap: &[TypeExprRef]) {
    for item in sig.iter_mut() {
        remap_sig_item_refs(item, remap);
    }
}

fn remap_sig_item_refs(item: &mut SignatureItem, remap: &[TypeExprRef]) {
    match item {
        SignatureItem::SigValue(_, vd) => remap_value_desc_refs(vd, remap),
        SignatureItem::SigType(_, td, _) => remap_type_decl_refs(td, remap),
        SignatureItem::SigTypext(_, ec, _) => remap_ext_ctor_refs(ec, remap),
        SignatureItem::SigModule(_, md, _) => remap_module_decl_refs(md, remap),
        SignatureItem::SigModtype(_, mtd) => remap_modtype_decl_refs(mtd, remap),
        SignatureItem::SigClass | SignatureItem::SigClassType => {}
    }
}

fn remap_value_desc_refs(vd: &mut ValueDescription, remap: &[TypeExprRef]) {
    vd.val_type = remap[vd.val_type.0];
}

fn remap_type_decl_refs(td: &mut TypeDeclaration, remap: &[TypeExprRef]) {
    for p in td.type_params.iter_mut() {
        *p = remap[p.0];
    }
    if let Some(ref mut m) = td.type_manifest {
        *m = remap[m.0];
    }
    match &mut td.type_kind {
        TypeKind::TypeAbstract | TypeKind::TypeOpen => {}
        TypeKind::TypeRecord(labels, _) => {
            for label in labels.iter_mut() {
                remap_label_decl_refs(label, remap);
            }
        }
        TypeKind::TypeVariant(ctors) => {
            for ctor in ctors.iter_mut() {
                remap_ctor_decl_refs(ctor, remap);
            }
        }
    }
    for inlined in td.type_inlined_types.iter_mut() {
        match inlined {
            crate::types::decl::TypeInlinedType::Record { labels, .. } => {
                for label in labels.iter_mut() {
                    remap_label_decl_refs(label, remap);
                }
            }
        }
    }
}

fn remap_label_decl_refs(ld: &mut LabelDeclaration, remap: &[TypeExprRef]) {
    ld.ld_type = remap[ld.ld_type.0];
}

fn remap_ctor_decl_refs(cd: &mut ConstructorDeclaration, remap: &[TypeExprRef]) {
    match &mut cd.cd_args {
        ConstructorArguments::CstrTuple(types) => {
            for t in types.iter_mut() {
                *t = remap[t.0];
            }
        }
        ConstructorArguments::CstrRecord(labels) => {
            for label in labels.iter_mut() {
                remap_label_decl_refs(label, remap);
            }
        }
    }
    if let Some(ref mut res) = cd.cd_res {
        *res = remap[res.0];
    }
}

fn remap_ext_ctor_refs(ec: &mut ExtensionConstructor, remap: &[TypeExprRef]) {
    for p in ec.ext_type_params.iter_mut() {
        *p = remap[p.0];
    }
    match &mut ec.ext_args {
        ConstructorArguments::CstrTuple(types) => {
            for t in types.iter_mut() {
                *t = remap[t.0];
            }
        }
        ConstructorArguments::CstrRecord(labels) => {
            for label in labels.iter_mut() {
                remap_label_decl_refs(label, remap);
            }
        }
    }
    if let Some(ref mut ret) = ec.ext_ret_type {
        *ret = remap[ret.0];
    }
}

fn remap_module_decl_refs(md: &mut ModuleDeclaration, remap: &[TypeExprRef]) {
    remap_module_type_refs(&mut md.md_type, remap);
}

fn remap_modtype_decl_refs(mtd: &mut ModtypeDeclaration, remap: &[TypeExprRef]) {
    if let Some(ref mut mt) = mtd.mtd_type {
        remap_module_type_refs(mt, remap);
    }
}

fn remap_module_type_refs(mt: &mut ModuleType, remap: &[TypeExprRef]) {
    match mt {
        ModuleType::MtySignature(sig) => remap_signature_refs(sig, remap),
        ModuleType::MtyFunctor {
            param_type, result, ..
        } => {
            if let Some(pt) = param_type.as_mut() {
                remap_module_type_refs(pt, remap);
            }
            remap_module_type_refs(result, remap);
        }
        ModuleType::MtyIdent(_) | ModuleType::MtyAlias(_, _) => {}
    }
}
