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
use std::sync::Arc;

use crate::parse_arena::ParseArena;
use crate::parser::longident::Longident;
use crate::types::asttypes::ArgLabel;
use crate::types::context::TypeContext;
use crate::types::decl::{
    ConstructorArguments, ConstructorDeclaration, ExtensionConstructor, LabelDeclaration,
    ModtypeDeclaration, ModuleDeclaration, ModuleType, Signature, SignatureItem, TypeDeclaration,
    TypeInlinedType, TypeKind, ValueDescription, ValueKind,
};
use crate::types::path::Path;
use crate::types::thread_store::ThreadTypeStore;
use crate::types::type_expr::{
    AbbrevMemo, AbbrevMemoRef, GENERIC_LEVEL, MutabilityRef, RowDesc, RowField, RowFieldRef, TypeArg,
    TypeDesc, TypeExprRef,
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
    /// Canonical variant layouts referenced by declarations in the signature.
    pub variant_layouts: Vec<crate::types::VariantLayout>,
    /// Object field mutability cells (subst.ml `for_saving` gives the saved
    /// graph its own cells; fields sharing a cell share an index here).
    pub mutabilities: Vec<crate::types::asttypes::MutableFlag>,
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
        args: Vec<(ArgLabel, usize)>,
        ret: usize,
    },
    Ttuple(Vec<usize>),
    Tconstr {
        path: Path,
        args: Vec<usize>,
    },
    Tobject {
        fields: usize,
    },
    Tfield {
        name: String,
        /// Index into `PortableTypeGraph.mutabilities`.
        mutability: usize,
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
        lids: Vec<PortableLongident>,
        args: Vec<usize>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum PortableLongident {
    Lident(String),
    Ldot(Box<PortableLongident>, String),
    Lapply(Box<PortableLongident>, Box<PortableLongident>),
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
    /// `PersStruct::ps_deprecated`.
    pub ps_deprecated: Option<String>,
    /// `PersStruct::ps_crcs`.
    pub ps_crcs: Vec<(String, Option<[u8; 16]>)>,
    /// Signature with TypeExprRef values being indices into `type_graph.entries`.
    pub ps_sig: Signature,
    /// Raw `ps_sig` copy for OCaml-style lazy alias scraping.
    ///
    /// OCaml stores `ps_sig = lazy (Subst.signature Subst.identity sign)` in
    /// compiler/ml/env.ml:669-678 and compiler/ml/env.ml:1960-1977, separately
    /// from component-table substitution at compiler/ml/env.ml:1513-1530. The
    /// in-process registry crosses TypeContext boundaries, so carry that raw
    /// copied signature portably instead of rebuilding it from the substituted
    /// component signature later.
    pub raw_ps_sig: Option<Signature>,
    /// Synthetic longident component names created while reading CMI files.
    pub cmi_longident_names: Vec<(u32, String)>,
    /// Self-contained type graph.
    pub type_graph: PortableTypeGraph,
    /// Self-contained type graph for `raw_ps_sig`.
    pub raw_type_graph: Option<PortableTypeGraph>,
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
    // Deterministic within a build (fixed seeds); the fingerprint only lives
    // in the in-memory interface registry.
    use std::hash::BuildHasher;
    let mut hasher =
        ahash::RandomState::with_seeds(0x5245_5343, 0x5249_5054, 0x4649_4e47, 0x4552_5052)
            .build_hasher();

    // Hash the public signature through its remapped TypeExprRef roots instead
    // of hashing the portable arena linearly. The same interface can serialize
    // its internal type graph in a different allocation order depending on
    // whether it was produced during a cold parallel build or a later watch
    // rebuild; dependency invalidation needs the interface shape, not arena
    // ordering.
    hash_signature(&mut hasher, sig, entries);

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

fn hash_type_ref(
    hasher: &mut impl Hasher,
    idx: usize,
    entries: &[PortableTypeEntry],
    visiting: &mut Vec<usize>,
) {
    if idx >= entries.len() {
        0xfeu8.hash(hasher);
        idx.hash(hasher);
        return;
    }

    if let Some(pos) = visiting.iter().position(|seen| *seen == idx) {
        0xffu8.hash(hasher);
        pos.hash(hasher);
        return;
    }

    visiting.push(idx);
    hash_portable_desc(hasher, &entries[idx].desc, entries, visiting);
    visiting.pop();
}

fn hash_type_refs(
    hasher: &mut impl Hasher,
    refs: &[usize],
    entries: &[PortableTypeEntry],
    visiting: &mut Vec<usize>,
) {
    refs.len().hash(hasher);
    for idx in refs {
        hash_type_ref(hasher, *idx, entries, visiting);
    }
}

fn hash_portable_desc(
    hasher: &mut impl Hasher,
    desc: &PortableTypeDesc,
    entries: &[PortableTypeEntry],
    visiting: &mut Vec<usize>,
) {
    std::mem::discriminant(desc).hash(hasher);
    match desc {
        PortableTypeDesc::Tvar(name) => name.hash(hasher),
        PortableTypeDesc::Tarrow { args, ret } => {
            args.len().hash(hasher);
            for (label, arg) in args {
                label.hash(hasher);
                hash_type_ref(hasher, *arg, entries, visiting);
            }
            hash_type_ref(hasher, *ret, entries, visiting);
        }
        PortableTypeDesc::Ttuple(elems) => hash_type_refs(hasher, elems, entries, visiting),
        PortableTypeDesc::Tconstr { path, args } => {
            hash_path_by_name(hasher, path);
            hash_type_refs(hasher, args, entries, visiting);
        }
        PortableTypeDesc::Tobject { fields } => {
            hash_type_ref(hasher, *fields, entries, visiting);
        }
        PortableTypeDesc::Tfield {
            name,
            mutability,
            typ,
            rest,
        } => {
            name.hash(hasher);
            mutability.hash(hasher);
            hash_type_ref(hasher, *typ, entries, visiting);
            hash_type_ref(hasher, *rest, entries, visiting);
        }
        PortableTypeDesc::Tnil => {}
        PortableTypeDesc::Tlink(idx) => hash_type_ref(hasher, *idx, entries, visiting),
        PortableTypeDesc::Tsubst(idx) => hash_type_ref(hasher, *idx, entries, visiting),
        PortableTypeDesc::Tvariant(rd) => hash_portable_row_desc(hasher, rd, entries, visiting),
        PortableTypeDesc::Tunivar(name) => name.hash(hasher),
        PortableTypeDesc::Tpoly { body, vars } => {
            hash_type_ref(hasher, *body, entries, visiting);
            hash_type_refs(hasher, vars, entries, visiting);
        }
        PortableTypeDesc::Tpackage { path, lids, args } => {
            hash_path_by_name(hasher, path);
            lids.hash(hasher);
            hash_type_refs(hasher, args, entries, visiting);
        }
    }
}

fn hash_portable_row_desc(
    hasher: &mut impl Hasher,
    rd: &PortableRowDesc,
    entries: &[PortableTypeEntry],
    visiting: &mut Vec<usize>,
) {
    rd.row_fields.len().hash(hasher);
    for (label, field) in &rd.row_fields {
        label.hash(hasher);
        hash_portable_row_field(hasher, field, entries, visiting);
    }
    hash_type_ref(hasher, rd.row_more, entries, visiting);
    rd.row_closed.hash(hasher);
    rd.row_fixed.hash(hasher);
    if let Some((p, args)) = &rd.row_name {
        true.hash(hasher);
        hash_path_by_name(hasher, p);
        hash_type_refs(hasher, args, entries, visiting);
    } else {
        false.hash(hasher);
    }
}

fn hash_portable_row_field(
    hasher: &mut impl Hasher,
    rf: &PortableRowField,
    entries: &[PortableTypeEntry],
    visiting: &mut Vec<usize>,
) {
    std::mem::discriminant(rf).hash(hasher);
    match rf {
        PortableRowField::Rpresent(opt) => {
            if let Some(idx) = opt {
                true.hash(hasher);
                hash_type_ref(hasher, *idx, entries, visiting);
            } else {
                false.hash(hasher);
            }
        }
        PortableRowField::Reither {
            constant,
            types,
            matched,
        } => {
            constant.hash(hasher);
            hash_type_refs(hasher, types, entries, visiting);
            matched.hash(hasher);
        }
        PortableRowField::Rabsent => {}
    }
}

/// Hash the signature structure: item names and kinds.
/// Uses name-based identity for all paths.
fn hash_signature(hasher: &mut impl Hasher, sig: &Signature, entries: &[PortableTypeEntry]) {
    sig.len().hash(hasher);
    for item in sig {
        hash_sig_item(hasher, item, entries);
    }
}

/// The fingerprint contribution of one signature item.
pub fn hash_sig_item_pub(hasher: &mut impl Hasher, item: &SignatureItem, entries: &[PortableTypeEntry]) {
    hash_sig_item(hasher, item, entries)
}

fn hash_sig_item(hasher: &mut impl Hasher, item: &SignatureItem, entries: &[PortableTypeEntry]) {
    std::mem::discriminant(item).hash(hasher);
    match item {
        SignatureItem::SigValue(ident, vd) => {
            ident.name().hash(hasher);
            hash_value_desc(hasher, vd, entries);
        }
        SignatureItem::SigType(ident, td, rec) => {
            ident.name().hash(hasher);
            std::mem::discriminant(rec).hash(hasher);
            hash_type_decl(hasher, td, entries);
        }
        SignatureItem::SigTypext(ident, ext, es) => {
            ident.name().hash(hasher);
            std::mem::discriminant(es).hash(hasher);
            hash_extension_constructor(hasher, ext, entries);
        }
        SignatureItem::SigModule(ident, md, _rec) => {
            ident.name().hash(hasher);
            hash_attributes(hasher, &md.md_attributes);
            hash_module_type(hasher, &md.md_type, entries);
        }
        SignatureItem::SigModtype(ident, mtd) => {
            ident.name().hash(hasher);
            hash_modtype_decl(hasher, mtd, entries);
        }
        SignatureItem::SigClass | SignatureItem::SigClassType => {}
    }
}

/// Attributes reach dependents: `@deprecated` warnings, `@as` and
/// `@unboxed` representations, GenType annotations.
fn hash_attributes(hasher: &mut impl Hasher, attrs: &[crate::types::decl::Attribute]) {
    attrs.len().hash(hasher);
    for attr in attrs {
        attr.attr_name.txt.hash(hasher);
        format!("{:?}", attr.attr_payload).hash(hasher);
    }
}

fn hash_value_desc(hasher: &mut impl Hasher, vd: &ValueDescription, entries: &[PortableTypeEntry]) {
    hash_type_ref(hasher, vd.val_type.index(), entries, &mut Vec::new());
    hash_attributes(hasher, &vd.val_attributes);
    match &vd.val_kind {
        ValueKind::ValReg => {
            0u8.hash(hasher);
        }
        ValueKind::ValPrim(prim) => {
            1u8.hash(hasher);
            prim.prim_name.hash(hasher);
            prim.prim_arity.hash(hasher);
            prim.prim_kind.hash(hasher);
            prim.prim_native_float.hash(hasher);
            prim.prim_from_constructor.hash(hasher);
        }
    }
    if let Some(path) = &vd.val_path {
        true.hash(hasher);
        hash_path_by_name(hasher, path);
    } else {
        false.hash(hasher);
    }
}

fn hash_type_decl(hasher: &mut impl Hasher, td: &TypeDeclaration, entries: &[PortableTypeEntry]) {
    td.type_arity.hash(hasher);
    hash_attributes(hasher, &td.type_attributes);
    hash_type_expr_refs(hasher, &td.type_params, entries);
    td.type_private.hash(hasher);
    if let Some(manifest) = td.type_manifest {
        true.hash(hasher);
        hash_type_ref(hasher, manifest.index(), entries, &mut Vec::new());
    } else {
        false.hash(hasher);
    }
    td.type_variance.hash(hasher);
    td.type_newtype_level.hash(hasher);
    td.type_immediate.hash(hasher);
    td.type_representation.hash(hasher);
    if let Some(path) = &td.type_path {
        true.hash(hasher);
        hash_path_by_name(hasher, path);
    } else {
        false.hash(hasher);
    }
    hash_type_kind(hasher, &td.type_kind, entries);
    td.type_inlined_types.len().hash(hasher);
    for inlined in &td.type_inlined_types {
        match inlined {
            TypeInlinedType::Record { type_name, labels } => {
                type_name.hash(hasher);
                hash_label_decls(hasher, labels, entries);
            }
        }
    }
}

fn hash_type_expr_refs(
    hasher: &mut impl Hasher,
    refs: &[TypeExprRef],
    entries: &[PortableTypeEntry],
) {
    refs.len().hash(hasher);
    for r in refs {
        hash_type_ref(hasher, r.index(), entries, &mut Vec::new());
    }
}

fn hash_type_kind(hasher: &mut impl Hasher, kind: &TypeKind, entries: &[PortableTypeEntry]) {
    std::mem::discriminant(kind).hash(hasher);
    match kind {
        TypeKind::TypeAbstract | TypeKind::TypeOpen => {}
        TypeKind::TypeRecord(labels, repr) => {
            hash_label_decls(hasher, labels, entries);
            std::mem::discriminant(repr).hash(hasher);
        }
        TypeKind::TypeVariant(ctors, _) => {
            ctors.len().hash(hasher);
            for ctor in ctors {
                ctor.cd_id.name().hash(hasher);
                hash_attributes(hasher, &ctor.cd_attributes);
                hash_constructor_args(hasher, &ctor.cd_args, entries);
                if let Some(res) = ctor.cd_res {
                    true.hash(hasher);
                    hash_type_ref(hasher, res.index(), entries, &mut Vec::new());
                } else {
                    false.hash(hasher);
                }
            }
        }
    }
}

fn hash_label_decls(
    hasher: &mut impl Hasher,
    labels: &[LabelDeclaration],
    entries: &[PortableTypeEntry],
) {
    labels.len().hash(hasher);
    for label in labels {
        label.ld_id.name().hash(hasher);
        hash_attributes(hasher, &label.ld_attributes);
        label.ld_mutable.hash(hasher);
        label.ld_optional.hash(hasher);
        hash_type_ref(hasher, label.ld_type.index(), entries, &mut Vec::new());
    }
}

fn hash_constructor_args(
    hasher: &mut impl Hasher,
    args: &ConstructorArguments,
    entries: &[PortableTypeEntry],
) {
    std::mem::discriminant(args).hash(hasher);
    match args {
        ConstructorArguments::CstrTuple(types) => hash_type_expr_refs(hasher, types, entries),
        ConstructorArguments::CstrRecord(labels) => hash_label_decls(hasher, labels, entries),
    }
}

fn hash_extension_constructor(
    hasher: &mut impl Hasher,
    ext: &ExtensionConstructor,
    entries: &[PortableTypeEntry],
) {
    hash_path_by_name(hasher, &ext.ext_type_path);
    hash_attributes(hasher, &ext.ext_attributes);
    hash_type_expr_refs(hasher, &ext.ext_type_params, entries);
    hash_constructor_args(hasher, &ext.ext_args, entries);
    if let Some(ret) = ext.ext_ret_type {
        true.hash(hasher);
        hash_type_ref(hasher, ret.index(), entries, &mut Vec::new());
    } else {
        false.hash(hasher);
    }
    ext.ext_private.hash(hasher);
    ext.ext_is_exception.hash(hasher);
}

fn hash_modtype_decl(
    hasher: &mut impl Hasher,
    mtd: &ModtypeDeclaration,
    entries: &[PortableTypeEntry],
) {
    hash_attributes(hasher, &mtd.mtd_attributes);
    if let Some(mty) = &mtd.mtd_type {
        true.hash(hasher);
        hash_module_type(hasher, mty, entries);
    } else {
        false.hash(hasher);
    }
}

fn hash_module_type(hasher: &mut impl Hasher, mty: &ModuleType, entries: &[PortableTypeEntry]) {
    std::mem::discriminant(mty).hash(hasher);
    match mty {
        ModuleType::MtyIdent(path) => hash_path_by_name(hasher, path),
        ModuleType::MtySignature(sig) => hash_signature(hasher, sig, entries),
        ModuleType::MtyFunctor {
            param,
            param_type,
            result,
        } => {
            param.name().hash(hasher);
            if let Some(pt) = param_type {
                hash_module_type(hasher, pt, entries);
            }
            hash_module_type(hasher, result, entries);
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
pub fn serialize_pers_struct(
    ps: &PersStruct,
    ctx: &TypeContext,
    arena: Option<&ParseArena>,
) -> PortablePersStruct {
    let (sig, type_graph) = serialize_signature(ps.ps_sig.as_ref(), ctx, arena);
    let raw = ctx
        .find_raw_module_sig(&ps.ps_name)
        .map(|raw_sig| serialize_signature(&raw_sig, ctx, arena));
    let (raw_ps_sig, raw_type_graph) = match raw {
        Some((sig, graph)) => (Some(sig), Some(graph)),
        None => (None, None),
    };
    let fingerprint = compute_type_graph_fingerprint(&type_graph.entries, &sig);
    PortablePersStruct {
        ps_name: ps.ps_name.clone(),
        ps_filename: ps.ps_filename.clone(),
        ps_deprecated: ps.ps_deprecated.clone(),
        ps_crcs: ps.ps_crcs.clone(),
        ps_sig: sig,
        raw_ps_sig,
        cmi_longident_names: ctx.snapshot_cmi_longident_names(),
        type_graph,
        raw_type_graph,
        fingerprint,
    }
}

fn serialize_signature(
    sig: &Signature,
    ctx: &TypeContext,
    arena: Option<&ParseArena>,
) -> (Signature, PortableTypeGraph) {
    let mut ser = TypeGraphSerializer {
        ctx,
        arena,
        entries: Vec::new(),
        cache: HashMap::new(),
        variant_layouts: Vec::new(),
        variant_layout_cache: HashMap::new(),
        file_name_cache: HashMap::new(),
        mutabilities: Vec::new(),
        mutability_cache: HashMap::new(),
    };
    let mut sig = sig.clone();
    ser.remap_signature(&mut sig);
    ser.remap_signature_locations(&mut sig);
    let type_graph = PortableTypeGraph {
        entries: ser.entries,
        variant_layouts: ser.variant_layouts,
        mutabilities: ser.mutabilities,
    };
    (sig, type_graph)
}

struct TypeGraphSerializer<'a> {
    ctx: &'a TypeContext,
    arena: Option<&'a ParseArena>,
    entries: Vec<PortableTypeEntry>,
    cache: HashMap<TypeExprRef, usize>,
    variant_layouts: Vec<crate::types::VariantLayout>,
    variant_layout_cache: HashMap<crate::types::VariantLayoutRef, usize>,
    /// Source-arena file names re-interned as synthetic CMI names.
    file_name_cache: HashMap<crate::intern::StrIdx, crate::intern::StrIdx>,
    mutabilities: Vec<crate::types::asttypes::MutableFlag>,
    mutability_cache: HashMap<MutabilityRef, usize>,
}

impl<'a> TypeGraphSerializer<'a> {
    /// Remap the file names of every location in a signature (declarations
    /// and attributes) to names portable across contexts.
    fn remap_signature_locations(&mut self, sig: &mut Signature) {
        crate::types::decl::for_each_signature_location(sig, &mut |loc| self.remap_loc(loc));
    }

    /// Declaration locations name their file through the source arena's
    /// string table, which does not travel with the signature. Re-intern the
    /// name in the TypeContext's synthetic CMI name table, as reading a `.cmi`
    /// does (`sig_reader::read_location`), so the importing compile can
    /// resolve it.
    fn remap_loc(&mut self, loc: &mut crate::location::Location) {
        let Some(arena) = self.arena else {
            return;
        };
        for pos in [&mut loc.loc_start, &mut loc.loc_end] {
            let idx = pos.file_name;
            if idx == crate::intern::StrIdx::default()
                || self.ctx.resolve_cmi_longident_component(idx).is_some()
            {
                continue;
            }
            let ctx = self.ctx;
            pos.file_name = *self
                .file_name_cache
                .entry(idx)
                .or_insert_with(|| ctx.intern_cmi_longident_name(arena.get_string(idx)));
        }
    }

    /// Serialize a mutability cell, returning its portable index. Fields
    /// sharing a cell class share the index.
    fn serialize_mutability(&mut self, m: MutabilityRef) -> usize {
        let m = self.ctx.mutability_ref_repr(m);
        if let Some(&idx) = self.mutability_cache.get(&m) {
            return idx;
        }
        let idx = self.mutabilities.len();
        self.mutabilities.push(self.ctx.mutability_repr(m));
        self.mutability_cache.insert(m, idx);
        idx
    }

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
            TypeDesc::Tarrow { args, ret } => PortableTypeDesc::Tarrow {
                args: args
                    .iter()
                    .map(|arg| (arg.label().clone(), self.serialize_type(arg.typ)))
                    .collect(),
                ret: self.serialize_type(*ret),
            },
            TypeDesc::Ttuple(types) => {
                PortableTypeDesc::Ttuple(types.iter().map(|t| self.serialize_type(*t)).collect())
            }
            TypeDesc::Tconstr { path, args, .. } => PortableTypeDesc::Tconstr {
                path: path.clone(),
                args: args.iter().map(|t| self.serialize_type(*t)).collect(),
            },
            TypeDesc::Tobject { fields } => PortableTypeDesc::Tobject {
                fields: self.serialize_type(*fields),
            },
            TypeDesc::Tfield {
                name,
                mutability,
                typ,
                rest,
            } => PortableTypeDesc::Tfield {
                name: name.clone(),
                mutability: self.serialize_mutability(*mutability),
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
                lids: lids
                    .iter()
                    .map(|lid| self.serialize_longident(lid))
                    .collect(),
                args: args.iter().map(|t| self.serialize_type(*t)).collect(),
            },
        }
    }

    fn serialize_longident(&self, lid: &Longident) -> PortableLongident {
        match lid {
            Longident::Lident(idx) => {
                PortableLongident::Lident(self.resolve_longident_component(*idx))
            }
            Longident::Ldot(prefix, idx) => PortableLongident::Ldot(
                Box::new(self.serialize_longident(prefix)),
                self.resolve_longident_component(*idx),
            ),
            Longident::Lapply(functor, arg) => PortableLongident::Lapply(
                Box::new(self.serialize_longident(functor)),
                Box::new(self.serialize_longident(arg)),
            ),
        }
    }

    fn resolve_longident_component(&self, idx: crate::intern::StrIdx) -> String {
        if let Some(name) = self.ctx.resolve_cmi_longident_component(idx) {
            return name;
        }
        if let Some(arena) = self.arena {
            return arena.get_string(idx).to_string();
        }
        panic!(
            "portable type serialization invariant violated: unresolved Longident component #{}",
            idx.raw()
        );
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
            SignatureItem::SigType(_, td, _) => self.remap_type_decl(std::sync::Arc::make_mut(td)),
            SignatureItem::SigTypext(_, ec, _) => self.remap_ext_ctor(ec),
            SignatureItem::SigModule(_, md, _) => self.remap_module_decl(md),
            SignatureItem::SigModtype(_, mtd) => self.remap_modtype_decl(mtd),
            SignatureItem::SigClass | SignatureItem::SigClassType => {}
        }
    }

    fn remap_value_desc(&mut self, vd: &mut ValueDescription) {
        vd.val_type = TypeExprRef::from_usize(self.serialize_type(vd.val_type));
        self.remap_loc(&mut vd.val_loc);
    }

    fn remap_type_decl(&mut self, td: &mut TypeDeclaration) {
        self.remap_loc(&mut td.type_loc);
        if let TypeKind::TypeVariant(_, layout_ref) = &mut td.type_kind {
            let index = if let Some(index) = self.variant_layout_cache.get(layout_ref) {
                *index
            } else {
                let index = self.variant_layouts.len();
                self.variant_layouts
                    .push(self.ctx.variant_layout(*layout_ref));
                self.variant_layout_cache.insert(*layout_ref, index);
                index
            };
            *layout_ref = crate::types::VariantLayoutRef(index as u32);
        }
        for p in td.type_params.iter_mut() {
            *p = TypeExprRef::from_usize(self.serialize_type(*p));
        }
        if let Some(ref mut m) = td.type_manifest {
            *m = TypeExprRef::from_usize(self.serialize_type(*m));
        }
        match &mut td.type_kind {
            TypeKind::TypeAbstract | TypeKind::TypeOpen => {}
            TypeKind::TypeRecord(labels, _) => {
                for label in labels.iter_mut() {
                    self.remap_label_decl(label);
                }
            }
            TypeKind::TypeVariant(ctors, _) => {
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
        ld.ld_type = TypeExprRef::from_usize(self.serialize_type(ld.ld_type));
        self.remap_loc(&mut ld.ld_loc);
    }

    fn remap_ctor_decl(&mut self, cd: &mut ConstructorDeclaration) {
        self.remap_loc(&mut cd.cd_loc);
        match &mut cd.cd_args {
            ConstructorArguments::CstrTuple(types) => {
                for t in types.iter_mut() {
                    *t = TypeExprRef::from_usize(self.serialize_type(*t));
                }
            }
            ConstructorArguments::CstrRecord(labels) => {
                for label in labels.iter_mut() {
                    self.remap_label_decl(label);
                }
            }
        }
        if let Some(ref mut res) = cd.cd_res {
            *res = TypeExprRef::from_usize(self.serialize_type(*res));
        }
    }

    fn remap_ext_ctor(&mut self, ec: &mut ExtensionConstructor) {
        self.remap_loc(&mut ec.ext_loc);
        for p in ec.ext_type_params.iter_mut() {
            *p = TypeExprRef::from_usize(self.serialize_type(*p));
        }
        match &mut ec.ext_args {
            ConstructorArguments::CstrTuple(types) => {
                for t in types.iter_mut() {
                    *t = TypeExprRef::from_usize(self.serialize_type(*t));
                }
            }
            ConstructorArguments::CstrRecord(labels) => {
                for label in labels.iter_mut() {
                    self.remap_label_decl(label);
                }
            }
        }
        if let Some(ref mut ret) = ec.ext_ret_type {
            *ret = TypeExprRef::from_usize(self.serialize_type(*ret));
        }
    }

    fn remap_module_decl(&mut self, md: &mut ModuleDeclaration) {
        self.remap_loc(&mut md.md_loc);
        self.remap_module_type(&mut md.md_type);
    }

    fn remap_modtype_decl(&mut self, mtd: &mut ModtypeDeclaration) {
        self.remap_loc(&mut mtd.mtd_loc);
        if let Some(ref mut mt) = mtd.mtd_type {
            self.remap_module_type(mt);
        }
    }

    fn remap_module_type(&mut self, mt: &mut ModuleType) {
        match mt {
            ModuleType::MtySignature(sig) => self.remap_signature(crate::types::decl::signature_mut(sig)),
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

/// Where internalized type nodes and their side cells are allocated: the
/// compilation-local arena, or the worker store shared by every compilation
/// on the thread.
pub(crate) trait TypeNodeSink {
    fn abbrev_nil(&self) -> AbbrevMemoRef;
    fn longident_name(&self, name: &str) -> crate::intern::StrIdx;
    /// A cell for an internalized graph. Store and shared graphs outlive any
    /// one compilation, so they get persistent cells.
    fn new_mutability(&self, flag: crate::types::asttypes::MutableFlag) -> MutabilityRef {
        MutabilityRef::new_persistent(flag)
    }
}

/// The cells of an internalized graph, one per saved cell class.
fn internalize_mutabilities<S: TypeNodeSink>(graph: &PortableTypeGraph, sink: &S) -> Vec<MutabilityRef> {
    graph.mutabilities.iter().map(|flag| sink.new_mutability(*flag)).collect()
}

impl TypeNodeSink for TypeContext {
    fn abbrev_nil(&self) -> AbbrevMemoRef {
        self.alloc_abbrev_nil()
    }

    fn new_mutability(&self, flag: crate::types::asttypes::MutableFlag) -> MutabilityRef {
        self.alloc_mutability(crate::types::type_expr::FieldMutability::Value(flag))
    }

    fn longident_name(&self, name: &str) -> crate::intern::StrIdx {
        self.intern_cmi_longident_name(name)
    }
}

impl TypeNodeSink for ThreadTypeStore {
    fn abbrev_nil(&self) -> AbbrevMemoRef {
        self.alloc_abbrev(AbbrevMemo::Mnil)
    }

    fn longident_name(&self, name: &str) -> crate::intern::StrIdx {
        self.intern_longident_name(name)
    }
}

/// Whether a portable graph entry keeps the store's generic-level invariant.
///
/// OCaml saves every persistent node at `generic_level` (`Subst.typexp
/// ~for_saving`, `compiler/ml/subst.ml:160-163`) and never leaves `Tsubst`
/// markers behind. `Tlink` nodes carry whatever level they had before
/// `link_type` (`compiler/ml/btype.ml:107-115` reads through them and
/// `compiler/ml/ctype.ml:488-503` generalizes only representatives), so their
/// level is dead state and does not disqualify a graph.
fn entry_is_shareable(entry: &PortableTypeEntry) -> bool {
    // A non-generic entry is shareable too: every level and descriptor write
    // to a store node goes to the reading compilation's overlay, so each
    // compilation sees the published level and its own later changes, as
    // with a private copy.
    !matches!(entry.desc, PortableTypeDesc::Tsubst(_))
}

/// Whether a portable graph can live in the worker store; a graph that does
/// not satisfy the generic-level invariant is internalized locally so the
/// exclusive-mutation invariant of the store holds trivially.
fn graph_is_shareable(graph: &PortableTypeGraph) -> bool {
    graph.entries.iter().all(entry_is_shareable)
}

/// Load a PortablePersStruct for the current compilation.
///
/// The dependency graph is internalized once per worker thread into the
/// store (`compiler/ml/env.ml:669-678`: one `persistent_structures` entry per
/// process) and shared by every later compilation on that thread; per-unit
/// side tables (`cmi_longident_names`, GenType raw signatures) are still
/// filled for each compilation.
pub fn internalize_pers_struct(pps: Arc<PortablePersStruct>, ctx: &TypeContext) -> Arc<PersStruct> {
    if pps.raw_ps_sig.is_some() && pps.raw_type_graph.is_some() {
        ctx.register_gentype_portable_raw_module_sig(&pps.ps_name, pps.clone());
    }

    let store = ctx.thread_store();
    if let Some(ps) = store.pers_struct(&pps) {
        return ps;
    }

    let shareable = graph_is_shareable(&pps.type_graph);
    if crate::debug_flags::debug_store() {
        let non_generic = pps
            .type_graph
            .entries
            .iter()
            .filter(|entry| !entry_is_shareable(entry))
            .count();
        let mut kinds = std::collections::BTreeMap::new();
        for entry in pps
            .type_graph
            .entries
            .iter()
            .filter(|entry| !entry_is_shareable(entry))
        {
            let kind = match entry.desc {
                PortableTypeDesc::Tvar(_) => "Tvar",
                PortableTypeDesc::Tarrow { .. } => "Tarrow",
                PortableTypeDesc::Ttuple(_) => "Ttuple",
                PortableTypeDesc::Tconstr { .. } => "Tconstr",
                PortableTypeDesc::Tobject { .. } => "Tobject",
                PortableTypeDesc::Tfield { .. } => "Tfield",
                PortableTypeDesc::Tnil => "Tnil",
                PortableTypeDesc::Tlink(_) => "Tlink",
                PortableTypeDesc::Tsubst(_) => "Tsubst",
                PortableTypeDesc::Tvariant(_) => "Tvariant",
                PortableTypeDesc::Tunivar(_) => "Tunivar",
                PortableTypeDesc::Tpoly { .. } => "Tpoly",
                PortableTypeDesc::Tpackage { .. } => "Tpackage",
            };
            *kinds
                .entry(format!("{kind}@{}", entry.level))
                .or_insert(0usize) += 1;
        }
        if non_generic > 0 {
            eprintln!("[store] non-shareable kinds {}: {kinds:?}", pps.ps_name);
        }
        let tsubst = pps
            .type_graph
            .entries
            .iter()
            .filter(|entry| matches!(entry.desc, PortableTypeDesc::Tsubst(_)))
            .count();
        eprintln!(
            "[store] internalize {} entries={} shareable={shareable} non_generic={non_generic} tsubst={tsubst} store_types={}",
            pps.ps_name,
            pps.type_graph.entries.len(),
            store.type_count()
        );
    }
    if shareable {
        // Internalize once per build for every worker; the worker store
        // keeps the result so later units on this worker skip the pool map.
        let pool = store.shared_pool();
        let shared = pool.pers_struct(&pps, || {
            let mut sig = internalize_signature_into_shared(&pps.ps_sig, &pps.type_graph, pool)?;
            remap_signature_file_names(&mut sig, &pps.cmi_longident_names, &|name| {
                pool.intern_longident_name(name)
            });
            Some(Arc::new(PersStruct {
                ps_name: pps.ps_name.clone(),
                ps_sig: Arc::new(sig),
                ps_filename: pps.ps_filename.clone(),
                ps_deprecated: pps.ps_deprecated.clone(),
                ps_crcs: pps.ps_crcs.clone(),
            }))
        });
        if let Some(ps) = shared {
            store.insert_pers_struct(pps, ps.clone());
            return ps;
        }
    }
    let sig = if shareable {
        let mut sig = internalize_signature_into_store(&pps.ps_sig, &pps.type_graph, store);
        remap_signature_file_names(&mut sig, &pps.cmi_longident_names, &|name| {
            store.intern_longident_name(name)
        });
        sig
    } else {
        let mut sig = internalize_signature(&pps.ps_sig, &pps.type_graph, ctx);
        remap_signature_file_names(&mut sig, &pps.cmi_longident_names, &|name| {
            ctx.intern_cmi_longident_name(name)
        });
        sig
    };
    let ps = Arc::new(PersStruct {
        ps_name: pps.ps_name.clone(),
        ps_sig: Arc::new(sig),
        ps_filename: pps.ps_filename.clone(),
        ps_deprecated: pps.ps_deprecated.clone(),
        ps_crcs: pps.ps_crcs.clone(),
    });
    if shareable {
        store.insert_pers_struct(pps, ps.clone());
    }
    ps
}

/// Internalize a graph into the worker store. Store nodes are complete on
/// allocation: their indices are known before any node is pushed because the
/// store arena is append-only and nothing else allocates while this runs.
fn internalize_signature_into_store(
    portable_sig: &Signature,
    graph: &PortableTypeGraph,
    store: &ThreadTypeStore,
) -> Signature {
    let base = store.type_count();
    let remap: Vec<TypeExprRef> = (0..graph.entries.len())
        .map(|i| TypeExprRef::from_store_index(base + i))
        .collect();
    let mremap = internalize_mutabilities(graph, store);
    for (i, entry) in graph.entries.iter().enumerate() {
        let desc = internalize_desc(&entry.desc, &remap, &mremap, store);
        let level = match entry.desc {
            PortableTypeDesc::Tlink(_) => GENERIC_LEVEL,
            _ => entry.level,
        };
        let allocated = store.alloc_type(desc, level);
        assert_eq!(
            allocated, remap[i],
            "thread store arena grew during internalization"
        );
    }
    let layout_remap: Vec<_> = graph
        .variant_layouts
        .iter()
        .cloned()
        .map(|layout| store.alloc_complete_variant_layout(layout))
        .collect();
    let mut sig = portable_sig.clone();
    remap_signature_refs(&mut sig, &remap, &layout_remap);
    sig
}

/// Allocation sink for a graph being published to the shared pool: each
/// `Tconstr` gets the memo cell keyed by its own node index.
struct SharedSink<'a> {
    pool: &'a crate::types::shared_store::SharedTypePool,
    current: std::cell::Cell<u32>,
}

impl TypeNodeSink for SharedSink<'_> {
    fn abbrev_nil(&self) -> AbbrevMemoRef {
        AbbrevMemoRef::from_shared_index(self.current.get())
    }

    fn longident_name(&self, name: &str) -> crate::intern::StrIdx {
        self.pool.intern_longident_name(name)
    }
}

/// Internalize a graph into the process-wide shared pool. The graph is built
/// completely before it is published, and is immutable afterwards. `None`
/// when the pool has no room.
fn internalize_signature_into_shared(
    portable_sig: &Signature,
    graph: &PortableTypeGraph,
    pool: &crate::types::shared_store::SharedTypePool,
) -> Option<Signature> {
    let mut remap = Vec::new();
    let base = pool.publish(graph.entries.len(), graph.variant_layouts.len(), |base| {
        remap = (0..graph.entries.len())
            .map(|i| crate::types::shared_store::shared_ref(base, i))
            .collect();
        let sink = SharedSink {
            pool,
            current: std::cell::Cell::new(base),
        };
        let mremap = internalize_mutabilities(graph, &sink);
        let nodes = graph
            .entries
            .iter()
            .enumerate()
            .map(|(i, entry)| {
                sink.current.set(base + i as u32);
                let desc = internalize_desc(&entry.desc, &remap, &mremap, &sink);
                let level = match entry.desc {
                    PortableTypeDesc::Tlink(_) => GENERIC_LEVEL,
                    _ => entry.level,
                };
                (desc, level)
            })
            .collect();
        (nodes, graph.variant_layouts.clone())
    })?;
    let layout_remap: Vec<_> = (0..graph.variant_layouts.len())
        .map(|i| crate::types::VariantLayoutRef::from_shared_index(base + i as u32))
        .collect();
    let mut sig = portable_sig.clone();
    remap_signature_refs(&mut sig, &remap, &layout_remap);
    Some(sig)
}

pub(crate) fn internalize_raw_signature(
    pps: &PortablePersStruct,
    ctx: &TypeContext,
) -> Option<Signature> {
    let mut sig = internalize_signature(
        pps.raw_ps_sig.as_ref()?,
        pps.raw_type_graph.as_ref()?,
        ctx,
    );
    remap_signature_file_names(&mut sig, &pps.cmi_longident_names, &|name| {
        ctx.intern_cmi_longident_name(name)
    });
    Some(sig)
}

/// Locations of a portable signature name their files through the
/// publishing context's synthetic names; every context numbers those from the
/// same base, so give each imported name a fresh index in `ctx`.
fn remap_signature_file_names(
    sig: &mut Signature,
    names: &[(u32, String)],
    intern: &dyn Fn(&str) -> crate::intern::StrIdx,
) {
    let names: HashMap<u32, &str> = names.iter().map(|(raw, name)| (*raw, name.as_str())).collect();
    let mut fresh: HashMap<u32, crate::intern::StrIdx> = HashMap::new();
    crate::types::decl::for_each_signature_location(sig, &mut |loc| {
        for pos in [&mut loc.loc_start, &mut loc.loc_end] {
            let raw = pos.file_name.raw();
            if let Some(name) = names.get(&raw) {
                pos.file_name = *fresh
                    .entry(raw)
                    .or_insert_with(|| intern(name));
            }
        }
    });
}

fn internalize_signature(
    portable_sig: &Signature,
    graph: &PortableTypeGraph,
    ctx: &TypeContext,
) -> Signature {
    // Phase 1: allocate placeholder TypeExprRefs for all entries.
    let remap: Vec<TypeExprRef> = graph
        .entries
        .iter()
        .map(|entry| {
            let level = if entry.level >= GENERIC_LEVEL {
                GENERIC_LEVEL
            } else {
                entry.level
            };
            ctx.alloc_type_at_level(TypeDesc::Tvar(None), level)
        })
        .collect();

    // Phase 2: set descriptors using remapped refs.
    let mremap = internalize_mutabilities(graph, ctx);
    for (i, entry) in graph.entries.iter().enumerate() {
        let desc = internalize_desc(&entry.desc, &remap, &mremap, ctx);
        ctx.set_desc(remap[i], desc);
    }

    let layout_remap: Vec<_> = graph
        .variant_layouts
        .iter()
        .cloned()
        .map(|layout| ctx.alloc_complete_variant_layout(layout))
        .collect();

    // Phase 3: clone and remap the signature.
    let mut sig = portable_sig.clone();
    remap_signature_refs(&mut sig, &remap, &layout_remap);
    sig
}

fn internalize_desc<S: TypeNodeSink>(
    desc: &PortableTypeDesc,
    remap: &[TypeExprRef],
    mremap: &[MutabilityRef],
    ctx: &S,
) -> TypeDesc {
    match desc {
        PortableTypeDesc::Tvar(name) => TypeDesc::Tvar(name.clone()),
        PortableTypeDesc::Tarrow { args, ret } => TypeDesc::Tarrow {
            args: args
                .iter()
                .map(|(lbl, typ)| TypeArg::new(lbl.clone(), remap[*typ]))
                .collect(),
            ret: remap[*ret],
        },
        PortableTypeDesc::Ttuple(types) => {
            TypeDesc::Ttuple(types.iter().map(|&i| remap[i]).collect())
        }
        PortableTypeDesc::Tconstr { path, args } => TypeDesc::Tconstr {
            path: path.clone(),
            args: args.iter().map(|&i| remap[i]).collect(),
            abbrev: ctx.abbrev_nil(),
        },
        PortableTypeDesc::Tobject { fields } => TypeDesc::Tobject {
            fields: remap[*fields],
        },
        PortableTypeDesc::Tfield {
            name,
            mutability,
            typ,
            rest,
        } => TypeDesc::Tfield {
            name: name.clone(),
            mutability: mremap[*mutability],
            typ: remap[*typ],
            rest: remap[*rest],
        },
        PortableTypeDesc::Tnil => TypeDesc::Tnil,
        PortableTypeDesc::Tlink(i) => TypeDesc::Tlink(remap[*i]),
        PortableTypeDesc::Tsubst(i) => TypeDesc::Tsubst(remap[*i]),
        PortableTypeDesc::Tvariant(prd) => {
            TypeDesc::Tvariant(Box::new(internalize_row_desc(prd, remap, ctx)))
        }
        PortableTypeDesc::Tunivar(name) => TypeDesc::Tunivar(name.clone()),
        PortableTypeDesc::Tpoly { body, vars } => TypeDesc::Tpoly {
            body: remap[*body],
            vars: vars.iter().map(|&i| remap[i]).collect(),
        },
        PortableTypeDesc::Tpackage { path, lids, args } => TypeDesc::Tpackage {
            path: path.clone(),
            lids: Box::new(
                lids.iter()
                    .map(|lid| internalize_longident(lid, ctx))
                    .collect(),
            ),
            args: args.iter().map(|&i| remap[i]).collect(),
        },
    }
}

fn internalize_longident<S: TypeNodeSink>(lid: &PortableLongident, ctx: &S) -> Longident {
    match lid {
        PortableLongident::Lident(name) => Longident::Lident(ctx.longident_name(name)),
        PortableLongident::Ldot(prefix, name) => Longident::Ldot(
            Box::new(internalize_longident(prefix, ctx)),
            ctx.longident_name(name),
        ),
        PortableLongident::Lapply(functor, arg) => Longident::Lapply(
            Box::new(internalize_longident(functor, ctx)),
            Box::new(internalize_longident(arg, ctx)),
        ),
    }
}

fn internalize_row_desc<S: TypeNodeSink>(
    prd: &PortableRowDesc,
    remap: &[TypeExprRef],
    ctx: &S,
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

fn internalize_row_field<S: TypeNodeSink>(
    prf: &PortableRowField,
    remap: &[TypeExprRef],
    _ctx: &S,
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

fn remap_signature_refs(
    sig: &mut Signature,
    remap: &[TypeExprRef],
    layout_remap: &[crate::types::VariantLayoutRef],
) {
    for item in sig.iter_mut() {
        remap_sig_item_refs(item, remap, layout_remap);
    }
}

fn remap_sig_item_refs(
    item: &mut SignatureItem,
    remap: &[TypeExprRef],
    layout_remap: &[crate::types::VariantLayoutRef],
) {
    match item {
        SignatureItem::SigValue(_, vd) => remap_value_desc_refs(vd, remap),
        SignatureItem::SigType(_, td, _) => remap_type_decl_refs(std::sync::Arc::make_mut(td), remap, layout_remap),
        SignatureItem::SigTypext(_, ec, _) => remap_ext_ctor_refs(ec, remap),
        SignatureItem::SigModule(_, md, _) => remap_module_decl_refs(md, remap, layout_remap),
        SignatureItem::SigModtype(_, mtd) => remap_modtype_decl_refs(mtd, remap, layout_remap),
        SignatureItem::SigClass | SignatureItem::SigClassType => {}
    }
}

fn remap_value_desc_refs(vd: &mut ValueDescription, remap: &[TypeExprRef]) {
    vd.val_type = remap[vd.val_type.index()];
}

fn remap_type_decl_refs(
    td: &mut TypeDeclaration,
    remap: &[TypeExprRef],
    layout_remap: &[crate::types::VariantLayoutRef],
) {
    if let TypeKind::TypeVariant(_, layout_ref) = &mut td.type_kind {
        *layout_ref = layout_remap[layout_ref.0 as usize];
    }
    for p in td.type_params.iter_mut() {
        *p = remap[p.index()];
    }
    if let Some(ref mut m) = td.type_manifest {
        *m = remap[m.index()];
    }
    match &mut td.type_kind {
        TypeKind::TypeAbstract | TypeKind::TypeOpen => {}
        TypeKind::TypeRecord(labels, _) => {
            for label in labels.iter_mut() {
                remap_label_decl_refs(label, remap);
            }
        }
        TypeKind::TypeVariant(ctors, _) => {
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
    ld.ld_type = remap[ld.ld_type.index()];
}

fn remap_ctor_decl_refs(cd: &mut ConstructorDeclaration, remap: &[TypeExprRef]) {
    match &mut cd.cd_args {
        ConstructorArguments::CstrTuple(types) => {
            for t in types.iter_mut() {
                *t = remap[t.index()];
            }
        }
        ConstructorArguments::CstrRecord(labels) => {
            for label in labels.iter_mut() {
                remap_label_decl_refs(label, remap);
            }
        }
    }
    if let Some(ref mut res) = cd.cd_res {
        *res = remap[res.index()];
    }
}

fn remap_ext_ctor_refs(ec: &mut ExtensionConstructor, remap: &[TypeExprRef]) {
    for p in ec.ext_type_params.iter_mut() {
        *p = remap[p.index()];
    }
    match &mut ec.ext_args {
        ConstructorArguments::CstrTuple(types) => {
            for t in types.iter_mut() {
                *t = remap[t.index()];
            }
        }
        ConstructorArguments::CstrRecord(labels) => {
            for label in labels.iter_mut() {
                remap_label_decl_refs(label, remap);
            }
        }
    }
    if let Some(ref mut ret) = ec.ext_ret_type {
        *ret = remap[ret.index()];
    }
}

fn remap_module_decl_refs(
    md: &mut ModuleDeclaration,
    remap: &[TypeExprRef],
    layout_remap: &[crate::types::VariantLayoutRef],
) {
    remap_module_type_refs(&mut md.md_type, remap, layout_remap);
}

fn remap_modtype_decl_refs(
    mtd: &mut ModtypeDeclaration,
    remap: &[TypeExprRef],
    layout_remap: &[crate::types::VariantLayoutRef],
) {
    if let Some(ref mut mt) = mtd.mtd_type {
        remap_module_type_refs(mt, remap, layout_remap);
    }
}

fn remap_module_type_refs(
    mt: &mut ModuleType,
    remap: &[TypeExprRef],
    layout_remap: &[crate::types::VariantLayoutRef],
) {
    match mt {
        ModuleType::MtySignature(sig) => remap_signature_refs(crate::types::decl::signature_mut(sig), remap, layout_remap),
        ModuleType::MtyFunctor {
            param_type, result, ..
        } => {
            if let Some(pt) = param_type.as_mut() {
                remap_module_type_refs(pt, remap, layout_remap);
            }
            remap_module_type_refs(result, remap, layout_remap);
        }
        ModuleType::MtyIdent(_) | ModuleType::MtyAlias(_, _) => {}
    }
}

#[cfg(test)]
mod type_arg_tests {
    use super::*;
    use crate::context::IdGenerator;
    use crate::intern::StrIdx;
    use crate::location::{Location, Position};

    #[test]
    fn type_arg_portable_roundtrip_preserves_metadata_and_identity() {
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let shared = ctx.new_generic_var(Some("a".into()));
        let distinct = ctx.new_generic_var(Some("a".into()));
        let loc = Location {
            loc_start: Position::new(StrIdx(13), 3, 18, 21),
            loc_end: Position::new(StrIdx(19), 5, 31, 36),
            loc_ghost: true,
        };
        let labels = [
            ArgLabel::Nolabel,
            ArgLabel::labelled("λ", loc),
            ArgLabel::optional("opt", loc),
        ];
        let arrow = ctx.new_type(TypeDesc::Tarrow {
            args: vec![
                TypeArg::unlabeled(shared),
                TypeArg::new(labels[1].clone(), shared),
                TypeArg::new(labels[2].clone(), distinct),
            ].into(),
            ret: shared,
        });
        let mut ser = TypeGraphSerializer { ctx: &ctx, arena: None, entries: Vec::new(),
            cache: HashMap::new(), variant_layouts: Vec::new(), variant_layout_cache: HashMap::new(),
            file_name_cache: HashMap::new(), mutabilities: Vec::new(), mutability_cache: HashMap::new() };
        let index = ser.serialize_type(arrow);
        let PortableTypeDesc::Tarrow { args, ret } = &ser.entries[index].desc else {
            panic!("not arrow")
        };
        assert_eq!(args.len(), 3);
        assert_eq!(args[0].1, *ret);
        assert_eq!(args[1].1, *ret);
        assert_ne!(args[2].1, *ret);
        let remap: Vec<_> = ser.entries.iter().map(|_| ctx.new_var(None)).collect();
        let restored = internalize_desc(&ser.entries[index].desc, &remap, &[], &ctx);
        let TypeDesc::Tarrow { args, ret } = restored else {
            panic!("not arrow")
        };
        assert_eq!(args[0].typ, ret);
        assert_eq!(args[1].typ, ret);
        assert_ne!(args[2].typ, ret);
        for (arg, expected) in args.iter().zip(&labels) {
            assert_eq!(arg.label(), expected);
            if let ArgLabel::Labelled(l) | ArgLabel::Optional(l) = arg.label() {
                assert_eq!(l.loc.loc_start, loc.loc_start);
                assert_eq!(l.loc.loc_end, loc.loc_end);
                assert_eq!(l.loc.loc_ghost, loc.loc_ghost);
            }
        }
    }
}
