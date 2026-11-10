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

use crate::fast_hash::AHashMap;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use crate::parse_arena::ParseArena;
use crate::parser::longident::Longident;
use crate::types::asttypes::{ArgLabel, Located};
use crate::types::context::TypeContext;
use crate::types::decl::{
    ConstructorArguments, ConstructorDeclaration, ExtensionConstructor, LabelDeclaration,
    ModtypeDeclaration, ModuleDeclaration, ModuleType, Signature, SignatureItem, TypeDeclaration,
    TypeInlinedType, TypeKind, ValueDescription, ValueKind,
};
use crate::types::decl_loc::{DeclLoc, DeclLocImport, DeclLocTable};
use crate::types::path::Path;
use crate::types::thread_store::ThreadTypeStore;
use crate::types::type_expr::{
    AbbrevMemo, AbbrevMemoRef, GENERIC_LEVEL, MutabilityRef, RowDesc, RowField, RowFieldRef,
    TypeArg, TypeDesc, TypeExprRef,
};

use super::persistent_env::PersStruct;

// ============================================================================
// Portable type graph types
// ============================================================================

/// A self-contained type graph that can be loaded into any TypeContext.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
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
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct PortableTypeEntry {
    pub desc: PortableTypeDesc,
    pub level: i32,
}

/// TypeDesc with indices into `PortableTypeGraph.entries` instead of arena refs.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub enum PortableTypeDesc {
    Tvar(Option<crate::name::Name>),
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
        name: crate::name::Name,
        /// Index into `PortableTypeGraph.mutabilities`.
        mutability: usize,
        typ: usize,
        rest: usize,
    },
    Tnil,
    Tlink(usize),
    Tsubst(usize),
    Tvariant(PortableRowDesc),
    Tunivar(Option<crate::name::Name>),
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

#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum PortableLongident {
    Lident(String),
    Ldot(Box<PortableLongident>, String),
    Lapply(Box<PortableLongident>, Box<PortableLongident>),
}

/// Portable row description for polymorphic variants.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct PortableRowDesc {
    pub row_fields: Vec<(String, PortableRowField)>,
    pub row_more: usize,
    pub row_closed: bool,
    pub row_fixed: bool,
    pub row_name: Option<(Path, Vec<usize>)>,
}

/// Portable row field.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
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
///
/// The signatures and type graphs are kept encoded (see
/// [`crate::binser::Encoded`]): a build publishes one per compiled module and
/// keeps them until it ends, while each is decoded only a few times (once by
/// the shared pool that internalizes it for every worker, and for the
/// incremental-build digests). Decoded, they were the largest part of a large
/// build's memory.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct PortablePersStruct {
    pub ps_name: String,
    pub ps_filename: String,
    /// `PersStruct::ps_deprecated`.
    pub ps_deprecated: Option<String>,
    /// `PersStruct::ps_crcs`.
    pub ps_crcs: Vec<(String, Option<[u8; 16]>)>,
    /// Whether every entry of the type graph can live in a shared store
    /// (see `graph_is_shareable`).
    pub shareable: bool,
    /// The signature, its type graph and file names.
    sig: crate::binser::Encoded<PortableSignature>,
    /// [`PortableRawSignature`], when the module has one.
    raw: Option<crate::binser::Encoded<PortableRawSignature>>,
    /// Stamp-independent structural fingerprint of the type graph.
    /// Computed during serialization by hashing type structure with name-based
    /// path identity (ignoring stamps). Two compilations producing the same
    /// logical interface will have the same fingerprint even if internal stamps
    /// differ due to dependency changes.
    pub fingerprint: u64,
}

/// The decoded signature of a [`PortablePersStruct`].
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct PortableSignature {
    /// Signature with TypeExprRef values being indices into `type_graph.entries`.
    pub ps_sig: Signature,
    /// Synthetic longident component names created while reading CMI files.
    pub cmi_longident_names: Vec<(u32, String)>,
    /// Self-contained type graph.
    pub type_graph: PortableTypeGraph,
    /// Locations of the signature's declarations and of its type graph's
    /// labels (`DeclLocKind::Portable` handles). Empty for a location-free
    /// compilation.
    pub locations: DeclLocTable,
}

/// Raw `ps_sig` copy for OCaml-style lazy alias scraping.
///
/// OCaml stores `ps_sig = lazy (Subst.signature Subst.identity sign)` in
/// compiler/ml/env.ml:669-678 and compiler/ml/env.ml:1960-1977, separately
/// from component-table substitution at compiler/ml/env.ml:1513-1530. The
/// in-process registry crosses TypeContext boundaries, so carry that raw
/// copied signature portably instead of rebuilding it from the substituted
/// component signature later.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct PortableRawSignature {
    pub raw_ps_sig: Signature,
    /// Self-contained type graph for `raw_ps_sig`.
    pub raw_type_graph: PortableTypeGraph,
    /// Location table of `raw_ps_sig` and `raw_type_graph`.
    pub raw_locations: DeclLocTable,
}

impl PortablePersStruct {
    pub fn new(
        ps_name: String,
        ps_filename: String,
        ps_deprecated: Option<String>,
        ps_crcs: Vec<(String, Option<[u8; 16]>)>,
        sig: PortableSignature,
        raw: Option<PortableRawSignature>,
        fingerprint: u64,
    ) -> Self {
        Self::encode(
            ps_name,
            ps_filename,
            ps_deprecated,
            ps_crcs,
            &sig,
            raw.as_ref(),
            fingerprint,
        )
    }

    /// [`Self::new`] from borrowed signatures.
    fn encode(
        ps_name: String,
        ps_filename: String,
        ps_deprecated: Option<String>,
        ps_crcs: Vec<(String, Option<[u8; 16]>)>,
        sig: &PortableSignature,
        raw: Option<&PortableRawSignature>,
        fingerprint: u64,
    ) -> Self {
        PortablePersStruct {
            ps_name,
            ps_filename,
            ps_deprecated,
            ps_crcs,
            shareable: graph_is_shareable(&sig.type_graph),
            sig: crate::binser::Encoded::encode(sig),
            raw: raw.map(crate::binser::Encoded::encode),
            fingerprint,
        }
    }

    /// The signature, decoded.
    pub fn signature(&self) -> PortableSignature {
        self.sig.decode()
    }

    /// The raw signature, decoded, if the module has one.
    pub fn raw_signature(&self) -> Option<PortableRawSignature> {
        self.raw.as_ref().map(crate::binser::Encoded::decode)
    }

    pub fn has_raw_signature(&self) -> bool {
        self.raw.is_some()
    }
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
/// What hashing a signature reads of its portable type graph: the type
/// entries, and the variant layouts and object-field mutabilities that
/// entries and declarations refer to by index (indices follow allocation
/// order, so they are hashed by what they point to).
#[derive(Clone, Copy)]
pub struct HashGraph<'a> {
    pub entries: &'a [PortableTypeEntry],
    pub layouts: &'a [crate::types::VariantLayout],
    pub mutabilities: &'a [crate::types::asttypes::MutableFlag],
}

impl<'a> HashGraph<'a> {
    pub fn of(graph: &'a PortableTypeGraph) -> Self {
        HashGraph {
            entries: &graph.entries,
            layouts: &graph.variant_layouts,
            mutabilities: &graph.mutabilities,
        }
    }
}

impl std::ops::Deref for HashGraph<'_> {
    type Target = [PortableTypeEntry];
    fn deref(&self) -> &[PortableTypeEntry] {
        self.entries
    }
}

pub fn compute_type_graph_fingerprint(entries: &HashGraph<'_>, sig: &Signature) -> u64 {
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
    use crate::types::path::PathView as P;
    match path.view() {
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
    entries: &HashGraph<'_>,
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
    entries: &HashGraph<'_>,
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
    entries: &HashGraph<'_>,
    visiting: &mut Vec<usize>,
) {
    std::mem::discriminant(desc).hash(hasher);
    match desc {
        PortableTypeDesc::Tvar(name) => name.hash(hasher),
        PortableTypeDesc::Tarrow { args, ret } => {
            args.len().hash(hasher);
            for (label, arg) in args {
                // The label's kind and name; not where it was written.
                std::mem::discriminant(label).hash(hasher);
                match label {
                    crate::types::asttypes::ArgLabel::Nolabel => {}
                    crate::types::asttypes::ArgLabel::Labelled(name)
                    | crate::types::asttypes::ArgLabel::Optional(name) => name.txt.hash(hasher),
                }
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
            entries.mutabilities.get(*mutability).hash(hasher);
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
    entries: &HashGraph<'_>,
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
    entries: &HashGraph<'_>,
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
fn hash_signature(hasher: &mut impl Hasher, sig: &Signature, entries: &HashGraph<'_>) {
    sig.len().hash(hasher);
    for item in sig {
        hash_sig_item(hasher, item, entries);
    }
}

/// The fingerprint contribution of one signature item.
pub fn hash_sig_item(hasher: &mut impl Hasher, item: &SignatureItem, entries: &HashGraph<'_>) {
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
            match &md.md_path {
                Some(path) => {
                    true.hash(hasher);
                    hash_path_by_name(hasher, path);
                }
                None => false.hash(hasher),
            }
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

fn hash_value_desc(hasher: &mut impl Hasher, vd: &ValueDescription, entries: &HashGraph<'_>) {
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

fn hash_type_decl(hasher: &mut impl Hasher, td: &TypeDeclaration, entries: &HashGraph<'_>) {
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

fn hash_type_expr_refs(hasher: &mut impl Hasher, refs: &[TypeExprRef], entries: &HashGraph<'_>) {
    refs.len().hash(hasher);
    for r in refs {
        hash_type_ref(hasher, r.index(), entries, &mut Vec::new());
    }
}

fn hash_type_kind(hasher: &mut impl Hasher, kind: &TypeKind, entries: &HashGraph<'_>) {
    std::mem::discriminant(kind).hash(hasher);
    match kind {
        TypeKind::TypeAbstract | TypeKind::TypeOpen => {}
        // The representations decide dependents' JS (`@unboxed`, `@tag`,
        // inlined records).
        TypeKind::TypeRecord(labels, repr) => {
            hash_label_decls(hasher, labels, entries);
            std::mem::discriminant(repr).hash(hasher);
            match repr {
                crate::types::decl::RecordRepresentation::RecordUnboxed(flag) => flag.hash(hasher),
                crate::types::decl::RecordRepresentation::RecordInlined {
                    name,
                    representation,
                } => {
                    name.hash(hasher);
                    representation.position.hash(hasher);
                    format!(
                        "{:?}",
                        entries.layouts.get(representation.variant.0 as usize)
                    )
                    .hash(hasher);
                }
                _ => {}
            }
        }
        TypeKind::TypeVariant(ctors, layout) => {
            format!("{:?}", entries.layouts.get(layout.0 as usize)).hash(hasher);
            ctors.len().hash(hasher);
            for ctor in ctors {
                ctor.cd_id.name().hash(hasher);
                // The run-time tag (`@as`).
                format!("{:?}", ctor.cd_runtime_tag).hash(hasher);
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
    entries: &HashGraph<'_>,
) {
    labels.len().hash(hasher);
    for label in labels {
        label.ld_id.name().hash(hasher);
        // The run-time field name (`@as`).
        label.ld_runtime_name.hash(hasher);
        hash_attributes(hasher, &label.ld_attributes);
        label.ld_mutable.hash(hasher);
        label.ld_optional.hash(hasher);
        hash_type_ref(hasher, label.ld_type.index(), entries, &mut Vec::new());
    }
}

fn hash_constructor_args(
    hasher: &mut impl Hasher,
    args: &ConstructorArguments,
    entries: &HashGraph<'_>,
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
    entries: &HashGraph<'_>,
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

fn hash_modtype_decl(hasher: &mut impl Hasher, mtd: &ModtypeDeclaration, entries: &HashGraph<'_>) {
    hash_attributes(hasher, &mtd.mtd_attributes);
    if let Some(mty) = &mtd.mtd_type {
        true.hash(hasher);
        hash_module_type(hasher, mty, entries);
    } else {
        false.hash(hasher);
    }
}

fn hash_module_type(hasher: &mut impl Hasher, mty: &ModuleType, entries: &HashGraph<'_>) {
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
    // The file names of the signatures' locations travel with them, keyed
    // in order of first use (see `PortableFileNames`).
    let mut file_names = PortableFileNames::default();
    let (sig, type_graph, locations) =
        serialize_signature(ps.ps_sig.as_ref(), ctx, arena, &mut file_names);
    let raw = ctx
        .find_raw_module_sig(&ps.ps_name)
        .map(|raw_sig| serialize_signature(&raw_sig, ctx, arena, &mut file_names));
    let fingerprint = compute_type_graph_fingerprint(&HashGraph::of(&type_graph), &sig);
    let sig = PortableSignature {
        ps_sig: sig,
        cmi_longident_names: file_names.names,
        type_graph,
        locations,
    };
    let raw = raw.map(
        |(raw_ps_sig, raw_type_graph, raw_locations)| PortableRawSignature {
            raw_ps_sig,
            raw_type_graph,
            raw_locations,
        },
    );
    let encode = || {
        PortablePersStruct::encode(
            ps.ps_name.clone(),
            ps.ps_filename.clone(),
            ps.ps_deprecated.clone(),
            ps.ps_crcs.clone(),
            &sig,
            raw.as_ref(),
            fingerprint,
        )
    };
    // Store binders the signature mentions are saved with the local stamps
    // they stand for (see `TypeContext::saved_store_stamps`); most
    // signatures mention none, so the table is only built for those that do.
    let (portable, has_store_stamps) =
        crate::ident::saving_store_stamps(Default::default(), encode);
    if !has_store_stamps {
        return portable;
    }
    let (portable, unmapped) = crate::ident::saving_store_stamps(ctx.saved_store_stamps(), encode);
    if unmapped {
        log::debug!(
            "the signature of {} keeps a store stamp this compilation did not build or replay",
            ps.ps_name
        );
    }
    portable
}

/// Serialize `sig` with its location table, adding the file names of its
/// locations to `file_names`.
fn serialize_signature(
    sig: &Signature,
    ctx: &TypeContext,
    arena: Option<&ParseArena>,
    file_names: &mut PortableFileNames,
) -> (Signature, PortableTypeGraph, DeclLocTable) {
    let mut ser = TypeGraphSerializer::new(ctx, arena, file_names);
    let mut sig = sig.clone();
    ser.remap_signature(&mut sig);
    ser.remap_signature_locations(&mut sig);
    let type_graph = PortableTypeGraph {
        entries: ser.entries,
        variant_layouts: ser.variant_layouts,
        mutabilities: ser.mutabilities,
    };
    (sig, type_graph, ser.locations)
}

struct TypeGraphSerializer<'a, 'f> {
    ctx: &'a TypeContext,
    arena: Option<&'a ParseArena>,
    entries: Vec<PortableTypeEntry>,
    /// The node of each entry.
    nodes: Vec<TypeExprRef>,
    cache: AHashMap<TypeExprRef, usize>,
    variant_layouts: Vec<crate::types::VariantLayout>,
    variant_layout_cache: AHashMap<crate::types::VariantLayoutRef, usize>,
    mutabilities: Vec<crate::types::asttypes::MutableFlag>,
    mutability_cache: AHashMap<MutabilityRef, usize>,
    /// Locations of the serialized declarations and labels.
    locations: DeclLocTable,
    /// File names of the locations, by portable key.
    file_names: &'f mut PortableFileNames,
}

/// First key of a portable signature's file names.
const PORTABLE_FILE_KEY_BASE: u32 = 0xF000_0000;

/// The file names of a portable signature's locations
/// (`PortableSignature::cmi_longident_names`), keyed in order of first use.
///
/// A compilation names files by indices of whichever table interned them:
/// its source arena, its own synthetic CMI names, or the process-wide shared
/// pool, whose indices depend on the order in which worker threads
/// internalized their dependencies. Keying the names by first use makes the
/// encoding of a signature independent of those indices, so equal
/// signatures encode to equal bytes, and keeps every name with the
/// signature, so a signature stored by one process names its files in
/// another (`FileRemap`).
#[derive(Default)]
struct PortableFileNames {
    /// Key of each file index seen.
    keys: AHashMap<crate::intern::StrIdx, crate::intern::StrIdx>,
    /// Key of each name.
    by_name: AHashMap<String, u32>,
    /// `(key, name)`, in key order.
    names: Vec<(u32, String)>,
}

impl PortableFileNames {
    /// The portable key of `file`, a file index of `ctx` or `arena`. The
    /// empty name (`Location::none`) and names that resolve nowhere are kept
    /// as they are.
    fn key(
        &mut self,
        file: crate::intern::StrIdx,
        ctx: &TypeContext,
        arena: Option<&ParseArena>,
    ) -> crate::intern::StrIdx {
        if file == crate::intern::StrIdx::default() {
            return file;
        }
        if let Some(key) = self.keys.get(&file) {
            return *key;
        }
        let Some(name) = ctx
            .resolve_cmi_longident_component(file)
            .or_else(|| arena.map(|arena| arena.get_string(file).to_string()))
        else {
            return file;
        };
        let next = PORTABLE_FILE_KEY_BASE + self.names.len() as u32;
        let key = *self.by_name.entry(name.clone()).or_insert_with(|| {
            self.names.push((next, name));
            next
        });
        let key = crate::intern::StrIdx::from_raw(key);
        self.keys.insert(file, key);
        key
    }
}

impl<'a, 'f> TypeGraphSerializer<'a, 'f> {
    fn new(
        ctx: &'a TypeContext,
        arena: Option<&'a ParseArena>,
        file_names: &'f mut PortableFileNames,
    ) -> Self {
        TypeGraphSerializer {
            ctx,
            arena,
            entries: Vec::new(),
            nodes: Vec::new(),
            cache: AHashMap::new(),
            variant_layouts: Vec::new(),
            variant_layout_cache: AHashMap::new(),
            mutabilities: Vec::new(),
            mutability_cache: AHashMap::new(),
            locations: DeclLocTable::default(),
            file_names,
        }
    }

    /// Move every location of a signature (declarations and attributes) to
    /// the portable table, with file names portable across contexts.
    fn remap_signature_locations(&mut self, sig: &mut Signature) {
        crate::types::decl::for_each_signature_location(sig, &mut |loc| {
            *loc = self.portable_loc(*loc);
        });
    }

    /// The portable handle of a location of the serialized context, naming
    /// its file by portable key.
    fn portable_loc(&mut self, loc: DeclLoc) -> DeclLoc {
        let identity = self.ctx.location_identity(loc);
        let mut loc = self.ctx.resolve_loc(loc);
        for pos in [&mut loc.loc_start, &mut loc.loc_end] {
            pos.file_name = self.file_names.key(pos.file_name, self.ctx, self.arena);
        }
        match identity {
            Some(identity) => self.locations.intern_with_identity(loc, identity),
            None => self.locations.intern(loc),
        }
    }

    fn portable_label(&mut self, label: &ArgLabel) -> ArgLabel {
        match label {
            ArgLabel::Nolabel => ArgLabel::Nolabel,
            ArgLabel::Labelled(l) => {
                ArgLabel::Labelled(Located::new(l.txt.clone(), self.portable_loc(l.loc)))
            }
            ArgLabel::Optional(l) => {
                ArgLabel::Optional(Located::new(l.txt.clone(), self.portable_loc(l.loc)))
            }
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
        self.nodes.push(r);
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
            TypeDesc::Tvar(name) => PortableTypeDesc::Tvar(*name),
            TypeDesc::Tarrow { args, ret } => PortableTypeDesc::Tarrow {
                args: self
                    .ctx
                    .type_args(args)
                    .iter()
                    .map(|arg| {
                        (
                            self.portable_label(&arg.label().to_arg_label()),
                            self.serialize_type(arg.typ),
                        )
                    })
                    .collect(),
                ret: self.serialize_type(*ret),
            },
            TypeDesc::Ttuple(types) => {
                PortableTypeDesc::Ttuple(self.ctx.type_list(types).iter().map(|t| self.serialize_type(t)).collect())
            }
            TypeDesc::Tconstr { path, args, .. } => PortableTypeDesc::Tconstr {
                path: *path,
                args: self.ctx.type_list(args).iter().map(|t| self.serialize_type(t)).collect(),
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
                name: *name,
                mutability: self.serialize_mutability(*mutability),
                typ: self.serialize_type(*typ),
                rest: self.serialize_type(*rest),
            },
            TypeDesc::Tnil => PortableTypeDesc::Tnil,
            TypeDesc::Tlink(r) => PortableTypeDesc::Tlink(self.serialize_type(*r)),
            TypeDesc::Tsubst(r) => PortableTypeDesc::Tsubst(self.serialize_type(*r)),
            TypeDesc::Tvariant(row_desc) => {
                PortableTypeDesc::Tvariant(self.serialize_row_desc(&self.ctx.row_desc(row_desc)))
            }
            TypeDesc::Tunivar(name) => PortableTypeDesc::Tunivar(*name),
            TypeDesc::Tpoly { body, vars } => PortableTypeDesc::Tpoly {
                body: self.serialize_type(*body),
                vars: self.ctx.type_list(vars).iter().map(|t| self.serialize_type(t)).collect(),
            },
            TypeDesc::Tpackage { path, lids, args } => PortableTypeDesc::Tpackage {
                path: *path,
                lids: self
                    .ctx
                    .package_lids(lids)
                    .iter()
                    .map(|lid| self.serialize_longident(lid))
                    .collect(),
                args: self.ctx.type_list(args).iter().map(|t| self.serialize_type(t)).collect(),
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
                    *p,
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
    }

    fn remap_type_decl(&mut self, td: &mut TypeDeclaration) {
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
    }

    fn remap_ctor_decl(&mut self, cd: &mut ConstructorDeclaration) {
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
        self.remap_module_type(&mut md.md_type);
    }

    fn remap_modtype_decl(&mut self, mtd: &mut ModtypeDeclaration) {
        if let Some(ref mut mt) = mtd.mtd_type {
            self.remap_module_type(mt);
        }
    }

    fn remap_module_type(&mut self, mt: &mut ModuleType) {
        match mt {
            ModuleType::MtySignature(sig) => {
                self.remap_signature(crate::types::decl::signature_mut(sig))
            }
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
    fn new_type_list(&self, items: &[TypeExprRef]) -> crate::types::type_expr::TypeRefList;
    fn new_type_args(&self, args: &[TypeArg]) -> crate::types::type_expr::TypeArgList;
    fn new_row_desc(&self, row: RowDesc) -> crate::types::type_expr::RowDescRef;
    fn new_package_lids(
        &self,
        lids: Vec<crate::parser::longident::Longident>,
    ) -> crate::types::type_expr::PackageLidsRef;
    fn new_type_list_from_iter(
        &self,
        items: impl Iterator<Item = TypeExprRef>,
    ) -> crate::types::type_expr::TypeRefList {
        let items: crate::types::type_expr::TypeRefs = items.collect();
        self.new_type_list(&items)
    }
    /// A cell for an internalized graph. Store and shared graphs outlive any
    /// one compilation, so they get persistent cells.
    fn new_mutability(&self, flag: crate::types::asttypes::MutableFlag) -> MutabilityRef {
        MutabilityRef::new_persistent(flag)
    }
}

/// The cells of an internalized graph, one per saved cell class.
fn internalize_mutabilities<S: TypeNodeSink>(
    graph: &PortableTypeGraph,
    sink: &S,
) -> Vec<MutabilityRef> {
    graph
        .mutabilities
        .iter()
        .map(|flag| sink.new_mutability(*flag))
        .collect()
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

    fn new_type_list(&self, items: &[TypeExprRef]) -> crate::types::type_expr::TypeRefList {
        TypeContext::new_type_list(self, items)
    }

    fn new_type_args(&self, args: &[TypeArg]) -> crate::types::type_expr::TypeArgList {
        TypeContext::new_type_args(self, args)
    }

    fn new_row_desc(&self, row: RowDesc) -> crate::types::type_expr::RowDescRef {
        TypeContext::new_row_desc(self, row)
    }

    fn new_package_lids(
        &self,
        lids: Vec<crate::parser::longident::Longident>,
    ) -> crate::types::type_expr::PackageLidsRef {
        TypeContext::new_package_lids(self, lids)
    }
}

impl TypeNodeSink for ThreadTypeStore {




    fn abbrev_nil(&self) -> AbbrevMemoRef {
        self.alloc_abbrev(AbbrevMemo::Mnil)
    }

    fn longident_name(&self, name: &str) -> crate::intern::StrIdx {
        self.intern_longident_name(name)
    }



    fn new_type_list(&self, items: &[TypeExprRef]) -> crate::types::type_expr::TypeRefList {
        self.alloc_type_list(items)
    }

    fn new_type_args(&self, args: &[TypeArg]) -> crate::types::type_expr::TypeArgList {
        self.alloc_type_args(args)
    }

    fn new_row_desc(&self, row: RowDesc) -> crate::types::type_expr::RowDescRef {
        self.alloc_row_desc(row)
    }

    fn new_package_lids(
        &self,
        lids: Vec<crate::parser::longident::Longident>,
    ) -> crate::types::type_expr::PackageLidsRef {
        self.alloc_package_lids(lids)
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
    if pps.has_raw_signature() {
        ctx.register_gentype_portable_raw_module_sig(&pps.ps_name, pps.clone());
    }

    let store = ctx.thread_store();
    if let Some(ps) = store.pers_struct(&pps) {
        return ps;
    }

    let shareable = pps.shareable;
    if shareable {
        // Internalize once per build for every worker; the worker store
        // keeps the result so later units on this worker skip the pool map.
        let pool = store.shared_pool();
        let shared = pool.pers_struct(&pps, || {
            let portable = pps.signature();
            let intern = |name: &str| pool.intern_longident_name(name);
            let files = FileRemap::new(&portable.cmi_longident_names, &intern);
            let sig = internalize_signature_into_shared(
                &portable.ps_sig,
                &portable.type_graph,
                &portable.locations,
                &files,
                pool,
            )?;
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
        let portable = pps.signature();
        let intern = |name: &str| store.intern_longident_name(name);
        let files = FileRemap::new(&portable.cmi_longident_names, &intern);
        let map = |file| files.map(file);
        let locs = store.import_portable_decl_locs(&portable.locations, &map);
        internalize_signature_into_store(&portable.ps_sig, &portable.type_graph, &locs, store)
    } else {
        let portable = pps.signature();
        let intern = |name: &str| ctx.intern_cmi_longident_name(name);
        let files = FileRemap::new(&portable.cmi_longident_names, &intern);
        let map = |file| files.map(file);
        let locs = ctx.import_portable_decl_locs(&portable.locations, &map);
        internalize_signature(&portable.ps_sig, &portable.type_graph, &locs, ctx)
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
    locs: &DeclLocImport<'_>,
    store: &ThreadTypeStore,
) -> Signature {
    let base = store.type_count();
    let remap: Vec<TypeExprRef> = (0..graph.entries.len())
        .map(|i| TypeExprRef::from_store_index(base + i))
        .collect();
    let mremap = internalize_mutabilities(graph, store);
    for (i, entry) in graph.entries.iter().enumerate() {
        let desc = internalize_desc(&entry.desc, &remap, &mremap, locs, store);
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
    let mut shapes = crate::types::variant_runtime::ShapeImport::new(&locs.scopes);
    let layout_remap: Vec<_> = graph
        .variant_layouts
        .iter()
        .cloned()
        .map(|mut layout| {
            shapes.layout(&mut layout);
            store.alloc_complete_variant_layout(layout)
        })
        .collect();
    let mut sig = portable_sig.clone();
    remap_signature_refs(&mut sig, &remap, &layout_remap);
    import_signature_locations(&mut sig, locs);
    shapes.signature(&mut sig);
    sig
}

/// Allocation sink for a graph being published to the shared pool: each
/// `Tconstr` gets the memo cell keyed by its own node index.
struct SharedSink<'a> {
    pool: &'a crate::types::shared_store::SharedTypePool,
    current: std::cell::Cell<u32>,
    /// The graph's base index and sizes, which place each payload section.
    base: u32,
    sizes: crate::types::shared_store::SharedGraphSizes,
    /// Payloads allocated so far.
    payloads: std::cell::RefCell<crate::types::shared_store::SharedGraphPayloads>,
}

impl SharedSink<'_> {
    /// Tagged shared index of entry `len` of the section at `start`.
    fn section_index(&self, start: usize, len: usize) -> u32 {
        (self.base + (start + len) as u32) | crate::types::type_expr::SHARED_REF_BITS
    }
}

impl TypeNodeSink for SharedSink<'_> {




    fn abbrev_nil(&self) -> AbbrevMemoRef {
        AbbrevMemoRef::from_shared_index(self.current.get())
    }

    fn longident_name(&self, name: &str) -> crate::intern::StrIdx {
        self.pool.intern_longident_name(name)
    }


    fn new_type_list(&self, items: &[TypeExprRef]) -> crate::types::type_expr::TypeRefList {
        let mut payloads = self.payloads.borrow_mut();
        let start = self.section_index(self.sizes.lists_start(), payloads.lists.len());
        payloads.lists.extend_from_slice(items);
        crate::types::type_expr::TypeRefList::from_parts(start, items.len())
    }

    fn new_type_args(&self, args: &[TypeArg]) -> crate::types::type_expr::TypeArgList {
        let mut payloads = self.payloads.borrow_mut();
        let start = self.section_index(self.sizes.args_start(), payloads.args.len());
        payloads.args.extend_from_slice(args);
        crate::types::type_expr::TypeArgList::from_parts(start, args.len())
    }

    fn new_row_desc(&self, row: RowDesc) -> crate::types::type_expr::RowDescRef {
        let mut payloads = self.payloads.borrow_mut();
        let index = self.section_index(self.sizes.rows_start(), payloads.rows.len());
        payloads.rows.push(row);
        crate::types::type_expr::RowDescRef::from_raw(index)
    }

    fn new_package_lids(
        &self,
        lids: Vec<crate::parser::longident::Longident>,
    ) -> crate::types::type_expr::PackageLidsRef {
        let mut payloads = self.payloads.borrow_mut();
        let index = self.section_index(self.sizes.lids_start(), payloads.lids.len());
        payloads.lids.push(lids);
        crate::types::type_expr::PackageLidsRef::from_raw(index)
    }
}

/// Sizes of the shared graph `internalize_desc` builds for `graph`: one
/// payload per type list element, arrow parameter, row and package.
fn shared_graph_sizes(graph: &PortableTypeGraph) -> crate::types::shared_store::SharedGraphSizes {
    let mut sizes = crate::types::shared_store::SharedGraphSizes {
        nodes: graph.entries.len(),
        layouts: graph.variant_layouts.len(),
        ..Default::default()
    };
    for entry in &graph.entries {
        match &entry.desc {
            PortableTypeDesc::Ttuple(items) => sizes.list_items += items.len(),
            PortableTypeDesc::Tconstr { args, .. } => sizes.list_items += args.len(),
            PortableTypeDesc::Tpackage { args, .. } => {
                sizes.list_items += args.len();
                sizes.lids += 1;
            }
            PortableTypeDesc::Tpoly { vars, .. } => sizes.list_items += vars.len(),
            PortableTypeDesc::Tarrow { args, .. } => sizes.arg_items += args.len(),
            PortableTypeDesc::Tvariant(_) => sizes.rows += 1,
            _ => {}
        }
    }
    sizes
}

/// Internalize a graph into the process-wide shared pool. The graph is built
/// completely before it is published, and is immutable afterwards. `None`
/// when the pool has no room.
fn internalize_signature_into_shared(
    portable_sig: &Signature,
    graph: &PortableTypeGraph,
    locations: &DeclLocTable,
    files: &FileRemap<'_>,
    pool: &crate::types::shared_store::SharedTypePool,
) -> Option<Signature> {
    let mut remap = Vec::new();
    let mut sig = portable_sig.clone();
    let mut scopes = crate::fast_hash::AHashMap::default();
    let map = |file| files.map(file);
    let sizes = shared_graph_sizes(graph);
    let base = pool.publish(sizes, |base| {
        remap = (0..graph.entries.len())
            .map(|i| crate::types::shared_store::shared_ref(base, i))
            .collect();
        let sink = SharedSink {
            pool,
            current: std::cell::Cell::new(base),
            base,
            sizes,
            payloads: Default::default(),
        };
        let locs = shared_decl_locs(base, &map);
        let mremap = internalize_mutabilities(graph, &sink);
        let nodes = graph
            .entries
            .iter()
            .enumerate()
            .map(|(i, entry)| {
                sink.current.set(base + i as u32);
                let desc =
                    internalize_desc(&entry.desc, &remap, &mremap, &locs, &sink);
                let level = match entry.desc {
                    PortableTypeDesc::Tlink(_) => GENERIC_LEVEL,
                    _ => entry.level,
                };
                (desc, level)
            })
            .collect();
        let mut table = locations.clone();
        scopes = table.remap_for_import(&map);
        let mut shapes = crate::types::variant_runtime::ShapeImport::new(&scopes);
        let layouts = graph
            .variant_layouts
            .iter()
            .cloned()
            .map(|mut layout| {
                shapes.layout(&mut layout);
                layout
            })
            .collect();
        shapes.signature(&mut sig);
        crate::types::shared_store::SharedGraphParts {
            nodes,
            payloads: sink.payloads.into_inner(),
            layouts,
            locations: table,
        }
    })?;
    let layout_remap: Vec<_> = (0..graph.variant_layouts.len())
        .map(|i| crate::types::VariantLayoutRef::from_shared_index(base + i as u32))
        .collect();
    remap_signature_refs(&mut sig, &remap, &layout_remap);
    import_signature_locations(&mut sig, &shared_decl_locs(base, &map));
    Some(sig)
}

/// The handles of a graph published to the shared pool at `base`: portable
/// entry `i` is entry `i` of that graph's own table.
fn shared_decl_locs<'a>(
    base: u32,
    files: &'a dyn Fn(crate::intern::StrIdx) -> crate::intern::StrIdx,
) -> DeclLocImport<'a> {
    DeclLocImport {
        kind: crate::types::decl_loc::DeclLocKind::Shared,
        owner: base,
        base: 0,
        instances: Vec::new(),
        files,
        scopes: Default::default(),
    }
}

pub(crate) fn internalize_raw_signature(
    pps: &PortablePersStruct,
    ctx: &TypeContext,
) -> Option<Signature> {
    let raw = pps.raw_signature()?;
    let names = pps.signature().cmi_longident_names;
    let intern = |name: &str| ctx.intern_cmi_longident_name(name);
    let files = FileRemap::new(&names, &intern);
    let map = |file| files.map(file);
    let locs = ctx.import_portable_decl_locs(&raw.raw_locations, &map);
    Some(internalize_signature(
        &raw.raw_ps_sig,
        &raw.raw_type_graph,
        &locs,
        ctx,
    ))
}

/// Locations of a portable signature name their files through the
/// publishing context's synthetic names; every context numbers those from the
/// same base, so each imported name gets a fresh index in the importing
/// owner, once.
struct FileRemap<'a> {
    names: AHashMap<u32, &'a str>,
    fresh: std::cell::RefCell<AHashMap<u32, crate::intern::StrIdx>>,
    intern: &'a dyn Fn(&str) -> crate::intern::StrIdx,
}

impl<'a> FileRemap<'a> {
    fn new(names: &'a [(u32, String)], intern: &'a dyn Fn(&str) -> crate::intern::StrIdx) -> Self {
        FileRemap {
            names: names
                .iter()
                .map(|(raw, name)| (*raw, name.as_str()))
                .collect(),
            fresh: Default::default(),
            intern,
        }
    }

    fn map(&self, file: crate::intern::StrIdx) -> crate::intern::StrIdx {
        let raw = file.raw();
        let Some(name) = self.names.get(&raw) else {
            return file;
        };
        if let Some(fresh) = self.fresh.borrow().get(&raw) {
            return *fresh;
        }
        let fresh = (self.intern)(name);
        self.fresh.borrow_mut().insert(raw, fresh);
        fresh
    }
}

/// Point the declaration and attribute locations of an internalized
/// signature at the importer's table.
fn import_signature_locations(sig: &mut Signature, locs: &DeclLocImport<'_>) {
    crate::types::decl::for_each_signature_location(sig, &mut |loc| *loc = locs.import(*loc));
}

fn import_label(label: &ArgLabel, locs: &DeclLocImport<'_>) -> ArgLabel {
    match label {
        ArgLabel::Nolabel => ArgLabel::Nolabel,
        ArgLabel::Labelled(l) => {
            ArgLabel::Labelled(Located::new(l.txt.clone(), locs.import(l.loc)))
        }
        ArgLabel::Optional(l) => {
            ArgLabel::Optional(Located::new(l.txt.clone(), locs.import(l.loc)))
        }
    }
}

fn internalize_signature(
    portable_sig: &Signature,
    graph: &PortableTypeGraph,
    locs: &DeclLocImport<'_>,
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
            ctx.alloc_type_at_level(
                TypeDesc::Tvar(None),
                level,
            )
        })
        .collect();

    // Phase 2: set descriptors using remapped refs.
    let mremap = internalize_mutabilities(graph, ctx);
    for (i, entry) in graph.entries.iter().enumerate() {
        let desc = internalize_desc(&entry.desc, &remap, &mremap, locs, ctx);
        ctx.set_desc(remap[i], desc);
    }

    let mut shapes = crate::types::variant_runtime::ShapeImport::new(&locs.scopes);
    let layout_remap: Vec<_> = graph
        .variant_layouts
        .iter()
        .cloned()
        .map(|mut layout| {
            shapes.layout(&mut layout);
            ctx.alloc_complete_variant_layout(layout)
        })
        .collect();

    // Phase 3: clone and remap the signature.
    let mut sig = portable_sig.clone();
    remap_signature_refs(&mut sig, &remap, &layout_remap);
    import_signature_locations(&mut sig, locs);
    shapes.signature(&mut sig);
    sig
}

/// The descriptor of entry `entry` of a graph, imported as node `node`.
#[allow(clippy::too_many_arguments)]
fn internalize_desc<S: TypeNodeSink>(
    desc: &PortableTypeDesc,
    remap: &[TypeExprRef],
    mremap: &[MutabilityRef],
    locs: &DeclLocImport<'_>,
    ctx: &S,
) -> TypeDesc {
    match desc {
        PortableTypeDesc::Tvar(name) => TypeDesc::Tvar(*name),
        PortableTypeDesc::Tarrow { args, ret } => TypeDesc::Tarrow {
            args: {
                let args: crate::types::type_expr::TypeArgs = args
                    .iter()
                    .map(|(lbl, typ)| TypeArg::new(import_label(lbl, locs), remap[*typ]))
                    .collect();
                ctx.new_type_args(&args)
            },
            ret: remap[*ret],
        },
        PortableTypeDesc::Ttuple(types) => {
            TypeDesc::Ttuple(ctx.new_type_list_from_iter(types.iter().map(|&i| remap[i])))
        }
        PortableTypeDesc::Tconstr { path, args } => TypeDesc::Tconstr {
            path: *path,
            args: ctx.new_type_list_from_iter(args.iter().map(|&i| remap[i])),
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
            name: *name,
            mutability: mremap[*mutability],
            typ: remap[*typ],
            rest: remap[*rest],
        },
        PortableTypeDesc::Tnil => TypeDesc::Tnil,
        PortableTypeDesc::Tlink(i) => TypeDesc::Tlink(remap[*i]),
        PortableTypeDesc::Tsubst(i) => TypeDesc::Tsubst(remap[*i]),
        PortableTypeDesc::Tvariant(prd) => {
            let mut row = internalize_row_desc(prd, remap, ctx);
            if let Some((path, _)) = &mut row.row_name {
                *path = *path;
            }
            TypeDesc::Tvariant(ctx.new_row_desc(row))
        }
        PortableTypeDesc::Tunivar(name) => {
            TypeDesc::Tunivar(name.as_deref().map(crate::name::Name::new))
        }
        PortableTypeDesc::Tpoly { body, vars } => TypeDesc::Tpoly {
            body: remap[*body],
            vars: ctx.new_type_list_from_iter(vars.iter().map(|&i| remap[i])),
        },
        PortableTypeDesc::Tpackage { path, lids, args } => TypeDesc::Tpackage {
            path: *path,
            lids: ctx.new_package_lids(
                lids.iter()
                    .map(|lid| internalize_longident(lid, ctx))
                    .collect(),
            ),
            args: ctx.new_type_list_from_iter(args.iter().map(|&i| remap[i])),
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
            .map(|(p, args)| (*p, args.iter().map(|&i| remap[i]).collect())),
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
        SignatureItem::SigType(_, td, _) => {
            remap_type_decl_refs(std::sync::Arc::make_mut(td), remap, layout_remap)
        }
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
        ModuleType::MtySignature(sig) => {
            remap_signature_refs(crate::types::decl::signature_mut(sig), remap, layout_remap)
        }
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
mod identity_tests {
    use super::*;
    use crate::context::IdGenerator;

    /// A saved graph with its entries.
    fn save(ctx: &TypeContext, roots: &[TypeExprRef]) -> (Vec<usize>, PortableTypeGraph) {
        let mut file_names = PortableFileNames::default();
        let mut ser = TypeGraphSerializer::new(ctx, None, &mut file_names);
        let indices = roots.iter().map(|&r| ser.serialize_type(r)).collect();
        let graph = PortableTypeGraph {
            entries: std::mem::take(&mut ser.entries),
            variant_layouts: Vec::new(),
            mutabilities: Vec::new(),
        };
        (indices, graph)
    }

    /// The nodes of `graph` imported into `ctx`, as `internalize_signature`
    /// imports them.
    fn import(ctx: &TypeContext, graph: &PortableTypeGraph) -> Vec<TypeExprRef> {
        let remap: Vec<_> = graph.entries.iter().map(|_| ctx.new_var(None)).collect();
        let locs = ctx.import_decl_locs(std::iter::empty(), &|file| file);
        for (i, entry) in graph.entries.iter().enumerate() {
            let desc = internalize_desc(&entry.desc, &remap, &[], &locs, ctx);
            ctx.set_desc(remap[i], desc);
        }
        remap
    }







    #[test]
    fn location_allocations_survive_cold_warm_store_and_shared_imports() {
        use crate::types::decl_loc::LocationIdentity;
        let source = TypeContext::new(Arc::new(IdGenerator::new()));
        let mut coordinate = crate::location::Location::none();
        coordinate.loc_start.line = 3;
        coordinate.loc_end.line = 3;
        let scope = source.fresh_location_scope();
        let first = source.intern_loc_with_identity(
            coordinate,
            LocationIdentity {
                scope,
                location: 1,
                start: 10,
                end: 11,
            },
        );
        let second = source.intern_loc_with_identity(
            coordinate,
            LocationIdentity {
                scope,
                location: 2,
                start: 11,
                end: 12,
            },
        );
        let typ = source.new_var(None);
        let sig: Signature = [first, first, second]
            .into_iter()
            .map(|loc| {
                SignatureItem::SigValue(
                    crate::ident::Ident::create_persistent("value"),
                    ValueDescription {
                        val_type: typ,
                        val_kind: ValueKind::ValReg,
                        val_loc: loc,
                        val_attributes: Default::default(),
                        val_path: None,
                    },
                )
            })
            .collect::<Vec<_>>()
            .into();
        let save = |ctx: &TypeContext, sig: &Signature| {
            serialize_signature(sig, ctx, None, &mut PortableFileNames::default())
        };
        let saved = save(&source, &sig);
        assert_eq!(saved.2.len(), 1, "coordinates still intern once");
        let cold = crate::binser::Encoded::encode(&saved).decode();
        drop(source);
        let verify = |ctx: &TypeContext, sig: &Signature| {
            let handles: Vec<_> = sig
                .iter()
                .map(|item| match item {
                    SignatureItem::SigValue(_, value) => value.val_loc,
                    _ => panic!("value"),
                })
                .collect();
            assert_eq!(handles[0], handles[1]);
            assert_ne!(handles[0], handles[2]);
            assert_eq!(ctx.resolve_loc(handles[0]), ctx.resolve_loc(handles[2]));
            let a = ctx.location_identity(handles[0]).unwrap();
            let b = ctx.location_identity(handles[2]).unwrap();
            assert_eq!(a.scope, b.scope);
            assert_ne!(a.location, b.location);
            assert_eq!(a.end, b.start, "shared position survives");
            assert_ne!(a.start, b.end, "equal coordinates do not merge positions");
            a.scope
        };
        let target = TypeContext::new(Arc::new(IdGenerator::new()));
        let identity = |file| file;
        let load = |saved: &(Signature, PortableTypeGraph, DeclLocTable)| {
            let locs = target.import_portable_decl_locs(&saved.2, &identity);
            internalize_signature(&saved.0, &saved.1, &locs, &target)
        };
        let warm = load(&saved);
        let cold_loaded = load(&cold);
        let warm_scope = verify(&target, &warm);
        assert_ne!(warm_scope, scope);
        assert_ne!(warm_scope, verify(&target, &cold_loaded));
        let worker_a = TypeContext::new(Arc::new(IdGenerator::new()));
        let worker_b = TypeContext::new(Arc::new(IdGenerator::new()));
        let store_load = |ctx: &TypeContext| {
            let locs = ctx
                .thread_store()
                .import_portable_decl_locs(&saved.2, &identity);
            internalize_signature_into_store(&saved.0, &saved.1, &locs, ctx.thread_store())
        };
        let a = store_load(&worker_a);
        let b = store_load(&worker_b);
        assert_ne!(verify(&worker_a, &a), verify(&worker_b, &b));
        let a = load(&save(&worker_a, &a));
        let b = load(&save(&worker_b, &b));
        assert_ne!(verify(&target, &a), verify(&target, &b));

        let intern = |name: &str| {
            target
                .thread_store()
                .shared_pool()
                .intern_longident_name(name)
        };
        let files = FileRemap::new(&[], &intern);
        let shared = internalize_signature_into_shared(
            &saved.0,
            &saved.1,
            &saved.2,
            &files,
            target.thread_store().shared_pool(),
        )
        .unwrap();
        let shared_scope = verify(&target, &shared);
        assert_ne!(shared_scope, warm_scope);
        let roundtrip = load(&save(&target, &shared));
        assert_ne!(verify(&target, &roundtrip), shared_scope);

        let digest = |value: &(Signature, PortableTypeGraph, DeclLocTable)| {
            let mut hash = std::collections::hash_map::DefaultHasher::new();
            crate::cmi::digest_ser::Canonical::new(&mut hash).hash(value);
            std::hash::Hasher::finish(&hash)
        };
        let mut without = saved.clone();
        without.2 = DeclLocTable::default();
        assert_eq!(digest(&saved), digest(&without));
        assert_eq!(std::mem::size_of::<DeclLoc>(), 8);
        assert_eq!(std::mem::size_of::<crate::ident::Ident>(), 16);
        assert_eq!(std::mem::size_of::<Path>(), 8);
        assert_eq!(std::mem::size_of::<TypeDesc>(), 24);
        assert_eq!(std::mem::size_of::<crate::types::TypeExpr>(), 40);
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
            origin: Default::default(),
        };
        let labels = [
            ArgLabel::Nolabel,
            ArgLabel::labelled("λ", ctx.intern_loc(loc)),
            ArgLabel::optional("opt", ctx.intern_loc(loc)),
        ];
        let arrow = ctx.new_type(TypeDesc::Tarrow {
            args: ctx.new_type_args(&[
                TypeArg::unlabeled(shared),
                TypeArg::new(labels[1].clone(), shared),
                TypeArg::new(labels[2].clone(), distinct),
            ]),
            ret: shared,
        });
        let mut file_names = PortableFileNames::default();
        let mut ser = TypeGraphSerializer::new(&ctx, None, &mut file_names);
        let index = ser.serialize_type(arrow);
        let PortableTypeDesc::Tarrow { args, ret } = &ser.entries[index].desc else {
            panic!("not arrow")
        };
        assert_eq!(args.len(), 3);
        assert_eq!(args[0].1, *ret);
        assert_eq!(args[1].1, *ret);
        assert_ne!(args[2].1, *ret);
        // Both labels share one portable entry.
        assert_eq!(ser.locations.len(), 1);
        let entries = std::mem::take(&mut ser.entries);
        let locations = std::mem::take(&mut ser.locations);
        drop(ser);
        // Import into another compilation: the producer's table is gone.
        drop(ctx);
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let same = |file| file;
        let locs = ctx.import_decl_locs(locations.locations().iter().copied(), &same);
        let remap: Vec<_> = entries.iter().map(|_| ctx.new_var(None)).collect();
        let restored = internalize_desc(
            &entries[index].desc,
            &remap,
            &[],
            &locs,
            &ctx,
        );
        let TypeDesc::Tarrow { args, ret } = restored else {
            panic!("not arrow")
        };
        let args = ctx.type_args(args).to_vec();
        assert_eq!(args[0].typ, ret);
        assert_eq!(args[1].typ, ret);
        assert_ne!(args[2].typ, ret);
        assert!(args[0].label().is_nolabel());
        for (arg, expected) in args.iter().zip(&labels).skip(1) {
            assert!(
                arg.label()
                    .same_label(crate::types::type_expr::TypeArgLabel::new(expected))
            );
            assert_eq!(ctx.resolve_loc(arg.label().loc()), loc);
        }
    }
}
