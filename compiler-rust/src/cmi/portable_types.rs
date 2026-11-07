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
    /// The physical sharing of the interface OCaml would save for these
    /// types. Cold, and outside every interface digest.
    pub identities: PortableIdentities,
}

/// The physical sharing of a saved interface's types, for
/// `Includemod.is_big` (includemod_error_size.rs) only.
///
/// OCaml saves `Subst.signature` with `for_saving` (subst.ml:132-232) and
/// the importer unmarshals it, so the importer's blocks are shared exactly as
/// the saved copy shares them, and none is one of its own: a `Pident` path,
/// its `Ident.t`, an arrow's `lbl` and a variable's descriptor are those of
/// the source graph (kept by `type_path`, `copy_type_desc` and `norm`); a
/// `Pdot` is rebuilt for each copied node; every `Tvar None` is the one
/// static `tvar_none`. Each kind of block is numbered within the unit.
#[derive(Clone, Debug, Default, serde::Serialize, serde::Deserialize)]
pub struct PortableIdentities {
    /// For each entry: the path block of a `Tconstr`, the descriptor block of
    /// a `Tvar` or `Tunivar`, else [`PortableIdentities::NONE`].
    blocks: Vec<u32>,
    /// The `Ident.t` blocks of the paths of `Tconstr`, `Tpackage` and row
    /// name entries, in entry order and, within a path, prefix first.
    path_idents: Vec<u32>,
    /// Declaration and module-path identifiers in signature traversal order.
    signature_idents: Vec<u32>,
    /// Name-string allocation class, indexed by identifier block number.
    ident_names: Vec<u32>,
    /// Path allocations in postorder, graph paths then signature paths.
    paths: Vec<PortablePathAllocation>,
    /// The `lbl` blocks of labelled arrow arguments, in entry order.
    labels: Vec<u32>,
}

/// `Subst` rebuilds dotted/application blocks, but retains Pident prefixes
/// and suffix strings (compiler/ml/subst.ml:69-100). Unknown evidence stays
/// unknown; interned text is never an allocation key.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
struct PortablePathAllocation {
    block: u32,
    name: u32,
}

impl PortableIdentities {
    const NONE: u32 = u32::MAX;
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
        PortablePersStruct {
            ps_name,
            ps_filename,
            ps_deprecated,
            ps_crcs,
            shareable: graph_is_shareable(&sig.type_graph),
            sig: crate::binser::Encoded::encode(&sig),
            raw: raw.as_ref().map(crate::binser::Encoded::encode),
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
    // File-name indices used by the signatures' locations: only those names
    // need to travel with them (`remap_signature_file_names`).
    let mut file_names = crate::fast_hash::AHashSet::new();
    let (sig, type_graph, locations) =
        serialize_signature(ps.ps_sig.as_ref(), ctx, arena, &mut file_names);
    let raw = ctx
        .find_raw_module_sig(&ps.ps_name)
        .map(|raw_sig| serialize_signature(&raw_sig, ctx, arena, &mut file_names));
    let fingerprint = compute_type_graph_fingerprint(&HashGraph::of(&type_graph), &sig);
    PortablePersStruct::new(
        ps.ps_name.clone(),
        ps.ps_filename.clone(),
        ps.ps_deprecated.clone(),
        ps.ps_crcs.clone(),
        PortableSignature {
            ps_sig: sig,
            cmi_longident_names: ctx.snapshot_cmi_longident_names(file_names),
            type_graph,
            locations,
        },
        raw.map(
            |(raw_ps_sig, raw_type_graph, raw_locations)| PortableRawSignature {
                raw_ps_sig,
                raw_type_graph,
                raw_locations,
            },
        ),
        fingerprint,
    )
}

/// Visit declaration identifiers and path identifiers outside the type graph.
// Keep the saving traversal read-only: observing identities must not clone
// shared prefix allocations or change declaration sharing.
fn visit_signature_identifiers(sig: &[SignatureItem], f: &mut dyn FnMut(&crate::ident::Ident)) {
    fn path(p: &Path, f: &mut dyn FnMut(&crate::ident::Ident)) {
        match p {
            Path::Pident(id) => f(id),
            Path::Pdot(prefix, ..) => path(prefix, f),
            Path::Papply(functor, argument) => {
                path(functor, f);
                path(argument, f);
            }
        }
    }
    fn opt_path(p: &Option<Path>, f: &mut dyn FnMut(&crate::ident::Ident)) {
        if let Some(p) = p {
            path(p, f);
        }
    }
    fn labels<'a>(
        lds: impl IntoIterator<Item = &'a LabelDeclaration>,
        f: &mut dyn FnMut(&crate::ident::Ident),
    ) {
        for ld in lds {
            f(&ld.ld_id);
        }
    }
    fn args(args: &ConstructorArguments, f: &mut dyn FnMut(&crate::ident::Ident)) {
        if let ConstructorArguments::CstrRecord(lds) = args {
            labels(lds.iter(), f);
        }
    }
    fn module_type(mty: &ModuleType, f: &mut dyn FnMut(&crate::ident::Ident)) {
        match mty {
            ModuleType::MtyIdent(_) | ModuleType::MtyAlias(..) => {
                path(mty.ident_or_alias_path().unwrap(), f)
            }
            ModuleType::MtySignature(sig) => {
                visit_signature_identifiers(sig, f);
            }
            ModuleType::MtyFunctor {
                param,
                param_type,
                result,
            } => {
                f(param);
                if let Some(param_type) = param_type {
                    module_type(param_type, f);
                }
                module_type(result, f);
            }
        }
    }
    for item in sig {
        match item {
            SignatureItem::SigValue(i, vd) => {
                f(i);
                opt_path(&vd.val_path, f);
            }
            SignatureItem::SigType(i, td, _) => {
                f(i);
                let td = td.as_ref();
                opt_path(&td.type_path, f);
                match &td.type_kind {
                    TypeKind::TypeRecord(lds, _) => labels(lds.iter(), f),
                    TypeKind::TypeVariant(cds, _) => {
                        for cd in cds.iter() {
                            f(&cd.cd_id);
                            args(&cd.cd_args, f);
                        }
                    }
                    TypeKind::TypeAbstract | TypeKind::TypeOpen => {}
                }
                for inlined in &td.type_inlined_types {
                    let crate::types::decl::TypeInlinedType::Record { labels: lds, .. } = inlined;
                    labels(lds.iter(), f);
                }
            }
            SignatureItem::SigTypext(i, ext, _) => {
                f(i);
                path(&ext.ext_type_path, f);
                args(&ext.ext_args, f);
            }
            SignatureItem::SigModule(i, md, _) => {
                f(i);
                opt_path(&md.md_path, f);
                module_type(&md.md_type, f);
            }
            SignatureItem::SigModtype(i, mtd) => {
                f(i);
                if let Some(mty) = &mtd.mtd_type {
                    module_type(mty, f);
                }
            }
            SignatureItem::SigClass | SignatureItem::SigClassType => {}
        }
    }
}

fn map_signature_identifiers(
    sig: &mut [SignatureItem],
    f: &mut dyn FnMut(&mut crate::ident::Ident),
) {
    type Prefixes = AHashMap<usize, (Arc<Path>, Arc<Path>)>;
    fn prefix(
        p: &mut Arc<Path>,
        f: &mut dyn FnMut(&mut crate::ident::Ident),
        prefixes: &mut Prefixes,
    ) {
        let key = Arc::as_ptr(p) as usize;
        let source = p.clone();
        let mut mapped = (**p).clone();
        path(&mut mapped, f, prefixes);
        let (_, target) = prefixes
            .entry(key)
            .or_insert_with(|| (source, Arc::new(mapped)));
        *p = target.clone();
    }
    fn path(p: &mut Path, f: &mut dyn FnMut(&mut crate::ident::Ident), prefixes: &mut Prefixes) {
        match p {
            Path::Pident(id) => f(id),
            Path::Pdot(p, ..) => prefix(p, f, prefixes),
            Path::Papply(functor, argument) => {
                prefix(functor, f, prefixes);
                prefix(argument, f, prefixes);
            }
        }
    }
    fn opt_path(
        p: &mut Option<Path>,
        f: &mut dyn FnMut(&mut crate::ident::Ident),
        prefixes: &mut Prefixes,
    ) {
        if let Some(p) = p {
            path(p, f, prefixes);
        }
    }
    fn labels<'a>(
        lds: impl IntoIterator<Item = &'a mut LabelDeclaration>,
        f: &mut dyn FnMut(&mut crate::ident::Ident),
    ) {
        for ld in lds {
            f(&mut ld.ld_id);
        }
    }
    fn args(args: &mut ConstructorArguments, f: &mut dyn FnMut(&mut crate::ident::Ident)) {
        if let ConstructorArguments::CstrRecord(lds) = args {
            labels(lds.iter_mut(), f);
        }
    }
    fn module_type(
        mty: &mut ModuleType,
        f: &mut dyn FnMut(&mut crate::ident::Ident),
        prefixes: &mut Prefixes,
    ) {
        match mty {
            ModuleType::MtyIdent(p) => path(p, f, prefixes),
            // The target is a shared block, remapped once per source block.
            ModuleType::MtyAlias(_, p) => prefix(p, f, prefixes),
            ModuleType::MtySignature(sig) => {
                walk(&mut Arc::make_mut(sig)[..], f, prefixes);
            }
            ModuleType::MtyFunctor {
                param,
                param_type,
                result,
            } => {
                f(param);
                if let Some(param_type) = param_type {
                    module_type(param_type, f, prefixes);
                }
                module_type(result, f, prefixes);
            }
        }
    }
    fn walk(
        sig: &mut [SignatureItem],
        f: &mut dyn FnMut(&mut crate::ident::Ident),
        prefixes: &mut Prefixes,
    ) {
        for item in sig {
            match item {
                SignatureItem::SigValue(i, vd) => {
                    f(i);
                    opt_path(&mut vd.val_path, f, prefixes);
                }
                SignatureItem::SigType(i, td, _) => {
                    f(i);
                    let td = Arc::make_mut(td);
                    opt_path(&mut td.type_path, f, prefixes);
                    match &mut td.type_kind {
                        TypeKind::TypeRecord(lds, _) => labels(lds.iter_mut(), f),
                        TypeKind::TypeVariant(cds, _) => {
                            for cd in cds.iter_mut() {
                                f(&mut cd.cd_id);
                                args(&mut cd.cd_args, f);
                            }
                        }
                        TypeKind::TypeAbstract | TypeKind::TypeOpen => {}
                    }
                    for inlined in &mut td.type_inlined_types {
                        let crate::types::decl::TypeInlinedType::Record { labels: lds, .. } =
                            inlined;
                        labels(lds.iter_mut(), f);
                    }
                }
                SignatureItem::SigTypext(i, ext, _) => {
                    f(i);
                    path(&mut ext.ext_type_path, f, prefixes);
                    args(&mut ext.ext_args, f);
                }
                SignatureItem::SigModule(i, md, _) => {
                    f(i);
                    opt_path(&mut md.md_path, f, prefixes);
                    module_type(&mut md.md_type, f, prefixes);
                }
                SignatureItem::SigModtype(i, mtd) => {
                    f(i);
                    if let Some(mty) = &mut mtd.mtd_type {
                        module_type(mty, f, prefixes);
                    }
                }
                SignatureItem::SigClass | SignatureItem::SigClassType => {}
            }
        }
    }
    walk(sig, f, &mut Prefixes::new());
}
/// Visit only path roots outside the type graph. The callback owns recursive
/// path traversal; declaration identifiers are handled by the identifier pass.
fn map_signature_paths(sig: &mut [SignatureItem], f: &mut dyn FnMut(&Path) -> Path) {
    fn optional(path: &mut Option<Path>, f: &mut dyn FnMut(&Path) -> Path) {
        if let Some(p) = path {
            *p = f(p);
        }
    }
    fn module_type(mty: &mut ModuleType, f: &mut dyn FnMut(&Path) -> Path) {
        match mty {
            ModuleType::MtyIdent(p) => *p = f(p),
            ModuleType::MtyAlias(_, p) => {
                let mapped = f(p);
                // Saving keeps an unreplaced `Pident` target block and
                // rebuilds a dotted one (subst.ml:69-75); the identifier pass
                // already remapped the `Pident` block per source block.
                if !matches!(p.as_ref(), Path::Pident(_)) {
                    *p = Arc::new(mapped);
                }
            }
            ModuleType::MtySignature(sig) => map_signature_paths(&mut Arc::make_mut(sig)[..], f),
            ModuleType::MtyFunctor {
                param_type, result, ..
            } => {
                if let Some(param_type) = param_type {
                    module_type(param_type, f);
                }
                module_type(result, f);
            }
        }
    }
    for item in sig {
        match item {
            SignatureItem::SigValue(_, vd) => optional(&mut vd.val_path, f),
            SignatureItem::SigType(_, td, _) => optional(&mut Arc::make_mut(td).type_path, f),
            SignatureItem::SigTypext(_, ext, _) => ext.ext_type_path = f(&ext.ext_type_path),
            SignatureItem::SigModule(_, md, _) => {
                optional(&mut md.md_path, f);
                module_type(&mut md.md_type, f);
            }
            SignatureItem::SigModtype(_, mtd) => {
                if let Some(mty) = &mut mtd.mtd_type {
                    module_type(mty, f);
                }
            }
            SignatureItem::SigClass | SignatureItem::SigClassType => {}
        }
    }
}

/// The blocks of the saved copy of `nodes` (see [`PortableIdentities`]),
/// numbered in entry order from the identities of the source graph.
#[cfg(test)]
fn saved_identities(ctx: &TypeContext, nodes: &[TypeExprRef]) -> PortableIdentities {
    saved_signature_identities(ctx, nodes, &mut Signature::default())
}

fn saved_signature_identities(
    ctx: &TypeContext,
    nodes: &[TypeExprRef],
    sig: &Signature,
) -> PortableIdentities {
    use crate::types::type_expr::{PathBlockOwner, VarDescBlock};

    #[derive(Clone, Copy, PartialEq, Eq, Hash)]
    enum Block {
        Node(TypeExprRef),
        Predef(i32),
        Token(u32),
        TvarNone,
        TunivarNone,
    }

    struct Numbering<K> {
        numbers: AHashMap<K, u32>,
    }

    impl<K> Default for Numbering<K> {
        fn default() -> Self {
            Numbering {
                numbers: AHashMap::new(),
            }
        }
    }

    impl<K: std::hash::Hash + Eq> Numbering<K> {
        fn number(&mut self, key: K) -> u32 {
            let next = self.numbers.len() as u32;
            *self.numbers.entry(key).or_insert(next)
        }

        fn fresh(&mut self, key: K) -> u32 {
            let next = self.numbers.len() as u32;
            self.numbers.insert(key, next);
            next
        }
    }

    fn number_ident(
        id: &crate::ident::Ident,
        ctx: &TypeContext,
        idents: &mut Numbering<(i32, usize, u32)>,
        names: &mut Numbering<crate::types::path_provenance::NameAllocation>,
        out: &mut Vec<u32>,
    ) -> u32 {
        let number = idents.number((id.stamp(), id.name().as_ptr() as usize, id.origin().get()));
        if number as usize == out.len() {
            out.push(names.number(ctx.ident_name_allocation(id)));
        }
        number
    }

    fn push_idents(
        path: &Path,
        ctx: &TypeContext,
        idents: &mut Numbering<(i32, usize, u32)>,
        names: &mut Numbering<crate::types::path_provenance::NameAllocation>,
        ids: &mut PortableIdentities,
    ) {
        match path {
            Path::Pident(id) => {
                let number = number_ident(id, ctx, idents, names, &mut ids.ident_names);
                ids.path_idents.push(number);
            }
            Path::Pdot(prefix, _, _) => push_idents(prefix, ctx, idents, names, ids),
            Path::Papply(functor, argument) => {
                push_idents(functor, ctx, idents, names, ids);
                push_idents(argument, ctx, idents, names, ids);
            }
        }
    }

    fn save_path(
        path: &Path,
        owner: Option<usize>,
        ctx: &TypeContext,
        prefixes: &mut Numbering<usize>,
        names: &mut Numbering<crate::types::path_provenance::NameAllocation>,
        out: &mut Vec<PortablePathAllocation>,
    ) {
        let mut evidence = PortablePathAllocation {
            block: PortableIdentities::NONE,
            name: PortableIdentities::NONE,
        };
        match path {
            Path::Pident(_) => {
                if let Some(owner) = owner {
                    evidence.block = prefixes.number(owner);
                }
            }
            Path::Pdot(prefix, _, _) => {
                let allocation = ctx.dotted_allocation(path);
                let prefix = allocation.as_ref().map_or(prefix, |a| &a.prefix);
                save_path(
                    prefix,
                    Some(Arc::as_ptr(prefix) as usize),
                    ctx,
                    prefixes,
                    names,
                    out,
                );
                if let Some(allocation) = allocation {
                    evidence.name = names.number(allocation.name);
                }
            }
            Path::Papply(functor, argument) => {
                for prefix in [functor, argument] {
                    save_path(
                        prefix,
                        Some(Arc::as_ptr(prefix) as usize),
                        ctx,
                        prefixes,
                        names,
                        out,
                    );
                }
            }
        }
        out.push(evidence);
    }

    let mut ids = PortableIdentities::default();
    let mut paths = Numbering::<Block>::default();
    let mut vars = Numbering::<Block>::default();
    let mut idents = Numbering::default();
    let mut names = Numbering::default();
    let mut prefixes = Numbering::default();
    let mut labels = Numbering::<usize>::default();
    for &node in nodes {
        let desc = ctx.get_desc(node);
        let block = match &*desc {
            TypeDesc::Tconstr {
                path, path_block, ..
            } => {
                push_idents(path, ctx, &mut idents, &mut names, &mut ids);
                save_path(path, None, ctx, &mut prefixes, &mut names, &mut ids.paths);
                // `type_path` keeps a `Pident` (subst.ml:87-94).
                match (path, path_block.owner()) {
                    (Path::Pident(_), PathBlockOwner::Own) => paths.number(Block::Node(node)),
                    (Path::Pident(_), PathBlockOwner::Of(owner)) => {
                        paths.number(Block::Node(owner))
                    }
                    (Path::Pident(id), PathBlockOwner::Predef) => {
                        paths.number(Block::Predef(id.stamp()))
                    }
                    (Path::Pident(_), PathBlockOwner::Token(token)) => {
                        paths.number(Block::Token(token))
                    }
                    _ => paths.fresh(Block::Node(node)),
                }
            }
            // `norm` (subst.ml:121-126) shares every `Tvar None`; another
            // descriptor is the source's.
            TypeDesc::Tvar(None, _) => vars.number(Block::TvarNone),
            TypeDesc::Tunivar(None, _) => vars.number(Block::TunivarNone),
            TypeDesc::Tvar(_, block) | TypeDesc::Tunivar(_, block) => match block {
                VarDescBlock::Of(owner) => vars.number(Block::Node(*owner)),
                VarDescBlock::Own | VarDescBlock::Static => vars.number(Block::Node(node)),
            },
            TypeDesc::Tarrow { args, .. } => {
                for arg in args.iter() {
                    if let Some(label) = arg.label_block() {
                        ids.labels.push(labels.number(label));
                    }
                }
                PortableIdentities::NONE
            }
            TypeDesc::Tpackage { path, .. } => {
                push_idents(path, ctx, &mut idents, &mut names, &mut ids);
                save_path(path, None, ctx, &mut prefixes, &mut names, &mut ids.paths);
                PortableIdentities::NONE
            }
            TypeDesc::Tvariant(row) => {
                if let Some((path, _)) = &row.row_name {
                    push_idents(path, ctx, &mut idents, &mut names, &mut ids);
                    save_path(path, None, ctx, &mut prefixes, &mut names, &mut ids.paths);
                }
                PortableIdentities::NONE
            }
            _ => PortableIdentities::NONE,
        };
        ids.blocks.push(block);
    }
    visit_signature_identifiers(sig, &mut |id| {
        let number = number_ident(id, ctx, &mut idents, &mut names, &mut ids.ident_names);
        ids.signature_idents.push(number);
    });
    // Cloning the signature leaves all source path carriers retained. The
    // callback observes them without rebuilding any prefix allocations.
    map_signature_paths(&mut sig.clone(), &mut |path| {
        save_path(path, None, ctx, &mut prefixes, &mut names, &mut ids.paths);
        path.clone()
    });
    ids
}

/// The importer's side of [`PortableIdentities`]: each saved block becomes
/// the block of the first node imported with it, each saved identifier a
/// fresh origin, each saved label one allocation.
struct ImportedIdentities<'g> {
    ids: &'g PortableIdentities,
    name_scope: u64,
    idents: usize,
    paths: usize,
    prefixes: AHashMap<u32, Arc<Path>>,
    labels: usize,
    path_blocks: AHashMap<u32, TypeExprRef>,
    var_descs: AHashMap<u32, TypeExprRef>,
    origins: AHashMap<u32, crate::ident::IdentOrigin>,
    label_args: AHashMap<u32, TypeArg>,
}

impl<'g> ImportedIdentities<'g> {
    fn new(ids: &'g PortableIdentities) -> Self {
        ImportedIdentities {
            ids,
            name_scope: if ids.ident_names.is_empty() {
                0
            } else {
                (crate::types::decl_loc::next_table_owner() as u64) << 32
            },
            idents: 0,
            paths: 0,
            prefixes: AHashMap::new(),
            labels: 0,
            path_blocks: AHashMap::new(),
            var_descs: AHashMap::new(),
            origins: AHashMap::new(),
            label_args: AHashMap::new(),
        }
    }

    /// Whether the graph was saved with its identities (a graph built
    /// directly, not by `serialize_signature`, has none, and then every
    /// block is the node's own).
    fn present(&self) -> bool {
        !self.ids.blocks.is_empty()
    }

    fn block_of(
        numbers: &mut AHashMap<u32, TypeExprRef>,
        number: u32,
        node: TypeExprRef,
    ) -> Option<TypeExprRef> {
        match numbers.get(&number) {
            Some(&owner) => Some(owner),
            None => {
                numbers.insert(number, node);
                None
            }
        }
    }

    fn path_block(
        &mut self,
        entry: usize,
        node: TypeExprRef,
    ) -> crate::types::type_expr::PathBlock {
        use crate::types::type_expr::PathBlock;
        if !self.present() {
            return PathBlock::OWN;
        }
        match Self::block_of(&mut self.path_blocks, self.ids.blocks[entry], node) {
            Some(owner) => PathBlock::OWN.copied_from(owner),
            None => PathBlock::OWN,
        }
    }

    fn var_desc(
        &mut self,
        entry: usize,
        node: TypeExprRef,
    ) -> crate::types::type_expr::VarDescBlock {
        use crate::types::type_expr::VarDescBlock;
        if !self.present() {
            return VarDescBlock::OWN;
        }
        match Self::block_of(&mut self.var_descs, self.ids.blocks[entry], node) {
            Some(owner) => VarDescBlock::OWN.copied_from(owner),
            None => VarDescBlock::OWN,
        }
    }

    fn ident<S: TypeNodeSink>(
        &mut self,
        number: u32,
        id: &crate::ident::Ident,
        sink: &S,
    ) -> crate::ident::Ident {
        if let Some(origin) = self.origins.get(&number) {
            return id.with_origin(*origin);
        }
        let origin = sink.fresh_ident_origin();
        self.origins.insert(number, origin);
        let id = id.with_origin(origin);
        if self.name_scope != 0 {
            sink.record_ident_name(
                &id,
                crate::types::path_provenance::NameAllocation::Source {
                    scope: self.name_scope,
                    string: self.ids.ident_names[number as usize],
                },
            );
        }
        id
    }

    /// Remap names and retained Pident prefixes. Every dotted/application
    /// occurrence is fresh, as in the saved Subst copy, not source deduplication.
    fn shared_path<S: TypeNodeSink>(&mut self, path: &Path, sink: &S, graph: bool) -> Arc<Path> {
        let mapped = self.mapped_path(path, sink, graph);
        let evidence = &self.ids.paths[self.paths - 1];
        if evidence.block != PortableIdentities::NONE {
            self.prefixes
                .entry(evidence.block)
                .or_insert_with(|| Arc::new(mapped))
                .clone()
        } else {
            Arc::new(mapped)
        }
    }

    fn mapped_path<S: TypeNodeSink>(&mut self, path: &Path, sink: &S, graph: bool) -> Path {
        let mapped = match path {
            Path::Pident(id) if graph => {
                let number = self.ids.path_idents[self.idents];
                self.idents += 1;
                Path::Pident(self.ident(number, id, sink))
            }
            Path::Pident(_) => path.clone(),
            Path::Pdot(prefix, name, pos) => {
                let prefix = self.shared_path(prefix, sink, graph);
                let evidence = &self.ids.paths[self.paths];
                if evidence.name != PortableIdentities::NONE {
                    sink.dotted_with_name(
                        prefix,
                        *name,
                        crate::types::path_provenance::NameAllocation::Source {
                            scope: self.name_scope,
                            string: evidence.name,
                        },
                        *pos,
                    )
                } else {
                    Path::Pdot(prefix, *name, *pos)
                }
            }
            Path::Papply(functor, argument) => {
                let functor = self.shared_path(functor, sink, graph);
                Path::Papply(functor, self.shared_path(argument, sink, graph))
            }
        };
        self.paths += 1;
        mapped
    }

    fn path<S: TypeNodeSink>(&mut self, path: &Path, sink: &S) -> Path {
        if !self.present() {
            return path.clone();
        }
        self.mapped_path(path, sink, true)
    }

    fn signature<S: TypeNodeSink>(&mut self, sig: &mut Signature, sink: &S) {
        // Directly constructed graphs do not carry a signature identity table.
        if self.ids.signature_idents.is_empty() {
            return;
        }
        let mut numbers = self.ids.signature_idents.iter();
        map_signature_identifiers(sig, &mut |id| {
            let number = *numbers
                .next()
                .expect("missing signature identifier identity");
            *id = self.ident(number, id, sink);
        });
        assert!(
            numbers.next().is_none(),
            "unused signature identifier identities"
        );
        map_signature_paths(sig, &mut |path| self.mapped_path(path, sink, false));
        assert_eq!(
            self.paths,
            self.ids.paths.len(),
            "unused saved path evidence"
        );
    }

    fn arg(&mut self, label: &ArgLabel, typ: TypeExprRef, locs: &DeclLocImport<'_>) -> TypeArg {
        if !self.present() || matches!(label, ArgLabel::Nolabel) {
            return TypeArg::new(import_label(label, locs), typ);
        }
        let number = self.ids.labels[self.labels];
        self.labels += 1;
        if let Some(arg) = self.label_args.get(&number) {
            return arg.with_type(typ);
        }
        let arg = TypeArg::new(import_label(label, locs), typ);
        self.label_args.insert(number, arg.clone());
        arg
    }
}

/// Serialize `sig` with its location table, adding the raw file-name indices
/// of its locations to `file_names`.
fn serialize_signature(
    sig: &Signature,
    ctx: &TypeContext,
    arena: Option<&ParseArena>,
    file_names: &mut crate::fast_hash::AHashSet<u32>,
) -> (Signature, PortableTypeGraph, DeclLocTable) {
    let mut ser = TypeGraphSerializer::new(ctx, arena, file_names);
    let mut sig = sig.clone();
    ser.remap_signature(&mut sig);
    ser.remap_signature_locations(&mut sig);
    let identities = saved_signature_identities(ctx, &ser.nodes, &sig);
    let type_graph = PortableTypeGraph {
        entries: ser.entries,
        variant_layouts: ser.variant_layouts,
        mutabilities: ser.mutabilities,
        identities,
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
    /// Source-arena file names re-interned as synthetic CMI names.
    file_name_cache: AHashMap<crate::intern::StrIdx, crate::intern::StrIdx>,
    mutabilities: Vec<crate::types::asttypes::MutableFlag>,
    mutability_cache: AHashMap<MutabilityRef, usize>,
    /// Locations of the serialized declarations and labels.
    locations: DeclLocTable,
    /// Raw file-name indices the locations use.
    file_names: &'f mut crate::fast_hash::AHashSet<u32>,
}

impl<'a, 'f> TypeGraphSerializer<'a, 'f> {
    fn new(
        ctx: &'a TypeContext,
        arena: Option<&'a ParseArena>,
        file_names: &'f mut crate::fast_hash::AHashSet<u32>,
    ) -> Self {
        TypeGraphSerializer {
            ctx,
            arena,
            entries: Vec::new(),
            nodes: Vec::new(),
            cache: AHashMap::new(),
            variant_layouts: Vec::new(),
            variant_layout_cache: AHashMap::new(),
            file_name_cache: AHashMap::new(),
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

    /// The portable handle of a location of the serialized context.
    fn portable_loc(&mut self, loc: DeclLoc) -> DeclLoc {
        let identity = self.ctx.location_identity(loc);
        let mut loc = self.ctx.resolve_loc(loc);
        self.remap_loc(&mut loc);
        self.file_names.insert(loc.loc_start.file_name.raw());
        self.file_names.insert(loc.loc_end.file_name.raw());
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
            TypeDesc::Tvar(name, ..) => PortableTypeDesc::Tvar(name.clone()),
            TypeDesc::Tarrow { args, ret } => PortableTypeDesc::Tarrow {
                args: args
                    .iter()
                    .map(|arg| {
                        (
                            self.portable_label(arg.label()),
                            self.serialize_type(arg.typ),
                        )
                    })
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
            TypeDesc::Tunivar(name, ..) => PortableTypeDesc::Tunivar(name.clone()),
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
    /// The origin of an identifier block of an imported graph.
    fn fresh_ident_origin(&self) -> crate::ident::IdentOrigin;
    fn dotted_with_name(
        &self,
        prefix: Arc<Path>,
        text: crate::name::Name,
        name: crate::types::path_provenance::NameAllocation,
        pos: i32,
    ) -> Path;
    fn record_ident_name(
        &self,
        id: &crate::ident::Ident,
        allocation: crate::types::path_provenance::NameAllocation,
    );
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
    fn dotted_with_name(
        &self,
        prefix: Arc<Path>,
        text: crate::name::Name,
        name: crate::types::path_provenance::NameAllocation,
        pos: i32,
    ) -> Path {
        TypeContext::dotted_with_name(self, prefix, text, name, pos)
    }

    fn record_ident_name(
        &self,
        id: &crate::ident::Ident,
        allocation: crate::types::path_provenance::NameAllocation,
    ) {
        TypeContext::record_ident_name(self, id, allocation);
    }

    fn abbrev_nil(&self) -> AbbrevMemoRef {
        self.alloc_abbrev_nil()
    }

    fn fresh_ident_origin(&self) -> crate::ident::IdentOrigin {
        TypeContext::fresh_ident_origin(self)
    }

    fn new_mutability(&self, flag: crate::types::asttypes::MutableFlag) -> MutabilityRef {
        self.alloc_mutability(crate::types::type_expr::FieldMutability::Value(flag))
    }

    fn longident_name(&self, name: &str) -> crate::intern::StrIdx {
        self.intern_cmi_longident_name(name)
    }
}

impl TypeNodeSink for ThreadTypeStore {
    fn dotted_with_name(
        &self,
        prefix: Arc<Path>,
        text: crate::name::Name,
        name: crate::types::path_provenance::NameAllocation,
        pos: i32,
    ) -> Path {
        ThreadTypeStore::dotted_with_name(self, prefix, text, name, pos)
    }

    fn record_ident_name(
        &self,
        id: &crate::ident::Ident,
        allocation: crate::types::path_provenance::NameAllocation,
    ) {
        ThreadTypeStore::record_ident_name(self, id, allocation);
    }

    fn abbrev_nil(&self) -> AbbrevMemoRef {
        self.alloc_abbrev(AbbrevMemo::Mnil)
    }

    fn longident_name(&self, name: &str) -> crate::intern::StrIdx {
        self.intern_longident_name(name)
    }

    fn fresh_ident_origin(&self) -> crate::ident::IdentOrigin {
        ThreadTypeStore::fresh_ident_origin(self)
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
    let mut ids = ImportedIdentities::new(&graph.identities);
    for (i, entry) in graph.entries.iter().enumerate() {
        let desc = internalize_desc(&entry.desc, i, &remap, &mremap, locs, &mut ids, store);
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
    ids.signature(&mut sig, store);
    remap_signature_refs(&mut sig, &remap, &layout_remap);
    import_signature_locations(&mut sig, locs);
    sig
}

/// Allocation sink for a graph being published to the shared pool: each
/// `Tconstr` gets the memo cell keyed by its own node index.
struct SharedSink<'a> {
    pool: &'a crate::types::shared_store::SharedTypePool,
    current: std::cell::Cell<u32>,
}

impl TypeNodeSink for SharedSink<'_> {
    fn dotted_with_name(
        &self,
        prefix: Arc<Path>,
        text: crate::name::Name,
        name: crate::types::path_provenance::NameAllocation,
        pos: i32,
    ) -> Path {
        self.pool.dotted_with_name(prefix, text, name, pos)
    }

    fn record_ident_name(
        &self,
        id: &crate::ident::Ident,
        allocation: crate::types::path_provenance::NameAllocation,
    ) {
        self.pool.record_ident_name(id, allocation);
    }

    fn abbrev_nil(&self) -> AbbrevMemoRef {
        AbbrevMemoRef::from_shared_index(self.current.get())
    }

    fn longident_name(&self, name: &str) -> crate::intern::StrIdx {
        self.pool.intern_longident_name(name)
    }

    fn fresh_ident_origin(&self) -> crate::ident::IdentOrigin {
        self.pool.fresh_ident_origin()
    }
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
    let map = |file| files.map(file);
    let base = pool.publish(graph.entries.len(), graph.variant_layouts.len(), |base| {
        remap = (0..graph.entries.len())
            .map(|i| crate::types::shared_store::shared_ref(base, i))
            .collect();
        let sink = SharedSink {
            pool,
            current: std::cell::Cell::new(base),
        };
        let locs = shared_decl_locs(base, &map);
        let mremap = internalize_mutabilities(graph, &sink);
        let mut ids = ImportedIdentities::new(&graph.identities);
        let nodes = graph
            .entries
            .iter()
            .enumerate()
            .map(|(i, entry)| {
                sink.current.set(base + i as u32);
                let desc =
                    internalize_desc(&entry.desc, i, &remap, &mremap, &locs, &mut ids, &sink);
                let level = match entry.desc {
                    PortableTypeDesc::Tlink(_) => GENERIC_LEVEL,
                    _ => entry.level,
                };
                (desc, level)
            })
            .collect();
        ids.signature(&mut sig, &sink);
        (nodes, graph.variant_layouts.clone(), {
            let mut table = locations.clone();
            table.remap_for_import(&map);
            table
        })
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
                TypeDesc::Tvar(None, crate::types::type_expr::VarDescBlock::OWN),
                level,
            )
        })
        .collect();

    // Phase 2: set descriptors using remapped refs.
    let mremap = internalize_mutabilities(graph, ctx);
    let mut ids = ImportedIdentities::new(&graph.identities);
    for (i, entry) in graph.entries.iter().enumerate() {
        let desc = internalize_desc(&entry.desc, i, &remap, &mremap, locs, &mut ids, ctx);
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
    ids.signature(&mut sig, ctx);
    remap_signature_refs(&mut sig, &remap, &layout_remap);
    import_signature_locations(&mut sig, locs);
    sig
}

/// The descriptor of entry `entry` of a graph, imported as node `node`.
#[allow(clippy::too_many_arguments)]
fn internalize_desc<S: TypeNodeSink>(
    desc: &PortableTypeDesc,
    entry: usize,
    remap: &[TypeExprRef],
    mremap: &[MutabilityRef],
    locs: &DeclLocImport<'_>,
    ids: &mut ImportedIdentities<'_>,
    ctx: &S,
) -> TypeDesc {
    let node = remap[entry];
    match desc {
        PortableTypeDesc::Tvar(name) => TypeDesc::Tvar(name.clone(), ids.var_desc(entry, node)),
        PortableTypeDesc::Tarrow { args, ret } => TypeDesc::Tarrow {
            args: args
                .iter()
                .map(|(lbl, typ)| ids.arg(lbl, remap[*typ], locs))
                .collect(),
            ret: remap[*ret],
        },
        PortableTypeDesc::Ttuple(types) => {
            TypeDesc::Ttuple(types.iter().map(|&i| remap[i]).collect())
        }
        PortableTypeDesc::Tconstr { path, args } => TypeDesc::Tconstr {
            path: ids.path(path, ctx),
            args: args.iter().map(|&i| remap[i]).collect(),
            abbrev: ctx.abbrev_nil(),
            path_block: ids.path_block(entry, node),
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
            let mut row = internalize_row_desc(prd, remap, ctx);
            if let Some((path, _)) = &mut row.row_name {
                *path = ids.path(path, ctx);
            }
            TypeDesc::Tvariant(Box::new(row))
        }
        PortableTypeDesc::Tunivar(name) => {
            TypeDesc::Tunivar(name.clone(), ids.var_desc(entry, node))
        }
        PortableTypeDesc::Tpoly { body, vars } => TypeDesc::Tpoly {
            body: remap[*body],
            vars: vars.iter().map(|&i| remap[i]).collect(),
        },
        PortableTypeDesc::Tpackage { path, lids, args } => TypeDesc::Tpackage {
            path: ids.path(path, ctx),
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
    use crate::types::type_expr::{PathBlockOwner, VarDescBlock};

    /// A saved graph with its entries and identities.
    fn save(ctx: &TypeContext, roots: &[TypeExprRef]) -> (Vec<usize>, PortableTypeGraph) {
        let mut file_names = crate::fast_hash::AHashSet::new();
        let mut ser = TypeGraphSerializer::new(ctx, None, &mut file_names);
        let indices = roots.iter().map(|&r| ser.serialize_type(r)).collect();
        let identities = saved_identities(ctx, &ser.nodes);
        let graph = PortableTypeGraph {
            entries: std::mem::take(&mut ser.entries),
            variant_layouts: Vec::new(),
            mutabilities: Vec::new(),
            identities,
        };
        (indices, graph)
    }

    /// The nodes of `graph` imported into `ctx`, as `internalize_signature`
    /// imports them.
    fn import(ctx: &TypeContext, graph: &PortableTypeGraph) -> Vec<TypeExprRef> {
        let remap: Vec<_> = graph.entries.iter().map(|_| ctx.new_var(None)).collect();
        let locs = ctx.import_decl_locs(std::iter::empty(), &|file| file);
        let mut ids = ImportedIdentities::new(&graph.identities);
        for (i, entry) in graph.entries.iter().enumerate() {
            let desc = internalize_desc(&entry.desc, i, &remap, &[], &locs, &mut ids, ctx);
            ctx.set_desc(remap[i], desc);
        }
        remap
    }

    fn path_of(ctx: &TypeContext, node: TypeExprRef) -> (Path, PathBlockOwner) {
        match &*ctx.get_desc(node) {
            TypeDesc::Tconstr {
                path, path_block, ..
            } => (path.clone(), path_block.owner()),
            _ => panic!("not a constructor"),
        }
    }

    fn origin_of(path: &Path) -> u32 {
        match path {
            Path::Pident(id) => id.origin().get(),
            _ => panic!("not a Pident"),
        }
    }

    /// OCaml saves an interface with `Subst.signature` `for_saving` and the
    /// importer unmarshals the copy, whose blocks are shared as the source's
    /// are (subst.ml:87-94, 121-126, btype.ml:511-512) and are none of the
    /// importer's own.
    #[test]
    fn an_imported_graph_shares_the_saved_blocks_and_holds_none_of_the_importers() {
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let int_a = ctx.new_predef_constr(crate::types::predef::path_int(), vec![]);
        let int_b = ctx.new_predef_constr(crate::types::predef::path_int(), vec![]);
        let t = Path::Pident(crate::ident::Ident::create_persistent("t"));
        let own = ctx.new_constr(t.clone(), vec![]);
        let kept = ctx.new_type(ctx.get_desc(own).clone().shared_from(own));
        let respelled = ctx.new_constr(t, vec![]);
        let none_a = ctx.new_var(None);
        let none_b = ctx.new_var(None);
        let named = ctx.new_var(Some("a".into()));
        let named_copy = ctx.new_type(TypeDesc::Tvar(
            Some("a".into()),
            VarDescBlock::OWN.copied_from(named),
        ));
        let arg = TypeArg::new(ArgLabel::labelled("x", DeclLoc::default()), int_a);
        let arrow_a = ctx.new_type(TypeDesc::Tarrow {
            args: vec![arg.clone()].into(),
            ret: int_a,
        });
        let arrow_b = ctx.new_type(TypeDesc::Tarrow {
            args: vec![arg.with_type(int_b)].into(),
            ret: int_b,
        });
        let other_label = ctx.new_type(TypeDesc::Tarrow {
            args: vec![TypeArg::new(
                ArgLabel::labelled("x", DeclLoc::default()),
                int_a,
            )]
            .into(),
            ret: int_a,
        });
        let roots = [
            int_a,
            int_b,
            own,
            kept,
            respelled,
            none_a,
            none_b,
            named,
            named_copy,
            arrow_a,
            arrow_b,
            other_label,
        ];
        let (at, graph) = save(&ctx, &roots);

        let importer = TypeContext::new(Arc::new(IdGenerator::new()));
        let nodes = import(&importer, &graph);
        let node = |i: usize| nodes[at[i]];

        // The saved predefined `int`: one block, the unit's, not Predef's.
        let (int_path, int_block) = path_of(&importer, node(0));
        assert_eq!(int_block, PathBlockOwner::Own);
        assert_eq!(path_of(&importer, node(1)).1, PathBlockOwner::Of(node(0)));
        assert_ne!(origin_of(&int_path), 0);
        assert_eq!(
            origin_of(&int_path),
            origin_of(&path_of(&importer, node(1)).0)
        );
        // A kept path stays shared; one allocated again does not.
        assert_eq!(path_of(&importer, node(3)).1, PathBlockOwner::Of(node(2)));
        assert_eq!(path_of(&importer, node(4)).1, PathBlockOwner::Own);
        // Every `Tvar None` is the static one; a copied descriptor stays shared.
        let var_block = |n| match &*importer.get_desc(n) {
            TypeDesc::Tvar(_, block) => *block,
            _ => panic!("not a variable"),
        };
        assert_eq!(var_block(node(6)), VarDescBlock::Of(node(5)));
        assert_eq!(var_block(node(7)), VarDescBlock::Own);
        assert_eq!(var_block(node(8)), VarDescBlock::Of(node(7)));
        // A label shared by two arrows stays shared; an equal one does not.
        let label = |n| match &*importer.get_desc(n) {
            TypeDesc::Tarrow { args, .. } => args[0].label_block().expect("labelled"),
            _ => panic!("not an arrow"),
        };
        assert_eq!(label(node(9)), label(node(10)));
        assert_ne!(label(node(9)), label(node(11)));

        // A second import holds blocks of its own.
        let again = import(&importer, &graph);
        assert_ne!(
            origin_of(&path_of(&importer, again[at[0]]).0),
            origin_of(&int_path)
        );
        assert_eq!(
            path_of(&importer, again[at[1]]).1,
            PathBlockOwner::Of(again[at[0]])
        );
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
                        val_attributes: vec![],
                        val_path: None,
                    },
                )
            })
            .collect::<Vec<_>>()
            .into();
        let save = |ctx: &TypeContext, sig: &Signature| {
            serialize_signature(sig, ctx, None, &mut crate::fast_hash::AHashSet::new())
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
        assert_eq!(std::mem::size_of::<Path>(), 24);
        assert_eq!(std::mem::size_of::<TypeDesc>(), 64);
        assert_eq!(std::mem::size_of::<crate::types::TypeExpr>(), 80);
    }

    #[test]
    fn dotted_allocations_survive_saved_cold_warm_store_and_shared_imports() {
        let save_sig = |ctx: &TypeContext, sig: &Signature| {
            serialize_signature(sig, ctx, None, &mut crate::fast_hash::AHashSet::new())
        };
        let saved = {
            let source = TypeContext::new(Arc::new(IdGenerator::new()));
            let mut arena = ParseArena::new();
            let name = arena.push_string("same");
            let equal = arena.push_string("same");
            let id = source.create_ast_ident(&arena, name);
            let other = source.create_ast_ident(&arena, equal);
            let prefix = Arc::new(Path::Pident(id));
            let a = source.dotted_from_ident(prefix.clone(), id, 0);
            let b = source.dotted_from_ident(prefix, other, 0);
            let c = source.dotted_from_ident(Arc::new(Path::Pident(id)), id, 0);
            let nested = source.dotted_from_ident(Arc::new(a.clone()), id, 0);
            let sig: Signature = [a.clone(), a, b, c]
                .into_iter()
                .map(|path| {
                    SignatureItem::SigValue(
                        id,
                        ValueDescription {
                            val_type: source.new_generic_constr(path, vec![]),
                            val_kind: ValueKind::ValReg,
                            val_loc: DeclLoc::default(),
                            val_attributes: vec![],
                            val_path: Some(nested.clone()),
                        },
                    )
                })
                .collect::<Vec<_>>()
                .into();
            save_sig(&source, &sig)
        };
        let verify = |ctx: &TypeContext, sig: &Signature| {
            let mut dots = Vec::new();
            let mut nested_dots = Vec::new();
            for item in sig.iter() {
                let SignatureItem::SigValue(id, value) = item else {
                    panic!("value")
                };
                let (path, _) = path_of(ctx, value.val_type);
                let dot = ctx.dotted_allocation(&path).expect("graph dotted evidence");
                let nested = ctx
                    .dotted_allocation(value.val_path.as_ref().unwrap())
                    .expect("signature dotted evidence");
                let inner = ctx
                    .dotted_allocation(&nested.prefix)
                    .expect("nested dotted evidence");
                assert_eq!(nested.name, ctx.ident_name_allocation(id));
                assert_eq!(inner.name, nested.name);
                assert_ne!(inner.key(), dot.key());
                nested_dots.push((nested, inner));
                dots.push(dot);
            }
            for (i, dot) in dots.iter().enumerate() {
                for other in &dots[i + 1..] {
                    assert_ne!(dot.key(), other.key());
                }
            }
            assert!(Arc::ptr_eq(&dots[0].prefix, &dots[1].prefix));
            assert!(Arc::ptr_eq(&dots[0].prefix, &dots[2].prefix));
            assert!(!Arc::ptr_eq(&dots[0].prefix, &dots[3].prefix));
            assert_eq!(dots[0].name, dots[1].name);
            assert_eq!(dots[0].name, dots[3].name);
            assert_ne!(dots[0].name, dots[2].name);
            for (i, (outer, inner)) in nested_dots.iter().enumerate() {
                assert!(Arc::ptr_eq(&dots[0].prefix, &inner.prefix));
                assert_eq!(dots[0].name, inner.name);
                for (next_outer, next_inner) in &nested_dots[i + 1..] {
                    assert_ne!(outer.key(), next_outer.key());
                    assert_ne!(inner.key(), next_inner.key());
                }
            }
            dots[0].name
        };
        let target = TypeContext::new(Arc::new(IdGenerator::new()));
        let locs = target.import_decl_locs(std::iter::empty(), &|file| file);
        let decoded = crate::binser::Encoded::encode(&saved).decode();
        let warm = internalize_signature(&saved.0, &saved.1, &locs, &target);
        let cold = internalize_signature(&decoded.0, &decoded.1, &locs, &target);
        assert_ne!(verify(&target, &warm), verify(&target, &cold));
        let workers: Vec<_> = (0..2)
            .map(|_| TypeContext::new(Arc::new(IdGenerator::new())))
            .collect();
        let mut names = Vec::new();
        for worker in &workers {
            let store = worker.thread_store();
            let locs = store.import_decl_locs(std::iter::empty(), &|file| file);
            let imported = internalize_signature_into_store(&saved.0, &saved.1, &locs, store);
            names.push(verify(worker, &imported));
            let again = save_sig(worker, &imported);
            let imported = internalize_signature(
                &again.0,
                &again.1,
                &target.import_decl_locs(std::iter::empty(), &|file| file),
                &target,
            );
            names.push(verify(&target, &imported));
        }
        for (i, a) in names.iter().enumerate() {
            for b in &names[i + 1..] {
                assert_ne!(a, b);
            }
        }
        let intern = |name: &str| target.intern_cmi_longident_name(name);
        let files = FileRemap::new(&[], &intern);
        let shared = internalize_signature_into_shared(
            &saved.0,
            &saved.1,
            &saved.2,
            &files,
            target.thread_store().shared_pool(),
        )
        .unwrap();
        let shared_name = verify(&target, &shared);
        assert_ne!(shared_name, verify(&target, &warm));
        let again = save_sig(&target, &shared);
        let imported = internalize_signature(&again.0, &again.1, &locs, &target);
        assert_ne!(shared_name, verify(&target, &imported));
        let digest = |value: &(Signature, PortableTypeGraph, DeclLocTable)| {
            let mut hash = std::collections::hash_map::DefaultHasher::new();
            crate::cmi::digest_ser::Canonical::new(&mut hash).hash(value);
            std::hash::Hasher::finish(&hash)
        };
        let mut without = saved.clone();
        without.1.identities.paths.clear();
        assert_eq!(digest(&saved), digest(&without));
    }

    #[test]
    fn name_allocations_survive_cold_warm_store_and_shared_imports() {
        let save_sig = |ctx: &TypeContext, sig: &Signature| {
            serialize_signature(sig, ctx, None, &mut crate::fast_hash::AHashSet::new())
        };
        let (saved, source_name) = {
            let source = TypeContext::new(Arc::new(IdGenerator::new()));
            let mut arena = ParseArena::new();
            let name = arena.push_string("same");
            let equal = arena.push_string("same");
            let a = source.create_ast_ident(&arena, name);
            let b = source.create_ast_ident(&arena, name);
            let c = source.create_ast_ident(&arena, equal);
            let typ = source.new_generic_constr(Path::Pident(a), vec![]);
            let value = |id| {
                SignatureItem::SigValue(
                    id,
                    ValueDescription {
                        val_type: typ,
                        val_kind: ValueKind::ValReg,
                        val_loc: DeclLoc::default(),
                        val_attributes: vec![],
                        val_path: Some(Path::Pident(a)),
                    },
                )
            };
            let sig: Signature = vec![value(a), value(b), value(c)].into();
            (save_sig(&source, &sig), source.ident_name_allocation(&a))
        };
        let verify = |ctx: &TypeContext, sig: &Signature| {
            let ids: Vec<_> = sig
                .iter()
                .map(|item| match item {
                    SignatureItem::SigValue(id, _) => *id,
                    _ => panic!("value"),
                })
                .collect();
            assert_ne!(ids[0].origin(), ids[1].origin());
            let a = ctx.ident_name_allocation(&ids[0]);
            assert_eq!(a, ctx.ident_name_allocation(&ids[1]));
            assert_ne!(a, ctx.ident_name_allocation(&ids[2]));
            assert_ne!(a, source_name);
            let SignatureItem::SigValue(_, value) = &sig[0] else {
                unreachable!()
            };
            let (Path::Pident(path_id), _) = path_of(ctx, value.val_type) else {
                panic!("path")
            };
            assert_eq!(a, ctx.ident_name_allocation(&path_id));
            a
        };
        let target = TypeContext::new(Arc::new(IdGenerator::new()));
        let locs = target.import_decl_locs(std::iter::empty(), &|file| file);
        let decoded = crate::binser::Encoded::encode(&saved).decode();
        let warm = internalize_signature(&saved.0, &saved.1, &locs, &target);
        let cold = internalize_signature(&decoded.0, &decoded.1, &locs, &target);
        assert_ne!(verify(&target, &warm), verify(&target, &cold));
        let workers: Vec<_> = (0..2)
            .map(|_| TypeContext::new(Arc::new(IdGenerator::new())))
            .collect();
        let mut names = Vec::new();
        for worker in &workers {
            let store = worker.thread_store();
            let locs = store.import_decl_locs(std::iter::empty(), &|file| file);
            let sig = internalize_signature_into_store(&saved.0, &saved.1, &locs, store);
            names.push(verify(worker, &sig));
            let saved_again = save_sig(worker, &sig);
            let imported = internalize_signature(
                &saved_again.0,
                &saved_again.1,
                &target.import_decl_locs(std::iter::empty(), &|file| file),
                &target,
            );
            names.push(verify(&target, &imported));
        }
        for (i, a) in names.iter().enumerate() {
            for b in &names[i + 1..] {
                assert_ne!(a, b);
            }
        }
        let intern = |name: &str| target.intern_cmi_longident_name(name);
        let files = FileRemap::new(&[], &intern);
        let shared = internalize_signature_into_shared(
            &saved.0,
            &saved.1,
            &saved.2,
            &files,
            target.thread_store().shared_pool(),
        )
        .unwrap();
        let shared_name = verify(&target, &shared);
        assert_ne!(shared_name, verify(&target, &warm));
        let again = save_sig(&target, &shared);
        let imported = internalize_signature(&again.0, &again.1, &locs, &target);
        assert_ne!(shared_name, verify(&target, &imported));
        let mut without = saved.clone();
        without.1.identities.ident_names.clear();
        let digest = |value: &(Signature, PortableTypeGraph, DeclLocTable)| {
            let mut hash = std::collections::hash_map::DefaultHasher::new();
            crate::cmi::digest_ser::Canonical::new(&mut hash).hash(value);
            std::hash::Hasher::finish(&hash)
        };
        assert_eq!(digest(&saved), digest(&without));
    }

    #[test]
    fn mapping_signature_identifiers_keeps_shared_prefix_allocations() {
        use crate::ident::Ident;
        let shared = Arc::new(Path::Pident(Ident::create_persistent("Prefix")));
        let distinct = Arc::new((*shared).clone());
        let item = |prefix: Arc<Path>| {
            SignatureItem::SigModtype(
                Ident::create_persistent("S"),
                ModtypeDeclaration {
                    mtd_type: Some(ModuleType::MtyIdent(Path::Pdot(prefix, "t".into(), 0))),
                    mtd_attributes: vec![],
                    mtd_loc: DeclLoc::default(),
                },
            )
        };
        let mut sig: Signature = vec![item(shared.clone()), item(shared), item(distinct)].into();
        map_signature_identifiers(&mut sig, &mut |id| {
            *id = id.with_origin(crate::ident::IdentOrigin::new(1));
        });
        let prefix = |i| match &sig[i] {
            SignatureItem::SigModtype(_, mtd) => match mtd.mtd_type.as_ref().unwrap() {
                ModuleType::MtyIdent(Path::Pdot(prefix, ..)) => prefix.clone(),
                _ => panic!("path"),
            },
            _ => panic!("modtype"),
        };
        assert!(Arc::ptr_eq(&prefix(0), &prefix(1)));
        assert!(!Arc::ptr_eq(&prefix(0), &prefix(2)));
    }

    /// Signature paths and graph paths use one saved namespace. Encoding
    /// discards runtime origins, so cold and warm imports must use the table.
    #[test]
    fn signature_and_graph_identities_survive_cold_warm_and_cross_store_imports() {
        use crate::ident::Ident;
        let source = TypeContext::new(Arc::new(IdGenerator::new()));
        let a = Ident::create_persistent("same").with_origin(source.fresh_ident_origin());
        let b = Ident::create_persistent("same").with_origin(source.fresh_ident_origin());
        let typ = source.new_constr(Path::Pident(a.clone()), vec![]);
        let sig: Signature = vec![
            SignatureItem::SigValue(
                a.clone(),
                ValueDescription {
                    val_type: typ,
                    val_kind: ValueKind::ValReg,
                    val_loc: DeclLoc::default(),
                    val_attributes: vec![],
                    val_path: Some(Path::Pident(a.clone())),
                },
            ),
            SignatureItem::SigModtype(
                b,
                ModtypeDeclaration {
                    mtd_type: Some(ModuleType::MtyIdent(Path::Pident(a))),
                    mtd_attributes: vec![],
                    mtd_loc: DeclLoc::default(),
                },
            ),
        ]
        .into();
        let save_sig = |ctx: &TypeContext, sig: &Signature| {
            serialize_signature(sig, ctx, None, &mut crate::fast_hash::AHashSet::new())
        };
        let saved = save_sig(&source, &sig);
        let decoded = crate::binser::Encoded::encode(&saved).decode();
        let verify = |ctx: &TypeContext, sig: &Signature| {
            let SignatureItem::SigValue(a, value) = &sig[0] else {
                panic!("value")
            };
            let SignatureItem::SigModtype(b, mtd) = &sig[1] else {
                panic!("modtype")
            };
            let Some(ModuleType::MtyIdent(path)) = &mtd.mtd_type else {
                panic!("path")
            };
            assert_ne!(a.origin().get(), 0);
            assert_ne!(
                a.origin(),
                b.origin(),
                "equal spelling does not merge blocks"
            );
            assert_eq!(
                a.origin().get(),
                origin_of(value.val_path.as_ref().unwrap())
            );
            assert_eq!(a.origin().get(), origin_of(path));
            assert_eq!(a.origin().get(), origin_of(&path_of(ctx, value.val_type).0));
            a.origin()
        };
        let target = TypeContext::new(Arc::new(IdGenerator::new()));
        let locs = target.import_decl_locs(std::iter::empty(), &|file| file);
        let warm = internalize_signature(&saved.0, &saved.1, &locs, &target);
        let cold = internalize_signature(&decoded.0, &decoded.1, &locs, &target);
        assert_ne!(verify(&target, &warm), verify(&target, &cold));

        // Both stores are live simultaneously. Their numeric origin spaces
        // may overlap; exporting each into one target must remap them apart.
        let worker_a = TypeContext::new(Arc::new(IdGenerator::new()));
        let worker_b = TypeContext::new(Arc::new(IdGenerator::new()));
        let into_store = |ctx: &TypeContext| {
            let store = ctx.thread_store();
            let locs = store.import_decl_locs(std::iter::empty(), &|file| file);
            internalize_signature_into_store(&saved.0, &saved.1, &locs, store)
        };
        let a = into_store(&worker_a);
        let b = into_store(&worker_b);
        verify(&worker_a, &a);
        verify(&worker_b, &b);
        let a = save_sig(&worker_a, &a);
        let b = save_sig(&worker_b, &b);
        let a = internalize_signature(&a.0, &a.1, &locs, &target);
        let b = internalize_signature(&b.0, &b.1, &locs, &target);
        assert_ne!(verify(&target, &a), verify(&target, &b));

        // The entire saved signature, not only its graph, has the same
        // semantic digest after clearing all physical identity metadata.
        let mut without = saved.clone();
        without.1.identities = PortableIdentities::default();
        let digest = |value: &(Signature, PortableTypeGraph, DeclLocTable)| {
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            crate::cmi::digest_ser::Canonical::new(&mut hasher).hash(value);
            std::hash::Hasher::finish(&hasher)
        };
        assert_eq!(digest(&saved), digest(&without));
    }

    /// The identities describe how the saved graph is laid out in memory,
    /// not what it means: no interface digest sees them.
    #[test]
    fn identities_stay_out_of_the_interface_digest() {
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let int = ctx.new_predef_constr(crate::types::predef::path_int(), vec![]);
        let (_, graph) = save(&ctx, &[int, int, ctx.new_var(None)]);
        assert!(!graph.identities.blocks.is_empty());
        let without = PortableTypeGraph {
            identities: PortableIdentities::default(),
            ..graph.clone()
        };
        let digest = |graph: &PortableTypeGraph| {
            let mut hasher = std::collections::hash_map::DefaultHasher::new();
            crate::cmi::digest_ser::Canonical::new(&mut hasher).hash(graph);
            std::hash::Hasher::finish(&hasher)
        };
        assert_eq!(digest(&graph), digest(&without));
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
            args: vec![
                TypeArg::unlabeled(shared),
                TypeArg::new(labels[1].clone(), shared),
                TypeArg::new(labels[2].clone(), distinct),
            ]
            .into(),
            ret: shared,
        });
        let mut file_names = crate::fast_hash::AHashSet::new();
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
        let none = PortableIdentities::default();
        let mut ids = ImportedIdentities::new(&none);
        let restored = internalize_desc(
            &entries[index].desc,
            index,
            &remap,
            &[],
            &locs,
            &mut ids,
            &ctx,
        );
        let TypeDesc::Tarrow { args, ret } = restored else {
            panic!("not arrow")
        };
        assert_eq!(args[0].typ, ret);
        assert_eq!(args[1].typ, ret);
        assert_ne!(args[2].typ, ret);
        assert!(matches!(args[0].label(), ArgLabel::Nolabel));
        for (arg, expected) in args.iter().zip(&labels).skip(1) {
            assert!(arg.label().same_label(expected));
            assert_eq!(ctx.resolve_loc(arg.label().loc()), loc);
        }
    }
}
