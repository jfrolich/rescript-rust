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

use super::graph_hash::{
    ArgKind, GraphWalk, Node, Row, RowFieldView, TypeGraph, hash_path_by_name,
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
    /// What the type is.
    pub desc: PortableTypeDesc,
    /// The type's binding level (`GENERIC_LEVEL` for generalized types).
    pub level: i32,
}

/// TypeDesc with indices into `PortableTypeGraph.entries` instead of arena refs.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub enum PortableTypeDesc {
    /// `TypeDesc::Tvar`: a type variable, with its name if it has one.
    Tvar(Option<crate::name::Name>),
    /// `TypeDesc::Tarrow`: a function type.
    Tarrow {
        /// The labelled parameter types.
        args: Vec<(ArgLabel, usize)>,
        /// The result type.
        ret: usize,
    },
    /// `TypeDesc::Ttuple`: the element types of a tuple.
    Ttuple(Vec<usize>),
    /// `TypeDesc::Tconstr`: a type constructor applied to arguments.
    Tconstr {
        /// The constructor.
        path: Path,
        /// The type arguments.
        args: Vec<usize>,
    },
    /// `TypeDesc::Tobject`: an object type.
    Tobject {
        /// The first `Tfield` of the field list (or its `Tnil`/row variable).
        fields: usize,
    },
    /// `TypeDesc::Tfield`: one field of an object's field list.
    Tfield {
        /// The field's name.
        name: crate::name::Name,
        /// Index into `PortableTypeGraph.mutabilities`.
        mutability: usize,
        /// The field's type.
        typ: usize,
        /// The rest of the field list.
        rest: usize,
    },
    /// `TypeDesc::Tnil`: the end of a closed object's field list.
    Tnil,
    /// `TypeDesc::Tlink`: an alias of another entry.
    Tlink(usize),
    /// `TypeDesc::Tsubst`: a substitution placeholder for another entry.
    Tsubst(usize),
    /// `TypeDesc::Tvariant`: a polymorphic variant type.
    Tvariant(PortableRowDesc),
    /// `TypeDesc::Tunivar`: a universally quantified variable.
    Tunivar(Option<crate::name::Name>),
    /// `TypeDesc::Tpoly`: a polymorphic type.
    Tpoly {
        /// The quantified type.
        body: usize,
        /// The `Tunivar` entries it quantifies over.
        vars: Vec<usize>,
    },
    /// `TypeDesc::Tpackage`: a first-class module type.
    Tpackage {
        /// The module type.
        path: Path,
        /// The constrained type names (`with type lid = ...`).
        lids: Vec<PortableLongident>,
        /// The types the constrained names are bound to, parallel to `lids`.
        args: Vec<usize>,
    },
}

/// A `Longident` that owns its names, independent of any `ParseArena`.
#[derive(Clone, Debug, PartialEq, Eq, Hash, serde::Serialize, serde::Deserialize)]
pub enum PortableLongident {
    /// A plain name.
    Lident(String),
    /// A name inside a module: `M.x`.
    Ldot(Box<PortableLongident>, String),
    /// A functor application: `F(X)`.
    Lapply(Box<PortableLongident>, Box<PortableLongident>),
}

/// Portable row description for polymorphic variants.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct PortableRowDesc {
    /// Labels as `RowDesc` keeps them: short ones decode inline, without
    /// an allocation.
    pub row_fields: Vec<(crate::types::asttypes::Label, PortableRowField)>,
    /// The row variable (or `Tnil`) standing for the other tags.
    pub row_more: usize,
    /// Whether no tags beyond `row_fields` are allowed.
    pub row_closed: bool,
    /// Whether the row may not be extended by unification.
    pub row_fixed: bool,
    /// The abbreviation the row was expanded from, with its arguments.
    pub row_name: Option<(Path, Vec<usize>)>,
}

/// Portable row field.
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub enum PortableRowField {
    /// `RowField::Rpresent`: the tag is present, with its argument type.
    Rpresent(Option<usize>),
    /// `RowField::Reither`: the tag may be present.
    Reither {
        /// Whether the tag may have no argument.
        constant: bool,
        /// The argument types it may have.
        types: Vec<usize>,
        /// Whether the tag was matched in a pattern.
        matched: bool,
    },
    /// `RowField::Rabsent`: the tag is absent.
    Rabsent,
}

/// A published signature. The checking worker freezes owned node arrays;
/// a first importer installs them in the pool, and storage encodes them later.
#[derive(Debug)]
pub struct PortablePersStruct {
    /// The unit name.
    pub ps_name: String,
    /// The source file name.
    pub ps_filename: String,
    /// The unit deprecation message.
    pub ps_deprecated: Option<String>,
    /// Imported interface digests.
    pub ps_crcs: Vec<(String, Option<[u8; 16]>)>,
    /// Whether the type graph can be published in the shared pool.
    pub shareable: bool,
    /// Stamp-independent structural fingerprint.
    pub fingerprint: u64,
    summary: std::sync::OnceLock<Arc<super::item_deps::SignatureSummary>>,
    /// Publication hashes from the shared graph; absent on stored/fallback units.
    shared_item_hashes: Option<Vec<(super::item_deps::Kind, crate::name::Name, u64)>>,
    decoded: std::sync::Mutex<Option<(PublishedSignature, Option<PortableRawSignature>)>>,
    encoded: std::sync::OnceLock<EncodedSignatures>,
    published_generation: Option<u64>,
    publication_counter_id: usize,
}

#[derive(Debug)]
enum PublishedSignature {
    Portable(Box<PortableSignature>),
    Shared(super::shared_reader::PublishedGraph),
}

impl PublishedSignature {
    fn portable(&self) -> std::borrow::Cow<'_, PortableSignature> {
        match self {
            Self::Portable(sig) => std::borrow::Cow::Borrowed(sig),
            Self::Shared(graph) => std::borrow::Cow::Owned(graph.portable()),
        }
    }
    fn summary(&self, unit: &str, hashes: Option<&[(super::item_deps::Kind, crate::name::Name, u64)]>) -> super::item_deps::SignatureSummary {
        match self {
            Self::Portable(sig) => super::item_deps::SignatureSummary::with_item_hashes(unit, sig, hashes),
            Self::Shared(graph) => super::item_deps::SignatureSummary::from_graph(
                unit, &graph.reader(), &graph.signature, hashes,
            ),
        }
    }
}

#[derive(Clone, Debug)]
struct EncodedSignatures {
    sig: crate::binser::Encoded<PortableSignature>,
    raw: Option<crate::binser::Encoded<PortableRawSignature>>,
}

// Preserve the order of the stored representation independently of the
// synchronization primitives used by a live publication.
#[derive(serde::Deserialize)]
struct StoredPersStruct {
    ps_name: String,
    ps_filename: String,
    ps_deprecated: Option<String>,
    ps_crcs: Vec<(String, Option<[u8; 16]>)>,
    shareable: bool,
    sig: crate::binser::Encoded<PortableSignature>,
    raw: Option<crate::binser::Encoded<PortableRawSignature>>,
    fingerprint: u64,
}

impl serde::Serialize for PortablePersStruct {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeStruct;
        let encoded = self.encoded();
        let mut s = serializer.serialize_struct("PortablePersStruct", 8)?;
        s.serialize_field("ps_name", &self.ps_name)?;
        s.serialize_field("ps_filename", &self.ps_filename)?;
        s.serialize_field("ps_deprecated", &self.ps_deprecated)?;
        s.serialize_field("ps_crcs", &self.ps_crcs)?;
        s.serialize_field("shareable", &self.shareable)?;
        s.serialize_field("sig", &encoded.sig)?;
        s.serialize_field("raw", &encoded.raw)?;
        s.serialize_field("fingerprint", &self.fingerprint)?;
        s.end()
    }
}

impl<'de> serde::Deserialize<'de> for PortablePersStruct {
    fn deserialize<D: serde::Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let s = <StoredPersStruct as serde::Deserialize>::deserialize(d)?;
        Ok(Self {
            ps_name: s.ps_name,
            ps_filename: s.ps_filename,
            ps_deprecated: s.ps_deprecated,
            ps_crcs: s.ps_crcs,
            shareable: s.shareable,
            fingerprint: s.fingerprint,
            published_generation: None,
            publication_counter_id: 0,
            summary: Default::default(),
            shared_item_hashes: None,
            decoded: Default::default(),
            encoded: std::sync::OnceLock::from(EncodedSignatures {
                sig: s.sig,
                raw: s.raw,
            }),
        })
    }
}

impl Clone for PortablePersStruct {
    fn clone(&self) -> Self {
        let encoded = self.encoded();
        Self {
            ps_name: self.ps_name.clone(),
            ps_filename: self.ps_filename.clone(),
            ps_deprecated: self.ps_deprecated.clone(),
            ps_crcs: self.ps_crcs.clone(),
            shareable: self.shareable,
            fingerprint: self.fingerprint,
            published_generation: self.published_generation,
            publication_counter_id: self.publication_counter_id,
            summary: self.summary.clone(),
            shared_item_hashes: None,
            decoded: Default::default(),
            encoded: std::sync::OnceLock::from(encoded.clone()),
        }
    }
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
    /// The raw signature, its type references being indices into
    /// `raw_type_graph.entries`.
    pub raw_ps_sig: Signature,
    /// File names shared by the main and raw location tables.
    pub cmi_longident_names: Vec<(u32, String)>,
    /// Self-contained type graph for `raw_ps_sig`.
    pub raw_type_graph: PortableTypeGraph,
    /// Location table of `raw_ps_sig` and `raw_type_graph`.
    pub raw_locations: DeclLocTable,
}

impl PortablePersStruct {
    fn record_access(&self, imported: bool) {
        if let Some(generation) = self.published_generation {
            crate::perf_counters::record_signature_access(
                self.publication_counter_id,
                generation,
                imported,
            );
        }
    }

    #[cfg(test)]
    pub(crate) fn has_decoded_signatures(&self) -> bool {
        self.decoded.lock().unwrap().is_some()
    }

    /// Retain decoded signatures until the first byte reader.
    pub fn new(
        ps_name: String,
        ps_filename: String,
        ps_deprecated: Option<String>,
        ps_crcs: Vec<(String, Option<[u8; 16]>)>,
        sig: PortableSignature,
        raw: Option<PortableRawSignature>,
        fingerprint: u64,
    ) -> Self {
        Self {
            ps_name,
            ps_filename,
            ps_deprecated,
            ps_crcs,
            shareable: graph_is_shareable(&sig.type_graph),
            fingerprint,
            published_generation: None,
            publication_counter_id: 0,
            summary: Default::default(),
            shared_item_hashes: None,
            encoded: Default::default(),
            decoded: std::sync::Mutex::new(Some((PublishedSignature::Portable(Box::new(sig)), raw))),
        }
    }

    /// Finish a leaf publication after signature release. No dependent needs
    /// its decoded graph, so keep only the bytes storage will need anyway.
    pub fn prepare_for_storage(&self) {
        self.encoded();
        // The scheduler calls this only for a unit with no waiting importer.
        // Unlike an ordinary storage reader, it can release detached arrays
        // as well as raw signatures. A later build can load the stored bytes.
        *self.decoded.lock().unwrap() = None;
    }

    fn encoded(&self) -> &EncodedSignatures {
        self.encoded.get_or_init(|| {
            let mut decoded = self.decoded.lock().unwrap();
            let (sig, raw) = decoded
                .as_ref()
                .expect("unencoded publication has signatures");
            // Compute the summary while the decoded form is still available.
            self.summary.get_or_init(|| {
                Arc::new(sig.summary(&self.ps_name, self.shared_item_hashes.as_deref()))
            });
            let encoded = EncodedSignatures {
                sig: match sig {
                    PublishedSignature::Portable(sig) => crate::binser::Encoded::encode(sig.as_ref()),
                    PublishedSignature::Shared(graph) => graph.encode(),
                },
                raw: raw.as_ref().map(crate::binser::Encoded::encode),
            };
            if matches!(sig, PublishedSignature::Portable(_)) {
                *decoded = None;
            } else if let Some((_, raw)) = decoded.as_mut() {
                // Keep the frozen graph for a later importer, not a duplicate
                // raw signature after its bytes have been produced.
                *raw = None;
            }
            encoded
        })
    }

    /// Item digests and references, computed on first use.
    pub fn summary(&self) -> &Arc<super::item_deps::SignatureSummary> {
        // Do not hold the summary's OnceLock while waiting for the slot:
        // the encoder fills the summary under the slot lock.
        if let Some(summary) = self.summary.get() {
            return summary;
        }
        let decoded = self.decoded.lock().unwrap();
        if let Some((sig, _)) = decoded.as_ref() {
            return self.summary.get_or_init(|| {
                Arc::new(sig.summary(&self.ps_name, self.shared_item_hashes.as_deref()))
            });
        }
        drop(decoded);
        let encoded = self.encoded();
        self.summary.get_or_init(|| {
            Arc::new(super::item_deps::SignatureSummary::of(
                &self.ps_name,
                &self.decode_signature(encoded),
            ))
        })
    }

    /// The main signature, decoded after ensuring bytes exist.
    pub fn signature(&self) -> PortableSignature {
        self.decode_signature(self.encoded())
    }

    fn decode_signature(&self, encoded: &EncodedSignatures) -> PortableSignature {
        if crate::perf_counters::enabled()
            && self.published_generation == Some(crate::types::thread_store::build_generation())
        {
            crate::perf_counters::record_published_signature_decode();
        }
        encoded.sig.decode()
    }
    /// The raw signature, using the retained graph until storage encodes it.
    pub fn raw_signature(&self) -> Option<PortableRawSignature> {
        if self.encoded.get().is_none() {
            let decoded = self.decoded.lock().unwrap();
            if let Some((_, raw)) = decoded.as_ref() {
                // GenType may read a dependency's raw signature while publishing
                // the current unit. Do not encode either signature just to read
                // this graph; byte production belongs to the storage reader.
                return raw.clone();
            }
        }
        self.encoded()
            .raw
            .as_ref()
            .map(crate::binser::Encoded::decode)
    }
    /// Whether a raw signature exists, without encoding or decoding.
    pub fn has_raw_signature(&self) -> bool {
        if let Some(encoded) = self.encoded.get() {
            return encoded.raw.is_some();
        }
        let decoded = self.decoded.lock().unwrap();
        match decoded.as_ref() {
            Some((_, raw)) => raw.is_some(),
            None => {
                drop(decoded);
                self.encoded().raw.is_some()
            }
        }
    }
}

// ============================================================================
// Fingerprinting: stamp-independent structural hash
// ============================================================================

/// What hashing a signature reads of its portable type graph: the type
/// entries, and the variant layouts and object-field mutabilities that
/// entries and declarations refer to by index (indices follow allocation
/// order, so they are hashed by what they point to).
#[derive(Clone, Copy)]
pub struct HashGraph<'a> {
    /// `PortableTypeGraph::entries`.
    pub entries: &'a [PortableTypeEntry],
    /// `PortableTypeGraph::variant_layouts`.
    pub layouts: &'a [crate::types::VariantLayout],
    /// `PortableTypeGraph::mutabilities`.
    pub mutabilities: &'a [crate::types::asttypes::MutableFlag],
}

impl<'a> HashGraph<'a> {
    /// What hashing reads of `graph`.
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

/// Compute a stamp-independent structural fingerprint of a portable type graph
/// and signature. Uses name-based identity for Paths (ignoring stamps) so that
/// recompilations producing the same logical interface get the same fingerprint
/// even if internal stamps shift due to dependency changes.
/// Public API for computing a fingerprint outside of `serialize_pers_struct`
/// (e.g., for namespace signatures synthesized directly).
pub fn compute_type_graph_fingerprint(entries: &HashGraph<'_>, sig: &Signature) -> u64 {
    signature_fingerprint(entries, sig)
}

/// The fingerprint of `sig`, whose types are nodes of `graph`: one hash of
/// the whole signature, so types shared between items are hashed once
/// (`graph_hash`). Linear in the signature and the nodes it reaches.
pub fn signature_fingerprint<G: TypeGraph>(graph: &G, sig: &Signature) -> u64 {
    // Deterministic within a build (fixed seeds); the fingerprint only lives
    // in the in-memory interface registry.
    use std::hash::BuildHasher;
    let mut hasher =
        ahash::RandomState::with_seeds(0x5245_5343, 0x5249_5054, 0x4649_4e47, 0x4552_5052)
            .build_hasher();

    // Hash the public signature through its type roots instead of hashing
    // the graph's storage linearly. The same interface can store its nodes
    // in a different order depending on whether it was produced during a
    // cold parallel build or a later watch rebuild; dependency invalidation
    // needs the interface's graph, not the order it is stored in.
    hash_signature(&mut hasher, sig, &mut GraphWalk::new(graph));

    hasher.finish()
}

impl super::graph_hash::TypeGraph for HashGraph<'_> {
    type Ref = usize;
    type Arg = (ArgLabel, usize);
    type Row = PortableRowDesc;
    type RowField = PortableRowField;
    type Mutability = usize;
    type Lid = PortableLongident;

    fn slots(&self) -> usize {
        self.entries.len()
    }

    fn slot(&self, r: usize) -> Option<usize> {
        (r < self.entries.len()).then_some(r)
    }

    fn root(&self, r: TypeExprRef) -> usize {
        r.index()
    }

    fn node(&self, slot: usize) -> Node<'_, Self> {
        match &self.entries[slot].desc {
            PortableTypeDesc::Tvar(name) => Node::Tvar(*name),
            PortableTypeDesc::Tarrow { args, ret } => Node::Tarrow { args, ret: *ret },
            PortableTypeDesc::Ttuple(elems) => Node::Ttuple(elems),
            PortableTypeDesc::Tconstr { path, args } => Node::Tconstr { path: *path, args },
            PortableTypeDesc::Tobject { fields } => Node::Tobject { fields: *fields },
            PortableTypeDesc::Tfield {
                name,
                mutability,
                typ,
                rest,
            } => Node::Tfield {
                name: *name,
                mutability: *mutability,
                typ: *typ,
                rest: *rest,
            },
            PortableTypeDesc::Tnil => Node::Tnil,
            PortableTypeDesc::Tlink(target) => Node::Tlink(*target),
            PortableTypeDesc::Tsubst(target) => Node::Tsubst(*target),
            PortableTypeDesc::Tvariant(row) => Node::Tvariant(row),
            PortableTypeDesc::Tunivar(name) => Node::Tunivar(*name),
            PortableTypeDesc::Tpoly { body, vars } => Node::Tpoly { body: *body, vars },
            PortableTypeDesc::Tpackage { path, lids, args } => Node::Tpackage {
                path: *path,
                lids,
                args,
            },
        }
    }

    fn arg<'a>(&'a self, arg: &'a (ArgLabel, usize)) -> (ArgKind, Option<&'a str>, usize) {
        match &arg.0 {
            ArgLabel::Nolabel => (ArgKind::Nolabel, None, arg.1),
            ArgLabel::Labelled(name) => (ArgKind::Labelled, Some(&name.txt), arg.1),
            ArgLabel::Optional(name) => (ArgKind::Optional, Some(&name.txt), arg.1),
        }
    }

    fn row<'a>(&'a self, row: &'a PortableRowDesc) -> Row<'a, Self> {
        Row {
            fields: &row.row_fields,
            more: row.row_more,
            closed: row.row_closed,
            fixed: row.row_fixed,
            name: row
                .row_name
                .as_ref()
                .map(|(path, args)| (*path, args.as_slice())),
        }
    }

    fn row_field<'a>(&'a self, field: &'a PortableRowField) -> RowFieldView<'a, Self> {
        match field {
            PortableRowField::Rpresent(typ) => RowFieldView::Rpresent(*typ),
            PortableRowField::Reither {
                constant,
                types,
                matched,
            } => RowFieldView::Reither {
                constant: *constant,
                types,
                matched: *matched,
            },
            PortableRowField::Rabsent => RowFieldView::Rabsent,
        }
    }

    fn mutability(&self, cell: usize) -> Option<crate::types::asttypes::MutableFlag> {
        self.mutabilities.get(cell).copied()
    }

    fn package_lids<'a>(
        &'a self,
        lids: &'a [PortableLongident],
    ) -> std::borrow::Cow<'a, [PortableLongident]> {
        std::borrow::Cow::Borrowed(lids)
    }

    fn layout(
        &self,
        layout: crate::types::VariantLayoutRef,
    ) -> Option<&crate::types::VariantLayout> {
        self.layouts.get(layout.0 as usize)
    }
}

/// Hash the signature structure: item names and kinds.
/// Uses name-based identity for all paths.
fn hash_signature<G: TypeGraph>(
    hasher: &mut impl Hasher,
    sig: &Signature,
    walk: &mut GraphWalk<'_, G>,
) {
    sig.len().hash(hasher);
    for item in sig {
        hash_sig_item(hasher, item, walk);
    }
}

/// The fingerprint contribution of one signature item.
pub fn hash_sig_item<G: TypeGraph>(
    hasher: &mut impl Hasher,
    item: &SignatureItem,
    walk: &mut GraphWalk<'_, G>,
) {
    std::mem::discriminant(item).hash(hasher);
    match item {
        SignatureItem::SigValue(ident, vd) => {
            ident.name().hash(hasher);
            hash_value_desc(hasher, vd, walk);
        }
        SignatureItem::SigType(ident, td, rec) => {
            ident.name().hash(hasher);
            std::mem::discriminant(rec).hash(hasher);
            hash_type_decl(hasher, td, walk);
        }
        SignatureItem::SigTypext(ident, ext, es) => {
            ident.name().hash(hasher);
            std::mem::discriminant(es).hash(hasher);
            hash_extension_constructor(hasher, ext, walk);
        }
        SignatureItem::SigModule(ident, md, _rec) => {
            ident.name().hash(hasher);
            hash_attributes(hasher, &md.md_attributes);
            hash_module_type(hasher, &md.md_type, walk);
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
            hash_modtype_decl(hasher, mtd, walk);
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

fn hash_value_desc<G: TypeGraph>(
    hasher: &mut impl Hasher,
    vd: &ValueDescription,
    walk: &mut GraphWalk<'_, G>,
) {
    walk.type_ref(hasher, vd.val_type);
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

fn hash_type_decl<G: TypeGraph>(
    hasher: &mut impl Hasher,
    td: &TypeDeclaration,
    walk: &mut GraphWalk<'_, G>,
) {
    td.type_arity.hash(hasher);
    hash_attributes(hasher, &td.type_attributes);
    hash_type_expr_refs(hasher, &td.type_params, walk);
    td.type_private.hash(hasher);
    if let Some(manifest) = td.type_manifest {
        true.hash(hasher);
        walk.type_ref(hasher, manifest);
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
    hash_type_kind(hasher, &td.type_kind, walk);
    td.type_inlined_types.len().hash(hasher);
    for inlined in &td.type_inlined_types {
        match inlined {
            TypeInlinedType::Record { type_name, labels } => {
                type_name.hash(hasher);
                hash_label_decls(hasher, labels, walk);
            }
        }
    }
}

fn hash_type_expr_refs<G: TypeGraph>(
    hasher: &mut impl Hasher,
    refs: &[TypeExprRef],
    walk: &mut GraphWalk<'_, G>,
) {
    refs.len().hash(hasher);
    for r in refs {
        walk.type_ref(hasher, *r);
    }
}

fn hash_type_kind<G: TypeGraph>(
    hasher: &mut impl Hasher,
    kind: &TypeKind,
    walk: &mut GraphWalk<'_, G>,
) {
    std::mem::discriminant(kind).hash(hasher);
    match kind {
        TypeKind::TypeAbstract | TypeKind::TypeOpen => {}
        // The representations decide dependents' JS (`@unboxed`, `@tag`,
        // inlined records).
        TypeKind::TypeRecord(labels, repr) => {
            hash_label_decls(hasher, labels, walk);
            std::mem::discriminant(repr).hash(hasher);
            match repr {
                crate::types::decl::RecordRepresentation::RecordUnboxed(flag) => flag.hash(hasher),
                crate::types::decl::RecordRepresentation::RecordInlined {
                    name,
                    representation,
                } => {
                    name.hash(hasher);
                    representation.position.hash(hasher);
                    hash_layout(hasher, walk.graph().layout(representation.variant));
                }
                _ => {}
            }
        }
        TypeKind::TypeVariant(ctors, layout) => {
            hash_layout(hasher, walk.graph().layout(*layout));
            ctors.len().hash(hasher);
            for ctor in ctors {
                ctor.cd_id.name().hash(hasher);
                // The run-time tag (`@as`).
                format!("{:?}", ctor.cd_runtime_tag).hash(hasher);
                hash_attributes(hasher, &ctor.cd_attributes);
                hash_constructor_args(hasher, &ctor.cd_args, walk);
                if let Some(res) = ctor.cd_res {
                    true.hash(hasher);
                    walk.type_ref(hasher, res);
                } else {
                    false.hash(hasher);
                }
            }
        }
    }
}

/// A variant layout, as its equality compares it. The allocation identities
/// of its shapes take no part (`variant_runtime::Instance`'s `Hash`): no
/// dependent reads them, and an import gives them new values, so the layout
/// of a stored interface and of its shared graph hash alike.
fn hash_layout(hasher: &mut impl Hasher, layout: Option<&crate::types::VariantLayout>) {
    let Some(layout) = layout else {
        false.hash(hasher);
        return;
    };
    true.hash(hasher);
    layout.unboxed.hash(hasher);
    layout.constructors.hash(hasher);
    layout.matching_facts.tag_name.hash(hasher);
    layout.matching_facts.block_types.hash(hasher);
    layout.matching_facts.literal_tags.hash(hasher);
}

fn hash_label_decls<G: TypeGraph>(
    hasher: &mut impl Hasher,
    labels: &[LabelDeclaration],
    walk: &mut GraphWalk<'_, G>,
) {
    labels.len().hash(hasher);
    for label in labels {
        label.ld_id.name().hash(hasher);
        // The run-time field name (`@as`).
        label.ld_runtime_name.hash(hasher);
        hash_attributes(hasher, &label.ld_attributes);
        label.ld_mutable.hash(hasher);
        label.ld_optional.hash(hasher);
        walk.type_ref(hasher, label.ld_type);
    }
}

fn hash_constructor_args<G: TypeGraph>(
    hasher: &mut impl Hasher,
    args: &ConstructorArguments,
    walk: &mut GraphWalk<'_, G>,
) {
    std::mem::discriminant(args).hash(hasher);
    match args {
        ConstructorArguments::CstrTuple(types) => hash_type_expr_refs(hasher, types, walk),
        ConstructorArguments::CstrRecord(labels) => hash_label_decls(hasher, labels, walk),
    }
}

fn hash_extension_constructor<G: TypeGraph>(
    hasher: &mut impl Hasher,
    ext: &ExtensionConstructor,
    walk: &mut GraphWalk<'_, G>,
) {
    hash_path_by_name(hasher, &ext.ext_type_path);
    hash_attributes(hasher, &ext.ext_attributes);
    hash_type_expr_refs(hasher, &ext.ext_type_params, walk);
    hash_constructor_args(hasher, &ext.ext_args, walk);
    if let Some(ret) = ext.ext_ret_type {
        true.hash(hasher);
        walk.type_ref(hasher, ret);
    } else {
        false.hash(hasher);
    }
    ext.ext_private.hash(hasher);
    ext.ext_is_exception.hash(hasher);
}

fn hash_modtype_decl<G: TypeGraph>(
    hasher: &mut impl Hasher,
    mtd: &ModtypeDeclaration,
    walk: &mut GraphWalk<'_, G>,
) {
    hash_attributes(hasher, &mtd.mtd_attributes);
    if let Some(mty) = &mtd.mtd_type {
        true.hash(hasher);
        hash_module_type(hasher, mty, walk);
    } else {
        false.hash(hasher);
    }
}

fn hash_module_type<G: TypeGraph>(
    hasher: &mut impl Hasher,
    mty: &ModuleType,
    walk: &mut GraphWalk<'_, G>,
) {
    std::mem::discriminant(mty).hash(hasher);
    match mty {
        ModuleType::MtyIdent(path) => hash_path_by_name(hasher, path),
        ModuleType::MtySignature(sig) => hash_signature(hasher, sig, walk),
        ModuleType::MtyFunctor {
            param,
            param_type,
            result,
        } => {
            param.name().hash(hasher);
            if let Some(pt) = param_type {
                hash_module_type(hasher, pt, walk);
            }
            hash_module_type(hasher, result, walk);
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
    serialize_pers_struct_inner(ps, ctx, arena, true, &PublicationStamps::new(ctx))
}

/// Publication computes hashes after the shared graph is built, not here.
pub(crate) fn serialize_for_publication(
    ps: &PersStruct,
    ctx: &TypeContext,
    arena: Option<&ParseArena>,
) -> PortablePersStruct {
    serialize_pers_struct_inner(ps, ctx, arena, false, &PublicationStamps::new(ctx))
}

/// Naming input shared by the direct builder and check-only oracle. Each
/// store binder consumes one fresh compilation stamp, independent of which
/// representation reads it. This is not a replay of store-building effects.
struct PublicationStamps<'a> {
    ctx: &'a TypeContext,
    assigned: std::cell::RefCell<AHashMap<i32, i32>>,
}
impl<'a> PublicationStamps<'a> {
    fn new(ctx: &'a TypeContext) -> Self {
        Self { ctx, assigned: Default::default() }
    }
    fn get(&self, stamp: i32) -> Option<i32> {
        Some(*self.assigned.borrow_mut().entry(stamp)
            .or_insert_with(|| self.ctx.published_binder_stamp()))
    }
}

fn serialize_pers_struct_inner(
    ps: &PersStruct,
    ctx: &TypeContext,
    arena: Option<&ParseArena>,
    hash_portable: bool,
    stamps: &PublicationStamps<'_>,
) -> PortablePersStruct {
    // The file names of the signatures' locations travel with them, keyed
    // in order of first use (see `PortableFileNames`).
    let mut file_names = PortableFileNames::default();
    let (sig, type_graph, locations) =
        serialize_signature(ps.ps_sig.as_ref(), ctx, arena, &mut file_names);
    let raw = ctx
        .find_raw_module_sig(&ps.ps_name)
        .map(|raw_sig| serialize_signature(&raw_sig, ctx, arena, &mut file_names));
    let mut sig = PortableSignature {
        ps_sig: sig,
        cmi_longident_names: file_names.names,
        type_graph,
        locations,
    };
    let mut raw = raw.map(
        |(raw_ps_sig, raw_type_graph, raw_locations)| PortableRawSignature {
            raw_ps_sig,
            raw_type_graph,
            raw_locations,
            cmi_longident_names: sig.cmi_longident_names.clone(),
        },
    );
    {
        let saved_stamp = |stamp| stamps.get(stamp);
        remap_saved_stamps(&mut sig.ps_sig, &mut sig.type_graph, &saved_stamp);
        if let Some(raw) = &mut raw {
            remap_saved_stamps(&mut raw.raw_ps_sig, &mut raw.raw_type_graph, &saved_stamp);
        }
    }
    let fingerprint = if hash_portable {
        compute_type_graph_fingerprint(&HashGraph::of(&sig.type_graph), &sig.ps_sig)
    } else {
        // Filled before the Arc is registered or exposed to any reader.
        0
    };
    PortablePersStruct::new(
        ps.ps_name.clone(),
        ps.ps_filename.clone(),
        ps.ps_deprecated.clone(),
        ps.ps_crcs.clone(),
        sig,
        raw,
        fingerprint,
    )
}

/// Apply the publication's deterministic store-binder mapping before
/// either shared nodes or bytes are produced. Graph indices are untouched.
fn remap_saved_ident(id: &mut crate::ident::Ident, stamps: &dyn Fn(i32) -> Option<i32>) {
    if id.stamp() >= crate::ident::STORE_STAMP_BASE
        && let Some(stamp) = stamps(id.stamp())
    {
        *id = id.with_stamp(stamp);
    }
}
fn remap_saved_path(p: &mut Path, stamps: &dyn Fn(i32) -> Option<i32>) {
    use crate::types::path::PathView;
    *p = match *p.view() {
        PathView::Pident(mut id) => {
            let before = id.stamp();
            remap_saved_ident(&mut id, stamps);
            if id.stamp() == before { *p } else { Path::pident(id) }
        }
        PathView::Pdot(mut parent, name, pos) => {
            let before = parent;
            remap_saved_path(&mut parent, stamps);
            if parent == before { *p } else { Path::pdot_pos(parent, name, pos) }
        }
        PathView::Papply(mut f, mut arg) => {
            let before = (f, arg);
            remap_saved_path(&mut f, stamps);
            remap_saved_path(&mut arg, stamps);
            if (f, arg) == before { *p } else { Path::papply(f, arg) }
        }
    };
}
/// Give every identifier with a store stamp the stamp `stamps` maps it to,
/// before either shared nodes or bytes are produced. Graph indices are
/// untouched. `stamps` is asked only for stamps of the store range.
fn remap_saved_stamps(
    sig: &mut Signature,
    graph: &mut PortableTypeGraph,
    stamps: &dyn Fn(i32) -> Option<i32>,
) {

    fn labels(labels: &mut [LabelDeclaration], stamps: &dyn Fn(i32) -> Option<i32>) {
        for label in labels {
            remap_saved_ident(&mut label.ld_id, stamps);
        }
    }
    fn args(args: &mut ConstructorArguments, stamps: &dyn Fn(i32) -> Option<i32>) {
        if let ConstructorArguments::CstrRecord(fields) = args {
            labels(fields, stamps);
        }
    }
    fn module(mty: &mut ModuleType, stamps: &dyn Fn(i32) -> Option<i32>) {
        match mty {
            ModuleType::MtyIdent(p) => remap_saved_path(p, stamps),
            ModuleType::MtyAlias(_, p) => remap_saved_path(Arc::make_mut(p), stamps),
            ModuleType::MtySignature(sig) => signature(Arc::make_mut(sig), stamps),
            ModuleType::MtyFunctor {
                param,
                param_type,
                result,
            } => {
                remap_saved_ident(param, stamps);
                if let Some(mty) = param_type {
                    module(mty, stamps);
                }
                module(result, stamps);
            }
        }
    }
    fn signature(sig: &mut Signature, stamps: &dyn Fn(i32) -> Option<i32>) {
        for item in sig {
            match item {
                SignatureItem::SigValue(id, vd) => {
                    remap_saved_ident(id, stamps);
                    if let Some(p) = &mut vd.val_path {
                        remap_saved_path(p, stamps);
                    }
                }
                SignatureItem::SigType(id, td, _) => {
                    remap_saved_ident(id, stamps);
                    let td = Arc::make_mut(td);
                    if let Some(p) = &mut td.type_path {
                        remap_saved_path(p, stamps);
                    }
                    match &mut td.type_kind {
                        TypeKind::TypeRecord(fields, _) => labels(fields, stamps),
                        TypeKind::TypeVariant(constructors, _) => {
                            for cd in constructors.iter_mut() {
                                remap_saved_ident(&mut cd.cd_id, stamps);
                                args(&mut cd.cd_args, stamps);
                            }
                        }
                        TypeKind::TypeAbstract | TypeKind::TypeOpen => {}
                    }
                    for TypeInlinedType::Record { labels: fields, .. } in &mut td.type_inlined_types
                    {
                        labels(fields, stamps);
                    }
                }
                SignatureItem::SigTypext(id, ext, _) => {
                    remap_saved_ident(id, stamps);
                    remap_saved_path(&mut ext.ext_type_path, stamps);
                    args(&mut ext.ext_args, stamps);
                }
                SignatureItem::SigModule(id, md, _) => {
                    remap_saved_ident(id, stamps);
                    if let Some(p) = &mut md.md_path {
                        remap_saved_path(p, stamps);
                    }
                    module(&mut md.md_type, stamps);
                }
                SignatureItem::SigModtype(id, md) => {
                    remap_saved_ident(id, stamps);
                    if let Some(mty) = &mut md.mtd_type {
                        module(mty, stamps);
                    }
                }
                SignatureItem::SigClass | SignatureItem::SigClassType => {}
            }
        }
    }
    signature(sig, stamps);
    for entry in &mut graph.entries {
        match &mut entry.desc {
            PortableTypeDesc::Tconstr { path: p, .. }
            | PortableTypeDesc::Tpackage { path: p, .. } => remap_saved_path(p, stamps),
            PortableTypeDesc::Tvariant(row) => {
                if let Some((p, _)) = &mut row.row_name {
                    remap_saved_path(p, stamps);
                }
            }
            PortableTypeDesc::Tvar(_)
            | PortableTypeDesc::Tarrow { .. }
            | PortableTypeDesc::Ttuple(_)
            | PortableTypeDesc::Tobject { .. }
            | PortableTypeDesc::Tfield { .. }
            | PortableTypeDesc::Tnil
            | PortableTypeDesc::Tlink(_)
            | PortableTypeDesc::Tsubst(_)
            | PortableTypeDesc::Tunivar(_)
            | PortableTypeDesc::Tpoly { .. } => {}
        }
    }
}

/// Serialize `sig` with its location table, adding the file names of its
/// locations to `file_names`.
fn serialize_signature(
    sig: &Signature,
    ctx: &TypeContext,
    arena: Option<&ParseArena>,
    file_names: &mut PortableFileNames,
) -> (Signature, PortableTypeGraph, DeclLocTable) {
    let mut ser = TypeGraphSerializer::<PortableSink>::new(ctx, arena, file_names);
    let mut sig = sig.clone();
    ser.remap_signature(&mut sig);
    ser.remap_signature_locations(&mut sig);
    let type_graph = PortableTypeGraph {
        entries: ser.sink.entries,
        variant_layouts: ser.variant_layouts,
        mutabilities: ser.mutabilities,
    };
    (sig, type_graph, ser.locations)
}

/// One traversal, with either portable entries or shared descriptor payloads.
trait SignatureSink: Default + Sized {
    type Desc;
    fn reserve(&mut self) -> usize;
    fn write(&mut self, index: usize, desc: Self::Desc, level: i32);
    fn describe(ser: &mut TypeGraphSerializer<'_, '_, Self>, desc: &TypeDesc) -> Self::Desc;
}

#[derive(Default)]
struct PortableSink { entries: Vec<PortableTypeEntry> }

impl SignatureSink for PortableSink {
    type Desc = PortableTypeDesc;
    fn reserve(&mut self) -> usize {
        let index = self.entries.len();
        self.entries.push(PortableTypeEntry { desc: PortableTypeDesc::Tvar(None), level: 0 });
        index
    }
    fn write(&mut self, index: usize, desc: Self::Desc, level: i32) {
        self.entries[index] = PortableTypeEntry { desc, level };
    }
    fn describe(ser: &mut TypeGraphSerializer<'_, '_, Self>, desc: &TypeDesc) -> PortableTypeDesc {
        match desc {
            TypeDesc::Tvar(name) => PortableTypeDesc::Tvar(*name),
            TypeDesc::Tarrow { args, ret } => PortableTypeDesc::Tarrow {
                args: ser
                    .ctx
                    .type_args(args)
                    .iter()
                    .map(|arg| {
                        (
                            ser.portable_label(&arg.label().to_arg_label()),
                            ser.serialize_type(arg.typ),
                        )
                    })
                    .collect(),
                ret: ser.serialize_type(*ret),
            },
            TypeDesc::Ttuple(types) => {
                PortableTypeDesc::Ttuple(ser.ctx.type_list(types).iter().map(|t| ser.serialize_type(t)).collect())
            }
            TypeDesc::Tconstr { path, args, .. } => PortableTypeDesc::Tconstr {
                path: *path,
                args: ser.ctx.type_list(args).iter().map(|t| ser.serialize_type(t)).collect(),
            },
            TypeDesc::Tobject { fields } => PortableTypeDesc::Tobject {
                fields: ser.serialize_type(*fields),
            },
            TypeDesc::Tfield {
                name,
                mutability,
                typ,
                rest,
            } => PortableTypeDesc::Tfield {
                name: *name,
                mutability: ser.serialize_mutability(*mutability),
                typ: ser.serialize_type(*typ),
                rest: ser.serialize_type(*rest),
            },
            TypeDesc::Tnil => PortableTypeDesc::Tnil,
            TypeDesc::Tlink(r) => PortableTypeDesc::Tlink(ser.serialize_type(*r)),
            TypeDesc::Tsubst(r) => PortableTypeDesc::Tsubst(ser.serialize_type(*r)),
            TypeDesc::Tvariant(row_desc) => {
                PortableTypeDesc::Tvariant(ser.serialize_row_desc(&ser.ctx.row_desc(row_desc)))
            }
            TypeDesc::Tunivar(name) => PortableTypeDesc::Tunivar(*name),
            TypeDesc::Tpoly { body, vars } => PortableTypeDesc::Tpoly {
                body: ser.serialize_type(*body),
                vars: ser.ctx.type_list(vars).iter().map(|t| ser.serialize_type(t)).collect(),
            },
            TypeDesc::Tpackage { path, lids, args } => PortableTypeDesc::Tpackage {
                path: *path,
                lids: ser
                    .ctx
                    .package_lids(lids)
                    .iter()
                    .map(|lid| ser.serialize_longident(lid))
                    .collect(),
                args: ser.ctx.type_list(args).iter().map(|t| ser.serialize_type(t)).collect(),
            },
        }
    }

}

#[path = "signature_builder.rs"]
mod signature_builder;

struct TypeGraphSerializer<'a, 'f, S: SignatureSink = PortableSink> {
    ctx: &'a TypeContext,
    arena: Option<&'a ParseArena>,
    sink: S,
    #[cfg(test)]
    visits: usize,
    cache: crate::types::type_marks::Pooled<crate::types::type_marks::TypeNodeTable<TypeExprRef>>,
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

impl<'a, 'f, S: SignatureSink> TypeGraphSerializer<'a, 'f, S> {
    fn new(
        ctx: &'a TypeContext,
        arena: Option<&'a ParseArena>,
        file_names: &'f mut PortableFileNames,
    ) -> Self {
        TypeGraphSerializer {
            ctx,
            arena,
            sink: S::default(),
            #[cfg(test)]
            visits: 0,
            cache: crate::types::type_marks::ref_table(),
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
        if let Some(mapped) = self.cache.get(r) {
            return mapped.index();
        }

        // Allocate placeholder first to handle recursive types.
        let idx = self.sink.reserve();
        self.cache.insert(r, TypeExprRef::from_usize(idx));

        #[cfg(test)]
        { self.visits += 1; }
        let desc_snapshot = self.ctx.get_desc(r);
        let level = self.ctx.get_level(r);
        let portable_desc = self.serialize_desc(&desc_snapshot);
        self.sink.write(idx, portable_desc, level);
        idx
    }

    fn serialize_desc(&mut self, desc: &TypeDesc) -> S::Desc {
        S::describe(self, desc)
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
                .map(|(label, field)| (label.clone(), self.serialize_row_field(field)))
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

/// When the scheduler needs a live shared graph for this signature.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SignaturePublicationMode {
    /// A dependent in this build (including an interface's implementation).
    Eager,
    /// No dependent in this build; storage may run as soon as lowering finishes.
    /// Hashing and storage retain a graph without installing it in the pool.
    OnDemand,
}

/// Publish directly from the checker. The portable oracle is check-only;
/// ordinary storage reconstructs it from the frozen graph after release.
pub(crate) fn publish_signature(
    ps: &PersStruct, ctx: &TypeContext, arena: Option<&ParseArena>,
    mode: SignaturePublicationMode, checked: bool,
) -> (Arc<PortablePersStruct>, Option<super::signature_check::Comparison>) {
    let stamps = PublicationStamps::new(ctx);
    let Some((graph, raw)) = signature_builder::build(ps, ctx, arena, &stamps) else {
        let portable = serialize_for_publication(ps, ctx, arena);
        return if checked {
            let (pps, comparison) = publish_pers_struct_checked(portable, ctx, mode);
            (pps, Some(comparison))
        } else { (publish_pers_struct(portable, ctx, mode), None) };
    };
    let reader = graph.reader();
    let fingerprint = signature_fingerprint(&reader, &graph.signature);
    let hashes = super::item_deps::item_declaration_hashes(&reader, &graph.signature);
    let comparison = checked.then(|| {
        use super::signature_check::{Comparison, Outcome};
        let oracle = serialize_pers_struct_inner(ps, ctx, arena, true, &stamps);
        let decoded = oracle.decoded.lock().unwrap();
        let portable = decoded.as_ref().unwrap().0.portable();
        let oracle_hashes = super::item_deps::item_declaration_hashes(&HashGraph::of(&portable.type_graph), &portable.ps_sig);
        let items = |xs: &[(super::item_deps::Kind, crate::name::Name, u64)]| {
            xs.iter().map(|(kind, name, hash)| ((*kind, *name), *hash)).collect::<Vec<_>>()
        };
        Comparison {
            shared_graph: "published", carried: graph.graph.carried.needed(),
            outcomes: [
                Outcome::fingerprint(oracle.fingerprint, fingerprint),
                Outcome::item_hashes(&items(&oracle_hashes), &items(&hashes)),
                Outcome::bytes(&crate::binser::to_vec(portable.as_ref()).unwrap(), &graph.storage_bytes_for_check()),
            ],
        }
    });
    let pps = Arc::new(PortablePersStruct {
        ps_name: ps.ps_name.clone(), ps_filename: ps.ps_filename.clone(),
        ps_deprecated: ps.ps_deprecated.clone(), ps_crcs: ps.ps_crcs.clone(),
        shareable: true, fingerprint, summary: Default::default(), shared_item_hashes: Some(hashes),
        decoded: std::sync::Mutex::new(Some((PublishedSignature::Shared(graph), raw))),
        encoded: Default::default(), published_generation: Some(crate::types::thread_store::build_generation()),
        publication_counter_id: crate::perf_counters::signature_publication_id(),
    });
    pps.record_access(false);
    (pps, comparison)
}

/// Build the shared graph before publishing its address-keyed registry entry.
/// Leaf units also need a graph: their fingerprint may not use the portable
/// form. Only a non-shareable signature or a full pool takes the old path.
fn prepare_publication(
    mut pps: PortablePersStruct,
    ctx: &TypeContext,
    check: bool,
) -> (Arc<PortablePersStruct>, Option<(Arc<PersStruct>, u32)>) {
    use super::shared_reader::FrozenGraph;
    pps.published_generation = Some(crate::types::thread_store::build_generation());
    pps.publication_counter_id = crate::perf_counters::signature_publication_id();
    let store = ctx.thread_store();
    let pool = store.shared_pool();
    let (shared, fingerprint, hashes) = {
        let decoded = pps.decoded.lock().unwrap();
        let source = &decoded.as_ref().expect("new publication").0;
        let sig = source.portable();
        let shared = if pps.shareable || check {
            shared_pers_struct_at(&pps, &sig, pool)
        } else {
            None
        };
        let (fingerprint, hashes) = match &shared {
            Some((ps, base)) => {
                let pages = pool.pages();
                let frozen = FrozenGraph::new(
                    pool, crate::types::shared_store::graph_at(&pages, *base),
                );
                (
                    signature_fingerprint(&frozen, &ps.ps_sig),
                    Some(super::item_deps::item_declaration_hashes(&frozen, &ps.ps_sig)),
                )
            }
            None => (signature_fingerprint(&HashGraph::of(&sig.type_graph), &sig.ps_sig), None),
        };
        (shared, fingerprint, hashes)
    };
    pps.fingerprint = fingerprint;
    pps.shared_item_hashes = hashes;
    let pps = Arc::new(pps);
    pps.record_access(false);
    if pps.shareable && let Some((ps, _)) = &shared {
        let cached = pool.pers_struct(&pps, || Some(ps.clone()))
            .expect("a prepared shared graph is registered once");
        store.insert_pers_struct(pps.clone(), cached);
    }
    (pps, shared)
}

/// Prepare the address-keyed pool and worker map before signature release.
pub fn publish_pers_struct(
    pps: PortablePersStruct,
    ctx: &TypeContext,
    _mode: SignaturePublicationMode,
) -> Arc<PortablePersStruct> {
    prepare_publication(pps, ctx, false).0
}

/// [`publish_pers_struct`] in signature check mode
/// (`RESCRIPT_SIGNATURE_CHECK`): also compare what the frozen shared graph
/// says of the signature with what its portable form says
/// (`docs/CHECKER_REDESIGN.md`, H.1.7 invariant 5): the fingerprint, every
/// item digest, and the encoded bytes.
///
/// Every unit is compared against a shared graph. A shareable signature is
/// published whatever `mode` says, so a unit without a dependent in this
/// build is covered; a signature that is not shareable is internalized into
/// a graph of the pool that no reader is given. Only a full pool leaves a
/// unit without a comparison.
pub fn publish_pers_struct_checked(
    pps: PortablePersStruct,
    ctx: &TypeContext,
    _mode: SignaturePublicationMode,
) -> (Arc<PortablePersStruct>, super::signature_check::Comparison) {
    use super::shared_reader::{FrozenGraph, portable_signature};
    use super::signature_check::{Comparison, Outcome};
    let (pps, shared) = prepare_publication(pps, ctx, true);
    let store = ctx.thread_store();
    let pool = store.shared_pool();
    let decoded = pps.decoded.lock().unwrap();
    let portable = decoded.as_ref().expect("new publication").0.portable();
    let shared_graph = if pps.shareable { "published" } else { "forced: not shareable" };
    let shared = shared.map(|(ps, base)| (ps.ps_sig.clone(), base));
    let comparison = match shared {
        None => Comparison::not_applicable(shared_graph, "the shared pool is full"),
        Some((sig, base)) => {
            let pages = pool.pages();
            let frozen = FrozenGraph::new(pool, crate::types::shared_store::graph_at(&pages, base));
            let items = |hashes: Vec<(super::item_deps::Kind, crate::name::Name, u64)>| {
                hashes
                    .into_iter()
                    .map(|(kind, name, hash)| ((kind, name), hash))
                    .collect::<Vec<_>>()
            };
            let encode = |sig: &PortableSignature| {
                crate::binser::to_vec(sig).expect("encoding to memory cannot fail")
            };
            Comparison {
                shared_graph,
                carried: crate::types::shared_store::graph_at(&pages, base).carried.needed(),
                outcomes: [
                    Outcome::fingerprint(
                        signature_fingerprint(&HashGraph::of(&portable.type_graph), &portable.ps_sig),
                        pps.fingerprint,
                    ),
                    Outcome::item_hashes(
                        &items(super::item_deps::item_declaration_hashes(
                            &HashGraph::of(&portable.type_graph),
                            &portable.ps_sig,
                        )),
                        &items(pps.shared_item_hashes.as_ref().expect("shared publication hashes").clone()),
                    ),
                    Outcome::bytes(
                        &encode(&portable),
                        &encode(&portable_signature(&frozen, &sig)),
                    ),
                ],
            }
        }
    };
    drop(decoded);
    (pps, comparison)
}

fn shared_pers_struct(
    pps: &PortablePersStruct,
    portable: &PortableSignature,
    pool: &crate::types::shared_store::SharedTypePool,
) -> Option<Arc<PersStruct>> {
    Some(shared_pers_struct_at(pps, portable, pool)?.0)
}

/// [`shared_pers_struct`], with the base index of the graph it published.
fn shared_pers_struct_at(
    pps: &PortablePersStruct,
    portable: &PortableSignature,
    pool: &crate::types::shared_store::SharedTypePool,
) -> Option<(Arc<PersStruct>, u32)> {
    let intern = |name: &str| pool.intern_longident_name(name);
    let files = FileRemap::new(&portable.cmi_longident_names, &intern);
    let (sig, base) = internalize_signature_into_shared(
        &portable.ps_sig,
        &portable.type_graph,
        &portable.locations,
        &files,
        pool,
        Some(&pps.ps_filename),
    )?;
    let ps = PersStruct {
        ps_name: pps.ps_name.clone(),
        ps_sig: Arc::new(sig),
        ps_filename: pps.ps_filename.clone(),
        ps_deprecated: pps.ps_deprecated.clone(),
        ps_crcs: pps.ps_crcs.clone(),
        ps_alias_rewrites: Default::default(),
    };
    Some((Arc::new(ps), base))
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
        pps.record_access(true);
        return ps;
    }

    let shareable = pps.shareable;
    if shareable {
        // Internalize once per build for every worker; the worker store
        // keeps the result so later units on this worker skip the pool map.
        let pool = store.shared_pool();
        let shared = pool.pers_struct(&pps, || {
            let mut decoded = pps.decoded.lock().unwrap();
            if let Some((PublishedSignature::Shared(graph), _)) = decoded.as_mut() {
                if !std::ptr::eq(graph.names.as_ref(), pool.names_ref()) {
                    // A source-built runtime or watch registry can outlive its
                    // pool generation. Import from its frozen graph, never from
                    // addresses or name indices owned by the previous pool.
                    return shared_pers_struct(&pps, &graph.portable(), pool);
                }
                if graph.graph.is_detached() {
                    *graph = signature_builder::promote(graph, &pps.ps_filename, pool)?;
                }
                return Some(Arc::new(PersStruct {
                    ps_name: pps.ps_name.clone(), ps_sig: graph.signature.clone(),
                    ps_filename: pps.ps_filename.clone(),
                    ps_deprecated: pps.ps_deprecated.clone(), ps_crcs: pps.ps_crcs.clone(),
                    ps_alias_rewrites: Default::default(),
                }));
            }
            drop(decoded);
            let portable = pps.signature();
            shared_pers_struct(&pps, &portable, pool)
        });
        if let Some(ps) = shared {
            pps.record_access(true);
            store.insert_pers_struct(pps, ps.clone());
            return ps;
        }
    }
    let sig = if shareable {
        let portable = pps.signature();
        let intern = |name: &str| store.intern_longident_name(name);
        let files = FileRemap::new(&portable.cmi_longident_names, &intern);
        let map = |file| files.map(file);
        let locs = store.import_portable_decl_locs(
            &portable.locations,
            &map,
            Some(interface_namespace(&pps.ps_filename)),
        );
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
        ps_alias_rewrites: Default::default(),
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
    let mut shapes = crate::types::variant_runtime::ShapeImport::with_namespace(
        &locs.scopes,
        locs.namespace,
    );
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
    remap_signature_refs(
        &mut sig,
        &IndexedRefs {
            types: &remap,
            layouts: &layout_remap,
        },
    );
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

/// The same dependency import has the same namespace in either persistent
/// storage tier. It is independent of which worker first requests it.
fn interface_namespace(unit: &str) -> u64 {
    let mut hash = std::collections::hash_map::DefaultHasher::new();
    ("persistent interface", unit).hash(&mut hash);
    hash.finish()
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
    unit: Option<&str>,
) -> Option<(Signature, u32)> {
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
        let namespace = unit.map(interface_namespace);
        scopes = match namespace {
            Some(namespace) => table.remap_for_import_with(&map, |scope| {
                crate::types::variant_runtime::identity_in_namespace(namespace, scope)
            }),
            None => table.remap_for_import(&map),
        };
        let mut shapes = crate::types::variant_runtime::ShapeImport::with_namespace(
            &scopes,
            namespace,
        );
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
        let mut carried = super::shared_reader::Carried {
            file_names: files.original.to_vec(),
            ..Default::default()
        };
        carried.record_import(graph, &scopes, shapes);
        crate::types::shared_store::SharedGraphParts {
            nodes,
            payloads: sink.payloads.into_inner(),
            layouts,
            locations: table,
            carried,
        }
    })?;
    let layout_remap: Vec<_> = (0..graph.variant_layouts.len())
        .map(|i| crate::types::VariantLayoutRef::from_shared_index(base + i as u32))
        .collect();
    remap_signature_refs(
        &mut sig,
        &IndexedRefs {
            types: &remap,
            layouts: &layout_remap,
        },
    );
    import_signature_locations(&mut sig, &shared_decl_locs(base, &map));
    Some((sig, base))
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
        namespace: None,
    }
}

pub(crate) fn internalize_raw_signature(
    pps: &PortablePersStruct,
    ctx: &TypeContext,
) -> Option<Signature> {
    let raw = pps.raw_signature()?;
    let names = &raw.cmi_longident_names;
    let intern = |name: &str| ctx.intern_cmi_longident_name(name);
    let files = FileRemap::new(names, &intern);
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
    original: &'a [(u32, String)],
    names: AHashMap<u32, &'a str>,
    fresh: std::cell::RefCell<AHashMap<u32, crate::intern::StrIdx>>,
    intern: &'a dyn Fn(&str) -> crate::intern::StrIdx,
}

impl<'a> FileRemap<'a> {
    fn new(names: &'a [(u32, String)], intern: &'a dyn Fn(&str) -> crate::intern::StrIdx) -> Self {
        FileRemap {
            original: names,
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

    let mut shapes = crate::types::variant_runtime::ShapeImport::with_namespace(
        &locs.scopes,
        locs.namespace,
    );
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
    remap_signature_refs(
        &mut sig,
        &IndexedRefs {
            types: &remap,
            layouts: &layout_remap,
        },
    );
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
            let row = internalize_row_desc(prd, remap, ctx);
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
                (label.clone(), internalize_row_field(field, remap, ctx))
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

/// How the type and variant layout references of a signature are renamed.
pub(crate) trait SignatureRefMap {
    /// The new name of a type reference.
    fn ty(&self, r: TypeExprRef) -> TypeExprRef;
    /// The new name of a variant layout reference.
    fn layout(&self, r: crate::types::VariantLayoutRef) -> crate::types::VariantLayoutRef;
}

/// Portable index `i` becomes entry `i` of each table.
struct IndexedRefs<'a> {
    types: &'a [TypeExprRef],
    layouts: &'a [crate::types::VariantLayoutRef],
}

impl SignatureRefMap for IndexedRefs<'_> {
    #[inline]
    fn ty(&self, r: TypeExprRef) -> TypeExprRef {
        self.types[r.index()]
    }

    #[inline]
    fn layout(&self, r: crate::types::VariantLayoutRef) -> crate::types::VariantLayoutRef {
        self.layouts[r.0 as usize]
    }
}

pub(crate) fn remap_signature_refs(sig: &mut Signature, map: &impl SignatureRefMap) {
    for item in sig.iter_mut() {
        remap_sig_item_refs(item, map);
    }
}

fn remap_sig_item_refs(item: &mut SignatureItem, map: &impl SignatureRefMap) {
    match item {
        SignatureItem::SigValue(_, vd) => remap_value_desc_refs(vd, map),
        SignatureItem::SigType(_, td, _) => remap_type_decl_refs(std::sync::Arc::make_mut(td), map),
        SignatureItem::SigTypext(_, ec, _) => remap_ext_ctor_refs(ec, map),
        SignatureItem::SigModule(_, md, _) => remap_module_decl_refs(md, map),
        SignatureItem::SigModtype(_, mtd) => remap_modtype_decl_refs(mtd, map),
        SignatureItem::SigClass | SignatureItem::SigClassType => {}
    }
}

fn remap_value_desc_refs(vd: &mut ValueDescription, map: &impl SignatureRefMap) {
    vd.val_type = map.ty(vd.val_type);
}

fn remap_type_decl_refs(td: &mut TypeDeclaration, map: &impl SignatureRefMap) {
    if let TypeKind::TypeVariant(_, layout_ref) = &mut td.type_kind {
        *layout_ref = map.layout(*layout_ref);
    }
    for p in td.type_params.iter_mut() {
        *p = map.ty(*p);
    }
    if let Some(ref mut m) = td.type_manifest {
        *m = map.ty(*m);
    }
    match &mut td.type_kind {
        TypeKind::TypeAbstract | TypeKind::TypeOpen => {}
        TypeKind::TypeRecord(labels, _) => {
            for label in labels.iter_mut() {
                remap_label_decl_refs(label, map);
            }
        }
        TypeKind::TypeVariant(ctors, _) => {
            for ctor in ctors.iter_mut() {
                remap_ctor_decl_refs(ctor, map);
            }
        }
    }
    for inlined in td.type_inlined_types.iter_mut() {
        match inlined {
            crate::types::decl::TypeInlinedType::Record { labels, .. } => {
                for label in labels.iter_mut() {
                    remap_label_decl_refs(label, map);
                }
            }
        }
    }
}

fn remap_label_decl_refs(ld: &mut LabelDeclaration, map: &impl SignatureRefMap) {
    ld.ld_type = map.ty(ld.ld_type);
}

fn remap_ctor_decl_refs(cd: &mut ConstructorDeclaration, map: &impl SignatureRefMap) {
    match &mut cd.cd_args {
        ConstructorArguments::CstrTuple(types) => {
            for t in types.iter_mut() {
                *t = map.ty(*t);
            }
        }
        ConstructorArguments::CstrRecord(labels) => {
            for label in labels.iter_mut() {
                remap_label_decl_refs(label, map);
            }
        }
    }
    if let Some(ref mut res) = cd.cd_res {
        *res = map.ty(*res);
    }
}

fn remap_ext_ctor_refs(ec: &mut ExtensionConstructor, map: &impl SignatureRefMap) {
    for p in ec.ext_type_params.iter_mut() {
        *p = map.ty(*p);
    }
    match &mut ec.ext_args {
        ConstructorArguments::CstrTuple(types) => {
            for t in types.iter_mut() {
                *t = map.ty(*t);
            }
        }
        ConstructorArguments::CstrRecord(labels) => {
            for label in labels.iter_mut() {
                remap_label_decl_refs(label, map);
            }
        }
    }
    if let Some(ref mut ret) = ec.ext_ret_type {
        *ret = map.ty(*ret);
    }
}

fn remap_module_decl_refs(md: &mut ModuleDeclaration, map: &impl SignatureRefMap) {
    remap_module_type_refs(&mut md.md_type, map);
}

fn remap_modtype_decl_refs(mtd: &mut ModtypeDeclaration, map: &impl SignatureRefMap) {
    if let Some(ref mut mt) = mtd.mtd_type {
        remap_module_type_refs(mt, map);
    }
}

fn remap_module_type_refs(mt: &mut ModuleType, map: &impl SignatureRefMap) {
    match mt {
        ModuleType::MtySignature(sig) => {
            remap_signature_refs(crate::types::decl::signature_mut(sig), map)
        }
        ModuleType::MtyFunctor {
            param_type, result, ..
        } => {
            if let Some(pt) = param_type.as_mut() {
                remap_module_type_refs(pt, map);
            }
            remap_module_type_refs(result, map);
        }
        ModuleType::MtyIdent(_) | ModuleType::MtyAlias(_, _) => {}
    }
}

#[cfg(test)]
mod identity_tests {
    use super::*;
    use crate::context::IdGenerator;

    #[test]
    fn publication_state_keeps_portable_fallback_out_of_line() {
        assert_eq!(std::mem::size_of::<PublishedSignature>(), 24);
    }

    #[test]
    fn store_stamps_are_remapped_everywhere_a_signature_holds_them() {
        use crate::ident::{Ident, IdentFlags, STORE_STAMP_BASE};
        use crate::types::decl::{RecStatus, signature_mut};
        let id = Ident::new("bound", STORE_STAMP_BASE + 7, IdentFlags::NONE);
        let path = Path::papply(Path::pident(id), Path::pdot_pos(Path::pident(id), "t", 2));
        let mut sig = vec![SignatureItem::SigModule(
            id,
            ModuleDeclaration {
                md_type: ModuleType::MtyFunctor {
                    param: id,
                    param_type: Some(Box::new(ModuleType::MtyIdent(path))),
                    result: Box::new(ModuleType::MtyAlias(
                        crate::types::decl::AliasPresence::MtaPresent,
                        Arc::new(path),
                    )),
                },
                md_attributes: vec![],
                md_loc: DeclLoc::none(),
                md_path: Some(path),
            },
            RecStatus::TrecNot,
        )];
        // Include a nested signature as well as a functor's binder and paths.
        let mut nested = Arc::new(sig.clone());
        signature_mut(&mut nested).extend(sig.clone());
        sig.push(SignatureItem::SigModtype(
            id,
            ModtypeDeclaration {
                mtd_type: Some(ModuleType::MtySignature(nested)),
                mtd_attributes: vec![],
                mtd_loc: DeclLoc::none(),
            },
        ));
        let mut graph = PortableTypeGraph {
            entries: vec![PortableTypeEntry {
                desc: PortableTypeDesc::Tconstr { path, args: vec![] },
                level: GENERIC_LEVEL,
            }],
            variant_layouts: vec![],
            mutabilities: vec![],
        };
        let asked = std::cell::Cell::new(0);
        remap_saved_stamps(&mut sig, &mut graph, &|stamp| {
            assert_eq!(stamp, STORE_STAMP_BASE + 7);
            asked.set(asked.get() + 1);
            Some(42)
        });
        assert!(asked.get() > 0);
        // No identifier of the store range is left, in binders or in paths:
        // the encoding mentions the mapped stamp only, and a second pass
        // (the common publication path) never asks for a stamp.
        let mapped = Ident::new("bound", 42, IdentFlags::NONE);
        let debug = format!("{sig:?}{graph:?}");
        assert!(!debug.contains(&(STORE_STAMP_BASE + 7).to_string()), "{debug}");
        let expected = crate::binser::to_vec(&(&sig, &graph)).unwrap();
        remap_saved_stamps(&mut sig, &mut graph, &|_| {
            panic!("ordinary binder requested a store stamp")
        });
        assert_eq!(crate::binser::to_vec(&(&sig, &graph)).unwrap(), expected);
        assert!(matches!(&sig[0], SignatureItem::SigModule(id, ..) if id.same(&mapped)));
    }

    #[test]
    fn dependency_raw_read_does_not_encode_during_publication() {
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let portable = serialize_pers_struct(
            &PersStruct {
                ps_name: "Provider".into(),
                ps_sig: Arc::new(vec![]),
                ps_filename: "Provider.res".into(),
                ps_deprecated: None,
                ps_crcs: vec![],
                ps_alias_rewrites: Default::default(),
            },
            &ctx,
            None,
        );
        {
            let mut decoded = portable.decoded.lock().unwrap();
            let (source, raw) = decoded.as_mut().unwrap();
            let sig = source.portable();
            *raw = Some(PortableRawSignature {
                raw_ps_sig: sig.ps_sig.clone(),
                cmi_longident_names: sig.cmi_longident_names.clone(),
                raw_type_graph: sig.type_graph.clone(),
                raw_locations: sig.locations.clone(),
            });
        }
        assert!(portable.has_raw_signature());
        assert!(portable.encoded.get().is_none());
        // The provider has been released but no storage reader has encoded it.
        // A dependent's GenType alias lookup is its first raw-signature reader.
        let before = {
            let _dependent = crate::perf_counters::SignaturePublication::begin();
            crate::binser::to_vec(&portable.raw_signature().unwrap()).unwrap()
        };
        assert!(portable.encoded.get().is_none());
        assert!(portable.summary.get().is_none());
        portable.prepare_for_storage();
        let after = {
            let _dependent = crate::perf_counters::SignaturePublication::begin();
            crate::binser::to_vec(&portable.raw_signature().unwrap()).unwrap()
        };
        assert_eq!(before, after);
    }

    #[test]
    fn direct_publication_preserves_first_mention_store_binder_order() {
        fn source(ctx: &TypeContext) -> PersStruct {
            let id = |name, n| crate::ident::Ident::new(
                name, crate::ident::STORE_STAMP_BASE + n, crate::ident::IdentFlags::NONE,
            );
            let nil = ctx.new_type(TypeDesc::Tnil);
            let row = ctx.new_row_desc(RowDesc {
                row_fields: Default::default(), row_more: nil, row_closed: true, row_fixed: true,
                row_name: Some((Path::pident(id("row", 8)), vec![])),
            });
            let variant = ctx.new_type(TypeDesc::Tvariant(row));
            let constr = ctx.new_type(TypeDesc::Tconstr {
                path: Path::pident(id("t", 9)), args: ctx.new_type_list(&[]),
                abbrev: AbbrevMemoRef::nil(),
            });
            let typ = ctx.new_type(TypeDesc::Ttuple(ctx.new_type_list(&[variant, constr])));
            let sig = Arc::new(vec![SignatureItem::SigValue(id("value", 7), ValueDescription {
                val_type: typ, val_kind: ValueKind::ValReg,
                val_loc: crate::types::DeclLoc::none(), val_attributes: Default::default(), val_path: None,
            })]);
            ctx.register_raw_module_sig("Binders", sig.clone());
            PersStruct {
                ps_name: "Binders".into(), ps_filename: "Binders.res".into(), ps_sig: sig,
                ps_deprecated: None, ps_crcs: vec![], ps_alias_rewrites: Default::default(),
            }
        }
        let reference = TypeContext::new(Arc::new(IdGenerator::new()));
        let expected = serialize_pers_struct(&source(&reference), &reference, None);
        let direct = TypeContext::new(Arc::new(IdGenerator::new()));
        let (actual, comparison) = publish_signature(
            &source(&direct), &direct, None, SignaturePublicationMode::OnDemand, true,
        );
        assert!(comparison.unwrap().outcomes.iter().all(|outcome|
            matches!(outcome, super::super::signature_check::Outcome::Equal)));
        assert_eq!(crate::binser::to_vec(&expected).unwrap(), crate::binser::to_vec(actual.as_ref()).unwrap());
        assert_eq!(reference.published_binder_stamp(), direct.published_binder_stamp(),
            "the oracle must not consume additional publication stamps");
    }

    #[test]
    fn direct_publication_defers_pool_installation_even_after_storage() {
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let leaf = ctx.new_var(None);
        let typ = ctx.new_type(TypeDesc::Ttuple(ctx.new_type_list(&[leaf, leaf])));
        let ps = PersStruct {
            ps_name: "Deferred".into(),
            ps_filename: "Deferred.res".into(),
            ps_sig: Arc::new(vec![SignatureItem::SigValue(
                crate::ident::Ident::create_persistent("value"),
                ValueDescription {
                    val_type: typ,
                    val_kind: ValueKind::ValReg,
                    val_loc: crate::types::DeclLoc::none(),
                    val_attributes: Default::default(),
                    val_path: None,
                },
            )]),
            ps_deprecated: None,
            ps_crcs: vec![],
            ps_alias_rewrites: Default::default(),
        };
        let oracle = serialize_pers_struct(&ps, &ctx, None).signature();
        let published = {
            let _release = crate::perf_counters::SignaturePublication::begin();
            publish_signature(&ps, &ctx, None, SignaturePublicationMode::Eager, true).0
        };
        assert!(ctx.thread_store().pers_struct(&published).is_none());
        let leaf = publish_signature(&ps, &ctx, None, SignaturePublicationMode::OnDemand, false).0;
        drop(ps);
        drop(ctx);
        // Ordinary storage may precede an importer. The scheduler's explicit
        // leaf path instead releases the graph because no importer is waiting.
        published.encoded();
        leaf.prepare_for_storage();
        assert!(!leaf.has_decoded_signatures());
        assert_eq!(crate::binser::to_vec(&leaf.signature()).unwrap(), crate::binser::to_vec(&oracle).unwrap());
        assert_eq!(
            crate::binser::to_vec(&published.signature()).unwrap(),
            crate::binser::to_vec(&oracle).unwrap()
        );
        let detached = || {
            let decoded = published.decoded.lock().unwrap();
            let Some((PublishedSignature::Shared(graph), _)) = decoded.as_ref() else {
                panic!("frozen graph")
            };
            graph.graph.is_detached()
        };
        assert!(detached());
        let reader = TypeContext::new(Arc::new(IdGenerator::new()));
        let first = internalize_pers_struct(published.clone(), &reader);
        assert!(!detached());
        assert!(Arc::ptr_eq(
            &first,
            &internalize_pers_struct(published.clone(), &reader)
        ));
        let decoded = published.decoded.lock().unwrap();
        let Some((PublishedSignature::Shared(graph), _)) = decoded.as_ref() else {
            panic!("frozen graph")
        };
        // Both the detached and pool-installed borrowed encodings have the
        // PortableSignature wire format, including repeated references.
        assert_eq!(
            crate::binser::to_vec(&graph.encode().decode()).unwrap(),
            crate::binser::to_vec(&oracle).unwrap()
        );
    }

    #[test]
    fn publication_fills_the_pool_under_the_registry_arc() {
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let mut portable = serialize_pers_struct(
            &PersStruct {
                ps_name: "Published".into(),
                ps_sig: Arc::new(vec![]),
                ps_filename: "Published.res".into(),
                ps_deprecated: None,
                ps_crcs: vec![],
                ps_alias_rewrites: Default::default(),
            },
            &ctx,
            None,
        );
        let expected_fingerprint = portable.fingerprint;
        portable.fingerprint = expected_fingerprint.wrapping_add(1);
        let published = {
            let _guard = crate::perf_counters::SignaturePublication::begin();
            publish_pers_struct(portable, &ctx, SignaturePublicationMode::Eager)
        };
        assert_eq!(published.fingerprint, expected_fingerprint);
        assert!(published.shared_item_hashes.is_some());
        assert!(published.has_decoded_signatures());
        let pool = ctx.thread_store().shared_pool();
        let shared = pool
            .pers_struct(&published.clone(), || {
                panic!("dependent rebuilt the published graph")
            })
            .unwrap();
        assert!(Arc::ptr_eq(
            &shared,
            &ctx.thread_store().pers_struct(&published).unwrap()
        ));
        assert!(published.has_decoded_signatures());
    }

    #[test]
    fn leaf_publication_hashes_shared_nodes_and_encodes_later() {
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let portable = serialize_pers_struct(
            &PersStruct {
                ps_name: "Leaf".into(),
                ps_sig: Arc::new(vec![]),
                ps_filename: "Leaf.res".into(),
                ps_deprecated: None,
                ps_crcs: vec![],
                ps_alias_rewrites: Default::default(),
            },
            &ctx,
            None,
        );
        let published = {
            let _guard = crate::perf_counters::SignaturePublication::begin();
            publish_pers_struct(portable, &ctx, SignaturePublicationMode::OnDemand)
        };
        assert!(published.has_decoded_signatures());
        assert!(ctx.thread_store().pers_struct(&published).is_some());
        published.prepare_for_storage();
        assert!(!published.has_decoded_signatures());

        let built = std::cell::Cell::new(false);
        let pool = ctx.thread_store().shared_pool();
        let shared = pool
            .pers_struct(&published, || {
                built.set(true);
                shared_pers_struct(&published, &published.signature(), pool)
            })
            .unwrap();
        assert!(!built.get(), "leaf rebuilt the graph used for hashing");
        let loaded = internalize_pers_struct(published.clone(), &ctx);
        assert!(Arc::ptr_eq(&shared, &loaded));
        assert!(Arc::ptr_eq(
            &loaded,
            &ctx.thread_store().pers_struct(&published).unwrap()
        ));
    }

    #[test]
    fn named_units_allocate_identities_independently_of_other_contexts() {
        let allocate = |unit: &str| {
            let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
            ctx.set_location_namespace(unit);
            let scopes = [ctx.fresh_location_scope(), ctx.fresh_location_scope()];
            let shapes = [ctx.fresh_shape_allocation(), ctx.fresh_shape_allocation()];
            assert_ne!(scopes[0], scopes[1]);
            assert_ne!(shapes[0], shapes[1]);
            (scopes, shapes)
        };
        let first = allocate("Unit.res");
        let other = allocate("Other.res");
        assert_ne!(first, other);
        assert_ne!(first, allocate("Unit.resi"));
        assert_eq!(first, allocate("Unit.res"));
    }

    #[test]
    fn shared_hash_walk_is_linear_in_chains_and_shared_children() {
        use super::super::graph_hash::GraphWalk;
        use super::super::shared_reader::FrozenGraph;
        const N: usize = 10_000;
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let pool = ctx.thread_store().shared_pool();
        for shared_child in [false, true] {
            let mut entries: Vec<_> = (0..N).map(|i| PortableTypeEntry {
                desc: if shared_child {
                    if i == 0 { PortableTypeDesc::Tnil } else { PortableTypeDesc::Ttuple(vec![0]) }
                } else if i + 1 == N {
                    PortableTypeDesc::Tnil
                } else {
                    PortableTypeDesc::Ttuple(vec![i + 1])
                },
                level: GENERIC_LEVEL,
            }).collect();
            let root = if shared_child {
                entries.push(PortableTypeEntry {
                    desc: PortableTypeDesc::Ttuple((1..N).collect()), level: GENERIC_LEVEL,
                });
                N
            } else { 0 };
            let graph = PortableTypeGraph { entries, variant_layouts: vec![], mutabilities: vec![] };
            let intern = |name: &str| pool.intern_longident_name(name);
            let files = FileRemap::new(&[], &intern);
            let (_, base) = internalize_signature_into_shared(
                &vec![], &graph, &DeclLocTable::default(), &files, pool, Some("Steps.res"),
            ).unwrap();
            let pages = pool.pages();
            let frozen = FrozenGraph::new(pool, crate::types::shared_store::graph_at(&pages, base));
            let mut walk = GraphWalk::new(&frozen);
            let mut h = std::collections::hash_map::DefaultHasher::new();
            walk.type_ref(&mut h, crate::types::shared_store::shared_ref(base, root));
            assert_eq!(walk.records(), graph.entries.len() as u64);
            walk.type_ref(&mut h, crate::types::shared_store::shared_ref(base, root));
            assert_eq!(walk.records(), graph.entries.len() as u64);
        }
    }

    #[test]
    fn a_frozen_graph_reads_back_without_portable_side_inputs() {
        use super::super::shared_reader::{FrozenGraph, portable_signature};
        use crate::types::asttypes::MutableFlag;
        let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
        let pool = ctx.thread_store().shared_pool();
        let entry = |desc, level| PortableTypeEntry { desc, level };
        let field = |name: &str, mutability, rest| PortableTypeDesc::Tfield {
            name: name.into(),
            mutability,
            typ: 1,
            rest,
        };
        // A link below the generic level, and three object fields of which
        // the first and the last share a mutability cell.
        let portable = PortableSignature {
            ps_sig: vec![],
            // Includes a file used only by the raw signature. Preserve its key
            // and order even though no location in this graph references it.
            cmi_longident_names: vec![(17, "Raw.res".into()), (4, "Unit.res".into())],
            type_graph: PortableTypeGraph {
                entries: vec![
                    entry(PortableTypeDesc::Tlink(1), 3),
                    entry(PortableTypeDesc::Tvar(Some("a".into())), GENERIC_LEVEL),
                    entry(field("x", 0, 3), GENERIC_LEVEL),
                    entry(field("y", 1, 4), GENERIC_LEVEL),
                    entry(field("z", 0, 5), GENERIC_LEVEL),
                    entry(PortableTypeDesc::Tnil, GENERIC_LEVEL),
                ],
                variant_layouts: vec![],
                mutabilities: vec![MutableFlag::Mutable, MutableFlag::Immutable],
            },
            locations: Default::default(),
        };
        let intern = |name: &str| pool.intern_longident_name(name);
        let files = FileRemap::new(&portable.cmi_longident_names, &intern);
        let (sig, base) = internalize_signature_into_shared(
            &portable.ps_sig,
            &portable.type_graph,
            &portable.locations,
            &files,
            pool,
            Some("Unit.res"),
        )
        .unwrap();
        let pages = pool.pages();
        let frozen = FrozenGraph::new(pool, crate::types::shared_store::graph_at(&pages, base));
        let bytes = |sig: &PortableSignature| crate::binser::to_vec(sig).unwrap();
        assert_eq!(
            crate::types::shared_store::graph_at(&pages, base).carried.needed(),
            ["file names", "link levels"]
        );
        assert_eq!(
            bytes(&portable_signature(&frozen, &sig)),
            bytes(&portable)
        );
        // Type readers still see the normalized link level.
        assert_eq!(
            crate::types::shared_store::graph_at(&pages, base).nodes()[0].level,
            GENERIC_LEVEL
        );
        // Both forms hash alike.
        assert_eq!(
            signature_fingerprint(&frozen, &sig),
            signature_fingerprint(&HashGraph::of(&portable.type_graph), &portable.ps_sig)
        );
        let expected = bytes(&portable);
        drop(files);
        drop(portable);
        assert_eq!(bytes(&portable_signature(&frozen, &sig)), expected);
    }

    #[test]
    fn named_imports_are_reproducible_but_separate_loads_remain_distinct() {
        use crate::types::decl_loc::LocationIdentity;
        let mut table = DeclLocTable::default();
        let location = table.intern_with_identity(
            crate::location::Location::none(),
            LocationIdentity {
                scope: 7,
                location: 1,
                start: 2,
                end: 3,
            },
        );
        let load = || {
            let ctx = TypeContext::new(Arc::new(IdGenerator::new()));
            ctx.set_location_namespace("Consumer.res");
            let files = |file| file;
            let first = ctx.import_portable_decl_locs(&table, &files);
            let second = ctx.import_portable_decl_locs(&table, &files);
            assert_ne!(first.scopes[&7], second.scopes[&7]);
            assert_ne!(first.import(location), second.import(location));
            (first.scopes[&7], second.scopes[&7])
        };
        assert_eq!(load(), load());
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
            .collect::<Vec<_>>();
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
                .import_portable_decl_locs(&saved.2, &identity, None);
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
            None,
        )
        .unwrap()
        .0;
        let shared_scope = verify(&target, &shared);
        assert_ne!(shared_scope, warm_scope);
        let roundtrip = load(&save(&target, &shared));
        assert_ne!(verify(&target, &roundtrip), shared_scope);

        // Both persistent storage tiers represent the same dependency import,
        // even when a worker falls back because the shared pool is full.
        let unit = "Producer.cmi";
        let locs = target.thread_store().import_portable_decl_locs(
            &saved.2,
            &identity,
            Some(interface_namespace(unit)),
        );
        let stored = internalize_signature_into_store(
            &saved.0,
            &saved.1,
            &locs,
            target.thread_store(),
        );
        let shared = internalize_signature_into_shared(
            &saved.0,
            &saved.1,
            &saved.2,
            &files,
            target.thread_store().shared_pool(),
            Some(unit),
        )
        .unwrap()
        .0;
        assert_eq!(verify(&target, &stored), verify(&target, &shared));
        assert_eq!(
            crate::binser::to_vec(&save(&target, &stored)).unwrap(),
            crate::binser::to_vec(&save(&target, &shared)).unwrap(),
        );

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
        let mut ser = TypeGraphSerializer::<PortableSink>::new(&ctx, None, &mut file_names);
        let index = ser.serialize_type(arrow);
        let PortableTypeDesc::Tarrow { args, ret } = &ser.sink.entries[index].desc else {
            panic!("not arrow")
        };
        assert_eq!(args.len(), 3);
        assert_eq!(args[0].1, *ret);
        assert_eq!(args[1].1, *ret);
        assert_ne!(args[2].1, *ret);
        // Both labels share one portable entry.
        assert_eq!(ser.locations.len(), 1);
        let entries = std::mem::take(&mut ser.sink.entries);
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
