//! A [`Segment`] as an old published unit: the detached old type graph and
//! the explicit old signature whose types are nodes of that graph. This is
//! the inverse of [`super::from_old`]; see its module documentation for the
//! encoding read here.
//!
//! # Output
//!
//! [`Output`] holds a detached `SharedGraph` (the form
//! `cmi/signature_builder.rs` builds a checked unit's publication in, and
//! that `signature_builder::promote` moves into the shared pool) with the old
//! `Signature`, as a `PublishedGraph` with a name table of its own.
//! `Output::into_pool` gives it the names of a pool, so the old checker
//! imports it like any other publication; nothing is serialized and no
//! portable graph is built.
//!
//! # Type nodes
//!
//! Old nodes are numbered densely: first the segment's shared nodes, `Ty(i)`
//! becoming old node `i`, then unique publication identities in template order.
//! Dense `old_offsets` maps template nodes to old nodes, using the publisher's
//! identity rows, not structural equality. In particular a generic parameter
//! also reached through a non-generic row remains the same old node. No node
//! is looked up in a hash table: each source occurrence is exactly one
//! old node, repeated positions of one node stay one old node, and every
//! non-generic node is one old node shared by every item that names it.
//! A multi-root item's synthetic tuple (`from_old::scheme_roots`, named by no
//! root) is node 0 of its template and gets no old node. Template nodes keep
//! their generic level; they are not instances.
//!
//! Template references are decoded as `Graph::instance` decodes them: bit 30
//! set is an offset in the template; otherwise an index of
//! `template_externals`, a shared node. A `SchemeRoot` without bit 30 is a
//! shared node directly. Template list and parameter pools are concatenated in
//! template order (`Graph::capture`), so each template's pool bases are
//! running sums of `Template::list_len` and of its arrows' arities.
//!
//! Descriptors map one to one (`ExtraDescriptor` slots are positions in the
//! node's own list). A `Tconstr` gets an empty abbreviation memo, a `Tfield`
//! its cell from one bulk reservation preserving shared cell identity, and a
//! `Reither` field no link, as a frozen graph has.
//!
//! # Metadata
//!
//! Each metadata row becomes one old value. Strings become owned strings or
//! interned names (one `Name` per distinct segment string); paths are built
//! once per path row; identifiers keep name, stamp and flags. A declaration
//! path that is the item's own binder address (`PathRow::Ident` of the item's
//! binder row) is the absent path it was made from. Coordinate-free
//! locations become source handles, every other location row one entry of the
//! graph's location table, with file names carried by key (`Carried`).
//!
//! What `from_old` drops cannot come back and is made fresh: shape and class
//! block allocations (fresh allocations), abbreviation memos and `Tlink`
//! nodes. Mutability cell classes are preserved by the indexed cell pool.
//!
//! Every walk is iterative: types in one linear pass, paths in row order,
//! longidents and signatures with explicit stacks of 8-byte tasks.

use std::sync::{Arc, RwLock};

use crate::binary_ast::marshal::MarshalFragment;
use crate::cmi::shared_reader::{Carried, PublishedGraph};
use crate::fast_hash::AHashMap;
use crate::ident::{Ident, IdentFlags};
use crate::intern::StrIdx;
use crate::location::{Location, LocationOrigin, Position};
use crate::name::Name;
use crate::parser::longident::Longident;
use crate::tc::graph::{ARROW, CONSTR, GENERIC, LINK, NONE, Node, Param, TUPLE, Ty, VAR};
use crate::tc::segment::*;
use crate::types::Variance;
use crate::types::asttypes::{Label, Located, MutableFlag, PrivateFlag};
use crate::types::decl::{
    AliasPresence, Attribute, AttributePayload, ConstructorArguments, ConstructorDeclaration,
    ExtStatus, ExtensionConstructor, LabelDeclaration, ModtypeDeclaration, ModuleDeclaration,
    ModuleType, PrimKind, PrimitiveDescription, RecStatus as OldRecStatus, RecordRepresentation,
    SemanticStringPayload, SharedVec, Signature, SignatureItem, TypeDeclaration, TypeInlinedType,
    TypeKind, TypeRepresentation, ValueDescription, ValueKind,
};
use crate::types::decl_loc::{DeclLoc, DeclLocKind, DeclLocTable};
use crate::types::external_ffi_types as ffi;
use crate::types::path::Path;
use crate::types::shared_store::{SharedGraph, SharedGraphParts, SharedGraphPayloads};
use crate::types::type_expr::{
    AbbrevMemoRef, GENERIC_LEVEL, MutabilityRef, PackageLidsRef, RowDesc, RowDescRef, RowField,
    RowFieldRef, TypeArg, TypeArgLabel, TypeArgList, TypeDesc, TypeExprRef, TypeRefList,
};
use crate::types::variant_runtime::{
    Block, BlockType, ClassBlocks, Configuration, ConstructorCase, ConstructorReference, Instance,
    Layout, LayoutRef, LiteralTag, ShapeAllocation, ShapeBlocks, Tag, TaggedBlock, ValueShape,
};

const _: () = assert!(GENERIC_LEVEL as u32 == GENERIC);

/// Template reference flag of a node relative to its template's first node
/// (tc/template.rs, `Template`).
const RELATIVE: u32 = 1 << 30;

/// One old published unit rebuilt from a segment: a detached old graph,
/// the old signature whose types are its nodes, and a name table of its own
/// for the graph's longident components. Resolved component indices skip
/// every unresolved diagnostic index retained by the segment.
/// Its fields are private.
pub struct Output {
    published: PublishedGraph,
    unit: String,
    deprecated: Option<String>,
    digest: [u8; 32],
}

impl Output {
    /// O(1): the old signature.
    pub fn signature(&self) -> &Signature {
        &self.published.signature
    }

    /// O(1): the unit's name.
    pub fn unit(&self) -> &str {
        &self.unit
    }

    /// O(1): the unit's own deprecation.
    pub fn deprecated(&self) -> Option<&str> {
        self.deprecated.as_deref()
    }

    /// O(1): the digest the segment's producer supplied.
    pub fn digest(&self) -> [u8; 32] {
        self.digest
    }

    /// O(graph + old printing): check the rebuilt graph with the independent
    /// old printer. Copies only for this explicit check; the cached output
    /// remains immutable, and no canonical text is retained in it.
    pub(crate) fn canonical_text(&self) -> Result<String, String> {
        let ctx =
            crate::types::TypeContext::new_scratch(Arc::new(crate::context::IdGenerator::new()));
        let copy = Self {
            published: PublishedGraph {
                graph: self.published.graph.clone(),
                signature: self.published.signature.clone(),
                names: self.published.names.clone(),
            },
            unit: self.unit.clone(),
            deprecated: self.deprecated.clone(),
            digest: self.digest,
        };
        let mut graph = copy.into_pool(ctx.thread_store().shared_pool());
        let signature =
            crate::cmi::portable_types::import_checker_publication(&mut graph, &self.unit, &ctx)?;
        Ok(crate::types::canonical_sig::canonical_signature(
            &ctx,
            &self.unit,
            &signature,
            self.deprecated.as_deref(),
            None,
        ))
    }

    /// O(1): the detached publication, readable in place
    /// (`PublishedGraph::reader`). An importer whose pool owns another name
    /// table imports it through its frozen graph
    /// (`portable_types::internalize_pers_struct`).
    ///
    /// Test-only until the world slot that publishes segments calls it.
    #[cfg(test)]
    pub(crate) fn into_published(self) -> PublishedGraph {
        self.published
    }

    /// O(graph parts moved + distinct components + package constraint
    /// components), one pool name per distinct component and an explicit
    /// stack over the constraints. The detached publication of the unit with
    /// the pool's longident names, as `signature_builder::build` makes one;
    /// the old importer (`signature_builder::promote`) moves it into the pool.
    ///
    pub(crate) fn into_pool(
        self,
        pool: &crate::types::shared_store::SharedTypePool,
    ) -> PublishedGraph {
        let PublishedGraph {
            mut graph,
            signature,
            names,
        } = self.published;
        let interned: Vec<(u32, StrIdx)> = {
            let names = names.read().unwrap();
            let mut rows: Vec<_> = names.iter().collect();
            rows.sort_unstable_by_key(|(index, _)| **index);
            rows.into_iter()
                .map(|(&index, name)| (index, pool.intern_longident_name(name)))
                .collect()
        };
        let mut parts = match Arc::get_mut(&mut graph) {
            Some(graph) => graph.take_parts(),
            None => graph.copy_parts(),
        };
        let map = |name: &mut StrIdx| {
            if let Ok(index) = interned.binary_search_by_key(&name.raw(), |(old, _)| *old) {
                *name = interned[index].1;
            }
        };
        let mut work: Vec<&mut Longident> = Vec::new();
        for lids in parts.payloads.lids.iter_mut() {
            work.extend(lids.iter_mut());
            while let Some(lid) = work.pop() {
                match lid {
                    Longident::Lident(name) => map(name),
                    Longident::Ldot(prefix, name) => {
                        map(name);
                        work.push(&mut **prefix);
                    }
                    Longident::Lapply(functor, argument) => {
                        work.push(&mut **functor);
                        work.push(&mut **argument);
                    }
                }
            }
        }
        drop(work);
        PublishedGraph {
            graph: Arc::new(SharedGraph::detached(parts)),
            signature,
            names: pool.names(),
        }
    }
}

/// O(segment nodes + list and parameter slots + metadata rows + signature
/// items + unresolved components log unresolved components), each segment node and row read once; walks are iterative.
/// Allocates by pool growth and for owned old metadata (strings, declaration
/// vectors, rows, boxes). Arrow labels reuse interned names through a dense
/// string-indexed cache; field cells use one atomic reservation per conversion,
/// never one per field. Old row and package descriptors own their vectors.
///
/// Panics on a segment `from_old` could not have made: a link node, a
/// reference outside its pool or template, or a row of the wrong shape.
pub fn to_old(segment: &Segment) -> Output {
    run(segment).0
}

/// Test builds count the old nodes made; the count is not a step.
struct Visits {
    #[cfg(test)]
    count: u64,
}

/// O(stored nodes + slots + metadata/output bytes + signature items +
/// unresolved components log unresolved components), with dense offset setup
/// before converting each distinct publication identity. Owned recursive old
/// metadata is rebuilt iteratively. Space is O(segment pools + old output);
/// cell identities use one bulk atomic reservation, labels reuse cached names.
/// Returns the test-only number of old nodes made alongside the publication.
fn run(segment: &Segment) -> (Output, Visits) {
    let unit = segment
        .signature
        .unit
        .expect("a converted segment names its unit");
    let mut rebuild = Rebuild::new(segment);
    rebuild.locations();
    rebuild.paths();
    rebuild.layouts();
    rebuild.types();
    rebuild.roots();
    let signature = rebuild.signatures(unit.signature);
    let visits = Visits {
        #[cfg(test)]
        count: rebuild.visits,
    };
    let unit_name = rebuild.text(unit.name).to_owned();
    let deprecated = rebuild.opt_string(unit.deprecated);
    let Rebuild {
        nodes,
        payloads,
        layouts,
        coordinates,
        file_names,
        components,
        component_keys,
        ..
    } = rebuild;
    let mut table = AHashMap::default();
    for (index, name) in component_keys.into_iter().zip(components) {
        table.insert(index, name);
    }
    let parts = SharedGraphParts {
        nodes,
        payloads,
        layouts,
        locations: coordinates.into_iter().collect::<DeclLocTable>(),
        carried: Carried {
            file_names,
            ..Carried::default()
        },
    };
    let output = Output {
        published: PublishedGraph {
            graph: Arc::new(SharedGraph::detached(parts)),
            signature: Arc::new(signature),
            names: Arc::new(RwLock::new(table)),
        },
        unit: unit_name,
        deprecated,
        digest: segment.digest,
    };
    (output, visits)
}

/// A template's place in combined segment numbering: offset `k` (with
/// `first <= k < len`) is publication node `start + k`; dense `old_offsets`
/// gives its old node. A shared frame names shared nodes directly. 16 bytes.
#[derive(Clone, Copy, Debug)]
struct Frame {
    start: u32,
    first: u32,
    len: u32,
    relative: bool,
}

const SHARED: Frame = Frame {
    start: 0,
    first: 0,
    len: 0,
    relative: false,
};

/// Longident walk work, an explicit post-order over `longidents` rows.
#[derive(Clone, Copy, Debug)]
enum LidTask {
    Enter(u32),
    Exit(u32),
}

/// Signature walk work over `signatures` and `module_types` rows: a row is
/// entered (its children queued), then done (built from its children).
#[derive(Clone, Copy, Debug)]
enum SigTask {
    Signature(u32),
    SignatureDone(u32),
    ModuleType(u32),
    ModuleTypeDone(u32),
}

struct Rebuild<'s> {
    seg: &'s Segment,
    pools: &'s SignaturePools,
    /// Every segment string, validated once.
    strs: Vec<&'s str>,
    /// The interned name of a segment string, made on first use.
    names: Vec<Option<Name>>,
    /// The handle of each `locations` row.
    locs: Vec<DeclLoc>,
    /// The location table's entries, one per coordinate row.
    coordinates: Vec<Location>,
    /// Whether a segment string is already a carried file name.
    file_seen: Vec<bool>,
    file_names: Vec<(u32, String)>,
    /// The path of each `paths` row.
    paths: Vec<Path>,
    nodes: Vec<(TypeDesc, i32)>,
    mutabilities: Vec<MutabilityRef>,
    payloads: SharedGraphPayloads,
    layouts: Vec<Layout>,
    /// The old node of each `roots` row.
    roots: Vec<TypeExprRef>,
    /// The frame of each template; `SHARED` for a zero-node template.
    bases: Vec<Frame>,
    /// Template-node offsets to old nodes; publication aliases share one entry.
    old_offsets: Vec<u32>,
    /// The component index of a segment string, NONE before its first use.
    component_of: Vec<u32>,
    components: Vec<String>,
    component_keys: Vec<u32>,
    reserved_components: Vec<u32>,
    next_component: u32,
    lid_work: Vec<LidTask>,
    lid_out: Vec<Longident>,
    #[cfg(test)]
    visits: u64,
}

impl<'s> Rebuild<'s> {
    /// O(strings + bytes + unresolved components log unresolved components):
    /// validate strings once and reserve missing-name diagnostic indices.
    fn new(seg: &'s Segment) -> Self {
        let pools = &seg.signature;
        let strs: Vec<&'s str> = pools
            .strings
            .iter()
            .map(|range| {
                let bytes = &pools.bytes[range.start as usize..(range.start + range.len) as usize];
                std::str::from_utf8(bytes).expect("segment strings are UTF-8")
            })
            .collect();
        let mut reserved_components: Vec<_> = pools
            .longidents
            .iter()
            .filter_map(|row| match row {
                LongidentRow::Unresolved(raw) | LongidentRow::UnresolvedDot { raw, .. } => {
                    Some(*raw)
                }
                _ => None,
            })
            .collect();
        reserved_components.sort_unstable();
        reserved_components.dedup();
        let template_slots = seg.template_lists.len() + seg.lists.len();
        Self {
            seg,
            pools,
            names: vec![None; strs.len()],
            strs,
            locs: Vec::with_capacity(pools.locations.len()),
            coordinates: Vec::new(),
            file_seen: Vec::new(),
            file_names: Vec::new(),
            paths: Vec::with_capacity(pools.paths.len()),
            nodes: Vec::with_capacity(seg.nodes.len() + seg.template_nodes.len()),
            mutabilities: MutabilityRef::new_persistent_batch(pools.mutabilities.iter().map(
                |&mutable| {
                    if mutable {
                        MutableFlag::Mutable
                    } else {
                        MutableFlag::Immutable
                    }
                },
            )),
            payloads: SharedGraphPayloads {
                lists: Vec::with_capacity(template_slots),
                args: Vec::with_capacity(seg.params.len() + seg.template_params.len()),
                rows: Vec::with_capacity(pools.variants.len()),
                lids: Vec::with_capacity(pools.packages.len()),
            },
            layouts: Vec::with_capacity(pools.layouts.len()),
            roots: Vec::with_capacity(pools.roots.len()),
            bases: Vec::with_capacity(seg.templates.len()),
            old_offsets: vec![NONE; seg.template_nodes.len()],
            component_of: Vec::new(),
            components: Vec::new(),
            component_keys: Vec::new(),
            reserved_components,
            next_component: 0,
            lid_work: Vec::new(),
            lid_out: Vec::new(),
            #[cfg(test)]
            visits: 0,
        }
    }

    /// O(1): a segment string.
    fn text(&self, index: u32) -> &'s str {
        self.strs[index as usize]
    }

    /// O(1) after a string's first use, which interns it once.
    fn name(&mut self, index: u32) -> Name {
        if let Some(name) = self.names[index as usize] {
            return name;
        }
        let name = Name::new(self.strs[index as usize]);
        self.names[index as usize] = Some(name);
        name
    }

    /// O(1) or O(None) after a string's first use.
    fn opt_name(&mut self, index: u32) -> Option<Name> {
        (index != NONE).then(|| self.name(index))
    }

    /// O(length): an owned string; NONE for none.
    fn opt_string(&self, index: u32) -> Option<String> {
        (index != NONE).then(|| self.text(index).to_owned())
    }

    /// O(total length): owned strings of a range of `indices`.
    fn string_list(&self, range: Range) -> Vec<String> {
        slice(&self.pools.indices, range)
            .iter()
            .map(|&index| self.text(index).to_owned())
            .collect()
    }

    /// O(total length): owned pairs of a range of `string_pairs`.
    fn string_pairs(&self, range: Range) -> Vec<(String, String)> {
        slice(&self.pools.string_pairs, range)
            .iter()
            .map(|pair| {
                (
                    self.text(pair.first).to_owned(),
                    self.text(pair.second).to_owned(),
                )
            })
            .collect()
    }

    /// O(1) after a string's first use: an identifier row's identifier, with
    /// its stamp and flags (its scope only locates its binder).
    fn ident(&mut self, row: u32) -> Ident {
        let row = self.pools.identifiers[row as usize];
        let flags = u8::try_from(row.flags).expect("identifier flags fit a byte");
        Ident::new(
            self.name(row.name),
            row.stamp,
            IdentFlags::from_bits_truncate(flags),
        )
    }

    /// O(1): a location row's handle.
    fn loc(&self, row: u32) -> DeclLoc {
        self.locs[row as usize]
    }

    /// O(location rows), one step per row: the coordinate-free ones become
    /// source handles, each other one table entry (no equality interning).
    fn locations(&mut self) {
        let pools = self.pools;
        for row in pools.locations.iter() {
            #[cfg(test)]
            crate::tc::steps::tick();
            let loc = Location {
                loc_start: self.position(row.start),
                loc_end: self.position(row.end),
                loc_ghost: row.ghost,
                origin: LocationOrigin::new(row.origin),
            };
            let handle = match DeclLoc::source(&loc) {
                Some(handle) => handle,
                None => {
                    self.coordinates.push(loc);
                    DeclLoc::table(DeclLocKind::Portable, 0, self.coordinates.len() - 1)
                }
            };
            self.locs.push(handle);
        }
    }

    /// O(1), or O(strings) once for the first file name. A file name is
    /// carried with key `string + 1`; NONE is `Location::none()`'s file.
    fn position(&mut self, position: PositionRow) -> Position {
        let file_name = if position.filename == NONE {
            StrIdx::default()
        } else {
            let index = position.filename as usize;
            if self.file_seen.is_empty() {
                self.file_seen = vec![false; self.strs.len()];
            }
            let key = position.filename + 1;
            if !self.file_seen[index] {
                self.file_seen[index] = true;
                self.file_names.push((key, self.strs[index].to_owned()));
            }
            StrIdx::from_raw(key)
        };
        Position {
            file_name,
            line: position.line,
            bol: position.beginning_of_line,
            cnum: position.offset,
        }
    }

    /// O(path rows), one step per row, in row order: `from_old` writes a
    /// path's parent rows before it, so every parent is already built.
    fn paths(&mut self) {
        let pools = self.pools;
        for (index, row) in pools.paths.iter().enumerate() {
            #[cfg(test)]
            crate::tc::steps::tick();
            let earlier = |row: u32| {
                assert!((row as usize) < index, "a path row follows its parts");
                row as usize
            };
            let path = match *row {
                PathRow::Ident(id) => Path::pident(self.ident(id)),
                PathRow::Dot {
                    parent,
                    name,
                    position,
                } => {
                    let parent = self.paths[earlier(parent)];
                    Path::pdot_pos(parent, self.name(name), position)
                }
                PathRow::Apply { functor, argument } => {
                    Path::papply(self.paths[earlier(functor)], self.paths[earlier(argument)])
                }
            };
            self.paths.push(path);
        }
    }

    /// O(1): the path of a declaration's path row, `None` when the row is the
    /// item's binder address (an absent source path, `from_old::declared_path`).
    fn declared(&self, path: u32, binder: u32) -> Option<Path> {
        match self.pools.paths[path as usize] {
            PathRow::Ident(id) if id == binder => None,
            _ => Some(self.paths[path as usize]),
        }
    }

    /// O(layout rows + runtime constructors): one old layout per row, so
    /// layout row `i` is `LayoutRef` `i` of the detached graph.
    fn layouts(&mut self) {
        let pools = self.pools;
        for row in pools.layouts.iter() {
            let cases = slice(&pools.runtime_constructors, row.constructors);
            let constructors = cases
                .iter()
                .map(|case| match *case {
                    RuntimeConstructorRow::Constant { name, literal } => {
                        ConstructorCase::Constant(self.tag(name, literal))
                    }
                    RuntimeConstructorRow::Tagged {
                        name,
                        literal,
                        tag_name,
                    } => ConstructorCase::Block(Block::Tagged(TaggedBlock {
                        tag: self.tag(name, literal),
                        tag_name: self.opt_string(tag_name),
                    })),
                    RuntimeConstructorRow::Untagged {
                        name,
                        literal,
                        block_type,
                    } => ConstructorCase::Block(Block::Untagged {
                        tag: self.tag(name, literal),
                        block_type: self.block_type(block_type),
                    }),
                })
                .collect();
            // The matching facts are derived from the constructors, as
            // variant_runtime.ml `make_layout` derives them.
            let layout = Layout::new(
                Configuration {
                    unboxed: row.unboxed,
                    tag_name: self.opt_string(row.tag_name),
                },
                constructors,
            );
            self.layouts.push(layout);
        }
    }

    /// O(1) plus the literal.
    fn tag(&mut self, name: u32, literal: u32) -> Tag {
        Tag {
            name: self.name(name),
            literal: self.literal(literal),
        }
    }

    /// O(1) plus a string copy.
    fn literal(&self, row: u32) -> LiteralTag {
        match self.pools.literals[row as usize] {
            LiteralRow::String(text) => LiteralTag::String(self.text(text).to_owned()),
            LiteralRow::Int(value) => LiteralTag::Int(value),
            LiteralRow::Float(text) => LiteralTag::Float(self.text(text).to_owned()),
            LiteralRow::BigInt(text) => LiteralTag::BigInt(self.text(text).to_owned()),
            LiteralRow::Bool(value) => LiteralTag::Bool(value),
            LiteralRow::Null => LiteralTag::Null,
            LiteralRow::Undefined => LiteralTag::Undefined,
        }
    }

    /// O(ancestors). A class or array kind gets fresh block allocations:
    /// `from_old` keeps no allocation identity.
    fn block_type(&self, row: u32) -> BlockType {
        match self.pools.block_types[row as usize] {
            BlockTypeRow::Number => BlockType::Number,
            BlockTypeRow::String => BlockType::String,
            BlockTypeRow::Bigint => BlockType::Bigint,
            BlockTypeRow::Boolean => BlockType::Boolean,
            BlockTypeRow::Array => BlockType::Instance(Instance::Array(ShapeAllocation::fresh())),
            BlockTypeRow::Class { name, ancestors } => BlockType::Instance(Instance::Class {
                name: self.text(name).to_owned(),
                ancestors: self.string_list(ancestors),
                blocks: ClassBlocks::fresh(ancestors.len as usize),
            }),
            BlockTypeRow::Symbol => BlockType::Symbol,
            BlockTypeRow::Function => BlockType::Function,
            BlockTypeRow::Object => BlockType::Object,
            BlockTypeRow::Unknown => BlockType::Unknown,
        }
    }

    /// O(ancestors).
    fn shape(&self, row: u32) -> ValueShape {
        match self.pools.shapes[row as usize] {
            ShapeRow::Unstated => ValueShape::Unstated,
            ShapeRow::NeverUndefined => ValueShape::NeverUndefined,
            ShapeRow::Recognized(block_type) => {
                ValueShape::recognized_as(self.block_type(block_type), ShapeBlocks::fresh())
            }
        }
    }

    /// O(stored nodes + slots): first assign dense offsets by publication
    /// identity, then convert each unique node and its slots once. Synthetic
    /// tuples and repeated identities produce no old node. No recursion or
    /// hash lookup. The counter counts converted nodes and copied slots.
    fn types(&mut self) {
        let seg = self.seg;
        let mut counts = vec![0u32; seg.templates.len()];
        for root in self.seg.signature.roots.iter() {
            counts[root.template as usize] += 1;
        }
        let shared = seg.nodes.len() as u32;
        let mut next = shared;
        for (index, template) in seg.templates.iter().enumerate() {
            if template.node_len == 0 {
                self.bases.push(SHARED);
                continue;
            }
            let first = u32::from(counts[index] > 1);
            self.bases.push(Frame {
                start: shared + template.nodes,
                first,
                len: template.node_len,
                relative: true,
            });
            for offset in first..template.node_len {
                let physical = shared + template.nodes + offset;
                let origin = seg.publication_node(physical);
                let old = if origin == physical {
                    let old = next;
                    next += 1;
                    old
                } else if origin < shared {
                    origin
                } else {
                    self.old_offsets[(origin - shared) as usize]
                };
                assert_ne!(old, NONE, "publication identity precedes its aliases");
                self.old_offsets[(physical - shared) as usize] = old;
            }
        }
        for &node in seg.nodes.iter() {
            let converted = self.node(node, SHARED, &seg.lists, &seg.params);
            self.nodes.push(converted);
        }
        let mut list_base = 0usize;
        let mut param_base = 0usize;
        let mut pools = 0usize;
        for (index, template) in seg.templates.iter().enumerate() {
            if template.node_len == 0 {
                assert_eq!(template.list_len, 0, "an external template has no lists");
                continue;
            }
            let count = counts[index];
            assert_ne!(count, 0, "a template belongs to an item with roots");
            let first = u32::from(count > 1);
            let frame = self.bases[index];
            let nodes = &seg.template_nodes
                [template.nodes as usize..(template.nodes + template.node_len) as usize];
            let lists = &seg.template_lists[list_base..list_base + template.list_len as usize];
            let params = &seg.template_params[param_base..];
            if first == 1 {
                let synthetic = nodes[0];
                assert!(
                    synthetic.tag() == TUPLE
                        && synthetic.head & EXTENDED == 0
                        && synthetic.arity() == count
                        && synthetic.level == GENERIC,
                    "a multi-root template starts with its synthetic tuple"
                );
            }
            for (offset, &node) in nodes.iter().enumerate().skip(first as usize) {
                if node.tag() == ARROW {
                    param_base += node.arity() as usize;
                }
                let physical = frame.start + offset as u32;
                if seg.publication_node(physical) == physical {
                    let node = crate::tc::template::descriptor(node);
                    let converted = self.node(node, frame, lists, params);
                    self.nodes.push(converted);
                }
            }
            list_base += template.list_len as usize;
            pools += 1;
        }
        assert_eq!(
            list_base,
            seg.template_lists.len(),
            "template lists are concatenated"
        );
        assert_eq!(
            param_base,
            seg.template_params.len(),
            "template parameters are concatenated"
        );
        assert_eq!(
            pools,
            seg.template_pools.len(),
            "one pool range per nonempty template"
        );
    }

    /// O(1): the old node a reference of `frame` names.
    fn at(&self, frame: Frame, ty: Ty) -> TypeExprRef {
        let shared = self.seg.nodes.len() as u32;
        let index = if !frame.relative {
            assert!(ty.0 < shared, "a shared reference names a shared node");
            ty.0
        } else if ty.0 & RELATIVE != 0 {
            let offset = ty.0 & !RELATIVE;
            assert!(
                (frame.first..frame.len).contains(&offset),
                "a template reference names a node of its own template"
            );
            self.old_offsets[(frame.start - shared + offset) as usize]
        } else {
            let target = self.seg.template_externals[ty.0 as usize].0;
            assert!(target < shared, "an external reference names a shared node");
            target
        };
        TypeExprRef::from_usize(index as usize)
    }

    /// Amortized O(slots), one step per slot: an old list of references.
    fn list(&mut self, frame: Frame, slots: &[Ty]) -> TypeRefList {
        let start = u32::try_from(self.payloads.lists.len()).expect("old list limit");
        for &slot in slots {
            #[cfg(test)]
            crate::tc::steps::tick();
            let target = self.at(frame, slot);
            self.payloads.lists.push(target);
        }
        TypeRefList::from_parts(start, slots.len())
    }

    /// Amortized O(slots), one step per slot: owned references.
    fn refs(&self, frame: Frame, slots: &[Ty]) -> Vec<TypeExprRef> {
        slots
            .iter()
            .map(|&slot| {
                #[cfg(test)]
                crate::tc::steps::tick();
                self.at(frame, slot)
            })
            .collect()
    }

    /// One step, plus one per list or parameter slot and the payload rows:
    /// the old descriptor and level of one segment node. `lists` and `params`
    /// start at the frame's pool bases.
    fn node(
        &mut self,
        node: Node,
        frame: Frame,
        lists: &[Ty],
        params: &[Param],
    ) -> (TypeDesc, i32) {
        #[cfg(test)]
        {
            crate::tc::steps::tick();
            self.visits += 1;
        }
        let level = i32::try_from(node.level).expect("a published level fits the old level");
        let arity = node.arity() as usize;
        let b = node.b as usize;
        let desc = match node.tag() {
            VAR => TypeDesc::Tvar(self.opt_name(node.a)),
            CONSTR => {
                assert_eq!(lists[b].0, NONE, "a published constructor has no memo");
                TypeDesc::Tconstr {
                    path: self.paths[node.a as usize],
                    args: self.list(frame, &lists[b + 1..b + 1 + arity]),
                    abbrev: AbbrevMemoRef::nil(),
                }
            }
            TUPLE if node.head & EXTENDED == 0 => {
                TypeDesc::Ttuple(self.list(frame, &lists[b..b + arity]))
            }
            TUPLE => self.extended(node.a, frame, &lists[b..b + arity]),
            ARROW => {
                let start = u32::try_from(self.payloads.args.len()).expect("old argument limit");
                for &param in &params[b..b + arity] {
                    #[cfg(test)]
                    crate::tc::steps::tick();
                    let arg = self.arg(frame, param);
                    self.payloads.args.push(arg);
                }
                TypeDesc::Tarrow {
                    args: TypeArgList::from_parts(start, arity),
                    ret: self.at(frame, Ty(node.a)),
                }
            }
            LINK => panic!("a published segment holds no link"),
            tag => panic!("unknown segment descriptor tag {tag}"),
        };
        (desc, level)
    }

    /// O(1) after interning a distinct label name once: one arrow parameter. The label is NONE
    /// (`Nolabel`) or `name << 1 | optional`.
    fn arg(&mut self, frame: Frame, param: Param) -> TypeArg {
        let typ = self.at(frame, param.ty);
        if param.label == NONE {
            assert_eq!(param.loc, NONE, "an unlabelled parameter has no location");
            return TypeArg::unlabeled(typ);
        }
        let name = self.name(param.label >> 1);
        let label = TypeArgLabel::from_name(name, param.label & 1 != 0, self.loc(param.loc));
        TypeArg::with_label(label, typ)
    }

    /// O(slots + payload rows): the descriptor of an `EXTENDED` node whose
    /// own list is `slots`.
    fn extended(&mut self, extra: u32, frame: Frame, slots: &[Ty]) -> TypeDesc {
        let pools = self.pools;
        let slot_count = |expected: usize| {
            assert_eq!(slots.len(), expected, "descriptor slot count");
        };
        match pools.descriptor_extras[extra as usize] {
            ExtraDescriptor::Object => {
                slot_count(1);
                TypeDesc::Tobject {
                    fields: self.at(frame, slots[0]),
                }
            }
            ExtraDescriptor::Field { name, mutability } => {
                slot_count(2);
                TypeDesc::Tfield {
                    name: self.name(name),
                    mutability: self.mutabilities[mutability as usize],
                    typ: self.at(frame, slots[0]),
                    rest: self.at(frame, slots[1]),
                }
            }
            ExtraDescriptor::Nil => {
                slot_count(0);
                TypeDesc::Tnil
            }
            ExtraDescriptor::Univar(name) => {
                slot_count(0);
                TypeDesc::Tunivar(self.opt_name(name))
            }
            ExtraDescriptor::Poly => {
                assert!(!slots.is_empty(), "a polytype has a body slot");
                TypeDesc::Tpoly {
                    body: self.at(frame, slots[0]),
                    vars: self.list(frame, &slots[1..]),
                }
            }
            ExtraDescriptor::Variant(row) => {
                let row = self.variant(row, frame, slots);
                TypeDesc::Tvariant(row)
            }
            ExtraDescriptor::Package(row) => {
                let row = pools.packages[row as usize];
                let indices = slice(&pools.indices, row.longidents);
                let mut lids = Vec::with_capacity(indices.len());
                for &lid in indices {
                    lids.push(self.longident(lid));
                }
                let arguments = row.arguments;
                assert_eq!(
                    (arguments.start, arguments.len as usize),
                    (0, slots.len()),
                    "every package slot is an argument"
                );
                let lids_index =
                    u32::try_from(self.payloads.lids.len()).expect("old package limit");
                self.payloads.lids.push(lids);
                TypeDesc::Tpackage {
                    path: self.paths[row.path as usize],
                    lids: PackageLidsRef::from_raw(lids_index),
                    args: self.list(frame, slots),
                }
            }
            ExtraDescriptor::Substitution => {
                slot_count(1);
                TypeDesc::Tsubst(self.at(frame, slots[0]))
            }
        }
    }

    /// O(fields + slots): an old row. Slots are, in order, each field's
    /// types, `row_more`, then the name's arguments.
    fn variant(&mut self, row: u32, frame: Frame, slots: &[Ty]) -> RowDescRef {
        let pools = self.pools;
        let row = pools.variants[row as usize];
        let fields = slice(&pools.row_fields, row.fields);
        let mut used = 0usize;
        let mut row_fields = Vec::with_capacity(fields.len());
        for field in fields {
            assert_eq!(field.link, NONE, "a frozen row field has no link");
            let types = slice(slots, field.types);
            used += types.len();
            let value = match field.kind {
                RowFieldKind::Present => match types {
                    [] => RowField::Rpresent(None),
                    [ty] => RowField::Rpresent(Some(self.at(frame, *ty))),
                    _ => panic!("a present row field has at most one argument"),
                },
                RowFieldKind::Absent => {
                    assert!(types.is_empty(), "an absent row field has no argument");
                    RowField::Rabsent
                }
                RowFieldKind::Either { constant, matched } => RowField::Reither {
                    constant,
                    types: self.refs(frame, types),
                    matched,
                    link: RowFieldRef::null(),
                },
            };
            row_fields.push((Label::new(self.text(field.name)), value));
        }
        let row_more = self.at(frame, slots[row.more as usize]);
        let row_name = if row.name == NONE {
            assert_eq!(
                row.name_arguments.len, 0,
                "an unnamed row has no name arguments"
            );
            None
        } else {
            Some((
                self.paths[row.name as usize],
                self.refs(frame, slice(slots, row.name_arguments)),
            ))
        };
        used += 1 + row.name_arguments.len as usize;
        assert_eq!(
            used,
            slots.len(),
            "a row's slots are its fields, more and name"
        );
        let index = u32::try_from(self.payloads.rows.len()).expect("old row limit");
        self.payloads.rows.push(RowDesc {
            row_fields: SharedVec::new(row_fields),
            row_more,
            row_closed: row.closed,
            row_fixed: row.fixed,
            row_name,
        });
        RowDescRef::from_raw(index)
    }

    /// O(1) after first use; first use also skips reserved unresolved indices
    /// with binary searches, preserving their diagnostic spelling.
    fn component(&mut self, name: u32) -> StrIdx {
        if self.component_of.is_empty() {
            self.component_of = vec![NONE; self.strs.len()];
        }
        let slot = self.component_of[name as usize];
        if slot != NONE {
            return StrIdx::from_raw(slot);
        }
        while self
            .reserved_components
            .binary_search(&self.next_component)
            .is_ok()
        {
            self.next_component = self
                .next_component
                .checked_add(1)
                .expect("longident component limit");
        }
        let index = self.next_component;
        self.next_component = self
            .next_component
            .checked_add(1)
            .expect("longident component limit");
        self.component_keys.push(index);
        self.components.push(self.strs[name as usize].to_owned());
        self.component_of[name as usize] = index;
        StrIdx::from_raw(index)
    }

    /// O(components), one step per row: explicit post-order with reused
    /// buffers; one box per old component, which the old form owns.
    fn longident(&mut self, root: u32) -> Longident {
        self.lid_work.clear();
        self.lid_out.clear();
        self.lid_work.push(LidTask::Enter(root));
        while let Some(task) = self.lid_work.pop() {
            match task {
                LidTask::Enter(row) => {
                    #[cfg(test)]
                    crate::tc::steps::tick();
                    match self.pools.longidents[row as usize] {
                        LongidentRow::Ident(name) => {
                            let name = self.component(name);
                            self.lid_out.push(Longident::Lident(name));
                        }
                        LongidentRow::Unresolved(raw) => {
                            self.lid_out.push(Longident::Lident(StrIdx::from_raw(raw)))
                        }
                        LongidentRow::Dot { parent, .. }
                        | LongidentRow::UnresolvedDot { parent, .. } => {
                            self.lid_work.push(LidTask::Exit(row));
                            self.lid_work.push(LidTask::Enter(parent));
                        }
                        LongidentRow::Apply { functor, argument } => {
                            self.lid_work.push(LidTask::Exit(row));
                            self.lid_work.push(LidTask::Enter(argument));
                            self.lid_work.push(LidTask::Enter(functor));
                        }
                    }
                }
                LidTask::Exit(row) => match self.pools.longidents[row as usize] {
                    LongidentRow::Dot { name, .. } => {
                        let prefix = self.lid_out.pop().expect("a prefix");
                        let name = self.component(name);
                        self.lid_out.push(Longident::Ldot(Box::new(prefix), name));
                    }
                    LongidentRow::UnresolvedDot { raw, .. } => {
                        let prefix = self.lid_out.pop().expect("a prefix");
                        self.lid_out
                            .push(Longident::Ldot(Box::new(prefix), StrIdx::from_raw(raw)));
                    }
                    LongidentRow::Apply { .. } => {
                        let argument = self.lid_out.pop().expect("an argument");
                        let functor = self.lid_out.pop().expect("a functor");
                        self.lid_out
                            .push(Longident::Lapply(Box::new(functor), Box::new(argument)));
                    }
                    LongidentRow::Ident(_) | LongidentRow::Unresolved(_) => {
                        unreachable!("a leaf is never exited")
                    }
                },
            }
        }
        let lid = self.lid_out.pop().expect("a longident");
        assert!(self.lid_out.is_empty(), "one longident per root");
        lid
    }

    /// O(roots): the old node of every scheme root. A root with bit 30 is an
    /// offset in its template; any other is a shared node.
    fn roots(&mut self) {
        let shared = self.seg.nodes.len() as u32;
        let pools = self.pools;
        for root in pools.roots.iter() {
            let target = if root.ty.0 & RELATIVE != 0 {
                let frame = self.bases[root.template as usize];
                assert!(
                    frame.relative,
                    "a relative root names a node of its template"
                );
                self.at(frame, root.ty)
            } else {
                assert!(root.ty.0 < shared, "a direct root names a shared node");
                TypeExprRef::from_usize(root.ty.0 as usize)
            };
            self.roots.push(target);
        }
    }

    /// O(1).
    fn root(&self, index: u32) -> TypeExprRef {
        self.roots[index as usize]
    }

    /// O(1) or O(None).
    fn opt_root(&self, index: u32) -> Option<TypeExprRef> {
        (index != NONE).then(|| self.root(index))
    }

    /// O(roots in range).
    fn root_list(&self, range: Range) -> Vec<TypeExprRef> {
        slice(&self.roots, range).to_vec()
    }

    /// O(signature rows + module type rows + item metadata), one explicit
    /// stack of 8-byte tasks whatever the nesting of modules and functors.
    /// Each nested signature and module type is built once, after its
    /// children, and moved into its parent.
    fn signatures(&mut self, top: u32) -> Signature {
        let pools = self.pools;
        let mut signatures: Vec<Option<Signature>> =
            (0..pools.signatures.len()).map(|_| None).collect();
        let mut module_types: Vec<Option<ModuleType>> =
            (0..pools.module_types.len()).map(|_| None).collect();
        let mut work = vec![SigTask::Signature(top)];
        while let Some(task) = work.pop() {
            match task {
                SigTask::Signature(index) => {
                    work.push(SigTask::SignatureDone(index));
                    for row in self.items(index) {
                        match row.kind {
                            SignatureKind::Module => {
                                let module = pools.modules[row.declaration as usize];
                                work.push(SigTask::ModuleType(module.module_type));
                            }
                            SignatureKind::ModuleType => {
                                let module = pools.modules[row.declaration as usize];
                                if module.module_type != NONE {
                                    work.push(SigTask::ModuleType(module.module_type));
                                }
                            }
                            _ => {}
                        }
                    }
                }
                SigTask::ModuleType(index) => {
                    work.push(SigTask::ModuleTypeDone(index));
                    match pools.module_types[index as usize] {
                        ModuleTypeRow::Signature(signature) => {
                            work.push(SigTask::Signature(signature))
                        }
                        ModuleTypeRow::Functor {
                            parameter_type,
                            result,
                            ..
                        } => {
                            if parameter_type != NONE {
                                work.push(SigTask::ModuleType(parameter_type));
                            }
                            work.push(SigTask::ModuleType(result));
                        }
                        ModuleTypeRow::Ident(_) | ModuleTypeRow::Alias { .. } => {}
                    }
                }
                SigTask::SignatureDone(index) => {
                    let rows = self.items(index);
                    let mut items = Vec::with_capacity(rows.len());
                    for &row in rows {
                        #[cfg(test)]
                        crate::tc::steps::tick();
                        items.push(self.item(row, &mut module_types));
                    }
                    signatures[index as usize] = Some(items);
                }
                SigTask::ModuleTypeDone(index) => {
                    #[cfg(test)]
                    crate::tc::steps::tick();
                    let module_type = self.module_type(index, &mut signatures, &mut module_types);
                    module_types[index as usize] = Some(module_type);
                }
            }
        }
        take(&mut signatures, top)
    }

    /// O(1): a signature row's items.
    fn items(&self, index: u32) -> &'s [SignatureItemRow] {
        let pools = self.pools;
        slice(&pools.ordered_items, pools.signatures[index as usize])
    }

    /// O(1), moving its built children.
    fn module_type(
        &mut self,
        index: u32,
        signatures: &mut [Option<Signature>],
        module_types: &mut [Option<ModuleType>],
    ) -> ModuleType {
        match self.pools.module_types[index as usize] {
            ModuleTypeRow::Ident(path) => ModuleType::MtyIdent(self.paths[path as usize]),
            ModuleTypeRow::Alias { path, present } => ModuleType::MtyAlias(
                if present {
                    AliasPresence::MtaPresent
                } else {
                    AliasPresence::MtaAbsent
                },
                Arc::new(self.paths[path as usize]),
            ),
            ModuleTypeRow::Signature(signature) => {
                ModuleType::MtySignature(Arc::new(take(signatures, signature)))
            }
            ModuleTypeRow::Functor {
                parameter,
                parameter_type,
                result,
            } => ModuleType::MtyFunctor {
                param: self.ident(parameter),
                param_type: (parameter_type != NONE)
                    .then(|| Box::new(take(module_types, parameter_type))),
                result: Box::new(take(module_types, result)),
            },
        }
    }

    /// O(the item's declaration metadata), moving its built module type.
    fn item(
        &mut self,
        row: SignatureItemRow,
        module_types: &mut [Option<ModuleType>],
    ) -> SignatureItem {
        let declaration = row.declaration;
        match row.kind {
            SignatureKind::Value => {
                ordinary(row.status);
                let ident = self.ident(row.ident);
                SignatureItem::SigValue(ident, self.value(declaration, row.ident))
            }
            SignatureKind::Type => {
                let ident = self.ident(row.ident);
                let decl = self.type_declaration(declaration, row.ident);
                SignatureItem::SigType(ident, Arc::new(decl), rec_status(row.status))
            }
            SignatureKind::Extension => {
                let ident = self.ident(row.ident);
                let status = match row.status {
                    ItemStatus::Extension(ExtensionStatus::First) => ExtStatus::TextFirst,
                    ItemStatus::Extension(ExtensionStatus::Next) => ExtStatus::TextNext,
                    ItemStatus::Extension(ExtensionStatus::Exception) => ExtStatus::TextException,
                    other => panic!("{other:?} is not an extension status"),
                };
                SignatureItem::SigTypext(ident, self.extension(declaration), status)
            }
            SignatureKind::Module => {
                let ident = self.ident(row.ident);
                let module = self.pools.modules[declaration as usize];
                let decl = ModuleDeclaration {
                    md_type: take(module_types, module.module_type),
                    md_attributes: self.attributes(module.attributes),
                    md_loc: self.loc(module.loc),
                    md_path: self.declared(module.path, row.ident),
                };
                SignatureItem::SigModule(ident, decl, rec_status(row.status))
            }
            SignatureKind::ModuleType => {
                ordinary(row.status);
                let ident = self.ident(row.ident);
                let module = self.pools.modules[declaration as usize];
                debug_assert!(
                    self.declared(module.path, row.ident).is_none(),
                    "a module type declaration has no source path"
                );
                let decl = ModtypeDeclaration {
                    mtd_type: (module.module_type != NONE)
                        .then(|| take(module_types, module.module_type)),
                    mtd_attributes: self.attributes(module.attributes),
                    mtd_loc: self.loc(module.loc),
                };
                SignatureItem::SigModtype(ident, decl)
            }
            SignatureKind::Class => {
                ordinary(row.status);
                SignatureItem::SigClass
            }
            SignatureKind::ClassType => {
                ordinary(row.status);
                SignatureItem::SigClassType
            }
        }
    }

    /// O(its attributes and primitive).
    fn value(&mut self, row: u32, binder: u32) -> ValueDescription {
        let value = self.pools.values[row as usize];
        let val_kind = if value.primitive == NONE {
            ValueKind::ValReg
        } else {
            ValueKind::ValPrim(Arc::new(self.primitive(value.primitive)))
        };
        ValueDescription {
            val_type: self.root(value.ty),
            val_kind,
            val_loc: self.loc(value.loc),
            val_attributes: self.attributes(value.attributes).into(),
            val_path: self.declared(value.path, binder),
        }
    }

    /// O(the declaration's metadata).
    fn type_declaration(&mut self, row: u32, binder: u32) -> TypeDeclaration {
        let seg = self.seg;
        let pools = self.pools;
        let hot = seg.type_declarations[row as usize];
        let cold = pools.type_details[row as usize];
        assert_eq!(hot.params, cold.parameter_roots.start, "parameter roots");
        assert_eq!(hot.variance, cold.variance.start, "variance range");
        let type_manifest = self.opt_root(hot.manifest);
        assert_eq!(
            hot.flags & 16 != 0,
            type_manifest.is_some(),
            "abbreviation flag"
        );
        let members = slice(
            &seg.members,
            Range {
                start: hot.members,
                len: hot.member_len,
            },
        );
        let type_kind = match hot.kind {
            DeclarationKind::Abstract | DeclarationKind::Open => {
                assert!(members.is_empty() && cold.representation == NONE);
                if hot.kind == DeclarationKind::Open {
                    TypeKind::TypeOpen
                } else {
                    TypeKind::TypeAbstract
                }
            }
            DeclarationKind::Record => {
                let labels = members
                    .iter()
                    .map(|member| self.label(member.args))
                    .collect();
                let representation = self.record_representation(cold.representation);
                TypeKind::TypeRecord(SharedVec::new(labels), representation)
            }
            DeclarationKind::Variant => {
                let constructors = members
                    .iter()
                    .map(|member| self.constructor(member.args))
                    .collect();
                TypeKind::TypeVariant(
                    SharedVec::new(constructors),
                    self.layout(cold.representation),
                )
            }
        };
        let type_variance = slice(&pools.variance, cold.variance)
            .iter()
            .map(|&bits| Variance::from_bits(bits))
            .collect();
        let inlined = slice(&pools.inlined_records, cold.inlined_records);
        let mut type_inlined_types = Vec::with_capacity(inlined.len());
        for record in inlined {
            type_inlined_types.push(TypeInlinedType::Record {
                type_name: self.text(record.name).to_owned(),
                labels: self.labels(record.labels),
            });
        }
        // The levels were written with `as u32`; the flag says whether
        // they exist, so a level of -1 is not mistaken for NONE.
        let type_newtype_level =
            (hot.flags & 8 != 0).then_some((cold.newtype_level as i32, cold.scope_level as i32));
        TypeDeclaration {
            type_params: self.root_list(cold.parameter_roots),
            type_arity: i32::from(hot.arity),
            type_kind,
            type_private: private(hot.flags & 1 != 0),
            type_manifest,
            type_variance,
            type_newtype_level,
            type_loc: self.loc(hot.loc),
            type_attributes: self.attributes(cold.attributes),
            type_immediate: hot.flags & 2 != 0,
            type_representation: if hot.flags & 4 != 0 {
                TypeRepresentation::Unboxed
            } else {
                TypeRepresentation::Boxed
            },
            type_shape: self.shape(cold.shape),
            type_inlined_types,
            type_path: self.declared(hot.path, binder),
        }
    }

    /// O(1): the old layout of a layout row.
    fn layout(&self, row: u32) -> LayoutRef {
        assert!((row as usize) < self.layouts.len(), "a layout row");
        LayoutRef::from_usize(row as usize)
    }

    /// O(labels and their metadata).
    fn labels(&mut self, range: Range) -> Vec<LabelDeclaration> {
        (range.start..range.start + range.len)
            .map(|row| self.label(row))
            .collect()
    }

    /// O(the label's attributes).
    fn label(&mut self, row: u32) -> LabelDeclaration {
        let label = self.pools.labels[row as usize];
        LabelDeclaration {
            ld_id: self.ident(label.ident),
            ld_runtime_name: self.opt_string(label.runtime_name),
            ld_mutable: if label.mutable {
                MutableFlag::Mutable
            } else {
                MutableFlag::Immutable
            },
            ld_optional: label.optional,
            ld_type: self.root(label.ty),
            ld_loc: self.loc(label.loc),
            ld_attributes: self.attributes(label.attributes),
        }
    }

    /// O(the constructor's metadata).
    fn constructor(&mut self, row: u32) -> ConstructorDeclaration {
        let constructor = self.pools.constructors[row as usize];
        ConstructorDeclaration {
            cd_id: self.ident(constructor.ident),
            cd_runtime_tag: (constructor.runtime_tag != NONE)
                .then(|| self.literal(constructor.runtime_tag)),
            cd_args: self.constructor_arguments(constructor.arguments),
            cd_res: self.opt_root(constructor.result),
            cd_loc: self.loc(constructor.loc),
            cd_attributes: self.attributes(constructor.attributes),
        }
    }

    /// O(arguments).
    fn constructor_arguments(&mut self, row: u32) -> ConstructorArguments {
        match self.pools.constructor_arguments[row as usize] {
            ConstructorArgumentsRow::Tuple(roots) => {
                ConstructorArguments::CstrTuple(self.root_list(roots))
            }
            ConstructorArgumentsRow::Record(labels) => {
                ConstructorArguments::CstrRecord(self.labels(labels))
            }
        }
    }

    /// O(the extension's metadata).
    fn extension(&mut self, row: u32) -> ExtensionConstructor {
        let extension = self.pools.extensions[row as usize];
        ExtensionConstructor {
            ext_type_path: self.paths[extension.path as usize],
            ext_type_params: self.root_list(extension.parameters),
            ext_args: self.constructor_arguments(extension.arguments),
            ext_ret_type: self.opt_root(extension.result),
            ext_private: private(extension.private),
            ext_loc: self.loc(extension.loc),
            ext_attributes: self.attributes(extension.attributes),
            ext_is_exception: extension.exception,
        }
    }

    /// O(1) plus a string copy.
    fn record_representation(&self, row: u32) -> RecordRepresentation {
        match self.pools.record_representations[row as usize] {
            RecordRepresentationRow::Regular => RecordRepresentation::RecordRegular,
            RecordRepresentationRow::Array => RecordRepresentation::RecordArray,
            RecordRepresentationRow::Unboxed(value) => RecordRepresentation::RecordUnboxed(value),
            RecordRepresentationRow::Extension => RecordRepresentation::RecordExtension,
            RecordRepresentationRow::Inlined {
                name,
                position,
                layout,
            } => RecordRepresentation::RecordInlined {
                name: self.text(name).to_owned(),
                representation: ConstructorReference {
                    variant: self.layout(layout),
                    position: position as usize,
                },
            },
        }
    }

    /// O(attributes and payloads).
    fn attributes(&self, range: Range) -> Vec<Attribute> {
        slice(&self.pools.attributes, range)
            .iter()
            .map(|row| Attribute {
                attr_name: Located {
                    txt: self.text(row.name).to_owned(),
                    loc: self.loc(row.name_loc),
                },
                attr_payload: self.attribute_payload(row.payload),
                attr_loc: self.loc(row.loc),
            })
            .collect()
    }

    /// O(payload size).
    fn attribute_payload(&self, row: u32) -> AttributePayload {
        let pools = self.pools;
        match pools.attribute_payloads[row as usize] {
            AttributePayloadRow::Empty => AttributePayload::Empty,
            AttributePayloadRow::Str(text) => AttributePayload::Str(self.text(text).to_owned()),
            AttributePayloadRow::Int(value) => AttributePayload::Int(value),
            AttributePayloadRow::IntLiteral(text) => {
                AttributePayload::IntLiteral(self.text(text).to_owned())
            }
            AttributePayloadRow::Float(text) => AttributePayload::Float(self.text(text).to_owned()),
            AttributePayloadRow::BigInt(text) => {
                AttributePayload::BigInt(self.text(text).to_owned())
            }
            AttributePayloadRow::Bool(value) => AttributePayload::Bool(value),
            AttributePayloadRow::Ident(text) => AttributePayload::Ident(self.text(text).to_owned()),
            AttributePayloadRow::Deprecated(row) => {
                let row = pools.deprecations[row as usize];
                AttributePayload::Deprecated {
                    reason: match row.reason {
                        SemanticStringValue::Missing => Ok(None),
                        SemanticStringValue::Valid(text) => Ok(Some(self.text(text).to_owned())),
                        SemanticStringValue::Invalid(loc) => Err(self.loc(loc)),
                    },
                    can_be_automigrated: row.can_be_automigrated,
                    migrate: self.fragment(row.migrate),
                    migrate_in_pipe_chain: self.fragment(row.migrate_in_pipe_chain),
                }
            }
            AttributePayloadRow::Structure(pairs) => {
                AttributePayload::Structure(self.string_pairs(pairs))
            }
            AttributePayloadRow::SemanticString(row) => {
                let row = pools.semantic_strings[row as usize];
                let semantic = match row.value {
                    SemanticStringValue::Valid(text) => Ok(self.text(text).to_owned()),
                    SemanticStringValue::Invalid(loc) => Err(self.loc(loc)),
                    SemanticStringValue::Missing => {
                        panic!("a semantic string payload has a value")
                    }
                };
                AttributePayload::SemanticString(Box::new(SemanticStringPayload {
                    semantic,
                    braces: row.braces,
                    template: row.template,
                }))
            }
            AttributePayloadRow::StrTuple(texts) => {
                AttributePayload::StrTuple(self.string_list(texts))
            }
        }
    }

    /// O(fragment bytes); NONE for none.
    fn fragment(&self, row: u32) -> Option<MarshalFragment> {
        if row == NONE {
            return None;
        }
        let row = self.pools.marshal_fragments[row as usize];
        let bytes = row.bytes;
        Some(MarshalFragment {
            bytes: slice(&self.pools.bytes, bytes).to_vec(),
            objects: row.objects,
            size_32: row.size_32,
            size_64: row.size_64,
        })
    }

    /// O(the primitive's FFI description).
    fn primitive(&self, row: u32) -> PrimitiveDescription {
        let primitive = self.pools.primitives[row as usize];
        let prim_kind = match primitive.kind {
            PrimitiveKindRow::Intrinsic => PrimKind::KindIntrinsic,
            PrimitiveKindRow::External(row) => PrimKind::KindExternal(Arc::new(self.ffi(row))),
            PrimitiveKindRow::Inline(row) => {
                PrimKind::KindInlineConst(Box::new(self.inline_constant(row)))
            }
        };
        PrimitiveDescription {
            prim_name: self.text(primitive.name).to_owned(),
            prim_arity: primitive.arity,
            prim_kind,
            prim_native_float: primitive.native_float,
            prim_from_constructor: primitive.from_constructor,
        }
    }

    /// O(parameters and their descriptions).
    fn ffi(&self, row: u32) -> ffi::ExternalFfi {
        let pools = self.pools;
        match pools.ffi[row as usize] {
            FfiRow::Call {
                params: range,
                declaration,
                return_wrapper,
            } => {
                let params = slice(&pools.ffi_params, range)
                    .iter()
                    .map(|param| ffi::Param {
                        arg_type: self.ffi_attribute(param.attribute),
                        arg_label: match param.label {
                            FfiLabelRow::Labelled => ffi::LabelNoname::ArgLabel,
                            FfiLabelRow::Positional => ffi::LabelNoname::ArgEmpty,
                            FfiLabelRow::Optional => ffi::LabelNoname::ArgOptional,
                            other => panic!("{other:?} labels an object parameter, not a call's"),
                        },
                    })
                    .collect();
                let return_wrapper = match return_wrapper {
                    ReturnWrapperRow::Unset => ffi::ReturnWrapper::ReturnUnset,
                    ReturnWrapperRow::Identity => ffi::ReturnWrapper::ReturnIdentity,
                    ReturnWrapperRow::NullToOption => ffi::ReturnWrapper::ReturnNullToOpt,
                    ReturnWrapperRow::NullUndefinedToOption => {
                        ffi::ReturnWrapper::ReturnNullUndefinedToOpt
                    }
                };
                ffi::ExternalFfi::FfiBs(
                    params,
                    return_wrapper,
                    self.external_declaration(declaration),
                )
            }
            FfiRow::Object(range) => ffi::ExternalFfi::FfiObjCreate(
                slice(&pools.ffi_params, range)
                    .iter()
                    .map(|param| ffi::ObjParam {
                        obj_arg_type: self.ffi_attribute(param.attribute),
                        obj_arg_label: match param.label {
                            FfiLabelRow::ObjectEmpty => ffi::Label::ObjEmpty,
                            FfiLabelRow::ObjectLabel(name) => ffi::Label::ObjLabel {
                                name: self.text(name).to_owned(),
                            },
                            FfiLabelRow::ObjectOptional {
                                name,
                                no_nested_option,
                            } => ffi::Label::ObjOptional {
                                name: self.text(name).to_owned(),
                                for_sure_no_nested_option: no_nested_option,
                            },
                            other => panic!("{other:?} labels a call parameter, not an object's"),
                        },
                    })
                    .collect(),
            ),
        }
    }

    /// O(the description's pairs).
    fn ffi_attribute(&self, row: u32) -> ffi::Attr {
        let pools = self.pools;
        match pools.ffi_attributes[row as usize] {
            FfiAttributeRow::PolyVarString(pairs) => ffi::Attr::PolyVarString {
                descr: self.string_pairs(pairs),
            },
            FfiAttributeRow::PolyVar(range) => ffi::Attr::PolyVar {
                descr: (range != NONE).then(|| self.string_pairs(pools.ranges[range as usize])),
            },
            FfiAttributeRow::Int(range) => ffi::Attr::Int(
                slice(&pools.string_int_pairs, range)
                    .iter()
                    .map(|pair| (self.text(pair.name).to_owned(), pair.value))
                    .collect(),
            ),
            FfiAttributeRow::Constant(row) => {
                ffi::Attr::ArgCst(match pools.constant_arguments[row as usize] {
                    ConstantArgumentRow::Int(value) => ffi::Cst::ArgIntLit(value),
                    ConstantArgumentRow::String(text) => {
                        ffi::Cst::ArgStringLit(self.text(text).to_owned())
                    }
                    ConstantArgumentRow::Json(text) => {
                        ffi::Cst::ArgJsonLit(self.text(text).to_owned())
                    }
                })
            }
            FfiAttributeRow::Unit => ffi::Attr::ExternUnit,
            FfiAttributeRow::Nothing => ffi::Attr::Nothing,
            FfiAttributeRow::Ignore => ffi::Attr::Ignore,
            FfiAttributeRow::Unwrap => ffi::Attr::Unwrap,
        }
    }

    /// O(scopes and import attributes).
    fn external_declaration(&self, row: u32) -> ffi::ExternalDecl {
        let pools = self.pools;
        let declaration = pools.external_declarations[row as usize];
        let name = |text: u32| self.text(text).to_owned();
        let kind = match declaration.kind {
            ExternalKindRow::Value(text) => ffi::DeclKind::DeclVal { name: name(text) },
            ExternalKindRow::Send(text) => ffi::DeclKind::DeclSend { name: name(text) },
            ExternalKindRow::New(text) => ffi::DeclKind::DeclNew { name: name(text) },
            ExternalKindRow::Get(text) => ffi::DeclKind::DeclGet { name: name(text) },
            ExternalKindRow::Set(text) => ffi::DeclKind::DeclSet { name: name(text) },
            ExternalKindRow::GetIndex => ffi::DeclKind::DeclGetIndex,
            ExternalKindRow::SetIndex => ffi::DeclKind::DeclSetIndex,
        };
        let module_ = match declaration.module {
            ModuleSourceRow::Absent => None,
            ModuleSourceRow::Itself => Some(ffi::ModuleSource::ModuleItself),
            ModuleSourceRow::Named(row) => {
                let module = pools.external_modules[row as usize];
                Some(ffi::ModuleSource::ModuleNamed(ffi::ExternalModuleName {
                    bundle: name(module.bundle),
                    module_bind_name: if module.binding_hint == NONE {
                        ffi::ModuleBindName::PhintNothing
                    } else {
                        ffi::ModuleBindName::PhintName(name(module.binding_hint))
                    },
                    import_attributes: (module.import_attributes != NONE).then(|| {
                        self.string_pairs(pools.ranges[module.import_attributes as usize])
                    }),
                }))
            }
        };
        ffi::ExternalDecl {
            kind,
            module_,
            scopes: self.string_list(declaration.scopes),
            variadic: declaration.variadic,
            effective_arity: declaration.effective_arity,
        }
    }

    /// O(1) plus a string copy.
    fn inline_constant(&self, row: u32) -> ffi::InlineConst {
        match self.pools.inline_constants[row as usize] {
            InlineConstantRow::String(text) => {
                ffi::InlineConst::ConstString(self.text(text).to_owned())
            }
            InlineConstantRow::Bool(value) => ffi::InlineConst::ConstBool(value),
            InlineConstantRow::Int(value) => ffi::InlineConst::ConstInt(value),
            InlineConstantRow::Bigint { positive, digits } => ffi::InlineConst::ConstBigint {
                positive,
                digits: self.text(digits).to_owned(),
            },
            InlineConstantRow::Float(text) => {
                ffi::InlineConst::ConstFloat(self.text(text).to_owned())
            }
        }
    }
}

/// O(1): the rows of a pool range.
fn slice<T>(pool: &[T], range: Range) -> &[T] {
    &pool[range.start as usize..(range.start + range.len) as usize]
}

/// O(1): move a built nested signature or module type out of its table.
fn take<T>(table: &mut [Option<T>], index: u32) -> T {
    table[index as usize]
        .take()
        .expect("a nested signature or module type has one parent")
}

/// O(1).
fn private(private: bool) -> PrivateFlag {
    if private {
        PrivateFlag::Private
    } else {
        PrivateFlag::Public
    }
}

/// O(1).
fn rec_status(status: ItemStatus) -> OldRecStatus {
    match status {
        ItemStatus::Recursive(RecStatus::Not) => OldRecStatus::TrecNot,
        ItemStatus::Recursive(RecStatus::First) => OldRecStatus::TrecFirst,
        ItemStatus::Recursive(RecStatus::Next) => OldRecStatus::TrecNext,
        other => panic!("{other:?} is not a recursive status"),
    }
}

/// O(1).
fn ordinary(status: ItemStatus) {
    assert_eq!(status, ItemStatus::Ordinary, "an item without a status");
}

#[cfg(test)]
mod tests {
    //! Tests of [`super::to_old`]. Bridge tests may name old types.

    use super::*;
    use crate::tc::graph::Graph;
    use crate::tc::publish::publish;
    use crate::tc::steps;
    use crate::types::shared_store::SharedTypePool;

    const N: u32 = 10_000;
    const UNRESOLVED: StrIdx = StrIdx(u32::MAX);

    macro_rules! fixture {
        ($($field:ident: $ty:ty),* $(,)?) => {
            /// Segment metadata under construction, before the type graph.
            #[derive(Default)]
            struct Fixture {
                $($field: Vec<$ty>,)*
                type_declarations: Vec<TypeDecl>,
                members: Vec<MemberDecl>,
            }

            impl Fixture {
                /// O(rows): the metadata as a segment with no type pools.
                fn into_segment(self, unit: UnitRow) -> Segment {
                    Segment {
                        type_declarations: self.type_declarations.into(),
                        members: self.members.into(),
                        signature: SignaturePools {
                            unit: Some(unit),
                            $($field: self.$field.into(),)*
                            roots: Box::default(),
                        },
                        ..Segment::default()
                    }
                }
            }
        };
    }

    fixture!(
        bytes: u8, strings: Range, ranges: Range, indices: u32, identifiers: IdentRow,
        paths: PathRow, longidents: LongidentRow, ordered_items: SignatureItemRow,
        signatures: Range, values: ValueRow, modules: ModuleRow, module_types: ModuleTypeRow,
        type_details: TypeDetailsRow, inlined_records: InlinedRecordRow,
        record_representations: RecordRepresentationRow, labels: LabelRow,
        constructor_arguments: ConstructorArgumentsRow, constructors: ConstructorRow,
        extensions: ExtensionRow, block_types: BlockTypeRow, shapes: ShapeRow,
        literals: LiteralRow, layouts: LayoutRow, runtime_constructors: RuntimeConstructorRow,
        attributes: AttributeRow, attribute_payloads: AttributePayloadRow,
        semantic_strings: SemanticStringRow, deprecations: DeprecatedRow,
        string_pairs: StringPair, string_int_pairs: StringIntPair,
        marshal_fragments: MarshalFragmentRow, primitives: PrimitiveRow,
        constant_arguments: ConstantArgumentRow, ffi_attributes: FfiAttributeRow,
        ffi_params: FfiParamRow, ffi: FfiRow, external_declarations: ExternalDeclRow,
        external_modules: ExternalModuleRow, inline_constants: InlineConstantRow,
        variants: VariantRow, row_fields: RowFieldRow, packages: PackageRow, variance: u8,
        locations: LocationRow, descriptor_extras: ExtraDescriptor, mutabilities: bool,
    );

    /// Amortized O(1): append a row and return its index.
    fn add<T>(pool: &mut Vec<T>, row: T) -> u32 {
        pool.push(row);
        (pool.len() - 1) as u32
    }

    impl Fixture {
        /// O(length): a new string row.
        fn string(&mut self, text: &str) -> u32 {
            let start = self.bytes.len() as u32;
            self.bytes.extend_from_slice(text.as_bytes());
            add(
                &mut self.strings,
                Range {
                    start,
                    len: text.len() as u32,
                },
            )
        }

        /// O(1): the unit `Test`, identifier 0 and path 0, whose signature is
        /// signature row 0.
        fn unit(&mut self) -> UnitRow {
            let name = self.string("Test");
            let ident = add(
                &mut self.identifiers,
                IdentRow {
                    name,
                    stamp: 0,
                    flags: u32::from(IdentFlags::GLOBAL.bits()),
                    scope: UNIT_SCOPE,
                },
            );
            let path = add(&mut self.paths, PathRow::Ident(ident));
            add(&mut self.signatures, Range::default());
            UnitRow {
                name,
                deprecated: NONE,
                signature: 0,
                path,
            }
        }

        /// O(1): a location; line 0 is coordinate-free.
        fn loc(&mut self, file: Option<&str>, line: i32) -> u32 {
            let filename = match file {
                Some(file) => self.string(file),
                None => NONE,
            };
            let position = PositionRow {
                filename,
                line,
                beginning_of_line: 0,
                offset: line * 10,
            };
            add(
                &mut self.locations,
                LocationRow {
                    start: position,
                    end: PositionRow {
                        offset: position.offset + 1 - i32::from(line == 0),
                        ..position
                    },
                    origin: 0,
                    ghost: line == 0,
                },
            )
        }

        /// O(1): an identifier row.
        fn ident(&mut self, name: &str, stamp: i32, scope: u32) -> u32 {
            let name = self.string(name);
            add(
                &mut self.identifiers,
                IdentRow {
                    name,
                    stamp,
                    flags: 0,
                    scope,
                },
            )
        }

        /// O(1): an item's binder and its binder-address path.
        fn binder(&mut self, name: &str, stamp: i32) -> (u32, u32) {
            let scope = self.ordered_items.len() as u32;
            let ident = self.ident(name, stamp, scope);
            (ident, add(&mut self.paths, PathRow::Ident(ident)))
        }

        /// O(1): append a value item whose type is root `ty`.
        fn value(&mut self, name: &str, stamp: i32, ty: u32) -> u32 {
            let (ident, path) = self.binder(name, stamp);
            let loc = self.loc(None, 0);
            let declaration = add(
                &mut self.values,
                ValueRow {
                    ty,
                    primitive: NONE,
                    attributes: Range::default(),
                    loc,
                    path,
                },
            );
            add(
                &mut self.ordered_items,
                SignatureItemRow {
                    ident,
                    declaration,
                    kind: SignatureKind::Value,
                    status: ItemStatus::Ordinary,
                },
            )
        }

        /// O(1): close signature row `index` over the items from `start`.
        fn close(&mut self, index: u32, start: u32) {
            self.signatures[index as usize] = Range {
                start,
                len: self.ordered_items.len() as u32 - start,
            };
        }
    }

    /// O(1).
    fn var(graph: &mut Graph, level: u32) -> Ty {
        graph.push(Node {
            head: VAR,
            level,
            a: NONE,
            b: 0,
        })
    }

    /// O(children).
    fn listed(graph: &mut Graph, head: u32, level: u32, a: u32, children: &[Ty]) -> Ty {
        let b = graph.lists.len() as u32;
        graph.lists.extend_from_slice(children);
        graph.push(Node {
            head: head | (children.len() as u32) << 8,
            level,
            a,
            b,
        })
    }

    /// O(children).
    fn tuple(graph: &mut Graph, level: u32, children: &[Ty]) -> Ty {
        listed(graph, TUPLE, level, 0, children)
    }

    /// O(children): an extended descriptor with payload row `extra`.
    fn extended(graph: &mut Graph, level: u32, extra: u32, children: &[Ty]) -> Ty {
        listed(graph, TUPLE | EXTENDED, level, extra, children)
    }

    /// O(arguments).
    fn constr(graph: &mut Graph, level: u32, path: u32, args: &[Ty]) -> Ty {
        let b = graph.lists.len() as u32;
        graph.lists.push(Ty(NONE));
        graph.lists.extend_from_slice(args);
        graph.push(Node {
            head: CONSTR | (args.len() as u32) << 8,
            level,
            a: path,
            b,
        })
    }

    /// O(nodes): publish one scheme per item, as `from_old` does, with a
    /// synthetic tuple for an item of several roots, then name the roots as
    /// `from_old::resolve_roots` does.
    fn finish(mut graph: Graph, schemes: &[&[Ty]], fixture: Fixture, unit: UnitRow) -> Segment {
        let mut publish_roots = Vec::new();
        for roots in schemes {
            if let [root] = roots {
                publish_roots.push(*root);
                continue;
            }
            publish_roots.push(tuple(&mut graph, GENERIC, roots));
        }
        let mut segment = publish(graph, &publish_roots, fixture.into_segment(unit));
        let mut out = Vec::new();
        let mut lists = 0usize;
        for (index, roots) in schemes.iter().enumerate() {
            let template = segment.templates[index];
            if roots.len() == 1 {
                let ty = if template.node_len == 0 {
                    Ty(template.nodes)
                } else {
                    Ty(RELATIVE)
                };
                out.push(SchemeRoot {
                    template: index as u32,
                    ty,
                });
            } else {
                for &reference in &segment.template_lists[lists..lists + roots.len()] {
                    let ty = if reference.0 & RELATIVE != 0 {
                        reference
                    } else {
                        segment.template_externals[reference.0 as usize]
                    };
                    out.push(SchemeRoot {
                        template: index as u32,
                        ty,
                    });
                }
            }
            lists += template.list_len as usize;
        }
        segment.signature.roots = out.into();
        segment
    }

    /// O(1): an old node's descriptor.
    fn desc(graph: &SharedGraph, r: TypeExprRef) -> TypeDesc {
        graph.nodes()[graph.node_offset(r).expect("a node of the graph")].desc
    }

    /// O(1): an old node's level.
    fn level(graph: &SharedGraph, r: TypeExprRef) -> i32 {
        graph.nodes()[graph.node_offset(r).expect("a node of the graph")].level
    }

    /// O(1): the type of a value item.
    fn value_type(item: &SignatureItem) -> TypeExprRef {
        match item {
            SignatureItem::SigValue(_, decl) => decl.val_type,
            other => panic!("not a value: {other:?}"),
        }
    }

    /// Drop deep old values where their recursive destructors have room.
    fn drop_on_a_large_stack<T: Send + 'static>(value: T) {
        std::thread::Builder::new()
            .stack_size(256 * 1024 * 1024)
            .spawn(move || drop(value))
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn sizes() {
        assert_eq!(std::mem::size_of::<Frame>(), 16);
        assert_eq!(std::mem::size_of::<LidTask>(), 8);
        assert_eq!(std::mem::size_of::<SigTask>(), 8);
        assert_eq!(std::mem::size_of::<Output>(), 104);
        assert_eq!(std::mem::size_of::<Visits>(), 8);
        assert_eq!(std::mem::size_of::<Rebuild<'static>>(), 584);
    }

    #[test]
    fn equal_nodes_stay_distinct_and_repeated_positions_stay_shared() {
        // let x: ('a, 'a, 'b, '_w); let y: '_w; let z: '_w; type t<'p> = ('p, 'p)
        let mut graph = Graph::default();
        let a = var(&mut graph, GENERIC);
        let b = var(&mut graph, GENERIC);
        let weak = var(&mut graph, 3);
        let x = tuple(&mut graph, GENERIC, &[a, a, b, weak]);
        let parameter = var(&mut graph, GENERIC);
        let manifest = tuple(&mut graph, GENERIC, &[parameter, parameter]);
        let mut f = Fixture::default();
        let unit = f.unit();
        // Roots: 0 x, 1 y, 2 z, 3 t's parameter, 4 t's manifest.
        f.value("x", 1, 0);
        f.value("y", 2, 1);
        f.value("z", 3, 2);
        let (ident, path) = f.binder("t", 4);
        let loc = f.loc(None, 0);
        let shape = add(&mut f.shapes, ShapeRow::Unstated);
        let variance = add(&mut f.variance, Variance::full().bits());
        let declaration = add(
            &mut f.type_declarations,
            TypeDecl {
                kind: DeclarationKind::Abstract,
                flags: 16,
                arity: 1,
                params: 3,
                manifest: 4,
                members: 0,
                member_len: 0,
                path,
                loc,
                variance,
            },
        );
        add(
            &mut f.type_details,
            TypeDetailsRow {
                parameter_roots: Range { start: 3, len: 1 },
                variance: Range {
                    start: variance,
                    len: 1,
                },
                attributes: Range::default(),
                inlined_records: Range::default(),
                representation: NONE,
                shape,
                newtype_level: NONE,
                scope_level: NONE,
            },
        );
        add(
            &mut f.ordered_items,
            SignatureItemRow {
                ident,
                declaration,
                kind: SignatureKind::Type,
                status: ItemStatus::Recursive(RecStatus::Not),
            },
        );
        f.close(0, 0);
        let segment = finish(
            graph,
            &[&[x], &[weak], &[weak], &[parameter, manifest]],
            f,
            unit,
        );
        let (output, visits) = run(&segment);
        // One shared node, three nodes of x's template, and t's parameter and
        // manifest: the synthetic tuple has no old node.
        assert_eq!(visits.count, 6);
        let published = output.into_published();
        let graph = &published.graph;
        assert!(graph.is_detached());
        assert_eq!(graph.nodes().len(), 6);
        let signature = &published.signature;
        let TypeDesc::Ttuple(list) = desc(graph, value_type(&signature[0])) else {
            panic!("x is a tuple");
        };
        let slots = graph.list(list);
        assert_eq!(slots.len(), 4);
        assert_eq!(slots[0], slots[1], "a repeated position stays one node");
        assert_ne!(slots[0], slots[2], "an equal node stays distinct");
        assert_eq!(slots[3], value_type(&signature[1]));
        assert_eq!(slots[3], value_type(&signature[2]));
        assert_eq!(level(graph, value_type(&signature[0])), GENERIC_LEVEL);
        assert_eq!(level(graph, slots[0]), GENERIC_LEVEL);
        assert_eq!(level(graph, slots[3]), 3);
        let SignatureItem::SigType(id, decl, OldRecStatus::TrecNot) = &signature[3] else {
            panic!("t is a type");
        };
        assert_eq!((id.name(), id.stamp()), ("t", 4));
        assert!(decl.type_path.is_none(), "an absent path comes back absent");
        assert_eq!(decl.type_params.len(), 1);
        let TypeDesc::Ttuple(list) = desc(graph, decl.type_manifest.unwrap()) else {
            panic!("t's manifest is a tuple");
        };
        assert_eq!(
            graph.list(list),
            &[decl.type_params[0], decl.type_params[0]]
        );
        assert_eq!(decl.type_variance[0].bits(), Variance::full().bits());
    }

    #[test]
    fn ten_thousand_deep_types_make_one_old_node_per_node_on_a_two_mb_stack() {
        std::thread::Builder::new()
            .stack_size(2 * 1024 * 1024)
            .spawn(|| {
                let mut graph = Graph::default();
                let mut chains = [Ty(0); 2];
                for (chain, level) in chains.iter_mut().zip([GENERIC, 1]) {
                    *chain = var(&mut graph, level);
                    for _ in 1..N {
                        *chain = tuple(&mut graph, level, &[*chain]);
                    }
                }
                let mut f = Fixture::default();
                let unit = f.unit();
                f.value("generic", 1, 0);
                f.value("local", 2, 1);
                f.close(0, 0);
                let segment = finish(graph, &[&[chains[0]], &[chains[1]]], f, unit);
                assert_eq!(segment.template_nodes.len(), N as usize);
                assert_eq!(segment.nodes.len(), N as usize);
                let mut result = None;
                let count = steps::scope(|| result = Some(run(&segment)));
                let (output, visits) = result.unwrap();
                assert_eq!(visits.count, 2 * u64::from(N));
                // 2N nodes, 2(N - 1) list slots, two items, three paths and two
                // locations.
                assert_eq!(count, 4 * u64::from(N) + 5);
                let published = output.into_published();
                let graph = &published.graph;
                for (item, expected) in published.signature.iter().zip([GENERIC_LEVEL, 1]) {
                    let mut ty = value_type(item);
                    for _ in 1..N {
                        assert_eq!(level(graph, ty), expected);
                        let TypeDesc::Ttuple(list) = desc(graph, ty) else {
                            panic!("a chain link is a tuple");
                        };
                        ty = graph.list(list)[0];
                    }
                    assert!(matches!(desc(graph, ty), TypeDesc::Tvar(None)));
                }
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn ten_thousand_nested_modules_on_a_two_mb_stack() {
        let output = std::thread::Builder::new()
            .stack_size(2 * 1024 * 1024)
            .spawn(|| {
                let mut f = Fixture::default();
                let unit = f.unit();
                for i in 0..N {
                    let (ident, path) = f.binder("M", i as i32 + 1);
                    let loc = f.loc(None, 0);
                    let signature = add(&mut f.signatures, Range::default());
                    let module_type = add(&mut f.module_types, ModuleTypeRow::Signature(signature));
                    let declaration = add(
                        &mut f.modules,
                        ModuleRow {
                            module_type,
                            attributes: Range::default(),
                            loc,
                            path,
                        },
                    );
                    let start = f.ordered_items.len() as u32;
                    add(
                        &mut f.ordered_items,
                        SignatureItemRow {
                            ident,
                            declaration,
                            kind: SignatureKind::Module,
                            status: ItemStatus::Recursive(RecStatus::Not),
                        },
                    );
                    f.close(signature - 1, start);
                }
                let segment = f.into_segment(unit);
                let mut result = None;
                let count = steps::scope(|| result = Some(run(&segment)));
                // Per level one path, one location, one item and one module type.
                assert_eq!(count, 4 * u64::from(N) + 1);
                let (output, visits) = result.unwrap();
                assert_eq!(visits.count, 0);
                let mut signature: &Signature = output.signature();
                for i in 0..N {
                    let [SignatureItem::SigModule(id, decl, OldRecStatus::TrecNot)] =
                        &signature[..]
                    else {
                        panic!("one module per level");
                    };
                    assert_eq!(id.stamp(), i as i32 + 1);
                    assert!(decl.md_path.is_none());
                    let ModuleType::MtySignature(inner) = &decl.md_type else {
                        panic!("a nested signature");
                    };
                    signature = &**inner;
                }
                assert!(signature.is_empty());
                output
            })
            .unwrap()
            .join()
            .unwrap();
        drop_on_a_large_stack(output);
    }

    #[test]
    fn ten_thousand_deep_paths_and_longidents_on_a_two_mb_stack() {
        let lid = std::thread::Builder::new()
            .stack_size(2 * 1024 * 1024)
            .spawn(|| {
                let mut f = Fixture::default();
                let unit = f.unit();
                let name = f.string("M");
                for i in 0..N {
                    add(
                        &mut f.paths,
                        PathRow::Dot {
                            parent: unit.path + i,
                            name,
                            position: i as i32,
                        },
                    );
                }
                add(&mut f.longidents, LongidentRow::Ident(name));
                for i in 1..N {
                    add(
                        &mut f.longidents,
                        LongidentRow::Dot {
                            parent: i - 1,
                            name,
                        },
                    );
                }
                f.close(0, 0);
                let segment = f.into_segment(unit);
                let mut rebuild = Rebuild::new(&segment);
                assert_eq!(steps::scope(|| rebuild.paths()), u64::from(N) + 1);
                let mut path = rebuild.paths[N as usize];
                for i in (0..N).rev() {
                    let crate::types::path::PathView::Pdot(parent, name, position) = *path.view()
                    else {
                        panic!("a dotted path");
                    };
                    assert_eq!((name.as_str(), position), ("M", i as i32));
                    path = parent;
                }
                assert_eq!(path, rebuild.paths[0]);
                let mut lid = None;
                assert_eq!(
                    steps::scope(|| lid = Some(rebuild.longident(N - 1))),
                    u64::from(N)
                );
                let lid = lid.unwrap();
                let mut at = &lid;
                for _ in 1..N {
                    let Longident::Ldot(prefix, name) = at else {
                        panic!("a dotted longident");
                    };
                    assert_eq!(*name, StrIdx::from_raw(0));
                    at = &**prefix;
                }
                assert_eq!(*at, Longident::Lident(StrIdx::from_raw(0)));
                assert_eq!(rebuild.components, ["M"]);
                lid
            })
            .unwrap()
            .join()
            .unwrap();
        drop_on_a_large_stack(lid);
    }

    #[test]
    fn every_extended_descriptor_maps_to_its_old_descriptor() {
        let mut f = Fixture::default();
        let unit = f.unit();
        let int = f.ident("int", 0, NONE);
        let int = add(&mut f.paths, PathRow::Ident(int));
        let name = f.string("name");
        let a = f.string("a");
        let x = f.string("x");
        let y = f.string("y");
        let label_loc = f.loc(Some("File.res"), 3);
        let mut graph = Graph::default();
        let extra = |f: &mut Fixture, row: ExtraDescriptor| add(&mut f.descriptor_extras, row);

        // {"name": int}
        let string = constr(&mut graph, GENERIC, int, &[]);
        let nil = extra(&mut f, ExtraDescriptor::Nil);
        let nil = extended(&mut graph, GENERIC, nil, &[]);
        let mutability = add(&mut f.mutabilities, true);
        let field = extra(&mut f, ExtraDescriptor::Field { name, mutability });
        let field = extended(&mut graph, GENERIC, field, &[string, nil]);
        let object = extra(&mut f, ExtraDescriptor::Object);
        let object = extended(&mut graph, GENERIC, object, &[field]);

        // 'a. ('a, ~x: 'a, ?y: 'a) => 'a
        let univar = extra(&mut f, ExtraDescriptor::Univar(a));
        let univar = extended(&mut graph, GENERIC, univar, &[]);
        let start = graph.params.len() as u32;
        graph.params.extend([
            Param {
                ty: univar,
                label: NONE,
                loc: NONE,
            },
            Param {
                ty: univar,
                label: x << 1,
                loc: label_loc,
            },
            Param {
                ty: univar,
                label: y << 1 | 1,
                loc: label_loc,
            },
        ]);
        let arrow = graph.push(Node {
            head: ARROW | 3 << 8,
            level: GENERIC,
            a: univar.0,
            b: start,
        });
        let poly = extra(&mut f, ExtraDescriptor::Poly);
        let poly = extended(&mut graph, GENERIC, poly, &[arrow, univar]);

        // [< #A(int) | #B | -#C | #D(int & int) ] as 'more, named int<int>
        let argument = constr(&mut graph, GENERIC, int, &[]);
        let more = var(&mut graph, GENERIC);
        let fields = f.row_fields.len() as u32;
        for (label, types, kind) in [
            ("A", Range { start: 0, len: 1 }, RowFieldKind::Present),
            ("B", Range { start: 1, len: 0 }, RowFieldKind::Present),
            ("C", Range { start: 1, len: 0 }, RowFieldKind::Absent),
            (
                "D",
                Range { start: 1, len: 2 },
                RowFieldKind::Either {
                    constant: false,
                    matched: true,
                },
            ),
        ] {
            let name = f.string(label);
            add(
                &mut f.row_fields,
                RowFieldRow {
                    name,
                    types,
                    link: NONE,
                    kind,
                },
            );
        }
        let row = add(
            &mut f.variants,
            VariantRow {
                fields: Range {
                    start: fields,
                    len: 4,
                },
                more: 3,
                name: int,
                name_arguments: Range { start: 4, len: 1 },
                closed: true,
                fixed: false,
            },
        );
        let row = extra(&mut f, ExtraDescriptor::Variant(row));
        let variant = extended(
            &mut graph,
            GENERIC,
            row,
            &[argument, argument, argument, more, argument],
        );

        // module(M.N with F(X), <unresolved>, M.<unresolved>) with one argument
        let m = f.string("M");
        let n = f.string("N");
        let functor = f.string("F");
        let argument_name = f.string("X");
        let lid_m = add(&mut f.longidents, LongidentRow::Ident(m));
        let lid_mn = add(
            &mut f.longidents,
            LongidentRow::Dot {
                parent: lid_m,
                name: n,
            },
        );
        let lid_f = add(&mut f.longidents, LongidentRow::Ident(functor));
        let lid_x = add(&mut f.longidents, LongidentRow::Ident(argument_name));
        let lid_fx = add(
            &mut f.longidents,
            LongidentRow::Apply {
                functor: lid_f,
                argument: lid_x,
            },
        );
        let lid_unresolved = add(
            &mut f.longidents,
            LongidentRow::Unresolved(UNRESOLVED.raw()),
        );
        let lid_m_unresolved = add(
            &mut f.longidents,
            LongidentRow::UnresolvedDot {
                parent: lid_m,
                raw: UNRESOLVED.raw(),
            },
        );
        let lids = f.indices.len() as u32;
        f.indices
            .extend([lid_mn, lid_fx, lid_unresolved, lid_m_unresolved]);
        let package = add(
            &mut f.packages,
            PackageRow {
                path: int,
                longidents: Range {
                    start: lids,
                    len: 4,
                },
                arguments: Range { start: 0, len: 1 },
            },
        );
        let package = extra(&mut f, ExtraDescriptor::Package(package));
        let package_argument = constr(&mut graph, GENERIC, int, &[]);
        let package = extended(&mut graph, GENERIC, package, &[package_argument]);

        // A substitution marker, and a shared (non-generic) empty object.
        let target = var(&mut graph, GENERIC);
        let substitution = extra(&mut f, ExtraDescriptor::Substitution);
        let substitution = extended(&mut graph, GENERIC, substitution, &[target]);
        let local_nil = extra(&mut f, ExtraDescriptor::Nil);
        let local_nil = extended(&mut graph, 2, local_nil, &[]);
        let local_object = extra(&mut f, ExtraDescriptor::Object);
        let local_object = extended(&mut graph, 2, local_object, &[local_nil]);

        for (index, name) in ["object", "poly", "variant", "package", "subst", "local"]
            .into_iter()
            .enumerate()
        {
            f.value(name, index as i32 + 1, index as u32);
        }
        f.close(0, 0);
        let segment = finish(
            graph,
            &[
                &[object],
                &[poly],
                &[variant],
                &[package],
                &[substitution],
                &[local_object],
            ],
            f,
            unit,
        );
        let published = to_old(&segment).into_published();
        let graph = &published.graph;
        let signature = &published.signature;
        let names = published.names.read().unwrap();

        let TypeDesc::Tobject { fields } = desc(graph, value_type(&signature[0])) else {
            panic!("an object");
        };
        let TypeDesc::Tfield {
            name,
            mutability,
            typ,
            rest,
        } = desc(graph, fields)
        else {
            panic!("a field");
        };
        assert_eq!(name.as_str(), "name");
        assert!(mutability.is_persistent());
        assert_eq!(mutability.persistent_value(), MutableFlag::Mutable);
        assert!(matches!(desc(graph, typ), TypeDesc::Tconstr { .. }));
        assert!(matches!(desc(graph, rest), TypeDesc::Tnil));

        let TypeDesc::Tpoly { body, vars } = desc(graph, value_type(&signature[1])) else {
            panic!("a polytype");
        };
        let vars = graph.list(vars);
        assert_eq!(vars.len(), 1);
        assert!(matches!(desc(graph, vars[0]), TypeDesc::Tunivar(Some(a)) if a.as_str() == "a"));
        let TypeDesc::Tarrow { args, ret } = desc(graph, body) else {
            panic!("an arrow");
        };
        assert_eq!(ret, vars[0]);
        let args = graph.args(args);
        assert_eq!(args.len(), 3);
        assert!(args.iter().all(|arg| arg.typ == vars[0]));
        assert!(args[0].label().is_nolabel());
        assert_eq!(args[0].label().loc(), DeclLoc::none());
        assert!(args[1].label().is_labelled());
        assert_eq!(args[1].label().label_name(), Some("x"));
        assert!(args[2].label().is_optional());
        assert_eq!(args[2].label().label_name(), Some("y"));
        let loc = args[1].label().loc();
        assert_eq!(loc.kind(), DeclLocKind::Portable);
        let location = graph.locations().get(loc.index());
        assert_eq!((location.loc_start.line, location.loc_start.cnum), (3, 30));
        let file = location.loc_start.file_name.raw();
        assert!(
            graph
                .carried
                .file_names
                .iter()
                .any(|(key, name)| *key == file && name == "File.res")
        );

        let TypeDesc::Tvariant(row) = desc(graph, value_type(&signature[2])) else {
            panic!("a variant");
        };
        let row = graph.row(row);
        assert!(row.row_closed && !row.row_fixed);
        assert!(matches!(desc(graph, row.row_more), TypeDesc::Tvar(None)));
        let labels: Vec<&str> = row
            .row_fields
            .iter()
            .map(|(label, _)| label.as_str())
            .collect();
        assert_eq!(labels, ["A", "B", "C", "D"]);
        let RowField::Rpresent(Some(present)) = &row.row_fields[0].1 else {
            panic!("a present field with an argument");
        };
        assert!(matches!(row.row_fields[1].1, RowField::Rpresent(None)));
        assert!(matches!(row.row_fields[2].1, RowField::Rabsent));
        let RowField::Reither {
            constant: false,
            types,
            matched: true,
            link,
        } = &row.row_fields[3].1
        else {
            panic!("an either field");
        };
        assert_eq!(types, &[*present, *present], "one node in every position");
        assert_eq!(*link, RowFieldRef::null());
        let (row_path, row_arguments) = row.row_name.as_ref().expect("a named row");
        assert_eq!(row_path.name(), "int");
        assert_eq!(row_arguments, &[*present]);

        let TypeDesc::Tpackage { path, lids, args } = desc(graph, value_type(&signature[3])) else {
            panic!("a package");
        };
        assert_eq!(path.name(), "int");
        assert_eq!(graph.list(args).len(), 1);
        let text = |name: StrIdx| names.get(&name.raw()).map(String::as_str);
        let lids = graph.lids(lids);
        assert_eq!(lids.len(), 4);
        let Longident::Ldot(prefix, last) = &lids[0] else {
            panic!("M.N");
        };
        assert_eq!(**prefix, Longident::Lident(StrIdx::from_raw(0)));
        assert_eq!(
            (text(StrIdx::from_raw(0)), text(*last)),
            (Some("M"), Some("N"))
        );
        let Longident::Lapply(f_lid, x_lid) = &lids[1] else {
            panic!("F(X)");
        };
        let (Longident::Lident(f_name), Longident::Lident(x_name)) = (&**f_lid, &**x_lid) else {
            panic!("F and X are identifiers");
        };
        assert_eq!((text(*f_name), text(*x_name)), (Some("F"), Some("X")));
        assert_eq!(lids[2], Longident::Lident(UNRESOLVED));
        assert_eq!(text(UNRESOLVED), None);
        assert!(matches!(&lids[3], Longident::Ldot(_, name) if *name == UNRESOLVED));

        let TypeDesc::Tsubst(target) = desc(graph, value_type(&signature[4])) else {
            panic!("a substitution");
        };
        assert!(matches!(desc(graph, target), TypeDesc::Tvar(None)));

        let local = value_type(&signature[5]);
        assert_eq!(level(graph, local), 2);
        let TypeDesc::Tobject { fields } = desc(graph, local) else {
            panic!("a shared object");
        };
        assert!(matches!(desc(graph, fields), TypeDesc::Tnil));
        assert_eq!(level(graph, fields), 2);
    }

    #[test]
    fn every_metadata_variant_maps_to_its_old_variant() {
        let mut f = Fixture::default();
        let unit = f.unit();
        let text = f.string("text");
        let other = f.string("other");
        let plain = f.loc(None, 0);
        let located = f.loc(Some("File.res"), 7);

        // Attribute payloads.
        let pair = add(
            &mut f.string_pairs,
            StringPair {
                first: text,
                second: other,
            },
        );
        let pairs = Range {
            start: pair,
            len: 1,
        };
        let tuple = f.indices.len() as u32;
        f.indices.extend([text, other]);
        let strings = Range {
            start: tuple,
            len: 2,
        };
        let fragment_bytes = f.bytes.len() as u32;
        f.bytes.extend_from_slice(&[0, 255, 7]);
        let fragment = add(
            &mut f.marshal_fragments,
            MarshalFragmentRow {
                bytes: Range {
                    start: fragment_bytes,
                    len: 3,
                },
                objects: 1,
                size_32: 2,
                size_64: 3,
            },
        );
        let deprecated = |f: &mut Fixture, reason: SemanticStringValue| {
            add(
                &mut f.deprecations,
                DeprecatedRow {
                    reason,
                    migrate: fragment,
                    migrate_in_pipe_chain: NONE,
                    can_be_automigrated: true,
                },
            )
        };
        let missing = deprecated(&mut f, SemanticStringValue::Missing);
        let valid = deprecated(&mut f, SemanticStringValue::Valid(text));
        let invalid = deprecated(&mut f, SemanticStringValue::Invalid(located));
        let semantic_valid = add(
            &mut f.semantic_strings,
            SemanticStringRow {
                value: SemanticStringValue::Valid(text),
                braces: 2,
                template: true,
            },
        );
        let semantic_invalid = add(
            &mut f.semantic_strings,
            SemanticStringRow {
                value: SemanticStringValue::Invalid(plain),
                braces: 0,
                template: false,
            },
        );
        let payloads = [
            AttributePayloadRow::Empty,
            AttributePayloadRow::Str(text),
            AttributePayloadRow::Int(-3),
            AttributePayloadRow::IntLiteral(text),
            AttributePayloadRow::Float(text),
            AttributePayloadRow::BigInt(text),
            AttributePayloadRow::Bool(true),
            AttributePayloadRow::Ident(text),
            AttributePayloadRow::Deprecated(missing),
            AttributePayloadRow::Deprecated(valid),
            AttributePayloadRow::Deprecated(invalid),
            AttributePayloadRow::Structure(pairs),
            AttributePayloadRow::SemanticString(semantic_valid),
            AttributePayloadRow::SemanticString(semantic_invalid),
            AttributePayloadRow::StrTuple(strings),
        ];
        let first_payload = f.attribute_payloads.len() as u32;
        f.attribute_payloads.extend(payloads);
        let attribute = add(
            &mut f.attributes,
            AttributeRow {
                name: other,
                payload: first_payload + 1,
                name_loc: located,
                loc: plain,
            },
        );

        // FFI descriptions.
        let int_pair = add(
            &mut f.string_int_pairs,
            StringIntPair {
                name: text,
                value: 5,
            },
        );
        let ranged = add(&mut f.ranges, pairs);
        let constants = [
            ConstantArgumentRow::Int(9),
            ConstantArgumentRow::String(text),
            ConstantArgumentRow::Json(other),
        ]
        .map(|row| add(&mut f.constant_arguments, row));
        let attrs = [
            FfiAttributeRow::PolyVarString(pairs),
            FfiAttributeRow::PolyVar(NONE),
            FfiAttributeRow::PolyVar(ranged),
            FfiAttributeRow::Int(Range {
                start: int_pair,
                len: 1,
            }),
            FfiAttributeRow::Constant(constants[0]),
            FfiAttributeRow::Constant(constants[1]),
            FfiAttributeRow::Constant(constants[2]),
            FfiAttributeRow::Unit,
            FfiAttributeRow::Nothing,
            FfiAttributeRow::Ignore,
            FfiAttributeRow::Unwrap,
        ]
        .map(|row| add(&mut f.ffi_attributes, row));
        let call_params = f.ffi_params.len() as u32;
        for label in [
            FfiLabelRow::Labelled,
            FfiLabelRow::Positional,
            FfiLabelRow::Optional,
        ] {
            add(
                &mut f.ffi_params,
                FfiParamRow {
                    attribute: attrs[0],
                    label,
                },
            );
        }
        let object_params = f.ffi_params.len() as u32;
        for label in [
            FfiLabelRow::ObjectEmpty,
            FfiLabelRow::ObjectLabel(text),
            FfiLabelRow::ObjectOptional {
                name: other,
                no_nested_option: true,
            },
        ] {
            add(
                &mut f.ffi_params,
                FfiParamRow {
                    attribute: attrs[8],
                    label,
                },
            );
        }
        let named = add(
            &mut f.external_modules,
            ExternalModuleRow {
                bundle: text,
                binding_hint: other,
                import_attributes: ranged,
            },
        );
        let bare = add(
            &mut f.external_modules,
            ExternalModuleRow {
                bundle: text,
                binding_hint: NONE,
                import_attributes: NONE,
            },
        );
        let kinds = [
            ExternalKindRow::Value(text),
            ExternalKindRow::Send(text),
            ExternalKindRow::New(text),
            ExternalKindRow::Get(text),
            ExternalKindRow::Set(text),
            ExternalKindRow::GetIndex,
            ExternalKindRow::SetIndex,
        ];
        let sources = [
            ModuleSourceRow::Absent,
            ModuleSourceRow::Itself,
            ModuleSourceRow::Named(named),
            ModuleSourceRow::Named(bare),
        ];
        let declarations: Vec<u32> = kinds
            .iter()
            .zip(sources.iter().cycle())
            .map(|(&kind, &module)| {
                add(
                    &mut f.external_declarations,
                    ExternalDeclRow {
                        kind,
                        module,
                        scopes: strings,
                        effective_arity: 4,
                        variadic: true,
                    },
                )
            })
            .collect();
        let wrappers = [
            ReturnWrapperRow::Unset,
            ReturnWrapperRow::Identity,
            ReturnWrapperRow::NullToOption,
            ReturnWrapperRow::NullUndefinedToOption,
        ];
        let calls: Vec<u32> = wrappers
            .iter()
            .map(|&return_wrapper| {
                add(
                    &mut f.ffi,
                    FfiRow::Call {
                        params: Range {
                            start: call_params,
                            len: 3,
                        },
                        declaration: declarations[0],
                        return_wrapper,
                    },
                )
            })
            .collect();
        let object = add(
            &mut f.ffi,
            FfiRow::Object(Range {
                start: object_params,
                len: 3,
            }),
        );
        let inlines = [
            InlineConstantRow::String(text),
            InlineConstantRow::Bool(true),
            InlineConstantRow::Int(-4),
            InlineConstantRow::Bigint {
                positive: false,
                digits: other,
            },
            InlineConstantRow::Float(text),
        ]
        .map(|row| add(&mut f.inline_constants, row));
        let primitives = [
            PrimitiveKindRow::Intrinsic,
            PrimitiveKindRow::External(calls[0]),
            PrimitiveKindRow::Inline(inlines[0]),
        ]
        .map(|kind| {
            add(
                &mut f.primitives,
                PrimitiveRow {
                    name: text,
                    arity: 2,
                    kind,
                    native_float: true,
                    from_constructor: false,
                },
            )
        });

        // Runtime representations.
        let literals = [
            LiteralRow::String(text),
            LiteralRow::Int(-1),
            LiteralRow::Float(text),
            LiteralRow::BigInt(other),
            LiteralRow::Bool(false),
            LiteralRow::Null,
            LiteralRow::Undefined,
        ]
        .map(|row| add(&mut f.literals, row));
        let blocks = [
            BlockTypeRow::Number,
            BlockTypeRow::String,
            BlockTypeRow::Bigint,
            BlockTypeRow::Boolean,
            BlockTypeRow::Array,
            BlockTypeRow::Symbol,
            BlockTypeRow::Function,
            BlockTypeRow::Object,
            BlockTypeRow::Unknown,
            BlockTypeRow::Class {
                name: text,
                ancestors: strings,
            },
        ]
        .map(|row| add(&mut f.block_types, row));
        let shapes = [
            ShapeRow::Unstated,
            ShapeRow::NeverUndefined,
            ShapeRow::Recognized(blocks[9]),
        ]
        .map(|row| add(&mut f.shapes, row));
        let cases = f.runtime_constructors.len() as u32;
        for row in [
            RuntimeConstructorRow::Constant {
                name: text,
                literal: literals[0],
            },
            RuntimeConstructorRow::Tagged {
                name: other,
                literal: literals[1],
                tag_name: text,
            },
            RuntimeConstructorRow::Tagged {
                name: other,
                literal: literals[2],
                tag_name: NONE,
            },
            RuntimeConstructorRow::Untagged {
                name: text,
                literal: literals[3],
                block_type: blocks[4],
            },
        ] {
            add(&mut f.runtime_constructors, row);
        }
        let layout = add(
            &mut f.layouts,
            LayoutRow {
                constructors: Range {
                    start: cases,
                    len: 4,
                },
                tag_name: other,
                unboxed: true,
            },
        );
        let representations = [
            RecordRepresentationRow::Regular,
            RecordRepresentationRow::Array,
            RecordRepresentationRow::Unboxed(true),
            RecordRepresentationRow::Extension,
            RecordRepresentationRow::Inlined {
                name: text,
                position: 3,
                layout,
            },
        ]
        .map(|row| add(&mut f.record_representations, row));
        f.close(0, 0);
        let segment = f.into_segment(unit);
        let mut rebuild = Rebuild::new(&segment);
        rebuild.locations();
        rebuild.paths();
        rebuild.layouts();
        let owned = |text: &str| text.to_owned();

        // Locations: a coordinate-free one is a source handle, any other one an
        // entry of the location table, with its file carried by key.
        assert_eq!(rebuild.loc(plain), DeclLoc::none());
        let handle = rebuild.loc(located);
        assert_eq!(handle.kind(), DeclLocKind::Portable);
        let location = rebuild.coordinates[handle.index()];
        assert_eq!(
            (
                location.loc_start.line,
                location.loc_end.cnum,
                location.loc_ghost
            ),
            (7, 71, false)
        );
        let key = location.loc_start.file_name.raw();
        assert_eq!(rebuild.file_names, [(key, owned("File.res"))]);

        let payload = |row: u32| rebuild.attribute_payload(first_payload + row);
        assert_eq!(payload(0), AttributePayload::Empty);
        assert_eq!(payload(1), AttributePayload::Str(owned("text")));
        assert_eq!(payload(2), AttributePayload::Int(-3));
        assert_eq!(payload(3), AttributePayload::IntLiteral(owned("text")));
        assert_eq!(payload(4), AttributePayload::Float(owned("text")));
        assert_eq!(payload(5), AttributePayload::BigInt(owned("text")));
        assert_eq!(payload(6), AttributePayload::Bool(true));
        assert_eq!(payload(7), AttributePayload::Ident(owned("text")));
        let migrate = Some(MarshalFragment {
            bytes: vec![0, 255, 7],
            objects: 1,
            size_32: 2,
            size_64: 3,
        });
        for (row, reason) in [
            (8, Ok(None)),
            (9, Ok(Some(owned("text")))),
            (10, Err(rebuild.loc(located))),
        ] {
            assert_eq!(
                payload(row),
                AttributePayload::Deprecated {
                    reason,
                    can_be_automigrated: true,
                    migrate: migrate.clone(),
                    migrate_in_pipe_chain: None,
                }
            );
        }
        assert_eq!(
            payload(11),
            AttributePayload::Structure(vec![(owned("text"), owned("other"))])
        );
        assert_eq!(
            payload(12),
            AttributePayload::SemanticString(Box::new(SemanticStringPayload {
                semantic: Ok(owned("text")),
                braces: 2,
                template: true,
            }))
        );
        assert_eq!(
            payload(13),
            AttributePayload::SemanticString(Box::new(SemanticStringPayload {
                semantic: Err(DeclLoc::none()),
                braces: 0,
                template: false,
            }))
        );
        assert_eq!(
            payload(14),
            AttributePayload::StrTuple(vec![owned("text"), owned("other")])
        );
        let attributes = rebuild.attributes(Range {
            start: attribute,
            len: 1,
        });
        assert_eq!(attributes.len(), 1);
        assert_eq!(attributes[0].attr_name.txt, "other");
        assert_eq!(attributes[0].attr_name.loc, rebuild.loc(located));
        assert_eq!(attributes[0].attr_loc, DeclLoc::none());
        assert_eq!(attributes[0].attr_payload, payload(1));

        let pairs_old = vec![(owned("text"), owned("other"))];
        let expected_attrs = [
            ffi::Attr::PolyVarString {
                descr: pairs_old.clone(),
            },
            ffi::Attr::PolyVar { descr: None },
            ffi::Attr::PolyVar {
                descr: Some(pairs_old.clone()),
            },
            ffi::Attr::Int(vec![(owned("text"), 5)]),
            ffi::Attr::ArgCst(ffi::Cst::ArgIntLit(9)),
            ffi::Attr::ArgCst(ffi::Cst::ArgStringLit(owned("text"))),
            ffi::Attr::ArgCst(ffi::Cst::ArgJsonLit(owned("other"))),
            ffi::Attr::ExternUnit,
            ffi::Attr::Nothing,
            ffi::Attr::Ignore,
            ffi::Attr::Unwrap,
        ];
        for (row, expected) in attrs.iter().zip(expected_attrs) {
            assert_eq!(rebuild.ffi_attribute(*row), expected);
        }
        let expected_kinds = [
            ffi::DeclKind::DeclVal {
                name: owned("text"),
            },
            ffi::DeclKind::DeclSend {
                name: owned("text"),
            },
            ffi::DeclKind::DeclNew {
                name: owned("text"),
            },
            ffi::DeclKind::DeclGet {
                name: owned("text"),
            },
            ffi::DeclKind::DeclSet {
                name: owned("text"),
            },
            ffi::DeclKind::DeclGetIndex,
            ffi::DeclKind::DeclSetIndex,
        ];
        let expected_modules = [
            None,
            Some(ffi::ModuleSource::ModuleItself),
            Some(ffi::ModuleSource::ModuleNamed(ffi::ExternalModuleName {
                bundle: owned("text"),
                module_bind_name: ffi::ModuleBindName::PhintName(owned("other")),
                import_attributes: Some(pairs_old.clone()),
            })),
            Some(ffi::ModuleSource::ModuleNamed(ffi::ExternalModuleName {
                bundle: owned("text"),
                module_bind_name: ffi::ModuleBindName::PhintNothing,
                import_attributes: None,
            })),
        ];
        for (index, (kind, module_)) in expected_kinds
            .into_iter()
            .zip(expected_modules.iter().cycle())
            .enumerate()
        {
            assert_eq!(
                rebuild.external_declaration(declarations[index]),
                ffi::ExternalDecl {
                    kind,
                    module_: module_.clone(),
                    scopes: vec![owned("text"), owned("other")],
                    variadic: true,
                    effective_arity: 4,
                }
            );
        }
        let call_labels = [
            ffi::LabelNoname::ArgLabel,
            ffi::LabelNoname::ArgEmpty,
            ffi::LabelNoname::ArgOptional,
        ];
        let expected_wrappers = [
            ffi::ReturnWrapper::ReturnUnset,
            ffi::ReturnWrapper::ReturnIdentity,
            ffi::ReturnWrapper::ReturnNullToOpt,
            ffi::ReturnWrapper::ReturnNullUndefinedToOpt,
        ];
        for (call, wrapper) in calls.iter().zip(expected_wrappers) {
            let ffi::ExternalFfi::FfiBs(params, return_wrapper, declaration) = rebuild.ffi(*call)
            else {
                panic!("a call");
            };
            assert_eq!(return_wrapper, wrapper);
            assert_eq!(declaration, rebuild.external_declaration(declarations[0]));
            let labels: Vec<_> = params.iter().map(|param| param.arg_label).collect();
            assert_eq!(labels, call_labels);
            assert!(
                params
                    .iter()
                    .all(|param| param.arg_type == expected_attrs_first())
            );
        }
        let ffi::ExternalFfi::FfiObjCreate(params) = rebuild.ffi(object) else {
            panic!("an object creation");
        };
        let labels: Vec<_> = params
            .iter()
            .map(|param| param.obj_arg_label.clone())
            .collect();
        assert_eq!(
            labels,
            [
                ffi::Label::ObjEmpty,
                ffi::Label::ObjLabel {
                    name: owned("text")
                },
                ffi::Label::ObjOptional {
                    name: owned("other"),
                    for_sure_no_nested_option: true,
                },
            ]
        );
        assert!(
            params
                .iter()
                .all(|param| param.obj_arg_type == ffi::Attr::Nothing)
        );
        let expected_inlines = [
            ffi::InlineConst::ConstString(owned("text")),
            ffi::InlineConst::ConstBool(true),
            ffi::InlineConst::ConstInt(-4),
            ffi::InlineConst::ConstBigint {
                positive: false,
                digits: owned("other"),
            },
            ffi::InlineConst::ConstFloat(owned("text")),
        ];
        for (row, expected) in inlines.iter().zip(expected_inlines) {
            assert_eq!(rebuild.inline_constant(*row), expected);
        }
        let kinds: Vec<_> = primitives
            .iter()
            .map(|row| {
                let primitive = rebuild.primitive(*row);
                assert_eq!(primitive.prim_name, "text");
                assert_eq!(primitive.prim_arity, 2);
                assert!(primitive.prim_native_float && !primitive.prim_from_constructor);
                primitive.prim_kind
            })
            .collect();
        assert!(matches!(kinds[0], PrimKind::KindIntrinsic));
        assert!(
            matches!(&kinds[1], PrimKind::KindExternal(external) if **external == rebuild.ffi(calls[0]))
        );
        assert!(
            matches!(&kinds[2], PrimKind::KindInlineConst(constant) if **constant == ffi::InlineConst::ConstString(owned("text")))
        );

        let expected_literals = [
            LiteralTag::String(owned("text")),
            LiteralTag::Int(-1),
            LiteralTag::Float(owned("text")),
            LiteralTag::BigInt(owned("other")),
            LiteralTag::Bool(false),
            LiteralTag::Null,
            LiteralTag::Undefined,
        ];
        for (row, expected) in literals.iter().zip(expected_literals) {
            assert_eq!(rebuild.literal(*row), expected);
        }
        let class = BlockType::Instance(Instance::Class {
            name: owned("text"),
            ancestors: vec![owned("text"), owned("other")],
            blocks: ClassBlocks::fresh(2),
        });
        let expected_blocks = [
            BlockType::Number,
            BlockType::String,
            BlockType::Bigint,
            BlockType::Boolean,
            BlockType::Instance(Instance::Array(ShapeAllocation::fresh())),
            BlockType::Symbol,
            BlockType::Function,
            BlockType::Object,
            BlockType::Unknown,
            class.clone(),
        ];
        // Block equality ignores allocation identity, which `from_old` drops.
        for (row, expected) in blocks.iter().zip(expected_blocks) {
            assert_eq!(rebuild.block_type(*row), expected);
        }
        assert_eq!(rebuild.shape(shapes[0]), ValueShape::Unstated);
        assert_eq!(rebuild.shape(shapes[1]), ValueShape::NeverUndefined);
        assert_eq!(
            rebuild.shape(shapes[2]).block_type(),
            Some(&class),
            "a recognized shape keeps its kind"
        );
        let layout = &rebuild.layouts[layout as usize];
        assert!(layout.unboxed);
        assert_eq!(layout.matching_facts.tag_name.as_deref(), Some("other"));
        assert!(
            matches!(&layout.constructors[0], ConstructorCase::Constant(tag) if tag.name.as_str() == "text" && tag.literal == LiteralTag::String(owned("text")))
        );
        assert!(matches!(
            &layout.constructors[1],
            ConstructorCase::Block(Block::Tagged(TaggedBlock { tag, tag_name: Some(name) }))
                if tag.name.as_str() == "other" && tag.literal == LiteralTag::Int(-1) && name == "text"
        ));
        assert!(matches!(
            &layout.constructors[2],
            ConstructorCase::Block(Block::Tagged(TaggedBlock { tag_name: None, .. }))
        ));
        assert!(matches!(
            &layout.constructors[3],
            ConstructorCase::Block(Block::Untagged {
                block_type: BlockType::Instance(Instance::Array(_)),
                ..
            })
        ));
        assert_eq!(
            layout.matching_facts.literal_tags,
            [LiteralTag::String(owned("text"))]
        );
        assert_eq!(layout.matching_facts.block_types.len(), 1);
        let expected_representations = [
            RecordRepresentation::RecordRegular,
            RecordRepresentation::RecordArray,
            RecordRepresentation::RecordUnboxed(true),
            RecordRepresentation::RecordExtension,
            RecordRepresentation::RecordInlined {
                name: owned("text"),
                representation: ConstructorReference {
                    variant: LayoutRef::from_usize(0),
                    position: 3,
                },
            },
        ];
        for (row, expected) in representations.iter().zip(expected_representations) {
            assert_eq!(rebuild.record_representation(*row), expected);
        }
    }

    /// O(1): the old form of the first FFI attribute row of the metadata test.
    fn expected_attrs_first() -> ffi::Attr {
        ffi::Attr::PolyVarString {
            descr: vec![("text".to_owned(), "other".to_owned())],
        }
    }

    #[test]
    fn every_item_kind_keeps_identifiers_paths_and_declarations() {
        let mut f = Fixture::default();
        let unit = f.unit();
        let mut graph = Graph::default();
        let weak = var(&mut graph, 1);
        let loc = f.loc(None, 0);
        let empty = Range::default();
        let shape = add(&mut f.shapes, ShapeRow::Unstated);
        let roots = |start: u32, len: u32| Range { start, len };

        // 0: let v (absent path); 1: let u (path Test.u, position 1).
        f.value("v", 1, 0);
        let u_name = f.string("u");
        let u_path = add(
            &mut f.paths,
            PathRow::Dot {
                parent: unit.path,
                name: u_name,
                position: 1,
            },
        );
        let u = f.value("u", 2, 1);
        let u_value = f.ordered_items[u as usize].declaration;
        f.values[u_value as usize].path = u_path;

        // 2: type r = {x: '_w, mutable y?: '_w}, rec first.
        let type_item = |f: &mut Fixture,
                         name: &str,
                         stamp: i32,
                         kind: DeclarationKind,
                         flags: u8,
                         members: (u32, u32),
                         details: TypeDetailsRow,
                         status: RecStatus| {
            let (ident, path) = f.binder(name, stamp);
            let declaration = add(
                &mut f.type_declarations,
                TypeDecl {
                    kind,
                    flags,
                    arity: 0,
                    params: details.parameter_roots.start,
                    manifest: NONE,
                    members: members.0,
                    member_len: members.1,
                    path,
                    loc,
                    variance: details.variance.start,
                },
            );
            add(&mut f.type_details, details);
            add(
                &mut f.ordered_items,
                SignatureItemRow {
                    ident,
                    declaration,
                    kind: SignatureKind::Type,
                    status: ItemStatus::Recursive(status),
                },
            );
        };
        let details =
            |representation: u32, inlined_records: Range, levels: (u32, u32)| TypeDetailsRow {
                parameter_roots: Range::default(),
                variance: Range::default(),
                attributes: Range::default(),
                inlined_records,
                representation,
                shape,
                newtype_level: levels.0,
                scope_level: levels.1,
            };
        let label = |f: &mut Fixture, name: &str, root: u32, mutable: bool, optional: bool| {
            let ident = f.ident(name, 0, NONE);
            let runtime_name = if mutable { NONE } else { f.string("ex") };
            add(
                &mut f.labels,
                LabelRow {
                    ident,
                    runtime_name,
                    ty: root,
                    attributes: Range::default(),
                    loc,
                    mutable,
                    optional,
                },
            )
        };
        let x = label(&mut f, "x", 2, false, false);
        let y = label(&mut f, "y", 3, true, true);
        let members = f.members.len() as u32;
        for (position, (label, flags)) in [(x, 0), (y, 3)].into_iter().enumerate() {
            let name = f.labels[label as usize].ident;
            let name = f.identifiers[name as usize].name;
            add(
                &mut f.members,
                MemberDecl {
                    name,
                    args: label,
                    tag_or_pos: position as u32,
                    flags,
                },
            );
        }
        let regular = add(
            &mut f.record_representations,
            RecordRepresentationRow::Regular,
        );
        type_item(
            &mut f,
            "r",
            3,
            DeclarationKind::Record,
            0,
            (members, 2),
            details(regular, empty, (NONE, NONE)),
            RecStatus::First,
        );

        // 3: type c = A | B('_w): '_w, with an inlined record {z: '_w}, a local
        // constraint at levels (2, -1), private, immediate and unboxed; rec next.
        let literal = add(&mut f.literals, LiteralRow::Int(1));
        let a = f.ident("A", 0, NONE);
        let b = f.ident("B", 0, NONE);
        let no_arguments = add(
            &mut f.constructor_arguments,
            ConstructorArgumentsRow::Tuple(roots(4, 0)),
        );
        let b_arguments = add(
            &mut f.constructor_arguments,
            ConstructorArgumentsRow::Tuple(roots(4, 1)),
        );
        let first_constructor = f.constructors.len() as u32;
        for (ident, runtime_tag, arguments, result) in
            [(a, literal, no_arguments, NONE), (b, NONE, b_arguments, 5)]
        {
            add(
                &mut f.constructors,
                ConstructorRow {
                    ident,
                    runtime_tag,
                    arguments,
                    result,
                    attributes: Range::default(),
                    loc,
                },
            );
        }
        let members = f.members.len() as u32;
        for position in 0..2 {
            let constructor = f.constructors[(first_constructor + position) as usize];
            let name = f.identifiers[constructor.ident as usize].name;
            add(
                &mut f.members,
                MemberDecl {
                    name,
                    args: first_constructor + position,
                    tag_or_pos: position,
                    flags: if position == 0 { 1 } else { 2 },
                },
            );
        }
        let layout = add(
            &mut f.layouts,
            LayoutRow {
                constructors: Range::default(),
                tag_name: NONE,
                unboxed: false,
            },
        );
        let z = label(&mut f, "z", 6, false, false);
        let inlined_name = f.string("c.B");
        let inlined = add(
            &mut f.inlined_records,
            InlinedRecordRow {
                name: inlined_name,
                labels: Range { start: z, len: 1 },
            },
        );
        type_item(
            &mut f,
            "c",
            4,
            DeclarationKind::Variant,
            1 | 2 | 4 | 8,
            (members, 2),
            details(
                layout,
                Range {
                    start: inlined,
                    len: 1,
                },
                (2, -1i32 as u32),
            ),
            RecStatus::Next,
        );

        // 4: type o = .., rec not (no roots).
        let no_members = f.members.len() as u32;
        type_item(
            &mut f,
            "o",
            5,
            DeclarationKind::Open,
            0,
            (no_members, 0),
            details(NONE, empty, (NONE, NONE)),
            RecStatus::Not,
        );

        // 5: exception E({w: '_w}), extending exn.
        let exn = f.ident("exn", 0, NONE);
        let exn = add(&mut f.paths, PathRow::Ident(exn));
        let w = label(&mut f, "w", 7, false, false);
        let record_arguments = add(
            &mut f.constructor_arguments,
            ConstructorArgumentsRow::Record(Range { start: w, len: 1 }),
        );
        let extension = add(
            &mut f.extensions,
            ExtensionRow {
                path: exn,
                parameters: roots(7, 0),
                result: NONE,
                arguments: record_arguments,
                attributes: Range::default(),
                loc,
                private: true,
                exception: true,
            },
        );
        let (ident, _) = f.binder("E", 6);
        add(
            &mut f.ordered_items,
            SignatureItemRow {
                ident,
                declaration: extension,
                kind: SignatureKind::Extension,
                status: ItemStatus::Extension(ExtensionStatus::Exception),
            },
        );

        // 6: module M: Test.u's module type path; 7: module N = alias (absent).
        // 8: module type S = {let s}; 9: module type F = (X: S) => {};
        // 10: module type G = () => S; 11: module type H.
        let module =
            |f: &mut Fixture, name: &str, stamp: i32, module_type: u32, kind: SignatureKind| {
                let (ident, path) = f.binder(name, stamp);
                let declaration = add(
                    &mut f.modules,
                    ModuleRow {
                        module_type,
                        attributes: Range::default(),
                        loc,
                        path,
                    },
                );
                add(
                    &mut f.ordered_items,
                    SignatureItemRow {
                        ident,
                        declaration,
                        kind,
                        status: if kind == SignatureKind::Module {
                            ItemStatus::Recursive(RecStatus::Not)
                        } else {
                            ItemStatus::Ordinary
                        },
                    },
                )
            };
        let ident_type = add(&mut f.module_types, ModuleTypeRow::Ident(u_path));
        module(&mut f, "M", 7, ident_type, SignatureKind::Module);
        let alias = add(
            &mut f.module_types,
            ModuleTypeRow::Alias {
                path: unit.path,
                present: false,
            },
        );
        module(&mut f, "N", 8, alias, SignatureKind::Module);
        let s_signature = add(&mut f.signatures, Range::default());
        let s_type = add(&mut f.module_types, ModuleTypeRow::Signature(s_signature));
        module(&mut f, "S", 9, s_type, SignatureKind::ModuleType);
        let functor_row = f.module_types.len() as u32 + 2;
        let parameter = f.ident("X", 20, FUNCTOR_SCOPE | functor_row);
        let parameter_type = add(&mut f.module_types, ModuleTypeRow::Ident(u_path));
        let f_signature = add(&mut f.signatures, Range::default());
        let result = add(&mut f.module_types, ModuleTypeRow::Signature(f_signature));
        let functor = add(
            &mut f.module_types,
            ModuleTypeRow::Functor {
                parameter,
                parameter_type,
                result,
            },
        );
        module(&mut f, "F", 10, functor, SignatureKind::ModuleType);
        let generative_row = f.module_types.len() as u32 + 1;
        let generative_parameter = f.ident("*", 21, FUNCTOR_SCOPE | generative_row);
        let generative_result = add(&mut f.module_types, ModuleTypeRow::Ident(u_path));
        let generative = add(
            &mut f.module_types,
            ModuleTypeRow::Functor {
                parameter: generative_parameter,
                parameter_type: NONE,
                result: generative_result,
            },
        );
        module(&mut f, "G", 11, generative, SignatureKind::ModuleType);
        module(&mut f, "H", 12, NONE, SignatureKind::ModuleType);
        for kind in [SignatureKind::Class, SignatureKind::ClassType] {
            add(
                &mut f.ordered_items,
                SignatureItemRow {
                    ident: NONE,
                    declaration: NONE,
                    kind,
                    status: ItemStatus::Ordinary,
                },
            );
        }
        f.close(0, 0);
        let start = f.ordered_items.len() as u32;
        f.value("s", 13, 8);
        f.close(s_signature, start);
        let start = f.ordered_items.len() as u32;
        f.close(f_signature, start);
        let schemes: [&[Ty]; 6] = [
            &[weak],
            &[weak],
            &[weak, weak],
            &[weak, weak, weak],
            &[weak],
            &[weak],
        ];
        let segment = finish(graph, &schemes, f, unit);
        let (output, visits) = run(&segment);
        assert_eq!(visits.count, 1, "only the shared node; no synthetic tuple");
        assert_eq!(output.unit(), "Test");
        assert_eq!(output.deprecated(), None);
        let w = TypeExprRef::from_usize(0);
        let signature = output.signature();
        assert_eq!(signature.len(), 14);

        let SignatureItem::SigValue(v, v_decl) = &signature[0] else {
            panic!("v");
        };
        assert_eq!((v.name(), v.stamp(), v.flags().bits()), ("v", 1, 0));
        assert!(v_decl.val_path.is_none());
        assert!(matches!(v_decl.val_kind, ValueKind::ValReg));
        assert_eq!(v_decl.val_type, w);
        let SignatureItem::SigValue(_, u_decl) = &signature[1] else {
            panic!("u");
        };
        let u_path = u_decl.val_path.expect("a present path stays present");
        assert_eq!(u_path.name(), "Test.u");
        let crate::types::path::PathView::Pdot(unit_path, _, 1) = *u_path.view() else {
            panic!("Test.u at position 1");
        };
        let head = unit_path.as_pident().expect("the unit");
        assert_eq!(
            (head.stamp(), head.flags().bits()),
            (0, IdentFlags::GLOBAL.bits())
        );

        let SignatureItem::SigType(_, r, OldRecStatus::TrecFirst) = &signature[2] else {
            panic!("r");
        };
        let TypeKind::TypeRecord(labels, RecordRepresentation::RecordRegular) = &r.type_kind else {
            panic!("a regular record");
        };
        assert_eq!(labels.len(), 2);
        assert_eq!(labels[0].ld_id.name(), "x");
        assert_eq!(labels[0].ld_runtime_name.as_deref(), Some("ex"));
        assert_eq!(labels[0].ld_mutable, MutableFlag::Immutable);
        assert_eq!(labels[1].ld_mutable, MutableFlag::Mutable);
        assert!(labels[1].ld_optional && !labels[0].ld_optional);
        assert!(labels.iter().all(|label| label.ld_type == w));
        assert!(r.type_path.is_none() && r.type_manifest.is_none());
        assert_eq!(r.type_private, PrivateFlag::Public);

        let SignatureItem::SigType(_, c, OldRecStatus::TrecNext) = &signature[3] else {
            panic!("c");
        };
        let TypeKind::TypeVariant(constructors, layout) = &c.type_kind else {
            panic!("a variant");
        };
        assert_eq!(*layout, LayoutRef::from_usize(0));
        assert_eq!(constructors[0].cd_id.name(), "A");
        assert_eq!(constructors[0].cd_runtime_tag, Some(LiteralTag::Int(1)));
        assert!(
            matches!(&constructors[0].cd_args, ConstructorArguments::CstrTuple(args) if args.is_empty())
        );
        assert!(constructors[0].cd_res.is_none());
        assert!(
            matches!(&constructors[1].cd_args, ConstructorArguments::CstrTuple(args) if args == &[w])
        );
        assert_eq!(constructors[1].cd_res, Some(w));
        assert_eq!(c.type_private, PrivateFlag::Private);
        assert!(c.type_immediate);
        assert_eq!(c.type_representation, TypeRepresentation::Unboxed);
        assert_eq!(c.type_newtype_level, Some((2, -1)));
        let [TypeInlinedType::Record { type_name, labels }] = &c.type_inlined_types[..] else {
            panic!("one inlined record");
        };
        assert_eq!(type_name, "c.B");
        assert_eq!(labels[0].ld_type, w);

        let SignatureItem::SigType(_, o, OldRecStatus::TrecNot) = &signature[4] else {
            panic!("o");
        };
        assert!(matches!(o.type_kind, TypeKind::TypeOpen));
        assert_eq!(o.type_representation, TypeRepresentation::Boxed);
        assert!(o.type_newtype_level.is_none());

        let SignatureItem::SigTypext(e, ext, ExtStatus::TextException) = &signature[5] else {
            panic!("E");
        };
        assert_eq!(e.stamp(), 6);
        assert_eq!(ext.ext_type_path.name(), "exn");
        assert!(ext.ext_is_exception);
        assert_eq!(ext.ext_private, PrivateFlag::Private);
        assert!(ext.ext_ret_type.is_none());
        assert!(
            matches!(&ext.ext_args, ConstructorArguments::CstrRecord(labels) if labels[0].ld_type == w)
        );

        let SignatureItem::SigModule(_, m, OldRecStatus::TrecNot) = &signature[6] else {
            panic!("M");
        };
        assert!(m.md_path.is_none());
        assert!(matches!(&m.md_type, ModuleType::MtyIdent(path) if *path == u_path));
        let SignatureItem::SigModule(_, n, _) = &signature[7] else {
            panic!("N");
        };
        assert!(matches!(
            &n.md_type,
            ModuleType::MtyAlias(AliasPresence::MtaAbsent, path) if **path == unit_path
        ));
        let SignatureItem::SigModtype(_, s) = &signature[8] else {
            panic!("S");
        };
        let Some(ModuleType::MtySignature(inner)) = &s.mtd_type else {
            panic!("a signature");
        };
        assert!(matches!(&inner[..], [SignatureItem::SigValue(id, _)] if id.name() == "s"));
        let SignatureItem::SigModtype(_, functor) = &signature[9] else {
            panic!("F");
        };
        let Some(ModuleType::MtyFunctor {
            param,
            param_type: Some(param_type),
            result,
        }) = &functor.mtd_type
        else {
            panic!("an applicative functor");
        };
        assert_eq!((param.name(), param.stamp()), ("X", 20));
        assert!(matches!(&**param_type, ModuleType::MtyIdent(_)));
        assert!(matches!(&**result, ModuleType::MtySignature(inner) if inner.is_empty()));
        let SignatureItem::SigModtype(_, generative) = &signature[10] else {
            panic!("G");
        };
        assert!(matches!(
            &generative.mtd_type,
            Some(ModuleType::MtyFunctor {
                param_type: None,
                ..
            })
        ));
        let SignatureItem::SigModtype(_, abstract_type) = &signature[11] else {
            panic!("H");
        };
        assert!(abstract_type.mtd_type.is_none());
        assert!(matches!(signature[12], SignatureItem::SigClass));
        assert!(matches!(signature[13], SignatureItem::SigClassType));
    }

    #[test]
    fn publication_into_a_pool_interns_components_once() {
        let mut f = Fixture::default();
        let unit = f.unit();
        let m = f.string("M");
        let lid_m = add(&mut f.longidents, LongidentRow::Ident(m));
        let lid_mm = add(
            &mut f.longidents,
            LongidentRow::Dot {
                parent: lid_m,
                name: m,
            },
        );
        let lids = f.indices.len() as u32;
        f.indices.push(lid_mm);
        let package = add(
            &mut f.packages,
            PackageRow {
                path: unit.path,
                longidents: Range {
                    start: lids,
                    len: 1,
                },
                arguments: Range::default(),
            },
        );
        let package = add(&mut f.descriptor_extras, ExtraDescriptor::Package(package));
        let mut graph = Graph::default();
        let root = extended(&mut graph, 1, package, &[]);
        f.value("p", 1, 0);
        f.close(0, 0);
        let segment = finish(graph, &[&[root]], f, unit);
        let pool = SharedTypePool::new();
        let output = to_old(&segment);
        {
            let names = output.published.names.read().unwrap();
            assert_eq!(names.len(), 1);
            assert_eq!(names[&0].as_str(), "M");
        }
        let published = output.into_pool(&pool);
        assert!(std::ptr::eq(published.names.as_ref(), pool.names_ref()));
        let TypeDesc::Tpackage { lids, .. } = published.graph.nodes()[0].desc else {
            panic!("a package");
        };
        let [Longident::Ldot(prefix, last)] = published.graph.lids(lids) else {
            panic!("M.M");
        };
        let Longident::Lident(first) = **prefix else {
            panic!("M");
        };
        assert_eq!(first, *last, "one pool name per distinct component");
        assert_eq!(pool.longident_name(first).as_deref(), Some("M"));
    }

    #[test]
    fn ten_thousand_fields_keep_cell_classes_on_a_two_mb_stack() {
        std::thread::Builder::new()
            .stack_size(2 * 1024 * 1024)
            .spawn(|| {
                let mut f = Fixture::default();
                let unit = f.unit();
                f.mutabilities.extend([true, true, false]);
                let name = f.string("field");
                let mut graph = Graph::default();
                let typ = var(&mut graph, GENERIC);
                let nil_extra = add(&mut f.descriptor_extras, ExtraDescriptor::Nil);
                let nil = extended(&mut graph, GENERIC, nil_extra, &[]);
                let mut fields = Vec::new();
                for index in 0..N {
                    let mutability = if index == N - 1 { 2 } else { index % 2 };
                    let extra = add(
                        &mut f.descriptor_extras,
                        ExtraDescriptor::Field { name, mutability },
                    );
                    fields.push(extended(&mut graph, GENERIC, extra, &[typ, nil]));
                }
                let root = tuple(&mut graph, GENERIC, &fields);
                f.value("fields", 1, 0);
                f.close(0, 0);
                let segment = finish(graph, &[&[root]], f, unit);
                let mut result = None;
                let steps = steps::scope(|| result = Some(run(&segment)));
                let (output, visits) = result.unwrap();
                assert_eq!(visits.count, u64::from(N) + 3);
                assert!(steps <= 4 * u64::from(N) + 20, "{steps}");
                let old = &output.published.graph;
                let TypeDesc::Ttuple(list) = desc(old, value_type(&output.signature()[0])) else {
                    panic!("tuple")
                };
                let fields = old.list(list);
                let cell = |index: usize| {
                    let TypeDesc::Tfield { mutability, .. } = desc(old, fields[index]) else {
                        panic!("field")
                    };
                    mutability
                };
                let (a, b, c) = (cell(0), cell(1), cell((N - 1) as usize));
                assert_ne!(a, b, "distinct equal cells stay distinct");
                assert_ne!(a, c);
                assert_ne!(b, c);
                assert_eq!(a.persistent_value(), MutableFlag::Mutable);
                assert_eq!(b.persistent_value(), MutableFlag::Mutable);
                assert_eq!(c.persistent_value(), MutableFlag::Immutable);
                for index in 0..N - 1 {
                    assert_eq!(cell(index as usize), if index % 2 == 0 { a } else { b });
                }
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn resolved_components_do_not_claim_unresolved_diagnostic_indices() {
        let mut f = Fixture::default();
        let unit = f.unit();
        let name = f.string("resolved");
        add(&mut f.longidents, LongidentRow::Unresolved(0));
        let known = add(&mut f.longidents, LongidentRow::Ident(name));
        let segment = f.into_segment(unit);
        let mut rebuild = Rebuild::new(&segment);
        assert_eq!(rebuild.longident(0), Longident::Lident(StrIdx::from_raw(0)));
        assert_eq!(
            rebuild.longident(known),
            Longident::Lident(StrIdx::from_raw(1))
        );
        assert_eq!(rebuild.component_keys, [1]);
        assert_eq!(rebuild.components, ["resolved"]);
    }
}

#[cfg(test)]
mod round_trip {
    //! Round trips of a compiled unit through both converters: new, old, new.
    //! Needs `from_old::Input::new` (see the accompanying from_old.rs hunk).

    use super::super::from_old::{Input, from_old};
    use super::*;
    use crate::cmi::item_deps::item_declaration_hashes;
    use crate::cmi::portable_types::signature_fingerprint;

    const SAMPLE: &str = r#"
    type option<'a> = None | Some('a)
    external \"++": (string, string) => string = "%string_concat"
    type color = | @as("r") Red | @as(2) Green | Blue(int, string)
    type point = {x: int, mutable y: int, @as("zed") z?: float}
    type shape = [#circle(float) | #square]
    type obj = {"name": string, "age": int}
    type poly = {f: 'a. 'a => 'a}
    @unboxed type wrapped = Wrapped(string)
    exception Failed(string, int)
    external length: string => int = "%string_length"
    @module("m") external bound: int => int = "bound"
    @deprecated("use other") let old = 1
    let id = x => x
    let pair = (x, y) => (x, y, x)
    module Inner = {
      type t = int
    }
    module type Showable = {
      type t
      let show: t => string
    }
    module MakeShow = (S: Showable) => {
      let twice = (x: S.t) => S.show(x) ++ S.show(x)
    }
    type packed = module(Showable with type t = int)
    "#;

    /// O(the unit): the segment of an old publication.
    fn segment_of(published: &PublishedGraph) -> Segment {
        from_old(Input::new(
            &published.graph,
            &published.signature,
            "Sample",
            None,
            &published.names,
            [0; 32],
        ))
    }

    macro_rules! same {
        ($a:expr, $b:expr; $($field:ident),* $(,)?) => {
            $(assert_eq!($a.$field, $b.$field, stringify!($field));)*
        };
    }

    /// O(pools): every pool of two segments is equal.
    fn assert_same(a: &Segment, b: &Segment) {
        same!(a, b; nodes, lists, params, template_nodes, template_lists, template_params,
            template_externals, template_origins, type_declarations, members, items, children, digest);
        let templates = |segment: &Segment| {
            segment
                .templates
                .iter()
                .map(|t| (t.nodes, t.node_len, t.pools, t.list_len))
                .collect::<Vec<_>>()
        };
        assert_eq!(templates(a), templates(b));
        assert_eq!(a.template_pools, b.template_pools);
        let (a, b) = (&a.signature, &b.signature);
        same!(a, b; unit, bytes, strings, ranges, indices, identifiers, paths, longidents,
            ordered_items, signatures, values, modules, module_types, type_details,
            inlined_records, record_representations, labels, constructor_arguments,
            constructors, extensions, block_types, shapes, literals, layouts,
            runtime_constructors, attributes, attribute_payloads, semantic_strings,
            deprecations, string_pairs, string_int_pairs, marshal_fragments, primitives,
            constant_arguments, ffi_attributes, ffi_params, ffi, external_declarations,
            external_modules, inline_constants, variants, row_fields, packages, variance,
            locations, descriptor_extras, mutabilities, roots);
    }

    #[test]
    fn shared_and_stored_publications_have_identical_segment_pools() {
        let options = crate::driver::CompilerOptions {
            nopervasives: true,
            ..Default::default()
        };
        let result = crate::driver::compile_source_in_process(
            SAMPLE, "Sample.res", "Sample", &options,
            &crate::cmi::persistent_env::ModuleRegistry::new(), false, None,
        ).expect("compiles");
        let shared = result.pers_struct.expect("published signature");
        let stored = std::sync::Arc::new(shared.as_ref().clone());
        assert!(shared.with_shared_graph(|_| ()).is_some());
        assert!(stored.with_shared_graph(|_| ()).is_none());
        let ctx = crate::types::context::TypeContext::new(std::sync::Arc::new(crate::context::IdGenerator::new()));
        let direct = shared.with_published_graph(&ctx, segment_of).unwrap();
        let restored = stored.with_published_graph(&ctx, segment_of).unwrap();
        assert_same(&direct, &restored);
    }

    #[test]
    fn a_compiled_unit_survives_new_old_new() {
        let options = crate::driver::CompilerOptions {
            nopervasives: true,
            ..Default::default()
        };
        let result = crate::driver::compile_source_in_process(
            SAMPLE,
            "Sample.res",
            "Sample",
            &options,
            &crate::cmi::persistent_env::ModuleRegistry::new(),
            false,
            None,
        )
        .expect("compiles");
        let unit = result.pers_struct.expect("the published signature");
        unit.with_shared_graph(|original| {
            let first = segment_of(original);
            let rebuilt = to_old(&first).into_published();
            let second = segment_of(&rebuilt);
            let again = to_old(&second).into_published();
            let third = segment_of(&again);
            // A rebuilt unit converts to the same segment as the unit it was
            // rebuilt from, once string and path rows are in rebuilt order.
            assert_same(&second, &third);
            assert_eq!(first.nodes.len(), second.nodes.len());
            assert_eq!(first.template_nodes.len(), second.template_nodes.len());
            assert_eq!(first.signature.roots.len(), second.signature.roots.len());
            // Old form: the structural fingerprint and per-item hashes of the
            // original and the rebuilt unit.
            assert_eq!(
                signature_fingerprint(&original.reader(), &original.signature),
                signature_fingerprint(&rebuilt.reader(), &rebuilt.signature)
            );
            assert_eq!(
                item_declaration_hashes(&original.reader(), &original.signature),
                item_declaration_hashes(&rebuilt.reader(), &rebuilt.signature)
            );
            // New form: the segment printer's canonical text (parent adapts the
            // entry name once tc::canonical lands).
            assert_eq!(
                crate::tc::canonical::canonical_signature(&first),
                crate::tc::canonical::canonical_signature(&second)
            );
        })
        .expect("the sample publishes a frozen graph");
    }

    #[test]
    fn generated_signatures_keep_the_old_canonical_text_and_sharing() {
        let options = crate::driver::CompilerOptions {
            nopervasives: true,
            ..Default::default()
        };
        let registry = crate::cmi::persistent_env::ModuleRegistry::new();
        // Fixed seeds and a fixed LCG make every failure exactly reproducible.
        // Each unit contains every declaration family; recursive terms combine
        // arrows, tuples, repeated constructor arguments, objects and rows.
        fn term(state: &mut u32, depth: u32) -> String {
            *state = state.wrapping_mul(1664525).wrapping_add(1013904223);
            let choice = *state;
            if depth == 0 {
                return ["int", "string", "'a"][(choice % 3) as usize].into();
            }
            let left = term(state, depth - 1);
            match choice % 6 {
                0 => {
                    let right = term(state, depth - 1);
                    format!("((~value: {left}, ~optional: {right}=?) => {left})")
                }
                1 => {
                    let right = term(state, depth - 1);
                    format!("({left}, {right})")
                }
                2 => format!("pair<{left}, {left}>"),
                3 => format!("box<{left}>"),
                4 => format!("{{\"value\": {left}, \"again\": {left}}}"),
                _ => format!("[#Empty | #Payload({left})]"),
            }
        }
        for seed in 0..512u32 {
            let mut state = seed + 1;
            let first = term(&mut state, 3);
            let second = term(&mut state, 3);
            let source = format!(
                r#"
                type box<'a>
                type pair<'a, 'b> = ('a, 'b)
                type repeated<'a> = ('a, 'a)
                type cell<'a> = {{mutable value: {first}, fixed: {second}, twins: ('a, 'a)}}
                type tagged<'a> = Empty | Payload({first}, {second})
                  | Inline({{left: {first}, right: 'a}})
                type alias<'a> = {second}
                type closed<'a> = [#Empty | #Payload({first})]
                type openRow<'a, 'row> = [> #Empty | #Payload({second})] as 'row
                type object_<'a> = {{"value": {first}, "again": 'a}}
                module Inner = {{
                  type t<'a> = {second}
                  module Deeper = {{let repeated = x => (x, x)}}
                }}
                module type S = {{
                  type t
                  let use: (~value: t, ~other: t=?) => (t, t)
                }}
                external identity: 'a => 'a = "%identity"
                exception Broken(int, string)
                let labelled = (~x, ~y=?) => (x, y, x)
                "#
            );
            let name = format!("Generated{seed}");
            let result = crate::driver::compile_source_in_process(
                &source,
                &format!("{name}.res"),
                &name,
                &options,
                &registry,
                false,
                None,
            )
            .unwrap_or_else(|error| panic!("seed {seed}: {error}\nSOURCE:\n{source}"));
            let unit = result.pers_struct.expect("generated published signature");
            super::super::from_old::check_published(&unit)
                .unwrap_or_else(|error| panic!("seed {seed}: {error}\nSOURCE:\n{source}"));
        }
    }
}
