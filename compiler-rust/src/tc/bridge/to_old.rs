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
//! becoming old node `i`, then each template's nodes in template order, one
//! old node per template node. The forwarding map is the per-template
//! [`Frame`] (an old base per template), so no node is looked up in a hash
//! table and no equal nodes are merged: each source occurrence is exactly one
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
//! a fresh persistent mutability cell holding the field's flag, and a
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
//! block allocations (fresh allocations), field mutability cell classes (one
//! cell per field), abbreviation memos and `Tlink` nodes.
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
use crate::types::asttypes::{ArgLabel, Label, Located, MutableFlag, PrivateFlag};
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
    RowFieldRef, TypeArg, TypeArgList, TypeDesc, TypeExprRef, TypeRefList,
};
use crate::types::variant_runtime::{
    Block, BlockType, ClassBlocks, Configuration, ConstructorCase, ConstructorReference, Instance,
    Layout, LayoutRef, LiteralTag, ShapeAllocation, ShapeBlocks, Tag, TaggedBlock, ValueShape,
};

const _: () = assert!(GENERIC_LEVEL as u32 == GENERIC);

/// Template reference flag of a node relative to its template's first node
/// (tc/template.rs, `Template`).
const RELATIVE: u32 = 1 << 30;

/// The longident component of a name `from_old` could not resolve
/// (`LongidentRow::Unresolved`, or a `Dot` name of NONE). No name table
/// holds this index: the pool's synthetic range ends below it.
const UNRESOLVED: StrIdx = StrIdx(u32::MAX);

/// One old published unit rebuilt from a segment: a detached old graph,
/// the old signature whose types are its nodes, and a name table of its own
/// for the graph's longident components (component `i` is `StrIdx(i)`).
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
    /// Test-only until the world slot that publishes segments calls it.
    #[cfg(test)]
    pub(crate) fn into_pool(
        self,
        pool: &crate::types::shared_store::SharedTypePool,
    ) -> PublishedGraph {
        let PublishedGraph {
            mut graph,
            signature,
            names,
        } = self.published;
        let interned: Vec<StrIdx> = {
            let names = names.read().unwrap();
            (0..names.len() as u32)
                .map(|index| pool.intern_longident_name(&names[&index]))
                .collect()
        };
        let mut parts = Arc::get_mut(&mut graph)
            .expect("an output owns its graph")
            .take_parts();
        let map = |name: &mut StrIdx| {
            if *name != UNRESOLVED {
                *name = interned[name.raw() as usize];
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
/// items), each segment node and row read once; walks are iterative.
/// Allocates once per pool and per owned old payload (strings, declaration
/// vectors, rows, boxes), never per visited type node, except where the old
/// representation owns per-node data: an arrow's labelled parameter (an
/// `ArgLabel` string and a thread-local name lookup, the only constructor of
/// `TypeArgLabel`), a field's persistent mutability cell (one relaxed atomic
/// increment), and a row's or package's owned vectors.
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

/// [`to_old`], also returning how many old nodes were made.
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
        ..
    } = rebuild;
    let mut table = AHashMap::default();
    for (index, name) in components.into_iter().enumerate() {
        table.insert(index as u32, name);
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

/// A template's place in the old node numbering: template offset `k` (with
/// `first <= k < len`) is old node `start + k - first`. A shared frame
/// (`relative` false) names segment nodes directly. 16 bytes, passed by value.
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
    payloads: SharedGraphPayloads,
    layouts: Vec<Layout>,
    /// The old node of each `roots` row.
    roots: Vec<TypeExprRef>,
    /// The frame of each template; `SHARED` for a zero-node template.
    bases: Vec<Frame>,
    /// The component index of a segment string, NONE before its first use.
    component_of: Vec<u32>,
    components: Vec<String>,
    lid_work: Vec<LidTask>,
    lid_out: Vec<Longident>,
    #[cfg(test)]
    visits: u64,
}

impl<'s> Rebuild<'s> {
    /// O(strings + string bytes): validate every string once.
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
            payloads: SharedGraphPayloads {
                lists: Vec::with_capacity(template_slots),
                args: Vec::with_capacity(seg.params.len() + seg.template_params.len()),
                rows: Vec::with_capacity(pools.variants.len()),
                lids: Vec::with_capacity(pools.packages.len()),
            },
            layouts: Vec::with_capacity(pools.layouts.len()),
            roots: Vec::with_capacity(pools.roots.len()),
            bases: Vec::with_capacity(seg.templates.len()),
            component_of: Vec::new(),
            components: Vec::new(),
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

    /// One step per segment node (each makes exactly one old node, except a
    /// synthetic tuple, which makes none) and one per list or parameter slot.
    /// One linear pass over the shared nodes, then over each template; the
    /// frames are the forwarding map. No queue, no recursion.
    fn types(&mut self) {
        let seg = self.seg;
        for &node in seg.nodes.iter() {
            let converted = self.node(node, SHARED, &seg.lists, &seg.params);
            self.nodes.push(converted);
        }
        let mut counts = vec![0u32; seg.templates.len()];
        for root in self.seg.signature.roots.iter() {
            counts[root.template as usize] += 1;
        }
        let mut list_base = 0usize;
        let mut param_base = 0usize;
        let mut pools = 0usize;
        for (index, template) in seg.templates.iter().enumerate() {
            if template.node_len == 0 {
                assert_eq!(template.list_len, 0, "an external template has no lists");
                self.bases.push(SHARED);
                continue;
            }
            let count = counts[index];
            assert_ne!(count, 0, "a template belongs to an item with roots");
            let first = u32::from(count > 1);
            let start = u32::try_from(self.nodes.len()).expect("old node limit");
            let frame = Frame {
                start,
                first,
                len: template.node_len,
                relative: true,
            };
            self.bases.push(frame);
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
            for &node in &nodes[first as usize..] {
                if node.tag() == ARROW {
                    param_base += node.arity() as usize;
                }
                let converted = self.node(node, frame, lists, params);
                self.nodes.push(converted);
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
            frame.start + (offset - frame.first)
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

    /// O(1), plus a label's string: one arrow parameter. The label is NONE
    /// (`Nolabel`) or `name << 1 | optional`.
    fn arg(&mut self, frame: Frame, param: Param) -> TypeArg {
        let typ = self.at(frame, param.ty);
        if param.label == NONE {
            assert_eq!(param.loc, NONE, "an unlabelled parameter has no location");
            return TypeArg::unlabeled(typ);
        }
        let text = self.text(param.label >> 1);
        let loc = self.loc(param.loc);
        let label = if param.label & 1 != 0 {
            ArgLabel::optional(text, loc)
        } else {
            ArgLabel::labelled(text, loc)
        };
        TypeArg::new(label, typ)
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
            ExtraDescriptor::Field { name, mutable } => {
                slot_count(2);
                let flag = if mutable {
                    MutableFlag::Mutable
                } else {
                    MutableFlag::Immutable
                };
                TypeDesc::Tfield {
                    name: self.name(name),
                    mutability: MutabilityRef::new_persistent(flag),
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

    /// O(1) after a string's first use: a longident component.
    fn component(&mut self, name: u32) -> StrIdx {
        if name == NONE {
            return UNRESOLVED;
        }
        if self.component_of.is_empty() {
            self.component_of = vec![NONE; self.strs.len()];
        }
        let slot = self.component_of[name as usize];
        if slot != NONE {
            return StrIdx::from_raw(slot);
        }
        let index = u32::try_from(self.components.len())
            .ok()
            .filter(|index| *index < UNRESOLVED.raw())
            .expect("longident component limit");
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
                        LongidentRow::Unresolved => {
                            self.lid_out.push(Longident::Lident(UNRESOLVED))
                        }
                        LongidentRow::Dot { parent, .. } => {
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
                    LongidentRow::Apply { .. } => {
                        let argument = self.lid_out.pop().expect("an argument");
                        let functor = self.lid_out.pop().expect("a functor");
                        self.lid_out
                            .push(Longident::Lapply(Box::new(functor), Box::new(argument)));
                    }
                    LongidentRow::Ident(_) | LongidentRow::Unresolved => {
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
#[path = "to_old_tests.rs"]
mod tests;
