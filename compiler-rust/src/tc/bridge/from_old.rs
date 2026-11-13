//! An old published unit (the world's frozen `SharedGraph` with its
//! signature) as a [`Segment`], published through [`crate::tc::publish::publish`].
//!
//! # Encoding
//!
//! Type nodes. Old node `i` (its offset from the graph's base,
//! `SharedGraph::node_offset`) becomes graph node `Ty(i)` before publication:
//! one linear pass, each old node read once, no recursion and no forwarding
//! table. Levels are kept (`GENERIC_LEVEL` is `graph::GENERIC`).
//!
//! - `Tvar(name)`: `VAR`, `a` the name string or NONE, `b` 0.
//! - `Tlink(t)`: `LINK` to `t`; publication follows it, as `repr` does.
//! - `Tarrow`: `ARROW`, `a` the result, `b` the first `Param`. A parameter's
//!   label is NONE (`Nolabel`) or `name << 1 | optional` with `name` a string;
//!   its `loc` a `locations` row, NONE for `Nolabel`.
//! - `Ttuple`: `TUPLE`. `Tconstr`: `CONSTR`, `a` a `paths` row, list slot 0 the
//!   empty abbreviation memo (NONE), then the arguments.
//! - Every other descriptor is `TUPLE | segment::EXTENDED` (see
//!   [`ExtraDescriptor`]): `a` indexes `descriptor_extras`, the children are
//!   the node's ordinary list slots, and payload rows name them by slot
//!   relative to the node's list start, so templates relocate them unchanged.
//!   `Tvariant` slots are, in order, each row field's types, then `row_more`,
//!   then the row name's arguments; `Tpackage` slots are its arguments.
//!
//! Schemes. Every signature item, nested ones included, is one scheme: the
//! types its declaration holds (a value's type; a type's parameters,
//! manifest, label and constructor types, inlined records; an extension's
//! parameters, arguments and result) are its roots, in that order, and are
//! numbered consecutively in `SignaturePools::roots`. Rows refer to them by
//! root index. An item with one root publishes that root; an item with more
//! publishes a synthetic generic `TUPLE` of them, which is node 0 of its
//! template and is named by no root. Every root then names a node of the
//! item's template, so equal positions across fields stay one node, while
//! non-generic nodes are shared across items.
//!
//! Metadata. Strings are one byte pool with a range per distinct string.
//! Paths are rows deduplicated by the interned path node. Identifiers keep
//! name, stamp and flags; their scope is `segment::IdentRow::scope`. Every
//! other declaration field has its row in [`SignaturePools`]:
//!
//! - `signatures[0]` is the unit's signature; `children[i]` is the sorted
//!   export table of `signatures[i]`. Export names are segment string
//!   indices; a later item hides an earlier one of the same name and kind.
//!   A value's payload is a `values` row, a type's a `type_declarations` row,
//!   a constructor's or label's a `members` row (an extension constructor's
//!   `extensions` row with `EXTENSION_PAYLOAD`), a module's or module type's
//!   a `modules` row.
//! - `ordered_items` rows: `declaration` is a `values`, `type_declarations`,
//!   `extensions` or `modules` row by kind (NONE for classes).
//! - `type_details[i]` is the cold half of `type_declarations[i]`.
//!   `TypeDecl::params` is the first parameter root, `manifest` a root, and
//!   `members` the record's labels or the variant's constructors as
//!   `MemberDecl { name, args: labels or constructors row, tag_or_pos:
//!   position, flags }` (label flags: 1 mutable, 2 optional; constructor
//!   flags: 1 has a runtime tag, 2 has a result type). `TypeDecl::flags`:
//!   1 private, 2 immediate, 4 unboxed, 8 local constraint, 16 abbreviation.
//!   `TypeDetailsRow::representation` is a `record_representations` row for a
//!   record, a `layouts` row for a variant, NONE otherwise; `newtype_level`
//!   and `scope_level` are NONE when absent.
//! - Ranges of strings (`StrTuple`, block-type ancestors, external scopes)
//!   index `indices`, each a string. `PolyVar` and import attributes index
//!   `ranges`, a range of `string_pairs`.
//! - Missing longident component names become explicit unresolved rows with
//!   the raw diagnostic index: the printed section uses `#index`, while the
//!   structural section uses `<unresolved>`. A missing file name (for example
//!   `Location::none`'s) is NONE.
//!
//! Not kept, by design: abbreviation memos, `Tlink` levels (publication
//! follows links), the allocation identities of shapes and class blocks
//! (types/canonical_sig.rs leaves them out of a unit's interface), location
//! allocation identities, and the old row-field links (a frozen row has none).

use std::sync::RwLock;

use crate::binary_ast::marshal::MarshalFragment;
use crate::fast_hash::AHashMap;
use crate::ident::Ident;
use crate::intern::StrIdx;
use crate::location::Position;
use crate::parser::longident::Longident;
use crate::tc::graph::{ARROW, CONSTR, GENERIC, Graph, LINK, NONE, Node, Param, TUPLE, Ty, VAR};
use crate::tc::publish::publish;
use crate::tc::segment::*;
use crate::types::asttypes::{MutableFlag, PrivateFlag};
use crate::types::decl::{
    AliasPresence, Attribute, AttributePayload, ConstructorArguments, ConstructorDeclaration,
    ExtStatus, ExtensionConstructor, LabelDeclaration, ModuleType, PrimKind, PrimitiveDescription,
    RecStatus as OldRecStatus, RecordRepresentation, Signature, SignatureItem, TypeDeclaration,
    TypeInlinedType, TypeKind, TypeRepresentation, ValueDescription, ValueKind,
};
use crate::types::decl_loc::{DeclLoc, DeclLocKind};
use crate::types::external_ffi_types as ffi;
use crate::types::path::{Path, PathView};
use crate::types::shared_store::SharedGraph;
use crate::types::type_expr::{GENERIC_LEVEL, RowField, TypeDesc, TypeExprRef};
use crate::types::variant_runtime::{
    Block, BlockType, ConstructorCase, Instance, LayoutRef, LiteralTag, TaggedBlock, ValueShape,
};

const _: () = assert!(GENERIC_LEVEL as u32 == GENERIC);

/// Template reference flag of a node relative to an instance's first node
/// (tc/template.rs, `Template`).
const RELATIVE: u32 = 1 << 30;

/// One old published unit: its frozen graph, the signature whose types are
/// nodes of that graph, and what the graph does not hold.
pub struct Input<'a> {
    graph: &'a SharedGraph,
    signature: &'a Signature,
    unit: &'a str,
    deprecated: Option<&'a str>,
    /// The pool's name table, for longident components and file names.
    names: &'a RwLock<AHashMap<u32, String>>,
    /// Supplied by the signature's producer; never computed by a graph walk.
    digest: [u8; 32],
}

/// O(1): borrow a frozen unit; its producer supplies the digest.
impl<'a> Input<'a> {
    pub(crate) fn new(
        graph: &'a SharedGraph,
        signature: &'a Signature,
        unit: &'a str,
        deprecated: Option<&'a str>,
        names: &'a RwLock<AHashMap<u32, String>>,
        digest: [u8; 32],
    ) -> Self {
        Self {
            graph,
            signature,
            unit,
            deprecated,
            names,
            digest,
        }
    }
}

/// O(unit-name + deprecation bytes), with no graph walk. A versioned
/// compatibility digest carries the old producer's existing 64-bit signature
/// fingerprint and separate name/deprecation hashes; it is not cryptographic.
fn published_digest(unit: &crate::cmi::portable_types::PortablePersStruct) -> [u8; 32] {
    use std::hash::BuildHasher;
    let name = crate::fast_hash::FastState.hash_one(&unit.ps_name);
    let deprecation = crate::fast_hash::FastState.hash_one(&unit.ps_deprecated);
    let mut digest = [0; 32];
    digest[..8].copy_from_slice(&unit.fingerprint.to_le_bytes());
    digest[8..16].copy_from_slice(&name.to_le_bytes());
    digest[16..24].copy_from_slice(&deprecation.to_le_bytes());
    digest[24..].copy_from_slice(b"OLD-SIG1");
    digest
}

/// Request this unit's segment in the current world. Only the first request
/// converts; ordinary old-checker registration and loading do not call it.
pub(crate) fn published_segment(
    unit: &std::sync::Arc<crate::cmi::portable_types::PortablePersStruct>,
    ctx: &crate::types::context::TypeContext,
) -> Result<std::sync::Arc<Segment>, String> {
    ctx.world().converted_segment(unit, || {
        unit.with_published_graph(ctx, |published| {
            from_old(Input::new(
                &published.graph,
                &published.signature,
                &unit.ps_name,
                unit.ps_deprecated.as_deref(),
                &published.names,
                published_digest(unit),
            ))
        })
    })
}

/// O(conversion + both canonical printers). Check mode explicitly requests
/// this unit's new representation, even when it has no dependent. The normal
/// old-checker path never calls this function.
pub(crate) fn check_published(
    unit: &std::sync::Arc<crate::cmi::portable_types::PortablePersStruct>,
) -> Result<(), String> {
    // Reference printing must not fill caches or overlays in the compiling
    // worker's context. This reader borrows the same immutable world.
    let ctx = crate::types::context::TypeContext::new(std::sync::Arc::new(
        crate::context::IdGenerator::new(),
    ));
    let old = crate::cmi::portable_types::internalize_pers_struct(unit.clone(), &ctx);
    let expected = crate::types::canonical_sig::canonical_signature(
        &ctx,
        &unit.ps_name,
        &old.ps_sig,
        unit.ps_deprecated.as_deref(),
        None,
    );
    let segment = published_segment(unit, &ctx)?;
    let actual = crate::tc::canonical::canonical_signature(&segment);
    compare_text(&unit.ps_name, "segment", &expected, &actual)?;
    let rebuilt = ctx.world().converted_old(unit, || super::to_old::to_old(&segment));
    let restored = rebuilt.canonical_text()?;
    compare_text(&unit.ps_name, "round-trip", &expected, &restored)?;
    log::debug!(target: "rescript_checker", "tc-segment-canonical {}", unit.ps_name);
    Ok(())
}

/// O(the matching prefix in bytes); reports the unit and first differing line.
fn compare_text(
    unit: &str,
    representation: &str,
    expected: &str,
    actual: &str,
) -> Result<(), String> {
    let mut before = expected.split_inclusive('\n');
    let mut after = actual.split_inclusive('\n');
    let mut line = 1;
    loop {
        let a = before.next();
        let b = after.next();
        if a != b {
            return Err(format!(
                "checker signature mismatch in {unit} ({representation}), line {line}:\nold: {:?}\nnew: {:?}",
                a.unwrap_or("<end>"),
                b.unwrap_or("<end>"),
            ));
        }
        if a.is_none() {
            return Ok(());
        }
        line += 1;
    }
}

/// O(old nodes + edges + signature metadata + exports·log exports + fields·log fields), plus
/// [`publish`]'s cost. Reads each old node once in one linear pass; the
/// signature is walked once with an explicit stack; the name table's lock is
/// taken once. Panics on a handle that is not of the unit's graph, a level
/// below zero, or a row-field link, none of which a frozen graph holds.
/// A 10,000-node singleton-tuple chain takes exactly 10,000 old-source visits;
/// with publication the test counter is at most 30,001 (10,000 old visits,
/// 10,000 captures, 9,999 slots and two item steps). Metadata work is described
/// separately by the helpers below; it is not another old-node visit.
pub fn from_old(input: Input<'_>) -> Segment {
    run(input).0
}

/// Test builds count the old nodes read; the count is not a step.
struct OldVisits {
    #[cfg(test)]
    count: u64,
}

/// [`from_old`], also returning how many old nodes were read.
fn run(input: Input<'_>) -> (Segment, OldVisits) {
    // The name table's lock is held for the conversion only, not publication.
    let (mut tc, rows, roots, schemes, unit, items, children, visits) = {
        let names = input.names.read().unwrap();
        let mut convert = Convert::new(input.graph, &names);
        convert.nodes();
        convert.resolve_mutabilities();
        let unit = convert.unit(input.unit, input.deprecated);
        convert.signatures(input.signature);
        convert.resolve_scopes();
        let (items, children) = convert.export_tables();
        let visits = OldVisits {
            #[cfg(test)]
            count: convert.old_visits,
        };
        let Convert {
            tc,
            rows,
            roots,
            schemes,
            ..
        } = convert;
        (tc, rows, roots, schemes, unit, items, children, visits)
    };
    let publish_roots = scheme_roots(&mut tc, &roots, &schemes);
    let (signature, type_declarations, members) = rows.into_pools(unit);
    let segment = Segment {
        type_declarations,
        members,
        items: items.into_boxed_slice(),
        children: children.into_boxed_slice(),
        digest: input.digest,
        signature,
        ..Segment::default()
    };
    let mut segment = publish(tc, &publish_roots, segment);
    segment.signature.roots = resolve_roots(&segment, &schemes, roots.len());
    (segment, visits)
}

/// O(schemes + roots of multi-root schemes). One publication root per item:
/// the item's only root, or a new generic tuple of its roots.
fn scheme_roots(graph: &mut Graph, roots: &[Ty], schemes: &[Range]) -> Vec<Ty> {
    let mut out = Vec::with_capacity(schemes.len());
    for scheme in schemes {
        let item = &roots[scheme.start as usize..(scheme.start + scheme.len) as usize];
        if let [root] = item {
            out.push(*root);
            continue;
        }
        let b = graph.lists.len() as u32;
        graph.lists.extend_from_slice(item);
        out.push(graph.push(Node {
            head: head(TUPLE, item.len()),
            level: GENERIC,
            a: 0,
            b,
        }));
    }
    out
}

/// O(templates + roots). Name every root by its item's template: a
/// synthetic tuple is captured first, so its list is the first of its
/// template's lists, which follow each other in template order.
fn resolve_roots(segment: &Segment, schemes: &[Range], count: usize) -> Box<[SchemeRoot]> {
    let mut out = vec![
        SchemeRoot {
            template: NONE,
            ty: Ty(NONE)
        };
        count
    ];
    let mut lists = 0usize;
    for (index, scheme) in schemes.iter().enumerate() {
        let template = segment.templates[index];
        let target = &mut out[scheme.start as usize..(scheme.start + scheme.len) as usize];
        let template_index = index as u32;
        if scheme.len == 1 {
            let ty = if template.node_len == 0 {
                Ty(template.nodes)
            } else {
                Ty(RELATIVE)
            };
            target[0] = SchemeRoot {
                template: template_index,
                ty,
            };
        } else {
            let root = segment.template_nodes[template.nodes as usize];
            assert!(template.node_len != 0 && root.b == 0 && root.arity() == scheme.len);
            for (k, slot) in target.iter_mut().enumerate() {
                let reference = segment.template_lists[lists + k];
                let ty = if reference.0 & RELATIVE != 0 {
                    reference
                } else {
                    segment.template_externals[reference.0 as usize]
                };
                *slot = SchemeRoot {
                    template: template_index,
                    ty,
                };
            }
        }
        lists += template.list_len as usize;
    }
    debug_assert_eq!(lists, segment.template_lists.len());
    out.into_boxed_slice()
}

/// O(1): a node head; arities need 24 bits.
fn head(tag: u32, arity: usize) -> u32 {
    let arity = u32::try_from(arity)
        .ok()
        .filter(|arity| *arity < 1 << 24)
        .expect("descriptor arity limit");
    tag | arity << 8
}

/// Amortized O(1): append a row and return its index. Indices stay below
/// bit 31, which `FUNCTOR_SCOPE` and `EXTENSION_PAYLOAD` use.
fn push<T>(pool: &mut Vec<T>, row: T) -> u32 {
    let index = pool.len();
    assert!(index < 1 << 31, "segment row limit");
    pool.push(row);
    index as u32
}

/// O(1): the graph node of an old node of `graph`.
fn offset(graph: &SharedGraph, r: TypeExprRef) -> Ty {
    let offset = graph
        .node_offset(r)
        .expect("a published unit refers only to nodes of its own graph");
    Ty(offset as u32)
}

/// O(1): the length of a pool tail as a range length.
fn tail(len: usize, start: u32) -> Range {
    Range {
        start,
        len: len as u32 - start,
    }
}

macro_rules! rows {
    ($($field:ident: $ty:ty),* $(,)?) => {
        /// The segment's cold pools while they are written.
        #[derive(Default)]
        struct Rows {
            $($field: Vec<$ty>,)*
            type_declarations: Vec<TypeDecl>,
            members: Vec<MemberDecl>,
        }

        impl Rows {
            /// O(total pool bytes) in the worst case: at most one shrink per pool.
            fn into_pools(self, unit: UnitRow) -> (SignaturePools, Box<[TypeDecl]>, Box<[MemberDecl]>) {
                (
                    SignaturePools {
                        unit: Some(unit),
                        $($field: self.$field.into_boxed_slice(),)*
                        roots: Box::default(),
                    },
                    self.type_declarations.into_boxed_slice(),
                    self.members.into_boxed_slice(),
                )
            }
        }
    };
}

rows!(
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

/// An identifier that binds a name in the signature, for scope resolution.
#[derive(Clone, Copy)]
struct Binder {
    stamp: i32,
    scope: u32,
}

/// One name of a signature's export table before sorting.
#[derive(Clone, Copy)]
struct Export {
    table: u32,
    name: u32,
    payload: u32,
    order: u32,
    kind: ExportKind,
}

/// Signature walk work: a signature to write into a `signatures` slot, or a
/// module type into a `module_types` slot. Thin references keep it 16 bytes.
#[derive(Clone, Copy)]
enum Task<'g> {
    Signature(&'g Signature, u32),
    ModuleType(&'g ModuleType, u32),
}

/// Longident walk work, an explicit post-order.
#[derive(Clone, Copy)]
enum LidStep<'g> {
    Enter(&'g Longident),
    Exit(&'g Longident),
}

struct Convert<'g> {
    graph: &'g SharedGraph,
    names: &'g AHashMap<u32, String>,
    /// A detached graph's portable file keys and names, sorted by key.
    files: Vec<(u32, &'g str)>,
    tc: Graph,
    rows: Rows,
    /// Distinct strings by content: names have no dense index here.
    strings: AHashMap<&'g str, u32>,
    /// Path rows by interned path node: paths have no dense index.
    path_rows: AHashMap<usize, u32>,
    path_work: Vec<Path>,
    lid_work: Vec<LidStep<'g>>,
    lid_results: Vec<u32>,
    /// Layout row by layout offset, NONE before its first reference.
    layout_rows: Vec<u32>,
    /// (old persistent cell identity, extra-descriptor row), once per field.
    mutability_work: Vec<(u32, u32)>,
    binders: Vec<Binder>,
    /// Every scheme root, numbered as `SignaturePools::roots`.
    roots: Vec<Ty>,
    /// Each item's range of `roots`, for items with at least one root.
    schemes: Vec<Range>,
    exports: Vec<Export>,
    unit_name: u32,
    #[cfg(test)]
    old_visits: u64,
}

impl<'g> Convert<'g> {
    /// O(layouts + file names · log file names), no node is read.
    fn new(graph: &'g SharedGraph, names: &'g AHashMap<u32, String>) -> Self {
        let mut files: Vec<(u32, &'g str)> = if graph.is_detached() {
            graph
                .carried
                .file_names
                .iter()
                .map(|(key, name)| (*key, name.as_str()))
                .collect()
        } else {
            Vec::new()
        };
        files.sort_unstable_by_key(|(key, _)| *key);
        let sizes = graph.sizes();
        let tc = Graph {
            nodes: Vec::with_capacity(sizes.nodes),
            lists: Vec::with_capacity(sizes.list_items + sizes.nodes),
            params: Vec::with_capacity(sizes.arg_items),
            ..Graph::default()
        };
        Self {
            graph,
            names,
            files,
            tc,
            rows: Rows::default(),
            strings: AHashMap::default(),
            path_rows: AHashMap::default(),
            path_work: Vec::new(),
            lid_work: Vec::new(),
            lid_results: Vec::new(),
            layout_rows: vec![NONE; graph.layouts().len()],
            mutability_work: Vec::new(),
            binders: Vec::new(),
            roots: Vec::new(),
            schemes: Vec::new(),
            exports: Vec::new(),
            unit_name: NONE,
            #[cfg(test)]
            old_visits: 0,
        }
    }

    /// Amortized O(length): the index of a distinct string.
    fn string(&mut self, text: &'g str) -> u32 {
        if let Some(&index) = self.strings.get(text) {
            return index;
        }
        let start = u32::try_from(self.rows.bytes.len()).expect("segment string bytes limit");
        self.rows.bytes.extend_from_slice(text.as_bytes());
        let len = u32::try_from(text.len()).expect("segment string length limit");
        let index = push(&mut self.rows.strings, Range { start, len });
        self.strings.insert(text, index);
        index
    }

    /// Amortized O(length); NONE for none.
    fn opt_string(&mut self, text: Option<&'g str>) -> u32 {
        match text {
            Some(text) => self.string(text),
            None => NONE,
        }
    }

    /// Amortized O(strings): a contiguous range of `indices`, each a string.
    fn string_list(&mut self, texts: &'g [String]) -> Range {
        let start = self.rows.indices.len() as u32;
        for text in texts {
            let index = self.string(text);
            self.rows.indices.push(index);
        }
        tail(self.rows.indices.len(), start)
    }

    /// Amortized O(pairs).
    fn string_pairs(&mut self, pairs: &'g [(String, String)]) -> Range {
        let start = self.rows.string_pairs.len() as u32;
        for (first, second) in pairs {
            let row = StringPair {
                first: self.string(first),
                second: self.string(second),
            };
            self.rows.string_pairs.push(row);
        }
        tail(self.rows.string_pairs.len(), start)
    }

    /// Amortized O(1): a name the pool's table holds, as a string.
    fn component(&mut self, name: StrIdx) -> Option<u32> {
        let names = self.names;
        let text = names.get(&name.raw())?;
        Some(self.string(text.as_str()))
    }

    /// One step per old node, O(nodes + edges + path and row metadata). A
    /// linear pass in offset order: a child is named by its offset whether
    /// or not it has been read, so there is no forwarding table, no queue
    /// and no recursion. This is the only read of the old nodes.
    fn nodes(&mut self) {
        let graph = self.graph;
        for node in graph.nodes() {
            #[cfg(test)]
            {
                crate::tc::steps::tick();
                self.old_visits += 1;
            }
            let level = u32::try_from(node.level).expect("a published level is not negative");
            let b = self.tc.lists.len() as u32;
            let converted = match node.desc {
                TypeDesc::Tvar(name) => Node {
                    head: VAR,
                    level,
                    a: self.opt_string(name.map(|name| name.as_str())),
                    b: 0,
                },
                TypeDesc::Tlink(target) => Node {
                    head: LINK,
                    level,
                    a: offset(graph, target).0,
                    b: 0,
                },
                TypeDesc::Tarrow { args, ret } => {
                    let start = self.tc.params.len() as u32;
                    let args = graph.args(args);
                    for arg in args {
                        let label = arg.label();
                        let (name, loc) = match label.label_name() {
                            None => (NONE, NONE),
                            Some(name) => {
                                let name = self.string(name);
                                assert!(name < 1 << 31, "label string limit");
                                (
                                    name << 1 | u32::from(label.is_optional()),
                                    self.loc(label.loc()),
                                )
                            }
                        };
                        let ty = offset(graph, arg.typ);
                        self.tc.params.push(Param {
                            ty,
                            label: name,
                            loc,
                        });
                    }
                    Node {
                        head: head(ARROW, args.len()),
                        level,
                        a: offset(graph, ret).0,
                        b: start,
                    }
                }
                TypeDesc::Ttuple(elements) => {
                    let elements = graph.list(elements);
                    self.slots(elements);
                    Node {
                        head: head(TUPLE, elements.len()),
                        level,
                        a: 0,
                        b,
                    }
                }
                TypeDesc::Tconstr { path, args, .. } => {
                    let path = self.path(path);
                    let args = graph.list(args);
                    self.tc.lists.push(Ty(NONE));
                    self.slots(args);
                    Node {
                        head: head(CONSTR, args.len()),
                        level,
                        a: path,
                        b,
                    }
                }
                TypeDesc::Tobject { fields } => {
                    self.slot(fields);
                    self.extended(level, ExtraDescriptor::Object, b)
                }
                TypeDesc::Tfield {
                    name,
                    mutability,
                    typ,
                    rest,
                } => {
                    assert!(
                        mutability.is_persistent(),
                        "a published field cell is persistent"
                    );
                    let extra = ExtraDescriptor::Field {
                        name: self.string(name.as_str()),
                        mutability: NONE,
                    };
                    self.slot(typ);
                    self.slot(rest);
                    let node = self.extended(level, extra, b);
                    self.mutability_work.push((mutability.0, node.a));
                    node
                }
                TypeDesc::Tnil => self.extended(level, ExtraDescriptor::Nil, b),
                TypeDesc::Tsubst(target) => {
                    self.slot(target);
                    self.extended(level, ExtraDescriptor::Substitution, b)
                }
                TypeDesc::Tunivar(name) => {
                    let name = self.opt_string(name.map(|name| name.as_str()));
                    self.extended(level, ExtraDescriptor::Univar(name), b)
                }
                TypeDesc::Tpoly { body, vars } => {
                    self.slot(body);
                    self.slots(graph.list(vars));
                    self.extended(level, ExtraDescriptor::Poly, b)
                }
                TypeDesc::Tvariant(row) => {
                    let row = self.variant(graph.row(row), b);
                    self.extended(level, ExtraDescriptor::Variant(row), b)
                }
                TypeDesc::Tpackage { path, lids, args } => {
                    let path = self.path(path);
                    let start = self.rows.indices.len() as u32;
                    for lid in graph.lids(lids) {
                        let row = self.longident(lid);
                        self.rows.indices.push(row);
                    }
                    let longidents = tail(self.rows.indices.len(), start);
                    let args = graph.list(args);
                    self.slots(args);
                    let row = PackageRow {
                        path,
                        longidents,
                        arguments: Range {
                            start: 0,
                            len: args.len() as u32,
                        },
                    };
                    let row = push(&mut self.rows.packages, row);
                    self.extended(level, ExtraDescriptor::Package(row), b)
                }
            };
            self.tc.push(converted);
        }
    }

    /// O(fields · log fields): sort cell identities collected during the only
    /// source-node pass. Cells have process-wide sparse IDs, not graph offsets;
    /// an identity sort avoids both a hash probe per node and a world-sized
    /// forwarding array. Only the compact field rows are revisited, not the
    /// source graph. Equal values never merge different cells.
    fn resolve_mutabilities(&mut self) {
        let mut work = std::mem::take(&mut self.mutability_work);
        work.sort_unstable_by_key(|&(cell, _)| cell);
        let mut previous = None;
        let mut index = NONE;
        for (raw, extra) in work {
            if previous != Some(raw) {
                let cell = crate::types::type_expr::MutabilityRef(raw);
                index = push(
                    &mut self.rows.mutabilities,
                    cell.persistent_value() == MutableFlag::Mutable,
                );
                previous = Some(raw);
            }
            let ExtraDescriptor::Field { mutability, .. } =
                &mut self.rows.descriptor_extras[extra as usize]
            else {
                unreachable!("only field descriptors carry cells")
            };
            *mutability = index;
        }
    }

    /// Amortized O(1): append one list slot.
    fn slot(&mut self, r: TypeExprRef) {
        let ty = offset(self.graph, r);
        self.tc.lists.push(ty);
    }

    /// Amortized O(children): append list slots.
    fn slots(&mut self, children: &[TypeExprRef]) {
        let graph = self.graph;
        self.tc
            .lists
            .extend(children.iter().map(|&child| offset(graph, child)));
    }

    /// Amortized O(1): an extended descriptor whose slots start at `b`.
    fn extended(&mut self, level: u32, extra: ExtraDescriptor, b: u32) -> Node {
        let a = push(&mut self.rows.descriptor_extras, extra);
        Node {
            head: head(TUPLE, self.tc.lists.len() - b as usize) | EXTENDED,
            level,
            a,
            b,
        }
    }

    /// O(fields + their types + name arguments): a row's slots and rows.
    fn variant(&mut self, row: &'g crate::types::type_expr::RowDesc, b: u32) -> u32 {
        let fields = self.rows.row_fields.len() as u32;
        for (label, field) in row.row_fields.iter() {
            let first = self.tc.lists.len() as u32 - b;
            let kind = match field {
                RowField::Rpresent(ty) => {
                    if let Some(ty) = ty {
                        self.slot(*ty);
                    }
                    RowFieldKind::Present
                }
                RowField::Reither {
                    constant,
                    types,
                    matched,
                    link,
                } => {
                    assert!(link.is_null(), "a published row field has no link");
                    self.slots(types);
                    RowFieldKind::Either {
                        constant: *constant,
                        matched: *matched,
                    }
                }
                RowField::Rabsent => RowFieldKind::Absent,
            };
            let types = tail(self.tc.lists.len() - b as usize, first);
            let row = RowFieldRow {
                name: self.string(label.as_str()),
                types,
                link: NONE,
                kind,
            };
            self.rows.row_fields.push(row);
        }
        let fields = tail(self.rows.row_fields.len(), fields);
        let more = self.tc.lists.len() as u32 - b;
        self.slot(row.row_more);
        let (name, name_arguments) = match &row.row_name {
            Some((path, args)) => {
                let path = self.path(*path);
                let first = self.tc.lists.len() as u32 - b;
                self.slots(args);
                (path, tail(self.tc.lists.len() - b as usize, first))
            }
            None => (NONE, Range::default()),
        };
        let row = VariantRow {
            fields,
            more,
            name,
            name_arguments,
            closed: row.row_closed,
            fixed: row.row_fixed,
        };
        push(&mut self.rows.variants, row)
    }

    /// O(components), explicit post-order, reused buffers.
    fn longident(&mut self, root: &'g Longident) -> u32 {
        self.lid_work.clear();
        self.lid_results.clear();
        self.lid_work.push(LidStep::Enter(root));
        while let Some(step) = self.lid_work.pop() {
            let row = match step {
                LidStep::Enter(lid) => match lid {
                    Longident::Lident(name) => match self.component(*name) {
                        Some(name) => LongidentRow::Ident(name),
                        None => LongidentRow::Unresolved(name.raw()),
                    },
                    Longident::Ldot(prefix, _) => {
                        self.lid_work.push(LidStep::Exit(lid));
                        self.lid_work.push(LidStep::Enter(prefix));
                        continue;
                    }
                    Longident::Lapply(functor, argument) => {
                        self.lid_work.push(LidStep::Exit(lid));
                        self.lid_work.push(LidStep::Enter(argument));
                        self.lid_work.push(LidStep::Enter(functor));
                        continue;
                    }
                },
                LidStep::Exit(lid) => match lid {
                    Longident::Ldot(_, name) => {
                        let parent = self.lid_results.pop().expect("a prefix row");
                        match self.component(*name) {
                            Some(name) => LongidentRow::Dot { parent, name },
                            None => LongidentRow::UnresolvedDot { parent, raw: name.raw() },
                        }
                    }
                    Longident::Lapply(..) => {
                        let argument = self.lid_results.pop().expect("an argument row");
                        let functor = self.lid_results.pop().expect("a functor row");
                        LongidentRow::Apply { functor, argument }
                    }
                    Longident::Lident(_) => unreachable!("an identifier is never exited"),
                },
            };
            let row = push(&mut self.rows.longidents, row);
            self.lid_results.push(row);
        }
        self.lid_results.pop().expect("a longident row")
    }

    /// Amortized O(1) for a converted path; otherwise O(new path nodes) with
    /// an explicit stack. Rows are shared by interned path node.
    fn path(&mut self, path: Path) -> u32 {
        if let Some(&row) = self.path_rows.get(&path.node_addr()) {
            return row;
        }
        self.path_work.clear();
        self.path_work.push(path);
        while let Some(top) = self.path_work.last().copied() {
            if self.path_rows.contains_key(&top.node_addr()) {
                self.path_work.pop();
                continue;
            }
            let row = match *top.view() {
                PathView::Pident(id) => Some(PathRow::Ident(self.ident(id, NONE))),
                PathView::Pdot(parent, name, position) => {
                    match self.path_rows.get(&parent.node_addr()).copied() {
                        Some(parent) => Some(PathRow::Dot {
                            parent,
                            name: self.string(name.as_str()),
                            position,
                        }),
                        None => {
                            self.path_work.push(parent);
                            None
                        }
                    }
                }
                PathView::Papply(functor, argument) => {
                    let f = self.path_rows.get(&functor.node_addr()).copied();
                    let a = self.path_rows.get(&argument.node_addr()).copied();
                    match (f, a) {
                        (Some(functor), Some(argument)) => {
                            Some(PathRow::Apply { functor, argument })
                        }
                        _ => {
                            if f.is_none() {
                                self.path_work.push(functor);
                            }
                            if a.is_none() {
                                self.path_work.push(argument);
                            }
                            None
                        }
                    }
                }
            };
            if let Some(row) = row {
                self.path_work.pop();
                let index = push(&mut self.rows.paths, row);
                self.path_rows.insert(top.node_addr(), index);
            }
        }
        self.path_rows[&path.node_addr()]
    }

    /// Amortized O(path) or O(1). An absent source path becomes an absolute
    /// binder address: (this unit, ordered item), not a name to resolve in an
    /// importing environment. This is the publication qualification of
    /// compiler/ml/env.ml:1369-1402 (prefix_idents), using a binder address.
    fn declared_path(&mut self, path: Option<Path>, ident: u32) -> u32 {
        match path {
            Some(path) => self.path(path),
            None => push(&mut self.rows.paths, PathRow::Ident(ident)),
        }
    }

    /// Amortized O(1): an identifier row.
    fn ident(&mut self, id: Ident, scope: u32) -> u32 {
        let row = IdentRow {
            name: self.string(id.name()),
            stamp: id.stamp(),
            flags: u32::from(id.flags().bits()),
            scope,
        };
        push(&mut self.rows.identifiers, row)
    }

    /// Amortized O(1): the identifier of a binder whose scope is `scope`.
    fn binder(&mut self, id: Ident, scope: u32) -> u32 {
        let row = self.ident(id, scope);
        self.binders.push(Binder {
            stamp: id.stamp(),
            scope,
        });
        row
    }

    /// O(binders · log binders + identifiers · log binders), no walk: give
    /// every identifier naming a binder of the signature that binder's
    /// scope (compiler/ext/ident.ml:75: equal nonzero stamps), and the unit's own
    /// persistent identifier `UNIT_SCOPE`.
    fn resolve_scopes(&mut self) {
        let mut binders = std::mem::take(&mut self.binders);
        binders.sort_unstable_by_key(|binder| binder.stamp);
        let unit = self.unit_name;
        for row in self.rows.identifiers.iter_mut() {
            if row.scope != NONE {
                continue;
            }
            if row.stamp == 0 {
                if row.name == unit {
                    row.scope = UNIT_SCOPE;
                }
                continue;
            }
            let at = binders.partition_point(|binder| binder.stamp < row.stamp);
            if let Some(binder) = binders.get(at)
                && binder.stamp == row.stamp
            {
                row.scope = binder.scope;
            }
        }
    }

    /// O(1) plus file-name lookups: a location row.
    fn loc(&mut self, loc: DeclLoc) -> u32 {
        let graph = self.graph;
        let location = match loc.kind() {
            DeclLocKind::Source => loc.source_location().expect("a source handle"),
            DeclLocKind::Shared => {
                assert_eq!(loc.owner(), graph.base(), "a location of another graph");
                graph.locations().get(loc.index())
            }
            DeclLocKind::Portable => {
                assert!(graph.is_detached(), "a portable location in a pool graph");
                graph.locations().get(loc.index())
            }
            kind @ (DeclLocKind::Local | DeclLocKind::Store) => {
                panic!("{kind:?} location in a published unit")
            }
        };
        let row = LocationRow {
            start: self.position(location.loc_start),
            end: self.position(location.loc_end),
            origin: location.origin.raw(),
            ghost: location.loc_ghost,
        };
        push(&mut self.rows.locations, row)
    }

    /// O(log file names) for a detached graph, else one name-table probe.
    fn position(&mut self, position: Position) -> PositionRow {
        let raw = position.file_name.raw();
        let names = self.names;
        let name = if self.graph.is_detached() {
            self.files
                .binary_search_by_key(&raw, |(key, _)| *key)
                .ok()
                .map(|index| self.files[index].1)
        } else {
            names.get(&raw).map(String::as_str)
        };
        PositionRow {
            filename: self.opt_string(name),
            line: position.line,
            beginning_of_line: position.bol,
            offset: position.cnum,
        }
    }

    /// O(1): the unit's row; its signature is `signatures[0]`.
    fn unit(&mut self, unit: &'g str, deprecated: Option<&'g str>) -> UnitRow {
        let name = self.string(unit);
        self.unit_name = name;
        let path = self.path(Path::pident(Ident::create_persistent(unit)));
        UnitRow {
            name,
            deprecated: self.opt_string(deprecated),
            signature: 0,
            path,
        }
    }

    /// O(items + declaration metadata), one explicit stack of 16-byte tasks
    /// whatever the nesting of modules and functors.
    fn signatures(&mut self, top: &'g Signature) {
        let mut work = Vec::new();
        let slot = push(&mut self.rows.signatures, Range::default());
        work.push(Task::Signature(top, slot));
        while let Some(task) = work.pop() {
            match task {
                Task::Signature(signature, slot) => {
                    let start = self.rows.ordered_items.len() as u32;
                    for item in signature.iter() {
                        let row = self.item(item, slot, &mut work);
                        push(&mut self.rows.ordered_items, row);
                    }
                    self.rows.signatures[slot as usize] =
                        tail(self.rows.ordered_items.len(), start);
                }
                Task::ModuleType(module_type, slot) => {
                    let row = self.module_type(module_type, slot, &mut work);
                    self.rows.module_types[slot as usize] = row;
                }
            }
        }
    }

    /// O(the item's declaration metadata); a nested module type is deferred.
    /// `table` is the enclosing signature's slot, which names its exports.
    fn item(
        &mut self,
        item: &'g SignatureItem,
        table: u32,
        work: &mut Vec<Task<'g>>,
    ) -> SignatureItemRow {
        let index = self.rows.ordered_items.len() as u32;
        let first = self.roots.len() as u32;
        let row = match item {
            SignatureItem::SigValue(id, decl) => {
                let ident = self.binder(*id, index);
                let declaration = self.value(decl, ident);
                self.export(table, id.name(), ExportKind::Value, declaration, index);
                SignatureItemRow {
                    ident,
                    declaration,
                    kind: SignatureKind::Value,
                    status: ItemStatus::Ordinary,
                }
            }
            SignatureItem::SigType(id, decl, rec) => {
                let ident = self.binder(*id, index);
                let declaration = self.type_declaration(decl, table, index, ident);
                self.export(table, id.name(), ExportKind::Type, declaration, index);
                SignatureItemRow {
                    ident,
                    declaration,
                    kind: SignatureKind::Type,
                    status: ItemStatus::Recursive(rec_status(*rec)),
                }
            }
            SignatureItem::SigTypext(id, ext, status) => {
                let ident = self.binder(*id, index);
                let declaration = self.extension(ext);
                let payload = declaration | EXTENSION_PAYLOAD;
                self.export(table, id.name(), ExportKind::Constructor, payload, index);
                SignatureItemRow {
                    ident,
                    declaration,
                    kind: SignatureKind::Extension,
                    status: ItemStatus::Extension(match status {
                        ExtStatus::TextFirst => ExtensionStatus::First,
                        ExtStatus::TextNext => ExtensionStatus::Next,
                        ExtStatus::TextException => ExtensionStatus::Exception,
                    }),
                }
            }
            SignatureItem::SigModule(id, decl, rec) => {
                let ident = self.binder(*id, index);
                let module_type = self.defer(&decl.md_type, work);
                let attributes = self.attributes(&decl.md_attributes);
                let loc = self.loc(decl.md_loc);
                let path = self.declared_path(decl.md_path, ident);
                let row = ModuleRow {
                    module_type,
                    attributes,
                    loc,
                    path,
                };
                let declaration = push(&mut self.rows.modules, row);
                self.export(table, id.name(), ExportKind::Module, declaration, index);
                SignatureItemRow {
                    ident,
                    declaration,
                    kind: SignatureKind::Module,
                    status: ItemStatus::Recursive(rec_status(*rec)),
                }
            }
            SignatureItem::SigModtype(id, decl) => {
                let ident = self.binder(*id, index);
                let module_type = match &decl.mtd_type {
                    Some(module_type) => self.defer(module_type, work),
                    None => NONE,
                };
                let attributes = self.attributes(&decl.mtd_attributes);
                let loc = self.loc(decl.mtd_loc);
                let row = ModuleRow {
                    module_type,
                    attributes,
                    loc,
                    path: self.declared_path(None, ident),
                };
                let declaration = push(&mut self.rows.modules, row);
                self.export(table, id.name(), ExportKind::ModuleType, declaration, index);
                SignatureItemRow {
                    ident,
                    declaration,
                    kind: SignatureKind::ModuleType,
                    status: ItemStatus::Ordinary,
                }
            }
            SignatureItem::SigClass => SignatureItemRow {
                ident: NONE,
                declaration: NONE,
                kind: SignatureKind::Class,
                status: ItemStatus::Ordinary,
            },
            SignatureItem::SigClassType => SignatureItemRow {
                ident: NONE,
                declaration: NONE,
                kind: SignatureKind::ClassType,
                status: ItemStatus::Ordinary,
            },
        };
        let len = self.roots.len() as u32 - first;
        if len != 0 {
            self.schemes.push(Range { start: first, len });
        }
        row
    }

    /// Amortized O(1).
    fn export(&mut self, table: u32, name: &'g str, kind: ExportKind, payload: u32, order: u32) {
        let name = self.string(name);
        self.exports.push(Export {
            table,
            name,
            payload,
            order,
            kind,
        });
    }

    /// O(exports · log exports): each signature's table sorted by name and
    /// namespace, the latest of one name and namespace kept.
    fn export_tables(&mut self) -> (Vec<ExportItem>, Vec<ChildTable>) {
        let mut exports = std::mem::take(&mut self.exports);
        exports.sort_unstable_by_key(|export| {
            (
                export.table,
                export.name,
                export.kind as u8,
                std::cmp::Reverse(export.order),
            )
        });
        exports.dedup_by_key(|export| (export.table, export.name, export.kind as u8));
        let mut children = vec![ChildTable::default(); self.rows.signatures.len()];
        let mut items = Vec::with_capacity(exports.len());
        for export in &exports {
            let table = &mut children[export.table as usize];
            if table.len == 0 {
                table.start = items.len() as u32;
            }
            table.len += 1;
            items.push(ExportItem {
                name: export.name,
                payload: export.payload,
                kind: export.kind,
            });
        }
        (items, children)
    }

    /// Amortized O(1): reserve a module type's row and queue it.
    fn defer(&mut self, module_type: &'g ModuleType, work: &mut Vec<Task<'g>>) -> u32 {
        let slot = push(&mut self.rows.module_types, ModuleTypeRow::Ident(NONE));
        work.push(Task::ModuleType(module_type, slot));
        slot
    }

    /// O(1) plus its path; nested signatures and module types are queued.
    fn module_type(
        &mut self,
        module_type: &'g ModuleType,
        slot: u32,
        work: &mut Vec<Task<'g>>,
    ) -> ModuleTypeRow {
        match module_type {
            ModuleType::MtyIdent(path) => ModuleTypeRow::Ident(self.path(*path)),
            ModuleType::MtyAlias(presence, path) => ModuleTypeRow::Alias {
                path: self.path(**path),
                present: *presence == AliasPresence::MtaPresent,
            },
            ModuleType::MtySignature(signature) => {
                let signatures = push(&mut self.rows.signatures, Range::default());
                work.push(Task::Signature(signature, signatures));
                ModuleTypeRow::Signature(signatures)
            }
            ModuleType::MtyFunctor {
                param,
                param_type,
                result,
            } => {
                let parameter = self.binder(*param, FUNCTOR_SCOPE | slot);
                let parameter_type = match param_type {
                    Some(module_type) => self.defer(module_type, work),
                    None => NONE,
                };
                let result = self.defer(result, work);
                ModuleTypeRow::Functor {
                    parameter,
                    parameter_type,
                    result,
                }
            }
        }
    }

    /// Amortized O(1): a root of the current item.
    fn root(&mut self, r: TypeExprRef) -> u32 {
        let ty = offset(self.graph, r);
        push(&mut self.roots, ty)
    }

    /// Amortized O(1) or O(None).
    fn opt_root(&mut self, r: Option<TypeExprRef>) -> u32 {
        match r {
            Some(r) => self.root(r),
            None => NONE,
        }
    }

    /// Amortized O(types): consecutive roots.
    fn root_list(&mut self, types: &[TypeExprRef]) -> Range {
        let start = self.roots.len() as u32;
        for &ty in types {
            self.root(ty);
        }
        tail(self.roots.len(), start)
    }

    /// O(its attributes and primitive).
    fn value(&mut self, decl: &'g ValueDescription, ident: u32) -> u32 {
        let ty = self.root(decl.val_type);
        let primitive = match &decl.val_kind {
            ValueKind::ValReg => NONE,
            ValueKind::ValPrim(primitive) => self.primitive(primitive),
        };
        let row = ValueRow {
            ty,
            primitive,
            attributes: self.attributes(&decl.val_attributes),
            loc: self.loc(decl.val_loc),
            path: self.declared_path(decl.val_path, ident),
        };
        push(&mut self.rows.values, row)
    }

    /// O(the declaration's metadata): the hot and cold rows of a type and
    /// the export entries of its constructors and labels.
    fn type_declaration(
        &mut self,
        decl: &'g TypeDeclaration,
        table: u32,
        order: u32,
        ident: u32,
    ) -> u32 {
        let parameter_roots = self.root_list(&decl.type_params);
        let manifest = self.opt_root(decl.type_manifest);
        let variance_start = self.rows.variance.len() as u32;
        self.rows
            .variance
            .extend(decl.type_variance.iter().map(|variance| variance.bits()));
        let variance = tail(self.rows.variance.len(), variance_start);
        let attributes = self.attributes(&decl.type_attributes);
        let loc = self.loc(decl.type_loc);
        let path = self.declared_path(decl.type_path, ident);
        let members = self.rows.members.len() as u32;
        let (kind, representation) = match &decl.type_kind {
            TypeKind::TypeAbstract => (DeclarationKind::Abstract, NONE),
            TypeKind::TypeOpen => (DeclarationKind::Open, NONE),
            TypeKind::TypeRecord(labels, representation) => {
                for (position, label) in labels.iter().enumerate() {
                    let args = self.label(label);
                    let flags = u32::from(label.ld_mutable == MutableFlag::Mutable)
                        | u32::from(label.ld_optional) << 1;
                    let member = MemberDecl {
                        name: self.string(label.ld_id.name()),
                        args,
                        tag_or_pos: position as u32,
                        flags,
                    };
                    let member = push(&mut self.rows.members, member);
                    self.export(table, label.ld_id.name(), ExportKind::Label, member, order);
                }
                (
                    DeclarationKind::Record,
                    self.record_representation(representation),
                )
            }
            TypeKind::TypeVariant(constructors, layout) => {
                for (position, constructor) in constructors.iter().enumerate() {
                    let args = self.constructor(constructor);
                    let flags = u32::from(constructor.cd_runtime_tag.is_some())
                        | u32::from(constructor.cd_res.is_some()) << 1;
                    let member = MemberDecl {
                        name: self.string(constructor.cd_id.name()),
                        args,
                        tag_or_pos: position as u32,
                        flags,
                    };
                    let member = push(&mut self.rows.members, member);
                    let name = constructor.cd_id.name();
                    self.export(table, name, ExportKind::Constructor, member, order);
                }
                (DeclarationKind::Variant, self.layout(*layout))
            }
        };
        let member_len = self.rows.members.len() as u32 - members;
        let inlined_start = self.rows.inlined_records.len() as u32;
        for inlined in &decl.type_inlined_types {
            let TypeInlinedType::Record { type_name, labels } = inlined;
            let row = InlinedRecordRow {
                name: self.string(type_name),
                labels: self.labels(labels),
            };
            self.rows.inlined_records.push(row);
        }
        let inlined_records = tail(self.rows.inlined_records.len(), inlined_start);
        let shape = self.shape(&decl.type_shape);
        let (newtype_level, scope_level) = match decl.type_newtype_level {
            Some((newtype, scope)) => (newtype as u32, scope as u32),
            None => (NONE, NONE),
        };
        let flags = u8::from(decl.type_private == PrivateFlag::Private)
            | u8::from(decl.type_immediate) << 1
            | u8::from(decl.type_representation == TypeRepresentation::Unboxed) << 2
            | u8::from(decl.type_newtype_level.is_some()) << 3
            | u8::from(decl.type_manifest.is_some()) << 4;
        let hot = TypeDecl {
            kind,
            flags,
            arity: u16::try_from(decl.type_arity).expect("type arity limit"),
            params: parameter_roots.start,
            manifest,
            members,
            member_len,
            path,
            loc,
            variance: variance_start,
        };
        let index = push(&mut self.rows.type_declarations, hot);
        let cold = TypeDetailsRow {
            parameter_roots,
            variance,
            attributes,
            inlined_records,
            representation,
            shape,
            newtype_level,
            scope_level,
        };
        assert_eq!(push(&mut self.rows.type_details, cold), index);
        index
    }

    /// O(labels and their attributes): one contiguous range of label rows.
    fn labels(&mut self, labels: &'g [LabelDeclaration]) -> Range {
        let start = self.rows.labels.len() as u32;
        for label in labels {
            self.label(label);
        }
        tail(self.rows.labels.len(), start)
    }

    /// O(the label's attributes), amortized O(1) otherwise. The ordinary
    /// record caller writes its member/export rows in this same source pass.
    fn label(&mut self, label: &'g LabelDeclaration) -> u32 {
        let row = LabelRow {
            ident: self.ident(label.ld_id, NONE),
            runtime_name: self.opt_string(label.ld_runtime_name.as_deref()),
            ty: self.root(label.ld_type),
            attributes: self.attributes(&label.ld_attributes),
            loc: self.loc(label.ld_loc),
            mutable: label.ld_mutable == MutableFlag::Mutable,
            optional: label.ld_optional,
        };
        push(&mut self.rows.labels, row)
    }

    /// O(the constructor's metadata).
    fn constructor(&mut self, constructor: &'g ConstructorDeclaration) -> u32 {
        let ident = self.ident(constructor.cd_id, NONE);
        let runtime_tag = match &constructor.cd_runtime_tag {
            Some(tag) => self.literal(tag),
            None => NONE,
        };
        let row = ConstructorRow {
            ident,
            runtime_tag,
            arguments: self.constructor_arguments(&constructor.cd_args),
            result: self.opt_root(constructor.cd_res),
            attributes: self.attributes(&constructor.cd_attributes),
            loc: self.loc(constructor.cd_loc),
        };
        push(&mut self.rows.constructors, row)
    }

    /// O(arguments).
    fn constructor_arguments(&mut self, arguments: &'g ConstructorArguments) -> u32 {
        let row = match arguments {
            ConstructorArguments::CstrTuple(types) => {
                ConstructorArgumentsRow::Tuple(self.root_list(types))
            }
            ConstructorArguments::CstrRecord(labels) => {
                ConstructorArgumentsRow::Record(self.labels(labels))
            }
        };
        push(&mut self.rows.constructor_arguments, row)
    }

    /// O(the extension's metadata).
    fn extension(&mut self, ext: &'g ExtensionConstructor) -> u32 {
        let path = self.path(ext.ext_type_path);
        let row = ExtensionRow {
            path,
            parameters: self.root_list(&ext.ext_type_params),
            arguments: self.constructor_arguments(&ext.ext_args),
            result: self.opt_root(ext.ext_ret_type),
            attributes: self.attributes(&ext.ext_attributes),
            loc: self.loc(ext.ext_loc),
            private: ext.ext_private == PrivateFlag::Private,
            exception: ext.ext_is_exception,
        };
        push(&mut self.rows.extensions, row)
    }

    /// O(1).
    fn record_representation(&mut self, representation: &'g RecordRepresentation) -> u32 {
        let row = match representation {
            RecordRepresentation::RecordRegular => RecordRepresentationRow::Regular,
            RecordRepresentation::RecordArray => RecordRepresentationRow::Array,
            RecordRepresentation::RecordUnboxed(b) => RecordRepresentationRow::Unboxed(*b),
            RecordRepresentation::RecordExtension => RecordRepresentationRow::Extension,
            RecordRepresentation::RecordInlined {
                name,
                representation,
            } => RecordRepresentationRow::Inlined {
                name: self.string(name),
                position: u32::try_from(representation.position).expect("constructor position"),
                layout: self.layout(representation.variant),
            },
        };
        push(&mut self.rows.record_representations, row)
    }

    /// O(constructors) the first time, then O(1): a layout row per layout
    /// of the graph, found by its offset in a dense table.
    fn layout(&mut self, layout: LayoutRef) -> u32 {
        let graph = self.graph;
        let offset = if graph.is_detached() {
            layout.0 as usize
        } else {
            assert!(layout.is_shared(), "a published layout is in the pool");
            (layout.shared_index() - graph.base()) as usize
        };
        if self.layout_rows[offset] != NONE {
            return self.layout_rows[offset];
        }
        let source = &graph.layouts()[offset];
        let start = self.rows.runtime_constructors.len() as u32;
        for case in &source.constructors {
            let row = match case {
                ConstructorCase::Constant(tag) => RuntimeConstructorRow::Constant {
                    name: self.string(tag.name.as_str()),
                    literal: self.literal(&tag.literal),
                },
                ConstructorCase::Block(Block::Tagged(TaggedBlock { tag, tag_name })) => {
                    RuntimeConstructorRow::Tagged {
                        name: self.string(tag.name.as_str()),
                        literal: self.literal(&tag.literal),
                        tag_name: self.opt_string(tag_name.as_deref()),
                    }
                }
                ConstructorCase::Block(Block::Untagged { tag, block_type }) => {
                    RuntimeConstructorRow::Untagged {
                        name: self.string(tag.name.as_str()),
                        literal: self.literal(&tag.literal),
                        block_type: self.block_type(block_type),
                    }
                }
            };
            self.rows.runtime_constructors.push(row);
        }
        let row = LayoutRow {
            constructors: tail(self.rows.runtime_constructors.len(), start),
            tag_name: self.opt_string(source.matching_facts.tag_name.as_deref()),
            unboxed: source.unboxed,
        };
        let row = push(&mut self.rows.layouts, row);
        self.layout_rows[offset] = row;
        row
    }

    /// O(1).
    fn literal(&mut self, literal: &'g LiteralTag) -> u32 {
        let row = match literal {
            LiteralTag::String(text) => LiteralRow::String(self.string(text)),
            LiteralTag::Int(value) => LiteralRow::Int(*value),
            LiteralTag::Float(text) => LiteralRow::Float(self.string(text)),
            LiteralTag::BigInt(text) => LiteralRow::BigInt(self.string(text)),
            LiteralTag::Bool(value) => LiteralRow::Bool(*value),
            LiteralTag::Null => LiteralRow::Null,
            LiteralTag::Undefined => LiteralRow::Undefined,
        };
        push(&mut self.rows.literals, row)
    }

    /// O(ancestors).
    fn block_type(&mut self, block_type: &'g BlockType) -> u32 {
        let row = match block_type {
            BlockType::Number => BlockTypeRow::Number,
            BlockType::String => BlockTypeRow::String,
            BlockType::Bigint => BlockTypeRow::Bigint,
            BlockType::Boolean => BlockTypeRow::Boolean,
            BlockType::Instance(Instance::Array(_)) => BlockTypeRow::Array,
            BlockType::Instance(Instance::Class {
                name, ancestors, ..
            }) => BlockTypeRow::Class {
                name: self.string(name),
                ancestors: self.string_list(ancestors),
            },
            BlockType::Symbol => BlockTypeRow::Symbol,
            BlockType::Function => BlockTypeRow::Function,
            BlockType::Object => BlockTypeRow::Object,
            BlockType::Unknown => BlockTypeRow::Unknown,
        };
        push(&mut self.rows.block_types, row)
    }

    /// O(ancestors).
    fn shape(&mut self, shape: &'g ValueShape) -> u32 {
        let row = match shape {
            ValueShape::Unstated => ShapeRow::Unstated,
            ValueShape::NeverUndefined => ShapeRow::NeverUndefined,
            ValueShape::RecognizedAs(shape) => {
                ShapeRow::Recognized(self.block_type(&shape.block_type))
            }
        };
        push(&mut self.rows.shapes, row)
    }

    /// O(attributes and payloads): one contiguous range of attribute rows.
    fn attributes(&mut self, attributes: &'g [Attribute]) -> Range {
        let start = self.rows.attributes.len() as u32;
        for attribute in attributes {
            let row = AttributeRow {
                name: self.string(&attribute.attr_name.txt),
                payload: self.attribute_payload(&attribute.attr_payload),
                name_loc: self.loc(attribute.attr_name.loc),
                loc: self.loc(attribute.attr_loc),
            };
            self.rows.attributes.push(row);
        }
        tail(self.rows.attributes.len(), start)
    }

    /// O(payload size).
    fn attribute_payload(&mut self, payload: &'g AttributePayload) -> u32 {
        let row = match payload {
            AttributePayload::Empty => AttributePayloadRow::Empty,
            AttributePayload::Str(text) => AttributePayloadRow::Str(self.string(text)),
            AttributePayload::Int(value) => AttributePayloadRow::Int(*value),
            AttributePayload::IntLiteral(text) => {
                AttributePayloadRow::IntLiteral(self.string(text))
            }
            AttributePayload::Float(text) => AttributePayloadRow::Float(self.string(text)),
            AttributePayload::BigInt(text) => AttributePayloadRow::BigInt(self.string(text)),
            AttributePayload::Bool(value) => AttributePayloadRow::Bool(*value),
            AttributePayload::Ident(text) => AttributePayloadRow::Ident(self.string(text)),
            AttributePayload::Deprecated {
                reason,
                can_be_automigrated,
                migrate,
                migrate_in_pipe_chain,
            } => {
                let reason = match reason {
                    Ok(None) => SemanticStringValue::Missing,
                    Ok(Some(text)) => SemanticStringValue::Valid(self.string(text)),
                    Err(loc) => SemanticStringValue::Invalid(self.loc(*loc)),
                };
                let row = DeprecatedRow {
                    reason,
                    migrate: self.fragment(migrate.as_ref()),
                    migrate_in_pipe_chain: self.fragment(migrate_in_pipe_chain.as_ref()),
                    can_be_automigrated: *can_be_automigrated,
                };
                AttributePayloadRow::Deprecated(push(&mut self.rows.deprecations, row))
            }
            AttributePayload::Structure(pairs) => {
                AttributePayloadRow::Structure(self.string_pairs(pairs))
            }
            AttributePayload::SemanticString(payload) => {
                let value = match &payload.semantic {
                    Ok(text) => SemanticStringValue::Valid(self.string(text)),
                    Err(loc) => SemanticStringValue::Invalid(self.loc(*loc)),
                };
                let row = SemanticStringRow {
                    value,
                    braces: payload.braces,
                    template: payload.template,
                };
                AttributePayloadRow::SemanticString(push(&mut self.rows.semantic_strings, row))
            }
            AttributePayload::StrTuple(texts) => {
                AttributePayloadRow::StrTuple(self.string_list(texts))
            }
        };
        push(&mut self.rows.attribute_payloads, row)
    }

    /// O(fragment bytes); NONE for none.
    fn fragment(&mut self, fragment: Option<&'g MarshalFragment>) -> u32 {
        let Some(fragment) = fragment else {
            return NONE;
        };
        let start = u32::try_from(self.rows.bytes.len()).expect("segment byte limit");
        self.rows.bytes.extend_from_slice(&fragment.bytes);
        let row = MarshalFragmentRow {
            bytes: tail(self.rows.bytes.len(), start),
            objects: fragment.objects,
            size_32: fragment.size_32,
            size_64: fragment.size_64,
        };
        push(&mut self.rows.marshal_fragments, row)
    }

    /// O(the primitive's FFI description).
    fn primitive(&mut self, primitive: &'g PrimitiveDescription) -> u32 {
        let kind = match &primitive.prim_kind {
            PrimKind::KindIntrinsic => PrimitiveKindRow::Intrinsic,
            PrimKind::KindExternal(external) => PrimitiveKindRow::External(self.ffi(external)),
            PrimKind::KindInlineConst(constant) => {
                PrimitiveKindRow::Inline(self.inline_constant(constant))
            }
        };
        let row = PrimitiveRow {
            name: self.string(&primitive.prim_name),
            arity: primitive.prim_arity,
            kind,
            native_float: primitive.prim_native_float,
            from_constructor: primitive.prim_from_constructor,
        };
        push(&mut self.rows.primitives, row)
    }

    /// O(parameters and their descriptions).
    fn ffi(&mut self, external: &'g ffi::ExternalFfi) -> u32 {
        let start = self.rows.ffi_params.len() as u32;
        let row = match external {
            ffi::ExternalFfi::FfiBs(params, return_wrapper, declaration) => {
                for param in params {
                    let row = FfiParamRow {
                        attribute: self.ffi_attribute(&param.arg_type),
                        label: match param.arg_label {
                            ffi::LabelNoname::ArgLabel => FfiLabelRow::Labelled,
                            ffi::LabelNoname::ArgEmpty => FfiLabelRow::Positional,
                            ffi::LabelNoname::ArgOptional => FfiLabelRow::Optional,
                        },
                    };
                    self.rows.ffi_params.push(row);
                }
                let params = tail(self.rows.ffi_params.len(), start);
                FfiRow::Call {
                    params,
                    declaration: self.external_declaration(declaration),
                    return_wrapper: match return_wrapper {
                        ffi::ReturnWrapper::ReturnUnset => ReturnWrapperRow::Unset,
                        ffi::ReturnWrapper::ReturnIdentity => ReturnWrapperRow::Identity,
                        ffi::ReturnWrapper::ReturnNullToOpt => ReturnWrapperRow::NullToOption,
                        ffi::ReturnWrapper::ReturnNullUndefinedToOpt => {
                            ReturnWrapperRow::NullUndefinedToOption
                        }
                    },
                }
            }
            ffi::ExternalFfi::FfiObjCreate(params) => {
                for param in params {
                    let label = match &param.obj_arg_label {
                        ffi::Label::ObjEmpty => FfiLabelRow::ObjectEmpty,
                        ffi::Label::ObjLabel { name } => {
                            FfiLabelRow::ObjectLabel(self.string(name))
                        }
                        ffi::Label::ObjOptional {
                            name,
                            for_sure_no_nested_option,
                        } => FfiLabelRow::ObjectOptional {
                            name: self.string(name),
                            no_nested_option: *for_sure_no_nested_option,
                        },
                    };
                    let row = FfiParamRow {
                        attribute: self.ffi_attribute(&param.obj_arg_type),
                        label,
                    };
                    self.rows.ffi_params.push(row);
                }
                FfiRow::Object(tail(self.rows.ffi_params.len(), start))
            }
        };
        push(&mut self.rows.ffi, row)
    }

    /// O(the description's pairs).
    fn ffi_attribute(&mut self, attribute: &'g ffi::Attr) -> u32 {
        let row = match attribute {
            ffi::Attr::PolyVarString { descr } => {
                FfiAttributeRow::PolyVarString(self.string_pairs(descr))
            }
            ffi::Attr::PolyVar { descr } => FfiAttributeRow::PolyVar(match descr {
                Some(descr) => {
                    let range = self.string_pairs(descr);
                    push(&mut self.rows.ranges, range)
                }
                None => NONE,
            }),
            ffi::Attr::Int(cases) => {
                let start = self.rows.string_int_pairs.len() as u32;
                for (name, value) in cases {
                    let row = StringIntPair {
                        name: self.string(name),
                        value: *value,
                    };
                    self.rows.string_int_pairs.push(row);
                }
                FfiAttributeRow::Int(tail(self.rows.string_int_pairs.len(), start))
            }
            ffi::Attr::ArgCst(constant) => {
                let row = match constant {
                    ffi::Cst::ArgIntLit(value) => ConstantArgumentRow::Int(*value),
                    ffi::Cst::ArgStringLit(text) => ConstantArgumentRow::String(self.string(text)),
                    ffi::Cst::ArgJsonLit(text) => ConstantArgumentRow::Json(self.string(text)),
                };
                FfiAttributeRow::Constant(push(&mut self.rows.constant_arguments, row))
            }
            ffi::Attr::ExternUnit => FfiAttributeRow::Unit,
            ffi::Attr::Nothing => FfiAttributeRow::Nothing,
            ffi::Attr::Ignore => FfiAttributeRow::Ignore,
            ffi::Attr::Unwrap => FfiAttributeRow::Unwrap,
        };
        push(&mut self.rows.ffi_attributes, row)
    }

    /// O(scopes and import attributes).
    fn external_declaration(&mut self, declaration: &'g ffi::ExternalDecl) -> u32 {
        let kind = match &declaration.kind {
            ffi::DeclKind::DeclVal { name } => ExternalKindRow::Value(self.string(name)),
            ffi::DeclKind::DeclSend { name } => ExternalKindRow::Send(self.string(name)),
            ffi::DeclKind::DeclNew { name } => ExternalKindRow::New(self.string(name)),
            ffi::DeclKind::DeclGet { name } => ExternalKindRow::Get(self.string(name)),
            ffi::DeclKind::DeclSet { name } => ExternalKindRow::Set(self.string(name)),
            ffi::DeclKind::DeclGetIndex => ExternalKindRow::GetIndex,
            ffi::DeclKind::DeclSetIndex => ExternalKindRow::SetIndex,
        };
        let module = match &declaration.module_ {
            None => ModuleSourceRow::Absent,
            Some(ffi::ModuleSource::ModuleItself) => ModuleSourceRow::Itself,
            Some(ffi::ModuleSource::ModuleNamed(module)) => {
                let import_attributes = match &module.import_attributes {
                    Some(pairs) => {
                        let range = self.string_pairs(pairs);
                        push(&mut self.rows.ranges, range)
                    }
                    None => NONE,
                };
                let row = ExternalModuleRow {
                    bundle: self.string(&module.bundle),
                    binding_hint: match &module.module_bind_name {
                        ffi::ModuleBindName::PhintName(name) => self.string(name),
                        ffi::ModuleBindName::PhintNothing => NONE,
                    },
                    import_attributes,
                };
                ModuleSourceRow::Named(push(&mut self.rows.external_modules, row))
            }
        };
        let row = ExternalDeclRow {
            kind,
            module,
            scopes: self.string_list(&declaration.scopes),
            effective_arity: declaration.effective_arity,
            variadic: declaration.variadic,
        };
        push(&mut self.rows.external_declarations, row)
    }

    /// O(1).
    fn inline_constant(&mut self, constant: &'g ffi::InlineConst) -> u32 {
        let row = match constant {
            ffi::InlineConst::ConstString(text) => InlineConstantRow::String(self.string(text)),
            ffi::InlineConst::ConstBool(value) => InlineConstantRow::Bool(*value),
            ffi::InlineConst::ConstInt(value) => InlineConstantRow::Int(*value),
            ffi::InlineConst::ConstBigint { positive, digits } => InlineConstantRow::Bigint {
                positive: *positive,
                digits: self.string(digits),
            },
            ffi::InlineConst::ConstFloat(text) => InlineConstantRow::Float(self.string(text)),
        };
        push(&mut self.rows.inline_constants, row)
    }
}

/// O(1).
fn rec_status(status: OldRecStatus) -> RecStatus {
    match status {
        OldRecStatus::TrecNot => RecStatus::Not,
        OldRecStatus::TrecFirst => RecStatus::First,
        OldRecStatus::TrecNext => RecStatus::Next,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ident::IdentFlags;
    use crate::tc::steps;
    use crate::types::decl_loc::DeclLocTable;
    use crate::types::shared_store::{SharedGraphParts, SharedGraphPayloads};
    use crate::types::type_expr::TypeRefList;

    #[test]
    fn work_item_sizes() {
        assert_eq!(std::mem::size_of::<Task<'static>>(), 16);
        assert_eq!(std::mem::size_of::<LidStep<'static>>(), 16);
        assert_eq!(std::mem::size_of::<Binder>(), 8);
        assert_eq!(std::mem::size_of::<(u32, u32)>(), 8);
        assert_eq!(std::mem::size_of::<Export>(), 20);
    }

    fn value(name: &str, stamp: i32, ty: usize) -> SignatureItem {
        SignatureItem::SigValue(
            Ident::new(name, stamp, IdentFlags::NONE),
            ValueDescription {
                val_type: TypeExprRef::from_usize(ty),
                val_kind: ValueKind::ValReg,
                val_loc: DeclLoc::none(),
                val_attributes: Default::default(),
                val_path: None,
            },
        )
    }

    fn detached(nodes: Vec<(TypeDesc, i32)>, lists: Vec<TypeExprRef>) -> SharedGraph {
        SharedGraph::detached(SharedGraphParts {
            nodes,
            payloads: SharedGraphPayloads {
                lists,
                ..Default::default()
            },
            layouts: Vec::new(),
            locations: DeclLocTable::default(),
            carried: Default::default(),
        })
    }

    fn input<'a>(
        graph: &'a SharedGraph,
        signature: &'a Signature,
        names: &'a RwLock<AHashMap<u32, String>>,
    ) -> Input<'a> {
        Input {
            graph,
            signature,
            unit: "Test",
            deprecated: None,
            names,
            digest: [7; 32],
        }
    }

    #[test]
    fn unused_units_run_neither_converter_and_requests_are_shared_across_workers() {
        use crate::context::IdGenerator;
        use crate::driver::{CheckerChoice, CompilerOptions, compile_source_in_process};
        use std::sync::{Arc, Barrier};
        let options = CompilerOptions {
            nopervasives: true,
            checker: CheckerChoice::Old,
            ..Default::default()
        };
        let registry = crate::cmi::persistent_env::ModuleRegistry::new();
        let compile = |name: &str| {
            compile_source_in_process(
                "let value = 1",
                &format!("{name}.res"),
                name,
                &options,
                &registry,
                false,
                None,
            )
            .expect("unit compiles")
            .pers_struct
            .expect("published unit")
        };
        let used = compile("R2Used");
        let unused = compile("R2Unused");
        let ctx = crate::types::context::TypeContext::new(Arc::new(IdGenerator::new()));
        let world = ctx.world().clone();
        assert_eq!(world.conversion_counts(&used), [0, 0]);
        assert_eq!(world.conversion_counts(&unused), [0, 0]);
        crate::cmi::portable_types::internalize_pers_struct(unused.clone(), &ctx);
        assert_eq!(
            world.conversion_counts(&unused),
            [0, 0],
            "old loading runs no converter"
        );
        let barrier = Arc::new(Barrier::new(8));
        let workers: Vec<_> = (0..8)
            .map(|_| {
                let (world, unit, barrier) = (world.clone(), used.clone(), barrier.clone());
                std::thread::spawn(move || {
                    barrier.wait();
                    let segment = world
                        .converted_segment(&unit, || {
                            Ok(unit
                                .with_shared_graph(|published| {
                                    from_old(Input {
                                        graph: &published.graph,
                                        signature: &published.signature,
                                        unit: &unit.ps_name,
                                        deprecated: unit.ps_deprecated.as_deref(),
                                        names: &published.names,
                                        digest: published_digest(&unit),
                                    })
                                })
                                .expect("a source-built graph"))
                        })
                        .expect("converted segment");
                    let restored =
                        world.converted_old(&unit, || super::super::to_old::to_old(&segment));
                    assert!(Arc::ptr_eq(
                        &segment,
                        &world
                            .converted_segment(&unit, || panic!("from_old is run once"))
                            .unwrap()
                    ));
                    assert!(Arc::ptr_eq(
                        &restored,
                        &world.converted_old(&unit, || panic!("to_old is run once"))
                    ));
                    (segment, restored)
                })
            })
            .collect();
        let results: Vec<_> = workers
            .into_iter()
            .map(|worker| worker.join().unwrap())
            .collect();
        for (segment, restored) in &results {
            assert!(Arc::ptr_eq(segment, &results[0].0));
            assert!(Arc::ptr_eq(restored, &results[0].1));
        }
        check_published(&used).expect("cached conversions match the old text");
        check_published(&used).expect("repeated requests reuse both conversions");
        assert_eq!(world.conversion_counts(&used), [1, 1]);
        assert_eq!(world.conversion_counts(&unused), [0, 0]);
    }

    #[test]
    fn ten_thousand_deep_value_reads_each_old_node_once_on_a_two_mb_stack() {
        std::thread::Builder::new()
            .stack_size(2 * 1024 * 1024)
            .spawn(|| {
                let mut nodes = vec![(TypeDesc::Tvar(None), GENERIC_LEVEL)];
                let mut lists = Vec::new();
                for i in 1..10000 {
                    let list = TypeRefList::from_parts(lists.len() as u32, 1);
                    lists.push(TypeExprRef::from_usize(i - 1));
                    nodes.push((TypeDesc::Ttuple(list), GENERIC_LEVEL));
                }
                let graph = detached(nodes, lists);
                let signature = vec![value("deep", 1, 9999)];
                let names = RwLock::new(AHashMap::default());
                let mut result = None;
                let count = steps::scope(|| result = Some(run(input(&graph, &signature, &names))));
                let (segment, visits) = result.unwrap();
                assert_eq!(visits.count, 10000);
                // 10,000 old reads, then publication: 10,000 captured nodes,
                // 9,999 list slots and two steps for the item.
                assert!(count <= 30001, "{count}");
                assert_eq!(segment.templates.len(), 1);
                assert_eq!(segment.template_nodes.len(), 10000);
                assert!(segment.nodes.is_empty());
                assert_eq!(segment.digest, [7; 32]);
                let root = segment.signature.roots[segment.signature.values[0].ty as usize];
                assert_eq!(
                    root,
                    SchemeRoot {
                        template: 0,
                        ty: Ty(RELATIVE)
                    }
                );
                let mut loaded = segment.graph();
                let instance = loaded.instance(segment.templates[0]);
                assert_eq!(loaded.nodes[instance.0 as usize].tag(), TUPLE);
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn unresolved_longident_components_keep_their_diagnostic_indices() {
        let graph = detached(Vec::new(), Vec::new());
        let names = AHashMap::default();
        let mut convert = Convert::new(&graph, &names);
        let lid = Longident::Ldot(
            Box::new(Longident::Lident(StrIdx::from_raw(7))),
            StrIdx::from_raw(9),
        );
        let last = convert.longident(&lid);
        assert_eq!(convert.rows.longidents[0], LongidentRow::Unresolved(7));
        assert_eq!(convert.rows.longidents[last as usize],
            LongidentRow::UnresolvedDot { parent: 0, raw: 9 });
    }

    #[test]
    fn stamped_names_resolve_to_absolute_binders() {
        let graph = detached(Vec::new(), Vec::new());
        let names = AHashMap::default();
        let mut convert = Convert::new(&graph, &names);
        for stamp in 1..=10000 {
            let bound = convert.binder(
                Ident::new("original", stamp, IdentFlags::NONE),
                stamp as u32,
            );
            let path = convert.declared_path(None, bound);
            assert_eq!(convert.rows.paths[path as usize], PathRow::Ident(bound));
            convert.ident(Ident::new("renamed", stamp, IdentFlags::NONE), NONE);
        }
        convert.resolve_scopes();
        for (index, pair) in convert.rows.identifiers.chunks_exact(2).enumerate() {
            assert_eq!(pair[0].scope, index as u32 + 1);
            assert_eq!(pair[1].scope, pair[0].scope);
        }
    }

    #[test]
    fn ten_thousand_items_share_one_non_generic_node() {
        let graph = detached(vec![(TypeDesc::Tvar(None), 3)], Vec::new());
        let signature: Signature = (0..10000).map(|i| value("weak", i + 1, 0)).collect();
        let names = RwLock::new(AHashMap::default());
        let segment = from_old(input(&graph, &signature, &names));
        assert_eq!(segment.nodes.len(), 1);
        assert_eq!(segment.templates.len(), 10000);
        assert!(segment.signature.roots.iter().all(|root| root.ty == Ty(0)));
        // A later item of the same name hides the earlier ones.
        // Identifier 0 is the unit's own, made first; then the binders.
        let weak = segment
            .lookup(segment.signature.identifiers[1].name)
            .unwrap();
        assert_eq!(weak.kind, ExportKind::Value);
        assert_eq!(weak.payload, 9999);
        assert_eq!(segment.children[0].len, 1);
    }

    #[test]
    fn a_multi_root_item_keeps_its_shared_parameter() {
        // type t<'a> = ('a, 'a): the parameter and both components are one node.
        let graph = detached(
            vec![
                (TypeDesc::Tvar(Some("a".into())), GENERIC_LEVEL),
                (
                    TypeDesc::Ttuple(TypeRefList::from_parts(0, 2)),
                    GENERIC_LEVEL,
                ),
            ],
            vec![TypeExprRef::from_usize(0), TypeExprRef::from_usize(0)],
        );
        let declaration = TypeDeclaration {
            type_params: vec![TypeExprRef::from_usize(0)],
            type_arity: 1,
            type_kind: TypeKind::TypeAbstract,
            type_private: PrivateFlag::Public,
            type_manifest: Some(TypeExprRef::from_usize(1)),
            type_variance: vec![crate::types::Variance::full()],
            type_newtype_level: None,
            type_loc: DeclLoc::none(),
            type_attributes: Vec::new(),
            type_immediate: false,
            type_representation: TypeRepresentation::Boxed,
            type_shape: ValueShape::Unstated,
            type_inlined_types: Vec::new(),
            type_path: None,
        };
        let signature = vec![SignatureItem::SigType(
            Ident::new("t", 1, IdentFlags::NONE),
            std::sync::Arc::new(declaration),
            OldRecStatus::TrecNot,
        )];
        let names = RwLock::new(AHashMap::default());
        let segment = from_old(input(&graph, &signature, &names));
        let decl = segment.type_declarations[0];
        assert_eq!(decl.flags & 16, 16);
        let pools = &segment.signature;
        let parameter = pools.roots[decl.params as usize];
        let manifest = pools.roots[decl.manifest as usize];
        assert_eq!(parameter.template, manifest.template);
        let mut loaded = segment.graph();
        let base = loaded.instance(segment.templates[parameter.template as usize]);
        let at = |root: SchemeRoot| Ty(base.0 + (root.ty.0 & !RELATIVE));
        let tuple = loaded.nodes[at(manifest).0 as usize];
        assert_eq!(tuple.tag(), TUPLE);
        let slots = tuple.b as usize;
        assert_eq!(loaded.lists[slots], at(parameter));
        assert_eq!(loaded.lists[slots + 1], at(parameter));
    }

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

    #[test]
    fn a_compiled_unit_converts_every_kind_of_item() {
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
        check_published(&unit).expect("independent canonical parity");
        unit.with_shared_graph(|published| {
            let segment = from_old(Input {
                graph: &published.graph,
                signature: &published.signature,
                unit: "Sample",
                deprecated: None,
                names: &published.names,
                digest: [0; 32],
            });
            check_sample(&segment, published.signature.len());
        })
        .expect("the sample publishes a frozen graph");
    }

    fn check_sample(segment: &Segment, items: usize) {
        let pools = &segment.signature;
        let text = |index: u32| {
            let range = pools.strings[index as usize];
            std::str::from_utf8(
                &pools.bytes[range.start as usize..(range.start + range.len) as usize],
            )
            .unwrap()
        };
        let find = |wanted: &str| {
            (0..pools.strings.len() as u32)
                .find(|&index| text(index) == wanted)
                .unwrap_or_else(|| panic!("no string {wanted:?}"))
        };
        assert!(
            segment
                .type_declarations
                .iter()
                .all(|decl| decl.path != NONE)
        );
        assert!(pools.values.iter().all(|decl| decl.path != NONE));
        assert!(pools.modules.iter().all(|decl| decl.path != NONE));
        assert_eq!(pools.signatures[0].len as usize, items);
        assert_eq!(text(pools.unit.unwrap().name), "Sample");
        let root = segment.children[0];
        let exported = |name: &str, kind: ExportKind| {
            let name = find(name);
            segment.items[root.start as usize..(root.start + root.len) as usize]
                .iter()
                .find(|item| item.name == name && item.kind == kind)
                .copied()
                .unwrap_or_else(|| panic!("no export {kind:?}"))
        };
        exported("id", ExportKind::Value);
        exported("color", ExportKind::Type);
        exported("Red", ExportKind::Constructor);
        exported("x", ExportKind::Label);
        exported("Inner", ExportKind::Module);
        exported("Showable", ExportKind::ModuleType);
        let failed = exported("Failed", ExportKind::Constructor);
        assert_ne!(failed.payload & EXTENSION_PAYLOAD, 0);
        let extras = &pools.descriptor_extras;
        assert!(extras.iter().any(|d| matches!(d, ExtraDescriptor::Object)));
        assert!(
            extras
                .iter()
                .any(|d| matches!(d, ExtraDescriptor::Field { .. }))
        );
        assert!(extras.iter().any(|d| matches!(d, ExtraDescriptor::Nil)));
        assert!(
            extras
                .iter()
                .any(|d| matches!(d, ExtraDescriptor::Variant(_)))
        );
        assert!(extras.iter().any(|d| matches!(d, ExtraDescriptor::Poly)));
        assert!(
            extras
                .iter()
                .any(|d| matches!(d, ExtraDescriptor::Univar(_)))
        );
        assert!(
            extras
                .iter()
                .any(|d| matches!(d, ExtraDescriptor::Package(_)))
        );
        assert!(
            pools
                .primitives
                .iter()
                .any(|p| matches!(p.kind, PrimitiveKindRow::External(_)))
        );
        assert!(pools.layouts.iter().any(|layout| layout.unboxed));
        assert!(!pools.deprecations.is_empty() || !pools.attributes.is_empty());
        // A functor's parameter and the paths through it share one scope.
        let functor = |row: &&IdentRow| {
            row.scope != NONE && row.scope != UNIT_SCOPE && row.scope & FUNCTOR_SCOPE != 0
        };
        let parameter = pools
            .identifiers
            .iter()
            .find(functor)
            .expect("a functor parameter");
        assert!(
            pools
                .identifiers
                .iter()
                .filter(functor)
                .filter(|row| row.scope == parameter.scope)
                .count()
                >= 2
        );
        // Every template instantiates through R1's kernel.
        let mut graph = segment.graph();
        for template in segment.templates.iter() {
            graph.instance(*template);
        }
        // pair: the first parameter and the first and third components are one node.
        let pair = pools.roots
            [pools.values[exported("pair", ExportKind::Value).payload as usize].ty as usize];
        let base = graph.instance(segment.templates[pair.template as usize]);
        let arrow = graph.nodes[(base.0 + (pair.ty.0 & !RELATIVE)) as usize];
        assert_eq!((arrow.tag(), arrow.arity()), (ARROW, 2));
        let x = graph.params[arrow.b as usize].ty;
        let tuple = graph.nodes[arrow.a as usize];
        assert_eq!((tuple.tag(), tuple.arity()), (TUPLE, 3));
        let slots = tuple.b as usize;
        assert_eq!(graph.lists[slots], x);
        assert_eq!(graph.lists[slots + 2], x);
        assert_ne!(graph.lists[slots + 1], x);
    }
    #[test]
    fn ten_thousand_fields_keep_shared_and_distinct_equal_cells() {
        std::thread::Builder::new()
            .stack_size(2 * 1024 * 1024)
            .spawn(|| {
                use crate::types::type_expr::MutabilityRef;
                let cells = [
                    MutabilityRef::new_persistent(MutableFlag::Immutable),
                    MutabilityRef::new_persistent(MutableFlag::Immutable),
                ];
                let mut nodes = vec![
                    (TypeDesc::Tvar(None), GENERIC_LEVEL),
                    (TypeDesc::Tnil, GENERIC_LEVEL),
                ];
                for i in 0..10000 {
                    nodes.push((
                        TypeDesc::Tfield {
                            name: format!("field{i}").into(),
                            mutability: cells[i % 2],
                            typ: TypeExprRef::from_usize(0),
                            rest: TypeExprRef::from_usize(i + 1),
                        },
                        GENERIC_LEVEL,
                    ));
                }
                nodes.push((
                    TypeDesc::Tobject {
                        fields: TypeExprRef::from_usize(10001),
                    },
                    GENERIC_LEVEL,
                ));
                let graph = detached(nodes, Vec::new());
                let signature = vec![value("object", 1, 10002)];
                let names = RwLock::new(AHashMap::default());
                let mut result = None;
                let count = steps::scope(|| result = Some(run(input(&graph, &signature, &names))));
                let (segment, visits) = result.unwrap();
                assert_eq!(visits.count, 10003);
                assert!(count <= 40009, "{count}");
                assert_eq!(&*segment.signature.mutabilities, &[false, false]);
                let mut previous = [NONE; 2];
                let mut fields = 0;
                for extra in &segment.signature.descriptor_extras {
                    if let ExtraDescriptor::Field { mutability, .. } = extra {
                        let parity = fields % 2;
                        if previous[parity] != NONE {
                            assert_eq!(*mutability, previous[parity]);
                        }
                        previous[parity] = *mutability;
                        fields += 1;
                    }
                }
                assert_eq!(fields, 10000);
                assert_ne!(
                    previous[0], previous[1],
                    "equal cell values do not merge identities"
                );
            })
            .unwrap()
            .join()
            .unwrap();
    }
}
