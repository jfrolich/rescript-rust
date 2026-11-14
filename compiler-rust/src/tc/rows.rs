//! R3 skeleton: the descriptors a 16-byte node does not hold (objects and
//! their fields, polymorphic variant rows, universal variables, polymorphic
//! types, packages) in worker-local pools, and their unification. Built by
//! slices R3e to R3h (CHECKER_REWRITE.md, "R3 as designed").
//!
//! The layout is the published one (tc/segment.rs, `ExtraDescriptor`): an
//! extended node is `TUPLE | EXTENDED`, `a` indexes [`Extras::descriptors`]
//! and the children are the node's list slots. A graph made from a segment
//! starts with the segment's rows copied ([`Extras::from_segment`]), so the
//! indices of frozen nodes stay valid; rows made during a check are appended.

use super::graph::{Graph, LINK, NONE, Node, TUPLE, Ty, VAR};
use super::segment::{
    ExtraDescriptor, PackageRow, Range, RowFieldKind, RowFieldRow, Segment, VariantRow,
};
use super::template::Template;
use super::unify::{Checker, Clash, Frame};

/// Worker-local descriptor pools, cleared between units.
#[derive(Default)]
pub struct Extras {
    pub descriptors: Vec<ExtraDescriptor>,
    pub variants: Vec<VariantRow>,
    pub row_fields: Vec<RowFieldRow>,
    pub packages: Vec<PackageRow>,
    /// The text of every name a field or a tag carries, for the one place
    /// that orders names: `flatten_fields` and `merge_row_fields` sort by
    /// text (compiler/ml/ctype.ml:323, 366). Equality is the index.
    pub names: NameTexts,
    /// Scratch of [`Checker::unify_fields`]: the two flattened field lists,
    /// the left one first. Empty between calls; it keeps its capacity.
    pub fields: Vec<FieldRef>,
    /// Scratch of one copy session ([`Checker::dup_cell`]): the cells that
    /// link to their duplicate until [`Checker::end_cell_session`].
    pub session: Vec<Ty>,
    /// The nodes that hold a reference of a variant field in a slot
    /// ([`Holder`]): lists by `next`, the head in the reference node's `b`.
    /// Rows are appended and never written; a restore leaves the rows it
    /// made unreachable. (R3f)
    pub holders: Vec<Holder>,
    /// Scratch of one [`Checker::unify_row`] call: the two flattened rows,
    /// the left one first, then the types of the field being unified.
    /// Empty between calls; it keeps its capacity. Not `fields`: a row is
    /// unified while the frames of an object are pending. (R3f)
    pub row_scratch: Vec<FieldRef>,
    /// The childless node a normalized holder of a present field names in
    /// its reference slot ([`RES_OWN`]), made at its first use. One per
    /// checker. (R3f)
    pub present_own: Option<Ty>,
}

/// Names as text: one buffer and a span per name index. For a graph made
/// from a segment these are the segment's `bytes` and `strings`.
#[derive(Default)]
pub struct NameTexts {
    pub bytes: Vec<u8>,
    pub spans: Vec<Range>,
}

impl NameTexts {
    /// O(1): the bytes of name `name`.
    #[inline]
    pub fn text(&self, name: u32) -> &[u8] {
        let span = self.spans[name as usize];
        &self.bytes[span.start as usize..(span.start + span.len) as usize]
    }
}

/// A field's mutability cell (`field_mutability ref`, compiler/ml/types.mli:
/// 79-85, 174-180) is a node of the graph that no node has as a child: a
/// `VAR` with no name whose `b` is 1 when mutable, or a link to another
/// cell (`Mutability_link`). `ExtraDescriptor::Field::mutability` is its
/// handle. So a promotion is `Graph::write`, a merge of two classes is
/// `Graph::link`, both logged in the trail inside a speculation and undone
/// by a restore like any node (`set_mutability` logs `Cmutability`,
/// compiler/ml/btype.ml:745-747), and no walk of a type ever meets a cell
/// (CHECKER_REWRITE 8.6, decision 27). O(1).
pub fn cell_node(mutable: bool) -> Node {
    Node {
        head: VAR,
        level: 0,
        a: NONE,
        b: u32::from(mutable),
    }
}

/// The representative of a cell's class (`mutability_ref_repr`,
/// compiler/ml/btype.ml:404-407): O(links), no write. Cell links are not
/// compressed: a class is as long as the merges that made it, and a walk
/// that wrote would have to log.
pub fn cell_repr(g: &Graph, mut cell: Ty) -> Ty {
    loop {
        let node = g.nodes[cell.0 as usize];
        if node.tag() != LINK {
            return cell;
        }
        cell = Ty(node.a);
    }
}

/// O(1): whether the representative `cell` is mutable (`mutability_repr`,
/// compiler/ml/btype.ml:409-412).
pub fn cell_mutable(g: &Graph, cell: Ty) -> bool {
    g.nodes[cell.0 as usize].b != 0
}

/// One field of a flattened object or row, on the walk's stack: 12 bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct FieldRef {
    pub name: u32,
    /// The `Tfield` node, or the row-field index for a variant.
    pub at: u32,
    /// An object's field: its type. A variant's field: the list index of
    /// slot 0 of the node the field is a field of (its *home*), so that a
    /// slot of the field is read with one load also when the home was the
    /// left node of the pair and is a link by now.
    pub ty: Ty,
}

// The reference of a variant field (CHECKER_REWRITE 8.6, decision 34).
//
// `Reither (c, tl, m, e)` (compiler/ml/types.mli:160-169) is spread over
// three places. `c`, `m` and the slots of `tl` are the field's
// `RowFieldRow`, shared by every instance of a scheme and never written.
// `tl` are slots of the variant node. `e` is one more slot of the variant
// node, `RowFieldRow::link`, after the published slots: it names a
// *reference node*, which is what `set_row_field` (btype.ml:742-744)
// writes:
//
// - unresolved (`ref None`): a variable with no name, [`ref_node`]. Its `b`
//   is the head of its [`Holder`] list or `NONE`.
// - resolved: a `TUPLE` node that is not `EXTENDED`, whose `a` is what it
//   was resolved to: [`RES_ABSENT`] (no slot), [`RES_PRESENT`] (no slot:
//   `Rpresent None`; one slot: `Rpresent (Some t)`), or [`RES_EITHER`] with
//   [`RES_CONSTANT`] and [`RES_MATCHED`] (`Reither (c, tl', m, e')`: the
//   slots are `tl'`, then the reference `e'`).
//
// Every write is `Graph::write` of the reference node: logged in the trail
// inside a speculation and undone by its restore, as `set_row_field` logs
// `Crow` (btype.ml:742). A walk of a type reaches the reference as a child
// of the variant node and, through it, the types a resolution added.
//
// A node whose arity is not above `link` is *unopened*: it has no slot for
// the reference yet, which stands for a reference of its own that nothing
// else holds. `Checker::open_row` gives it the slots.

/// `a` of a resolved reference node: `Rabsent`.
pub const RES_ABSENT: u32 = 1;
/// `a` of a resolved reference node: `Rpresent`, with the type in slot 0
/// when the node has one.
pub const RES_PRESENT: u32 = 2;
/// `a` of a resolved reference node: `Reither`, the added types in the
/// slots before the last, the next reference in the last.
pub const RES_EITHER: u32 = 3;
/// The two bits of `a` that hold [`RES_ABSENT`], [`RES_PRESENT`] or
/// [`RES_EITHER`].
pub const RES_KIND: u32 = 3;
/// With [`RES_EITHER`]: `c`, the tag is constant.
pub const RES_CONSTANT: u32 = 4;
/// With [`RES_EITHER`]: `m`, the tag is matched.
pub const RES_MATCHED: u32 = 8;
/// With [`RES_PRESENT`], on `Extras::present_own` only: the field is
/// present with the first of its own types (`Rpresent (Some (List.hd
/// tl))`, compiler/ml/btype.ml:117), and the node adds no child.
pub const RES_OWN: u32 = 16;

/// One node that holds a reference in a slot: 8 bytes. `home` is the
/// variant node, `next` the next holder of the same reference or `NONE`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct Holder {
    pub home: Ty,
    pub next: u32,
}

/// An unresolved reference (`ref None`) at `level`, with `holders` the head
/// of its [`Holder`] list or `NONE`. A variable, so that
/// `generalize_structure` leaves it at the level it leaves the row
/// variable at, and a copy shares it when it shares that variable
/// (`let e = if keep then e else ref None`, compiler/ml/btype.ml:374).
/// O(1).
pub fn ref_node(level: u32, holders: u32) -> Node {
    Node {
        head: VAR,
        level,
        a: NONE,
        b: holders,
    }
}

/// What a field is after its reference is followed (`row_field_repr`,
/// compiler/ml/btype.ml:112-121): 16 bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct FieldRepr {
    /// `Either`: the unresolved reference, or `NONE` for an unopened node.
    /// Otherwise `NONE`.
    pub end: Ty,
    /// `Present`: the type, or `NONE` for a constant tag. `Either`: the
    /// first of its types, or `NONE`.
    pub first: Ty,
    /// `Either`: how many types it has (`tl @ tl'`, btype.ml:114).
    pub types: u32,
    pub kind: RowFieldKind,
}

/// `row_field_repr` (compiler/ml/btype.ml:112-121) of `field`, a field of
/// the variant node whose slots start at list index `b` and whose arity
/// is `arity`. The field's own kind when that is not `Either`; otherwise
/// the chain of references from its slot: each [`RES_EITHER`] adds its
/// types and replaces `c` and `m`, [`RES_PRESENT`] with a type is that type
/// unless the field had one (`Rpresent (Some (List.hd tl))`), [`RES_OWN`]
/// is the field's first own type. O(resolutions of the field), one node
/// load each, no write, no allocation.
pub fn field_repr(g: &Graph, b: u32, arity: u32, field: RowFieldRow) -> FieldRepr {
    let own = field.types;
    let mut first = match own.len {
        0 => Ty(NONE),
        _ => g.lists[(b + own.start) as usize],
    };
    let mut kind = field.kind;
    if !matches!(kind, RowFieldKind::Either { .. }) {
        return FieldRepr { end: Ty(NONE), first, types: own.len, kind };
    }
    let mut types = own.len;
    if field.link >= arity {
        return FieldRepr { end: Ty(NONE), first, types, kind };
    }
    let mut reference = g.lists[(b + field.link) as usize];
    loop {
        let node = g.nodes[reference.0 as usize];
        if node.tag() != TUPLE {
            return FieldRepr { end: reference, first, types, kind };
        }
        match node.a & RES_KIND {
            RES_ABSENT => {
                kind = RowFieldKind::Absent;
                return FieldRepr { end: Ty(NONE), first: Ty(NONE), types: 0, kind };
            }
            RES_PRESENT => {
                let argument = node.arity() == 1 || node.a & RES_OWN != 0;
                if !argument {
                    first = Ty(NONE);
                } else if types == 0 {
                    first = g.lists[node.b as usize];
                }
                kind = RowFieldKind::Present;
                return FieldRepr { end: Ty(NONE), first, types: u32::from(argument), kind };
            }
            _ => {
                let added = node.arity() - 1;
                if types == 0 && added != 0 {
                    first = g.lists[node.b as usize];
                }
                types += added;
                kind = RowFieldKind::Either {
                    constant: node.a & RES_CONSTANT != 0,
                    matched: node.a & RES_MATCHED != 0,
                };
                reference = g.lists[(node.b + added) as usize];
            }
        }
    }
}

/// The types of an `Either` field in OCaml's order (`tl @ tl'`,
/// compiler/ml/btype.ml:114), appended to `out`: the field's own, then
/// those each [`RES_EITHER`] of its chain added. O(types + resolutions),
/// no allocation when `out` has the capacity.
pub fn field_types(g: &Graph, b: u32, arity: u32, field: RowFieldRow, out: &mut Vec<Ty>) {
    let own = field.types;
    out.extend_from_slice(&g.lists[(b + own.start) as usize..(b + own.start + own.len) as usize]);
    if field.link >= arity {
        return;
    }
    let mut reference = g.lists[(b + field.link) as usize];
    loop {
        let node = g.nodes[reference.0 as usize];
        if node.tag() != TUPLE || node.a & RES_KIND != RES_EITHER {
            return;
        }
        let added = node.arity() - 1;
        out.extend_from_slice(&g.lists[node.b as usize..(node.b + added) as usize]);
        reference = g.lists[(node.b + added) as usize];
    }
}

/// How many slots a published node of `row` has: its field types, its
/// `more` and the arguments of its name (tc/bridge/from_old.rs, `variant`).
/// The reference of its k-th `Either` field is slot `published_slots + k`.
/// O(fields).
pub fn published_slots(row: VariantRow, fields: &[RowFieldRow]) -> u32 {
    let mut slots = (row.more + 1).max(row.name_arguments.start + row.name_arguments.len);
    for field in &fields[row.fields.start as usize..(row.fields.start + row.fields.len) as usize] {
        slots = slots.max(field.types.start + field.types.len);
    }
    slots
}

impl Extras {
    /// O(rows of the segment): one bulk copy per pool, one cell node
    /// pushed on `g` per cell of the segment ([`cell_node`]; a frozen cell
    /// holds its value and links to nothing), and one pass over the
    /// descriptors that turns each field's cell index into that node's
    /// handle, and one pass over the variant rows that gives each `Either`
    /// field the slot of its reference ([`published_slots`]). The indices
    /// of a segment's rows are the indices here, so the
    /// nodes of an instance name their descriptors without translation.
    /// `g` is the graph made from the same segment (`Segment::graph`).
    pub fn from_segment(segment: &Segment, g: &mut Graph) -> Extras {
        let pools = &segment.signature;
        let first = g.nodes.len() as u32;
        g.nodes.extend(pools.mutabilities.iter().map(|&mutable| cell_node(mutable)));
        let mut descriptors = pools.descriptor_extras.to_vec();
        for descriptor in &mut descriptors {
            if let ExtraDescriptor::Field { mutability, .. } = descriptor {
                *mutability += first;
            }
        }
        // A published `Either` field has no reference (`link` is `NONE`,
        // tc/segment.rs): here it gets the slot its reference will have
        // once a node of the row is opened, after the published slots.
        let mut row_fields = pools.row_fields.to_vec();
        for &row in pools.variants.iter() {
            let mut slot = published_slots(row, &row_fields);
            let fields = row.fields;
            for field in &mut row_fields[fields.start as usize..(fields.start + fields.len) as usize] {
                if matches!(field.kind, RowFieldKind::Either { .. }) {
                    field.link = slot;
                    slot += 1;
                }
            }
        }
        Extras {
            descriptors,
            variants: pools.variants.to_vec(),
            row_fields,
            packages: pools.packages.to_vec(),
            names: NameTexts {
                bytes: pools.bytes.to_vec(),
                spans: pools.strings.to_vec(),
            },
            fields: Vec::new(),
            session: Vec::new(),
            holders: Vec::new(),
            row_scratch: Vec::new(),
            present_own: None,
        }
    }
}

/// Whether an instance of `template` duplicates a mutability cell: the
/// template has a field whose rest is a variable of the template itself
/// (a reference with bit 30 to a `VAR` node of `nodes`), which is the last
/// field of a row that ends in a generic variable
/// (`row_terminator_generic`, compiler/ml/btype.ml:478-506). `nodes` and
/// `lists` are the template pools the template indexes
/// (`Segment::template_nodes`, `template_lists`). O(nodes of the template),
/// one list load per field, no allocation. The caller of an instance keeps
/// the answer in its own row (a `TypeInfo` flag for a manifest; the
/// harness per value) and calls [`Checker::instance_open`] or
/// [`Checker::instance`] by it. (R3e)
#[allow(unused_variables)]
pub fn template_has_open_row(
    nodes: &[Node],
    lists: &[Ty],
    descriptors: &[ExtraDescriptor],
    template: Template,
) -> bool {
    todo!("R3e")
}

impl Checker {
    /// `flatten_fields` (compiler/ml/ctype.ml:314-323): append the fields of
    /// the list that starts at `fields` (a field node, or what ends a list)
    /// to `out`, following `repr` at every rest, then sort the appended
    /// part by name text (`List.sort (fun f f' -> compare f.f_name
    /// f'.f_name)`; `NameTexts::text`, bytes compared as OCaml compares
    /// strings), and return the representative that is not a field (a
    /// variable, `Tnil`, a constructor). A row has no two fields of one
    /// name (typetexp.ml:596-607 collapses them, `build_fields` adds only
    /// names the row lacks), so `sort_unstable_by` gives OCaml's order and
    /// allocates nothing. O(fields) loads, one step a field, and
    /// O(fields log fields) name comparisons. (R3e)
    pub fn flatten_fields(&mut self, fields: Ty, out: &mut Vec<FieldRef>) -> Ty {
        todo!("R3e")
    }

    /// `unify_fields env ty1 ty2` (compiler/ml/ctype.ml:2467-2518) for two
    /// field lists (the slot 0 of two objects, or two field nodes). It
    /// links nothing itself and never fails itself: it makes nodes and
    /// pushes frames, in this order of work:
    ///
    /// 1. Flatten both lists into `extras.fields` (left first), keeping the
    ///    two rests; `l1`, `l2` are the levels of `repr(left)`,
    ///    `repr(right)`; `open1`, `open2` whether each rest is a variable,
    ///    read now (ctype.ml:2476).
    /// 2. In `Mode::Explain` push a [`FrameKind::Fields`] frame: `left`,
    ///    `right` the two rests, `extra` the index in `saved` of their two
    ///    descriptors (`rest1.desc <- d1; rest2.desc <- d2`,
    ///    ctype.ml:2513-2517).
    /// 3. `va` = [`Checker::make_rowvar`] at `min(l1, l2)` with `use1` =
    ///    the right list lacks nothing, `use2` = the left lacks nothing.
    /// 4. One merge of the two sorted lists from their last names to their
    ///    first (`associate_fields`, ctype.ml:330-342): a field only on the
    ///    left goes on top of the list being built at `l1` from `va`
    ///    ([`Checker::build_field`]), a field only on the right on the one
    ///    built at `l2`, and a name on both sides pushes a
    ///    [`FrameKind::Field`] frame (`left`, `right` the two field nodes,
    ///    `extra` bit 0 `open1`, bit 1 `open2`). Walking backwards builds
    ///    each list in name order (`List.fold_right`, ctype.ml:325-328) and
    ///    leaves the common fields to be popped in name order.
    /// 5. Push the pair `(rest1, built at l2)`, then the pair `(built at
    ///    l1, rest2)`, so that the second is popped first: `unify env
    ///    (build_fields l1 miss1 va) rest2; unify env rest1 (build_fields l2
    ///    miss2 va)` (ctype.ml:2485-2486), then the common fields.
    ///
    /// Cost: the two flattenings, one step per merge step, one node and
    /// two list slots per field a side lacks, one 16-byte frame per common
    /// field, two pair frames; no descriptor row is made or written
    /// (CHECKER_REWRITE 8.6, decision 27). `extras.fields` is cleared
    /// before it returns. (R3e)
    pub fn unify_fields(&mut self, left: Ty, right: Ty) -> Result<(), Clash> {
        todo!("R3e")
    }

    /// `make_rowvar level use1 rest1 use2 rest2` (compiler/ml/ctype.ml:
    /// 2445-2465): the variable both built lists end in. `rest1` when
    /// `use1`, else `rest2` when `use2`, else a new variable at `level`
    /// carrying the name below. The name: of two named variables, `rest1`'s
    /// when `rest1.level <= rest2.level`, else `rest2`'s; when only `rest1`
    /// is a named variable, its name, and `rest2` takes it when `use2` and
    /// `rest2` is a variable with no name (`set_name`: `Graph::write`,
    /// logged in a speculation); when only `rest2` is a named variable, its
    /// name (the `set_name rest2 name` of that arm changes nothing: `rest2`
    /// already has it). O(1). (R3e)
    pub fn make_rowvar(&mut self, level: u32, use1: bool, rest1: Ty, use2: bool, rest2: Ty) -> Ty {
        todo!("R3e")
    }

    /// One field of `build_fields` (compiler/ml/ctype.ml:325-328): a new
    /// field node at `level` with the name and the cell of field node
    /// `source` (the same descriptor index: the descriptor is not copied
    /// and not written), the type `source` has (its slot 0) and `rest`.
    /// One node, two list slots. (R3e)
    pub fn build_field(&mut self, level: u32, source: Ty, rest: Ty) -> Ty {
        todo!("R3e")
    }

    /// The pop of a [`FrameKind::Field`] frame: one common field
    /// (compiler/ml/ctype.ml:2487-2511). [`Checker::unify_mutability`] of
    /// the two field nodes with the frame's `open1`, `open2`; its clash has
    /// no pair (`Err([NONE, NONE])`: `raise (Unify [])` outside the `try`).
    /// Then, in `Mode::Explain`, a [`FrameKind::FieldEnd`] frame with the
    /// two field nodes, which stays below whatever the types push; then
    /// the two types (slot 0 of each node), as `run_frames` treats a pair:
    /// their representatives, nothing when they are one node, else
    /// [`Checker::unify_pair`], whose clash is `Err([left, right])`.
    /// O(1) plus the callee. (R3e)
    pub fn unify_field(&mut self, frame: Frame) -> Result<(), [Ty; 2]> {
        todo!("R3e")
    }

    /// `unify_mutability ~open1 ~open2 f1 f2` (compiler/ml/ctype.ml:
    /// 2520-2539) for two field nodes. `r1`, `r2` the representatives of
    /// their cells ([`cell_repr`]); nothing when they are one cell.
    /// Otherwise by the two values: equal, nothing; `r1` immutable and
    /// `r2` mutable, `r1` becomes mutable when `open1`, else a clash;
    /// `r1` mutable and `r2` immutable, `r2` becomes mutable when `open2`,
    /// else a clash (`Graph::write` of the cell node with `b = 1`). Then
    /// `r2` is linked to `r1` (`Graph::link`: `set_mutability r2
    /// (Mutability_link r1)`). Both writes are logged in a speculation and
    /// undone by its restore. No descriptor row is written. O(class
    /// links). (R3e)
    pub fn unify_mutability(&mut self, open1: bool, open2: bool, f1: Ty, f2: Ty) -> Result<(), Clash> {
        todo!("R3e")
    }

    /// The trace pair of a common field whose types clashed
    /// (compiler/ml/ctype.ml:2493-2510): for each of the two field nodes a
    /// new field node at the current level with its name and cell (the
    /// same descriptor index), its type, and a new `Tnil` node as rest
    /// (one `Nil` descriptor row appended per call). Failure path of
    /// `Mode::Explain` only: four nodes, four list slots. (R3e)
    pub fn field_trace_pair(&mut self, f1: Ty, f2: Ty) -> [Ty; 2] {
        todo!("R3e")
    }

    /// An instance of a template that has an open row
    /// ([`template_has_open_row`]): `Graph::instance`, then the pass of
    /// [`Checker::link_memorized`] over the new nodes with `cells`, which
    /// duplicates the cell of every field whose row ends in a variable of
    /// the instance. The caller knows the template is one; for any other
    /// template [`Checker::instance`] is the same instance and costs
    /// nothing for cells. O(template) plus one step per new node. (R3e)
    pub fn instance_open(&mut self, template: Template) -> Ty {
        todo!("R3e")
    }

    /// One field node of a copy session (an instance or a copy; `first` is
    /// the first node the session made): `copy_type_desc` for `Tfield`
    /// (compiler/ml/btype.ml:516-532). When the field's row ends in a
    /// variable the session made (handle >= `first`: the copy of a generic
    /// variable; `row_terminator_generic`, btype.ml:478-506), the field
    /// gets a new descriptor row with its name and the duplicate of its
    /// cell's class (`dup_mutability`, btype.ml:462-472): the class's
    /// representative when the session made it already (a cell handle >=
    /// the session's first cell), otherwise a new cell node with the same
    /// value, to which the source representative is linked until
    /// [`Checker::end_cell_session`] (pushed on `extras.session`; the
    /// temporary link is a plain store, not logged). Otherwise the field
    /// keeps its descriptor, and so shares the cell.
    ///
    /// The terminator of a row is found once per session: `marks` holds,
    /// for each field node of the row, one of two generations of this
    /// session (ends in a session variable, or not); a walk from a field
    /// stops at the first marked node and then marks the nodes it passed.
    /// At most two steps a field over the whole session, one descriptor
    /// row (12 bytes) per duplicated field, one node per duplicated class.
    /// (R3e)
    pub fn dup_cell(&mut self, field: Ty, node: Node, first: u32) {
        todo!("R3e")
    }

    /// End a copy session: every cell of `extras.session` gets its
    /// descriptor back (a cell node with the value its duplicate has: no
    /// promotion happens inside a session), and the list is emptied
    /// (`end_type_copy_session`, compiler/ml/btype.ml:449-456). O(classes
    /// duplicated). (R3e)
    pub fn end_cell_session(&mut self) {
        todo!("R3e")
    }

    /// `unify_row` (compiler/ml/ctype.ml:2541-2641): merge the two rows'
    /// fields (`merge_row_fields`, ctype.ml:380), decide closedness and the
    /// row name, link the two `more` variables to a fresh row, then
    /// [`Checker::unify_row_field`] for each common tag. O(tags log tags)
    /// plus the fields. (R3f)
    pub fn unify_row(&mut self, left: Ty, right: Ty) -> Result<(), Clash> {
        todo!("R3f")
    }

    /// `unify_row_field` (compiler/ml/ctype.ml:2643-2730): one common tag of
    /// two rows. O(types of the two fields). (R3f)
    pub fn unify_row_field(
        &mut self,
        fixed_left: bool,
        fixed_right: bool,
        more: Ty,
        left: u32,
        right: u32,
    ) -> Result<(), Clash> {
        todo!("R3f")
    }

    /// `unify_univar` (compiler/ml/ctype.ml:1544-1561): two universal
    /// variables are equal only when the innermost scope that binds either
    /// pairs them. O(scopes × bound variables). (R3g)
    pub fn unify_univar(&mut self, left: Ty, right: Ty) -> Result<(), Clash> {
        todo!("R3g")
    }

    /// `enter_poly` (compiler/ml/ctype.ml:1656-1686): pair the bound
    /// variables of two polymorphic types for the unification of their
    /// bodies, and check afterwards that none escaped
    /// (`univars_escape`, ctype.ml:1626). Pushes the body pair and a
    /// `LeavePoly` frame. O(bound variables) plus the escape walk. (R3g)
    pub fn enter_poly(&mut self, left: Ty, right: Ty) -> Result<(), Clash> {
        todo!("R3g")
    }

    /// `occur_univar` (compiler/ml/ctype.ml:1563-1624): no universal
    /// variable of `ty` is free of its binder. O(nodes), marks, explicit
    /// stack; O(1) when the unit has made no universal variable. (R3g)
    pub fn occur_univar(&mut self, ty: Ty) -> Result<(), Clash> {
        todo!("R3g")
    }

    /// `unify_package` (compiler/ml/ctype.ml:2172-2203): two packages of
    /// one module type path unify their type arguments by name. O(arguments
    /// log arguments). (R3g)
    pub fn unify_package(&mut self, left: Ty, right: Ty) -> Result<(), Clash> {
        todo!("R3g")
    }

    /// `reify` (compiler/ml/ctype.ml:1813-1870): replace the variables of a
    /// type by fresh abstract types at the newtype level, in pattern mode.
    /// O(nodes), marks. (R3h)
    pub fn reify(&mut self, ty: Ty) {
        todo!("R3h")
    }

    /// `add_gadt_equation` (compiler/ml/ctype.ml:2093-2100): give the
    /// locally abstract type `source` the manifest `destination` when the
    /// equation is well-founded, and clean the memos. O(nodes of
    /// `destination`). (R3h)
    pub fn add_gadt_equation(&mut self, source: u32, destination: Ty) {
        todo!("R3h")
    }

    /// `mcomp` (compiler/ml/ctype.ml:1905-2090): whether two types can have
    /// a common instance; never links. O(pairs), pair set, explicit stack.
    /// (R3h)
    pub fn mcomp(&mut self, left: Ty, right: Ty) -> Result<(), Clash> {
        todo!("R3h")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sizes() {
        assert_eq!(std::mem::size_of::<FieldRef>(), 12);
        assert_eq!(std::mem::size_of::<Holder>(), 8);
        assert_eq!(std::mem::size_of::<FieldRepr>(), 16);
    }

    /// O(1): push a node.
    fn push(g: &mut Graph, head: u32, a: u32, slots: &[Ty]) -> Ty {
        let b = g.lists.len() as u32;
        g.lists.extend_from_slice(slots);
        g.push(Node { head: head | (slots.len() as u32) << 8, level: 1, a, b })
    }

    /// `row_field_repr` on hand-built chains (compiler/ml/btype.ml:112-121):
    /// an unopened field and an unresolved reference are `Reither` with the
    /// field's own types; `Reither` in a reference adds its types after
    /// them and replaces `c` and `m` (`Reither (_, tl', _, {contents = Some
    /// fi}) -> row_field_repr_aux (tl @ tl') fi`); `Rpresent (Some _)` at
    /// the end is the first type met on the way (`Rpresent (Some (List.hd
    /// tl))`) or its own; `Rpresent None` and `Rabsent` are themselves.
    #[test]
    fn a_field_is_read_through_its_references() {
        let mut g = Graph::default();
        let either = |constant, matched| RowFieldKind::Either { constant, matched };
        let [t0, t1, t2, t3] = [0u32, 1, 2, 3].map(|serial| {
            g.push(Node { head: VAR, level: 1, a: NONE, b: serial })
        });
        let end = g.push(ref_node(1, NONE));
        // The home: slots [t0, t1 | more | reference].
        let field = RowFieldRow {
            name: 0,
            types: Range { start: 0, len: 2 },
            link: 3,
            kind: either(false, false),
        };
        let home = |g: &mut Graph, reference: Ty| {
            let node = push(g, TUPLE, 0, &[t0, t1, t2, reference]);
            g.nodes[node.0 as usize]
        };
        let read = |g: &Graph, node: Node, arity: u32| {
            let repr = field_repr(g, node.b, arity, field);
            let mut types = Vec::new();
            field_types(g, node.b, arity, field, &mut types);
            (repr, types)
        };
        // Unopened: the node has three slots.
        let node = home(&mut g, end);
        let (repr, types) = read(&g, node, 3);
        assert_eq!(repr, FieldRepr { end: Ty(NONE), first: t0, types: 2, kind: either(false, false) });
        assert_eq!(types, [t0, t1]);
        // Unresolved.
        let (repr, types) = read(&g, node, 4);
        assert_eq!(repr, FieldRepr { end, first: t0, types: 2, kind: either(false, false) });
        assert_eq!(types, [t0, t1]);
        // `Reither (true, [t3], true, end)` in the reference.
        let added = push(&mut g, TUPLE, RES_EITHER | RES_CONSTANT | RES_MATCHED, &[t3, end]);
        let node = home(&mut g, added);
        let (repr, types) = read(&g, node, 4);
        assert_eq!(repr, FieldRepr { end, first: t0, types: 3, kind: either(true, true) });
        assert_eq!(types, [t0, t1, t3]);
        // Then `Rpresent (Some t2)` at the end: the first type met.
        let present = push(&mut g, TUPLE, RES_PRESENT, &[t2]);
        let added = push(&mut g, TUPLE, RES_EITHER, &[t3, present]);
        let node = home(&mut g, added);
        let (repr, _) = read(&g, node, 4);
        assert_eq!(repr, FieldRepr { end: Ty(NONE), first: t0, types: 1, kind: RowFieldKind::Present });
        // A field with no type of its own takes the reference's.
        let constant = RowFieldRow { types: Range { start: 0, len: 0 }, ..field };
        let repr = field_repr(&g, node.b, 4, constant);
        assert_eq!(repr.first, t3);
        let node = home(&mut g, present);
        assert_eq!(field_repr(&g, node.b, 4, constant).first, t2);
        // `Rpresent None`, the normalized holder, `Rabsent`.
        let none = push(&mut g, TUPLE, RES_PRESENT, &[]);
        let node = home(&mut g, none);
        let repr = field_repr(&g, node.b, 4, constant);
        assert_eq!(repr, FieldRepr { end: Ty(NONE), first: Ty(NONE), types: 0, kind: RowFieldKind::Present });
        let own = push(&mut g, TUPLE, RES_PRESENT | RES_OWN, &[]);
        let node = home(&mut g, own);
        let (repr, _) = read(&g, node, 4);
        assert_eq!(repr, FieldRepr { end: Ty(NONE), first: t0, types: 1, kind: RowFieldKind::Present });
        let absent = push(&mut g, TUPLE, RES_ABSENT, &[]);
        let node = home(&mut g, absent);
        let (repr, _) = read(&g, node, 4);
        assert_eq!(repr, FieldRepr { end: Ty(NONE), first: Ty(NONE), types: 0, kind: RowFieldKind::Absent });
        // A field that is not `Reither` has no reference.
        let present = RowFieldRow { kind: RowFieldKind::Present, link: NONE, types: Range { start: 0, len: 1 }, ..field };
        assert_eq!(field_repr(&g, node.b, 4, present).first, t0);
    }

    /// A chain of 10,000 resolutions is read in one pass, with no write:
    /// the steps are the loads, counted here by the length.
    #[test]
    fn a_chain_of_ten_thousand_resolutions_is_read_once() {
        let mut g = Graph::default();
        let end = g.push(ref_node(1, NONE));
        let ty = g.push(Node { head: VAR, level: 1, a: NONE, b: 0 });
        let mut reference = end;
        for _ in 0..10_000 {
            reference = push(&mut g, TUPLE, RES_EITHER, &[ty, reference]);
        }
        let field = RowFieldRow {
            name: 0,
            types: Range { start: 0, len: 0 },
            link: 0,
            kind: RowFieldKind::Either { constant: false, matched: false },
        };
        let home = push(&mut g, TUPLE, 0, &[reference]);
        let node = g.nodes[home.0 as usize];
        let before = g.nodes.clone();
        let repr = field_repr(&g, node.b, 1, field);
        assert_eq!((repr.end, repr.types, repr.first), (end, 10_000, ty));
        let mut types = Vec::new();
        field_types(&g, node.b, 1, field, &mut types);
        assert_eq!(types.len(), 10_000);
        assert_eq!(g.nodes, before);
    }

    /// The reference of the k-th `Either` field of a published row is the
    /// slot after the published ones.
    #[test]
    fn the_reference_slots_follow_the_published_slots() {
        let either = RowFieldKind::Either { constant: false, matched: false };
        let fields = [
            RowFieldRow { name: 0, types: Range { start: 0, len: 2 }, link: NONE, kind: either },
            RowFieldRow { name: 1, types: Range { start: 2, len: 0 }, link: NONE, kind: RowFieldKind::Present },
            RowFieldRow { name: 2, types: Range { start: 2, len: 1 }, link: NONE, kind: either },
        ];
        let row = VariantRow {
            fields: Range { start: 0, len: 3 },
            more: 3,
            name: 7,
            name_arguments: Range { start: 4, len: 2 },
            closed: true,
            fixed: false,
        };
        assert_eq!(published_slots(row, &fields), 6);
        let unnamed = VariantRow { name: NONE, name_arguments: Range::default(), ..row };
        assert_eq!(published_slots(unnamed, &fields), 4);
    }
}
