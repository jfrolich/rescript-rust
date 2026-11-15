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

use std::cmp::Ordering;

use super::graph::{CONSTR, Graph, LINK, Mode, NONE, Node, TUPLE, Ty, VAR};
use super::segment::{
    EXTENDED, ExtraDescriptor, PackageRow, Range, RowFieldKind, RowFieldRow, Segment, VariantRow,
};
use super::template::Template;
use super::unify::{Checker, Clash, Frame, FrameKind};

/// Bit 31 of [`FieldRef::name`] in [`Checker::unify_fields`]'s scratch:
/// the name is on both sides. Name indices stay below it.
const COMMON: u32 = 1 << 31;

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
    /// The nodes that hold types on the way to an unresolved reference
    /// ([`Holder`]): lists by `next`, the head in the reference node's `b`.
    /// Rows are appended and never written; a restore leaves the rows it
    /// made unreachable. (R3f)
    pub holders: Vec<Holder>,
    /// Scratch of one [`Checker::unify_row`] call: the two flattened rows,
    /// the left one first, then the types of the field being unified.
    /// Empty between calls; it keeps its capacity. Not `fields`: a row is
    /// unified while the frames of an object are pending. (R3f)
    pub row_scratch: Vec<FieldRef>,
    /// Set by [`Checker::copy`] around its pass over the nodes it made:
    /// `g.work` holds the node each was copied from
    /// ([`Checker::copy_refs`]). (R3n)
    pub copying: bool,
    /// `passive_variants` and `rigid_variants`
    /// (compiler/ml/ctype.ml:2184-2190), read by
    /// [`Checker::unify_row_field`]; both false in unification proper.
    pub passive_variants: bool,
    pub rigid_variants: bool,
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
// A field `Reither (c, tl, m, e)` (compiler/ml/types.mli:160-169) of a
// published row is its `RowFieldRow` (`c`, `m`, the slots of `tl`), shared
// by every instance of a scheme and never written, and no `e`: a node of
// such a row is *unopened*, and each of its `Reither` fields stands for a
// reference of its own that nothing else holds. `RowFieldRow::link` is the
// slot the reference will have, after the published slots.
//
// `Checker::open_row` gives a node those slots. From then on what the slot
// names is the field: a chain of *reference nodes*, read by [`field_repr`].
//
// - An unresolved reference (`ref None`) is a variable with no name,
//   [`ref_node`]; its `b` is the head of its [`Holder`] list or `NONE`.
// - A resolved one is a `TUPLE` node that is not `EXTENDED` (a tuple's `a`
//   is 0, a reference's is not): `a` says what `set_row_field`
//   (btype.ml:742-744) put there. [`RES_ABSENT`]: no slot. [`RES_PRESENT`]:
//   no slot (`Rpresent None`) or one, the type. [`RES_EITHER`] with
//   [`RES_CONSTANT`] and [`RES_MATCHED`] (`Reither (c, tl', m, e')`): the
//   slots are `tl'`, then the reference `e'`.
// - The field's own `tl` is the first link of the chain: opening a node
//   makes, for a field that has types, a [`RES_EITHER`] node with the row's
//   `c` and `m`, those types, and a new unresolved reference; a field
//   without types gets the unresolved reference itself. The published type
//   slots of an opened node's `Reither` fields name that first node, so a
//   type of such a field is a child of the variant node through the chain
//   only, and one write of a chain node takes it away.
//
// Every write is `Graph::write` of a reference node: logged in the trail
// inside a speculation and undone by its restore, as `set_row_field` logs
// `Crow`. A walk of a type reaches the chain as children of the variant
// node: one node more per `Reither` field without types and two per field
// with types, for an opened node; nothing for an unopened one.

/// `a` of a resolved reference node: `Rabsent`.
pub const RES_ABSENT: u32 = 1;
/// `a` of a resolved reference node: `Rpresent`, with the type in slot 0
/// when the node has one.
pub const RES_PRESENT: u32 = 2;
/// `a` of a resolved reference node: `Reither`, the types in the slots
/// before the last, the next reference in the last.
pub const RES_EITHER: u32 = 3;
/// The two bits of `a` that hold [`RES_ABSENT`], [`RES_PRESENT`] or
/// [`RES_EITHER`].
pub const RES_KIND: u32 = 3;
/// With [`RES_EITHER`]: `c`, the tag is constant.
pub const RES_CONSTANT: u32 = 4;
/// With [`RES_EITHER`]: `m`, the tag is matched.
pub const RES_MATCHED: u32 = 8;

/// One [`RES_EITHER`] node that has types and whose chain ends in the
/// unresolved reference this list belongs to: 8 bytes. `node` is that
/// node, `next` the next holder of the same reference or `NONE`. When the
/// reference is resolved to something that is not `Reither`, each holder
/// is rewritten so that it stops being a parent of the types `iter_row`
/// (compiler/ml/btype.ml:229-236) no longer visits
/// ([`Checker::resolve`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct Holder {
    pub node: Ty,
    pub next: u32,
}

/// In the `b` of a [`FrameKind::RowField`] record: row 1 is fixed.
pub const ROW_FIXED1: u32 = 1;
/// In the `b` of a [`FrameKind::RowField`] record: row 2 is fixed.
pub const ROW_FIXED2: u32 = 2;
/// In the `b` of a record: the types of two `Reither` fields were unified
/// first; [`Checker::row_field_end`] decides whether the pair is unified
/// again (`redo`, compiler/ml/ctype.ml:2663-2675).
pub const ROW_AGAIN: u32 = 4;
/// In the `b` of a record: a reference was resolved to a present field
/// and its holders are settled once the types are unified.
pub const ROW_SETTLE: u32 = 8;

/// O(1): the `a` of a [`RES_EITHER`] node with `c` and `m`.
#[inline]
pub fn either_flags(constant: bool, matched: bool) -> u32 {
    RES_EITHER | if constant { RES_CONSTANT } else { 0 } | if matched { RES_MATCHED } else { 0 }
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
/// is `arity`. The field's own kind and type when the kind is not
/// `Either`. For an unopened node (`arity <= field.link`), `Either` with
/// the types in the field's own slots. Otherwise the chain from the
/// field's reference slot: each [`RES_EITHER`] adds its types and gives
/// `c` and `m`, [`RES_PRESENT`] with a type is the first type met on the
/// way or else its own (`Rpresent (Some (List.hd tl))`), [`RES_PRESENT`]
/// without one is `Rpresent None`, [`RES_ABSENT`] is `Rabsent`. O(chain),
/// one node load each, no write, no allocation.
pub fn field_repr(g: &Graph, b: u32, arity: u32, field: RowFieldRow) -> FieldRepr {
    let own = field.types;
    let mut kind = field.kind;
    if !matches!(kind, RowFieldKind::Either { .. }) || field.link >= arity {
        let first = match own.len {
            0 => Ty(NONE),
            _ => g.lists[(b + own.start) as usize],
        };
        return FieldRepr { end: Ty(NONE), first, types: own.len, kind };
    }
    let (mut first, mut types) = (Ty(NONE), 0);
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
                let argument = node.arity() == 1;
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
/// compiler/ml/btype.ml:114), appended to `out`: the field's own slots
/// for an unopened node, otherwise those of each [`RES_EITHER`] of its
/// chain. O(types + chain), no allocation when `out` has the capacity.
pub fn field_types(g: &Graph, b: u32, arity: u32, field: RowFieldRow, out: &mut Vec<Ty>) {
    if field.link >= arity {
        let own = field.types;
        out.extend_from_slice(&g.lists[(b + own.start) as usize..(b + own.start + own.len) as usize]);
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
            copying: false,
            passive_variants: false,
            rigid_variants: false,
        }
    }
}

/// Whether an instance of `template` duplicates a mutability cell: the
/// template has a field whose rest is a variable of the template itself
/// (a reference with bit 30 to a `VAR` node of `nodes`), which is the last
/// field of a row that ends in a generic variable
/// (`row_terminator_generic`, compiler/ml/btype.ml:478-506). `nodes` is
/// the pool the template indexes (`Segment::template_nodes`); `lists` is
/// the template's own slots (`template::slots`), which the `b` of its
/// nodes counts from. O(nodes of the template),
/// one list load per field, no allocation. The caller of an instance keeps
/// the answer in its own row (a `TypeInfo` flag for a manifest; the
/// harness per value) and calls [`Checker::instance_open`] or
/// [`Checker::instance`] by it. (R3e)
pub fn template_has_open_row(
    nodes: &[Node],
    lists: &[Ty],
    descriptors: &[ExtraDescriptor],
    template: Template,
) -> bool {
    let nodes = &nodes[template.nodes as usize..(template.nodes + template.node_len) as usize];
    nodes.iter().any(|&node| {
        #[cfg(test)]
        super::steps::tick();
        ends_open_row(nodes, lists, descriptors, node)
    })
}

/// O(1): whether stored node `node` of a template is a field whose rest
/// is a variable of the template (a reference with bit 30 to a `VAR` node).
/// `nodes` are the template's own nodes, `lists` its own slots
/// (`template::slots`). One descriptor load, and one list load for a field.
pub(super) fn ends_open_row(
    nodes: &[Node],
    lists: &[Ty],
    descriptors: &[ExtraDescriptor],
    node: Node,
) -> bool {
    const RELATIVE: u32 = 1 << 30;
    if node.head & EXTENDED == 0
        || !matches!(descriptors[node.a as usize], ExtraDescriptor::Field { .. })
    {
        return false;
    }
    let rest = lists[node.b as usize + 1];
    rest.0 != NONE && rest.0 & RELATIVE != 0 && nodes[(rest.0 & !RELATIVE) as usize].tag() == VAR
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
        let start = out.len();
        let mut at = self.g.repr(fields);
        loop {
            let node = self.g.nodes[at.0 as usize];
            let ExtraDescriptor::Field { name, .. } = self.field_descriptor(node) else {
                break;
            };
            #[cfg(test)]
            super::steps::tick();
            out.push(FieldRef {
                name,
                at: at.0,
                ty: self.g.lists[node.b as usize],
            });
            at = self.g.repr(self.g.lists[node.b as usize + 1]);
        }
        let names = &self.extras.names;
        out[start..].sort_unstable_by(|f, g| names.text(f.name).cmp(names.text(g.name)));
        at
    }

    /// O(1): the descriptor row of an extended node, or `Nil` for a node
    /// that is not extended (what ends a list either way).
    #[inline]
    fn field_descriptor(&self, node: Node) -> ExtraDescriptor {
        if node.head & EXTENDED != 0 {
            self.extras.descriptors[node.a as usize]
        } else {
            ExtraDescriptor::Nil
        }
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
    /// 2. In `Mode::Explain` push a [`FrameKind::Fields`] frame below the
    ///    frames of steps 4 and 5: `left`, `right` the two rests, `extra`
    ///    the index in `saved` of their two descriptors as they are AFTER
    ///    step 3: `let d1 = rest1.desc and d2 = rest2.desc` (ctype.ml:2482)
    ///    follows `make_rowvar`, whose `set_name` may have named the right
    ///    rest, and that named descriptor is the one a failure puts back
    ///    (`rest1.desc <- d1; rest2.desc <- d2`, ctype.ml:2513-2517).
    /// 3. `va` = [`Checker::make_rowvar`] at `min(l1, l2)` with `use1` =
    ///    the left list lacks nothing of the right (`miss2 = []`), `use2` =
    ///    the right lacks nothing of the left (`miss1 = []`),
    ///    ctype.ml:2477-2481.
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
        // 1. Flatten, left first; the scratch is taken so that
        //    `flatten_fields` can read the names (it keeps its capacity).
        let mut fields = std::mem::take(&mut self.extras.fields);
        debug_assert!(fields.is_empty());
        let rest1 = self.flatten_fields(left, &mut fields);
        let n1 = fields.len();
        let rest2 = self.flatten_fields(right, &mut fields);
        let (left, right) = (self.g.repr(left), self.g.repr(right));
        let l1 = self.g.nodes[left.0 as usize].level;
        let l2 = self.g.nodes[right.0 as usize].level;
        let open1 = self.g.nodes[rest1.0 as usize].tag() == VAR;
        let open2 = self.g.nodes[rest2.0 as usize].tag() == VAR;
        // 2. The `Fields` frame goes below everything else; its two saved
        //    descriptors are filled after step 3.
        let saved = self.saved.len();
        if self.g.mode == Mode::Explain {
            let extra = saved as u32;
            self.saved.push(self.g.nodes[rest1.0 as usize]);
            self.saved.push(self.g.nodes[rest2.0 as usize]);
            self.frames.push(Frame {
                left: rest1,
                right: rest2,
                kind: FrameKind::Fields,
                extra,
            });
        }
        // `associate_fields` (ctype.ml:330-342), from the last names to the
        // first. Its first half decides which names are common, pushing
        // the `Field` frames (last name first, so they are popped in name
        // order) and marking both sides with `COMMON`: `make_rowvar` needs
        // to know whether a side lacks anything before a field is built.
        let open = u32::from(open1) | u32::from(open2) << 1;
        let (mut i, mut j) = (n1, fields.len());
        let mut common = 0;
        while i > 0 && j > n1 {
            #[cfg(test)]
            super::steps::tick();
            let (f1, f2) = (fields[i - 1], fields[j - 1]);
            // Two indices may spell one name (8.6, decision 32): differing
            // indices compare their texts once.
            let order = if f1.name == f2.name {
                Ordering::Equal
            } else {
                let names = &self.extras.names;
                names.text(f1.name).cmp(names.text(f2.name))
            };
            if order == Ordering::Equal {
                fields[i - 1].name |= COMMON;
                fields[j - 1].name |= COMMON;
                self.frames.push(Frame {
                    left: Ty(f1.at),
                    right: Ty(f2.at),
                    kind: FrameKind::Field,
                    extra: open,
                });
                common += 1;
                i -= 1;
                j -= 1;
            } else if order == Ordering::Greater {
                i -= 1;
            } else {
                j -= 1;
            }
        }
        // 3. `make_rowvar (min l1 l2) (miss2 = []) rest1 (miss1 = []) rest2`.
        let miss1 = n1 - common;
        let miss2 = fields.len() - n1 - common;
        let va = self.make_rowvar(l1.min(l2), miss2 == 0, rest1, miss1 == 0, rest2);
        // `let d1 = rest1.desc and d2 = rest2.desc` (ctype.ml:2482), after
        // `make_rowvar` may have named the right rest.
        if self.g.mode == Mode::Explain {
            self.saved[saved] = self.g.nodes[rest1.0 as usize];
            self.saved[saved + 1] = self.g.nodes[rest2.0 as usize];
        }
        // 4. The second half: `build_fields l1 miss1 va` and `build_fields
        //    l2 miss2 va`, each list built from its last field.
        let mut built = [va, va];
        for (at, field) in fields.iter().enumerate().rev() {
            if field.name & COMMON == 0 {
                let (side, level) = if at < n1 { (0, l1) } else { (1, l2) };
                built[side] = self.build_field(level, Ty(field.at), built[side]);
            }
        }
        fields.clear();
        self.extras.fields = fields;
        // 5. Popped first: `unify (build_fields l1 miss1 va) rest2`, then
        //    `unify rest1 (build_fields l2 miss2 va)` (ctype.ml:2485-2486).
        self.frames.push(Frame {
            left: rest1,
            right: built[1],
            kind: FrameKind::Pair,
            extra: 0,
        });
        self.frames.push(Frame {
            left: built[0],
            right: rest2,
            kind: FrameKind::Pair,
            extra: 0,
        });
        Ok(())
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
        let n1 = self.g.nodes[rest1.0 as usize];
        let n2 = self.g.nodes[rest2.0 as usize];
        let named = |node: Node| node.tag() == VAR && node.a != NONE;
        let name = match (named(n1), named(n2)) {
            (true, true) if n1.level <= n2.level => n1.a,
            (true, true) => n2.a,
            (true, false) => {
                // `if use2 then set_name rest2 name`: `Tvar None` only.
                if use2 && n2.tag() == VAR {
                    self.g.write(rest2, Node { a: n1.a, ..n2 });
                }
                n1.a
            }
            (false, true) => n2.a,
            (false, false) => NONE,
        };
        if use1 {
            rest1
        } else if use2 {
            rest2
        } else {
            self.g.push(Node {
                head: VAR,
                level,
                a: name,
                b: 0,
            })
        }
    }

    /// One field of `build_fields` (compiler/ml/ctype.ml:325-328): a new
    /// field node at `level` with the name and the cell of field node
    /// `source` (the same descriptor index: the descriptor is not copied
    /// and not written), the type `source` has (its slot 0) and `rest`.
    /// One node, two list slots. (R3e)
    pub fn build_field(&mut self, level: u32, source: Ty, rest: Ty) -> Ty {
        #[cfg(test)]
        super::steps::tick();
        let node = self.g.nodes[source.0 as usize];
        let b = self.g.lists.len() as u32;
        let ty = self.g.lists[node.b as usize];
        self.g.lists.extend_from_slice(&[ty, rest]);
        self.g.push(Node { level, b, ..node })
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
    /// O(1) plus the callee. (R3e) Out of line: the loop of `run_frames`
    /// pays for this arm only when it is popped.
    #[inline(never)]
    pub fn unify_field(&mut self, frame: Frame) -> Result<(), [Ty; 2]> {
        let (f1, f2) = (frame.left, frame.right);
        let (open1, open2) = (frame.extra & 1 != 0, frame.extra & 2 != 0);
        if self.unify_mutability(open1, open2, f1, f2).is_err() {
            return Err([Ty(NONE), Ty(NONE)]);
        }
        if self.g.mode == Mode::Explain {
            self.frames.push(Frame {
                kind: FrameKind::FieldEnd,
                ..frame
            });
        }
        // The pair of the two types goes on the stack and `run_frames` pops
        // it next: the representatives, nothing when they are one node,
        // else `unify_pair`, whose one call site stays in `run_frames`.
        let (n1, n2) = (self.g.nodes[f1.0 as usize], self.g.nodes[f2.0 as usize]);
        self.frames.push(Frame {
            left: self.g.lists[n1.b as usize],
            right: self.g.lists[n2.b as usize],
            kind: FrameKind::Pair,
            extra: 0,
        });
        Ok(())
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
        let r1 = cell_repr(&self.g, self.cell_of(f1));
        let r2 = cell_repr(&self.g, self.cell_of(f2));
        if r1 == r2 {
            return Ok(());
        }
        match (cell_mutable(&self.g, r1), cell_mutable(&self.g, r2)) {
            (false, true) if open1 => self.promote(r1),
            (true, false) if open2 => self.promote(r2),
            (false, true) | (true, false) => return Err(Clash),
            _ => {}
        }
        self.g.link(r2, r1);
        Ok(())
    }

    /// O(1): `set_mutability r (Mutability_value Mutable)`, logged in a
    /// speculation like any node write.
    fn promote(&mut self, cell: Ty) {
        let node = self.g.nodes[cell.0 as usize];
        self.g.write(cell, Node { b: 1, ..node });
    }

    /// O(1): the cell of field node `field`.
    #[inline]
    fn cell_of(&self, field: Ty) -> Ty {
        let node = self.g.nodes[field.0 as usize];
        match self.extras.descriptors[node.a as usize] {
            ExtraDescriptor::Field { mutability, .. } => Ty(mutability),
            _ => unreachable!("a field node"),
        }
    }

    /// The trace pair of a common field whose types clashed
    /// (compiler/ml/ctype.ml:2493-2510): for each of the two field nodes a
    /// new field node at the current level with its name and cell (the
    /// same descriptor index), its type, and a new `Tnil` node as rest
    /// (one `Nil` descriptor row appended per call). Failure path of
    /// `Mode::Explain` only: four nodes, four list slots. (R3e)
    pub fn field_trace_pair(&mut self, f1: Ty, f2: Ty) -> [Ty; 2] {
        let level = self.g.level;
        let nil = self.extras.descriptors.len() as u32;
        self.extras.descriptors.push(ExtraDescriptor::Nil);
        [f1, f2].map(|field| {
            let rest = self.g.push(Node {
                head: TUPLE | EXTENDED,
                level,
                a: nil,
                b: self.g.lists.len() as u32,
            });
            self.build_field(level, field, rest)
        })
    }

    /// An instance of a template that has an open row
    /// ([`template_has_open_row`]): `Graph::instance`, then the pass of
    /// [`Checker::link_memorized`] over the new nodes with `cells`, which
    /// duplicates the cell of every field whose row ends in a variable of
    /// the instance. The caller knows the template is one; for any other
    /// template [`Checker::instance`] is the same instance and costs
    /// nothing for cells. O(template) plus one step per new node. (R3e)
    pub fn instance_open(&mut self, template: Template) -> Ty {
        let first = self.g.nodes.len();
        let root = self.g.instance(template);
        self.link_memorized(first, NONE, true);
        root
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
        let rest = self.g.lists[node.b as usize + 1];
        if !self.ends_in_session(rest, first) {
            return;
        }
        let ExtraDescriptor::Field { name, mutability } = self.extras.descriptors[node.a as usize]
        else {
            unreachable!("a field node");
        };
        let source = cell_repr(&self.g, Ty(mutability));
        // A cell at or above `first` was made by this session: no instance
        // or copy makes a cell, which is no node's child.
        let duplicate = if source.0 >= first {
            source
        } else {
            let cell = self.g.nodes[source.0 as usize];
            let duplicate = self.g.push(cell);
            self.g.nodes[source.0 as usize] = super::expand::link_node(cell, duplicate);
            self.extras.session.push(source);
            duplicate
        };
        let a = self.extras.descriptors.len() as u32;
        self.extras.descriptors.push(ExtraDescriptor::Field {
            name,
            mutability: duplicate.0,
        });
        // The field node is the session's own: no trail entry.
        self.g.nodes[field.0 as usize] = Node { a, ..node };
    }

    /// `row_terminator_generic rest` (compiler/ml/btype.ml:478-506) for a
    /// copy session whose nodes start at `first`: whether the row from
    /// `rest` ends in a variable the session made. The two latest mark
    /// generations are the session's (`link_memorized` takes them): the
    /// newest marks a field node of a row that does, the one before a field
    /// node of a row that does not. A first walk stops at the first marked
    /// node or at the end, a second marks the field nodes the first passed.
    /// One step per node passed or marked, so at most two per field node
    /// over the whole session; links are followed without compression.
    fn ends_in_session(&mut self, rest: Ty, first: u32) -> bool {
        let (yes, no) = (self.mark_generation, self.mark_generation - 1);
        let mut at = rest;
        let answer = loop {
            at = cell_repr(&self.g, at);
            let mark = self.marks.get(at.0 as usize).copied().unwrap_or(0);
            if mark == yes || mark == no {
                break mark == yes;
            }
            #[cfg(test)]
            super::steps::tick();
            let node = self.g.nodes[at.0 as usize];
            match self.field_descriptor(node) {
                ExtraDescriptor::Field { .. } => at = self.g.lists[node.b as usize + 1],
                _ => break node.tag() == VAR && at.0 >= first,
            }
        };
        let generation = if answer { yes } else { no };
        let mut at = rest;
        loop {
            at = cell_repr(&self.g, at);
            let node = self.g.nodes[at.0 as usize];
            let mark = self.marks.get(at.0 as usize).copied();
            let unmarked = mark.is_some_and(|mark| mark != yes && mark != no);
            if !unmarked || !matches!(self.field_descriptor(node), ExtraDescriptor::Field { .. }) {
                return answer;
            }
            #[cfg(test)]
            super::steps::tick();
            self.marks[at.0 as usize] = generation;
            at = self.g.lists[node.b as usize + 1];
        }
    }

    /// O(1) amortized: two consecutive fresh mark generations for a copy
    /// session ([`Checker::ends_in_session`] reads them as the two latest).
    pub(super) fn begin_cell_session(&mut self) {
        let older = self.fresh_marks();
        if self.fresh_marks() != older + 1 {
            // The counter wrapped and the marks were cleared: start again
            // above the cleared value.
            self.fresh_marks();
        }
    }

    /// End a copy session: every cell of `extras.session` gets its
    /// descriptor back (a cell node with the value its duplicate has: no
    /// promotion happens inside a session), and the list is emptied
    /// (`end_type_copy_session`, compiler/ml/btype.ml:449-456). O(classes
    /// duplicated). (R3e)
    pub fn end_cell_session(&mut self) {
        while let Some(source) = self.extras.session.pop() {
            let duplicate = Ty(self.g.nodes[source.0 as usize].a);
            let mutable = cell_mutable(&self.g, duplicate);
            self.g.nodes[source.0 as usize] = cell_node(mutable);
        }
    }

    /// Give variant node `ty` the slots of its references and return the
    /// node as it then is; any other node, an opened variant node and a
    /// variant node without a `Reither` field are returned as they are
    /// (one descriptor load, one row load).
    ///
    /// Opening: a new list of `published_slots + k` slots (`k` the row's
    /// `Reither` fields). The published slots are copied; then, for each
    /// `Reither` field in row order, a new unresolved reference
    /// ([`ref_node`]) at the node's level, and
    /// - when the field has no type, that reference goes in the field's
    ///   reference slot;
    /// - when it has types, a new [`RES_EITHER`] node at the node's level
    ///   with the row's `c` and `m`, a new list of those types and the
    ///   reference, goes in the reference slot *and in each of the
    ///   field's type slots*; one [`Holder`] row names it and the
    ///   reference's `b` is that row.
    ///
    /// Then `Graph::write` of `ty` with the new list and arity (logged in
    /// a speculation; the descriptor index is unchanged and no row is made
    /// or written). Per `Reither` field: one node and one slot, or two
    /// nodes, `types + 2` slots and 8 bytes of holder. O(slots of the
    /// node), one step a field of the row.
    ///
    /// An unopened node's references are held by nothing else, so opening
    /// changes no type (`field_repr` reads the same field before and
    /// after); it is done before the node is unified, copied with its row
    /// variable shared, or listed as a rest. (R3f)
    pub fn open_row(&mut self, ty: Ty) -> Node {
        let node = self.g.nodes[ty.0 as usize];
        if node.head & EXTENDED == 0 {
            return node;
        }
        let ExtraDescriptor::Variant(row) = self.extras.descriptors[node.a as usize] else {
            return node;
        };
        let fields = self.extras.variants[row as usize].fields;
        let fields = fields.start as usize..(fields.start + fields.len) as usize;
        // The k-th reference slot is `published_slots + k` (`from_segment`):
        // the first `Reither` field's slot is the count of published slots,
        // the last one's is one below the opened arity, and a node is
        // opened exactly when its arity covers the first.
        let either = |field: &&RowFieldRow| matches!(field.kind, RowFieldKind::Either { .. });
        let row_fields = &self.extras.row_fields[fields.clone()];
        let Some(published) = row_fields.iter().find(either).map(|field| field.link) else {
            return node;
        };
        if published < node.arity() {
            return node;
        }
        let arity = row_fields.iter().rev().find(either).map_or(published, |field| field.link + 1);
        // The new list: the published slots, then one slot per reference.
        let b = self.g.lists.len() as u32;
        self.g
            .lists
            .extend_from_within(node.b as usize..(node.b + published) as usize);
        self.g.lists.resize((b + arity) as usize, Ty(NONE));
        for index in fields {
            #[cfg(test)]
            super::steps::tick();
            let field = self.extras.row_fields[index];
            let RowFieldKind::Either { constant, matched } = field.kind else {
                continue;
            };
            let types = field.types;
            let first = if types.len == 0 {
                self.g.push(ref_node(node.level, NONE))
            } else {
                // `Reither (c, tl, m, e)` as a chain node of this node's
                // own: the types, then `e`, of which it is the one holder.
                let holder = self.extras.holders.len() as u32;
                let reference = self.g.push(ref_node(node.level, holder));
                let start = self.g.lists.len() as u32;
                let own = (b + types.start) as usize..(b + types.start + types.len) as usize;
                self.g.lists.extend_from_within(own.clone());
                self.g.lists.push(reference);
                let chain = self.g.push(Node {
                    head: TUPLE | (types.len + 1) << 8,
                    level: node.level,
                    a: either_flags(constant, matched),
                    b: start,
                });
                self.extras.holders.push(Holder { node: chain, next: NONE });
                self.g.lists[own].fill(chain);
                chain
            };
            self.g.lists[(b + field.link) as usize] = first;
        }
        let opened = Node {
            head: (node.head & 0xff) | arity << 8,
            b,
            ..node
        };
        self.g.write(ty, opened);
        opened
    }

    /// `row_repr` (compiler/ml/btype.ml:126-135) of the row of `top`, a
    /// variant node's descriptor: append one [`FieldRef`] per field to
    /// `extras.row_scratch`, the fields of `top` first, then those of each
    /// variant node its `more` leads to (`row.row_more`'s representative is
    /// a variant: `f :: ll`, outermost first), with `name` the tag, `at`
    /// the row-field index and `ty` the list index of the home's slot 0.
    /// Each chain node is opened first ([`Checker::open_row`]; `top` is
    /// opened by the caller). Returns the last variant node met (whose
    /// flags and name are the row's, btype.ml:134) as its handle, or
    /// `NONE` when that is `top` itself, and the representative of its
    /// `more`. O(fields + chain), one step a field, no allocation once the
    /// scratch has the capacity. (R3f)
    pub fn flatten_row(&mut self, top: Node) -> (Ty, Ty) {
        let (mut last, mut node) = (Ty(NONE), top);
        loop {
            let ExtraDescriptor::Variant(row) = self.extras.descriptors[node.a as usize] else {
                unreachable!("a variant node");
            };
            let row = self.extras.variants[row as usize];
            for at in row.fields.start..row.fields.start + row.fields.len {
                #[cfg(test)]
                super::steps::tick();
                let name = self.extras.row_fields[at as usize].name;
                self.extras.row_scratch.push(FieldRef { name, at, ty: Ty(node.b) });
            }
            let more = self.g.repr(self.g.lists[(node.b + row.more) as usize]);
            let next = self.g.nodes[more.0 as usize];
            let variant = next.head & EXTENDED != 0
                && matches!(self.extras.descriptors[next.a as usize], ExtraDescriptor::Variant(_));
            if !variant {
                return (last, more);
            }
            last = more;
            node = self.open_row(more);
        }
    }

    /// `merge_row_fields` (compiler/ml/ctype.ml:380-386) of the two rows
    /// in `extras.row_scratch[first..]`, `left` fields then the right
    /// ones. Returns how many pairs there are; afterwards the scratch
    /// holds, from `first`: `r1` (the fields only the left row has), `r2`,
    /// then for each pair its left and its right field, the pairs in the
    /// order `List.iter` meets them.
    ///
    /// - No pair, both lists as they were, when a list is empty, or when
    ///   one list has one field whose tag the other lacks (`[p1], _ when
    ///   not (List.mem_assoc (fst p1) fi2)`, then the same for the right;
    ///   one scan of the other list).
    /// - Otherwise both lists are sorted by tag text (`sort_row_fields`;
    ///   `NameTexts::text`, bytes compared as OCaml compares strings; a
    ///   row has no two fields of one tag, so `sort_unstable_by` gives
    ///   `List.sort`'s order) and merged: `r1` and `r2` ascending, and the
    ///   pairs **descending**: `merge_rf` conses each pair on the list it
    ///   returns (`(l1, f1, f2) :: pairs`, ctype.ml:374), so the last tag
    ///   merged is the first unified.
    ///
    /// Tags are one tag when their name indices are equal; when the
    /// indices differ the two texts are compared once (one `cmp` with three
    /// outcomes; `Equal` is a common tag; 8.6, decision 39). O(n log n) name
    /// comparisons and one step per merge step; the merge writes into the
    /// scratch above the two lists and moves the result down: no
    /// allocation. (R3f)
    pub fn merge_rows(&mut self, first: usize, left: usize) -> usize {
        let scratch = &mut self.extras.row_scratch;
        let names = &self.extras.names;
        let order = |f: &FieldRef, g: &FieldRef| {
            if f.name == g.name {
                Ordering::Equal
            } else {
                names.text(f.name).cmp(names.text(g.name))
            }
        };
        let middle = first + left;
        let end = scratch.len();
        let right = end - middle;
        // `[], _ | _, [] -> (fi1, fi2, [])`, and a single tag the other
        // list lacks (`List.mem_assoc`).
        let lacks = |one: &FieldRef, other: &[FieldRef]| {
            other.iter().all(|f| order(one, f) != Ordering::Equal)
        };
        if left == 0
            || right == 0
            || (left == 1 && lacks(&scratch[first], &scratch[middle..end]))
            || (right == 1 && lacks(&scratch[middle], &scratch[first..middle]))
        {
            return 0;
        }
        scratch[first..middle].sort_unstable_by(order);
        scratch[middle..end].sort_unstable_by(order);
        // `merge_rf` into a region above the lists: `r1` ascending from its
        // start, `r2` ascending from `left` on, and the k-th pair met at
        // `left - 1 - k` (its left field) and `left + right - 1 - k` (its
        // right one): `r1` and the pairs fill at most `left` slots, `r2`
        // and the pairs at most `right`.
        scratch.resize(end + left + right, FieldRef { name: 0, at: 0, ty: Ty(NONE) });
        let (mut i, mut j) = (first, middle);
        let (mut r1, mut r2, mut pairs) = (0, 0, 0);
        while i < middle || j < end {
            #[cfg(test)]
            super::steps::tick();
            let step = if i == middle {
                Ordering::Greater
            } else if j == end {
                Ordering::Less
            } else {
                order(&scratch[i], &scratch[j])
            };
            match step {
                Ordering::Equal => {
                    scratch[end + left - 1 - pairs] = scratch[i];
                    scratch[end + left + right - 1 - pairs] = scratch[j];
                    pairs += 1;
                    i += 1;
                    j += 1;
                }
                Ordering::Less => {
                    scratch[end + r1] = scratch[i];
                    r1 += 1;
                    i += 1;
                }
                Ordering::Greater => {
                    scratch[end + left + r2] = scratch[j];
                    r2 += 1;
                    j += 1;
                }
            }
        }
        // Down: `r1`, `r2`, then the pairs, the last met first. Every
        // destination is below `end`, where the region starts.
        scratch.copy_within(end..end + r1, first);
        scratch.copy_within(end + left..end + left + r2, first + r1);
        let at = first + r1 + r2;
        for k in 0..pairs {
            scratch[at + 2 * k] = scratch[end + left - pairs + k];
            scratch[at + 2 * k + 1] = scratch[end + left + right - pairs + k];
        }
        scratch.truncate(at + 2 * pairs);
        pairs
    }

    /// `unify_row env row1 row2` (compiler/ml/ctype.ml:2541-2641), for the
    /// two variant nodes of a pair that `unify3` has opened and linked:
    /// `t1x` is a link to the right node by now, `left` and `right` are
    /// the two opened descriptors. Like [`Checker::push_children`] it
    /// pushes nothing when it fails. In this order:
    ///
    /// 1. [`Checker::flatten_row`] of `left`, then of `right`, into
    ///    `extras.row_scratch` from its current length (the scratch is
    ///    truncated back to that length before the function returns, on
    ///    every path). `rm1`, `rm2` are the two representatives it returns;
    ///    `row1`, `row2` the `VariantRow`s of the two last nodes.
    /// 2. `if unify_eq rm1 rm2 then ()`: one node, nothing is done.
    /// 3. [`Checker::merge_rows`].
    /// 4. `fixed1`, `fixed2` ([`Checker::row_is_fixed`]). `more` is `rm1`
    ///    when `fixed1`, else `rm2` when `fixed2`, else a new variable with
    ///    no name at the lower of the two levels (ctype.ml:2548-2552).
    ///    `closed = row1.closed || row2.closed`.
    /// 5. The empty type (ctype.ml:2564-2573): when `closed && (empty r1
    ///    || row2.closed) && (empty r2 || row1.closed)` and every pair has
    ///    an absent side, a clash whose pair is two new empty closed rows
    ///    ([`Checker::trace_row`] twice with no field). `empty` is "every
    ///    field is `Rabsent`" ([`field_repr`]).
    /// 6. The name (ctype.ml:2574-2586): `row1`'s when it has one, `row1`
    ///    is closed or `r2` is empty, and `row2` is open or (`keep` and
    ///    `r1` is empty); else `row2`'s by the mirrored test; else none.
    ///    `keep` for row 1 is "in every pair the left field is absent or
    ///    the right one is not", mirrored for row 2.
    /// 7. In `Mode::Explain` a [`FrameKind::Fields`] frame with `rm1`,
    ///    `rm2` and, in `saved`, their two descriptors (`rm1.desc <- md1;
    ///    rm2.desc <- md2`, ctype.ml:2637-2641).
    /// 8. [`Checker::set_more`] for row 2 with `r1`, then for row 1 with
    ///    `r2` (ctype.ml:2618-2619).
    /// 9. When `closed`, a [`FrameKind::RowEnd`] frame (`left` the right
    ///    node `t2x`): `static_row row1` reads row 1 again after both
    ///    `set_more` (`row_repr`, btype.ml:162-170), and that row is closed
    ///    exactly when `closed` is (a fixed row 1 that is open while
    ///    `closed` holds has clashed in step 8). Then one [`FrameKind::RowField`] frame per
    ///    pair, the last pair of step 3's order first, so that they are
    ///    popped in that order; `left` and `right` of a frame are the two
    ///    `ty` of the pair's [`FieldRef`]s, `extra` the index in `saved`
    ///    of one record: `head` the left row-field index, `level` the
    ///    right one, `a` the handle of `more`, `b` [`ROW_FIXED1`] and
    ///    [`ROW_FIXED2`]. Then the pair a fixed row's `set_more` asked for,
    ///    if any, so that it is popped first.
    ///
    /// When step 5 or 8 clashes: in `Mode::Explain` `rm1` and `rm2` get
    /// their descriptors back and the clash's pair is pushed on
    /// `Checker::trace`; the frames and `saved` records this call pushed
    /// are taken off; `Err(Clash)`.
    ///
    /// Cost: the two flattenings and the merge; one step per field of a
    /// rest; per changed row what [`Checker::set_more`] allocates; 16
    /// bytes of frame and 16 of record per pair. (R3f)
    pub fn unify_row(&mut self, [t1x, t2x]: [Ty; 2], left: Node, right: Node) -> Result<(), Clash> {
        todo!("R3f")
    }

    /// `row_fixed row` (compiler/ml/btype.ml:153-160) for a flattened row:
    /// `fixed` of its last node's `VariantRow`, or `more` (the
    /// representative) is a universal variable or a constructor; a
    /// variable and `Tnil` are not. O(1). (R3f)
    pub fn row_is_fixed(&self, row: VariantRow, more: Ty) -> bool {
        let node = self.g.nodes[more.0 as usize];
        row.fixed
            || node.tag() == CONSTR
            || (node.head & EXTENDED != 0
                && matches!(self.extras.descriptors[node.a as usize], ExtraDescriptor::Univar(_)))
    }

    /// `set_more row rest` (compiler/ml/ctype.ml:2596-2616). `rest` is
    /// `extras.row_scratch[rest]`, the fields the other row has and `row`
    /// lacks; `row` is the `VariantRow` of the row that gains them, `rm`
    /// its `more`, `fixed` its [`Checker::row_is_fixed`]; `more`, `closed`
    /// and `name` (a `VariantRow` whose `name` and `name_arguments` are
    /// the chosen row's, with `home` the list index those arguments are
    /// slots of) are step 4 and 6 of [`Checker::unify_row`]; `first`
    /// says the gaining row is row 1 (the order of the clash's pair).
    ///
    /// 1. When `closed`, `filter_row_fields row.closed rest`
    ///    (ctype.ml:388-397), from the last field to the first: an absent
    ///    field is dropped; when `row.closed`, a field that is `Reither`
    ///    with `m` false is resolved to `Rabsent` ([`Checker::resolve`],
    ///    then [`Checker::settle`] of the list it returns) and dropped; the others stay, in their order.
    /// 2. A clash when a field is left and `row` is closed or fixed, or
    ///    when `closed`, `row` is fixed and `row` is not closed. Its pair
    ///    is a new empty closed row and a new open row of what is left
    ///    ([`Checker::trace_row`]), the empty one on `row`'s side
    ///    (`if row == row1 then (t1, t2) else (t2, t1)`), pushed on
    ///    `Checker::trace` in `Mode::Explain`.
    /// 3. A fixed row: nothing when `more` is `rm`; `Graph::link(rm,
    ///    more)` when `rm` is a variable; otherwise the pair `(rm, more)`
    ///    is returned for [`Checker::unify_row`] to push last (`unify env
    ///    rm more`; it is popped before the common tags, and after row 1's
    ///    `set_more` where OCaml runs it before: the two differ only in
    ///    which of two clashes is reported).
    /// 4. Any other row: a new variant node at the generic level
    ///    (`newgenty (Tvariant {row0 with row_fields = rest})`) whose
    ///    fields are what is left, in order, with `more`, `closed`, the
    ///    `fixed` of the two rows and the name; [`Checker::lower`] of it
    ///    to `rm`'s level; `Graph::link(rm, node)`. A field of the new
    ///    node is the field it copies, read now ([`field_repr`]): absent;
    ///    present with its type in a slot of its own or with none; or
    ///    `Either` with the `c` and `m` read, no type slot, and in its
    ///    reference slot **the handle the source home has in that field's
    ///    reference slot** (the two homes then hold one chain, as two rows
    ///    hold one `row_field` in OCaml).
    ///
    /// Allocates, for a row that is not fixed: one node, one descriptor
    /// row (12 bytes), one `VariantRow` (28), one `RowFieldRow` (20) per
    /// field left, and one slot per present type, per `Either` field, for
    /// `more` and per argument of the name. Nothing for a fixed row. One
    /// step a field of `rest`. (R3f)
    #[allow(clippy::too_many_arguments)]
    pub fn set_more(
        &mut self,
        row: VariantRow,
        rm: Ty,
        fixed: bool,
        rest: std::ops::Range<usize>,
        more: Ty,
        closed: bool,
        name: (VariantRow, u32),
        first: bool,
    ) -> Result<Option<[Ty; 2]>, Clash> {
        todo!("R3f")
    }

    /// `set_row_field e v` (compiler/ml/btype.ml:742-744) for a `v` that is
    /// not `Reither`: `Graph::write` of the unresolved reference `e` with
    /// a resolved node at `e`'s level: [`RES_ABSENT`]; [`RES_PRESENT`]
    /// with no slot (`ty` is `NONE`: `Rpresent None`) or with one new slot
    /// holding `ty`. Returns the head of the holder list `e` had.
    /// The holders are not touched: [`Checker::settle`] does that once the
    /// resolution stands. O(1); one slot for a type. (R3f)
    pub fn resolve(&mut self, e: Ty, kind: u32, ty: Ty) -> u32 {
        todo!("R3f")
    }

    /// The holders of a reference that was resolved to `kind`
    /// ([`RES_ABSENT`] or [`RES_PRESENT`]), from the row `holders`: what
    /// makes a holder's types children no longer, as `iter_row` visits
    /// only what `row_field_repr` gives (compiler/ml/btype.ml:112-121,
    /// 229-236). Each holder that is still a [`RES_EITHER`] node is
    /// written (`Graph::write`):
    /// - [`RES_ABSENT`]: an absent reference with no slot;
    /// - [`RES_PRESENT`]: a present reference whose one slot is the
    ///   holder's first type: the same list index `b` with arity 1
    ///   (`Rpresent (Some (List.hd tl))`). A holder of a list whose
    ///   reference is `Rpresent None` is left as it is.
    ///
    /// A holder that is anything else by now was written since and is
    /// skipped. O(holders), one step and at most one node write each, no
    /// allocation. (R3f)
    pub fn settle(&mut self, holders: u32, kind: u32) {
        todo!("R3f")
    }

    /// `set_row_field e (Reither (c, tl, m, e'))` (compiler/ml/ctype.ml:
    /// 2659-2660, 2707-2708): `Graph::write` of the unresolved reference
    /// `e` with a [`RES_EITHER`] node at `e`'s level whose flags are
    /// `flags` ([`RES_CONSTANT`], [`RES_MATCHED`]), whose slots are a new
    /// list of `extras.row_scratch[types]` (the `ty` of each) and then
    /// `next`. The holders of `e` become holders of `next`: one new
    /// [`Holder`] row per row of `e`'s list, and one for `e` itself when
    /// it got a type, in front of the list `next` has; `next`'s `b` is
    /// written last. O(types + holders of `e`), 8 bytes a holder. (R3f)
    pub fn resolve_either(&mut self, e: Ty, flags: u32, types: std::ops::Range<usize>, next: Ty) {
        todo!("R3f")
    }

    /// The pop of a [`FrameKind::RowField`] frame: `unify_row_field env
    /// fixed1 fixed2 more l f1 f2` (compiler/ml/ctype.ml:2643-2730) for the
    /// pair the frame's record describes. `Err([NONE, NONE])` is a clash
    /// with no pair of its own (`raise (Unify [])`); a clash of a lowering
    /// is `Err([NONE, NONE])` too, with the pair the lowering pushed.
    ///
    /// First a [`FrameKind::RowFieldEnd`] frame with the same `left`,
    /// `right` and `extra`: it stays below whatever this pushes, puts the
    /// pair of the two fields into the trace when a frame above it fails
    /// (ctype.ml:2622-2628), and is where the record leaves `saved`. Then
    /// `f1`, `f2` are the two fields read now ([`field_repr`]; the homes
    /// are opened, so the arity passed is `u32::MAX`), and by the pair of
    /// kinds, in OCaml's order of arms:
    ///
    /// - `Rpresent (Some t1), Rpresent (Some t2)`: the pair `(t1, t2)`.
    /// - `Rpresent None, Rpresent None`: nothing.
    /// - `Reither, Reither` with one unresolved reference (`e1 == e2`):
    ///   nothing.
    /// - `Reither (c1, tl1, m1, e1), Reither (c2, tl2, m2, e2)`, a row
    ///   fixed, neither constant, `tl1` and `tl2` of one length (PR#7496,
    ///   ctype.ml:2652-2661): a new unresolved reference `e` at the level
    ///   of `more`'s representative; [`Checker::resolve_either`] of `e1`
    ///   and of `e2` with `c1 || c2`, `m1 || m2`, no type and `e`; then
    ///   the pairs of `tl1` and `tl2` position by position, the first
    ///   popped first.
    /// - Any other two `Reither` (ctype.ml:2662-2708). When the row is not
    ///   passive and (`m1 || m2 || fixed1 || fixed2`, or rigid and one
    ///   list has one type) and `tl1 @ tl2` is not empty: a clash when `c1
    ///   || c2`; otherwise [`ROW_AGAIN`] is set in the record and the
    ///   pairs of the first type with each of the others are pushed, in
    ///   order. Otherwise [`Checker::join_either`] now.
    /// - `Reither (_, _, false, e1), Rabsent` when row 1 is not fixed:
    ///   [`Checker::resolve`] of `e1` to [`RES_ABSENT`] and
    ///   [`Checker::settle`]; the mirrored arm for `e2`.
    /// - `Rabsent, Rabsent`: nothing.
    /// - `Reither (false, tl, _, e1), Rpresent (Some t2)` when row 1 is not
    ///   fixed (ctype.ml:2711-2717): [`Checker::resolve`] of `e1` to
    ///   [`RES_PRESENT`] with `t2`; [`Checker::lower`] of `t2` to the
    ///   level of `more`'s representative; [`ROW_SETTLE`] is set in the
    ///   record, with the holder list and `e1` kept in the
    ///   `RowFieldEnd` frame (`left` the reference, `right` the list); in
    ///   `Mode::Explain` a [`FrameKind::Fields`] frame with `e1` twice and
    ///   the unresolved node it was, twice (`e1 := None` on a failure);
    ///   then the pairs `(t1, t2)` for each `t1` of `tl`, in order. The
    ///   mirrored arm resolves `e2` with `t1` and pushes `(t1, t)` for
    ///   each `t` of `tl`.
    /// - `Reither (true, [], _, e1), Rpresent None` when row 1 is not
    ///   fixed: [`Checker::resolve`] of `e1` to [`RES_PRESENT`] with no
    ///   type; mirrored for `e2`.
    /// - Anything else: a clash.
    ///
    /// The types of a field are read into `extras.row_scratch` above its
    /// current length ([`field_types`], the `ty` of a [`FieldRef`]) and
    /// taken off before the function returns. O(types of the two fields)
    /// plus the callees. PR#6744's split of the types that hold a
    /// universal variable (ctype.ml:2688-2702) is R3g's. (R3f)
    pub fn unify_row_field(&mut self, frame: Frame) -> Result<(), [Ty; 2]> {
        todo!("R3f")
    }

    /// The end of two `Reither` fields that stay `Reither`
    /// (compiler/ml/ctype.ml:2676-2708), for the record at `saved[record]`
    /// and its two fields read again: `tl1'` is each type of `tl2` whose
    /// representative is not the representative of a type of `tl1`
    /// (`remq tl1 tl2`), `tl2'` the mirror; [`Checker::lower`] of each of
    /// `tl1' @ tl2'` to the level of `more`'s representative; a new
    /// unresolved reference `e` at that level;
    /// [`Checker::resolve_either`] of `e1` with `c1 || c2`, `m1 || m2`,
    /// `tl1'` and `e`, and of `e2` with `tl2'`. O(|tl1| × |tl2|)
    /// comparisons of representatives, in the scratch, no allocation
    /// beyond the two lists. (R3f)
    pub fn join_either(&mut self, frame: Frame) -> Result<(), [Ty; 2]> {
        todo!("R3f")
    }

    /// The pop of a [`FrameKind::RowFieldEnd`] frame: everything the pair
    /// pushed has been unified. With [`ROW_AGAIN`] in the record: when
    /// one of the two fields' references is resolved by now (`!e1 <> None
    /// || !e2 <> None`, ctype.ml:2674: the field read again is not
    /// `Either`, or ends in another reference) the pair is unified again
    /// from the start (a new [`FrameKind::RowField`] frame with the record
    /// and the bit cleared); otherwise [`Checker::join_either`]. With
    /// [`ROW_SETTLE`]: [`Checker::settle`] of the frame's list
    /// ([`RES_PRESENT`]). Then the record leaves `saved` (`saved` is cut
    /// back to the frame's `extra`), unless the pair is unified again.
    /// O(1) plus the callee. (R3f)
    pub fn row_field_end(&mut self, frame: Frame) -> Result<(), [Ty; 2]> {
        todo!("R3f")
    }

    /// The pop of a [`FrameKind::RowEnd`] frame, pushed when the merged
    /// row is closed (`if static_row row1 then ... link_type rm (newty2
    /// rm.level Tnil)`, compiler/ml/ctype.ml:2630-2636), after every
    /// common tag. Row 1 read again has the tags of the right node's row
    /// (its own, and through its `more` those it gained); a tag only one
    /// of the two lists is one that was absent or was made absent, so
    /// "no field is `Reither`" is the same question on either. So:
    /// flatten the row of the frame's `left` (its representative; the
    /// scratch is cut back afterwards); when no field of it is `Either`
    /// ([`field_repr`]) and its `more` is a variable, that variable is
    /// linked to a new `Tnil` node at its level (one node, one 12-byte
    /// descriptor row). O(fields of the row), one step a field. (R3f)
    pub fn row_end(&mut self, frame: Frame) {
        todo!("R3f")
    }

    /// `mkvariant fields closed` (compiler/ml/ctype.ml:1704-1713) for a
    /// trace: a new variant node at the generic level whose fields are
    /// `extras.row_scratch[fields]` as [`Checker::set_more`] copies a
    /// field, whose `more` is a new variable at the current level, not
    /// fixed, with no name. Failure path of `Mode::Explain` only. (R3f)
    pub fn trace_row(&mut self, fields: std::ops::Range<usize>, closed: bool) -> Ty {
        todo!("R3f")
    }

    /// The trace pair of a common tag whose fields clashed
    /// (`(mkvariant [(l, f1)] true, mkvariant [(l, f2)] true) :: trace`,
    /// compiler/ml/ctype.ml:2624-2628), from a [`FrameKind::RowFieldEnd`]
    /// frame: two [`Checker::trace_row`] of one field each, closed.
    /// Failure path of `Mode::Explain` only. (R3f)
    pub fn row_trace_pair(&mut self, frame: Frame) -> [Ty; 2] {
        todo!("R3f")
    }

    /// The references of one variant node a copy made (`copy_row`,
    /// compiler/ml/btype.ml:366-392, with `keep = more.level <>
    /// generic_level`, ctype.ml:806): `node` at handle `copy`, of the copy
    /// session whose first node is `first`. Called by the pass of
    /// [`Checker::link_memorized`] for each variant node while
    /// `extras.copying` is set, which [`Checker::copy`] does around its
    /// pass: the node `copy` was copied from is `g.work[copy - first]`
    /// (`Graph::copy` queues each source when it makes its copy, and the
    /// pass does not touch the queue). An instance of a template never
    /// comes here: every node of a template is generic, so its rows are
    /// unopened and their row variables are the instance's own.
    ///
    /// The row variable is the representative of the node's `more` slot,
    /// followed through the variant nodes it leads to; the copy shares it
    /// (`keep`) when its handle is below `first`.
    ///
    /// - The source is unopened, not `keep`: nothing. The copy's
    ///   references are its own (`ref None`).
    /// - The source is unopened, `keep`: the source is opened with its
    ///   new references at the level of the row variable
    ///   ([`Checker::open_row`], then one `Graph::write` of the level of
    ///   each reference it made), so that every later copy shares them;
    ///   then the copy is opened onto the same unresolved references: its
    ///   own [`RES_EITHER`] node for each field that has types (the copy's
    ///   own type slots), a holder of the source's reference.
    /// - The source is opened, `keep`: each `Reither` field's chain must
    ///   end in the unresolved reference the source's ends in. When the
    ///   session copied that reference (its handle is at or above
    ///   `first`: it was generic while the row variable was not), the
    ///   slot that names it in the copy's chain is pointed at the
    ///   source's (`g.work[handle - first]`). The chain nodes of the copy
    ///   that have types become holders of it, each once.
    /// - The source is opened, not `keep`: each `Reither` field gets a
    ///   chain of its own with a new unresolved reference at its end, at
    ///   the current level (`ref None` per field). A chain node is taken
    ///   as it is when the session made it and no field of the session
    ///   has taken it (marks, one generation a session); otherwise it is
    ///   copied (one node, the same slots in a new list). The slot that
    ///   named the old end names the new one, and the chain nodes that
    ///   have types are its holders.
    ///
    /// A field whose chain ends resolved is left as the copy made it.
    /// O(fields of the node + their chains), one step a field; per
    /// `Reither` field at most one node per chain node, one reference
    /// and 8 bytes of holder. (R3n)
    pub fn copy_refs(&mut self, copy: Ty, node: Node, first: u32) {
        todo!("R3n")
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
    /// an unopened field is `Reither` with the types in its own slots; an
    /// opened one is read from its reference slot alone: `Reither` adds
    /// its types and gives `c` and `m` (`Reither (_, tl', _, {contents =
    /// Some fi}) -> row_field_repr_aux (tl @ tl') fi`); `Rpresent (Some _)`
    /// at the end is the first type met on the way (`Rpresent (Some
    /// (List.hd tl))`) or its own; `Rpresent None` and `Rabsent` are
    /// themselves.
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
        // Unopened: the node has three slots, the types are its own.
        let node = home(&mut g, end);
        let (repr, types) = read(&g, node, 3);
        assert_eq!(repr, FieldRepr { end: Ty(NONE), first: t0, types: 2, kind: either(false, false) });
        assert_eq!(types, [t0, t1]);
        // Opened, a field without types: the unresolved reference itself.
        let (repr, types) = read(&g, node, 4);
        assert_eq!(repr, FieldRepr { end, first: Ty(NONE), types: 0, kind: either(false, false) });
        assert!(types.is_empty());
        // Opened, the field's own `Reither (false, [t0; t1], true, end)`.
        let own = push(&mut g, TUPLE, RES_EITHER | RES_MATCHED, &[t0, t1, end]);
        let node = home(&mut g, own);
        let (repr, types) = read(&g, node, 4);
        assert_eq!(repr, FieldRepr { end, first: t0, types: 2, kind: either(false, true) });
        assert_eq!(types, [t0, t1]);
        // `Reither (true, [t3], false, end)` behind it.
        let added = push(&mut g, TUPLE, RES_EITHER | RES_CONSTANT, &[t3, end]);
        let own = push(&mut g, TUPLE, RES_EITHER, &[t0, t1, added]);
        let node = home(&mut g, own);
        let (repr, types) = read(&g, node, 4);
        assert_eq!(repr, FieldRepr { end, first: t0, types: 3, kind: either(true, false) });
        assert_eq!(types, [t0, t1, t3]);
        // `Rpresent (Some t2)` at the end: the first type met.
        let present = push(&mut g, TUPLE, RES_PRESENT, &[t2]);
        let own = push(&mut g, TUPLE, RES_EITHER, &[t0, t1, present]);
        let node = home(&mut g, own);
        let (repr, _) = read(&g, node, 4);
        assert_eq!(repr, FieldRepr { end: Ty(NONE), first: t0, types: 1, kind: RowFieldKind::Present });
        // With no type on the way, the reference's own.
        let node = home(&mut g, present);
        let (repr, _) = read(&g, node, 4);
        assert_eq!(repr, FieldRepr { end: Ty(NONE), first: t2, types: 1, kind: RowFieldKind::Present });
        // `Rpresent None` and `Rabsent`.
        let none = push(&mut g, TUPLE, RES_PRESENT, &[]);
        let node = home(&mut g, none);
        let (repr, _) = read(&g, node, 4);
        assert_eq!(repr, FieldRepr { end: Ty(NONE), first: Ty(NONE), types: 0, kind: RowFieldKind::Present });
        let absent = push(&mut g, TUPLE, RES_ABSENT, &[]);
        let node = home(&mut g, absent);
        let (repr, _) = read(&g, node, 4);
        assert_eq!(repr, FieldRepr { end: Ty(NONE), first: Ty(NONE), types: 0, kind: RowFieldKind::Absent });
        // A field that is not `Reither` has no reference: its own slot.
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

    /// A checker whose pools hold one row of `n` fields, `kind(k)` the k-th,
    /// each with one type when `typed`, named `f00000` and up, as
    /// `Extras::from_segment` lays out a published row; and the node.
    fn row_of(n: u32, typed: bool, kind: impl Fn(u32) -> RowFieldKind) -> (Checker, Ty) {
        let mut c = Checker::new(Graph::default(), Default::default());
        let ty = push(&mut c.g, CONSTR, 0, &[]);
        let mut slots = Vec::new();
        for k in 0..n {
            let start = c.extras.names.bytes.len() as u32;
            c.extras.names.bytes.extend_from_slice(format!("f{k:05}").as_bytes());
            c.extras.names.spans.push(Range { start, len: 6 });
            let types = Range { start: slots.len() as u32, len: u32::from(typed) };
            if typed {
                slots.push(ty);
            }
            c.extras.row_fields.push(RowFieldRow { name: k, types, link: NONE, kind: kind(k) });
        }
        let more = slots.len() as u32;
        slots.push(push(&mut c.g, VAR, NONE, &[]));
        let row = VariantRow {
            fields: Range { start: 0, len: n },
            more,
            name: NONE,
            name_arguments: Range::default(),
            closed: false,
            fixed: false,
        };
        let mut slot = published_slots(row, &c.extras.row_fields);
        for field in &mut c.extras.row_fields {
            if matches!(field.kind, RowFieldKind::Either { .. }) {
                field.link = slot;
                slot += 1;
            }
        }
        c.extras.variants.push(row);
        c.extras.descriptors.push(ExtraDescriptor::Variant(0));
        let node = push(&mut c.g, TUPLE | EXTENDED, 0, &slots);
        (c, node)
    }

    /// Opening a node of 10,000 `Reither` fields with a type each is one
    /// step a field and two nodes a field; a second opening is none.
    #[test]
    fn opening_ten_thousand_fields_is_one_step_a_field() {
        let either = |_| RowFieldKind::Either { constant: false, matched: false };
        let (mut c, ty) = row_of(10_000, true, either);
        let nodes = c.g.nodes.len();
        let opened = super::super::steps::scope(|| {
            c.open_row(ty);
        });
        assert_eq!(opened, 10_000);
        assert_eq!(c.g.nodes.len() - nodes, 20_000);
        assert_eq!(c.g.nodes[ty.0 as usize].arity(), 20_001);
        let again = super::super::steps::scope(|| {
            c.open_row(ty);
        });
        assert_eq!(again, 0);
    }

    /// `merge_rows` of two lists of 10,000 tags, every other tag common:
    /// one step a merge step, at most 15,000; the pairs descending.
    #[test]
    fn merging_ten_thousand_tags_is_one_step_a_merge_step() {
        let (mut c, _) = row_of(15_000, false, |_| RowFieldKind::Present);
        let field = |k: u32| FieldRef { name: k, at: k, ty: Ty(0) };
        // Left: the even tags and the first 5,000 odd ones, reversed; right:
        // the even tags and the last 5,000 names.
        let left: Vec<FieldRef> = (0..10_000).rev().map(field).collect();
        let right: Vec<FieldRef> = (0..5_000).map(|k| field(2 * k)).chain((10_000..15_000).map(field)).collect();
        c.extras.row_scratch.extend(left);
        c.extras.row_scratch.extend(right);
        let mut pairs = 0;
        let steps = super::super::steps::scope(|| pairs = c.merge_rows(0, 10_000));
        assert_eq!(pairs, 5_000);
        assert!(steps <= 15_000, "{steps}");
        let scratch = &c.extras.row_scratch;
        assert_eq!(scratch.len(), 5_000 + 5_000 + 10_000);
        assert_eq!((scratch[0].name, scratch[4_999].name), (1, 9_999));
        assert_eq!((scratch[5_000].name, scratch[9_999].name), (10_000, 14_999));
        assert_eq!((scratch[10_000].name, scratch[10_001].name), (9_998, 9_998));
        assert_eq!(scratch[19_999].name, 0);
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
