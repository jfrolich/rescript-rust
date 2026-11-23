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

use super::expand::{ABBREV, DATATYPE, ExpandMode, Manifest, NEWTYPE, Newtype, TypeInfo, TypeTable};
use super::graph::{ARROW, CONSTR, GENERIC, Graph, LINK, Mode, NONE, Node, TUPLE, Ty, VAR};
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
    /// Scratch of one [`Checker::free_univar`] walk: per polymorphic type
    /// the walk entered, whether it is still open. Empty between walks; it
    /// keeps its capacity. (R3g)
    pub open_polys: Vec<bool>,
    /// How many `descriptors` rows are `Univar`: zero means the graph has
    /// no universal variable, and [`Checker::occur_univar`] returns on
    /// this one read. Kept by [`Extras::from_segment`] and
    /// [`Extras::univar`], the only two makers of such a row. (R3g)
    pub univars: u32,
    /// The tables of `Checker::instance_poly`. (R3q)
    pub poly: PolyCopy,
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

/// In the `b` of a record: [`Checker::split_univars`] pushed the pairs of
/// the types that hold a universal variable (PR#6744,
/// compiler/ml/ctype.ml:2696-2699); [`Checker::row_field_end`] runs
/// [`Checker::join_either`] again when they are unified, and that second
/// run does not split. (R3g)
pub const ROW_UNIVARS: u32 = 16;

/// One open scope of universal variables: what `enter_poly` puts on
/// `univar_pairs` for two polymorphic types (`(cl1, cl2) :: (cl2, cl1)`,
/// compiler/ml/ctype.ml:1670-1672), once, for both directions. 20 bytes.
///
/// The bound variables are not copied: `left` and `right` are the list
/// indices of the first bound variable of each type (slot 1 of the node:
/// lists never move), `left_len` and `right_len` how many each has. OCaml
/// keeps `List.map repr tl` and takes `repr` again at every lookup
/// (`find_univ`, ctype.ml:1546-1551); reading the slot and taking `repr`
/// at the lookup finds the same node.
///
/// `partners` is the first of `left_len + right_len` consecutive *partner
/// nodes*, one per bound variable, left ones first: the `ref None` of
/// `(t, ref None)` (ctype.ml:1670). A partner node is a node of the graph
/// that no node has as a child ([`partner_node`]), as a mutability cell
/// is, so that `set_univar` (compiler/ml/btype.ml:739-741, which logs
/// `Cuniv`) is `Graph::write`: logged inside a speculation and undone by
/// its restore, with no log of its own.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct PolyScope {
    pub left: u32,
    pub right: u32,
    pub left_len: u32,
    pub right_len: u32,
    pub partners: Ty,
}

/// The partner of a bound variable in an open scope (`Tunivar` `option
/// ref`, compiler/ml/ctype.ml:1670): a `VAR` at level 0 whose `a` is the
/// partner's handle, or `NONE` while it has none. No node has it as a
/// child, so no walk of a type meets it. O(1).
pub fn partner_node(partner: Ty) -> Node {
    Node {
        head: VAR,
        level: 0,
        a: partner.0,
        b: 0,
    }
}

/// What a module type answers for one type name a package of it does not
/// list (`complete_type_list`, compiler/ml/ctype.ml:2135-2169).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Completion {
    /// A public abstract type without parameters that has a manifest: an
    /// instance of the manifest, free of the module type's own names, at
    /// the level asked for (`(n, nondep_instance env' lv2 id2 t2)`,
    /// ctype.ml:2155).
    Type(Ty),
    /// A public abstract type without parameters and without a manifest
    /// (ctype.ml:2156-2163): skipped with `allow_absent` (subtyping, R3j),
    /// incompatible otherwise.
    Abstract,
    /// The module type has no type of that name (`Not_found`, ctype.ml:
    /// 2166): skipped with `allow_absent`, incompatible otherwise.
    Missing,
    /// Any other declaration, or a manifest that cannot be freed of the
    /// module type's own names (`raise Exit`, ctype.ml:2164):
    /// incompatible.
    Other,
}

/// What [`Checker::unify_package`] asks of the declarations, which the
/// kernel does not have (CHECKER_REWRITE 8.6, decision 52). R5a supplies
/// it over its module types; the tests of R3p supply one built by hand.
/// Three questions and no state the kernel reads: the names of a package
/// are ordered by `Longident.cmp`, which is on the declarations' side.
pub trait PackageDecls {
    /// `Longident.cmp` (compiler/ml/longident.ml:17-28) of two names of
    /// package rows. A name is a POSITION in the pool that
    /// `PackageRow::longidents` ranges over (`SignaturePools::indices` for
    /// the rows of a segment): `row.longidents.start + i` for the `i`-th
    /// name. The kernel never reads that pool. O(components).
    fn compare(&self, left: u32, right: u32) -> Ordering;
    /// The answer of module type `path` (a `PackageRow::path`) for the
    /// type name `name`, as [`Completion`]; an instance is made in `c` at
    /// `level`. Called once per name one package lists and the other
    /// does not.
    fn complete(&mut self, c: &mut Checker, path: u32, name: u32, level: u32) -> Completion;
    /// For two packages of different paths, after their completed lists
    /// are unified: `eq_package_path env p1 p2 || (!package_subtype env p1
    /// n1 tl1 p2 n2 tl2 && !package_subtype env p2 n2 tl2 p1 n1 tl1)`
    /// (ctype.ml:2175-2180), without the `Path.same` the kernel has
    /// already tested. `left` and `right` are the two descriptors; the
    /// arguments are their slots.
    fn compatible(&mut self, c: &mut Checker, left: Node, right: Node) -> bool;
}

/// One equation of pattern mode in force (`Env.add_local_constraint`,
/// compiler/ml/ctype.ml:2093-2100): the type that got a manifest and the
/// `TypeInfo` row it had before, so that cutting the log back puts the
/// row back ([`Checker::cut_equations`]). 20 bytes; one per equation
/// added and not yet cut. (R3h; CHECKER_REWRITE 8.9)
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct Equation {
    pub type_index: u32,
    pub previous: super::expand::TypeInfo,
}

/// What two declarations answer when `mcomp` compares them
/// (`mcomp_type_decl`, compiler/ml/ctype.ml:2011-2039).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DeclMatch {
    /// The kinds, the representations, the names, flags and number of the
    /// members agree; the pairs of member types were pushed
    /// ([`Checker::push_compatible`]).
    Members,
    /// They cannot be one type (`raise (Unify [])`).
    Clash,
}

/// What pattern mode asks of the declarations, which the kernel does not
/// have (CHECKER_REWRITE 8.9). R5a supplies it; the tests of R3h supply
/// one built by hand. Held in [`Checker::locals`]; without one, `reify`
/// of a type that has a variable stops the compiler (a caller that types
/// a pattern installs one first) and two different data types clash.
pub trait LocalDecls {
    /// A new locally abstract type for `reify` (`create_fresh_constr`,
    /// compiler/ml/ctype.ml:1815-1826): the supplier makes the identifier
    /// (`get_new_abstract_name` of `"$'" ^ name`, or `"$"` when `name` is
    /// `NONE`; `name` is the variable's name index) and whatever its own
    /// tables hold for a declaration, and returns the type index. The
    /// kernel writes the [`TypeTable`](super::expand::TypeTable) row
    /// (abstract, [`NEWTYPE`](super::expand::NEWTYPE), both newtype levels
    /// the current one). O(1) amortized.
    fn fresh_abstract(&mut self, name: u32) -> u32;
    /// `mcomp_type_decl` for two DIFFERENT types that are both data types
    /// (a record, a variant or an open type) and not both names of the
    /// unit being checked (ctype.ml:2026-2037): `Clash` unless both are
    /// records of one representation, both variants, or both open; for
    /// records and variants every pair of member types is pushed with
    /// [`Checker::push_compatible`], in declaration order, the result
    /// before the arguments, and a difference in names, mutability,
    /// optionality, argument shape or number of members is a `Clash`
    /// (`mcomp_variant_description`, `mcomp_record_description`,
    /// ctype.ml:2047-2078). The member types are nodes of `c`'s graph:
    /// the declarations' own types, not instances for the two argument
    /// lists, as in OCaml. O(members).
    fn compare(&mut self, c: &mut Checker, left: u32, right: u32) -> DeclMatch;
}

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

/// One row a node of the graph, for the walk of
/// [`Checker::instance_poly`] (R3q; CHECKER_REWRITE 8.10): 16 bytes. The
/// table is [`PolyCopy::slots`], indexed by the node's handle.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct PolySlot {
    /// `2 * call` when `Checker::mark_holders` of the call met the
    /// node, `2 * call + 1` when a universal variable is free below it;
    /// anything else is a row of an earlier call.
    pub stamp: u32,
    /// The first [`PolyEdge`] of its parents, or `NONE`. Read only while
    /// the stamp is the call's.
    pub parents: u32,
    /// Its copy while it is on the way of `Checker::copy_sep`, and for
    /// a universal variable while a binder on the way binds it; `NONE`
    /// otherwise, and always between two calls.
    pub copy: Ty,
    /// [`PolyCopy::depth`] when `copy` was set.
    pub depth: u32,
}

/// One edge of the inverse graph of `Checker::mark_holders`
/// (`inv_parents`, compiler/ml/ctype.ml:678-681): 8 bytes. `next` is the
/// next edge of the same child or `NONE`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(C)]
pub struct PolyEdge {
    pub parent: Ty,
    pub next: u32,
}

/// The tables and pools of [`Checker::instance_poly`], kept between
/// calls for their capacity and empty for a unit that never calls it.
#[derive(Default)]
pub struct PolyCopy {
    /// One row a node of the graph.
    pub slots: Vec<PolySlot>,
    /// The inverse graph of the call.
    pub edges: Vec<PolyEdge>,
    /// The polymorphic types with bound variables below the body, in
    /// the order the first walk met them.
    pub binders: Vec<Ty>,
    /// `delayed_copy` (compiler/ml/ctype.ml:1027-1028): a stub and the generic
    /// node, without a universal variable, whose copy it becomes a link
    /// to.
    pub delayed: Vec<[Ty; 2]>,
    /// The field nodes the walk made, for their cells.
    pub fields: Vec<Ty>,
    /// The types of one `Reither` field while a row is copied.
    pub types: Vec<Ty>,
    /// The number of the call; a stamp is `2 * call` or `2 * call + 1`.
    pub call: u32,
    /// How many binders are entered on the way (`List.length bound`,
    /// counted in binders and not in variables).
    pub depth: u32,
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
    each_field_types(g, b, arity, field, |types| out.extend_from_slice(types));
}

/// [`field_types`] for any destination: `each` gets the types of the
/// field one run of slots at a time, in order. Same cost, no allocation.
pub fn each_field_types(g: &Graph, b: u32, arity: u32, field: RowFieldRow, mut each: impl FnMut(&[Ty])) {
    if field.link >= arity {
        let own = field.types;
        each(&g.lists[(b + own.start) as usize..(b + own.start + own.len) as usize]);
        return;
    }
    let mut reference = g.lists[(b + field.link) as usize];
    loop {
        let node = g.nodes[reference.0 as usize];
        if node.tag() != TUPLE || node.a & RES_KIND != RES_EITHER {
            return;
        }
        let added = node.arity() - 1;
        each(&g.lists[node.b as usize..(node.b + added) as usize]);
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
        let univars = descriptors
            .iter()
            .filter(|descriptor| matches!(descriptor, ExtraDescriptor::Univar(_)))
            .count() as u32;
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
            open_polys: Vec::new(),
            univars,
            poly: PolyCopy::default(),
        }
    }

    /// O(1) amortized: a new `Univar` descriptor row with `name` (a name
    /// index or `NONE`), counted in `univars`; its index is the `a` of a
    /// universal variable's node (`TUPLE | EXTENDED`, no slot). Every
    /// maker of a universal variable outside a segment calls this, so
    /// that the count stays the gate of [`Checker::occur_univar`]. A copy
    /// of a universal variable makes no row: it keeps the `a` of its
    /// source (`Tunivar _ as ty -> ty`, compiler/ml/btype.ml:536). (R3g)
    pub fn univar(&mut self, name: u32) -> u32 {
        self.univars += 1;
        self.descriptors.push(ExtraDescriptor::Univar(name));
        self.descriptors.len() as u32 - 1
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
        match self.opened_row(node) {
            Some(opened) => {
                self.g.write(ty, opened);
                opened
            }
            None => node,
        }
    }

    /// [`Checker::open_row`] for a node the caller made since the last
    /// speculation was opened: the node is stored, not logged, so that a
    /// restore of that speculation leaves it opened. For a copy inside
    /// [`Checker::duplicate`], whose restore must put back the levels of
    /// the source and nothing of the copy (`Checker::match_unmatched`).
    /// The cost of `open_row` without the trail entry.
    fn open_fresh(&mut self, ty: Ty) -> Node {
        let node = self.g.nodes[ty.0 as usize];
        match self.opened_row(node) {
            Some(opened) => {
                self.g.nodes[ty.0 as usize] = opened;
                opened
            }
            None => node,
        }
    }

    /// The node [`Checker::open_row`] writes for descriptor `node`, with
    /// its new list, references and holders made, or `None` when there is
    /// nothing to open. Its cost is `open_row`'s.
    fn opened_row(&mut self, node: Node) -> Option<Node> {
        if node.head & EXTENDED == 0 {
            return None;
        }
        let ExtraDescriptor::Variant(row) = self.extras.descriptors[node.a as usize] else {
            return None;
        };
        let fields = self.extras.variants[row as usize].fields;
        let fields = fields.start as usize..(fields.start + fields.len) as usize;
        // The k-th reference slot is `published_slots + k` (`from_segment`):
        // the first `Reither` field's slot is the count of published slots,
        // the last one's is one below the opened arity, and a node is
        // opened exactly when its arity covers the first.
        let either = |field: &&RowFieldRow| matches!(field.kind, RowFieldKind::Either { .. });
        let row_fields = &self.extras.row_fields[fields.clone()];
        let published = row_fields.iter().find(either).map(|field| field.link)?;
        if published < node.arity() {
            return None;
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
        Some(Node {
            head: (node.head & 0xff) | arity << 8,
            b,
            ..node
        })
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
    /// After step 8 a row that is not fixed has a variant node as its
    /// `more`, and the arguments of its name stop being children of its
    /// home (`Checker::drop_name_children`; CHECKER_REWRITE 8.6, decision
    /// 60): the home of row 2 is its last node, or `t2x`; the home of row
    /// 1 is its last node, or `t1x` when `t1x` is still a variant node,
    /// which it is in pattern mode only (`unify3` links it in expression
    /// mode, and a link has no children).
    ///
    /// Cost: the two flattenings and the merge; one step per field of a
    /// rest; per changed row what [`Checker::set_more`] allocates; 16
    /// bytes of frame and 16 of record per pair; and for the names two
    /// compares per row that is not fixed (`name` against none, the
    /// number of its arguments against zero), on the `VariantRow` the
    /// call has loaded: no read. A row with a name that has arguments
    /// pays one node load more (its home's head) and, when the home is
    /// not a link, one list of the home's slots. (R3f)
    pub fn unify_row(&mut self, [t1x, t2x]: [Ty; 2], left: Node, right: Node) -> Result<(), Clash> {
        // 1. `row_repr` of both.
        let base = self.extras.row_scratch.len();
        let (last1, rm1) = self.flatten_row(left);
        let n1 = self.extras.row_scratch.len() - base;
        let (last2, rm2) = self.flatten_row(right);
        let n2 = self.extras.row_scratch.len() - base - n1;
        // 2. `if unify_eq rm1 rm2 then ()`.
        if rm1 == rm2 {
            self.extras.row_scratch.truncate(base);
            return Ok(());
        }
        let home = |c: &Checker, last: Ty, top: Node| {
            let node = if last.0 == NONE { top } else { c.g.nodes[last.0 as usize] };
            let ExtraDescriptor::Variant(row) = c.extras.descriptors[node.a as usize] else {
                unreachable!("a variant node");
            };
            (c.extras.variants[row as usize], node.b)
        };
        let (row1, home1) = home(self, last1, left);
        let (row2, home2) = home(self, last2, right);
        // 3. `merge_row_fields`: `r1`, `r2`, then the pairs.
        let pairs = self.merge_rows(base, n1);
        let r1 = base..base + n1 - pairs;
        let r2 = r1.end..r1.end + n2 - pairs;
        let paired = r2.end..r2.end + 2 * pairs;
        // 4. `more`, `fixed`, `closed` (ctype.ml:2547-2553).
        let fixed1 = self.row_is_fixed(row1, rm1);
        let fixed2 = self.row_is_fixed(row2, rm2);
        let more = if fixed1 {
            rm1
        } else if fixed2 {
            rm2
        } else {
            let level = self.g.nodes[rm1.0 as usize].level.min(self.g.nodes[rm2.0 as usize].level);
            self.g.push(Node { head: VAR, level, a: NONE, b: 0 })
        };
        let closed = row1.closed || row2.closed;
        let explain = self.g.mode == Mode::Explain;
        let (frames, saved) = (self.frames.len(), self.saved.len());
        // 5. The empty type (ctype.ml:2564-2573).
        let empty1 = self.all_absent(r1.clone());
        let empty2 = self.all_absent(r2.clone());
        let a_side_absent = (0..pairs).all(|k| {
            let at = paired.start + 2 * k;
            self.absent_now(at) || self.absent_now(at + 1)
        });
        let result = if closed && (empty1 || row2.closed) && (empty2 || row1.closed) && a_side_absent {
            if explain {
                let t1 = self.trace_row(base..base, true);
                let t2 = self.trace_row(base..base, true);
                self.trace.push([t1, t2]);
            }
            Err(Clash)
        } else {
            // 6. The name (ctype.ml:2574-2586); `keep` for row 1, then for
            //    row 2.
            let keep = |c: &Checker, first: usize| {
                (0..pairs).all(|k| {
                    let at = paired.start + 2 * k;
                    c.absent_now(at + first) || !c.absent_now(at + 1 - first)
                })
            };
            let chosen = if row1.name != NONE
                && (row1.closed || empty2)
                && (!row2.closed || (keep(self, 0) && empty1))
            {
                Some((row1, home1))
            } else if row2.name != NONE
                && (row2.closed || empty1)
                && (!row1.closed || (keep(self, 1) && empty2))
            {
                Some((row2, home2))
            } else {
                None
            };
            let row0 = VariantRow {
                fields: Range::default(),
                more: 0,
                name: chosen.map_or(NONE, |(row, _)| row.name),
                name_arguments: chosen.map_or(Range::default(), |(row, _)| row.name_arguments),
                closed,
                fixed: fixed1 || fixed2,
            };
            let name = (row0, chosen.map_or(0, |(_, home)| home));
            // 7. `let md1 = rm1.desc and md2 = rm2.desc`.
            if explain {
                let extra = self.saved.len() as u32;
                self.saved.push(self.g.nodes[rm1.0 as usize]);
                self.saved.push(self.g.nodes[rm2.0 as usize]);
                self.frames.push(Frame { left: rm1, right: rm2, kind: FrameKind::Fields, extra });
            }
            // 8. `set_more row2 r1; set_more row1 r2`.
            self.set_more(row2, rm2, fixed2, r1, more, closed, name, false)
                .and_then(|pair2| {
                    let pair1 = self.set_more(row1, rm1, fixed1, r2, more, closed, name, true)?;
                    Ok(pair2.or(pair1))
                })
        };
        let pair = match result {
            Ok(pair) => pair,
            Err(clash) => {
                if explain && self.frames.len() > frames {
                    // `rm1.desc <- md1; rm2.desc <- md2` (ctype.ml:2637-2641):
                    // the descriptor, at the level the rest has now.
                    for (rest, slot) in [(rm1, saved), (rm2, saved + 1)] {
                        let level = self.g.nodes[rest.0 as usize].level;
                        self.g.write(rest, Node { level, ..self.saved[slot] });
                    }
                }
                self.frames.truncate(frames);
                self.saved.truncate(saved);
                self.extras.row_scratch.truncate(base);
                return Err(clash);
            }
        };
        // A row that is not fixed has a variant node as its `more` now
        // (`link_type rm ty`, ctype.ml:2619), so its name's arguments are
        // children no longer (`iter_row`, btype.ml:229-241).
        // The home of row 1 is the left node itself when `last1` is none.
        // In expression mode `unify3` has linked that node away and it
        // has no children left; in pattern mode it is still a variant
        // node (CHECKER_REWRITE 8.6, decision 60). The node is read only
        // for a row that has a name with arguments.
        let homes = [
            (fixed1, row1, if last1.0 == NONE { t1x } else { last1 }),
            (fixed2, row2, if last2.0 == NONE { t2x } else { last2 }),
        ];
        for (kept, row, home) in homes {
            if !kept
                && row.name != NONE
                && row.name_arguments.len != 0
                && self.g.nodes[home.0 as usize].head != LINK
            {
                self.drop_name_children(home, row);
            }
        }
        // 9. The static row below the common tags, which are popped in the
        //    order of the pairs, then the pair a fixed row asked for.
        if closed {
            self.frames.push(Frame { left: t2x, right: t2x, kind: FrameKind::RowEnd, extra: 0 });
        }
        let flags = if fixed1 { ROW_FIXED1 } else { 0 } | if fixed2 { ROW_FIXED2 } else { 0 };
        for k in (0..pairs).rev() {
            let at = paired.start + 2 * k;
            let (f1, f2) = (self.extras.row_scratch[at], self.extras.row_scratch[at + 1]);
            let extra = self.saved.len() as u32;
            self.saved.push(Node { head: f1.at, level: f2.at, a: more.0, b: flags });
            self.frames.push(Frame { left: f1.ty, right: f2.ty, kind: FrameKind::RowField, extra });
        }
        if let Some([rm, more]) = pair {
            self.frames.push(Frame { left: rm, right: more, kind: FrameKind::Pair, extra: 0 });
        }
        self.extras.row_scratch.truncate(base);
        Ok(())
    }

    /// The arguments of a row's name stop being children of variant node
    /// `home` (a representative, whose `VariantRow` is `row`) once the
    /// row's `more` is a variant node: OCaml's `iter_row` visits them only
    /// for the row a chain of rows ends in (compiler/ml/btype.ml:229-241):
    ///
    /// ```text
    /// match (repr row.row_more).desc with
    /// | Tvariant row -> iter_row f row
    /// | Tvar _ | Tunivar _ | Tsubst _ | Tconstr _ | Tnil ->
    ///   Misc.may (fun (_, l) -> List.iter f l) row.row_name
    /// ```
    ///
    /// and every walk of a type goes through it (`iter_type_expr`,
    /// btype.ml:263-265): `update_level`, `generalize`, `deep_occur`,
    /// `occur_univar`, `univars_escape`; a copy takes the name of the
    /// innermost row (`row_repr`, btype.ml:126-135). The kernel's walks
    /// push every slot of a node, so the node is written
    /// (`Graph::write`, logged in a speculation) with a new list in which
    /// each slot of the name's arguments holds what the `more` slot
    /// holds: a child the walk reaches anyway. The shared `VariantRow` is
    /// not written, and nothing reads the name of a row that is not the
    /// innermost (`row_repr`). In `Mode::Explain` a
    /// [`FrameKind::Fields`] frame puts the node's descriptor back when
    /// the unification fails, as it puts back the two rests, whose links
    /// are what made the name stale (`rm1.desc <- md1`, ctype.ml:
    /// 2637-2641). Called by [`Checker::unify_row`] for a row that has a
    /// name with arguments and is not fixed: O(slots of the node), one
    /// list of that length; a row without a name with arguments costs the
    /// two compares of the caller. (CHECKER_REWRITE 8.6, decision 60)
    #[cold]
    #[inline(never)]
    fn drop_name_children(&mut self, home: Ty, row: VariantRow) {
        if self.g.mode == Mode::Explain {
            let node = self.g.nodes[home.0 as usize];
            let extra = self.saved.len() as u32;
            self.saved.push(node);
            self.saved.push(node);
            self.frames.push(Frame {
                left: home,
                right: home,
                kind: FrameKind::Fields,
                extra,
            });
        }
        self.forget_name_children(home, row);
    }

    /// The write of [`Checker::drop_name_children`] without its frame:
    /// variant node `home`, whose `VariantRow` is `row`, gets a new list
    /// in which each slot of the name's arguments holds what the `more`
    /// slot holds (`Graph::write`, logged in a speculation). For a caller
    /// whose link of the row variable stays when the unification fails:
    /// `reify` (compiler/ml/ctype.ml:1848-1853: the link is written
    /// before the clash and `unify3`'s handler puts back the left
    /// descriptor only, ctype.ml:2436-2438). O(slots of the node), one
    /// list of that length.
    fn forget_name_children(&mut self, home: Ty, row: VariantRow) {
        let node = self.g.nodes[home.0 as usize];
        let b = self.g.lists.len() as u32;
        self.g
            .lists
            .extend_from_within(node.b as usize..(node.b + node.arity()) as usize);
        let more = self.g.lists[(b + row.more) as usize];
        let arguments = row.name_arguments;
        self.g.lists
            [(b + arguments.start) as usize..(b + arguments.start + arguments.len) as usize]
            .fill(more);
        self.g.write(home, Node { b, ..node });
    }

    /// O(chain): the field `extras.row_scratch[at]` is, read now
    /// ([`field_repr`]; its home is opened, so every `Reither` field of it
    /// has its reference slot).
    #[inline]
    fn field_now_at(&self, at: usize) -> FieldRepr {
        let field = self.extras.row_scratch[at];
        field_repr(&self.g, field.ty.0, u32::MAX, self.extras.row_fields[field.at as usize])
    }

    /// O(chain): whether the field `extras.row_scratch[at]` is `Rabsent`.
    #[inline]
    fn absent_now(&self, at: usize) -> bool {
        self.field_now_at(at).kind == RowFieldKind::Absent
    }

    /// `empty fields` (compiler/ml/ctype.ml:2563) of a range of the
    /// scratch. O(fields + chains), no write.
    fn all_absent(&self, fields: std::ops::Range<usize>) -> bool {
        fields.into_iter().all(|at| self.absent_now(at))
    }

    /// `newgenty (Tvariant row)` for the fields `extras.row_scratch[fields]`
    /// as [`Checker::set_more`] copies a field, with `more`, `closed`,
    /// `fixed` and the name and name arguments of `name.0` (slots of the
    /// list at `name.1`). Slots: the present types in field order, `more`,
    /// the name's arguments, then one reference slot per `Either` field
    /// holding the handle its source home has in that field's reference
    /// slot. Each field is copied as its row has it, not read through
    /// its chain. One node, one descriptor row, one `VariantRow`, one
    /// `RowFieldRow` a field and those slots; two row loads per field
    /// (one to count the slots, one to fill them), no allocation beyond
    /// the pools.
    fn build_variant(
        &mut self,
        fields: std::ops::Range<usize>,
        more: Ty,
        closed: bool,
        fixed: bool,
        name: (VariantRow, u32),
    ) -> Ty {
        let (mut types, mut references) = (0, 0);
        for at in fields.clone() {
            let field = self.extras.row_fields[self.extras.row_scratch[at].at as usize];
            match field.kind {
                RowFieldKind::Present => types += field.types.len,
                RowFieldKind::Either { .. } => references += 1,
                RowFieldKind::Absent => {}
            }
        }
        let arguments = if name.0.name == NONE { Range::default() } else { name.0.name_arguments };
        let published = types + 1 + arguments.len;
        let b = self.g.lists.len() as u32;
        self.g.lists.resize((b + published + references) as usize, Ty(NONE));
        let start = self.extras.row_fields.len() as u32;
        let (mut typed, mut referenced) = (0, 0);
        for at in fields.clone() {
            let source = self.extras.row_scratch[at];
            let row_field = self.extras.row_fields[source.at as usize];
            let mut copy = RowFieldRow {
                name: row_field.name,
                types: Range::default(),
                link: NONE,
                kind: row_field.kind,
            };
            match row_field.kind {
                RowFieldKind::Present if row_field.types.len != 0 => {
                    let ty = self.g.lists[(source.ty.0 + row_field.types.start) as usize];
                    self.g.lists[(b + typed) as usize] = ty;
                    copy.types = Range { start: typed, len: 1 };
                    typed += 1;
                }
                RowFieldKind::Either { .. } => {
                    copy.link = published + referenced;
                    let chain = self.g.lists[(source.ty.0 + row_field.link) as usize];
                    self.g.lists[(b + copy.link) as usize] = chain;
                    referenced += 1;
                }
                _ => {}
            }
            self.extras.row_fields.push(copy);
        }
        self.g.lists[(b + types) as usize] = more;
        let from = (name.1 + arguments.start) as usize;
        self.g
            .lists
            .copy_within(from..from + arguments.len as usize, (b + types + 1) as usize);
        let row = self.extras.variants.len() as u32;
        self.extras.variants.push(VariantRow {
            fields: Range { start, len: fields.len() as u32 },
            more: types,
            name: name.0.name,
            name_arguments: Range { start: types + 1, len: arguments.len },
            closed,
            fixed,
        });
        let a = self.extras.descriptors.len() as u32;
        self.extras.descriptors.push(ExtraDescriptor::Variant(row));
        self.g.push(Node {
            head: TUPLE | EXTENDED | (published + references) << 8,
            level: GENERIC,
            a,
            b,
        })
    }

    /// The variant arm of `update_level` (compiler/ml/ctype.ml:615-621)
    /// for variant node `ty` above `level`, whose descriptor is `node`:
    ///
    /// ```text
    /// | Tvariant row ->
    ///   let row = row_repr row in
    ///   (match row.row_name with
    ///   | Some (p, _tl) when level < get_level env p ->
    ///     log_type ty;
    ///     ty.desc <- Tvariant {row with row_name = None}
    ///   | _ -> ());
    /// ```
    ///
    /// Returns the descriptor `ty` has afterwards, which the caller
    /// lowers and whose slots it walks. The name read is that of the
    /// last row of the chain (`row_repr`, btype.ml:126-135): one
    /// descriptor load, one `VariantRow` load and one node load a chain
    /// node, then, when the row has a name, one `TypeInfo` load and one
    /// compare of its scope (`get_level`, as for a constructor). No
    /// write when the row has no name or its name's scope is not above
    /// `level`. Otherwise [`Checker::unname_row`]. One step a chain
    /// node. The caller walks the chain a second time for the children
    /// (`Checker::lower_scoped`, in line, as `iter_row`,
    /// btype.ml:229-241): the name decides what `ty` is before its
    /// children are known, and the inner nodes of the chain are not
    /// handed to this function, so a chain of n nodes costs 2n loads
    /// when its first node is lowered and not n squared over two.
    /// (CHECKER_REWRITE 8.6, decisions 75 and 89)
    pub(super) fn lower_row_name(&mut self, ty: Ty, node: Node, level: u32) -> Node {
        let mut current = node;
        let row = loop {
            #[cfg(test)]
            super::steps::tick();
            let ExtraDescriptor::Variant(index) = self.extras.descriptors[current.a as usize]
            else {
                unreachable!("a variant node");
            };
            let row = self.extras.variants[index as usize];
            let more = self.g.repr(self.g.lists[(current.b + row.more) as usize]);
            let next = self.g.nodes[more.0 as usize];
            let variant = next.head & EXTENDED != 0
                && matches!(self.extras.descriptors[next.a as usize], ExtraDescriptor::Variant(_));
            if !variant {
                break row;
            }
            current = next;
        };
        if row.name == NONE || self.types.info(row.name).scope <= level {
            return node;
        }
        self.unname_row(ty, row)
    }

    /// `ty.desc <- Tvariant {row with row_name = None}`, `row` being
    /// `row_repr` of the row of variant node `ty` and `last` the
    /// `VariantRow` its chain ends in: `ty` is written
    /// (`Graph::write`, logged in a speculation, as `log_type ty`) as
    /// one row of every field of its chain, outermost first, each copied
    /// as its row has it with the reference its home has
    /// ([`Checker::flatten_row`], [`Checker::build_variant`]), with the
    /// `more`, `closed` and `fixed` of `last` and no name. The level is
    /// kept. Only `ty` is written: another node whose chain ends in the
    /// same row still reads the name, and the name's arguments are
    /// children of `ty` no longer (they are not lowered through it, as
    /// `iter_row` reads the name of the new descriptor,
    /// btype.ml:229-241). O(fields of the chain): one node, one
    /// descriptor row, one `VariantRow`, one `RowFieldRow` a field; the
    /// node `build_variant` makes is not reachable afterwards.
    #[cold]
    #[inline(never)]
    fn unname_row(&mut self, ty: Ty, last: VariantRow) -> Node {
        let opened = self.open_row(ty);
        let scratch = self.extras.row_scratch.len();
        let (_, more) = self.flatten_row(opened);
        let fields = scratch..self.extras.row_scratch.len();
        let unnamed = VariantRow { name: NONE, name_arguments: Range::default(), ..last };
        let flat = self.build_variant(fields, more, last.closed, last.fixed, (unnamed, 0));
        self.extras.row_scratch.truncate(scratch);
        let written = Node { level: opened.level, ..self.g.nodes[flat.0 as usize] };
        self.g.write(ty, written);
        written
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

    /// `set_more row rest` (compiler/ml/ctype.ml:2597-2619). `rest` is
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
    ///    node is the `row_field` it copies, as its row has it (OCaml puts
    ///    the same value in the new row, `filter_row_fields` keeps `p`):
    ///    absent; present with its type in a slot of its own or with none;
    ///    or `Either` with the row's `c` and `m`, no type slot, and in its
    ///    reference slot **the handle the source home has in that field's
    ///    reference slot** (the two homes then hold one chain, as two rows
    ///    hold one `row_field` in OCaml). Read through the chain it is
    ///    what the source reads now, and it follows a later restore of the
    ///    chain as the source does (`e1 := None`, ctype.ml:2716).
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
        // 1. `filter_row_fields row.row_closed rest` when `closed`, from
        //    the last field to the first; the kept ones move up to the end.
        let mut kept = rest.end;
        for at in rest.clone().rev() {
            #[cfg(test)]
            super::steps::tick();
            let field = self.field_now_at(at);
            let dropped = closed
                && match field.kind {
                    RowFieldKind::Absent => true,
                    RowFieldKind::Either { matched: false, .. } if row.closed => {
                        let holders = self.resolve(field.end, RES_ABSENT, Ty(NONE));
                        self.settle(holders, RES_ABSENT);
                        true
                    }
                    _ => false,
                };
            if !dropped {
                kept -= 1;
                self.extras.row_scratch[kept] = self.extras.row_scratch[at];
            }
        }
        let rest = kept..rest.end;
        // 2. A row that may not gain a tag (ctype.ml:2600-2604).
        if (!rest.is_empty() && (row.closed || fixed)) || (closed && fixed && !row.closed) {
            if self.g.mode == Mode::Explain {
                let t1 = self.trace_row(rest.start..rest.start, true);
                let t2 = self.trace_row(rest, false);
                self.trace.push(if first { [t1, t2] } else { [t2, t1] });
            }
            return Err(Clash);
        }
        // 3. A fixed row (ctype.ml:2609-2612).
        if fixed {
            if more == rm {
                return Ok(None);
            }
            if self.g.nodes[rm.0 as usize].tag() == VAR {
                self.g.link(rm, more);
                return Ok(None);
            }
            return Ok(Some([rm, more]));
        }
        // 4. `let ty = newgenty (Tvariant {row0 with row_fields = rest}) in
        //    update_level !env rm.level ty; link_type rm ty`.
        let level = self.g.nodes[rm.0 as usize].level;
        let ty = self.build_variant(rest, more, closed, name.0.fixed, name);
        if level != GENERIC {
            self.lower(ty, level)?;
        }
        self.g.link(rm, ty);
        Ok(None)
    }

    /// `set_row_field e v` (compiler/ml/btype.ml:742-744) for a `v` that is
    /// not `Reither`: `Graph::write` of the unresolved reference `e` with
    /// a resolved node at `e`'s level: [`RES_ABSENT`]; [`RES_PRESENT`]
    /// with no slot (`ty` is `NONE`: `Rpresent None`) or with one new slot
    /// holding `ty`. Returns the head of the holder list `e` had.
    /// The holders are not touched: [`Checker::settle`] does that once the
    /// resolution stands. O(1); one slot for a type. (R3f)
    pub fn resolve(&mut self, e: Ty, kind: u32, ty: Ty) -> u32 {
        let reference = self.g.nodes[e.0 as usize];
        let b = self.g.lists.len() as u32;
        let arity = if ty.0 == NONE {
            0
        } else {
            self.g.lists.push(ty);
            1
        };
        self.g.write(e, Node { head: TUPLE | arity << 8, level: reference.level, a: kind, b });
        reference.b
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
        let mut at = holders;
        while at != NONE {
            #[cfg(test)]
            super::steps::tick();
            let holder = self.extras.holders[at as usize];
            at = holder.next;
            let node = self.g.nodes[holder.node.0 as usize];
            if node.head & (EXTENDED | 15) != TUPLE || node.a & RES_KIND != RES_EITHER {
                continue;
            }
            let settled = if kind == RES_ABSENT {
                Node { head: TUPLE, a: RES_ABSENT, b: 0, ..node }
            } else {
                Node { head: TUPLE | 1 << 8, a: RES_PRESENT, ..node }
            };
            self.g.write(holder.node, settled);
        }
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
        let reference = self.g.nodes[e.0 as usize];
        let b = self.g.lists.len() as u32;
        let count = types.len() as u32;
        for at in types {
            let ty = self.extras.row_scratch[at].ty;
            self.g.lists.push(ty);
        }
        self.g.lists.push(next);
        self.g.write(
            e,
            Node { head: TUPLE | (count + 1) << 8, level: reference.level, a: flags, b },
        );
        let target = self.g.nodes[next.0 as usize];
        let mut head = target.b;
        let mut at = reference.b;
        while at != NONE {
            #[cfg(test)]
            super::steps::tick();
            let holder = self.extras.holders[at as usize];
            self.extras.holders.push(Holder { node: holder.node, next: head });
            head = self.extras.holders.len() as u32 - 1;
            at = holder.next;
        }
        if count != 0 {
            self.extras.holders.push(Holder { node: e, next: head });
            head = self.extras.holders.len() as u32 - 1;
        }
        self.g.write(next, Node { b: head, ..target });
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
    ///   || c2`; otherwise [`ROW_AGAIN`] is set in the record, the two
    ///   references the arm saw go in a `saved` entry right after it
    ///   (`head`, `level`), and the
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
    ///   record, with the holder list in `a` of a `saved` entry right
    ///   after the record (the `RowFieldEnd` frame keeps the two homes,
    ///   which [`Checker::row_trace_pair`] reads); in
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
    /// universal variable (ctype.ml:2685-2699) is
    /// [`Checker::split_univars`], called by [`Checker::join_either`].
    /// (R3f)
    #[inline(never)]
    pub fn unify_row_field(&mut self, frame: Frame) -> Result<(), [Ty; 2]> {
        const UNIFY: [Ty; 2] = [Ty(NONE), Ty(NONE)];
        let extra = frame.extra as usize;
        let record = self.saved[extra];
        self.frames.push(Frame { kind: FrameKind::RowFieldEnd, ..frame });
        let (fixed1, fixed2) = (record.b & ROW_FIXED1 != 0, record.b & ROW_FIXED2 != 0);
        let (row1, row2) = (
            self.extras.row_fields[record.head as usize],
            self.extras.row_fields[record.level as usize],
        );
        let f1 = field_repr(&self.g, frame.left.0, u32::MAX, row1);
        let f2 = field_repr(&self.g, frame.right.0, u32::MAX, row2);
        let base = self.extras.row_scratch.len();
        let result = match (f1.kind, f2.kind) {
            // `Rpresent (Some t1), Rpresent (Some t2) -> unify env t1 t2`;
            // `Rpresent None, Rpresent None -> ()`.
            (RowFieldKind::Present, RowFieldKind::Present) => match (f1.first.0 == NONE, f2.first.0 == NONE) {
                (false, false) => {
                    self.push_row_pair(f1.first, f2.first);
                    Ok(())
                }
                (true, true) => Ok(()),
                _ => Err(UNIFY),
            },
            (
                RowFieldKind::Either { constant: c1, matched: m1 },
                RowFieldKind::Either { constant: c2, matched: m2 },
            ) => {
                if f1.end == f2.end {
                    Ok(())
                } else if (fixed1 || fixed2) && !(c1 || c2) && f1.types == f2.types {
                    // PR#7496 (ctype.ml:2652-2661): one `Reither (c, [], m,
                    // ref None)` for both, then the types pairwise.
                    let level = self.more_level(record);
                    let e = self.g.push(ref_node(level, NONE));
                    let flags = either_flags(c1 || c2, m1 || m2);
                    self.read_types(frame.left.0, row1);
                    self.read_types(frame.right.0, row2);
                    self.resolve_either(f1.end, flags, base..base, e);
                    self.resolve_either(f2.end, flags, base..base, e);
                    let n = f1.types as usize;
                    for k in (0..n).rev() {
                        let (t1, t2) = (self.extras.row_scratch[base + k].ty, self.extras.row_scratch[base + n + k].ty);
                        self.push_row_pair(t1, t2);
                    }
                    Ok(())
                } else if !self.extras.passive_variants
                    && (m1 || m2 || fixed1 || fixed2
                        || (self.extras.rigid_variants && (f1.types == 1 || f2.types == 1)))
                    && f1.types + f2.types != 0
                {
                    // `redo` (ctype.ml:2663-2675): the first type of `tl1 @
                    // tl2` with each of the others; `row_field_end` reads
                    // the references afterwards.
                    if c1 || c2 {
                        Err(UNIFY)
                    } else {
                        self.saved[extra].b |= ROW_AGAIN;
                        self.saved.push(Node { head: f1.end.0, level: f2.end.0, a: NONE, b: 0 });
                        self.read_types(frame.left.0, row1);
                        self.read_types(frame.right.0, row2);
                        let end = self.extras.row_scratch.len();
                        let t1 = self.extras.row_scratch[base].ty;
                        for at in (base + 1..end).rev() {
                            let t = self.extras.row_scratch[at].ty;
                            self.push_row_pair(t1, t);
                        }
                        Ok(())
                    }
                } else {
                    self.join_either(frame)
                }
            }
            (RowFieldKind::Either { matched: false, .. }, RowFieldKind::Absent) if !fixed1 => {
                let holders = self.resolve(f1.end, RES_ABSENT, Ty(NONE));
                self.settle(holders, RES_ABSENT);
                Ok(())
            }
            (RowFieldKind::Absent, RowFieldKind::Either { matched: false, .. }) if !fixed2 => {
                let holders = self.resolve(f2.end, RES_ABSENT, Ty(NONE));
                self.settle(holders, RES_ABSENT);
                Ok(())
            }
            (RowFieldKind::Absent, RowFieldKind::Absent) => Ok(()),
            (RowFieldKind::Either { constant: false, .. }, RowFieldKind::Present)
                if f2.first.0 != NONE && !fixed1 =>
            {
                self.present_either(extra, record, f1.end, f2.first, frame.left.0, row1, true)
            }
            (RowFieldKind::Present, RowFieldKind::Either { constant: false, .. })
                if f1.first.0 != NONE && !fixed2 =>
            {
                self.present_either(extra, record, f2.end, f1.first, frame.right.0, row2, false)
            }
            // `Reither (true, [], _, e1), Rpresent None when not fixed1`.
            (RowFieldKind::Either { constant: true, .. }, RowFieldKind::Present)
                if f1.types == 0 && f2.first.0 == NONE && !fixed1 =>
            {
                self.resolve(f1.end, RES_PRESENT, Ty(NONE));
                Ok(())
            }
            (RowFieldKind::Present, RowFieldKind::Either { constant: true, .. })
                if f2.types == 0 && f1.first.0 == NONE && !fixed2 =>
            {
                self.resolve(f2.end, RES_PRESENT, Ty(NONE));
                Ok(())
            }
            _ => Err(UNIFY),
        };
        self.extras.row_scratch.truncate(base);
        result
    }

    /// `Reither (false, tl, _, e), Rpresent (Some t)` and its mirror
    /// (compiler/ml/ctype.ml:2711-2724): `e` resolved to present with `t`,
    /// `t` lowered to the level of `more`'s representative, the holders
    /// kept for [`Checker::row_field_end`] in a `saved` entry after the
    /// record, in `Mode::Explain` a `Fields` frame that puts `e` back
    /// (`e1 := None`), then the pairs of `t` with each type of the
    /// `Reither` side (`(t1, t2)` when it is the left side, else `(t2,
    /// t1)`), the first popped first. O(types) plus the lowering.
    #[allow(clippy::too_many_arguments)]
    fn present_either(
        &mut self,
        extra: usize,
        record: Node,
        e: Ty,
        t: Ty,
        home: u32,
        field: RowFieldRow,
        left: bool,
    ) -> Result<(), [Ty; 2]> {
        let unresolved = self.g.nodes[e.0 as usize];
        let holders = self.resolve(e, RES_PRESENT, t);
        let level = self.more_level(record);
        if level != GENERIC && self.lower(t, level).is_err() {
            return Err([Ty(NONE), Ty(NONE)]);
        }
        self.saved[extra].b |= ROW_SETTLE;
        self.saved.push(Node { head: NONE, level: NONE, a: holders, b: 0 });
        if self.g.mode == Mode::Explain {
            let slot = self.saved.len() as u32;
            self.saved.push(unresolved);
            self.saved.push(unresolved);
            self.frames.push(Frame { left: e, right: e, kind: FrameKind::Fields, extra: slot });
        }
        let base = self.extras.row_scratch.len();
        self.read_types(home, field);
        for at in (base..self.extras.row_scratch.len()).rev() {
            let other = self.extras.row_scratch[at].ty;
            if left {
                self.push_row_pair(other, t);
            } else {
                self.push_row_pair(t, other);
            }
        }
        Ok(())
    }

    /// O(1): push the pair `(left, right)` for `run_frames` to unify.
    #[inline]
    fn push_row_pair(&mut self, left: Ty, right: Ty) {
        self.frames.push(Frame { left, right, kind: FrameKind::Pair, extra: 0 });
    }

    /// O(links): the level of the representative of a record's `more`
    /// (`(repr more).level`).
    fn more_level(&mut self, record: Node) -> u32 {
        let more = self.g.repr(Ty(record.a));
        self.g.nodes[more.0 as usize].level
    }

    /// The types of `field` of the opened home at list index `home`, in
    /// OCaml's order ([`each_field_types`]), appended to
    /// `extras.row_scratch` as the `ty` of a [`FieldRef`]. O(types +
    /// chain), no allocation once the scratch has the capacity.
    fn read_types(&mut self, home: u32, field: RowFieldRow) {
        let scratch = &mut self.extras.row_scratch;
        each_field_types(&self.g, home, u32::MAX, field, |types| {
            scratch.extend(types.iter().map(|&ty| FieldRef { name: 0, at: 0, ty }));
        });
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
        let record = self.saved[frame.extra as usize];
        let (row1, row2) = (
            self.extras.row_fields[record.head as usize],
            self.extras.row_fields[record.level as usize],
        );
        let f1 = field_repr(&self.g, frame.left.0, u32::MAX, row1);
        let f2 = field_repr(&self.g, frame.right.0, u32::MAX, row2);
        let (
            RowFieldKind::Either { constant: c1, matched: m1 },
            RowFieldKind::Either { constant: c2, matched: m2 },
        ) = (f1.kind, f2.kind)
        else {
            unreachable!("two `Reither` fields");
        };
        // `List.map repr tl1` and `tl2`, then `tl1'` (what row 1 gains:
        // `remq tl1 tl2`) and `tl2'` (`remq tl2 tl1`).
        let base = self.extras.row_scratch.len();
        self.read_types(frame.left.0, row1);
        let middle = self.extras.row_scratch.len();
        self.read_types(frame.right.0, row2);
        let end = self.extras.row_scratch.len();
        for at in base..end {
            let ty = self.g.repr(self.extras.row_scratch[at].ty);
            self.extras.row_scratch[at].ty = ty;
        }
        let missing = |c: &mut Checker, from: std::ops::Range<usize>, against: std::ops::Range<usize>| {
            for at in from {
                let ty = c.extras.row_scratch[at];
                if !c.extras.row_scratch[against.clone()].iter().any(|other| other.ty == ty.ty) {
                    c.extras.row_scratch.push(ty);
                }
            }
        };
        // The second run, after the types that hold a universal variable
        // were unified: `tl1'` and `tl2'` are the lists the first run kept
        // (`let tl1', tlu1 = split_univars tl1'`, computed BEFORE `List.iter
        // (unify env tu1) (tlu1 @ tlu2)`, ctype.ml:2685-2697), read back
        // from `saved` after the record ([`Checker::split_univars`]), not
        // the two lists compared again: a type those unifications made
        // the same node as one the side already has is still gained
        // (CHECKER_REWRITE 8.6, decision 58).
        let (gained1, gained2) = if record.b & ROW_UNIVARS != 0 {
            let counts = self.saved[frame.extra as usize + 1];
            let first = frame.extra as usize + 2;
            for at in first..first + (counts.head + counts.level) as usize {
                let ty = Ty(self.saved[at].head);
                self.extras
                    .row_scratch
                    .push(FieldRef { name: 0, at: 0, ty });
            }
            (
                end..end + counts.head as usize,
                end + counts.head as usize..self.extras.row_scratch.len(),
            )
        } else {
            missing(self, middle..end, base..middle);
            let gained1 = end..self.extras.row_scratch.len();
            missing(self, base..middle, middle..end);
            (gained1.clone(), gained1.end..self.extras.row_scratch.len())
        };
        // PR#6744 (ctype.ml:2685-2699), on one load when the graph has no
        // universal variable; not on the second run.
        let (gained1, gained2) = if self.extras.univars != 0 && record.b & ROW_UNIVARS == 0 {
            match self.split_univars(frame, [gained1, gained2]) {
                Ok(Some([gained1, gained2])) => (gained1, gained2),
                Ok(None) => {
                    self.extras.row_scratch.truncate(base);
                    return Ok(());
                }
                Err(clash) => {
                    self.extras.row_scratch.truncate(base);
                    return Err(clash);
                }
            }
        } else {
            (gained1, gained2)
        };
        // `List.iter (update_level !env (repr more).level) (tl1' @ tl2')`:
        // each range on its own. After the split the two need not be
        // adjacent, and what lies between them is what its compaction
        // left behind, which can be a type that holds a universal
        // variable and that OCaml does not lower.
        let level = self.more_level(record);
        if level != GENERIC {
            for at in gained1.clone().chain(gained2.clone()) {
                let ty = self.extras.row_scratch[at].ty;
                if self.lower(ty, level).is_err() {
                    self.extras.row_scratch.truncate(base);
                    return Err([Ty(NONE), Ty(NONE)]);
                }
            }
        }
        let e = self.g.push(ref_node(level, NONE));
        let flags = either_flags(c1 || c2, m1 || m2);
        self.resolve_either(f1.end, flags, gained1, e);
        self.resolve_either(f2.end, flags, gained2, e);
        self.extras.row_scratch.truncate(base);
        Ok(())
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
    #[inline(never)]
    pub fn row_field_end(&mut self, frame: Frame) -> Result<(), [Ty; 2]> {
        let extra = frame.extra as usize;
        let record = self.saved[extra];
        if record.b & ROW_AGAIN != 0 {
            // `!e1 <> None || !e2 <> None` (ctype.ml:2674): the ends the
            // arm saw, after the record.
            let ends = self.saved[extra + 1];
            let still = |c: &Checker, home: Ty, field: u32, end: u32| {
                let field = field_repr(&c.g, home.0, u32::MAX, c.extras.row_fields[field as usize]);
                matches!(field.kind, RowFieldKind::Either { .. }) && field.end.0 == end
            };
            let unresolved = still(self, frame.left, record.head, ends.head)
                && still(self, frame.right, record.level, ends.level);
            self.saved.truncate(extra + 1);
            self.saved[extra].b &= !ROW_AGAIN;
            if !unresolved {
                self.frames.push(Frame { kind: FrameKind::RowField, ..frame });
                return Ok(());
            }
            self.join_either(frame)?;
            // The join pushed the pairs of the types that hold a universal
            // variable ([`ROW_UNIVARS`], set just now): the record stays
            // for the `RowFieldEnd` frame below them.
            if self.saved[extra].b & ROW_UNIVARS != 0 {
                return Ok(());
            }
        } else if record.b & ROW_UNIVARS != 0 {
            // Those pairs are unified: the join again, without the split.
            self.join_either(frame)?;
        } else if record.b & ROW_SETTLE != 0 {
            let holders = self.saved[extra + 1].a;
            self.settle(holders, RES_PRESENT);
        }
        self.saved.truncate(extra);
        Ok(())
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
    #[inline(never)]
    pub fn row_end(&mut self, frame: Frame) {
        let top = self.g.repr(frame.left);
        let node = self.open_row(top);
        let variant = node.head & EXTENDED != 0
            && matches!(self.extras.descriptors[node.a as usize], ExtraDescriptor::Variant(_));
        if !variant {
            return;
        }
        let base = self.extras.row_scratch.len();
        let (_, more) = self.flatten_row(node);
        let end = self.extras.row_scratch.len();
        let static_row = (base..end).all(|at| !matches!(self.field_now_at(at).kind, RowFieldKind::Either { .. }));
        self.extras.row_scratch.truncate(base);
        let rest = self.g.nodes[more.0 as usize];
        if static_row && rest.tag() == VAR {
            // `link_type rm (newty2 rm.level Tnil)`.
            let nil = self.extras.descriptors.len() as u32;
            self.extras.descriptors.push(ExtraDescriptor::Nil);
            let b = self.g.lists.len() as u32;
            let tnil = self.g.push(Node { head: TUPLE | EXTENDED, level: rest.level, a: nil, b });
            self.g.link(more, tnil);
        }
    }

    /// `mkvariant fields closed` (compiler/ml/ctype.ml:1704-1713) for a
    /// trace: a new variant node at the generic level whose fields are
    /// `extras.row_scratch[fields]` as [`Checker::set_more`] copies a
    /// field, whose `more` is a new variable at the current level, not
    /// fixed, with no name. Failure path of `Mode::Explain` only. (R3f)
    pub fn trace_row(&mut self, fields: std::ops::Range<usize>, closed: bool) -> Ty {
        let more = self.g.push(Node { head: VAR, level: self.g.level, a: NONE, b: 0 });
        let unnamed = VariantRow {
            fields: Range::default(),
            more: 0,
            name: NONE,
            name_arguments: Range::default(),
            closed,
            fixed: false,
        };
        self.build_variant(fields, more, closed, false, (unnamed, 0))
    }

    /// The trace pair of a common tag whose fields clashed
    /// (`(mkvariant [(l, f1)] true, mkvariant [(l, f2)] true) :: trace`,
    /// compiler/ml/ctype.ml:2624-2628), from a [`FrameKind::RowFieldEnd`]
    /// frame: two [`Checker::trace_row`] of one field each, closed.
    /// Failure path of `Mode::Explain` only. (R3f)
    pub fn row_trace_pair(&mut self, frame: Frame) -> [Ty; 2] {
        let record = self.saved[frame.extra as usize];
        let base = self.extras.row_scratch.len();
        for (at, home) in [(record.head, frame.left), (record.level, frame.right)] {
            let name = self.extras.row_fields[at as usize].name;
            self.extras.row_scratch.push(FieldRef { name, at, ty: home });
        }
        let t1 = self.trace_row(base..base + 1, true);
        let t2 = self.trace_row(base + 1..base + 2, true);
        self.extras.row_scratch.truncate(base);
        [t1, t2]
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
    ///   ([`Checker::open_row`], then one store of the level of each
    ///   reference it made: a fresh node), so that every later copy shares
    ///   them;
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
        let ExtraDescriptor::Variant(row) = self.extras.descriptors[node.a as usize] else {
            unreachable!("a variant node");
        };
        let row = self.extras.variants[row as usize];
        let fields = row.fields.start..row.fields.start + row.fields.len;
        let either = |field: &&RowFieldRow| matches!(field.kind, RowFieldKind::Either { .. });
        let rows = &self.extras.row_fields[fields.start as usize..fields.end as usize];
        let Some(published) = rows.iter().find(either).map(|field| field.link) else {
            return;
        };
        // `more = repr row.row_more` of the flattened row (ctype.ml:803),
        // read in the copy: a generic `more` is one this session copied.
        let mut more = self.g.repr(self.g.lists[(node.b + row.more) as usize]);
        // `row.row_fixed` of the flattened row is the flag of the last
        // variant node on the way to `more` (btype.ml:126-135).
        let mut fixed = row.fixed;
        while let next = self.g.nodes[more.0 as usize]
            && next.head & EXTENDED != 0
            && let ExtraDescriptor::Variant(next_row) = self.extras.descriptors[next.a as usize]
        {
            let next_row = self.extras.variants[next_row as usize];
            fixed = next_row.fixed;
            more = self.g.repr(self.g.lists[(next.b + next_row.more) as usize]);
        }
        // `| {desc = Tconstr _} when not row.row_fixed -> {row with
        // row_fixed = true}` (PR#6163, ctype.ml:826-830): a row over a
        // constructor is copied as a fixed one.
        fixed |= self.g.nodes[more.0 as usize].tag() == CONSTR;
        // `let keep = more.level <> generic_level` (ctype.ml:813).
        let keep = more.0 < first;
        let source = self.g.work[(copy.0 - first) as usize];
        if published >= self.g.nodes[source.0 as usize].arity() {
            if keep {
                let level = self.g.nodes[more.0 as usize].level;
                self.open_shared([copy, source], node, level, published, fields);
            }
            // `let m = if row.row_fixed then fixed else m` (btype.ml:375,
            // with `fixed = true` from `Ctype.copy`, ctype.ml:868).
            if fixed {
                self.match_fixed_fields(copy, first);
            }
            return;
        }
        let generation = self.mark_generation;
        let end = first + self.g.work.len() as u32;
        for index in fields {
            #[cfg(test)]
            super::steps::tick();
            let field = self.extras.row_fields[index as usize];
            if !matches!(field.kind, RowFieldKind::Either { .. }) {
                continue;
            }
            let last = field_repr(&self.g, node.b, node.arity(), field).end;
            if last.0 == NONE {
                continue;
            }
            let mut slot = node.b + field.link;
            if keep {
                // `e` of the copy is the source's (btype.ml:374): the end
                // the session copied is pointed back at its source.
                let target = if last.0 >= first && last.0 < end {
                    self.g.work[(last.0 - first) as usize]
                } else {
                    last
                };
                loop {
                    let at = self.g.lists[slot as usize];
                    if at == last {
                        self.g.lists[slot as usize] = target;
                        break;
                    }
                    if at.0 < first || at.0 >= end || self.marks[at.0 as usize] == generation {
                        break;
                    }
                    self.marks[at.0 as usize] = generation;
                    let chain = self.g.nodes[at.0 as usize];
                    let added = chain.arity() - 1;
                    if added != 0 {
                        self.hold(at, target);
                    }
                    slot = chain.b + added;
                }
            } else {
                // `ref None` (btype.ml:374): a chain of the field's own.
                let mut head = NONE;
                loop {
                    let mut at = self.g.lists[slot as usize];
                    if at == last {
                        break;
                    }
                    let mut chain = self.g.nodes[at.0 as usize];
                    // Not the session's, or taken by a field before: copied.
                    let shared = at.0 < first || at.0 >= end || self.marks[at.0 as usize] == generation;
                    if shared {
                        let start = self.g.lists.len() as u32;
                        self.g.lists.extend_from_within(chain.b as usize..(chain.b + chain.arity()) as usize);
                        chain.b = start;
                        at = self.g.push(chain);
                        self.g.lists[slot as usize] = at;
                        if slot == node.b + field.link {
                            let own = node.b + field.types.start;
                            self.g.lists[own as usize..(own + field.types.len) as usize].fill(at);
                        }
                    } else {
                        self.marks[at.0 as usize] = generation;
                    }
                    let added = chain.arity() - 1;
                    if added != 0 {
                        self.extras.holders.push(Holder { node: at, next: head });
                        head = self.extras.holders.len() as u32 - 1;
                    }
                    slot = chain.b + added;
                }
                self.g.lists[slot as usize] = self.g.push(ref_node(self.g.level, head));
            }
        }
        if fixed {
            self.match_fixed_fields(copy, first);
        }
    }

    /// The fixed-row rule of a copy (`let m = if row.row_fixed then fixed
    /// else m`, compiler/ml/btype.ml:375, with `fixed = true` from
    /// `Ctype.copy`, ctype.ml:868): every `Reither` field of `copy`, the
    /// copy of a variant node whose flattened row is fixed, reads
    /// matched. Called by [`Checker::copy_refs`] for such a copy, after
    /// its references are in place. One [`field_repr`] per `Reither`
    /// field; a field that reads matched already costs nothing more, and
    /// the first one that does not hands the node to
    /// [`Checker::match_unmatched`]. A row from a declaration or an
    /// annotation has matched fields when it is fixed
    /// (`make_fixed_univars`, typetexp.ml:684-696); the rows `reify`
    /// fixes do not (CHECKER_REWRITE 8.6, decision 47). O(fields of the
    /// node + their chains), one step a field.
    fn match_fixed_fields(&mut self, copy: Ty, first: u32) {
        let node = self.g.nodes[copy.0 as usize];
        let ExtraDescriptor::Variant(row) = self.extras.descriptors[node.a as usize] else {
            unreachable!("a variant node");
        };
        let row = self.extras.variants[row as usize];
        for index in row.fields.start..row.fields.start + row.fields.len {
            #[cfg(test)]
            super::steps::tick();
            let field = self.extras.row_fields[index as usize];
            let now = field_repr(&self.g, node.b, node.arity(), field);
            if matches!(now.kind, RowFieldKind::Either { matched: false, .. }) {
                return self.match_unmatched(copy, first);
            }
        }
    }

    /// [`Checker::match_fixed_fields`] for a copy that has a `Reither`
    /// field which reads unmatched. The copy is opened
    /// ([`Checker::open_fresh`]: an unopened copy reads `m` from the
    /// shared `RowFieldRow`, which is not written; the store is not
    /// logged, since the copy may be [`Checker::duplicate`]'s). Then, per `Reither` field
    /// whose chain ends unresolved and reads unmatched ([`field_repr`]
    /// gives the flags of the LAST [`RES_EITHER`] node of the chain):
    /// - the chain has such a node and the session made it (its handle is
    ///   at or above `first`): [`RES_MATCHED`] is set in its `a`, a plain
    ///   store on a fresh node;
    /// - the chain has none (a field without types, whose slot names the
    ///   reference itself): a new [`RES_EITHER`] node at the copy's level
    ///   with the field's `c`, [`RES_MATCHED`], no type and the reference
    ///   as its one slot goes into the field's reference slot;
    /// - the last such node is not the session's (the copy shares it with
    ///   its source): it is copied as [`Checker::copy_refs`] copies a
    ///   shared chain node (one node, the same slots in a new list, the
    ///   slot that named it pointed at the copy, a holder of the
    ///   reference when it has types), with [`RES_MATCHED`]. When the
    ///   node before it is not the session's either, the chain is copied
    ///   so from the first node that is not, so that no slot of the
    ///   source's chain is written (`copy_row` makes the copy's field a
    ///   new value, btype.ml:373-377). A holder of a reference the
    ///   session made is a plain store ([`Checker::hold_in_copy`]).
    ///
    /// The source's field keeps its `m`: the two share the reference
    /// (`e`), not the flags (`Reither (c, tl, m, e)` is a new value,
    /// btype.ml:373-377). O(fields of the node + their chains); per field
    /// changed at most one node and its slots. (R3h; CHECKER_REWRITE 8.6,
    /// decision 47)
    #[cold]
    #[inline(never)]
    fn match_unmatched(&mut self, copy: Ty, first: u32) {
        let node = self.open_fresh(copy);
        let ExtraDescriptor::Variant(row) = self.extras.descriptors[node.a as usize] else {
            unreachable!("a variant node");
        };
        let row = self.extras.variants[row as usize];
        for index in row.fields.start..row.fields.start + row.fields.len {
            #[cfg(test)]
            super::steps::tick();
            let field = self.extras.row_fields[index as usize];
            let now = field_repr(&self.g, node.b, node.arity(), field);
            let RowFieldKind::Either { constant, matched: false } = now.kind else {
                continue;
            };
            // Every node of the chain before its end is a `RES_EITHER`
            // node (`field_repr` read `Either`): the last one names the
            // end. `shared` is the slot that names the first node that is
            // not the session's; every node after it is reached through
            // it and is not the session's either.
            let (end, link) = (now.end, node.b + field.link);
            let (mut slot, mut last, mut shared) = (link, None, None);
            while let at = self.g.lists[slot as usize]
                && at != end
            {
                if shared.is_none() && at.0 < first {
                    shared = Some(slot);
                }
                last = Some(at);
                let chain = self.g.nodes[at.0 as usize];
                slot = chain.b + chain.arity() - 1;
            }
            match (last, shared) {
                // A field without types: a matched node of its own.
                (None, _) => {
                    let b = self.g.lists.len() as u32;
                    self.g.lists.push(end);
                    let own = self.g.push(Node {
                        head: TUPLE | 1 << 8,
                        level: node.level,
                        a: either_flags(constant, true),
                        b,
                    });
                    self.g.lists[link as usize] = own;
                }
                (Some(at), None) => self.g.nodes[at.0 as usize].a |= RES_MATCHED,
                // The source's part of the chain is copied, node by node,
                // the last one matched; the source's field keeps its `m`.
                (Some(last), Some(mut slot)) => loop {
                    let at = self.g.lists[slot as usize];
                    let mut chain = self.g.nodes[at.0 as usize];
                    let start = self.g.lists.len() as u32;
                    self.g
                        .lists
                        .extend_from_within(chain.b as usize..(chain.b + chain.arity()) as usize);
                    chain.b = start;
                    if at == last {
                        chain.a |= RES_MATCHED;
                    }
                    let own = self.g.push(chain);
                    self.g.lists[slot as usize] = own;
                    if slot == link {
                        let types = node.b + field.types.start;
                        self.g.lists[types as usize..(types + field.types.len) as usize].fill(own);
                    }
                    if chain.arity() > 1 {
                        self.hold_in_copy(own, end, first);
                    }
                    if at == last {
                        break;
                    }
                    slot = chain.b + chain.arity() - 1;
                },
            }
        }
    }

    /// O(1): [`Checker::hold`] for a chain node of a copy whose session
    /// starts at `first`: a reference the session made is fresh and
    /// written with a plain store, so that the restore of
    /// [`Checker::duplicate`] leaves the copy as it is; an older one is
    /// logged as `hold` logs it.
    fn hold_in_copy(&mut self, chain: Ty, reference: Ty, first: u32) {
        if reference.0 < first {
            return self.hold(chain, reference);
        }
        let holders = &mut self.g.nodes[reference.0 as usize].b;
        self.extras.holders.push(Holder { node: chain, next: *holders });
        *holders = self.extras.holders.len() as u32 - 1;
    }

    /// O(1): make chain node `chain` a holder of the unresolved reference
    /// `reference`: one 8-byte [`Holder`] row and one logged write of the
    /// reference's `b`.
    fn hold(&mut self, chain: Ty, reference: Ty) {
        let mut node = self.g.nodes[reference.0 as usize];
        self.extras.holders.push(Holder { node: chain, next: node.b });
        node.b = self.extras.holders.len() as u32 - 1;
        self.g.write(reference, node);
    }

    /// The second case of [`Checker::copy_refs`]: open `source`, give the
    /// references it made the `level` of the shared row variable, and open
    /// `copy` (the unopened `node`, of the same row) onto them: as
    /// [`Checker::open_row`] does, but each field's end is the source's.
    /// The source's references and the copy are fresh or the session's:
    /// plain stores. `published` is the row's count of published slots.
    /// O(slots of the node); the steps are `open_row`'s, one a field. Per
    /// `Reither` field with types one node, `types + 1` slots and one
    /// holder; nothing per field without.
    fn open_shared(&mut self, [copy, source]: [Ty; 2], node: Node, level: u32, published: u32, fields: std::ops::Range<u32>) {
        let opened = self.open_row(source);
        let (b, arity) = (self.g.lists.len() as u32, opened.arity());
        self.g.lists.extend_from_within(node.b as usize..(node.b + published) as usize);
        self.g.lists.resize((b + arity) as usize, Ty(NONE));
        for index in fields {
            let field = self.extras.row_fields[index as usize];
            let RowFieldKind::Either { constant, matched } = field.kind else {
                continue;
            };
            let types = field.types;
            let mut reference = self.g.lists[(opened.b + field.link) as usize];
            if types.len != 0 {
                reference = self.g.lists[(self.g.nodes[reference.0 as usize].b + types.len) as usize];
            }
            self.g.nodes[reference.0 as usize].level = level;
            let mut slot = reference;
            if types.len != 0 {
                let start = self.g.lists.len() as u32;
                let own = (b + types.start) as usize..(b + types.start + types.len) as usize;
                self.g.lists.extend_from_within(own.clone());
                self.g.lists.push(reference);
                slot = self.g.push(Node {
                    head: TUPLE | (types.len + 1) << 8,
                    level: node.level,
                    a: either_flags(constant, matched),
                    b: start,
                });
                let holders = &mut self.g.nodes[reference.0 as usize].b;
                self.extras.holders.push(Holder { node: slot, next: *holders });
                *holders = self.extras.holders.len() as u32 - 1;
                self.g.lists[own].fill(slot);
            }
            self.g.lists[(b + field.link) as usize] = slot;
        }
        self.g.nodes[copy.0 as usize] = Node { head: (node.head & 0xff) | arity << 8, b, ..node };
    }

    /// O(1): whether the node `ty` (a representative) is a universal
    /// variable (`is_Tunivar`, compiler/ml/btype.ml:53-55). One node load
    /// and, for an extended node, one descriptor load.
    #[inline]
    pub fn is_univar(&self, ty: Ty) -> bool {
        let node = self.g.nodes[ty.0 as usize];
        node.head & EXTENDED != 0
            && matches!(
                self.extras.descriptors[node.a as usize],
                ExtraDescriptor::Univar(_)
            )
    }

    /// `unify_univar t1 t2 !univar_pairs` (compiler/ml/ctype.ml:1544-1559)
    /// for two distinct representatives that are universal variables: `Ok`
    /// when the innermost scope that holds either pairs them, a clash
    /// otherwise. It links nothing: the caller does
    /// ([`Checker::unify_pair`], `unify3`).
    ///
    /// The scopes of [`Checker::scopes`] from the last (innermost) to the
    /// first; each scope twice, as OCaml's two entries `(cl1, cl2) ::
    /// (cl2, cl1)`: first with `a` its left list and `b` its right list,
    /// then with `a` its right list and `b` its left one. For one entry:
    /// `i` is the first position in `a` whose slot's representative is
    /// `t1` and `j` the first in `b` whose slot's representative is `t2`
    /// (`find_univ`: `t == repr t'`, ctype.ml:1546-1551), each a scan of
    /// the whole list.
    /// - Both found. When the partner node of `a[i]` holds a handle whose
    ///   representative is `t2`: `Ok` (ctype.ml:1553). When both partner
    ///   nodes hold `NONE`: `Graph::write` of the partner node of `a[i]`
    ///   to [`partner_node`]`(t2)` and of that of `b[j]` to
    ///   `partner_node(t1)`, `Ok` (`set_univar r1 t2; set_univar r2 t1`,
    ///   ctype.ml:1554-1556). Otherwise a clash (ctype.ml:1558).
    /// - Neither found: the next entry (ctype.ml:1557).
    /// - One found: a clash (ctype.ml:1558).
    ///
    /// No entry left: a clash (`[] -> raise (Unify [])`, ctype.ml:1559).
    /// A clash pushes nothing on the trace. The partner node of position
    /// `i` of the left list is `scope.partners + i`, of position `j` of
    /// the right list `scope.partners + scope.left_len + j`.
    /// O(scopes × bound variables): one step and one `repr` per slot
    /// compared, at most `2 × (left_len + right_len)` a scope; no
    /// allocation. (R3g)
    #[inline(never)]
    pub fn unify_univar(&mut self, t1: Ty, t2: Ty) -> Result<(), Clash> {
        for at in (0..self.scopes.len()).rev() {
            let scope = self.scopes[at];
            // `(cl1, cl2)`, then `(cl2, cl1)`: each list with the first
            // partner node of its own positions.
            let left = (scope.left, scope.left_len, scope.partners.0);
            let right = (scope.right, scope.right_len, scope.partners.0 + scope.left_len);
            for (a, b) in [(left, right), (right, left)] {
                match (self.find_univ(t1, a), self.find_univ(t2, b)) {
                    (Some(r1), Some(r2)) => {
                        let (p1, p2) = (self.g.nodes[r1.0 as usize].a, self.g.nodes[r2.0 as usize].a);
                        // `Some {contents = Some t'2}, Some _ when t2 == repr
                        // t'2 -> ()`.
                        if p1 != NONE && self.g.repr(Ty(p1)) == t2 {
                            return Ok(());
                        }
                        // `Some ({contents = None} as r1), Some ({contents =
                        // None} as r2) -> set_univar r1 t2; set_univar r2 t1`.
                        if p1 == NONE && p2 == NONE {
                            self.g.write(r1, partner_node(t2));
                            self.g.write(r2, partner_node(t1));
                            return Ok(());
                        }
                        return Err(Clash);
                    }
                    (None, None) => {}
                    _ => return Err(Clash),
                }
            }
        }
        Err(Clash)
    }

    /// `find_univ t cl` of [`Checker::unify_univar`] (compiler/ml/ctype.ml:
    /// 1546-1551): the partner node of the first slot of the binder list
    /// `(start, len, partners)` whose representative is `t`, or `None`.
    /// O(len): one step and one `repr` a slot read; no allocation.
    #[inline]
    fn find_univ(&mut self, t: Ty, (start, len, partners): (u32, u32, u32)) -> Option<Ty> {
        for i in 0..len {
            #[cfg(test)]
            super::steps::tick();
            if self.g.repr(self.g.lists[(start + i) as usize]) == t {
                return Some(Ty(partners + i));
            }
        }
        None
    }

    /// `enter_poly env univar_pairs t1 tl1 t2 tl2 (unify env)`
    /// (compiler/ml/ctype.ml:1656-1679) for two polymorphic types that
    /// have a bound variable, after the link of unify3: `left` and
    /// `right` are the descriptors the two nodes had (the left node is a
    /// link by now, so both types are read from their descriptors: body
    /// in slot 0, bound variables in the slots after it).
    ///
    /// 1. When a scope is open: one fresh generation of marks; the
    ///    representative of every bound-variable slot of every open scope,
    ///    both lists, is marked (`known_univars`, ctype.ml:1658-1662).
    ///    `known1`: some bound variable of `left` (its representative) is
    ///    marked; `known2` the same for `right`. Both are read before
    ///    step 2, which takes marks of its own.
    /// 2. The escape test, BEFORE anything is pushed (ctype.ml:1664-1669;
    ///    CHECKER_REWRITE 8.6, decision 49): `known1 &&`
    ///    [`Checker::univars_escape`]`(left, right)`, or else `known2 &&
    ///    univars_escape(right, left)`: a clash, with nothing on the
    ///    trace (`raise (Unify [])`) and nothing pushed. With no scope
    ///    open neither can hold and nothing of steps 1 and 2 runs.
    /// 3. `left_len + right_len` new partner nodes
    ///    ([`partner_node`]`(Ty(NONE))`, consecutive handles), and a
    ///    [`PolyScope`] pushed on [`Checker::scopes`]
    ///    (`univar_pairs := (cl1, cl2) :: (cl2, cl1) :: old_univars`).
    /// 4. A [`FrameKind::LeavePoly`] frame whose `extra` is the number of
    ///    scopes before step 3, then the pair of the two bodies above it
    ///    (`f t1 t2`), so that the scope is left when the bodies are
    ///    unified.
    ///
    /// Like [`Checker::push_children`], it pushes nothing when it fails.
    /// Cost: with no scope open, `left_len + right_len` nodes of 16 bytes,
    /// one 20-byte scope and two frames; with `s` scopes open that hold
    /// `B` bound variables in all, one step per slot marked or tested
    /// (`B + left_len + right_len`), and the escape walk only when a bound
    /// variable is already known. OCaml rebuilds `known_univars` at every
    /// entry too. (R3g)
    #[inline(never)]
    pub fn enter_poly(&mut self, left: Node, right: Node) -> Result<(), Clash> {
        let (left_len, right_len) = (left.arity() - 1, right.arity() - 1);
        let base = self.scopes.len();
        if base != 0 {
            // `known_univars` (ctype.ml:1658-1662).
            let known = self.fresh_marks();
            for at in 0..base {
                let scope = self.scopes[at];
                self.mark_slots(scope.left, scope.left_len, known);
                self.mark_slots(scope.right, scope.right_len, known);
            }
            let known1 = self.any_marked(left.b + 1, left_len, known);
            let known2 = self.any_marked(right.b + 1, right_len, known);
            // `raise (Unify [])`, before anything is pushed (ctype.ml:
            // 1664-1669).
            if known1 && self.univars_escape(left, right) || known2 && self.univars_escape(right, left) {
                return Err(Clash);
            }
        }
        // `let cl1 = List.map (fun t -> (t, ref None)) tl1 and cl2 = ...`;
        // `univar_pairs := (cl1, cl2) :: (cl2, cl1) :: old_univars`.
        let partners = Ty(self.g.nodes.len() as u32);
        for _ in 0..left_len + right_len {
            self.g.push(partner_node(Ty(NONE)));
        }
        self.scopes.push(PolyScope {
            left: left.b + 1,
            right: right.b + 1,
            left_len,
            right_len,
            partners,
        });
        // `f t1 t2`, then `univar_pairs := old_univars` (ctype.ml:
        // 1673-1676).
        self.frames.push(Frame { left: Ty(NONE), right: Ty(NONE), kind: FrameKind::LeavePoly, extra: base as u32 });
        let (body1, body2) = (self.g.lists[left.b as usize], self.g.lists[right.b as usize]);
        self.push_row_pair(body1, body2);
        Ok(())
    }

    /// O(len): mark the representative of each of the `len` slots from
    /// list index `start` with `generation`; one step a slot read.
    fn mark_slots(&mut self, start: u32, len: u32, generation: u32) {
        for i in 0..len {
            #[cfg(test)]
            super::steps::tick();
            let ty = self.g.repr(self.g.lists[(start + i) as usize]);
            self.marks[ty.0 as usize] = generation;
        }
    }

    /// O(len): whether the representative of one of the `len` slots from
    /// list index `start` is marked with `generation`; one step a slot
    /// read, stopping at the first.
    fn any_marked(&mut self, start: u32, len: u32, generation: u32) -> bool {
        (0..len).any(|i| {
            #[cfg(test)]
            super::steps::tick();
            let ty = self.g.repr(self.g.lists[(start + i) as usize]);
            self.marks[ty.0 as usize] == generation
        })
    }

    /// `univars_escape env old_univars tl (newty (Tpoly (t, tl')))`
    /// (compiler/ml/ctype.ml:1610-1653): whether a universal variable of
    /// the family of `binder`'s bound variables occurs in the polymorphic
    /// type `other` outside a binder of the family. `binder` and `other`
    /// are descriptors of polymorphic types; the scopes are those open
    /// now (the caller has not pushed its own).
    ///
    /// The family (`get_univar_family`, ctype.ml:1612-1623), as one
    /// generation of marks on the representatives: the bound variables of
    /// `binder`; then one pass over the scopes from the innermost to the
    /// outermost, each scope twice (left list as `cl1` and right as
    /// `cl2`, then the other way round): when `cl2` is not empty and some
    /// slot of `cl1` is marked, every slot of `cl2` is marked. One pass,
    /// not a closure.
    ///
    /// The walk (`occur`, ctype.ml:1630-1648), with a second generation
    /// for the nodes visited, on `g.work`, starting as for a polymorphic
    /// node with `other`'s slots: a universal variable in the family is
    /// an escape (`true`, the work list cleared); a polymorphic type one
    /// of whose bound variables is in the family is not entered, any
    /// other is entered through its body only (slot 0); a constructor
    /// without arguments is a leaf; a constructor with arguments pushes
    /// the arguments [`TypeTable::may_occur`] allows; any other node
    /// pushes every child (`Graph::children`). A universal variable is
    /// tested and not marked as visited (the two generations share one
    /// table). O(bound variables of the open scopes + nodes of `other`),
    /// one step a slot of the family pass and one a node visited; no
    /// allocation. (R3g)
    #[inline(never)]
    pub fn univars_escape(&mut self, binder: Node, other: Node) -> bool {
        // `get_univar_family` (ctype.ml:1612-1623).
        let family = self.fresh_marks();
        self.mark_slots(binder.b + 1, binder.arity() - 1, family);
        for at in (0..self.scopes.len()).rev() {
            let scope = self.scopes[at];
            let left = (scope.left, scope.left_len);
            let right = (scope.right, scope.right_len);
            for ((start1, len1), (start2, len2)) in [(left, right), (right, left)] {
                if len2 != 0 && self.any_marked(start1, len1, family) {
                    self.mark_slots(start2, len2, family);
                }
            }
        }
        // `occur (newty (Tpoly (t, tl')))` (ctype.ml:1630-1652).
        let visited = self.fresh_marks();
        self.g.work.clear();
        self.push_unless_bound(other, family);
        while let Some(entry) = self.g.work.pop() {
            let t = self.g.repr(entry);
            if self.marks[t.0 as usize] == visited {
                continue;
            }
            #[cfg(test)]
            super::steps::tick();
            let node = self.g.nodes[t.0 as usize];
            if self.is_univar(t) {
                // `Tunivar _ -> if Type_set.mem t family then raise Occur`.
                if self.marks[t.0 as usize] == family {
                    self.g.work.clear();
                    return true;
                }
                continue;
            }
            self.marks[t.0 as usize] = visited;
            match node.tag() {
                // `Tconstr (_, [], _) -> ()` and the arguments the
                // variances allow (ctype.ml:1638-1647).
                CONSTR => {
                    for i in 0..node.arity() {
                        if self.types.may_occur(node.a, i) {
                            let ty = self.g.lists[(node.b + 1 + i) as usize];
                            self.g.work.push(ty);
                        }
                    }
                }
                TUPLE if node.head & EXTENDED != 0
                    && matches!(self.extras.descriptors[node.a as usize], ExtraDescriptor::Poly) =>
                {
                    self.push_unless_bound(node, family);
                }
                _ => self.g.children(node, false),
            }
        }
        false
    }

    /// `Tpoly (t, tl)` of [`Checker::univars_escape`] (compiler/ml/ctype.
    /// ml:1634-1636): push the body of the polymorphic descriptor `node`
    /// unless one of its bound variables is in the family (marked
    /// `family`). O(bound variables): one step a slot read.
    fn push_unless_bound(&mut self, node: Node, family: u32) {
        if !self.any_marked(node.b + 1, node.arity() - 1, family) {
            self.g.work.push(self.g.lists[node.b as usize]);
        }
    }

    /// The walk of `occur_univar` (compiler/ml/ctype.ml:1563-1607): the
    /// first universal variable of `ty` that no polymorphic type on the
    /// way to it binds, or `NONE`. "First" is in the order below, which
    /// is `iter_type_expr`'s; it is the variable a diagnostic names.
    ///
    /// *Contexts.* The walk numbers the polymorphic types it enters:
    /// context 0 is the root (nothing bound), context `k` the k-th entry.
    /// Context `k` has the mark generation `g0 + k`, where `g0` is the
    /// generation taken at the start; the walk takes one generation per
    /// entry and nothing else takes one meanwhile (it expands nothing and
    /// makes no node). `extras.open_polys[k]` says the context is still
    /// open. A mark `m` is *live* when `m >= g0 && open_polys[m - g0]`.
    /// Before the walk: when `mark_generation > u32::MAX / 2`, the marks
    /// are filled with 0 and the counter reset, so that the generations
    /// of one walk are consecutive.
    ///
    /// *The loop*, on `g.work`, depth first; `current` is the generation
    /// of the innermost open context. An entry `NONE` leaves a context:
    /// the entry below it is the generation to return to; the context
    /// left is closed (`open_polys[current - g0] = false`). Any other
    /// entry is a node, taken as its representative `t`:
    /// - a universal variable: when its mark is live it is bound
    ///   (`Type_set.mem ty bound`); otherwise it is the answer (the work
    ///   list and `open_polys` are cleared);
    /// - a node whose mark is live: skipped. It was visited in a context
    ///   that is still open, whose bound variables are among the current
    ///   ones (ctype.ml:1572-1581: visited with `bound'`, not visited
    ///   again while `bound'` is within `bound`). A node visited in the
    ///   root context is never visited again (ctype.ml:1569-1571); one
    ///   visited in a context that has closed is visited again;
    /// - otherwise the node is marked with `current`, one step, and:
    ///   - a polymorphic type without bound variables: its body, in the
    ///     current context (`bound` is unchanged, ctype.ml:1587-1589);
    ///   - a polymorphic type with bound variables: a new generation `g`
    ///     and `open_polys.push(true)`; each bound variable's
    ///     representative whose mark is not live is marked `g` (one that
    ///     an enclosing open type binds keeps that mark, so that leaving
    ///     this context does not unbind it); pushed: `current`, `NONE`,
    ///     then the body (slot 0) on top; `current = g`. The bound
    ///     variables are not children;
    ///   - a constructor without arguments: nothing (ctype.ml:1590); with
    ///     arguments, those [`TypeTable::may_occur`] allows, in order
    ///     (ctype.ml:1591-1599);
    ///   - a variant row: its slots in order except its `more` slot, then
    ///     its `more` slot (`iter_row` visits the fields and the name's
    ///     arguments, `iter_type_expr` the row variable after them,
    ///     compiler/ml/btype.ml:229-241, 263-266);
    ///   - any other node: its children in `Checker::child`'s order.
    ///
    /// Children are pushed last first, so that they are visited in order.
    ///
    /// Cost: one step per visit; a node is visited once, plus once per
    /// closed context it was first visited in (as OCaml's `visited` map,
    /// which the source calls "way too expensive"); O(nodes) for a type
    /// without a polymorphic type that shares a node with the outside.
    /// No allocation: `g.work` and `open_polys` keep their capacity.
    /// Never called when [`Extras::univars`] is 0. (R3g)
    #[inline(never)]
    pub fn free_univar(&mut self, ty: Ty) -> Ty {
        if self.mark_generation > u32::MAX / 2 {
            self.marks.fill(0);
            self.mark_generation = 0;
        }
        let first = self.fresh_marks();
        let mut current = first;
        self.extras.open_polys.push(true);
        self.g.work.clear();
        self.g.work.push(ty);
        let mut found = Ty(NONE);
        while let Some(entry) = self.g.work.pop() {
            if entry.0 == NONE {
                // Leave the context: the entry below is the one to return to.
                self.extras.open_polys[(current - first) as usize] = false;
                current = self.g.work.pop().expect("a context to return to").0;
                continue;
            }
            let t = self.g.repr(entry);
            let live = self.live_mark(t, first);
            if self.is_univar(t) {
                // `if not (Type_set.mem ty bound) then raise ...`.
                if !live {
                    found = t;
                    break;
                }
                continue;
            }
            if !live {
                self.marks[t.0 as usize] = current;
                #[cfg(test)]
                super::steps::tick();
                let node = self.g.nodes[t.0 as usize];
                self.push_free_univar_children(node, first, &mut current);
            }
        }
        self.g.work.clear();
        self.extras.open_polys.clear();
        found
    }

    /// O(1): whether the mark of `t` is a generation of the current
    /// [`Checker::free_univar`] walk (from `first`) whose context is still
    /// open. One mark load and, for a mark of this walk, one flag load.
    #[inline]
    fn live_mark(&self, t: Ty, first: u32) -> bool {
        let mark = self.marks[t.0 as usize];
        mark >= first && self.extras.open_polys[(mark - first) as usize]
    }

    /// One visit of [`Checker::free_univar`] after `node` was marked: push
    /// what the walk visits next, last first, so that the children are
    /// popped in `iter_type_expr`'s order (compiler/ml/btype.ml:229-272).
    /// A polymorphic type opens a context (a new generation, its bound
    /// variables marked with it unless an open context binds them
    /// already) and makes `current` that generation. O(arity) pushes and,
    /// for a polymorphic type, one mark load and store per bound
    /// variable; no allocation beyond `g.work`'s growth.
    fn push_free_univar_children(&mut self, node: Node, first: u32, current: &mut u32) {
        let arity = node.arity();
        match node.tag() {
            ARROW => {
                self.g.work.push(Ty(node.a));
                for i in (0..arity).rev() {
                    let ty = self.g.params[(node.b + i) as usize].ty;
                    self.g.work.push(ty);
                }
            }
            // `Tconstr (_, [], _) -> ()`; the arguments the variances allow
            // (compiler/ml/ctype.ml:1590-1599). The abbreviation memo is
            // not a child (`iter_type_expr`).
            CONSTR => {
                for i in (0..arity).rev() {
                    if self.types.may_occur(node.a, i) {
                        let ty = self.g.lists[(node.b + 1 + i) as usize];
                        self.g.work.push(ty);
                    }
                }
            }
            TUPLE if node.head & EXTENDED != 0 => match self.extras.descriptors[node.a as usize] {
                // `Tpoly (ty, tyl)`: the body with the bound variables
                // added to `bound` (compiler/ml/ctype.ml:1587-1589).
                // `Tpoly (ty, [])` adds nothing to `bound`: no context, the
                // body is a child like any other. A context for it would
                // make every node first met below it be visited again
                // after it is left, which doubles the walk at each such
                // type that shares its body with the outside
                // (CHECKER_REWRITE 8.6, decision 59).
                ExtraDescriptor::Poly if arity == 1 => {
                    self.g.work.push(self.g.lists[node.b as usize]);
                }
                ExtraDescriptor::Poly => {
                    let generation = self.fresh_marks();
                    self.extras.open_polys.push(true);
                    for i in 1..arity {
                        let bound = self.g.repr(self.g.lists[(node.b + i) as usize]);
                        if !self.live_mark(bound, first) {
                            self.marks[bound.0 as usize] = generation;
                        }
                    }
                    self.g.work.push(Ty(*current));
                    self.g.work.push(Ty(NONE));
                    self.g.work.push(self.g.lists[node.b as usize]);
                    *current = generation;
                }
                // `iter_row` (the fields and the name's arguments), then
                // the row variable (compiler/ml/btype.ml:229-241, 263-266).
                ExtraDescriptor::Variant(index) => {
                    let more = self.extras.variants[index as usize].more;
                    self.g.work.push(self.g.lists[(node.b + more) as usize]);
                    for i in (0..arity).rev() {
                        if i != more {
                            self.g.work.push(self.g.lists[(node.b + i) as usize]);
                        }
                    }
                }
                _ => {
                    for i in (0..arity).rev() {
                        self.g.work.push(self.g.lists[(node.b + i) as usize]);
                    }
                }
            },
            TUPLE => {
                for i in (0..arity).rev() {
                    self.g.work.push(self.g.lists[(node.b + i) as usize]);
                }
            }
            _ => {}
        }
    }

    /// `occur_univar env ty` (compiler/ml/ctype.ml:1563-1607): a clash
    /// when [`Checker::free_univar`] finds a universal variable; in
    /// `Mode::Explain` its pair, the variable and a new variable at the
    /// generic level, goes on the trace (`raise (Unify [(ty, newgenvar
    /// ())])`, ctype.ml:1586). Out of line: its callers test
    /// [`Extras::univars`] first, one load, and a unit without a
    /// universal variable never calls it. O(1) plus the walk.
    #[inline(never)]
    pub fn occur_univar(&mut self, ty: Ty) -> Result<(), Clash> {
        let free = self.free_univar(ty);
        if free.0 == NONE {
            return Ok(());
        }
        if self.g.mode == Mode::Explain {
            let var = self.g.push(Node {
                head: VAR,
                level: GENERIC,
                a: NONE,
                b: 0,
            });
            self.trace.push([free, var]);
        }
        Err(Clash)
    }

    /// PR#6744 (compiler/ml/ctype.ml:2685-2699), called by
    /// [`Checker::join_either`] when the graph has a universal variable:
    /// `gained[0]` and `gained[1]` are the ranges of `extras.row_scratch`
    /// that hold `tl1'` and `tl2'` (what row 1 and row 2 gain,
    /// representatives), `frame` the pair's [`FrameKind::RowField`] or
    /// [`FrameKind::RowFieldEnd`] frame.
    ///
    /// `tlu1` and `tlu2` are the types of each range in which
    /// [`Checker::free_univar`] finds a variable (`split_univars`: the
    /// trace is not touched by the test).
    /// - Both empty: `Ok(Some(gained))`, unchanged.
    /// - Both not empty and `extras.passive_variants`: each range is
    ///   compacted in place to the types that hold none, in order, and
    ///   the two new ranges are returned (they may leave a gap in the
    ///   scratch between them).
    /// - Both not empty otherwise (`List.iter (unify env tu1) (tlu1 @
    ///   tlu2)`): [`ROW_UNIVARS`] is set in the pair's record
    ///   (`saved[frame.extra]`); when the frame on top of `frames` is not
    ///   this pair's `RowFieldEnd` frame (the caller is
    ///   [`Checker::row_field_end`], which popped it) one is pushed; then
    ///   the pairs of the first type of `tlu1` with each other type of
    ///   `tlu1` and each type of `tlu2`, pushed so that they are popped
    ///   in that order; the types each range KEEPS are written to
    ///   `saved` after the record (an entry with the two counts, then one
    ///   entry a type). `Ok(None)`: the join is run again when the
    ///   holders are unified, and gains exactly those kept types, as
    ///   OCaml's `tl1'` and `tl2'` are computed before `unify env tu1`
    ///   (ctype.ml:2685-2706; CHECKER_REWRITE 8.6, decision 58).
    /// - One empty (`occur_univar !env tu`): [`Checker::occur_univar`] of
    ///   the first type of the other, which fails and pushes its pair in
    ///   `Mode::Explain`: `Err([NONE, NONE])`.
    ///
    /// O(types gained) walks, each [`Checker::free_univar`]'s cost; no
    /// allocation. (R3g)
    #[inline(never)]
    pub fn split_univars(
        &mut self,
        frame: Frame,
        gained: [std::ops::Range<usize>; 2],
    ) -> Result<Option<[std::ops::Range<usize>; 2]>, [Ty; 2]> {
        let [gained1, gained2] = gained;
        // `let tl1', tlu1 = split_univars tl1' and tl2', tlu2 = ...`.
        let (kept1, held1) = self.partition_univars(gained1);
        let (kept2, held2) = self.partition_univars(gained2);
        match (held1.is_empty(), held2.is_empty()) {
            (true, true) => Ok(Some([kept1, kept2])),
            (false, false) if self.extras.passive_variants => Ok(Some([kept1, kept2])),
            // `tu1 :: tlu1, _ :: _ -> List.iter (unify env tu1) (tlu1 @
            // tlu2)`.
            (false, false) => {
                self.saved[frame.extra as usize].b |= ROW_UNIVARS;
                // What the two fields gain is decided now, before the
                // holders are unified (ctype.ml:2685-2706): the kept types
                // go after the record, first an entry with the two
                // counts (`head`, `level`), then one entry a type
                // (`head`). Only this arm writes them: O(types kept),
                // 16 bytes each, until the pair's `RowFieldEnd` frame is
                // popped.
                debug_assert_eq!(self.saved.len(), frame.extra as usize + 1);
                self.saved.push(Node {
                    head: kept1.len() as u32,
                    level: kept2.len() as u32,
                    a: NONE,
                    b: 0,
                });
                for at in kept1.clone().chain(kept2.clone()) {
                    let ty = self.extras.row_scratch[at].ty;
                    self.saved.push(Node {
                        head: ty.0,
                        level: 0,
                        a: NONE,
                        b: 0,
                    });
                }
                let end = Frame { kind: FrameKind::RowFieldEnd, ..frame };
                if self.frames.last() != Some(&end) {
                    self.frames.push(end);
                }
                let tu1 = self.extras.row_scratch[held1.start].ty;
                for at in (held1.start + 1..held2.end).rev() {
                    // The two holder ranges are adjacent: `held2` was
                    // appended right after `held1`.
                    let ty = self.extras.row_scratch[at].ty;
                    self.push_row_pair(tu1, ty);
                }
                Ok(None)
            }
            // `tu :: _, [] | [], tu :: _ -> occur_univar !env tu`.
            (false, true) | (true, false) => {
                let first = if held1.is_empty() { held2.start } else { held1.start };
                let tu = self.extras.row_scratch[first].ty;
                let refused = self.occur_univar(tu);
                debug_assert!(refused.is_err(), "the type holds a free universal variable");
                Err([Ty(NONE), Ty(NONE)])
            }
        }
    }

    /// `List.partition` of [`Checker::split_univars`] (compiler/ml/
    /// ctype.ml:2685-2690) over `extras.row_scratch[range]`: the types in
    /// which [`Checker::free_univar`] finds no variable are compacted in
    /// place, in order, to the start of the range; those in which it finds
    /// one are appended, in order, at the end of the scratch. Returns the
    /// two ranges. O(types) walks, each `free_univar`'s cost; no
    /// allocation beyond the scratch's growth.
    fn partition_univars(&mut self, range: std::ops::Range<usize>) -> (std::ops::Range<usize>, std::ops::Range<usize>) {
        let (start, held) = (range.start, self.extras.row_scratch.len());
        let mut kept = start;
        for at in range {
            let field = self.extras.row_scratch[at];
            if self.free_univar(field.ty).0 == NONE {
                self.extras.row_scratch[kept] = field;
                kept += 1;
            } else {
                self.extras.row_scratch.push(field);
            }
        }
        (start..kept, held..self.extras.row_scratch.len())
    }

    /// `Tpackage (p1, n1, tl1), Tpackage (p2, n2, tl2)` of unify3
    /// (compiler/ml/ctype.ml:2416-2423) with `unify_package`
    /// (ctype.ml:2172-2181), after the link: `[t1x, t2x]` are the two
    /// nodes and `left`, `right` the descriptors they had. The levels
    /// `lv1` and `lv2` are both `min(left.level, right.level)`: OCaml
    /// reads `t1.level` and `t2.level` after `unify2` lowered both to the
    /// lower of the two expansions' levels (ctype.ml:2283-2285).
    ///
    /// One merge of the two name lists (`PackageRow::longidents`, each
    /// sorted by `Longident.cmp`; [`PackageDecls::compare`]), which is
    /// `complete_type_list` in both directions (ctype.ml:2135-2169): a
    /// name both list gives the pair of the two arguments; a name only
    /// the left lists asks [`PackageDecls::complete`] of the RIGHT
    /// package's path at `lv2` and pairs the left argument with the
    /// answer; a name only the right lists asks the left path at `lv1`.
    /// An answer that is not [`Completion::Type`] is a clash (`Not_found`
    /// in expression mode, ctype.ml:2420-2421), as is a missing
    /// [`Checker::packages`]. First `left` goes on `saved` and a
    /// [`FrameKind::PackageEnd`] frame of `t1x`, `t2x` with that index as
    /// its `extra` is pushed; then one pair a name as the merge meets
    /// them; when the merge is complete the pairs' part of `frames` is
    /// reversed in place, so that they are popped in name order
    /// (`unify_list`, ctype.ml:2175). A clash during the merge cuts
    /// `frames` and `saved` back to where they were: nothing stays
    /// pushed. The supplier is taken out of [`Checker::packages`] for the
    /// calls and put back, also on a clash. Pattern mode (`List.iter
    /// (reify env) (tl1 @ tl2)`) is R3h's. O(names of both), one step a
    /// name; no allocation beyond the frames. Cold and not inlined, as its
    /// `todo!` was: packages are rare, and inlined it moves the code of
    /// every unification. (R3p)
    #[cold]
    #[inline(never)]
    pub fn unify_package(
        &mut self,
        [t1x, t2x]: [Ty; 2],
        left: Node,
        right: Node,
    ) -> Result<(), Clash> {
        let Some(mut decls) = self.packages.take() else {
            return Err(Clash);
        };
        let (base, saved_base) = (self.frames.len(), self.saved.len());
        self.saved.push(left);
        self.frames.push(Frame {
            left: t1x,
            right: t2x,
            kind: FrameKind::PackageEnd,
            extra: saved_base as u32,
        });
        let merged = self.merge_packages(&mut *decls, left, right);
        self.packages = Some(decls);
        if merged.is_err() {
            self.frames.truncate(base);
            self.saved.truncate(saved_base);
            return merged;
        }
        self.frames[base + 1..].reverse();
        Ok(())
    }

    /// The merge of [`Checker::unify_package`]: one turn a name of either
    /// list, one [`PackageDecls::compare`] while both lists have names
    /// left, one [`PackageDecls::complete`] for a name of one side only,
    /// one pair pushed a turn, in name order. Stops at the first answer
    /// that is not a type. O(names of both) plus the supplier; no
    /// allocation beyond the frames.
    fn merge_packages(
        &mut self,
        decls: &mut dyn PackageDecls,
        left: Node,
        right: Node,
    ) -> Result<(), Clash> {
        let (row1, row2) = (self.package_row(left), self.package_row(right));
        let level = left.level.min(right.level);
        let (n1, n2) = (row1.longidents.len, row2.longidents.len);
        // The arguments are the node's slots from `arguments.start` on.
        let (args1, args2) = (
            left.b + row1.arguments.start,
            right.b + row2.arguments.start,
        );
        let (mut i, mut j) = (0, 0);
        while i < n1 || j < n2 {
            #[cfg(test)]
            super::steps::tick();
            let (name1, name2) = (row1.longidents.start + i, row2.longidents.start + j);
            let order = if i == n1 {
                Ordering::Greater
            } else if j == n2 {
                Ordering::Less
            } else {
                decls.compare(name1, name2)
            };
            let [l, r] = match order {
                Ordering::Equal => [
                    self.g.lists[(args1 + i) as usize],
                    self.g.lists[(args2 + j) as usize],
                ],
                // A name only the left lists: the right module type's
                // answer (`complete_type_list env n1 lv2 (Mty_ident p2)`,
                // ctype.ml:2173).
                Ordering::Less => match decls.complete(self, row2.path, name1, level) {
                    Completion::Type(ty) => [self.g.lists[(args1 + i) as usize], ty],
                    _ => return Err(Clash),
                },
                Ordering::Greater => match decls.complete(self, row1.path, name2, level) {
                    Completion::Type(ty) => [ty, self.g.lists[(args2 + j) as usize]],
                    _ => return Err(Clash),
                },
            };
            i += u32::from(order != Ordering::Greater);
            j += u32::from(order != Ordering::Less);
            self.frames.push(Frame {
                left: l,
                right: r,
                kind: FrameKind::Pair,
                extra: 0,
            });
        }
        Ok(())
    }

    /// O(1): the [`PackageRow`] of a package descriptor.
    fn package_row(&self, node: Node) -> PackageRow {
        match self.extras.descriptors[node.a as usize] {
            ExtraDescriptor::Package(row) => self.extras.packages[row as usize],
            _ => unreachable!("a package descriptor"),
        }
    }

    /// The pop of a [`FrameKind::PackageEnd`] frame: the completed lists
    /// are unified, and the two paths decide (`if eq_package_path env p1
    /// p2 || ... then () else raise Not_found`, compiler/ml/ctype.ml:
    /// 2176-2181). Equal `PackageRow::path` indices: `Ok` (`Path.same`).
    /// Otherwise [`PackageDecls::compatible`] with the left descriptor
    /// (`saved[frame.extra]`) and the right node's; `false` is a clash
    /// with no pair of its own. `saved` is cut back to the frame's
    /// `extra`. O(1) plus the supplier. Cold and not inlined, like
    /// [`Checker::unify_package`]. (R3p)
    #[cold]
    #[inline(never)]
    pub fn package_end(&mut self, frame: Frame) -> Result<(), Clash> {
        let left = self.saved[frame.extra as usize];
        self.saved.truncate(frame.extra as usize);
        let right = self.g.nodes[frame.right.0 as usize];
        if self.package_row(left).path == self.package_row(right).path {
            return Ok(());
        }
        let Some(mut decls) = self.packages.take() else {
            return Err(Clash);
        };
        let compatible = decls.compatible(self, left, right);
        self.packages = Some(decls);
        if compatible { Ok(()) } else { Err(Clash) }
    }

    /// `Not_found` of two packages (compiler/ml/ctype.ml:2420-2422: `if
    /// !(umode ()) = Expression then raise (Unify []); List.iter (reify
    /// env) (tl1 @ tl2)`), for the two package nodes `left` and `right`:
    /// in expression mode a clash; in pattern mode [`Checker::reify`] of
    /// every argument of the left package, then of the right one, in
    /// order, and `Ok` unless one clashes. Its two callers: the package
    /// arm of pattern mode when [`Checker::unify_package`] clashes in its
    /// merge (a completion that is no type, or no supplier), and the pop
    /// of a [`FrameKind::PackageEnd`] frame whose
    /// [`Checker::package_end`] clashed (the two paths are not
    /// compatible). One load of `umode`, on a failure path; then
    /// O(arguments) plus the walks. (R3r; CHECKER_REWRITE 8.9, decision
    /// 63)
    #[cold]
    #[inline(never)]
    pub fn package_fallback(&mut self, left: Ty, right: Ty) -> Result<(), Clash> {
        if self.umode == super::unify::UnifyMode::Expression {
            return Err(Clash);
        }
        for package in [left, right] {
            let node = self.g.nodes[package.0 as usize];
            let arguments = self.package_row(node).arguments;
            for slot in arguments.start..arguments.start + arguments.len {
                let argument = self.g.lists[(node.b + slot) as usize];
                self.reify(argument)?;
            }
        }
        Ok(())
    }

    /// `reify env t` (compiler/ml/ctype.ml:1813-1859): every variable
    /// `ty` reaches becomes a new locally abstract type of the newtype
    /// level, and the row variable of every variant that is neither
    /// static nor fixed a fixed row without tags over one. A clash when
    /// such a variable is below [`Checker::newtype_level`]: it is linked
    /// first (ctype.ml:1837-1838, 1851-1853) and the link stays.
    ///
    /// One walk: a new mark generation, the stack `g.work` (nothing is
    /// expanded, so nothing else uses it), children pushed so that they
    /// pop in the order OCaml visits them: the fresh types are named in
    /// visit order. Per representative not yet marked:
    ///
    /// - a variable: [`Checker::fresh_abstract`] at its level with its
    ///   name; `Graph::link` of the variable to that node; then the level
    ///   test (`if ty.level < newtype_level then raise (Unify [(t,
    ///   newvar2 ty.level)])`): in `Mode::Explain` the pair of the new
    ///   node and a new variable at the variable's level goes on
    ///   [`Checker::trace`];
    /// - a variant: its row is read as `row_repr` reads it (the chain of
    ///   variant nodes down to the last one, whose `VariantRow` has the
    ///   flags and the name; each field through its references,
    ///   [`field_repr`]). Unless it is static (closed and no field is
    ///   `Reither`, btype.ml `static_row`): for a `fixed` last row, and
    ///   for one over a constructor, which OCaml's copy has made fixed
    ///   (PR#6163, ctype.ml:826-830; the kernel's copy shares the row,
    ///   [`Checker::copy_refs`]), the representative of its `more` is
    ///   visited FIRST; otherwise that
    ///   `more` is a variable (anything else is an invariant failure) and
    ///   becomes, through `Graph::link`, a new variant node at its level
    ///   with no field, `fixed`, the `closed` and the name of the last
    ///   row (`{r with row_fields = []; row_fixed = true; row_more = t}`,
    ///   ctype.ml:1848-1850) and the fresh type as its `more`; the last
    ///   node, whose `more` is a variant now, loses the arguments of its
    ///   name as children (`Checker::forget_name_children`, without a
    ///   frame: the link stays when the unification fails); then the same
    ///   level test for the row variable. Then, in order: the types of
    ///   the fields, chain node by chain node (`Rpresent (Some ty)`: the
    ///   type; `Reither`: every type), and the arguments of the last
    ///   row's name (`iter_row`, btype.ml:229-241). The `more` of a row
    ///   that is static is not visited;
    /// - a constructor whose path is an object type (`is_object_type`,
    ///   ctype.ml:1856-1857): no kernel type has such a path; not built;
    /// - anything else: its children in `iter_type_expr`'s order.
    ///
    /// No supplier ([`Checker::locals`] is `None`) and a variable to
    /// reify: a panic that names `Checker::locals`.
    ///
    /// Cost: one step and one mark a node reached; per variable one
    /// `TypeInfo` row (16 bytes), one `Newtype` row (8), one node and one
    /// list slot; per row variable also what `Checker::build_variant`
    /// allocates for a row without fields. A variant node costs one
    /// descriptor load and one `VariantRow` load per chain node and one
    /// `field_repr` per field. (R3h; CHECKER_REWRITE 8.9)
    pub fn reify(&mut self, ty: Ty) -> Result<(), Clash> {
        let generation = self.fresh_marks();
        self.g.work.clear();
        self.g.work.push(ty);
        while let Some(entry) = self.g.work.pop() {
            let t = self.g.repr(entry);
            // A fresh type is a node past the marks.
            if t.0 as usize >= self.marks.len() {
                self.marks.resize(self.g.nodes.len(), 0);
            }
            if self.marks[t.0 as usize] == generation {
                continue;
            }
            self.marks[t.0 as usize] = generation;
            #[cfg(test)]
            super::steps::tick();
            let node = self.g.nodes[t.0 as usize];
            if node.tag() == VAR {
                let fresh = self.fresh_abstract(node.level, node.a);
                self.g.link(t, fresh);
                if node.level < self.newtype_level {
                    self.g.work.clear();
                    return Err(self.below_newtype_level(fresh, node.level));
                }
                continue;
            }
            if node.head & EXTENDED != 0
                && matches!(self.extras.descriptors[node.a as usize], ExtraDescriptor::Variant(_))
            {
                self.reify_row(t, node)?;
                continue;
            }
            // `iter_type_expr`'s order: pushed last first.
            let count = match node.tag() {
                ARROW => node.arity() + 1,
                CONSTR | TUPLE => node.arity(),
                _ => 0,
            };
            for index in (0..count).rev() {
                let child = self.child(node, index).expect("a child below the count");
                self.g.work.push(child);
            }
        }
        Ok(())
    }

    /// The variant arm of [`Checker::reify`] for variant node `ty`, whose
    /// descriptor is `node`, read as `row_repr` reads it
    /// (compiler/ml/btype.ml:126-135, 229-241; ctype.ml:1841-1855): the
    /// types of every field of the chain and the arguments of the last
    /// row's name go on `g.work` so that they pop in order, and above
    /// them the `more` of a fixed row, which pops first; or the row
    /// variable of a row that is neither static nor fixed is linked to a
    /// fixed row without tags over a fresh type. A row over a constructor
    /// is read as fixed, as [`Checker::copy_refs`] reads it (PR#6163,
    /// ctype.ml:826-830: OCaml's copy sets the flag, the kernel's copy
    /// shares the row). O(chain nodes + fields + their types), no
    /// allocation but what the fixed row allocates.
    fn reify_row(&mut self, ty: Ty, node: Node) -> Result<(), Clash> {
        let start = self.g.work.len();
        let mut work = std::mem::take(&mut self.g.work);
        let (mut home, mut current, mut static_fields) = (ty, node, true);
        let (row, more) = loop {
            let ExtraDescriptor::Variant(index) = self.extras.descriptors[current.a as usize] else {
                unreachable!("a variant node");
            };
            let row = self.extras.variants[index as usize];
            for at in row.fields.start..row.fields.start + row.fields.len {
                let field = self.extras.row_fields[at as usize];
                let read = field_repr(&self.g, current.b, current.arity(), field);
                match read.kind {
                    RowFieldKind::Present if read.first.0 != NONE => work.push(read.first),
                    RowFieldKind::Either { .. } => {
                        static_fields = false;
                        each_field_types(&self.g, current.b, current.arity(), field, |types| {
                            work.extend_from_slice(types)
                        });
                    }
                    _ => {}
                }
            }
            let more = self.g.repr(self.g.lists[(current.b + row.more) as usize]);
            let next = self.g.nodes[more.0 as usize];
            if next.head & EXTENDED == 0
                || !matches!(self.extras.descriptors[next.a as usize], ExtraDescriptor::Variant(_))
            {
                break (row, more);
            }
            (home, current) = (more, next);
        };
        if row.name != NONE {
            let arguments = row.name_arguments;
            let from = (current.b + arguments.start) as usize;
            work.extend_from_slice(&self.g.lists[from..from + arguments.len as usize]);
        }
        work[start..].reverse();
        self.g.work = work;
        if row.closed && static_fields {
            return Ok(());
        }
        let variable = self.g.nodes[more.0 as usize];
        if row.fixed || variable.tag() == CONSTR {
            self.g.work.push(more);
            return Ok(());
        }
        assert_eq!(variable.tag(), VAR, "the row variable of a row that is not fixed");
        let fresh = self.fresh_abstract(variable.level, variable.a);
        let scratch = self.extras.row_scratch.len();
        let tail = self.build_variant(scratch..scratch, fresh, row.closed, true, (row, current.b));
        self.g.nodes[tail.0 as usize].level = variable.level;
        self.g.link(more, tail);
        if row.name != NONE && row.name_arguments.len != 0 {
            self.forget_name_children(home, row);
        }
        if variable.level < self.newtype_level {
            self.g.work.clear();
            return Err(self.below_newtype_level(fresh, variable.level));
        }
        Ok(())
    }

    /// `create_fresh_constr lev name` of `reify` (compiler/ml/ctype.ml:
    /// 1815-1826): a node of a new locally abstract type at `level`.
    /// [`LocalDecls::fresh_abstract`] gives the type index for the
    /// variable's name index `name` (or `NONE`); the `TypeTable` row of
    /// that index is pushed (`rows.len()` must equal the index: the
    /// supplier counts with the table): abstract, [`NEWTYPE`], a
    /// `Newtype` row of `(newtype_level, newtype_level)`
    /// (`new_declaration (Some (newtype_level, newtype_level)) None`),
    /// scope `newtype_level` (`get_level`, ctype.ml:562-569), and
    /// `TypeTable::scoped` counts it. Then a constructor node without
    /// arguments of it at `level`. Panics, naming `Checker::locals`, when
    /// no supplier is installed. O(1) amortized: two rows, one node, one
    /// list slot. (R3h)
    fn fresh_abstract(&mut self, level: u32, name: u32) -> Ty {
        let mut locals = self
            .locals
            .take()
            .expect("Checker::locals: reify needs a supplier of locally abstract types");
        let fresh = locals.fresh_abstract(name);
        self.locals = Some(locals);
        assert_eq!(self.types.rows.len() as u32, fresh, "the supplier counts with the table");
        let newtype = self.types.newtypes.len() as u32;
        let newtype_level = self.newtype_level;
        self.types.newtypes.push(Newtype { level: newtype_level, expansion_level: newtype_level });
        self.types.rows.push(TypeInfo {
            manifest: NONE,
            scope: newtype_level,
            newtype,
            arity: 0,
            flags: NEWTYPE,
            reserved: 0,
        });
        if newtype_level != 0 {
            self.types.scoped += 1;
        }
        let b = self.g.lists.len() as u32;
        self.g.lists.push(Ty(NONE));
        self.g.push(Node { head: CONSTR, level, a: fresh, b })
    }

    /// `raise (Unify [(t, newvar2 level)])` of `reify`
    /// (compiler/ml/ctype.ml:1838, 1852-1853): in `Mode::Explain` the pair
    /// of `fresh` and a new variable at `level` goes on
    /// [`Checker::trace`]. O(1) amortized: one node and one trace entry.
    #[cold]
    fn below_newtype_level(&mut self, fresh: Ty, level: u32) -> Clash {
        if self.g.mode == Mode::Explain {
            let variable = self.g.push(Node { head: VAR, level, a: NONE, b: 0 });
            self.trace.push([fresh, variable]);
        }
        Clash
    }

    /// `add_gadt_equation env source destination` (compiler/ml/ctype.ml:
    /// 2093-2100). In this order:
    ///
    /// 1. [`Checker::non_recursive_abbrev`]: `Ok(false)`, nothing happens
    ///    and it is no clash; a clash of an expansion it makes is this
    ///    call's clash;
    /// 2. [`Checker::cleanup_abbrev`] (OCaml runs it last, ctype.ml:2100;
    ///    nothing reads a memo in between, and step 3 must copy with no
    ///    live memo: a copy of a constructor without arguments would
    ///    otherwise link to a memorized node that is not generic);
    /// 3. [`Checker::duplicate`] of `destination`: the body;
    /// 4. a `Manifest` row `{ template: an empty template, params: the
    ///    length of `roots`, body }`, never instantiated: `subst` takes
    ///    the equation arm for a row with [`NEWTYPE`] and copies `body`;
    /// 5. the entry `Equation { type_index: source, previous: the row }`
    ///    goes on [`Checker::equations`]; then the row gets [`ABBREV`],
    ///    [`NEWTYPE`], the manifest, and a NEW `Newtype` row `(level,
    ///    newtype_level)`: `level` is the first of
    ///    [`Checker::find_newtype_level`] of the source as it was
    ///    (`new_declaration (Some source_lev)`), and the expansion level
    ///    is the level of the pattern being typed
    ///    (`Env.add_local_constraint source decl newtype_level`,
    ///    compiler/ml/env.ml:1805-1810). The scope of the row does not
    ///    change.
    ///
    /// Cost: the walk of step 1, the cleanup, the three passes of step 3
    /// over `destination`, and 28 + 8 + 20 bytes of rows. (R3h;
    /// CHECKER_REWRITE 8.9, decision 67)
    pub fn add_gadt_equation(&mut self, source: u32, destination: Ty) -> Result<(), Clash> {
        if !self.non_recursive_abbrev(source, destination)? {
            return Ok(());
        }
        self.cleanup_abbrev();
        let body = self.duplicate(destination);
        let previous = self.types.rows[source as usize];
        let (level, _) = self.find_newtype_level(source);
        let manifest = self.types.manifests.len() as u32;
        // A zero-node template naming the body: never instantiated, the
        // equation arm of `subst` copies `body` (template.rs, `Template`).
        let template = Template { nodes: body.0, node_len: 0, pools: 0, list_len: 0 };
        let params = self.types.roots.len() as u32;
        self.types.manifests.push(Manifest { template, params, body });
        let newtype = self.types.newtypes.len() as u32;
        let expansion_level = self.newtype_level;
        self.types.newtypes.push(Newtype { level, expansion_level });
        self.equations.push(Equation { type_index: source, previous });
        let flags = previous.flags | ABBREV | NEWTYPE;
        self.types.rows[source as usize] = TypeInfo { manifest, newtype, flags, ..previous };
        Ok(())
    }

    /// `local_non_recursive_abbrev env p ty` (compiler/ml/ctype.ml:
    /// 1503-1536, called with `strict = false`): `Ok(false)` when `ty`
    /// names the type `source` where the walk below looks; a clash when
    /// an expansion the walk makes clashes (`try_expand_once` "may raise
    /// Unify", ctype.ml:1249-1256, and only `Occur` is caught, 1536).
    /// Each entry of the walk is a node and whether it is visited
    /// STRICTLY; `ty` is not. Per representative:
    ///
    /// - a constructor of `source`: `Ok(false)` (`if Path.same p p' then
    ///   raise Occur`, 1508);
    /// - any other constructor: nothing when the visit is not strict and
    ///   its type is [`TypeTable::contractive`] (1509). Otherwise its
    ///   head is expanded ([`Checker::expand_head`] in
    ///   [`ExpandMode::Unif`]: `try_expand_head try_expand_once`, 1515,
    ///   not the `_opt` form) and, when that gives another node, the walk
    ///   goes on in it with the same strictness; when it does not expand,
    ///   each argument is visited, strictly when the visit is strict or
    ///   the parameter of the declaration is not a variable
    ///   ([`TypeTable::constrained`]; for a type without a row, when the
    ///   argument itself is not a variable: `with Not_found -> args`,
    ///   1517-1524);
    /// - any other node: its children, strictly, when the visit is
    ///   strict; nothing otherwise (`| _ -> if strict then`, 1525-1529).
    ///
    /// So with `strict = false` a tuple or an arrow at the top is not
    /// searched, and `a := (a, int)`, `a := array<a>` and `a := box<a>`
    /// for a data type `box` are equations, while `a := M.t<a>` for an
    /// abstract `M.t` is none (both compilers; 8.9, decision 67).
    ///
    /// OCaml's `visited` is the list of the nodes on the way from `ty`
    /// (`if not (List.memq ty visited)`, 1505; `let visited = ty ::
    /// visited`, 1511 and 1528): a node that is on the way is skipped
    /// WHATEVER the strictness it was entered with, and a shared node
    /// is walked once per path. The kernel keeps both facts in the
    /// marks of one node, five generations:
    ///
    /// - *on the way* (entered strictly, entered otherwise, or entered
    ///   otherwise and met again strictly: "met"): set when a
    ///   constructor is entered or a structure is entered strictly, and
    ///   taken off by a LEAVE entry of the stack that lies below the
    ///   node's children. A node on the way is skipped, as line 1505
    ///   skips it.
    /// - *done* (strictly, or otherwise): what the LEAVE entry writes.
    ///   A node that is done is not entered again, except strictly
    ///   after a visit that was not strict (it reaches more). That
    ///   memory across paths is not OCaml's, and it is sound only for a
    ///   node whose walk skipped nothing a later path would enter. The
    ///   one skip that breaks it is a STRICT meeting of a node that is
    ///   on the way and was entered otherwise: on a later path that
    ///   node is entered strictly. So while such a "met" node is on the
    ///   way (`met`, a count), a node that is left is not remembered
    ///   (its mark goes back to none), and is walked once per path as
    ///   in OCaml. Every other skip is of a node whose own walk, once
    ///   it is left, covered at least what the later visit would.
    ///
    /// The stack is [`Checker::frames`] above the length the call
    /// finds: an expansion lowers and unifies, which use `g.work` and
    /// the frames above. Cost: at most two entries and two LEAVE
    /// entries a node reached, one `TypeInfo` load a constructor, one
    /// [`Checker::expand_head`] a constructor that is entered; a node
    /// below a "met" node is entered once per path that reaches it
    /// while that node is on the way (a type that reaches itself
    /// through a parameter that is not constrained and again through
    /// one that is: only pattern mode makes one). (R3h; corrected in
    /// the eighth skeleton turn; CHECKER_REWRITE 8.9, decision 67)
    ///
    /// It traces GADT instances while it runs (`wrap_trace_gadt_instances
    /// env (local_non_recursive_abbrev false [] env p) ty`, compiler/ml/
    /// ctype.ml:1534, PR#7397): one load of `Checker::gadt` and one
    /// branch a call. (R3s; CHECKER_REWRITE 8.11, (iv))
    pub fn non_recursive_abbrev(&mut self, source: u32, ty: Ty) -> Result<bool, Clash> {
        let turned_on = self.gadt & super::unify::GADT_LOCAL != 0 && self.trace_on();
        let result = self.non_recursive_abbrev_walk(source, ty);
        self.trace_off(turned_on);
        result
    }

    /// The walk of [`Checker::non_recursive_abbrev`], whose text
    /// describes it.
    fn non_recursive_abbrev_walk(&mut self, source: u32, ty: Ty) -> Result<bool, Clash> {
        /// The bit of `extra` that makes an entry a LEAVE entry.
        const LEAVE: u32 = 2;
        let lax = self.fresh_marks();
        let strictly = self.fresh_marks();
        let on_lax = self.fresh_marks();
        let on_strict = self.fresh_marks();
        let on_met = self.fresh_marks();
        // How many nodes on the way are "met".
        let mut met = 0u32;
        let base = self.frames.len();
        self.push_visit(ty, false);
        while self.frames.len() > base {
            let frame = self.frames.pop().expect("an entry above the base");
            if frame.extra & LEAVE != 0 {
                // The node's frame is left: `visited` loses it.
                let slot = frame.left.0 as usize;
                let mut done = if self.marks[slot] == on_strict { strictly } else { lax };
                if self.marks[slot] == on_met {
                    met -= 1;
                }
                if met != 0 {
                    done = 0;
                }
                self.marks[slot] = done;
                continue;
            }
            let strict = frame.extra != 0;
            let t = self.g.repr(frame.left);
            // An expansion of the walk adds nodes past the marks.
            if t.0 as usize >= self.marks.len() {
                self.marks.resize(self.g.nodes.len(), 0);
            }
            let mark = self.marks[t.0 as usize];
            if mark == on_lax || mark == on_strict || mark == on_met {
                // `if not (List.memq ty visited)` (1505).
                if strict && mark == on_lax {
                    self.marks[t.0 as usize] = on_met;
                    met += 1;
                }
                continue;
            }
            if mark == strictly || (mark == lax && !strict) {
                continue;
            }
            let (done, on_the_way) = if strict { (strictly, on_strict) } else { (lax, on_lax) };
            #[cfg(test)]
            super::steps::tick();
            let node = self.g.nodes[t.0 as usize];
            if node.tag() != CONSTR {
                // `| _ -> if strict then ... iter_type_expr` (1525-1529).
                let count = match node.tag() {
                    ARROW if strict => node.arity() + 1,
                    TUPLE if strict => node.arity(),
                    _ => 0,
                };
                if count == 0 {
                    self.marks[t.0 as usize] = done;
                    continue;
                }
                self.marks[t.0 as usize] = on_the_way;
                self.frames.push(Frame { left: t, right: Ty(NONE), kind: FrameKind::Pair, extra: LEAVE });
                for index in (0..count).rev() {
                    let child = self.child(node, index).expect("a child below the count");
                    self.push_visit(child, true);
                }
                continue;
            }
            if node.a == source {
                self.frames.truncate(base);
                return Ok(false);
            }
            if !strict && TypeTable::contractive(self.types.info(node.a)) {
                self.marks[t.0 as usize] = done;
                continue;
            }
            // `let visited = ty :: visited in` (1511).
            self.marks[t.0 as usize] = on_the_way;
            self.frames.push(Frame { left: t, right: Ty(NONE), kind: FrameKind::Pair, extra: LEAVE });
            let head = match self.expand_head(t, ExpandMode::Unif) {
                Ok(head) => self.g.repr(head),
                Err(clash) => {
                    self.frames.truncate(base);
                    return Err(clash);
                }
            };
            if head != t {
                self.push_visit(head, strict);
                continue;
            }
            // `Cannot_expand`: the arguments, by the declared parameters
            // (`with Not_found -> args` for a type without a row).
            let declared = (node.a as usize) < self.types.rows.len();
            for index in (0..node.arity()).rev() {
                let argument = self.g.lists[(node.b + 1 + index) as usize];
                let constrained = if declared {
                    self.types.constrained(node.a, index)
                } else {
                    let argument = self.g.repr(argument);
                    self.g.nodes[argument.0 as usize].tag() != VAR
                };
                self.push_visit(argument, strict || constrained);
            }
        }
        Ok(true)
    }

    /// O(1) amortized: one entry of [`Checker::non_recursive_abbrev`]'s
    /// walk on [`Checker::frames`], `extra` its strictness.
    fn push_visit(&mut self, ty: Ty, strict: bool) {
        self.frames.push(Frame { left: ty, right: Ty(NONE), kind: FrameKind::Pair, extra: u32::from(strict) });
    }

    /// `duplicate_type` for an equation (`Subst.type_expr Subst.identity`,
    /// compiler/ml/ctype.ml:496; subst.ml:132-158): a copy of `ty` in
    /// which every node is generic, sharing kept; `ty` is as it was
    /// afterwards. `g.speculate()`; then a walk over `ty` that makes
    /// every node of it generic and goes THROUGH a node that is generic
    /// already (OCaml's copy copies every node whatever its level,
    /// `| _ ->` of `Subst.typexp`, subst.ml:144-158; `Graph::generalize`
    /// stops at a generic node and would leave the nodes below it shared
    /// with the copy): on `g.work`, one new generation of marks
    /// ([`Checker::fresh_marks`]), each representative visited once, its
    /// level written generic with `Graph::write` when it is not (logged,
    /// so the restore puts it back), its children pushed as
    /// `Graph::generalize` pushes them (`Graph::children` with the
    /// memo); [`Checker::copy`] with `g.level` generic; `g.level` put
    /// back; `Graph::restore` of the token, which puts the levels of `ty`
    /// back. The copy's nodes are new and not on the trail, so they stay.
    /// The walk does not forget the memo of constructors without
    /// arguments, as [`Checker::generalize`] does: that memo is not on
    /// the trail (the caller has cleaned the memos already, step 2 of
    /// [`Checker::add_gadt_equation`], so no copy is linked to a
    /// memorized node). OCaml's copy keeps a variable and a universal
    /// variable as the node they are (subst.ml:135-143); the destination
    /// of an equation has no variable (`reify` ran first, or it is a
    /// constructor without arguments), and a universal variable that is
    /// free in it is COPIED here: no program is known that has one
    /// (8.9, decision 67). Cost: three passes over `ty`: one step a node
    /// visited and one trail entry (20 bytes) a level written, one step
    /// a node copied, one step a level restored. (R3h; total in R3r)
    pub fn duplicate(&mut self, ty: Ty) -> Ty {
        let token = self.g.speculate();
        let generation = self.fresh_marks();
        self.g.work.clear();
        self.g.work.push(ty);
        while let Some(next) = self.g.work.pop() {
            let next = self.g.repr(next);
            let mark = &mut self.marks[next.0 as usize];
            if *mark == generation {
                continue;
            }
            *mark = generation;
            #[cfg(test)]
            super::steps::tick();
            let node = self.g.nodes[next.0 as usize];
            if node.level != GENERIC {
                self.g.write(next, Node { level: GENERIC, ..node });
            }
            self.g.children(node, true);
        }
        let level = std::mem::replace(&mut self.g.level, GENERIC);
        let copy = self.copy(ty);
        self.g.level = level;
        self.g.restore(token);
        copy
    }

    /// `find_newtype_level env path` (compiler/ml/ctype.ml:2084-2091):
    /// the `Newtype` row's `(level, expansion_level)` of a type with
    /// [`NEWTYPE`], otherwise `(scope, scope)` (`Path.binding_time`).
    /// Compared as pairs. A type without a row: `(0, 0)`. O(1): one row
    /// load and at most one `Newtype` load. (R3h)
    pub fn find_newtype_level(&self, type_index: u32) -> (u32, u32) {
        let row = self.types.info(type_index);
        if row.flags & NEWTYPE != 0 && row.newtype != NONE {
            let newtype = self.types.newtypes[row.newtype as usize];
            (newtype.level, newtype.expansion_level)
        } else {
            (row.scope, row.scope)
        }
    }

    /// `mcomp` (compiler/ml/ctype.ml:1905-2080): whether two types can
    /// have a common instance; never links, never lowers. The arms are
    /// in CHECKER_REWRITE 8.9, decision 70. Its table is
    /// [`Checker::compatible`], emptied when it returns; its stack is
    /// [`Checker::frames`] above the length it finds (it expands, and an
    /// expansion uses `g.work`): a [`FrameKind::Pair`] frame is a pair to
    /// compare, a [`FrameKind::LeavePoly`] frame, which
    /// [`Checker::enter_poly`] pushes below the pair of two bodies, cuts
    /// [`Checker::scopes`] back to its `extra` when it is popped. A clash
    /// cuts `frames` and `scopes` back to the lengths the call found
    /// (`univar_pairs := old_univars`, ctype.ml:1677-1679). One step a
    /// pair popped; O(pairs). (R3r)
    pub fn mcomp(&mut self, left: Ty, right: Ty) -> Result<(), Clash> {
        let (base, scopes) = (self.frames.len(), self.scopes.len());
        self.push_compatible(left, right);
        let result = self.mcomp_frames(base);
        if result.is_err() {
            self.frames.truncate(base);
            self.scopes.truncate(scopes);
        }
        if !self.compatible.keys.is_empty() {
            self.compatible.keys.clear();
        }
        result
    }

    /// One more pair for the `mcomp` in progress: what
    /// [`LocalDecls::compare`] calls for each pair of member types.
    /// O(1) amortized: one [`FrameKind::Pair`] frame. (R3r)
    pub fn push_compatible(&mut self, left: Ty, right: Ty) {
        self.frames.push(Frame { left, right, kind: FrameKind::Pair, extra: 0 });
    }

    /// The loop of [`Checker::mcomp`] over the frames above `base`, the
    /// arms of compiler/ml/ctype.ml:1905-1965 (CHECKER_REWRITE 8.9,
    /// decision 70). The pairs a pair gives are pushed so that they are
    /// popped in the order OCaml's recursion takes them. Per pair: two
    /// `repr`, two `expand_head` in [`ExpandMode::Opt`], one table
    /// lookup and insert, then one frame a child pair, or one of the
    /// callees. One step a pair popped; a [`FrameKind::LeavePoly`]
    /// frame is one `truncate` and no step. O(pairs) plus the
    /// expansions.
    fn mcomp_frames(&mut self, base: usize) -> Result<(), Clash> {
        while self.frames.len() > base {
            let frame = self.frames.pop().expect("a frame above the base");
            if frame.kind == FrameKind::LeavePoly {
                self.scopes.truncate(frame.extra as usize);
                continue;
            }
            debug_assert_eq!(frame.kind, FrameKind::Pair);
            #[cfg(test)]
            super::steps::tick();
            let (t1, t2) = (self.g.repr(frame.left), self.g.repr(frame.right));
            if t1 == t2 {
                continue;
            }
            let (d1, d2) = (self.g.nodes[t1.0 as usize], self.g.nodes[t2.0 as usize]);
            // `Tvar _, _ | _, Tvar _`; `Tconstr (p1, [], _), Tconstr (p2,
            // [], _) when Path.same p1 p2` (ctype.ml:1913-1914).
            if d1.tag() == VAR || d2.tag() == VAR || (d1.head == CONSTR && d2.head == CONSTR && d1.a == d2.a) {
                continue;
            }
            let t1x = self.expand_head(t1, ExpandMode::Opt)?;
            let t2x = self.expand_head(t2, ExpandMode::Opt)?;
            let (t1x, t2x) = (self.g.repr(t1x), self.g.repr(t2x));
            // `Type_pairs.find type_pairs (t1', t2')`: ordered pairs.
            if t1x == t2x || !self.compatible.keys.insert(u64::from(t1x.0) << 32 | u64::from(t2x.0)) {
                continue;
            }
            let (d1, d2) = (self.g.nodes[t1x.0 as usize], self.g.nodes[t2x.0 as usize]);
            let start = self.frames.len();
            let plain = (d1.head | d2.head) & EXTENDED == 0;
            match (d1.tag(), d2.tag()) {
                (VAR, VAR) => unreachable!("mcomp: two variables after expansion (ctype.ml:1926)"),
                (ARROW, ARROW) if plain && d1.arity() == d2.arity() => {
                    let optional = |label: u32| label != NONE && label & 1 != 0;
                    for i in 0..d1.arity() {
                        let (p1, p2) = (self.g.params[(d1.b + i) as usize], self.g.params[(d2.b + i) as usize]);
                        if p1.label != p2.label && (optional(p1.label) || optional(p2.label)) {
                            return Err(Clash);
                        }
                        self.push_compatible(p1.ty, p2.ty);
                    }
                    self.push_compatible(Ty(d1.a), Ty(d2.a));
                }
                (TUPLE, TUPLE) if plain => {
                    if d1.arity() != d2.arity() {
                        return Err(Clash);
                    }
                    self.push_slots(d1.b, d2.b, d1.arity());
                }
                (CONSTR, CONSTR) => self.mcomp_type_decl(d1, d2)?,
                (CONSTR, _) | (_, CONSTR) => {
                    let path = if d1.tag() == CONSTR { d1.a } else { d2.a };
                    if let Some(&row) = self.types.rows.get(path as usize)
                        && (TypeTable::non_aliasable(row) || row.flags & DATATYPE != 0)
                    {
                        return Err(Clash);
                    }
                }
                _ if d1.head & d2.head & EXTENDED == 0 => return Err(Clash),
                _ => match (self.extras.descriptors[d1.a as usize], self.extras.descriptors[d2.a as usize]) {
                    (ExtraDescriptor::Package(_), ExtraDescriptor::Package(_))
                    | (ExtraDescriptor::Nil, ExtraDescriptor::Nil) => {}
                    (ExtraDescriptor::Variant(_), ExtraDescriptor::Variant(_)) => self.mcomp_row(t1x, t2x)?,
                    (ExtraDescriptor::Object, ExtraDescriptor::Object) => {
                        let (fields1, fields2) = (self.g.lists[d1.b as usize], self.g.lists[d2.b as usize]);
                        self.mcomp_fields(fields1, fields2)?;
                    }
                    // "Actually unused" (ctype.ml:1956-1958).
                    (ExtraDescriptor::Field { .. }, ExtraDescriptor::Field { .. }) => self.mcomp_fields(t1x, t2x)?,
                    (ExtraDescriptor::Poly, ExtraDescriptor::Poly) if d1.arity() == 1 && d2.arity() == 1 => {
                        let (body1, body2) = (self.g.lists[d1.b as usize], self.g.lists[d2.b as usize]);
                        self.push_compatible(body1, body2);
                    }
                    // The `LeavePoly` frame below the pair of the bodies:
                    // nothing to reverse.
                    (ExtraDescriptor::Poly, ExtraDescriptor::Poly) => {
                        self.enter_poly(d1, d2)?;
                        continue;
                    }
                    (ExtraDescriptor::Univar(_), ExtraDescriptor::Univar(_)) => self.unify_univar(t1x, t2x)?,
                    _ => return Err(Clash),
                },
            }
            // Pushed in OCaml's order, popped in it.
            self.frames[start..].reverse();
        }
        Ok(())
    }

    /// O(len): the pairs of two list ranges, first first (the caller
    /// reverses what a pair pushed).
    fn push_slots(&mut self, left: u32, right: u32, len: u32) {
        for i in 0..len {
            let (l, r) = (self.g.lists[(left + i) as usize], self.g.lists[(right + i) as usize]);
            self.push_compatible(l, r);
        }
    }

    /// `mcomp_type_decl` (compiler/ml/ctype.ml:2011-2039) for two
    /// constructor descriptors, pushing first first. A type without a row
    /// on either side: compatible (`with Not_found -> ()`). One type:
    /// the arguments whose parameter is [`TypeTable::injective`]. Two
    /// types, both `non_aliasable`: a clash. Two data types: the
    /// arguments (a clash when their numbers differ), then what
    /// [`LocalDecls::compare`] pushes or a clash; without a supplier a
    /// clash. One data type and an abstract type that is not
    /// `non_aliasable`, or two abstract types: compatible; else a clash.
    /// O(arguments) plus the supplier.
    fn mcomp_type_decl(&mut self, d1: Node, d2: Node) -> Result<(), Clash> {
        let (Some(&row1), Some(&row2)) = (self.types.rows.get(d1.a as usize), self.types.rows.get(d2.a as usize))
        else {
            return Ok(());
        };
        if d1.a == d2.a {
            for i in 0..d1.arity().min(d2.arity()) {
                if self.types.injective(d1.a, i) {
                    let (l, r) = (self.g.lists[(d1.b + 1 + i) as usize], self.g.lists[(d2.b + 1 + i) as usize]);
                    self.push_compatible(l, r);
                }
            }
            return Ok(());
        }
        if TypeTable::non_aliasable(row1) && TypeTable::non_aliasable(row2) {
            return Err(Clash);
        }
        match (row1.flags & DATATYPE != 0, row2.flags & DATATYPE != 0) {
            (true, true) => {
                if d1.arity() != d2.arity() {
                    return Err(Clash);
                }
                self.push_slots(d1.b + 1, d2.b + 1, d1.arity());
                let Some(mut decls) = self.locals.take() else {
                    return Err(Clash);
                };
                let answer = decls.compare(self, d1.a, d2.a);
                self.locals = Some(decls);
                if answer == DeclMatch::Clash { Err(Clash) } else { Ok(()) }
            }
            (false, false) => Ok(()),
            (false, true) if !TypeTable::non_aliasable(row1) => Ok(()),
            (true, false) if !TypeTable::non_aliasable(row2) => Ok(()),
            _ => Err(Clash),
        }
    }

    /// `mcomp_fields` (compiler/ml/ctype.ml:1971-1981) of two field lists:
    /// both flattened into `extras.fields` ([`Checker::flatten_fields`]),
    /// the pair of the two rests pushed, then one merge of the two sorted
    /// lists (`associate_fields`) pushing the pair of the types of every
    /// common name; a clash when a side lacks a name and the other's rest
    /// is `Tnil`. O(fields) plus the flattenings, one step a merge step;
    /// the scratch is cut back to where it was.
    fn mcomp_fields(&mut self, left: Ty, right: Ty) -> Result<(), Clash> {
        let mut fields = std::mem::take(&mut self.extras.fields);
        let base = fields.len();
        let rest1 = self.flatten_fields(left, &mut fields);
        let n1 = fields.len();
        let rest2 = self.flatten_fields(right, &mut fields);
        self.push_compatible(rest1, rest2);
        let (mut i, mut j) = (base, n1);
        let (mut miss1, mut miss2) = (false, false);
        while i < n1 || j < fields.len() {
            #[cfg(test)]
            super::steps::tick();
            let order = if i == n1 {
                Ordering::Greater
            } else if j == fields.len() {
                Ordering::Less
            } else if fields[i].name == fields[j].name {
                Ordering::Equal
            } else {
                let names = &self.extras.names;
                names.text(fields[i].name).cmp(names.text(fields[j].name))
            };
            match order {
                Ordering::Equal => self.push_compatible(fields[i].ty, fields[j].ty),
                Ordering::Less => miss1 = true,
                Ordering::Greater => miss2 = true,
            }
            i += usize::from(order != Ordering::Greater);
            j += usize::from(order != Ordering::Less);
        }
        fields.truncate(base);
        self.extras.fields = fields;
        let nil = |c: &Checker, rest: Ty| {
            let node = c.g.nodes[rest.0 as usize];
            node.head & EXTENDED != 0 && c.extras.descriptors[node.a as usize] == ExtraDescriptor::Nil
        };
        if (miss1 && nil(self, rest2)) || (miss2 && nil(self, rest1)) {
            return Err(Clash);
        }
        Ok(())
    }

    /// `mcomp_row` (compiler/ml/ctype.ml:1983-2009) of two variant nodes:
    /// both opened and flattened ([`Checker::flatten_row`]) and merged
    /// ([`Checker::merge_rows`]); a clash when a closed row lacks a tag
    /// the other has present; then, per common tag in the merge's order,
    /// the table of ctype.ml:1996-2008: a clash, the pair of the two
    /// present types, or the present type against each type of the
    /// other's conjunction. O(tags + chains) plus the merge, one step a
    /// tag flattened, a merge step, a tag only one row has (when the
    /// other row is closed) and a common tag; no allocation once the
    /// scratch has the capacity; the scratch is cut back to where it
    /// was.
    fn mcomp_row(&mut self, left: Ty, right: Ty) -> Result<(), Clash> {
        let base = self.extras.row_scratch.len();
        let top1 = self.open_row(left);
        let (last1, _) = self.flatten_row(top1);
        let n1 = self.extras.row_scratch.len() - base;
        let top2 = self.open_row(right);
        let (last2, _) = self.flatten_row(top2);
        let n2 = self.extras.row_scratch.len() - base - n1;
        let closed = |c: &Checker, last: Ty, top: Node| {
            let node = if last.0 == NONE { top } else { c.g.nodes[last.0 as usize] };
            let ExtraDescriptor::Variant(row) = c.extras.descriptors[node.a as usize] else {
                unreachable!("a variant node");
            };
            c.extras.variants[row as usize].closed
        };
        let (closed1, closed2) = (closed(self, last1, top1), closed(self, last2, top2));
        let pairs = self.merge_rows(base, n1);
        let r1 = base..base + n1 - pairs;
        let r2 = r1.end..r1.end + n2 - pairs;
        let present = |c: &Checker, range: std::ops::Range<usize>| {
            range.into_iter().any(|at| {
                #[cfg(test)]
                super::steps::tick();
                c.field_now_at(at).kind == RowFieldKind::Present
            })
        };
        let mut result = if (closed1 && present(self, r2.clone())) || (closed2 && present(self, r1.clone())) {
            Err(Clash)
        } else {
            Ok(())
        };
        for k in 0..pairs {
            if result.is_err() {
                break;
            }
            #[cfg(test)]
            super::steps::tick();
            let at = r2.end + 2 * k;
            let (f1, f2) = (self.field_now_at(at), self.field_now_at(at + 1));
            result = match (mcomp_shape(f1), mcomp_shape(f2)) {
                (Shape::Present(false), Shape::Present(true) | Shape::Either { typed: true, .. } | Shape::Absent)
                | (Shape::Present(true), Shape::Present(false) | Shape::Either { constant: true, .. } | Shape::Absent)
                | (Shape::Either { typed: true, .. } | Shape::Absent, Shape::Present(false))
                | (Shape::Either { constant: true, .. } | Shape::Absent, Shape::Present(true)) => Err(Clash),
                (Shape::Present(true), Shape::Present(true)) => {
                    self.push_compatible(f1.first, f2.first);
                    Ok(())
                }
                (Shape::Present(true), Shape::Either { constant: false, .. }) => {
                    self.push_against(f1.first, at + 1);
                    Ok(())
                }
                (Shape::Either { constant: false, .. }, Shape::Present(true)) => {
                    self.push_against(f2.first, at);
                    Ok(())
                }
                _ => Ok(()),
            };
        }
        self.extras.row_scratch.truncate(base);
        result
    }

    /// The pairs of `single` and each type of the conjunction of the
    /// field `extras.row_scratch[at]` (`List.iter (mcomp t1) tl2`), in
    /// order. O(types + chain), no allocation.
    fn push_against(&mut self, single: Ty, at: usize) {
        let field = self.extras.row_scratch[at];
        let row_field = self.extras.row_fields[field.at as usize];
        let frames = &mut self.frames;
        each_field_types(&self.g, field.ty.0, u32::MAX, row_field, |types| {
            for &ty in types {
                frames.push(Frame { left: single, right: ty, kind: FrameKind::Pair, extra: 0 });
            }
        });
    }

}

// -----------------------------------------------------------------
// `instance_poly` and `instance_label` (R3q; CHECKER_REWRITE 8.10)
// -----------------------------------------------------------------
// R3q removes this `allow` with its last `todo!`.
#[allow(unused_variables, dead_code)]
impl Checker {
    /// `instance_poly ?keep_names ~fixed univars sch`
    /// (compiler/ml/ctype.ml:1081-1095) for the polymorphic type node
    /// `poly` (`Tpoly (sch, univars)`: slot 0 the body, slots 1.. the
    /// bound variables; every caller of OCaml's passes the two parts of
    /// one `Tpoly`): the instance of the body, and one new variable for
    /// each bound variable pushed on `vars` in order (named as the
    /// universal variable when `keep_names`, ctype.ml:1085-1086; at the
    /// current level).
    ///
    /// Three parts, in this order:
    /// 1. `Checker::mark_holders` (`compute_univars sch`);
    /// 2. the new variables, each the copy of its universal variable in
    ///    [`PolySlot::copy`] (`pairs`, ctype.ml:1090), then
    ///    `Checker::copy_sep` of the body; the pairs are taken out
    ///    again;
    /// 3. `Checker::poly_session` with no result: the delayed copies
    ///    (`List.iter Lazy.force !delayed_copy`, ctype.ml:1093).
    ///
    /// Cost: the three parts. Linear in the nodes below the body for a
    /// body in which no node that holds a universal variable is reached
    /// by two paths; such a node is copied once per path, as in OCaml
    /// ("Copy without sharing until there are no free univars left",
    /// ctype.ml:1030). A unit that never calls it pays nothing: the
    /// tables of [`PolyCopy`] are empty until the first call.
    pub fn instance_poly(&mut self, fixed: bool, keep_names: bool, poly: Ty, vars: &mut Vec<Ty>) -> Ty {
        todo!("R3q")
    }

    /// `instance_label fixed lbl` (compiler/ml/ctype.ml:1097-1105): the
    /// instances of a label's argument type and of its record type, made
    /// in ONE copy session, so that a generic node both reach is one node
    /// in both instances (the record's parameters). Returns `(argument,
    /// result)`; when the argument is a polymorphic type its new
    /// variables are pushed on `vars` (`instance_poly ~fixed tl ty`,
    /// 1102), otherwise nothing is.
    ///
    /// - The argument is not a polymorphic type (its representative is
    ///   not a `Poly` node): [`Graph::copy_begin`], `copy_ref(result)`,
    ///   `copy_ref(argument)` (OCaml copies the result first, 1099),
    ///   [`Graph::copy_drain`], then the pass of
    ///   `Checker::poly_session` over the nodes made. No table of
    ///   [`PolyCopy`] is touched and no stub is made: this is the label
    ///   of every record field without a polymorphic type.
    /// - It is one: parts 1 and 2 of [`Checker::instance_poly`] (with
    ///   `keep_names` false), then `Checker::poly_session` with
    ///   `result`, whose copy is made first in the session. The walk
    ///   comes before the copy of the result where OCaml's comes after
    ///   it; the two share nodes only through the session, so the order
    ///   cannot be seen.
    ///
    /// Cost: one copy of the two types, plus [`Checker::instance_poly`]'s
    /// for a polymorphic argument.
    pub fn instance_label(&mut self, fixed: bool, argument: Ty, result: Ty, vars: &mut Vec<Ty>) -> (Ty, Ty) {
        todo!("R3q")
    }

    /// Start a call: [`PolyCopy::slots`] grown to the graph (new rows
    /// have no stamp and no copy), a new [`PolyCopy::call`], the pools
    /// and the depth emptied. When the call counter would overflow the
    /// stamps (`2 * call + 1`), every stamp is cleared once. O(1)
    /// amortized.
    fn poly_begin(&mut self) {
        todo!("R3q")
    }

    /// Parts 1 and 2 of [`Checker::instance_poly`] for the `Poly` node
    /// `poly`, after [`Checker::poly_begin`]. Its cost is theirs.
    fn poly_walk(&mut self, fixed: bool, keep_names: bool, poly: Ty, vars: &mut Vec<Ty>) -> Ty {
        todo!("R3q")
    }

    /// `compute_univars sch` (compiler/ml/ctype.ml:693-713), as far as
    /// [`Checker::copy_sep`] reads it: for every node below `body`,
    /// whether a universal variable is FREE below it (one that is not
    /// bound by a polymorphic type on the way from the node to it:
    /// `| Tpoly (_ty, tl) when List.memq univ (List.map repr tl) -> ()`,
    /// 699). `poly` is the descriptor of the node whose body `body` is.
    /// The answer is [`PolySlot::stamp`] `== 2 * call + 1`.
    ///
    /// Two steps, as OCaml's:
    /// - *the inverse graph* (`inv_type`, 680-691): a walk from `body` on
    ///   `g.work` that meets each representative once (its stamp becomes
    ///   `2 * call`) and pushes one [`PolyEdge`] for each child slot of
    ///   each node (`Checker::child`: every slot of an extended node, the
    ///   bound variables of a polymorphic type included). A polymorphic
    ///   type with bound variables is pushed on [`PolyCopy::binders`].
    /// - *the propagation* (`add_univar`, 696-707), one CLASS at a time:
    ///   first the bound variables of `poly` (no binder below `body`
    ///   stops them), then those of each binder met, in the order met.
    ///   For one class, one new generation of `marks`: from each of its
    ///   variables that the first step met, up the edges, never through
    ///   the class's own binder, each node once; every node reached, the
    ///   variable included, gets the stamp `2 * call + 1`. A node that
    ///   another class marked is NOT a place to stop: a variable of an
    ///   outer binder is free further up than one of an inner binder.
    ///
    /// Cost: one step a node and one edge (8 bytes) a child slot for the
    /// first step; for the second, one step a node for each class that
    /// has a variable free below it: linear for a body without a
    /// polymorphic type inside, at most nodes times the depth of nested
    /// binders otherwise (OCaml keeps a set of variables a node: the same
    /// bound with a set operation a step).
    fn mark_holders(&mut self, poly: Node, body: Ty) {
        todo!("R3q")
    }

    /// `copy_sep fixed free bound visited ty` (compiler/ml/ctype.ml:
    /// 1033-1079) for `root`, after [`Checker::mark_holders`]: the copy.
    /// A loop over [`Checker::frames`] above the length it finds, no
    /// recursion:
    /// - `root` goes to [`Checker::sep_child`], whose answer is the
    ///   result;
    /// - a [`FrameKind::Pair`] frame (`left` a source node, `right` the
    ///   stub of its copy) goes to [`Checker::sep_fill`];
    /// - a [`FrameKind::Linked`] frame puts `right` and `extra` back as
    ///   the [`PolySlot::copy`] and [`PolySlot::depth`] of `left`: the
    ///   node, or the bound variable, is off the way again (OCaml's
    ///   `visited` is an argument: what a call adds is gone when it
    ///   returns);
    /// - a [`FrameKind::LeavePoly`] frame puts `extra` back as
    ///   [`PolyCopy::depth`].
    ///
    /// A frame's children are filled after it and before the frames
    /// below it, so the `Linked` frames on the stack are exactly the
    /// nodes on the way to the node being filled. Cost: one step a node
    /// filled; three frames at most a node (16 bytes each); what
    /// [`Checker::sep_fill`] makes.
    fn copy_sep(&mut self, fixed: bool, root: Ty) -> Ty {
        todo!("R3q")
    }

    /// The first lines of `copy_sep` for one child (compiler/ml/ctype.ml:
    /// 1034-1049): what stands for `child` in the copy. Per
    /// representative `c`:
    /// - no universal variable is free below it (its stamp is not `2 *
    ///   call + 1`): `c` itself when it is not generic (1037); otherwise
    ///   a new variable at the current level, pushed with `c` on
    ///   [`PolyCopy::delayed`] (`delayed_copy`, 1039-1041:
    ///   [`Checker::poly_session`] makes it a link to the copy);
    /// - it has a [`PolySlot::copy`] (it is on the way, or it is a bound
    ///   variable): that copy (`List.assq ty visited`, 1044), unless a
    ///   binder was entered since ([`PolySlot::depth`] is below
    ///   [`PolyCopy::depth`]), `c` is not a universal variable (`if
    ///   is_Tunivar ty then []`, 1045) and [`Checker::sep_conflicts`]
    ///   holds (1046): then it is copied again;
    /// - otherwise a new variable at the current level, the stub (`let t
    ///   = newvar ()`, 1049), and a [`FrameKind::Pair`] frame of `c` and
    ///   the stub.
    ///
    /// O(1) besides `sep_conflicts`: one `repr`, one [`PolySlot`] load
    /// and, for a node that is copied, one node and one frame.
    fn sep_child(&mut self, child: Ty) -> Ty {
        todo!("R3q")
    }

    /// `conflicts univars dl` (compiler/ml/ctype.ml:1046, 1023-1025) for
    /// `c`, a node on the way that is met again after a binder was
    /// entered: whether a variable bound SINCE `c` was entered is free in
    /// `c`. The binders entered since are the [`FrameKind::LeavePoly`]
    /// frames above the topmost [`FrameKind::Linked`] frame of `c`
    /// (`left` of a `LeavePoly` frame is the polymorphic type). For each,
    /// one new generation of `marks` and a walk on `g.work` above the
    /// length it finds: from its bound variables up the edges of
    /// [`Checker::mark_holders`], never through the binder; `c` reached
    /// is "free". When it holds OCaml copies the node again, with the
    /// new binding; when a node is its own way back to the binder with
    /// nothing between, OCaml does not end, and neither does this.
    ///
    /// Cost: one step a frame scanned and a node walked: for each binder
    /// entered since, the nodes its variables are free in. Reached only
    /// by a type that reaches itself through a polymorphic type.
    fn sep_conflicts(&mut self, c: Ty) -> bool {
        todo!("R3q")
    }

    /// The rest of `copy_sep` for one node (compiler/ml/ctype.ml:
    /// 1049-1079): `stub` becomes the copy of `c`, a node below which a
    /// universal variable is free, at the current level.
    ///
    /// First the way (`(ty, (t, bound)) :: visited`, 1052-1056): for an
    /// arrow, a tuple, a constructor, an object, a variant and a package
    /// (and for no other node: a field, a polymorphic type and a
    /// universal variable are not in `visited`), a [`FrameKind::Linked`]
    /// frame with the [`PolySlot::copy`] and [`PolySlot::depth`] `c` had,
    /// and then `stub` and [`PolyCopy::depth`] in their place.
    ///
    /// Then the descriptor, each child through [`Checker::sep_child`]:
    /// - an arrow: the result, then the parameters, into new `Param`
    ///   rows (label and location kept);
    /// - a tuple, a constructor (a new empty memo slot: `ref Mnil`,
    ///   btype.ml:514): a new list;
    /// - a polymorphic type (1070-1077): a [`FrameKind::LeavePoly`] frame
    ///   (`left` the node `c`, `extra` the depth) and the depth one more;
    ///   for each bound variable a new node with the variable's
    ///   descriptor at the current level (`newty t.desc`), a `Linked`
    ///   frame with the slot the variable had, and the new node and the
    ///   depth as its slot; then the body; a new list, the body in slot
    ///   0;
    /// - a variant: [`Checker::copy_sep_row`];
    /// - any other extended node (an object, a field, a package, a
    ///   universal variable no binder on the way binds): a new list, the
    ///   descriptor row shared; a field is pushed on
    ///   [`PolyCopy::fields`], for the cells.
    ///
    /// One step; one list or `Param` slot a child; no trail entry (the
    /// stub is a node of this call).
    fn sep_fill(&mut self, fixed: bool, c: Ty, stub: Ty) {
        todo!("R3q")
    }

    /// The variant arm of `copy_sep` (compiler/ml/ctype.ml:1061-1069)
    /// with `copy_row` (compiler/ml/btype.ml:366-392) for variant node
    /// `c`, whose descriptor is `node`: the descriptor of its copy, ONE
    /// row of every field of its chain (`row_repr`, btype.ml:126-135),
    /// at the current level.
    ///
    /// ```text
    /// | Tvariant row0 ->
    ///   let row = row_repr row0 in
    ///   let more = repr row.row_more in
    ///   (* We shall really check the level on the row variable *)
    ///   let keep = is_Tvar more && more.level <> generic_level in
    ///   let more' = copy_rec more in
    ///   let fixed' = fixed && is_Tvar (repr more') in
    ///   let row = copy_row copy_rec fixed' row keep more' in
    ///   Tvariant row
    /// ```
    ///
    /// The chain is read and not opened ([`field_repr`] with each
    /// node's own arity; `each_field_types` for the types of a `Reither`
    /// field), twice: once to its end for the last row (its `closed`,
    /// `fixed`, name and `more`), once for the fields.
    /// - `keep`: the representative of the last `more` is a variable
    ///   that is not generic.
    /// - `more'` is [`Checker::sep_child`] of it, and `fixed'` is `fixed`
    ///   and "`more'` is a variable node now" (a stub is one: OCaml reads
    ///   `is_Tvar` before the delayed copy is linked).
    /// - The slots: `more'`, the copies of the name's arguments, then
    ///   the copies of the types of each field in order: one for
    ///   `Rpresent (Some _)`, all of `tl` for `Reither`.
    /// - A new `RowFieldRow` a field with what the field reads NOW:
    ///   `Present`, `Absent`, or `Either` with its `c` and `m`, where `m`
    ///   is `fixed'` when the source row is fixed (`let m = if
    ///   row.row_fixed then fixed else m`, btype.ml:375). A new
    ///   `VariantRow` with the last row's `closed` and name and `fixed =
    ///   row.row_fixed && fixed'` (btype.ml:389), and a new descriptor
    ///   row.
    /// - Not `keep`: the node is UNOPENED: each `Reither` field stands
    ///   for a reference of its own (`let e = if keep then e else ref
    ///   None`, btype.ml:374).
    /// - `keep`, and the row has a `Reither` field: the copy shares each
    ///   field's reference. The home of the field is opened when it is
    ///   not ([`Checker::open_row`], and the references that made get the
    ///   level of the row variable, as in `Checker::copy_refs`); the copy
    ///   is built opened: a field without types has the source's
    ///   unresolved reference in its reference slot, one with types a
    ///   new [`RES_EITHER`] node with its `c` and `m`, its copied types
    ///   and that reference, in its reference slot and in each of its
    ///   type slots, and it is a holder of the reference
    ///   (`Checker::hold`).
    ///
    /// O(fields + chain + types), one step a field; [`PolyCopy::types`]
    /// above the length it finds is the scratch of the types of one
    /// field. Per
    /// field one `RowFieldRow` (20 bytes) and one slot a type; with
    /// `keep`, per `Reither` field with types one node, its slots and 8
    /// bytes of holder.
    fn copy_sep_row(&mut self, fixed: bool, c: Ty, node: Node) -> Node {
        todo!("R3q")
    }

    /// The copy session of [`Checker::instance_poly`] and
    /// [`Checker::instance_label`], after the walk
    /// (`with_copy_session`; `List.iter Lazy.force !delayed_copy`,
    /// compiler/ml/ctype.ml:1093): [`Graph::copy_begin`]; the copy of
    /// `result` when it is not `NONE` (returned; `NONE` otherwise); for
    /// each pair of [`PolyCopy::delayed`], in order, `copy_ref` of the
    /// source and the stub written as a link to it (`t.desc <- Tlink
    /// (copy ty)`; the stub is this call's: a plain store);
    /// [`Graph::copy_drain`]; then [`Checker::poly_pass`] over the nodes
    /// the session made. The session comes after the walk so that its
    /// nodes are the last and in the order of its queue, which
    /// `Checker::copy_refs` reads. Cost: one [`Checker::copy`] of all the
    /// roots.
    fn poly_session(&mut self, result: Ty) -> Ty {
        todo!("R3q")
    }

    /// The pass of [`Checker::copy`] over the nodes a session made since
    /// `first`, in one cell session with the fields the walk made:
    /// nothing when no memorized expansion is live and the graph has no
    /// descriptor row; otherwise `begin_cell_session`, `extras.copying`
    /// set, `Checker::memorized_node` for each node of the session
    /// (the memo of constructors without arguments, the cells of copied
    /// fields, the references of copied rows), `extras.copying` cleared,
    /// then [`Checker::dup_cell`] for each node of [`PolyCopy::fields`]
    /// (`copy_type_desc` for `Tfield`, compiler/ml/btype.ml:516-532: the
    /// cell is duplicated when the row ends in a generic variable, which
    /// is when the copy's row ends in a variable the session made; a
    /// class the session duplicated already is found through its
    /// temporary link), and `end_cell_session`. Cost: one step a node of
    /// the session and what `dup_cell` says a field.
    fn poly_pass(&mut self, first: usize) {
        todo!("R3q")
    }
}

/// A field of a row as the table of `mcomp_row` reads it
/// (compiler/ml/ctype.ml:1996-2007): `Rpresent` with or without a type,
/// `Reither` with its `c` and whether it has a type, `Rabsent`.
#[derive(Clone, Copy)]
enum Shape {
    Present(bool),
    Either { constant: bool, typed: bool },
    Absent,
}

/// O(1): the [`Shape`] of a field read now.
fn mcomp_shape(field: FieldRepr) -> Shape {
    match field.kind {
        RowFieldKind::Present => Shape::Present(field.first.0 != NONE),
        RowFieldKind::Either { constant, .. } => Shape::Either { constant, typed: field.types != 0 },
        RowFieldKind::Absent => Shape::Absent,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sizes_of_the_instance_of_a_polymorphic_type() {
        // One a node of the graph, and one a child slot of a body.
        assert_eq!(std::mem::size_of::<PolySlot>(), 16);
        assert_eq!(std::mem::size_of::<PolyEdge>(), 8);
    }

    #[test]
    fn sizes() {
        assert_eq!(std::mem::size_of::<FieldRef>(), 12);
        assert_eq!(std::mem::size_of::<Holder>(), 8);
        assert_eq!(std::mem::size_of::<FieldRepr>(), 16);
        // One per equation in force (CHECKER_REWRITE 8.9, decision 67).
        assert_eq!(std::mem::size_of::<Equation>(), 20);
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
        let node = add_row(&mut c, 0..n, typed, kind);
        (c, node)
    }

    /// An open row of the tags `names` (named `f00000` and up) on `c`, as
    /// [`row_of`] makes one.
    fn add_row(c: &mut Checker, names: std::ops::Range<u32>, typed: bool, kind: impl Fn(u32) -> RowFieldKind) -> Ty {
        let ty = push(&mut c.g, CONSTR, 0, &[]);
        let mut slots = Vec::new();
        let first = c.extras.row_fields.len();
        for k in names.clone() {
            while c.extras.names.spans.len() <= k as usize {
                let start = c.extras.names.bytes.len() as u32;
                let text = format!("f{:05}", c.extras.names.spans.len());
                c.extras.names.bytes.extend_from_slice(text.as_bytes());
                c.extras.names.spans.push(Range { start, len: 6 });
            }
            let types = Range { start: slots.len() as u32, len: u32::from(typed) };
            if typed {
                slots.push(ty);
            }
            c.extras.row_fields.push(RowFieldRow { name: k, types, link: NONE, kind: kind(k) });
        }
        let more = slots.len() as u32;
        slots.push(push(&mut c.g, VAR, NONE, &[]));
        let row = VariantRow {
            fields: Range { start: first as u32, len: names.len() as u32 },
            more,
            name: NONE,
            name_arguments: Range::default(),
            closed: false,
            fixed: false,
        };
        let mut slot = published_slots(row, &c.extras.row_fields);
        for field in &mut c.extras.row_fields[first..] {
            if matches!(field.kind, RowFieldKind::Either { .. }) {
                field.link = slot;
                slot += 1;
            }
        }
        let index = c.extras.variants.len() as u32;
        c.extras.variants.push(row);
        let descriptor = c.extras.descriptors.len() as u32;
        c.extras.descriptors.push(ExtraDescriptor::Variant(index));
        push(&mut c.g, TUPLE | EXTENDED, descriptor, &slots)
    }

    /// Two open rows of 10,000 tags each, none in common: each row gains
    /// the other's 10,000 in one node. Steps: two flattenings, the merge,
    /// one a field of each rest and the lowering of the two new rows; at
    /// most 7 a tag.
    #[test]
    fn rows_that_gain_ten_thousand_tags_make_one_node_each() {
        let mut c = Checker::new(Graph::default(), Default::default());
        let present = |_| RowFieldKind::Present;
        let left = add_row(&mut c, 0..10_000, true, present);
        let right = add_row(&mut c, 10_000..20_000, true, present);
        let nodes = c.g.nodes.len();
        let steps = super::super::steps::scope(|| c.unify(left, right).unwrap());
        assert_eq!(c.g.nodes.len() - nodes, 3, "a variable and two rows");
        assert!(steps <= 7 * 20_000, "{steps}");
    }

    /// A reference held by 10,000 chain nodes, resolved to absent: one
    /// step a holder, and each holder stops being a parent of its type.
    #[test]
    fn settling_ten_thousand_holders_is_one_step_a_holder() {
        let mut c = Checker::new(Graph::default(), Default::default());
        let ty = push(&mut c.g, VAR, NONE, &[]);
        let end = c.g.push(ref_node(1, NONE));
        let mut head = NONE;
        let mut chains = Vec::new();
        for _ in 0..10_000 {
            let chain = push(&mut c.g, TUPLE, RES_EITHER, &[ty, end]);
            c.extras.holders.push(Holder { node: chain, next: head });
            head = c.extras.holders.len() as u32 - 1;
            chains.push(chain);
        }
        c.g.nodes[end.0 as usize].b = head;
        let steps = super::super::steps::scope(|| {
            let holders = c.resolve(end, RES_ABSENT, Ty(NONE));
            c.settle(holders, RES_ABSENT);
        });
        assert_eq!(steps, 10_000);
        for chain in chains {
            let node = c.g.nodes[chain.0 as usize];
            assert_eq!((node.a, node.arity()), (RES_ABSENT, 0));
        }
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

    /// The four cases of `copy_refs` on a row of 10,000 `Reither` fields
    /// with a type each: one step a field (the first case none), besides
    /// the copy's own step a node and the pass's. Unopened source, generic
    /// `more`: nothing. Unopened, shared `more`: the source is opened and
    /// the copy shares its references. Opened, shared `more`: a copy's
    /// chain ends in the source's reference and holds it. Opened, generic
    /// `more`: each field gets a reference of its own.
    #[test]
    fn copying_ten_thousand_references_is_one_step_a_field() {
        let either = |_| RowFieldKind::Either { constant: false, matched: false };
        let reference = |c: &Checker, ty: Ty, k: u32| {
            let node = c.g.nodes[ty.0 as usize];
            let field = c.extras.row_fields[k as usize];
            field_repr(&c.g, node.b, node.arity(), field).end
        };
        let holders = |c: &Checker, end: Ty| {
            let (mut count, mut at) = (0, c.g.nodes[end.0 as usize].b);
            while at != NONE {
                count += 1;
                at = c.extras.holders[at as usize].next;
            }
            count
        };
        let (mut c, ty) = row_of(10_000, true, either);
        let more = Ty(ty.0 - 1);
        c.g.nodes[ty.0 as usize].level = GENERIC;
        c.g.nodes[more.0 as usize].level = GENERIC;
        let mut copied = ty;
        assert_eq!(super::super::steps::scope(|| copied = c.copy(ty)), 2 + 2);
        assert!(c.g.nodes[copied.0 as usize].arity() < 20_001, "unopened");
        // Shared `more`, unopened source.
        c.g.nodes[more.0 as usize].level = 1;
        assert_eq!(super::super::steps::scope(|| copied = c.copy(ty)), 1 + 1 + 10_000);
        assert_eq!(c.g.nodes[ty.0 as usize].arity(), 20_001);
        for k in [0, 9_999] {
            let end = reference(&c, ty, k);
            assert_eq!((reference(&c, copied, k), c.g.nodes[end.0 as usize].level), (end, 1));
            assert_eq!(holders(&c, end), 2);
        }
        // Shared `more`, opened source: the chain nodes are copied.
        assert_eq!(super::super::steps::scope(|| copied = c.copy(ty)), 2 * 10_001 + 10_000);
        for k in [0, 9_999] {
            let end = reference(&c, ty, k);
            assert_eq!((reference(&c, copied, k), holders(&c, end)), (end, 3));
        }
        // Generic `more`, opened source: the references are copied too.
        let (mut c, ty) = row_of(10_000, true, either);
        c.g.nodes[ty.0 as usize].level = GENERIC;
        c.g.nodes[ty.0 as usize - 1].level = GENERIC;
        c.open_row(ty);
        assert_eq!(super::super::steps::scope(|| copied = c.copy(ty)), 2 * 20_002 + 10_000);
        let mut ends: Vec<u32> = (0..10_000).map(|k| reference(&c, copied, k).0).collect();
        for &end in &ends {
            assert_eq!((c.g.nodes[end as usize].level, holders(&c, Ty(end))), (c.g.level, 1));
        }
        ends.sort();
        ends.dedup();
        assert_eq!(ends.len(), 10_000);
        assert_ne!(reference(&c, ty, 0), reference(&c, copied, 0));
    }

    /// A chain of `n` variant nodes, each with the one tag `f(i)` and
    /// its row variable linked to the next, at level 2; the first node
    /// and the last. With `named` the last row has the name of type 0,
    /// whose scope is `scope`.
    fn chain_of_rows(n: u32, scope: Option<u32>) -> (Checker, Ty, Ty) {
        let mut c = Checker::new(Graph::default(), Default::default());
        let last = add_row(&mut c, 0..1, false, |_| RowFieldKind::Present);
        if let Some(scope) = scope {
            let row = c.extras.variants.len() - 1;
            c.extras.variants[row].name = 0;
            c.types.rows.push(TypeInfo { manifest: NONE, scope, newtype: NONE, arity: 0, flags: 0, reserved: 0 });
        }
        let mut first = last;
        for i in 1..n {
            let node = add_row(&mut c, i..i + 1, false, |_| RowFieldKind::Present);
            c.g.link(Ty(node.0 - 1), first);
            first = node;
        }
        for node in &mut c.g.nodes {
            node.level = 2;
        }
        c.types.scoped = 1;
        c.g.level = 2;
        (c, first, last)
    }

    /// The loops of the variant arm of a lowering, as relations between
    /// 1,000 and 10,000 (`update_level`, compiler/ml/ctype.ml:615-623;
    /// `iter_row`, btype.ml:229-241, which walks a `more` that is a
    /// variant IN LINE and does not hand the inner node to
    /// `update_level`):
    ///
    /// - `lower_row_name` over a chain of n variant nodes whose name
    ///   does not escape (and one without a name): linear. Seen to fail
    ///   before the inner nodes were skipped (each inner node the walk
    ///   visited read the chain to its end: 1,002,000 steps at 1,000
    ///   and 100,020,000 at 10,000). The inner nodes
    ///   keep their level, as in OCaml; the row variable at the end is
    ///   lowered.
    /// - `unname_row` over the same chain when the name escapes: one
    ///   row of n fields, linear.
    #[test]
    fn lowering_a_chain_of_ten_thousand_rows_is_linear() {
        let run = |n: u32, scope: Option<u32>| {
            let (mut c, first, last) = chain_of_rows(n, scope);
            let steps = super::super::steps::scope(|| c.lower(first, 1).unwrap());
            let more = c.g.repr(Ty(last.0 - 1));
            assert_eq!(c.g.nodes[first.0 as usize].level, 1);
            assert_eq!(c.g.nodes[more.0 as usize].level, 1);
            let escaped = scope == Some(2);
            let node = c.g.nodes[first.0 as usize];
            let ExtraDescriptor::Variant(row) = c.extras.descriptors[node.a as usize] else {
                unreachable!("a variant node");
            };
            let row = c.extras.variants[row as usize];
            // The name is dropped, and the node is one row of n fields.
            assert_eq!(row.fields.len, if escaped { n } else { 1 });
            assert_eq!(row.name, NONE);
            if !escaped && n > 1 {
                // `iter_row` does not hand an inner node to `update_level`.
                assert_eq!(c.g.nodes[last.0 as usize].level, 2);
            }
            steps
        };
        for scope in [None, Some(1), Some(2)] {
            let (small, large) = (run(1_000, scope), run(10_000, scope));
            assert!(large <= 11 * small, "{scope:?}: {small} {large}");
        }
    }

    /// `match_fixed_fields` over the copy of a fixed row of n `Reither`
    /// fields that read matched (`let m = if row.row_fixed then fixed
    /// else m`, compiler/ml/btype.ml:375): one step a field, linear
    /// between 1,000 and 10,000, and `match_unmatched` is not reached
    /// (no node beyond the copy's own).
    #[test]
    fn matching_the_fields_of_a_fixed_row_is_one_step_a_field() {
        let run = |n: u32| {
            let either = |_| RowFieldKind::Either { constant: false, matched: true };
            let (mut c, ty) = row_of(n, true, either);
            let row = c.extras.variants.len() - 1;
            c.extras.variants[row].fixed = true;
            c.g.nodes[ty.0 as usize].level = GENERIC;
            c.g.nodes[ty.0 as usize - 1].level = GENERIC;
            let nodes = c.g.nodes.len();
            let mut copied = ty;
            let steps = super::super::steps::scope(|| copied = c.copy(ty));
            assert_ne!(copied, ty);
            let made = c.g.nodes.len() - nodes;
            (steps, made)
        };
        let (small, large) = (run(1_000), run(10_000));
        assert!(large.0 <= 11 * small.0, "{small:?} {large:?}");
        assert!(small.0 >= 1_000 && large.0 >= 10_000, "{small:?} {large:?}");
        assert_eq!(small.1, large.1, "nodes made do not grow with the fields");
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
