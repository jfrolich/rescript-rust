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

use super::graph::{Graph, LINK, Mode, NONE, Node, TUPLE, Ty, VAR};
use super::segment::{
    EXTENDED, ExtraDescriptor, PackageRow, Range, RowFieldRow, Segment, VariantRow,
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
    pub ty: Ty,
}

impl Extras {
    /// O(rows of the segment): one bulk copy per pool, one cell node
    /// pushed on `g` per cell of the segment ([`cell_node`]; a frozen cell
    /// holds its value and links to nothing), and one pass over the
    /// descriptors that turns each field's cell index into that node's
    /// handle. The indices of a segment's rows are the indices here, so the
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
        Extras {
            descriptors,
            variants: pools.variants.to_vec(),
            row_fields: pools.row_fields.to_vec(),
            packages: pools.packages.to_vec(),
            names: NameTexts {
                bytes: pools.bytes.to_vec(),
                spans: pools.strings.to_vec(),
            },
            fields: Vec::new(),
            session: Vec::new(),
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
    /// O(1) plus the callee. (R3e)
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
    }
}
