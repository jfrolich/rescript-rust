//! Typed reads of a [`Segment`]'s pools, and the overlay of the changes the
//! old printer makes to the graph while it prints.
//!
//! # Handles
//!
//! A node is an [`N`], a dense index over three ranges: the segment's shared
//! nodes (`0..shared`), then every template node (`shared..real`, absolute in
//! `template_nodes`), then nodes this printer makes (`real..`). Every table
//! keyed by node is a dense `Vec` over that range.
//!
//! # The overlay
//!
//! types/canonical_sig.rs prints a signature through `Printtyp`, which
//! changes the graph it prints: `mark_loops` normalizes rows and objects
//! (compiler-rust/src/types/ctype.rs `normalize_type`), `filter_params`,
//! `unalias` and the variant-name hack allocate nodes, and
//! `tree_of_type_decl` drops the name of a `_` parameter. The structural
//! `== items` section is printed after, from the changed graph. A segment
//! is immutable, so those changes are recorded here, per node, and every
//! read goes through [`Graph::desc`].

use crate::tc::graph::{ARROW, CONSTR, NONE, Node, TUPLE, VAR};
use crate::tc::segment::{
    EXTENDED, ExtraDescriptor, IdentRow, LongidentRow, PathRow, Range, RowFieldKind, SchemeRoot,
    Segment, SignaturePools,
};

/// Template reference flag of a node relative to its template's first node
/// (tc/template.rs `Template`).
pub(super) const RELATIVE: u32 = 1 << 30;

/// A node: dense over shared, template and printer-made nodes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(super) struct N(pub u32);

/// A stored node's logical child list. The node determines its pool and
/// offset, keeping a descriptor passed down the walk within sixteen bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct Slots {
    node: N,
    pub len: u32,
}

/// A descriptor as the old `TypeDesc` reads, children resolved to nodes.
/// `Variant`'s row is read with [`Graph::row`].
#[derive(Clone, Copy, Debug)]
pub(super) enum Desc {
    Var(u32),
    Univar(u32),
    Nil,
    Subst(N),
    Arrow {
        params: Slots,
        ret: N,
    },
    Tuple(Slots),
    /// `trim`: the path's last name without its `#row` suffix (a private
    /// row type renamed by normalization).
    Constr {
        path: u32,
        trim: bool,
        args: Slots,
    },
    Object(N),
    Field {
        name: u32,
        mutable: bool,
        typ: N,
        rest: N,
    },
    Poly {
        body: N,
        vars: Slots,
    },
    Variant,
    Package {
        row: u32,
        args: Slots,
    },
}

/// A flattened row (`Btype.row_repr`): `fields` index [`Graph::fields`],
/// `name_args` index [`Graph::ns`]; `name` is a path row or NONE.
#[derive(Clone, Copy, Debug)]
pub(super) struct Row {
    pub fields: Range,
    pub name_args: Range,
    pub more: N,
    pub name: u32,
    pub closed: bool,
    pub fixed: bool,
}

/// One row field: `types` index [`Graph::ns`].
#[derive(Clone, Copy, Debug)]
pub(super) struct FieldV {
    pub label: u32,
    pub types: Range,
    pub kind: RowFieldKind,
}

/// A node the printer made. Sixteen bytes.
#[derive(Clone, Copy, Debug)]
enum Virtual {
    /// A field of a rebuilt (sorted) object chain.
    Field {
        name: u32,
        typ: N,
        rest: N,
        mutable: bool,
    },
    /// `filter_params`'s `Tsubst` of a repeated parameter.
    Subst(N),
    /// `newty2 level desc`: a shallow copy with its own identity.
    Copy { base: N, level: u32 },
    /// A fresh `Tvar None`.
    FreshVar { level: u32 },
    /// A variant; its row is in `Graph::row_of`.
    Variant { level: u32 },
    /// `newty2 level (Tobject fields)`.
    Object { fields: N, level: u32 },
}

/// A change to an existing node's descriptor. Sixteen bytes.
#[derive(Clone, Copy, Debug)]
enum Override {
    /// `Tvar None` in place of `Tvar (Some "_")`.
    Unnamed,
    Field {
        name: u32,
        typ: N,
        rest: N,
        mutable: bool,
    },
    /// The renamed private row type: the path of node `of`, trimmed.
    Constr { of: N },
    /// A normalized row, in `Graph::row_of`.
    Variant,
}

/// Immutable reads of one segment. Built in O(template nodes + templates).
pub(super) struct View<'s> {
    pub seg: &'s Segment,
    pub p: &'s SignaturePools,
    pub shared: u32,
    pub real: u32,
    /// Template index of each template node.
    owner: Box<[u32]>,
    /// Per template: its first slot of `template_lists`, of `template_params`.
    list_base: Box<[u32]>,
    param_base: Box<[u32]>,
}

impl<'s> View<'s> {
    /// O(templates + template nodes): template ranges are concatenated in
    /// template order (tc/publish.rs captures roots in order); list offsets
    /// are prefix sums of `list_len` and parameter offsets prefix sums of
    /// the arities of each template's arrows, which is what capture
    /// appends per template.
    pub fn new(seg: &'s Segment) -> Self {
        let mut owner = vec![NONE; seg.template_nodes.len()].into_boxed_slice();
        let mut list_base = Vec::with_capacity(seg.templates.len());
        let mut param_base = Vec::with_capacity(seg.templates.len());
        let (mut lists, mut params) = (0u32, 0u32);
        for (index, template) in seg.templates.iter().enumerate() {
            list_base.push(lists);
            param_base.push(params);
            lists += template.list_len;
            if template.node_len == 0 {
                continue;
            }
            let nodes = template.nodes as usize..(template.nodes + template.node_len) as usize;
            for (slot, node) in owner[nodes.clone()]
                .iter_mut()
                .zip(&seg.template_nodes[nodes])
            {
                *slot = index as u32;
                if node.tag() == ARROW {
                    params += node.arity();
                }
            }
        }
        let shared = u32::try_from(seg.nodes.len()).expect("segment node limit");
        let real = shared
            .checked_add(u32::try_from(seg.template_nodes.len()).expect("template node limit"))
            .filter(|real| *real < NONE / 2)
            .expect("segment node limit");
        View {
            seg,
            p: &seg.signature,
            shared,
            real,
            owner,
            list_base: list_base.into_boxed_slice(),
            param_base: param_base.into_boxed_slice(),
        }
    }

    /// O(1): a string of the pool.
    pub fn str(&self, index: u32) -> &'s str {
        let range = self.p.strings[index as usize];
        std::str::from_utf8(&self.p.bytes[range.start as usize..(range.start + range.len) as usize])
            .expect("segment strings are UTF-8")
    }

    /// O(1): a string, or `default` for NONE.
    pub fn opt_str(&self, index: u32) -> Option<&'s str> {
        (index != NONE).then(|| self.str(index))
    }

    /// O(1).
    pub fn ident(&self, row: u32) -> IdentRow {
        self.p.identifiers[row as usize]
    }

    /// O(1).
    pub fn path(&self, row: u32) -> PathRow {
        self.p.paths[row as usize]
    }

    /// O(1).
    pub fn longident(&self, row: u32) -> LongidentRow {
        self.p.longidents[row as usize]
    }

    /// O(1): `Ident.same` of two identifier rows: equal nonzero stamps, or
    /// two persistent identifiers of one name (compiler/ext/ident.ml:75).
    /// The stamps are compared, never printed.
    pub fn same_ident(&self, a: u32, b: u32) -> bool {
        let (a, b) = (self.ident(a), self.ident(b));
        if a.stamp != 0 {
            a.stamp == b.stamp
        } else {
            b.stamp == 0 && a.name == b.name
        }
    }

    /// O(path length), an explicit loop over the spine: `Path.same`, which
    /// ignores positions. `Papply` arguments are compared with a small stack.
    pub fn same_path(&self, a: u32, b: u32) -> bool {
        let mut work: smallvec::SmallVec<[(u32, u32); 8]> = smallvec::smallvec![(a, b)];
        while let Some((a, b)) = work.pop() {
            if a == b {
                continue;
            }
            match (self.path(a), self.path(b)) {
                (PathRow::Ident(x), PathRow::Ident(y)) => {
                    if !self.same_ident(x, y) {
                        return false;
                    }
                }
                (
                    PathRow::Dot {
                        parent: p, name: m, ..
                    },
                    PathRow::Dot {
                        parent: q, name: n, ..
                    },
                ) => {
                    if m != n {
                        return false;
                    }
                    work.push((p, q));
                }
                (
                    PathRow::Apply {
                        functor: f,
                        argument: x,
                    },
                    PathRow::Apply {
                        functor: g,
                        argument: y,
                    },
                ) => {
                    work.push((f, g));
                    work.push((x, y));
                }
                _ => return false,
            }
        }
        true
    }

    /// O(components), structural equality independent of metadata row indices.
    pub fn same_longident(&self, a: u32, b: u32) -> bool {
        let mut work = smallvec::smallvec![(a, b)];
        let work: &mut smallvec::SmallVec<[(u32, u32); 8]> = &mut work;
        while let Some((a, b)) = work.pop() {
            if a == b {
                continue;
            }
            match (self.longident(a), self.longident(b)) {
                (LongidentRow::Ident(a), LongidentRow::Ident(b)) if a == b => {}
                (LongidentRow::Unresolved(a), LongidentRow::Unresolved(b)) if a == b => {}
                (
                    LongidentRow::Dot { parent: a, name: x },
                    LongidentRow::Dot { parent: b, name: y },
                ) if x == y => work.push((a, b)),
                (
                    LongidentRow::UnresolvedDot { parent: a, raw: x },
                    LongidentRow::UnresolvedDot { parent: b, raw: y },
                ) if x == y => work.push((a, b)),
                (
                    LongidentRow::Apply {
                        functor: f,
                        argument: a,
                    },
                    LongidentRow::Apply {
                        functor: g,
                        argument: b,
                    },
                ) => {
                    work.push((f, g));
                    work.push((a, b));
                }
                _ => return false,
            }
        }
        true
    }

    /// O(1): the node a scheme root names.
    pub fn root(&self, root: SchemeRoot) -> N {
        if root.ty.0 & RELATIVE != 0 {
            let template = self.seg.templates[root.template as usize];
            N(self.seg.publication_node(
                self.shared + template.nodes + (root.ty.0 & !RELATIVE),
            ))
        } else {
            N(root.ty.0)
        }
    }

    /// O(1): the node of root row `index`.
    pub fn root_at(&self, index: u32) -> N {
        self.root(self.p.roots[index as usize])
    }

    /// O(1): the stored node of a shared or template node, with its owner.
    fn raw(&self, n: N) -> (Node, u32) {
        if n.0 < self.shared {
            (self.seg.nodes[n.0 as usize], NONE)
        } else {
            let index = (n.0 - self.shared) as usize;
            (
                crate::tc::template::descriptor(self.seg.template_nodes[index]),
                self.owner[index],
            )
        }
    }

    /// O(1): resolve a child reference of a node of `owner`. In a template a
    /// reference without bit 30 indexes `template_externals`, which hold
    /// shared nodes; a shared node's references are shared nodes.
    fn resolve(&self, owner: u32, reference: u32) -> N {
        if owner == NONE {
            N(reference)
        } else if reference & RELATIVE != 0 {
            let template = self.seg.templates[owner as usize];
            N(self.seg.publication_node(
                self.shared + template.nodes + (reference & !RELATIVE),
            ))
        } else {
            N(self.seg.template_externals[reference as usize].0)
        }
    }

    /// O(1): list slot `i` of `slots`.
    pub fn slot(&self, slots: Slots, i: u32) -> N {
        debug_assert!(i < slots.len);
        let (node, owner) = self.raw(slots.node);
        let offset = u32::from(
            node.tag() == CONSTR
                || (node.tag() == TUPLE
                    && node.head & EXTENDED != 0
                    && slots.len + 1 == node.arity()
                    && matches!(
                        self.p.descriptor_extras[node.a as usize],
                        ExtraDescriptor::Poly
                    )),
        );
        let index = (node.b
            + offset
            + i
            + if owner == NONE {
                0
            } else {
                self.list_base[owner as usize]
            }) as usize;
        let reference = if owner == NONE {
            self.seg.lists[index].0
        } else {
            self.seg.template_lists[index].0
        };
        self.resolve(owner, reference)
    }

    /// O(1): parameter label and type; no temporary owned label.
    pub fn param(&self, params: Slots, i: u32) -> (u32, N) {
        debug_assert!(i < params.len);
        let (node, owner) = self.raw(params.node);
        let index = (node.b
            + i
            + if owner == NONE {
                0
            } else {
                self.param_base[owner as usize]
            }) as usize;
        let param = if owner == NONE {
            self.seg.params[index]
        } else {
            self.seg.template_params[index]
        };
        (param.label, self.resolve(owner, param.ty.0))
    }

    /// O(1): the level of a shared or template node.
    fn level(&self, n: N) -> u32 {
        self.raw(n).0.level
    }

    /// O(1): the descriptor of a shared or template node (see tc/bridge/
    /// from_old.rs for the encoding).
    fn desc(&self, n: N) -> Desc {
        let (node, owner) = self.raw(n);
        let list = |len: u32| Slots { node: n, len };
        match node.tag() {
            VAR => Desc::Var(node.a),
            ARROW => Desc::Arrow {
                params: list(node.arity()),
                ret: self.resolve(owner, node.a),
            },
            CONSTR => Desc::Constr {
                path: node.a,
                trim: false,
                args: list(node.arity()),
            },
            TUPLE if node.head & EXTENDED == 0 => Desc::Tuple(list(node.arity())),
            TUPLE => {
                let slots = list(node.arity());
                let at = |i| self.slot(slots, i);
                match self.p.descriptor_extras[node.a as usize] {
                    ExtraDescriptor::Object => Desc::Object(at(0)),
                    ExtraDescriptor::Field { name, mutability } => Desc::Field {
                        name,
                        mutable: self.p.mutabilities[mutability as usize],
                        typ: at(0),
                        rest: at(1),
                    },
                    ExtraDescriptor::Nil => Desc::Nil,
                    ExtraDescriptor::Univar(name) => Desc::Univar(name),
                    ExtraDescriptor::Poly => Desc::Poly {
                        body: at(0),
                        vars: list(node.arity() - 1),
                    },
                    ExtraDescriptor::Variant(_) => Desc::Variant,
                    ExtraDescriptor::Package(row) => Desc::Package { row, args: slots },
                    ExtraDescriptor::Substitution => Desc::Subst(at(0)),
                }
            }
            tag => panic!("a published node has no descriptor tag {tag}"),
        }
    }

    /// O(1): a variant node's `variants` row and its slots.
    fn variant_row(&self, n: N) -> (crate::tc::segment::VariantRow, Slots) {
        let (node, _) = self.raw(n);
        let ExtraDescriptor::Variant(row) = self.p.descriptor_extras[node.a as usize] else {
            panic!("not a variant node");
        };
        (
            self.p.variants[row as usize],
            Slots {
                node: n,
                len: node.arity(),
            },
        )
    }
}

/// A dense set of nodes with O(1) clearing by epoch. Four bytes a node.
#[derive(Default)]
pub(super) struct Marks {
    stamps: Vec<u32>,
    epoch: u32,
}

impl Marks {
    /// O(1).
    pub fn clear(&mut self) {
        self.epoch = self.epoch.checked_add(1).expect("mark epoch exhausted");
    }

    /// O(1): whether `n` is in the set.
    pub fn has(&self, n: N) -> bool {
        self.epoch != 0 && self.stamps.get(n.0 as usize) == Some(&self.epoch)
    }

    /// Amortized O(1); table growth is O(new slots). Returns whether `n` was
    /// not in the set.
    pub fn insert(&mut self, n: N) -> bool {
        if self.epoch == 0 {
            self.epoch = 1;
        }
        let index = n.0 as usize;
        if index >= self.stamps.len() {
            self.stamps.resize((index + 1).next_power_of_two(), 0);
        }
        let fresh = self.stamps[index] != self.epoch;
        self.stamps[index] = self.epoch;
        fresh
    }

    /// O(1).
    pub fn remove(&mut self, n: N) {
        if let Some(slot) = self.stamps.get_mut(n.0 as usize) {
            *slot = 0;
        }
    }
}

/// The segment with the printer's overlay. Dense per-node tables cover the
/// real and the made nodes; they grow as nodes are made.
pub(super) struct Graph<'s> {
    pub v: View<'s>,
    virtuals: Vec<Virtual>,
    /// Per node: NONE or an `overrides` index.
    over: Vec<u32>,
    overrides: Vec<Override>,
    /// Per node: NONE or a `rows` index, for variants.
    row_of: Vec<u32>,
    pub rows: Vec<Row>,
    pub fields: Vec<FieldV>,
    pub ns: Vec<N>,
    /// Nodes `normalize` has rewritten (or visited); see normalize.rs.
    pub normalized: Marks,
}

impl<'s> Graph<'s> {
    /// O(real nodes): the dense tables.
    pub fn new(v: View<'s>) -> Self {
        let real = v.real as usize;
        Graph {
            v,
            virtuals: Vec::new(),
            over: vec![NONE; real],
            overrides: Vec::new(),
            row_of: vec![NONE; real],
            rows: Vec::new(),
            fields: Vec::new(),
            ns: Vec::new(),
            normalized: Marks::default(),
        }
    }

    /// Amortized O(1).
    fn make(&mut self, node: Virtual) -> N {
        let n = N(self.v.real + u32::try_from(self.virtuals.len()).expect("node limit"));
        assert!(n.0 < NONE / 2, "node limit");
        self.virtuals.push(node);
        self.over.push(NONE);
        self.row_of.push(NONE);
        n
    }

    /// O(1): a field node of a rebuilt object chain.
    pub fn make_field(&mut self, name: u32, mutable: bool, typ: N, rest: N) -> N {
        self.make(Virtual::Field {
            name,
            typ,
            rest,
            mutable,
        })
    }

    /// O(1): `newgenty (Tsubst ty)`.
    pub fn make_subst(&mut self, target: N) -> N {
        self.make(Virtual::Subst(target))
    }

    /// O(1): `newty2 (level of base) (desc of base)`.
    pub fn make_copy(&mut self, base: N) -> N {
        let level = self.level(base);
        self.make(Virtual::Copy { base, level })
    }

    /// O(1): `newty2 level (Tvar None)`.
    pub fn make_var(&mut self, level: u32) -> N {
        self.make(Virtual::FreshVar { level })
    }

    /// O(1): `newty2 level (Tobject fields)`.
    pub fn make_object(&mut self, fields: N, level: u32) -> N {
        self.make(Virtual::Object { fields, level })
    }

    /// O(1): a variant with row `rows[row]` at `level`.
    pub fn make_variant(&mut self, row: u32, level: u32) -> N {
        let n = self.make(Virtual::Variant { level });
        self.row_of[n.0 as usize] = row;
        n
    }

    /// Amortized O(1).
    fn set_override(&mut self, n: N, change: Override) {
        let index = u32::try_from(self.overrides.len()).expect("override limit");
        self.overrides.push(change);
        self.over[n.0 as usize] = index;
    }

    /// O(1): drop the name of a `Tvar (Some "_")`.
    pub fn unname(&mut self, n: N) {
        self.set_override(n, Override::Unnamed);
    }

    /// O(1): the head of a rebuilt object chain takes its first field.
    pub fn set_field(&mut self, n: N, name: u32, mutable: bool, typ: N, rest: N) {
        self.set_override(
            n,
            Override::Field {
                name,
                typ,
                rest,
                mutable,
            },
        );
    }

    /// O(1): `n` becomes the `Tconstr` of private row type `of`, trimmed.
    pub fn set_renamed(&mut self, n: N, of: N) {
        self.set_override(n, Override::Constr { of });
    }

    /// O(1): `n`'s row becomes `rows[row]`.
    pub fn set_row(&mut self, n: N, row: u32) {
        self.set_override(n, Override::Variant);
        self.row_of[n.0 as usize] = row;
    }

    /// O(1) for a stored node, O(copy chain) (at most two) otherwise.
    pub fn level(&self, n: N) -> u32 {
        if n.0 < self.v.real {
            return self.v.level(n);
        }
        match self.virtuals[(n.0 - self.v.real) as usize] {
            Virtual::Copy { level, .. }
            | Virtual::FreshVar { level }
            | Virtual::Variant { level, .. }
            | Virtual::Object { level, .. } => level,
            // Rebuilt fields take their chain's level; no field level is
            // printed. A `Tsubst` is generic (`newgenty`).
            Virtual::Field { .. } | Virtual::Subst(_) => crate::tc::graph::GENERIC,
        }
    }

    /// O(1) amortized: the descriptor with the overlay applied. A copy reads
    /// its base, which is a stored node or one other made node.
    pub fn desc(&self, mut n: N) -> Desc {
        loop {
            let change = self.over[n.0 as usize];
            if change != NONE {
                return match self.overrides[change as usize] {
                    Override::Unnamed => Desc::Var(NONE),
                    Override::Field {
                        name,
                        typ,
                        rest,
                        mutable,
                    } => Desc::Field {
                        name,
                        mutable,
                        typ,
                        rest,
                    },
                    Override::Constr { of } => match self.desc(of) {
                        Desc::Constr { path, args, .. } => Desc::Constr {
                            path,
                            trim: true,
                            args,
                        },
                        _ => unreachable!("a renamed row names a constructor"),
                    },
                    Override::Variant => Desc::Variant,
                };
            }
            if n.0 < self.v.real {
                return self.v.desc(n);
            }
            match self.virtuals[(n.0 - self.v.real) as usize] {
                Virtual::Field {
                    name,
                    typ,
                    rest,
                    mutable,
                } => {
                    return Desc::Field {
                        name,
                        mutable,
                        typ,
                        rest,
                    };
                }
                Virtual::Subst(target) => return Desc::Subst(target),
                Virtual::Copy { base, .. } => n = base,
                Virtual::FreshVar { .. } => return Desc::Var(NONE),
                Virtual::Variant { .. } => return Desc::Variant,
                Virtual::Object { fields, .. } => return Desc::Object(fields),
            }
        }
    }

    /// O(1): slot `i` of a node's list.
    pub fn slot(&self, slots: Slots, i: u32) -> N {
        self.v.slot(slots, i)
    }

    /// O(1): an arrow parameter's label and type.
    pub fn param(&self, params: Slots, i: u32) -> (u32, N) {
        self.v.param(params, i)
    }

    /// O(1): the nodes of `ns[range]`.
    pub fn ns_at(&self, range: Range, i: u32) -> N {
        self.ns[(range.start + i) as usize]
    }

    /// O(1): a row field.
    pub fn field(&self, range: Range, i: u32) -> FieldV {
        self.fields[(range.start + i) as usize]
    }

    /// The flattened row of a variant node (`Btype.row_repr`): amortized
    /// O(1) once computed; the first read is O(fields of the row chain).
    /// Nested rows (a `row_more` that is itself a variant) are concatenated
    /// outermost first, and the innermost row gives `more`, `closed`,
    /// `fixed` and the name (compiler-rust/src/types/btype.rs `row_repr`).
    /// A copy shares its base's row.
    pub fn row(&mut self, n: N) -> Row {
        let mut n = n;
        // A copy of a variant reads its base's row.
        while n.0 >= self.v.real {
            match self.virtuals[(n.0 - self.v.real) as usize] {
                Virtual::Copy { base, .. } if self.row_of[n.0 as usize] == NONE => n = base,
                _ => break,
            }
        }
        let cached = self.row_of[n.0 as usize];
        if cached != NONE {
            return self.rows[cached as usize];
        }
        let fields_start = self.fields.len() as u32;
        let mut current = n;
        let row = loop {
            let cached = self.row_of[current.0 as usize];
            if cached != NONE {
                let inner = self.rows[cached as usize];
                for i in 0..inner.fields.len {
                    let field = self.field(inner.fields, i);
                    self.fields.push(field);
                }
                break inner;
            }
            let (source, slots) = self.v.variant_row(current);
            for i in 0..source.fields.len {
                let field = self.v.p.row_fields[(source.fields.start + i) as usize];
                let types_start = self.ns.len() as u32;
                for k in 0..field.types.len {
                    let ty = self.v.slot(slots, field.types.start + k);
                    self.ns.push(ty);
                }
                self.fields.push(FieldV {
                    label: field.name,
                    types: Range {
                        start: types_start,
                        len: field.types.len,
                    },
                    kind: field.kind,
                });
            }
            let more = self.v.slot(slots, source.more);
            if matches!(self.desc(more), Desc::Variant) && more != current {
                current = more;
                continue;
            }
            let args_start = self.ns.len() as u32;
            for k in 0..source.name_arguments.len {
                let ty = self.v.slot(slots, source.name_arguments.start + k);
                self.ns.push(ty);
            }
            break Row {
                fields: Range::default(),
                name_args: Range {
                    start: args_start,
                    len: source.name_arguments.len,
                },
                more,
                name: source.name,
                closed: source.closed,
                fixed: source.fixed,
            };
        };
        let row = Row {
            fields: Range {
                start: fields_start,
                len: self.fields.len() as u32 - fields_start,
            },
            ..row
        };
        let index = self.push_row(row);
        self.row_of[n.0 as usize] = index;
        row
    }

    /// Amortized O(1).
    pub fn push_row(&mut self, row: Row) -> u32 {
        let index = u32::try_from(self.rows.len()).expect("row limit");
        self.rows.push(row);
        index
    }

    /// O(fields): `Btype.static_row`: closed, and no field is an `Reither`.
    pub fn static_row(&mut self, n: N) -> bool {
        let row = self.row(n);
        row.closed
            && (0..row.fields.len)
                .all(|i| !matches!(self.field(row.fields, i).kind, RowFieldKind::Either { .. }))
    }

    /// O(fields) for a variant, O(object fields) for an object, else O(1):
    /// `Btype.proxy`.
    pub fn proxy(&mut self, n: N) -> N {
        match self.desc(n) {
            Desc::Variant => {
                if self.static_row(n) {
                    n
                } else {
                    // `row_more` of a flattened row.
                    self.row(n).more
                }
            }
            Desc::Object(fields) => {
                let mut current = fields;
                loop {
                    match self.desc(current) {
                        Desc::Field { rest, .. } => current = rest,
                        Desc::Var(_) | Desc::Univar(_) | Desc::Constr { .. } => return current,
                        _ => return n,
                    }
                }
            }
            _ => n,
        }
    }

    /// O(path length): the last name of a constructor path as it reads.
    pub fn last_name(&self, path: u32, trim: bool) -> &'s str {
        let name = match self.v.path(path) {
            PathRow::Ident(id) => self.v.str(self.v.ident(id).name),
            PathRow::Dot { name, .. } => self.v.str(name),
            PathRow::Apply { .. } => "",
        };
        if trim { &name[..name.len() - 4] } else { name }
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn sizes() {
        assert_eq!(std::mem::size_of::<super::N>(), 4);
        assert_eq!(std::mem::size_of::<super::Slots>(), 8);
        assert_eq!(std::mem::size_of::<super::Desc>(), 16);
        assert_eq!(std::mem::size_of::<super::Virtual>(), 16);
        assert_eq!(std::mem::size_of::<super::Override>(), 16);
        assert_eq!(std::mem::size_of::<super::FieldV>(), 16);
        assert_eq!(std::mem::size_of::<super::Row>(), 28);
    }
}
