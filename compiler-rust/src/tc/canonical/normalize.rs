//! The graph changes `Printtyp.mark_loops` makes before it prints
//! (compiler-rust/src/types/ctype.rs `normalize_type`, printtyp.rs:576), as
//! overlay writes, and the two read-only walks the declaration printer uses.

use smallvec::SmallVec;

use super::view::{Desc, FieldV, Graph, Marks, N, Row};
use crate::tc::segment::{PathRow, Range, RowFieldKind};

/// One object field as `Ctype.flatten_fields` returns it.
#[derive(Clone, Copy)]
pub(super) struct ObjectField {
    pub name: u32,
    pub typ: N,
    pub mutable: bool,
}

/// Dense left-node roots into compressed binary radix trees of right indices.
/// Each probe follows at most 32 branching bits, independent of the number of
/// previous partners. Each distinct pair uses at most two 16-byte pool entries;
/// Vec growth is amortized, with no per-pair heap allocation or hashing.
#[derive(Default)]
struct Pairs {
    heads: Vec<u32>,
    entries: Vec<PairNode>,
}

#[derive(Clone, Copy)]
struct PairNode {
    children: [u32; 2],
    key: u32,
    bit: u32,
}

impl Pairs {
    fn insert(&mut self, a: N, b: N) -> bool {
        use crate::tc::graph::NONE;
        let index = a.0 as usize;
        if index >= self.heads.len() {
            self.heads.resize((index + 1).next_power_of_two(), NONE);
        }
        let root = self.heads[index];
        let leaf = PairNode {
            children: [NONE; 2],
            key: b.0,
            bit: 32,
        };
        if root == NONE {
            self.heads[index] = self.entries.len() as u32;
            self.entries.push(leaf);
            return true;
        }
        let side = |bit| ((b.0 >> (31 - bit)) & 1) as usize;
        let mut current = root;
        loop {
            #[cfg(test)]
            crate::tc::steps::tick();
            let node = self.entries[current as usize];
            if node.bit == 32 {
                break;
            }
            current = node.children[side(node.bit)];
        }
        let difference = (self.entries[current as usize].key ^ b.0).leading_zeros();
        if difference == 32 {
            return false;
        }
        let fresh = self.entries.len() as u32;
        self.entries.push(leaf);
        let mut parent = NONE;
        let mut parent_side = 0;
        current = root;
        while self.entries[current as usize].bit < difference {
            #[cfg(test)]
            crate::tc::steps::tick();
            parent = current;
            parent_side = side(self.entries[current as usize].bit);
            current = self.entries[current as usize].children[parent_side];
        }
        let mut children = [current; 2];
        children[side(difference)] = fresh;
        let branch = self.entries.len() as u32;
        self.entries.push(PairNode {
            children,
            key: 0,
            bit: difference,
        });
        if parent == NONE {
            self.heads[index] = branch;
        } else {
            self.entries[parent as usize].children[parent_side] = branch;
        }
        true
    }
}

impl<'s> Graph<'s> {
    /// O(fields log fields): `Ctype.flatten_fields`: the chain from `ty`, accumulated in
    /// reverse and stably sorted by name (ctype.rs:9383), and its rest.
    pub(super) fn flatten_fields(&self, ty: N, out: &mut Vec<ObjectField>) -> N {
        out.clear();
        let mut current = ty;
        while let Desc::Field {
            name,
            mutable,
            typ,
            rest,
        } = self.desc(current)
        {
            out.push(ObjectField { name, typ, mutable });
            current = rest;
        }
        out.reverse();
        let v = &self.v;
        out.sort_by(|a, b| v.str(a.name).cmp(v.str(b.name)));
        current
    }

    /// O(row chain): `Btype.row_of_type`.
    fn row_of_type(&mut self, ty: N) -> N {
        match self.desc(ty) {
            Desc::Object(fields) => {
                let mut current = fields;
                while let Desc::Field { rest, .. } = self.desc(current) {
                    current = rest;
                }
                current
            }
            Desc::Variant => self.row(ty).more,
            _ => ty,
        }
    }

    /// O(1): `Btype.is_constr_row ~allow_ident:false`.
    fn is_constr_row(&self, ty: N) -> bool {
        match self.desc(ty) {
            Desc::Constr { path, trim, .. } => {
                matches!(self.v.path(path), PathRow::Dot { .. })
                    && is_row_name(self.last_name(path, trim))
            }
            _ => false,
        }
    }

    /// O(reachable nodes + edges + field sorting), plus [`Self::equal`]
    /// for a conjunction of two or more types: `Ctype.normalize_type` with an
    /// empty environment, in its preorder. A node is processed once for the
    /// whole printing; processing it again is the identity, except that an
    /// object chain is rebuilt into fresh nodes again, which no text tells
    /// apart. Explicit stack, no recursion.
    pub(super) fn normalize(&mut self, root: N) {
        let mut work: Vec<N> = vec![root];
        let mut fields = Vec::new();
        let mut children: SmallVec<[N; 8]> = SmallVec::new();
        while let Some(ty) = work.pop() {
            #[cfg(test)]
            crate::tc::steps::tick();
            if !self.normalized.insert(ty) {
                continue;
            }
            let tm = self.row_of_type(ty);
            let is_constr = matches!(self.desc(ty), Desc::Constr { .. });
            if !is_constr && self.is_constr_row(tm) {
                // ctype.ml:4058-4065: name the private row type by its declaration.
                self.set_renamed(ty, tm);
            } else {
                match self.desc(ty) {
                    Desc::Variant => self.normalize_row(ty),
                    Desc::Object(head) => {
                        let rest = self.flatten_fields(head, &mut fields);
                        if !fields.is_empty() {
                            let mut next = rest;
                            for field in fields[1..].iter().rev() {
                                next = self.make_field(field.name, field.mutable, field.typ, next);
                            }
                            let first = fields[0];
                            self.set_field(head, first.name, first.mutable, first.typ, next);
                        }
                    }
                    _ => {}
                }
            }
            children.clear();
            self.children(ty, &mut children);
            work.extend(children.iter().rev());
        }
    }

    /// O(children): `Btype.iter_type_expr`, in its order. A row gives its
    /// fields' types, then the row name's arguments when `more` is a
    /// variable, constructor, `Tsubst` or `Tnil`, then `more`.
    pub(super) fn children(&mut self, ty: N, out: &mut SmallVec<[N; 8]>) {
        match self.desc(ty) {
            Desc::Var(_) | Desc::Univar(_) | Desc::Nil => {}
            Desc::Arrow { params, ret } => {
                for i in 0..params.len {
                    out.push(self.param(params, i).1);
                }
                out.push(ret);
            }
            Desc::Tuple(slots)
            | Desc::Constr { args: slots, .. }
            | Desc::Package { args: slots, .. } => {
                for i in 0..slots.len {
                    out.push(self.slot(slots, i));
                }
            }
            Desc::Object(fields) => out.push(fields),
            Desc::Field { typ, rest, .. } => {
                out.push(typ);
                out.push(rest);
            }
            Desc::Subst(target) => out.push(target),
            Desc::Poly { body, vars } => {
                out.push(body);
                for i in 0..vars.len {
                    out.push(self.slot(vars, i));
                }
            }
            Desc::Variant => {
                let row = self.row(ty);
                self.row_types(row, out);
                if matches!(
                    self.desc(row.more),
                    Desc::Var(_)
                        | Desc::Univar(_)
                        | Desc::Subst(_)
                        | Desc::Constr { .. }
                        | Desc::Nil
                ) {
                    for i in 0..row.name_args.len {
                        out.push(self.ns_at(row.name_args, i));
                    }
                }
                out.push(row.more);
            }
        }
    }

    /// O(field types): `Btype.iter_row`'s field part: a present field's
    /// argument, every type of a conjunction.
    pub(super) fn row_types(&self, row: Row, out: &mut SmallVec<[N; 8]>) {
        for i in 0..row.fields.len {
            let field = self.field(row.fields, i);
            for k in 0..field.types.len {
                out.push(self.ns_at(field.types, k));
            }
        }
    }

    /// O(fields · log fields + conjunct comparisons): ctype.ml:4069-4092. Drop
    /// conjuncts `equal` to an earlier one, drop absent fields, sort by label.
    fn normalize_row(&mut self, ty: N) {
        let row = self.row(ty);
        let mut kept: Vec<FieldV> = Vec::with_capacity(row.fields.len as usize);
        for i in 0..row.fields.len {
            let field = self.field(row.fields, i);
            match field.kind {
                RowFieldKind::Absent => continue,
                RowFieldKind::Either { .. } if field.types.len >= 2 => {
                    let start = self.ns.len() as u32;
                    let first = self.ns_at(field.types, 0);
                    self.ns.push(first);
                    for k in 1..field.types.len {
                        let t = self.ns_at(field.types, k);
                        let len = self.ns.len() as u32 - start;
                        let duplicate = (0..len).any(|j| {
                            let earlier = self.ns[(start + j) as usize];
                            self.equal(t, earlier)
                        });
                        if !duplicate {
                            self.ns.push(t);
                        }
                    }
                    kept.push(FieldV {
                        types: Range {
                            start,
                            len: self.ns.len() as u32 - start,
                        },
                        ..field
                    });
                }
                _ => kept.push(field),
            }
        }
        let v = &self.v;
        kept.sort_by(|a, b| v.str(a.label).cmp(v.str(b.label)));
        let start = self.fields.len() as u32;
        self.fields.extend_from_slice(&kept);
        let normalized = Row {
            fields: Range {
                start,
                len: kept.len() as u32,
            },
            ..row
        };
        let index = self.push_row(normalized);
        self.set_row(ty, index);
    }

    /// O(reachable pairs + merged fields + any sorting of unnormalized fields),
    /// with at most 64 radix probes per assumed pair and an explicit pair stack.
    /// Only conjunctions of two or more types reach this walk: `Ctype.equal Env.empty false [a] [b]`
    /// (ctype.rs:11043). With an empty environment no abbreviation expands.
    /// Package types compare paths and constraint names; OCaml's completion
    /// of missing constraints from the module type needs an environment.
    pub(super) fn equal(&mut self, a: N, b: N) -> bool {
        let mut work: Vec<(N, N)> = vec![(a, b)];
        let mut assumed = Pairs::default();
        let mut left_fields = Vec::new();
        let mut right_fields = Vec::new();
        while let Some((a, b)) = work.pop() {
            #[cfg(test)]
            crate::tc::steps::tick();
            if a == b {
                continue;
            }
            let (da, db) = (self.desc(a), self.desc(b));
            if let (
                Desc::Constr {
                    path: p,
                    trim: tp,
                    args: x,
                },
                Desc::Constr {
                    path: q,
                    trim: tq,
                    args: y,
                },
            ) = (da, db)
                && x.len == 0
                && y.len == 0
                && tp == tq
                && self.v.same_path(p, q)
            {
                continue;
            }
            if !assumed.insert(a, b) {
                continue;
            }
            match (da, db) {
                (Desc::Arrow { params: x, ret: r }, Desc::Arrow { params: y, ret: s })
                    if x.len == y.len
                        && (0..x.len).all(|i| self.param(x, i).0 == self.param(y, i).0) =>
                {
                    for i in 0..x.len {
                        work.push((self.param(x, i).1, self.param(y, i).1));
                    }
                    work.push((r, s));
                }
                (Desc::Tuple(x), Desc::Tuple(y)) if x.len == y.len => {
                    for i in 0..x.len {
                        work.push((self.slot(x, i), self.slot(y, i)));
                    }
                }
                (
                    Desc::Constr {
                        path: p,
                        trim: tp,
                        args: x,
                    },
                    Desc::Constr {
                        path: q,
                        trim: tq,
                        args: y,
                    },
                ) if tp == tq && self.v.same_path(p, q) && x.len == y.len => {
                    for i in 0..x.len {
                        work.push((self.slot(x, i), self.slot(y, i)));
                    }
                }
                (Desc::Package { row: r, args: x }, Desc::Package { row: s, args: y }) => {
                    let p = self.v.p;
                    let (r, s) = (p.packages[r as usize], p.packages[s as usize]);
                    if !self.v.same_path(r.path, s.path)
                        || r.longidents.len != s.longidents.len
                        || !indices(p, r.longidents)
                            .iter()
                            .zip(indices(p, s.longidents))
                            .all(|(&a, &b)| self.v.same_longident(a, b))
                        || x.len != y.len
                    {
                        return false;
                    }
                    for i in 0..x.len {
                        work.push((self.slot(x, i), self.slot(y, i)));
                    }
                }
                (Desc::Variant, Desc::Variant) => {
                    let (left, right) = (self.row(a), self.row(b));
                    if !self.equal_rows(a, left, right, &mut work) {
                        return false;
                    }
                }
                (Desc::Object(x), Desc::Object(y)) => {
                    if !self.equal_fields(x, y, &mut left_fields, &mut right_fields, &mut work) {
                        return false;
                    }
                }
                (Desc::Field { .. }, Desc::Field { .. }) => {
                    if !self.equal_fields(a, b, &mut left_fields, &mut right_fields, &mut work) {
                        return false;
                    }
                }
                (Desc::Nil, Desc::Nil) => {}
                (Desc::Poly { body: x, vars: u }, Desc::Poly { body: y, vars: w })
                    if u.len == w.len =>
                {
                    work.push((x, y));
                }
                (Desc::Univar(x), Desc::Univar(y)) if x == y => {}
                _ => return false,
            }
        }
        true
    }

    /// O(fields) for normalized rows; O(fields log fields) only if equality
    /// is reached from a conjunction before its child rows are normalized.
    /// Borrow sorted runs; otherwise sort a temporary copy without mutating
    /// the row. Labels compare by text, not by string-pool index.
    fn sorted_row_fields(&self, range: Range) -> std::borrow::Cow<'_, [FieldV]> {
        let fields = &self.fields[range.start as usize..(range.start + range.len) as usize];
        let compare = |a: &FieldV, b: &FieldV| {
            #[cfg(test)]
            crate::tc::steps::tick();
            self.v.str(a.label).cmp(self.v.str(b.label))
        };
        if fields
            .windows(2)
            .all(|pair| !compare(&pair[0], &pair[1]).is_gt())
        {
            std::borrow::Cow::Borrowed(fields)
        } else {
            let mut sorted = fields.to_vec();
            sorted.sort_by(compare);
            std::borrow::Cow::Owned(sorted)
        }
    }

    /// O(left fields + right fields + field types) after normalization:
    /// ctype.ml:3147-3180 / `equal_rows_without_renaming` merges label runs.
    /// Before normalization only the temporary sorting above is non-linear.
    /// Unequal-length Reither conjunctions retain ctype's first-against-rest
    /// rule below; that rule also queues only a linear number of pairs.
    fn equal_rows(&mut self, left_node: N, left: Row, right: Row, work: &mut Vec<(N, N)>) -> bool {
        if left.closed != right.closed {
            return false;
        }
        if !self.static_row(left_node) {
            work.push((left.more, right.more));
        }
        let left_fields = self.sorted_row_fields(left.fields);
        let right_fields = self.sorted_row_fields(right.fields);
        let (mut i, mut j) = (0, 0);
        let mut pairs: SmallVec<[(FieldV, FieldV); 8]> = SmallVec::new();
        while i < left_fields.len() || j < right_fields.len() {
            #[cfg(test)]
            crate::tc::steps::tick();
            let ordering = match (left_fields.get(i), right_fields.get(j)) {
                (Some(l), Some(r)) => self.v.str(l.label).cmp(self.v.str(r.label)),
                (Some(_), None) => std::cmp::Ordering::Less,
                (None, Some(_)) => std::cmp::Ordering::Greater,
                (None, None) => unreachable!("at least one field remains"),
            };
            match ordering {
                std::cmp::Ordering::Less => {
                    if !left.closed || left_fields[i].kind != RowFieldKind::Absent {
                        return false;
                    }
                    i += 1;
                }
                std::cmp::Ordering::Greater => {
                    if !left.closed || right_fields[j].kind != RowFieldKind::Absent {
                        return false;
                    }
                    j += 1;
                }
                std::cmp::Ordering::Equal => {
                    pairs.push((left_fields[i], right_fields[j]));
                    i += 1;
                    j += 1;
                }
            }
        }
        for (l, r) in pairs {
            let ty = |field: FieldV, k: u32| self.ns_at(field.types, k);
            match (l.kind, r.kind) {
                (RowFieldKind::Present, RowFieldKind::Present) => {
                    match (l.types.len, r.types.len) {
                        (0, 0) => {}
                        (1, 1) => work.push((ty(l, 0), ty(r, 0))),
                        _ => return false,
                    }
                }
                (RowFieldKind::Absent, RowFieldKind::Absent) => {}
                (
                    RowFieldKind::Either { constant: c, .. },
                    RowFieldKind::Either { constant: d, .. },
                ) if c == d => match (l.types.len, r.types.len) {
                    (0, 0) => {}
                    (0, _) | (_, 0) => return false,
                    (m, n) => {
                        work.push((ty(l, 0), ty(r, 0)));
                        if m == n {
                            for k in 1..m {
                                work.push((ty(l, k), ty(r, k)));
                            }
                        } else {
                            for k in 1..n {
                                work.push((ty(l, 0), ty(r, k)));
                            }
                            for k in 1..m {
                                work.push((ty(l, k), ty(r, 0)));
                            }
                        }
                    }
                },
                _ => return false,
            }
        }
        true
    }

    /// O(fields log fields): ctype.rs `equal_object_fields_without_renaming`.
    fn equal_fields(
        &mut self,
        left: N,
        right: N,
        left_fields: &mut Vec<ObjectField>,
        right_fields: &mut Vec<ObjectField>,
        work: &mut Vec<(N, N)>,
    ) -> bool {
        let left_rest = self.flatten_fields(left, left_fields);
        let right_rest = self.flatten_fields(right, right_fields);
        if left_fields.len() != right_fields.len() {
            return false;
        }
        work.push((left_rest, right_rest));
        for (l, r) in left_fields.iter().zip(right_fields.iter()) {
            if l.name != r.name || l.mutable != r.mutable {
                return false;
            }
            work.push((l.typ, r.typ));
        }
        true
    }

    /// O(reachable nodes + edges + row fields), explicit stack:
    /// `Ctype.free_variables` without an environment (printtyp.rs:940): the
    /// variables in preorder, a row's `more` only when it is not static.
    pub(super) fn free_variables(&mut self, root: N, visited: &mut Marks, out: &mut Vec<N>) {
        visited.clear();
        out.clear();
        let mut work = vec![root];
        let mut children: SmallVec<[N; 8]> = SmallVec::new();
        while let Some(ty) = work.pop() {
            #[cfg(test)]
            crate::tc::steps::tick();
            if !visited.insert(ty) {
                continue;
            }
            children.clear();
            match self.desc(ty) {
                Desc::Var(_) => out.push(ty),
                Desc::Variant => {
                    let row = self.row(ty);
                    self.row_types(row, &mut children);
                    // `iter_row`'s name arguments, then `more` unless static.
                    if matches!(
                        self.desc(row.more),
                        Desc::Var(_)
                            | Desc::Univar(_)
                            | Desc::Subst(_)
                            | Desc::Constr { .. }
                            | Desc::Nil
                    ) {
                        for i in 0..row.name_args.len {
                            children.push(self.ns_at(row.name_args, i));
                        }
                    }
                    if !self.static_row(ty) {
                        children.push(row.more);
                    }
                }
                _ => self.children(ty, &mut children),
            }
            work.extend(children.iter().rev());
        }
    }
}

/// O(1): `Btype.is_row_name`.
pub(super) fn is_row_name(s: &str) -> bool {
    s.len() >= 4 && s.ends_with("#row")
}

/// O(1): a range of `indices`.
fn indices(p: &crate::tc::segment::SignaturePools, range: Range) -> &[u32] {
    &p.indices[range.start as usize..(range.start + range.len) as usize]
}

#[cfg(test)]
mod tests {
    use super::super::view::View;
    use super::*;
    use crate::tc::{
        graph::{GENERIC, NONE},
        segment::Segment,
        steps,
    };

    #[test]
    fn ten_thousand_sorted_row_fields_compare_linearly() {
        let mut segment = Segment::default();
        let mut bytes = Vec::new();
        let mut strings = Vec::new();
        // Deliberately reverse pool order: merging must compare label text.
        for i in (0..10_000).rev() {
            let name = format!("field{i:05}");
            strings.push(Range {
                start: bytes.len() as u32,
                len: name.len() as u32,
            });
            bytes.extend_from_slice(name.as_bytes());
        }
        segment.signature.bytes = bytes.into_boxed_slice();
        segment.signature.strings = strings.into_boxed_slice();
        let mut graph = Graph::new(View::new(&segment));
        for _ in 0..2 {
            for label in (0..10_000).rev() {
                graph.fields.push(FieldV {
                    label,
                    types: Range::default(),
                    kind: RowFieldKind::Present,
                });
            }
        }
        let row = Row {
            fields: Range {
                start: 0,
                len: 10_000,
            },
            name_args: Range::default(),
            more: N(0),
            name: NONE,
            closed: true,
            fixed: false,
        };
        let l = graph.push_row(row);
        let r = graph.push_row(Row {
            fields: Range {
                start: 10_000,
                len: 10_000,
            },
            ..row
        });
        let left = graph.make_variant(l, GENERIC);
        let right = graph.make_variant(r, GENERIC);
        let count = steps::scope(|| assert!(graph.equal(left, right)));
        assert!(count <= 3 * 10_000, "{count} comparisons/visits");
    }

    #[test]
    fn ten_thousand_partners_have_bounded_radix_probes() {
        assert_eq!(std::mem::size_of::<PairNode>(), 16);
        let mut pairs = Pairs::default();
        let count = steps::scope(|| {
            for i in 0..10_000 {
                assert!(pairs.insert(N(7), N(i)));
            }
            for i in (0..10_000).rev() {
                assert!(!pairs.insert(N(7), N(i)));
            }
        });
        assert!(count <= 64 * 20_000, "{count} radix probes");
        assert_eq!(pairs.entries.len(), 19_999);
    }
}
