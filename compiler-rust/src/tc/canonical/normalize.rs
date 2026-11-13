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

/// Sparse pair relation over dense node indices. A left node indexes a
/// collision-free chain of right nodes; storage grows only by pool capacity.
/// Insertion is O(previous partners of the left node), not O(all pairs).
#[derive(Default)]
struct Pairs {
    heads: Vec<u32>,
    entries: Vec<(N, u32)>,
}

impl Pairs {
    fn insert(&mut self, a: N, b: N) -> bool {
        use crate::tc::graph::NONE;
        let index = a.0 as usize;
        if index >= self.heads.len() {
            self.heads.resize((index + 1).next_power_of_two(), NONE);
        }
        let head = self.heads[index];
        let mut current = head;
        while current != NONE {
            let (right, next) = self.entries[current as usize];
            if right == b {
                return false;
            }
            current = next;
        }
        self.heads[index] = self.entries.len() as u32;
        self.entries.push((b, head));
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

    /// O(pairs + field comparisons/sorts + sum of squared partner counts),
    /// with dense-indexed assumed-pair chains and an explicit pair stack.
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

    /// O(left fields × right fields + field types): ctype.rs `equal_rows_without_renaming`, queuing the pairs.
    fn equal_rows(&mut self, left_node: N, left: Row, right: Row, work: &mut Vec<(N, N)>) -> bool {
        if left.closed != right.closed {
            return false;
        }
        let mut matched: SmallVec<[bool; 16]> =
            smallvec::smallvec![false; right.fields.len as usize];
        let mut pairs: SmallVec<[(FieldV, FieldV); 8]> = SmallVec::new();
        for i in 0..left.fields.len {
            let l = self.field(left.fields, i);
            match (0..right.fields.len).find(|&j| self.field(right.fields, j).label == l.label) {
                Some(j) => {
                    matched[j as usize] = true;
                    pairs.push((l, self.field(right.fields, j)));
                }
                None => {
                    if !left.closed || l.kind != RowFieldKind::Absent {
                        return false;
                    }
                }
            }
        }
        for j in 0..right.fields.len {
            if !matched[j as usize]
                && (!left.closed || self.field(right.fields, j).kind != RowFieldKind::Absent)
            {
                return false;
            }
        }
        if !self.static_row(left_node) {
            work.push((left.more, right.more));
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
