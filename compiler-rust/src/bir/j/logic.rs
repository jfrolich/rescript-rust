//! Bounded J-E9/J-E10 speculation. A flat recipe pool keeps unsuccessful
//! attempts from mutating the owned Bir tree. Only the selected recipe is built.
use super::plain as p;
use crate::bir::{Bir, Constant, NodeId, View};
use crate::fast_hash::{AHashMap, AHashSet};
use crate::js_ir::BinOp;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Term {
    Source(NodeId),
    Recipe(u32),
}
#[derive(Clone, Copy)]
enum Recipe {
    Bool(bool),
    Bin(u16, Term, Term, Option<NodeId>),
    Not(Term),
    Clean(Term),
}
struct Plan<'a> {
    b: &'a Bir,
    recipes: Vec<Recipe>,
    steps: usize,
}
impl<'a> Plan<'a> {
    fn new(b: &'a Bir) -> Self {
        Self {
            b,
            recipes: vec![],
            steps: 0,
        }
    }
    fn add(&mut self, r: Recipe) -> Term {
        let id = self.recipes.len() as u32;
        self.recipes.push(r);
        Term::Recipe(id)
    }
    fn boolean(&mut self, b: bool) -> Term {
        self.add(Recipe::Bool(b))
    }
    fn raw(&mut self, op: BinOp, l: Term, r: Term) -> Term {
        self.add(Recipe::Bin(op as u16, l, r, None))
    }
    fn clean(&mut self, t: Term) -> Term {
        self.add(Recipe::Clean(t))
    }
    fn stripped(&self, mut t: Term) -> Term {
        while let Term::Recipe(i) = t {
            if let Recipe::Clean(v) = self.recipes[i as usize] {
                t = v;
            } else {
                break;
            }
        }
        t
    }
    fn source(&self, t: Term) -> Option<NodeId> {
        if let Term::Source(id) = self.stripped(t) {
            Some(id)
        } else {
            None
        }
    }
    fn cold_source(&self, t: Term) -> Option<NodeId> {
        match t {
            Term::Source(id) => Some(id),
            Term::Recipe(i) => match self.recipes[i as usize] {
                Recipe::Bin(_, _, _, cold) => cold,
                _ => None,
            },
        }
    }
    fn bool_of(&self, t: Term) -> Option<bool> {
        match self.stripped(t) {
            Term::Source(id) => p::bool_of(self.b, id),
            Term::Recipe(i) => match self.recipes[i as usize] {
                Recipe::Bool(v) => Some(v),
                _ => None,
            },
        }
    }
    fn bin(&self, t: Term) -> Option<(u16, Term, Term)> {
        match self.stripped(t) {
            Term::Source(id) => {
                if let View::JBin { left, right } = self.b.view(id) {
                    Some((
                        self.b.node(id).aux(),
                        Term::Source(left),
                        Term::Source(right),
                    ))
                } else {
                    None
                }
            }
            Term::Recipe(i) => match self.recipes[i as usize] {
                Recipe::Bin(op, l, r, _) => Some((op, l, r)),
                _ => None,
            },
        }
    }
    fn bin_is(&self, t: Term, op: BinOp) -> Option<(Term, Term)> {
        self.bin(t)
            .and_then(|(o, l, r)| (o == op as u16).then_some((l, r)))
    }
    fn not(&self, t: Term) -> Option<Term> {
        match self.stripped(t) {
            Term::Source(id) => {
                if let View::JNot { value } = self.b.view(id) {
                    Some(Term::Source(value))
                } else {
                    None
                }
            }
            Term::Recipe(i) => match self.recipes[i as usize] {
                Recipe::Not(v) => Some(v),
                _ => None,
            },
        }
    }
    fn variable(&self, t: Term) -> bool {
        self.source(t)
            .is_some_and(|id| matches!(self.b.view(id), View::Var { .. } | View::JQualified { .. }))
    }
    fn same_var(&self, x: Term, y: Term) -> bool {
        match (self.source(x), self.source(y)) {
            (Some(x), Some(y)) => p::same_var(self.b, x, y),
            _ => false,
        }
    }
    fn literal(&self, t: Term) -> bool {
        self.bool_of(t).is_some()
            || self.source(t).is_some_and(|id| {
                matches!(
                    self.b.view(id),
                    View::JNull | View::JUndefined | View::JNumber { .. } | View::JStr { .. }
                )
            })
    }
    fn literal_type(&self, t: Term, ty: &str) -> bool {
        if ty == "boolean" {
            return self.bool_of(t).is_some();
        }
        self.source(t).is_some_and(|id| {
            matches!(
                (ty, self.b.view(id)),
                ("string", View::JStr { .. })
                    | ("number", View::JNumber { .. })
                    | ("object", View::JNull)
            )
        })
    }
    fn typeof_test(&self, t: Term) -> Option<(Term, &str)> {
        let (l, r) = self.bin_is(t, BinOp::EqEqEq)?;
        let View::JTypeof { value } = self.b.view(self.source(l)?) else {
            return None;
        };
        let View::JStr { text } = self.b.view(self.source(r)?) else {
            return None;
        };
        let v = Term::Source(value);
        self.variable(v).then_some((v, self.b.text(text)))
    }
    fn comparison(&self, t: Term) -> Option<(u16, Term, Term)> {
        let (op, l, r) = self.bin(t)?;
        ((op == BinOp::EqEqEq as u16 || op == BinOp::NotEqEq as u16) && self.variable(l))
            .then_some((op, l, r))
    }
    fn array_test(&self, t: Term) -> Option<Term> {
        let View::JCall { callee, args, .. } = self.b.view(self.source(t)?) else {
            return None;
        };
        if let [arg] = args {
            let arg = Term::Source(*arg);
            if self.variable(arg) && super::facts::is_array_is_array(self.b, callee) {
                return Some(arg);
            }
        }
        None
    }
    fn either(
        &self,
        l: Term,
        r: Term,
        pred: impl Fn(&Self, Term) -> bool,
    ) -> Option<(Term, Term, bool)> {
        if pred(self, l) {
            Some((l, r, true))
        } else if pred(self, r) {
            Some((r, l, false))
        } else {
            None
        }
    }
    fn is_type(&self, t: Term, names: &[&str]) -> bool {
        self.typeof_test(t).is_some_and(|(_, n)| names.contains(&n))
    }
    fn same_type_var(&self, t: Term, v: Term) -> bool {
        self.typeof_test(t)
            .is_some_and(|(x, _)| self.same_var(x, v))
    }
    fn equal(&mut self, l: Term, r: Term) -> bool {
        let mut stack = vec![(l, r)];
        while let Some((l, r)) = stack.pop() {
            self.steps += 1;
            if let (Some(l), Some(r)) = (self.source(l), self.source(r)) {
                if !super::equal::equal(self.b, l, r, &mut self.steps) {
                    return false;
                }
                continue;
            }
            if let (Some(l), Some(r)) = (self.bool_of(l), self.bool_of(r)) {
                if l != r {
                    return false;
                }
                continue;
            }
            if let (Some((op, l1, l2)), Some((oq, r1, r2))) = (self.bin(l), self.bin(r)) {
                if op != oq {
                    return false;
                }
                stack.push((l2, r2));
                stack.push((l1, r1));
                continue;
            }
            return false;
        }
        true
    }
    fn literal_eq(&self, l: Term, r: Term) -> Option<bool> {
        if let (Some(l), Some(r)) = (self.bool_of(l), self.bool_of(r)) {
            return Some(l == r);
        }
        let (Some(l), Some(r)) = (self.source(l), self.source(r)) else {
            return (self.literal(l) && self.literal(r)).then_some(false);
        };
        match (self.b.view(l), self.b.view(r)) {
            (View::JNumber { value: l }, View::JNumber { value: r }) => {
                match (self.b.constant(l), self.b.constant(r)) {
                    (Constant::BigInt(l), Constant::BigInt(r)) => Some(l == r),
                    (Constant::BigInt(_), _) | (_, Constant::BigInt(_)) => Some(false),
                    (l, r) => {
                        let num = |n: &Constant| match n {
                            Constant::Int(n) => Some(*n as f64),
                            Constant::Char(n) => Some(f64::from(*n)),
                            Constant::Float(f) => {
                                crate::ocaml_float::float_of_string(self.b.text(f.spelling()))
                            }
                            _ => None,
                        };
                        Some(num(l)? == num(r)?)
                    }
                }
            }
            (View::JStr { text: l }, View::JStr { text: r }) => Some(l == r),
            (View::JNull, View::JNull) | (View::JUndefined, View::JUndefined) => Some(true),
            _ => Some(false),
        }
    }
    /// B:633; success requires both sides of every logical node. Traversal and
    /// postorder reconstruction use explicit stacks, including failed attempts.
    fn negate(&mut self, root: Term) -> Option<Term> {
        enum Work {
            Enter(Term),
            Bin(u16, Option<NodeId>),
        }
        let mut work = vec![Work::Enter(root)];
        let mut values = vec![];
        while let Some(w) = work.pop() {
            self.steps += 1;
            match w {
                Work::Enter(t) => {
                    if let Some(v) = self.not(t) {
                        values.push(v);
                        continue;
                    }
                    if let Some(v) = self.bool_of(t) {
                        let v = self.boolean(!v);
                        values.push(v);
                        continue;
                    }
                    if let Some((op, l, r)) = self.bin(t) {
                        let cold = self.cold_source(t);
                        if op == BinOp::EqEqEq as u16 || op == BinOp::NotEqEq as u16 {
                            let op = if op == BinOp::EqEqEq as u16 {
                                BinOp::NotEqEq
                            } else {
                                BinOp::EqEqEq
                            };
                            let v = self.add(Recipe::Bin(op as u16, l, r, cold));
                            values.push(v);
                            continue;
                        }
                        if op == BinOp::And as u16 || op == BinOp::Or as u16 {
                            let op = if op == BinOp::And as u16 {
                                BinOp::Or
                            } else {
                                BinOp::And
                            };
                            work.push(Work::Bin(op as u16, cold));
                            work.push(Work::Enter(r));
                            work.push(Work::Enter(l));
                            continue;
                        }
                    }
                    return None;
                }
                Work::Bin(op, cold) => {
                    let r = values.pop().unwrap();
                    let l = values.pop().unwrap();
                    let v = self.add(Recipe::Bin(op, l, r, cold));
                    values.push(v);
                }
            }
        }
        values.pop()
    }
    /// J-E9's only recursion is on the explicit, legacy n<=10 budget, never
    /// on unbounded expression depth. All structural walks above are iterative.
    fn and(&mut self, n: usize, l: Term, r: Term) -> Option<Term> {
        self.steps += 1;
        if n > 10 {
            return None;
        }
        if self.bool_of(l) == Some(false) || self.bool_of(r) == Some(false) {
            return Some(self.boolean(false));
        }
        if self.bool_of(l) == Some(true) {
            return Some(r);
        }
        if self.bool_of(r) == Some(true) {
            return Some(l);
        }
        if let Some((a, b)) = self.bin_is(l, BinOp::And) {
            let ao = self.and(n + 1, a, r);
            let bo = self.and(n + 1, b, r);
            return match (ao, bo) {
                (None, None) => {
                    let e = self.and(n + 1, a, b)?;
                    Some(self.and_force(n + 1, e, r))
                }
                (Some(a), None) => Some(self.and_force(n + 1, a, b)),
                (None, Some(b)) => Some(self.and_force(n + 1, a, b)),
                (Some(a), Some(b)) => Some(self.and_force(n + 1, a, b)),
            };
        }
        if let Some((a, b)) = self.bin_is(r, BinOp::And) {
            let e = self.raw(BinOp::And, l, a);
            return self.and(n + 1, e, b);
        }
        if let Some((a, b)) = self.bin_is(l, BinOp::Or) {
            let ao = self.and(n + 1, a, r);
            let bo = self.and(n + 1, b, r);
            return match (ao, bo) {
                (Some(x), None) if self.bool_of(x) == Some(false) => {
                    Some(self.raw(BinOp::And, b, r))
                }
                (None, Some(x)) if self.bool_of(x) == Some(false) => {
                    Some(self.raw(BinOp::And, a, r))
                }
                (None, _) | (_, None) => {
                    let e = self.or(n + 1, a, b)?;
                    Some(self.and_force(n + 1, e, r))
                }
                (Some(a), Some(b)) => Some(self.or_force(n + 1, a, b)),
            };
        }
        for ty in ["boolean", "string", "number"] {
            if let Some((test, cmp, _)) = self.either(l, r, |s, e| s.is_type(e, &[ty])) {
                if let Some((op, var, v)) = self.comparison(cmp) {
                    if op == BinOp::EqEqEq as u16
                        && self.literal_type(v, ty)
                        && self.same_type_var(test, var)
                    {
                        return Some(self.clean(cmp));
                    }
                }
            }
        }
        if let Some((test, cmp, _)) =
            self.either(l, r, |s, e| s.is_type(e, &["boolean", "string", "number"]))
        {
            if let Some((op, var, v)) = self.comparison(cmp) {
                if op == BinOp::EqEqEq as u16 && self.literal(v) && self.same_type_var(test, var) {
                    return Some(self.boolean(false));
                }
            }
        }
        if let Some((test, cmp, _)) = self.either(l, r, |s, e| s.array_test(e).is_some()) {
            if let Some((op, var, v)) = self.comparison(cmp) {
                if op == BinOp::EqEqEq as u16
                    && self.literal(v)
                    && self.same_var(self.array_test(test).unwrap(), var)
                {
                    return Some(self.boolean(false));
                }
            }
        }
        if let Some((test, other, _)) = self.either(l, r, |s, e| s.is_type(e, &["boolean"])) {
            let target = if self.variable(other) && self.same_type_var(test, other) {
                Some((other, true))
            } else if let Some(inner) = self.not(other) {
                if self.variable(inner) && self.same_type_var(test, inner) {
                    Some((inner, false))
                } else {
                    None
                }
            } else if let Some((op, var, v)) = self.comparison(other) {
                if op == BinOp::NotEqEq as u16 && self.same_type_var(test, var) {
                    self.bool_of(v).map(|v| (var, !v))
                } else {
                    None
                }
            } else {
                None
            };
            if let Some((var, v)) = target {
                let var = self.clean(var);
                let v = self.boolean(v);
                return Some(self.raw(BinOp::EqEqEq, var, v));
            }
        }
        for ty in ["string", "number", "object"] {
            if let Some((test, cmp, _)) = self.either(l, r, |s, e| s.is_type(e, &[ty])) {
                if let Some((op, var, v)) = self.comparison(cmp) {
                    if op == BinOp::NotEqEq as u16
                        && self.literal_type(v, ty)
                        && self.same_type_var(test, var)
                    {
                        return None;
                    }
                }
            }
        }
        if let Some((test, cmp, first)) = self.either(l, r, |s, e| {
            s.is_type(e, &["boolean", "string", "number", "object"])
        }) {
            if let Some((op, var, v)) = self.comparison(cmp) {
                let literal = if first {
                    self.literal(v)
                } else {
                    self.bool_of(v).is_some()
                        || self.source(v).is_some_and(|v| {
                            matches!(self.b.view(v), View::JNull | View::JUndefined)
                        })
                };
                if op == BinOp::NotEqEq as u16 && literal && self.same_type_var(test, var) {
                    return Some(self.clean(test));
                }
            }
        }
        if let Some((test, cmp, _)) = self.either(l, r, |s, e| s.array_test(e).is_some()) {
            if let Some((op, var, v)) = self.comparison(cmp) {
                if op == BinOp::NotEqEq as u16
                    && self.literal(v)
                    && self.same_var(self.array_test(test).unwrap(), var)
                {
                    return Some(self.clean(test));
                }
            }
        }
        if self.equal(l, r) {
            return Some(l);
        }
        if let (Some((op1, v1, c1)), Some((op2, v2, c2))) = (self.comparison(l), self.comparison(r))
        {
            if self.literal(c1) && self.literal(c2) && self.same_var(v1, v2) {
                if op1 == BinOp::EqEqEq as u16 && op2 == BinOp::EqEqEq as u16 {
                    return self
                        .literal_eq(c1, c2)
                        .map(|eq| if eq { l } else { self.boolean(false) });
                }
                if op1 != op2 {
                    return self.literal_eq(c1, c2).map(|eq| {
                        if eq {
                            self.boolean(false)
                        } else if op1 == BinOp::EqEqEq as u16 {
                            l
                        } else {
                            r
                        }
                    });
                }
            }
        }
        None
    }
    fn and_force(&mut self, n: usize, l: Term, r: Term) -> Term {
        self.and(n, l, r)
            .unwrap_or_else(|| self.raw(BinOp::And, l, r))
    }
    fn or_force(&mut self, n: usize, l: Term, r: Term) -> Term {
        self.or(n, l, r)
            .unwrap_or_else(|| self.raw(BinOp::Or, l, r))
    }
    fn or(&mut self, n: usize, l: Term, r: Term) -> Option<Term> {
        self.steps += 1;
        if self.bool_of(l) == Some(true) || self.bool_of(r) == Some(true) {
            return Some(self.boolean(true));
        }
        if self.bool_of(l) == Some(false) {
            return Some(r);
        }
        if self.bool_of(r) == Some(false) {
            return Some(l);
        }
        let l = self.negate(l)?;
        let r = self.negate(r)?;
        let value = self.and(n + 1, l, r)?;
        self.negate(value)
    }
}

// A repeated pure function is a second owned tree, not a shared binder. Keep
// its source printing identities: the legacy arena shares that same function.
fn copy_j(b: &mut Bir, root: NodeId) -> NodeId {
    let copy = b.copy_subtree(root, &[]);
    let mut stack = vec![(root, copy)];
    while let Some((old, new)) = stack.pop() {
        // Function bodies can also declare or catch identifiers.
        let old_vars = b.binders(old);
        let new_vars = b.binders(new);
        for (old, new) in old_vars.into_iter().zip(new_vars) {
            let origin = b.vars.j_origin[old.index()];
            b.vars.j_origin[new.index()] = origin;
        }
        stack.extend(
            b.view(old)
                .children()
                .into_iter()
                .zip(b.view(new).children()),
        );
    }
    copy
}

/// Realise only the selected recipe. Disjoint retained subtrees move without a
/// copy. Repeated/overlapping occurrences are copied before any source is edited.
/// Ancestor classification is memoised; each removed ancestor is examined once.
fn finish(b: &mut Bir, recipes: Vec<Recipe>, result: Term, roots: &[NodeId]) -> NodeId {
    enum Work {
        Enter(Term),
        Build(Recipe),
    }
    enum Output {
        Source(usize),
        Build(Recipe),
    }
    let mut work = vec![Work::Enter(result)];
    let mut output = vec![];
    let mut leaves = vec![];
    while let Some(w) = work.pop() {
        match w {
            Work::Enter(Term::Source(id)) => {
                output.push(Output::Source(leaves.len()));
                leaves.push(id);
            }
            Work::Enter(Term::Recipe(i)) => {
                let r = recipes[i as usize];
                work.push(Work::Build(r));
                match r {
                    Recipe::Bool(_) => {}
                    Recipe::Bin(_, l, r, _) => {
                        work.push(Work::Enter(r));
                        work.push(Work::Enter(l));
                    }
                    Recipe::Not(t) | Recipe::Clean(t) => work.push(Work::Enter(t)),
                }
            }
            Work::Build(r) => output.push(Output::Build(r)),
        }
    }
    let selected: AHashSet<_> = leaves.iter().copied().collect();
    let mut covered: AHashMap<NodeId, bool> = AHashMap::default();
    let mut seen = AHashSet::default();
    let mut retained = vec![];
    let mut resolved = vec![];
    for &id in &leaves {
        let mut path = vec![];
        let mut parent = b.parents[id.index()];
        let mut overlaps = false;
        while let Some(p) = parent {
            if selected.contains(&p) {
                overlaps = true;
                break;
            }
            if let Some(&answer) = covered.get(&p) {
                overlaps = answer;
                break;
            }
            path.push(p);
            parent = b.parents[p.index()];
        }
        for p in path {
            covered.insert(p, overlaps);
        }
        if overlaps || !seen.insert(id) {
            resolved.push(copy_j(b, id));
        } else {
            resolved.push(id);
            retained.push(id);
        }
    }
    // Save recipe metadata before shells can be freed or their slots reused.
    let mut cold = AHashMap::default();
    for recipe in &recipes {
        if let Recipe::Bin(_, _, _, Some(id)) = recipe {
            cold.entry(*id).or_insert((
                b.cold(*id),
                b.node(*id)
                    .flags()
                    .contains(crate::bir::NodeFlags::JS_LOC_PRESENT),
            ));
        }
    }

    for &id in &retained {
        if b.parents[id.index()].is_some() {
            b.detach(id);
        }
    }
    // Build before releasing roots so metadata lookup is never a recycled slot.
    let mut values = vec![];
    for task in output {
        match task {
            Output::Source(i) => values.push(resolved[i]),
            Output::Build(r) => {
                let value = match r {
                    Recipe::Bool(v) => p::boolean(b, v),
                    Recipe::Bin(op, _, _, source) => {
                        let right = values.pop().unwrap();
                        let left = values.pop().unwrap();
                        let id = p::node(b, View::JBin { left, right }, op);
                        if let Some(source) = source {
                            let (metadata, loc) = cold[&source];
                            if let Some(metadata) = metadata {
                                b.set_cold(id, metadata);
                            }
                            if loc {
                                let mut flags = b.node(id).flags();
                                flags.0 |= crate::bir::NodeFlags::JS_LOC_PRESENT;
                                b.nodes[id.index()].set_flags(flags);
                            }
                        }
                        id
                    }
                    Recipe::Not(_) => {
                        let value = values.pop().unwrap();
                        p::node(b, View::JNot { value }, 0)
                    }
                    Recipe::Clean(_) => {
                        let id = values.pop().unwrap();
                        if !b.cold.is_empty() {
                            b.cold[id.index()] = None;
                        }
                        let mut flags = b.node(id).flags();
                        flags.0 &= !(crate::bir::NodeFlags::HAS_LOC
                            | crate::bir::NodeFlags::JS_LOC_PRESENT);
                        b.nodes[id.index()].set_flags(flags);
                        id
                    }
                };
                values.push(value);
            }
        }
    }
    for &root in roots {
        if !retained.contains(&root) {
            b.release(root);
        }
    }
    values.pop().unwrap()
}

pub(super) fn simplify(
    b: &mut Bir,
    l: NodeId,
    r: NodeId,
    or: bool,
    steps: &mut usize,
) -> Option<NodeId> {
    let mut plan = Plan::new(b);
    let (lt, rt) = (Term::Source(l), Term::Source(r));
    let result = if or {
        plan.or(0, lt, rt)
    } else {
        plan.and(0, lt, rt)
    };
    let measured = plan.steps;
    *steps += measured;
    let recipes = plan.recipes;
    if or {
        b.j_stats.or_attempts += 1;
        b.j_stats.max_or_steps = b.j_stats.max_or_steps.max(measured);
    } else {
        b.j_stats.and_attempts += 1;
        b.j_stats.max_and_steps = b.j_stats.max_and_steps.max(measured);
    }
    result.map(|result| finish(b, recipes, result, &[l, r]))
}
pub(super) fn negate(b: &mut Bir, value: NodeId, steps: &mut usize) -> Option<NodeId> {
    let mut plan = Plan::new(b);
    let result = plan.negate(Term::Source(value));
    *steps += plan.steps;
    let recipes = plan.recipes;
    result.map(|result| finish(b, recipes, result, &[value]))
}
pub(super) fn negated_and(
    b: &mut Bir,
    test: NodeId,
    no: NodeId,
    steps: &mut usize,
) -> Option<NodeId> {
    if !p::pure(b, test) || !p::pure(b, no) {
        return None;
    }
    let mut plan = Plan::new(b);
    let t = Term::Source(test);
    // Full J-E8 not, including integer and ordered-comparison cases.
    let negated = if let Some(n) = p::int_of(b, test) {
        plan.boolean(n == 0)
    } else if let Some(v) = plan.bool_of(t) {
        plan.boolean(!v)
    } else if let Some(v) = plan.not(t) {
        v
    } else if let Some((op, l, r)) = plan.bin(t) {
        let opposite = [
            (BinOp::EqEqEq, BinOp::NotEqEq),
            (BinOp::NotEqEq, BinOp::EqEqEq),
            (BinOp::Lt, BinOp::Ge),
            (BinOp::Ge, BinOp::Lt),
            (BinOp::Le, BinOp::Gt),
            (BinOp::Gt, BinOp::Le),
        ]
        .into_iter()
        .find(|(x, _)| *x as u16 == op);
        if let Some((_, op)) = opposite {
            plan.add(Recipe::Bin(op as u16, l, r, Some(test)))
        } else {
            plan.negate(t).unwrap_or_else(|| plan.add(Recipe::Not(t)))
        }
    } else {
        plan.negate(t).unwrap_or_else(|| plan.add(Recipe::Not(t)))
    };
    let result = plan.and(0, negated, Term::Source(no));
    let measured = plan.steps;
    *steps += measured;
    let recipes = plan.recipes;
    b.j_stats.and_attempts += 1;
    b.j_stats.max_and_steps = b.j_stats.max_and_steps.max(measured);
    result.map(|result| finish(b, recipes, result, &[test, no]))
}
