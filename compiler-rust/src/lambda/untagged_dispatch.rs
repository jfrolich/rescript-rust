//! The dispatch of a `switch` on an untagged variant, as data.
//!
//! Port of `compiler/ml/untagged_dispatch.ml`: which tests the generated code
//! runs on the scrutinee, in which statements, and which body each path runs.
//! `LambdaCompiler::compile_untagged_plan` prints a plan as JavaScript, and
//! constant folding (`Lambda::switch`) evaluates it with [`select`], so a
//! folded match and the generated code agree by construction.
//!
//! OCaml builds the plan as a tree of `test` and `tree` values. Here a
//! [`Plan`] keeps its tests, its tree nodes and the cases of its switches in
//! typed pools addressed by `u32` handles, the nodes built in the order the
//! OCaml constructors run. Nodes are never mutated: a rewrite such as
//! `simplify` adds new nodes, and a node shared by two parents is the value
//! OCaml shares between them.

use crate::types::variant_runtime::{
    BlockType, FieldCheck, Instance, LiteralTag, MatchingFacts, ObjectCase, same_literal_value,
};

/// A test in [`Plan::tests`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct TestId(u32);

/// A node in [`Plan::trees`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct TreeId(u32);

/// The cases of a switch: a range of [`Plan::value_clauses`] or
/// [`Plan::typeof_clauses`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Clauses {
    start: u32,
    len: u32,
}

impl Clauses {
    pub(crate) fn len(self) -> usize {
        self.len as usize
    }
    fn range(self) -> std::ops::Range<usize> {
        self.start as usize..(self.start + self.len) as usize
    }
}

/// A test on the scrutinee `x` (untagged_dispatch.mli `test`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Test {
    /// `x === literal`
    Equals(LiteralTag),
    /// `typeof x === "k"`, for a kind with a `typeof` name
    Typeof(BlockType),
    /// `Array.isArray(x)` or `x instanceof C`
    Instance(Instance),
    /// `x !== null`
    NotNull,
    /// `"f" in x`, on an object
    FieldIn(String),
    /// `x.f === literal`, on an object
    FieldEquals(String, LiteralTag),
    /// `typeof x.f === "k"`, on an object
    FieldTypeof(String, BlockType),
    /// `Array.isArray(x.f)`, on an object
    FieldIsArray(String),
    Not(TestId),
    And(TestId, TestId),
    Or(TestId, TestId),
}

/// How the generated code reaches the bodies `A` (untagged_dispatch.mli
/// `tree`).
#[derive(Debug, Clone)]
pub(crate) enum Tree<A> {
    /// An arm's body, unchecked.
    Run(A),
    /// The match's default action, reached from the payload dispatch.
    Fallback,
    /// No statement.
    Skip,
    If(TestId, TreeId, TreeId),
    /// A statement block around the tree.
    Block(TreeId),
    /// `switch (x)` over literals; the tree is the `default:`.
    SwitchValue(Clauses, TreeId),
    /// `switch (typeof x)` over kinds with a `typeof` name; the tree is the
    /// `default:`. A switch with one clause that is not empty is printed as
    /// an `if`.
    SwitchTypeof(Clauses, TreeId),
}

/// A `case` of a switch.
#[derive(Debug, Clone)]
pub(crate) enum Clause<A> {
    /// An empty case falling through to the next one; the body only gives
    /// the source location.
    FallsThrough(Option<A>),
    /// A `Run` or `Fallback`.
    Body(TreeId),
}

/// A plan: its pools and the root of its tree.
#[derive(Debug, Clone)]
pub(crate) struct Plan<A> {
    tests: Vec<Test>,
    trees: Vec<Tree<A>>,
    value_clauses: Vec<(LiteralTag, Clause<A>)>,
    typeof_clauses: Vec<(BlockType, Clause<A>)>,
    root: TreeId,
}

impl<A> Plan<A> {
    fn new() -> Self {
        Plan {
            tests: Vec::new(),
            trees: Vec::new(),
            value_clauses: Vec::new(),
            typeof_clauses: Vec::new(),
            root: TreeId(0),
        }
    }

    pub(crate) fn root(&self) -> TreeId {
        self.root
    }

    pub(crate) fn tree(&self, id: TreeId) -> &Tree<A> {
        &self.trees[id.0 as usize]
    }

    pub(crate) fn test(&self, id: TestId) -> &Test {
        &self.tests[id.0 as usize]
    }

    pub(crate) fn value_clauses(&self, clauses: Clauses) -> &[(LiteralTag, Clause<A>)] {
        &self.value_clauses[clauses.range()]
    }

    pub(crate) fn typeof_clauses(&self, clauses: Clauses) -> &[(BlockType, Clause<A>)] {
        &self.typeof_clauses[clauses.range()]
    }

    fn add_test(&mut self, test: Test) -> TestId {
        let id = TestId(self.tests.len() as u32);
        self.tests.push(test);
        id
    }

    fn not(&mut self, test: TestId) -> TestId {
        self.add_test(Test::Not(test))
    }

    fn and(&mut self, a: TestId, b: TestId) -> TestId {
        self.add_test(Test::And(a, b))
    }

    fn or(&mut self, a: TestId, b: TestId) -> TestId {
        self.add_test(Test::Or(a, b))
    }

    fn add_tree(&mut self, tree: Tree<A>) -> TreeId {
        let id = TreeId(self.trees.len() as u32);
        self.trees.push(tree);
        id
    }

    fn switch_value(&mut self, clauses: Vec<(LiteralTag, Clause<A>)>, default: TreeId) -> TreeId {
        let start = self.value_clauses.len() as u32;
        let len = clauses.len() as u32;
        self.value_clauses.extend(clauses);
        self.add_tree(Tree::SwitchValue(Clauses { start, len }, default))
    }

    fn switch_typeof(&mut self, clauses: Vec<(BlockType, Clause<A>)>, default: TreeId) -> TreeId {
        let start = self.typeof_clauses.len() as u32;
        let len = clauses.len() as u32;
        self.typeof_clauses.extend(clauses);
        self.add_tree(Tree::SwitchTypeof(Clauses { start, len }, default))
    }

    /// OCaml's structural `test1 = test2`.
    fn same_test(&self, a: TestId, b: TestId) -> bool {
        match (self.test(a), self.test(b)) {
            (Test::Not(a), Test::Not(b)) => self.same_test(*a, *b),
            (Test::And(a1, a2), Test::And(b1, b2)) | (Test::Or(a1, a2), Test::Or(b1, b2)) => {
                self.same_test(*a1, *b1) && self.same_test(*a2, *b2)
            }
            (Test::Not(_) | Test::And(..) | Test::Or(..), _)
            | (_, Test::Not(_) | Test::And(..) | Test::Or(..)) => false,
            (a, b) => a == b,
        }
    }
}

pub(crate) struct Input<'f, A> {
    pub facts: &'f MatchingFacts,
    /// The arms of the literal cases, in the order of the match.
    pub literal_arms: Vec<(LiteralTag, A)>,
    /// The arms of the payload cases, in the order of the match. With
    /// several object cases (`facts.object_cases`), those are in
    /// `object_arms` instead.
    pub payload_arms: Vec<(BlockType, A)>,
    /// The arms of the object cases of a variant with several, by their
    /// position in `facts.object_cases`.
    pub object_arms: Vec<(usize, A)>,
    /// Every literal case has an arm.
    pub literals_complete: bool,
    /// Every payload case has an arm.
    pub payloads_complete: bool,
    /// The default action of the match, for the cases without an arm.
    pub fallback: Option<A>,
}

/// The kinds `switch (typeof x)` tells apart; functions and objects are
/// checked after the classes.
fn is_primitive(kind: &BlockType) -> bool {
    matches!(
        kind,
        BlockType::Number
            | BlockType::String
            | BlockType::Bigint
            | BlockType::Boolean
            | BlockType::Symbol
    )
}

/// `Ext_list.stable_group`: groups of equal elements, each group in the
/// order of the list, the groups in the order of their first element... as
/// built from the tail, an element joining the first group whose head it
/// equals.
fn stable_group<T: Clone>(list: &[T], eq: impl Fn(&T, &T) -> bool) -> Vec<Vec<T>> {
    // ext_list.ml `stable_group`: `List.rev (fold_left (fun acc x ->
    // stable_add x acc) [] ...)`... mirrors the existing Rust
    // `stable_group_switch_cases`, which walks from the tail and inserts each
    // element into the first matching group.
    let mut groups: Vec<Vec<T>> = Vec::new();
    for x in list.iter().rev() {
        match groups
            .iter_mut()
            .find(|group| group.last().is_some_and(|head| eq(x, head)))
        {
            Some(group) => group.push(x.clone()),
            None => groups.push(vec![x.clone()]),
        }
    }
    groups.reverse();
    groups
        .into_iter()
        .map(|mut group| {
            group.reverse();
            group
        })
        .collect()
}

/// The cases of a switch: arms with one body share it, the earlier ones
/// falling through to the last.
fn clauses<K: Clone, A: Clone>(
    p: &mut Plan<A>,
    same: &impl Fn(&A, &A) -> bool,
    shares: impl Fn(&K, &K) -> bool,
    arms: &[(K, A)],
) -> Vec<(K, Clause<A>)> {
    let groups = stable_group(arms, |(key1, body1), (key2, body2)| {
        shares(key1, key2) && same(body1, body2)
    });
    let mut result = Vec::with_capacity(arms.len());
    for group in groups {
        let last = group.len() - 1;
        for (index, (key, body)) in group.into_iter().enumerate() {
            if index == last {
                let run = p.add_tree(Tree::Run(body));
                result.push((key, Clause::Body(run)));
            } else {
                result.push((key, Clause::FallsThrough(Some(body))));
            }
        }
    }
    result
}

/// A subclass is checked before its superclasses, otherwise the declaration
/// order decides.
fn subclasses_first(mut instances: Vec<Instance>) -> Vec<Instance> {
    let mut ordered = Vec::with_capacity(instances.len());
    while !instances.is_empty() {
        let first = instances
            .iter()
            .find(|i| !instances.iter().any(|j| j.is_subclass(i)))
            .expect("subclass relation is acyclic")
            .clone();
        instances.retain(|i| *i != first);
        ordered.push(first);
    }
    ordered
}

/// An entry of the payload `if` chain: the check (`None`: unchecked), whether
/// it is a class check, and the arm body (`None`: the default).
type Entry = (Option<TestId>, bool, Option<TreeId>);

/// The payload cases, after the literals: one `switch (typeof x)` over the
/// primitive kinds, whose default is an `if` chain over the classes
/// (subclasses first), arrays, functions and objects.
#[allow(clippy::too_many_arguments)]
fn payload_part<A: Clone>(
    p: &mut Plan<A>,
    same: &impl Fn(&A, &A) -> bool,
    block_cases: &[BlockType],
    object_cases: &[ObjectCase],
    null_guard: bool,
    fallback: Option<&A>,
    has_default: bool,
    arms: &[(BlockType, A)],
    object_arms: &[(usize, A)],
) -> TreeId {
    match (arms, object_arms, has_default) {
        ([], [], true) => return p.add_tree(Tree::Fallback),
        ([], [], false) => return p.add_tree(Tree::Skip),
        ([(_, body)], [], false) | ([], [(_, body)], false) => {
            return p.add_tree(Tree::Run(body.clone()));
        }
        _ => {}
    }
    // An arm with the default's body is the default.
    let arms: Vec<(BlockType, A)> = match fallback {
        Some(fallback) if has_default => arms
            .iter()
            .filter(|(_, body)| !same(fallback, body))
            .cloned()
            .collect(),
        _ => arms.to_vec(),
    };
    let object_arms: Vec<(usize, A)> = match fallback {
        Some(fallback) if has_default => object_arms
            .iter()
            .filter(|(_, body)| !same(fallback, body))
            .cloned()
            .collect(),
        _ => object_arms.to_vec(),
    };
    let all_clauses = clauses(
        p,
        same,
        |k1, k2| is_primitive(k1) && is_primitive(k2),
        &arms,
    );
    let (primitive_clauses, other_clauses): (Vec<_>, Vec<_>) = all_clauses
        .into_iter()
        .partition(|(kind, _)| is_primitive(kind));
    let arm = |block_type: &BlockType| -> Option<TreeId> {
        other_clauses
            .iter()
            .find_map(|(kind, clause)| match clause {
                Clause::Body(tree) if kind == block_type => Some(*tree),
                _ => None,
            })
    };
    let instances = subclasses_first(
        block_cases
            .iter()
            .filter_map(|block_type| match block_type {
                BlockType::Instance(i) => Some(i.clone()),
                _ => None,
            })
            .collect(),
    );
    // `null`, when it did not go to the default before.
    let is_object = if null_guard {
        let typeof_object = p.add_test(Test::Typeof(BlockType::Object));
        let not_null = p.add_test(Test::NotNull);
        p.and(typeof_object, not_null)
    } else {
        p.add_test(Test::Typeof(BlockType::Object))
    };
    let mut entries: Vec<Entry> = Vec::new();
    // Tests on the fields of an object case, joined to the object check.
    let mut field_check: Option<TestId> = None;
    for i in &instances {
        let is_class = matches!(i, Instance::Class { .. });
        match arm(&BlockType::Instance(i.clone())) {
            Some(body) => {
                let check = p.add_test(Test::Instance(i.clone()));
                entries.push((Some(check), is_class, Some(body)));
            }
            None if has_default => {
                let check = p.add_test(Test::Instance(i.clone()));
                entries.push((Some(check), is_class, None));
            }
            None => {}
        }
    }
    if let Some(body) = arm(&BlockType::Function) {
        let check = p.add_test(Test::Typeof(BlockType::Function));
        entries.push((Some(check), false, Some(body)));
    }
    if object_cases.is_empty() {
        if let Some(body) = arm(&BlockType::Object) {
            entries.push((Some(is_object), false, Some(body)));
        }
    } else if let Some(mut region) = object_region(p, object_cases, &object_arms, has_default) {
        // With a default after it, `if (o) { if (t) body else default }` is
        // `if (o && t) body`, and `if (o) { if (t) default else body }` is
        // `if (o && !t) body`. The tests on fields are joined last, after the
        // checks that the value is of no earlier case.
        while has_default && let Tree::If(test, then_, else_) = *p.tree(region) {
            let test = if matches!(p.tree(else_), Tree::Fallback) {
                region = then_;
                test
            } else if matches!(p.tree(then_), Tree::Fallback) {
                region = else_;
                p.not(test)
            } else {
                break;
            };
            field_check = Some(match field_check {
                Some(check) => p.and(check, test),
                None => test,
            });
        }
        entries.push((Some(is_object), false, Some(region)));
    }
    if let Some(body) = arm(&BlockType::Unknown) {
        entries.push((None, false, Some(body)));
    }
    // Checks leading to the default are needed only before an arm.
    while matches!(entries.last(), Some((_, _, None))) {
        entries.pop();
    }
    // `if (c1) default else if (c2) body else default` is
    // `if (c2 && !c1) body else default`.
    if has_default && matches!(entries.last(), Some((Some(_), _, Some(_)))) {
        let (check, is_class, body) = entries.pop().expect("checked above");
        let mut check = check.expect("checked above");
        while matches!(entries.last(), Some((Some(_), _, None))) {
            let (previous, _, _) = entries.pop().expect("checked above");
            let not_previous = p.not(previous.expect("checked above"));
            check = p.and(check, not_previous);
        }
        entries.push((Some(check), is_class, body));
    }
    if let Some(fields) = field_check
        && let Some((Some(check), _, _)) = entries.last_mut()
    {
        *check = p.and(*check, fields);
    }
    // Consecutive checks leading to the default share one `if`.
    let mut merged: Vec<Entry> = Vec::with_capacity(entries.len());
    for entry in entries {
        match (merged.last_mut(), &entry) {
            (Some((Some(c1), class1, None)), (Some(c2), class2, None)) => {
                *c1 = p.or(*c1, *c2);
                *class1 = *class1 || *class2;
            }
            _ => merged.push(entry),
        }
    }
    let mut entries = merged;
    // An arm may compile to no statement, so arms are counted here.
    let has_other_arms = !entries.is_empty();
    // The last arm of a complete match is not checked.
    let final_tree = if has_default {
        p.add_tree(Tree::Fallback)
    } else {
        match entries.pop() {
            Some((_, _, Some(body))) => body,
            Some((_, _, None)) | None => p.add_tree(Tree::Skip),
        }
    };
    let has_class_check = entries.iter().any(|(_, is_class, _)| *is_class);
    let chain = |p: &mut Plan<A>, entries: Vec<Entry>| -> TreeId {
        let mut tree = final_tree;
        for (check, _, body) in entries.into_iter().rev() {
            let body = match body {
                Some(body) => body,
                None => p.add_tree(Tree::Fallback),
            };
            tree = match check {
                Some(check) => p.add_tree(Tree::If(check, body, tree)),
                None => body,
            };
        }
        tree
    };
    // The primitive kinds of the type without an arm go to the default
    // directly when the chain has class checks.
    let mut primitive_clauses = primitive_clauses;
    if has_default && has_class_check {
        let kinds: Vec<&BlockType> = block_cases
            .iter()
            .filter(|kind| is_primitive(kind) && !primitive_clauses.iter().any(|(k, _)| k == *kind))
            .collect();
        let last = kinds.len().saturating_sub(1);
        for (index, kind) in kinds.into_iter().enumerate() {
            let clause = if index == last {
                Clause::Body(p.add_tree(Tree::Fallback))
            } else {
                Clause::FallsThrough(None)
            };
            primitive_clauses.push((kind.clone(), clause));
        }
    }
    if primitive_clauses.is_empty() {
        let chain = chain(p, entries);
        return p.add_tree(Tree::Block(chain));
    }
    if !has_other_arms {
        // No other arm: in a complete match the last primitive arm is not
        // checked.
        if !has_default {
            let (_, last) = primitive_clauses.pop().expect("non-empty");
            let default = match last {
                Clause::Body(tree) => tree,
                Clause::FallsThrough(_) => p.add_tree(Tree::Skip),
            };
            // The cases falling through to that arm go to the default too.
            while matches!(primitive_clauses.last(), Some((_, Clause::FallsThrough(_)))) {
                primitive_clauses.pop();
            }
            return p.switch_typeof(primitive_clauses, default);
        }
        let fallback = p.add_tree(Tree::Fallback);
        return p.switch_typeof(primitive_clauses, fallback);
    }
    let chain = chain(p, entries);
    p.switch_typeof(primitive_clauses, chain)
}

/// The test of an object case: its checks joined with `&&`.
fn object_test<A>(p: &mut Plan<A>, checks: &[FieldCheck]) -> TestId {
    let mut tests = checks.iter().map(|check| match check {
        FieldCheck::Present(field) => p.add_test(Test::FieldIn(field.clone())),
        FieldCheck::Literals(field, literals) => {
            let mut literals = literals.iter();
            let first = literals.next().expect("a literal check has a literal");
            let mut test = p.add_test(Test::FieldEquals(field.clone(), first.clone()));
            for literal in literals {
                let equals = p.add_test(Test::FieldEquals(field.clone(), literal.clone()));
                test = p.or(test, equals);
            }
            test
        }
        FieldCheck::Kind(field, BlockType::Instance(Instance::Array(_))) => {
            p.add_test(Test::FieldIsArray(field.clone()))
        }
        FieldCheck::Kind(field, kind) => p.add_test(Test::FieldTypeof(field.clone(), kind.clone())),
    });
    let first = tests.next().expect("an object test has a check");
    let rest: Vec<TestId> = tests.collect();
    rest.into_iter().fold(first, |test, next| p.and(test, next))
}

/// The dispatch among several object cases, for values that are objects
/// and of no earlier case: the cases in the order of `cases`, each tested
/// with its checks, the last not tested. Without a default every value is
/// of a case with an arm, so only those are tested. `None` when no object
/// case has an arm.
fn object_region<A: Clone>(
    p: &mut Plan<A>,
    cases: &[ObjectCase],
    arms: &[(usize, A)],
    has_default: bool,
) -> Option<TreeId> {
    if arms.is_empty() {
        return None;
    }
    let body = |p: &mut Plan<A>, case: usize| match arms.iter().find(|(c, _)| *c == case) {
        Some((_, body)) => p.add_tree(Tree::Run(body.clone())),
        None => p.add_tree(Tree::Fallback),
    };
    let tested: Vec<usize> = (0..cases.len())
        .filter(|case| has_default || arms.iter().any(|(c, _)| c == case))
        .collect();
    let (last, earlier) = tested.split_last()?;
    let mut tree = body(p, *last);
    for case in earlier.iter().rev() {
        let test = object_test(p, &cases[*case].test);
        let then_ = body(p, *case);
        tree = p.add_tree(Tree::If(test, then_, tree));
    }
    Some(tree)
}

/// What constant folding knows about a constant: the JavaScript value it is
/// emitted as.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum Value {
    Literal(LiteralTag),
    /// A record or an inline record, which is no class instance.
    Object,
    /// A tuple, or a record whose fields are named 0, 1, …
    Array,
}

pub(crate) enum Outcome<A> {
    Arm(A),
    /// The match's default action.
    Default,
    /// No statement runs.
    Nothing,
}

/// What `typeof` returns for a value, as a kind.
fn kind_of(value: &Value) -> Option<BlockType> {
    match value {
        Value::Literal(LiteralTag::String(_)) => Some(BlockType::String),
        Value::Literal(LiteralTag::Int(_) | LiteralTag::Float(_)) => Some(BlockType::Number),
        Value::Literal(LiteralTag::BigInt(_)) => Some(BlockType::Bigint),
        Value::Literal(LiteralTag::Bool(_)) => Some(BlockType::Boolean),
        Value::Literal(LiteralTag::Null) | Value::Object | Value::Array => Some(BlockType::Object),
        Value::Literal(LiteralTag::Undefined) => None,
    }
}

/// What the code printed from a plan runs for a value. `on_test` sees each
/// test that is evaluated.
pub(crate) fn select<A: Clone>(
    plan: &Plan<A>,
    value: &Value,
    on_test: &mut impl FnMut(&Test),
) -> Outcome<A> {
    select_tree(plan, plan.root, value, on_test)
}

fn select_tree<A: Clone>(
    p: &Plan<A>,
    tree: TreeId,
    value: &Value,
    on_test: &mut impl FnMut(&Test),
) -> Outcome<A> {
    // JavaScript semantics, including the short circuits of `&&` and `||`.
    // `None` when the outcome depends on a field, which constant folding
    // does not know.
    fn holds<A>(
        p: &Plan<A>,
        test: TestId,
        value: &Value,
        on_test: &mut impl FnMut(&Test),
    ) -> Option<bool> {
        let test = p.test(test);
        on_test(test);
        Some(match (test, value) {
            (Test::Equals(literal), Value::Literal(v)) => same_literal_value(v, literal),
            (Test::Equals(_), Value::Object | Value::Array) => false,
            (Test::Typeof(kind), _) => kind_of(value).as_ref() == Some(kind),
            (Test::Instance(Instance::Array(_)), _) => *value == Value::Array,
            (Test::Instance(Instance::Class { .. }), _) => false,
            (Test::NotNull, _) => *value != Value::Literal(LiteralTag::Null),
            (
                Test::FieldIn(_)
                | Test::FieldEquals(..)
                | Test::FieldTypeof(..)
                | Test::FieldIsArray(_),
                _,
            ) => return None,
            (Test::Not(test), _) => !holds(p, *test, value, on_test)?,
            (Test::And(t1, t2), _) => {
                holds(p, *t1, value, on_test)? && holds(p, *t2, value, on_test)?
            }
            (Test::Or(t1, t2), _) => {
                holds(p, *t1, value, on_test)? || holds(p, *t2, value, on_test)?
            }
        })
    }
    fn from_clauses<K, A: Clone>(
        p: &Plan<A>,
        matches: impl Fn(&K) -> bool,
        clauses: &[(K, Clause<A>)],
        default: TreeId,
        value: &Value,
        on_test: &mut impl FnMut(&Test),
    ) -> Outcome<A> {
        // A matching case runs its body, or falls through to the next one.
        match clauses.iter().position(|(key, _)| matches(key)) {
            None => run(p, default, value, on_test),
            Some(start) => {
                for (_, clause) in &clauses[start..] {
                    if let Clause::Body(tree) = clause {
                        return run(p, *tree, value, on_test);
                    }
                }
                run(p, default, value, on_test)
            }
        }
    }
    fn run<A: Clone>(
        p: &Plan<A>,
        tree: TreeId,
        value: &Value,
        on_test: &mut impl FnMut(&Test),
    ) -> Outcome<A> {
        match p.tree(tree) {
            Tree::Run(body) => Outcome::Arm(body.clone()),
            Tree::Fallback => Outcome::Default,
            Tree::Skip => Outcome::Nothing,
            Tree::If(test, then_, else_) => match holds(p, *test, value, on_test) {
                // Constant folding does not know the fields of a constant: the
                // dispatch stays.
                None => Outcome::Nothing,
                Some(true) => run(p, *then_, value, on_test),
                Some(false) => run(p, *else_, value, on_test),
            },
            Tree::Block(tree) => run(p, *tree, value, on_test),
            Tree::SwitchValue(clauses, default) => match value {
                Value::Literal(v) => from_clauses(
                    p,
                    |literal| same_literal_value(v, literal),
                    p.value_clauses(*clauses),
                    *default,
                    value,
                    on_test,
                ),
                Value::Object | Value::Array => run(p, *default, value, on_test),
            },
            Tree::SwitchTypeof(clauses, default) => match kind_of(value) {
                Some(kind) => from_clauses(
                    p,
                    |k| *k == kind,
                    p.typeof_clauses(*clauses),
                    *default,
                    value,
                    on_test,
                ),
                None => run(p, *default, value, on_test),
            },
        }
    }
    run(p, tree, value, on_test)
}

/// Two trees that run the same bodies after the same tests.
fn same_tree<A>(p: &Plan<A>, same: &impl Fn(&A, &A) -> bool, tree1: TreeId, tree2: TreeId) -> bool {
    match (p.tree(tree1), p.tree(tree2)) {
        (Tree::Run(b1), Tree::Run(b2)) => same(b1, b2),
        (Tree::Fallback, Tree::Fallback) | (Tree::Skip, Tree::Skip) => true,
        (Tree::If(t1, then1, else1), Tree::If(t2, then2, else2)) => {
            p.same_test(*t1, *t2)
                && same_tree(p, same, *then1, *then2)
                && same_tree(p, same, *else1, *else2)
        }
        (Tree::Block(t1), Tree::Block(t2)) => same_tree(p, same, *t1, *t2),
        (Tree::SwitchValue(c1, d1), Tree::SwitchValue(c2, d2)) => {
            same_clauses(p, same, p.value_clauses(*c1), p.value_clauses(*c2))
                && same_tree(p, same, *d1, *d2)
        }
        (Tree::SwitchTypeof(c1, d1), Tree::SwitchTypeof(c2, d2)) => {
            same_clauses(p, same, p.typeof_clauses(*c1), p.typeof_clauses(*c2))
                && same_tree(p, same, *d1, *d2)
        }
        _ => false,
    }
}

fn same_clauses<K: PartialEq, A>(
    p: &Plan<A>,
    same: &impl Fn(&A, &A) -> bool,
    clauses1: &[(K, Clause<A>)],
    clauses2: &[(K, Clause<A>)],
) -> bool {
    clauses1.len() == clauses2.len()
        && clauses1.iter().zip(clauses2).all(|((k1, c1), (k2, c2))| {
            k1 == k2
                && match (c1, c2) {
                    (Clause::FallsThrough(_), Clause::FallsThrough(_)) => true,
                    (Clause::Body(t1), Clause::Body(t2)) => same_tree(p, same, *t1, *t2),
                    _ => false,
                }
        })
}

/// A test whose branches run the same is not run, and a case of a switch that
/// runs what its default runs is left to the default, with the cases falling
/// through to it.
fn simplify<A: Clone>(p: &mut Plan<A>, same: &impl Fn(&A, &A) -> bool, tree: TreeId) -> TreeId {
    match p.tree(tree).clone() {
        Tree::Run(_) | Tree::Fallback | Tree::Skip => tree,
        Tree::If(test, then_, else_) => {
            let then_ = simplify(p, same, then_);
            let else_ = simplify(p, same, else_);
            if same_tree(p, same, then_, else_) {
                then_
            } else {
                p.add_tree(Tree::If(test, then_, else_))
            }
        }
        Tree::Block(inner) => {
            let inner = simplify(p, same, inner);
            p.add_tree(Tree::Block(inner))
        }
        Tree::SwitchValue(clauses, default) => {
            let default = simplify(p, same, default);
            let clauses = p.value_clauses(clauses).to_vec();
            let clauses = simplify_clauses(p, same, default, clauses);
            if clauses.is_empty() {
                default
            } else {
                p.switch_value(clauses, default)
            }
        }
        Tree::SwitchTypeof(clauses, default) => {
            let default = simplify(p, same, default);
            let clauses = p.typeof_clauses(clauses).to_vec();
            let clauses = simplify_clauses(p, same, default, clauses);
            if clauses.is_empty() {
                default
            } else {
                p.switch_typeof(clauses, default)
            }
        }
    }
}

fn simplify_clauses<K, A: Clone>(
    p: &mut Plan<A>,
    same: &impl Fn(&A, &A) -> bool,
    default: TreeId,
    clauses: Vec<(K, Clause<A>)>,
) -> Vec<(K, Clause<A>)> {
    // The cases falling through to a body, then the body.
    let mut groups: Vec<Vec<(K, Clause<A>)>> = Vec::new();
    let mut pending = Vec::new();
    for clause in clauses {
        let is_body = matches!(clause.1, Clause::Body(_));
        pending.push(clause);
        if is_body {
            groups.push(std::mem::take(&mut pending));
        }
    }
    if !pending.is_empty() {
        groups.push(pending);
    }
    let mut result = Vec::new();
    for mut group in groups {
        match group.pop() {
            Some((key, Clause::Body(tree))) => {
                let tree = simplify(p, same, tree);
                if !same_tree(p, same, tree, default) {
                    result.extend(group);
                    result.push((key, Clause::Body(tree)));
                }
            }
            Some(last) => {
                result.extend(group);
                result.push(last);
            }
            None => {}
        }
    }
    result
}

/// untagged_dispatch.ml `plan`; `same` tells two bodies that are one body
/// apart.
pub(crate) fn plan<A: Clone>(same: impl Fn(&A, &A) -> bool, input: Input<'_, A>) -> Plan<A> {
    let mut p = Plan::new();
    p.root = plan_tree(&mut p, &same, input);
    p
}

fn plan_tree<A: Clone>(
    p: &mut Plan<A>,
    same: &impl Fn(&A, &A) -> bool,
    input: Input<'_, A>,
) -> TreeId {
    let Input {
        facts,
        literal_arms,
        payload_arms,
        object_arms,
        literals_complete,
        payloads_complete,
        fallback,
    } = input;
    let block_cases = &facts.block_types[..];
    let object_cases = &facts.object_cases[..];
    let literal_cases = &facts.literal_tags[..];
    let literal_default = if literals_complete {
        None
    } else {
        fallback.as_ref()
    };
    let mut payload_has_default = !payloads_complete && fallback.is_some();
    if literals_complete && literal_arms.is_empty() {
        let payload = payload_part(
            p,
            same,
            block_cases,
            object_cases,
            false,
            fallback.as_ref(),
            payload_has_default,
            &payload_arms,
            &object_arms,
        );
        return simplify(p, same, payload);
    }
    // The literals first, compared with `===` by one switch whose default is
    // the payload dispatch. A literal without an arm goes to the match's
    // default, never to a payload arm.
    let unnamed: Vec<&LiteralTag> = literal_cases
        .iter()
        .filter(|literal| !literal_arms.iter().any(|(named, _)| named == *literal))
        .collect();
    // A literal without an arm skips the switch when the payload dispatch
    // takes it to the default without a class check, which could throw when
    // the class does not exist.
    let skip_payload = literal_default.map(|_| {
        payload_part(
            p,
            same,
            block_cases,
            object_cases,
            unnamed.iter().any(|l| **l == LiteralTag::Null),
            fallback.as_ref(),
            true,
            &payload_arms,
            &object_arms,
        )
    });
    let skips_the_switch = |p: &Plan<A>, literal: &LiteralTag| -> bool {
        match skip_payload {
            None => false,
            Some(payload) => {
                let mut class_check = false;
                let outcome =
                    select_tree(p, payload, &Value::Literal(literal.clone()), &mut |test| {
                        if matches!(test, Test::Instance(Instance::Class { .. })) {
                            class_check = true;
                        }
                    });
                match outcome {
                    Outcome::Default => !class_check,
                    Outcome::Arm(_) | Outcome::Nothing => false,
                }
            }
        }
    };
    // Values no payload arm takes are the literals without an arm.
    payload_has_default = payload_has_default
        || (literal_default.is_some() && unnamed.iter().any(|l| skips_the_switch(p, l)));
    let null_guard = literal_default.is_some()
        && payload_has_default
        && unnamed
            .iter()
            .any(|literal| **literal == LiteralTag::Null && skips_the_switch(p, literal));
    let unnamed_arms: Vec<(LiteralTag, A)> = match literal_default {
        Some(fallback) => unnamed
            .iter()
            .filter(|literal| !(payload_has_default && skips_the_switch(p, literal)))
            .map(|literal| ((*literal).clone(), fallback.clone()))
            .collect(),
        None => Vec::new(),
    };
    let mut literal_arms = literal_arms;
    literal_arms.extend(unnamed_arms);
    let payload = payload_part(
        p,
        same,
        block_cases,
        object_cases,
        null_guard,
        fallback.as_ref(),
        payload_has_default,
        &payload_arms,
        &object_arms,
    );
    let payload = simplify(p, same, payload);
    // A payload dispatch that runs one body unchecked takes the literals with
    // that body too.
    if let Tree::Run(body) = p.tree(payload) {
        let body = body.clone();
        literal_arms.retain(|(_, other)| !same(&body, other));
    }
    if literal_arms.len() <= 2 {
        // An `if` per body, testing its literals with `===`.
        let mut groups: Vec<(Vec<LiteralTag>, A)> = Vec::new();
        let mut rest = literal_arms;
        while !rest.is_empty() {
            let (literal, body) = rest.remove(0);
            let (same_body, others): (Vec<_>, Vec<_>) =
                rest.into_iter().partition(|(_, other)| same(&body, other));
            let mut literals = vec![literal];
            literals.extend(same_body.into_iter().map(|(literal, _)| literal));
            groups.push((literals, body));
            rest = others;
        }
        let mut tree = payload;
        for (literals, body) in groups.into_iter().rev() {
            let mut literals = literals.into_iter();
            let mut test = p.add_test(Test::Equals(literals.next().expect("non-empty group")));
            for literal in literals {
                let equals = p.add_test(Test::Equals(literal));
                test = p.or(test, equals);
            }
            let run = p.add_tree(Tree::Run(body));
            tree = p.add_tree(Tree::If(test, run, tree));
        }
        tree
    } else {
        let clauses = clauses(p, same, |_, _| true, &literal_arms);
        let switch = p.switch_value(clauses, payload);
        simplify(p, same, switch)
    }
}

/// Port of upstream's `tests/ounit_tests/ounit_untagged_dispatch_tests.ml`:
/// the expected plans are upstream's.
#[cfg(test)]
mod tests {
    use super::*;

    type P = Plan<&'static str>;

    fn test_to_string(p: &P, test: TestId) -> String {
        match p.test(test) {
            Test::Equals(literal) => format!("x === {}", literal.value_key()),
            Test::Typeof(block_type) => {
                format!("typeof x === {}", block_type.typeof_name().unwrap_or("?"))
            }
            Test::Instance(instance) => format!("x instanceof {}", instance.as_str()),
            Test::NotNull => "x !== null".to_string(),
            Test::FieldIn(field) => format!("\"{field}\" in x"),
            Test::FieldEquals(field, literal) => format!("x.{field} === {}", literal.value_key()),
            Test::FieldTypeof(field, kind) => {
                format!("typeof x.{field} === {}", kind.typeof_name().unwrap_or("?"))
            }
            Test::FieldIsArray(field) => format!("Array.isArray(x.{field})"),
            Test::Not(test) => format!("!({})", test_to_string(p, *test)),
            Test::And(t1, t2) => {
                format!("({} && {})", test_to_string(p, *t1), test_to_string(p, *t2))
            }
            Test::Or(t1, t2) => {
                format!("({} || {})", test_to_string(p, *t1), test_to_string(p, *t2))
            }
        }
    }

    fn tree_to_string(p: &P, tree: TreeId) -> String {
        match p.tree(tree) {
            Tree::Run(body) => body.to_string(),
            Tree::Fallback => "fallback".to_string(),
            Tree::Skip => "skip".to_string(),
            Tree::If(test, then_, else_) => format!(
                "if ({}) {} else {}",
                test_to_string(p, *test),
                tree_to_string(p, *then_),
                tree_to_string(p, *else_)
            ),
            Tree::Block(tree) => format!("{{{}}}", tree_to_string(p, *tree)),
            Tree::SwitchValue(clauses, default) => format!(
                "switch (x) {{{}default: {}}}",
                p.value_clauses(*clauses)
                    .iter()
                    .map(|(literal, clause)| format!(
                        "{}: {}; ",
                        literal.value_key(),
                        clause_to_string(p, clause)
                    ))
                    .collect::<String>(),
                tree_to_string(p, *default)
            ),
            Tree::SwitchTypeof(clauses, default) => format!(
                "switch (typeof x) {{{}default: {}}}",
                p.typeof_clauses(*clauses)
                    .iter()
                    .map(|(block_type, clause)| format!(
                        "{}: {}; ",
                        block_type.typeof_name().unwrap_or("?"),
                        clause_to_string(p, clause)
                    ))
                    .collect::<String>(),
                tree_to_string(p, *default)
            ),
        }
    }

    fn clause_to_string(p: &P, clause: &Clause<&'static str>) -> String {
        match clause {
            Clause::FallsThrough(_) => "falls through".to_string(),
            Clause::Body(tree) => tree_to_string(p, *tree),
        }
    }

    fn class(name: &str, ancestors: &[&str]) -> BlockType {
        BlockType::Instance(Instance::Class {
            name: name.to_string(),
            ancestors: ancestors.iter().map(|a| a.to_string()).collect(),
            blocks: crate::types::ClassBlocks::fresh(ancestors.len()),
        })
    }

    fn s(value: &str) -> LiteralTag {
        LiteralTag::String(value.to_string())
    }

    /// The plan of a match with these arms on a variant with these literal
    /// and payload cases; `fallback` is the match's default.
    fn plan_of(
        literals: Vec<LiteralTag>,
        kinds: Vec<BlockType>,
        fallback: Option<&'static str>,
        literal_arms: Vec<(LiteralTag, &'static str)>,
        payload_arms: Vec<(BlockType, &'static str)>,
    ) -> P {
        let facts = MatchingFacts {
            tag_name: None,
            block_types: kinds.clone(),
            literal_tags: literals.clone(),
            object_cases: Vec::new(),
        };
        plan(
            |a: &&str, b: &&str| a == b,
            Input {
                facts: &facts,
                literals_complete: literal_arms.len() == literals.len(),
                payloads_complete: payload_arms.len() == kinds.len(),
                literal_arms,
                payload_arms,
                object_arms: Vec::new(),
                fallback,
            },
        )
    }

    fn assert_plan(expected: &str, plan: P) {
        assert_eq!(tree_to_string(&plan, plan.root()), expected);
    }

    /// A small deterministic generator for the random matches.
    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }
        fn int(&mut self, bound: u64) -> u64 {
            self.next() % bound
        }
        fn bool(&mut self) -> bool {
            self.int(2) == 0
        }
    }

    type Case = (
        Vec<LiteralTag>,
        Vec<BlockType>,
        Vec<(LiteralTag, &'static str)>,
        Vec<(BlockType, &'static str)>,
    );

    fn random_case(rng: &mut Rng) -> Case {
        fn some_of<T>(rng: &mut Rng, list: Vec<T>) -> Vec<T> {
            list.into_iter().filter(|_| rng.bool()).collect()
        }
        // A literal of each kind.
        let literals = some_of(
            rng,
            vec![
                s("a"),
                s("b"),
                LiteralTag::Int(1),
                LiteralTag::Float("1.5".into()),
                LiteralTag::Bool(true),
                LiteralTag::Null,
                LiteralTag::Undefined,
                LiteralTag::BigInt("2".into()),
            ],
        );
        let kinds = if rng.int(10) == 0 {
            vec![BlockType::Unknown]
        } else {
            some_of(
                rng,
                vec![
                    BlockType::String,
                    BlockType::Number,
                    BlockType::Bigint,
                    BlockType::Boolean,
                    BlockType::Symbol,
                    BlockType::Function,
                    BlockType::Object,
                    BlockType::Instance(Instance::Array(crate::types::ShapeAllocation::fresh())),
                    class("Date", &[]),
                    class("Animal", &[]),
                    class("Dog", &["Animal"]),
                ],
            )
            .into_iter()
            // A boolean payload needs a boolean that is not a literal case.
            .filter(|kind| {
                *kind != BlockType::Boolean || !literals.contains(&LiteralTag::Bool(true))
            })
            .collect()
        };
        fn arms<K: Clone>(rng: &mut Rng, cases: &[K]) -> Vec<(K, &'static str)> {
            cases
                .iter()
                .filter_map(|case| {
                    if rng.int(5) < 3 {
                        Some((case.clone(), ["b0", "b1", "b2"][rng.int(3) as usize]))
                    } else {
                        None
                    }
                })
                .collect()
        }
        let literal_arms = arms(rng, &literals);
        let payload_arms = arms(rng, &kinds);
        (literals, kinds, literal_arms, payload_arms)
    }

    /// Rules 7 to 9: a literal case takes its arm, any other value the arm of
    /// its kind, and a case without an arm the default. `None` for a value of
    /// no case.
    fn oracle(case: &Case, value: &Value) -> Option<String> {
        let (literals, kinds, literal_arms, payload_arms) = case;
        fn of_arm<K: PartialEq>(arms: &[(K, &'static str)], case: &K) -> String {
            arms.iter()
                .find(|(k, _)| k == case)
                .map_or("default".to_string(), |(_, body)| body.to_string())
        }
        let declared = |kind: &BlockType| kinds.contains(kind);
        let kind_case = if declared(&BlockType::Unknown) {
            Some(BlockType::Unknown)
        } else {
            match value {
                Value::Literal(LiteralTag::String(_)) => Some(BlockType::String),
                Value::Literal(LiteralTag::Int(_) | LiteralTag::Float(_)) => {
                    Some(BlockType::Number)
                }
                Value::Literal(LiteralTag::BigInt(_)) => Some(BlockType::Bigint),
                Value::Literal(LiteralTag::Bool(_)) => Some(BlockType::Boolean),
                Value::Literal(LiteralTag::Null | LiteralTag::Undefined) => None,
                Value::Object => Some(BlockType::Object),
                Value::Array => {
                    if declared(&BlockType::Instance(Instance::Array(
                        crate::types::ShapeAllocation::fresh(),
                    ))) {
                        Some(BlockType::Instance(Instance::Array(
                            crate::types::ShapeAllocation::fresh(),
                        )))
                    } else {
                        Some(BlockType::Object)
                    }
                }
            }
        };
        match value {
            Value::Literal(literal) if literals.iter().any(|l| same_literal_value(literal, l)) => {
                Some(of_arm(literal_arms, literal))
            }
            _ => match kind_case {
                Some(kind) if declared(&kind) => Some(of_arm(payload_arms, &kind)),
                _ => None,
            },
        }
    }

    /// One value of each case of the variant.
    fn values(literals: &[LiteralTag], kinds: &[BlockType]) -> Vec<Value> {
        let mut values: Vec<Value> = literals.iter().cloned().map(Value::Literal).collect();
        for kind in kinds {
            match kind {
                BlockType::String => values.push(Value::Literal(s("fresh"))),
                BlockType::Number => values.push(Value::Literal(LiteralTag::Int(98765))),
                BlockType::Bigint => values.push(Value::Literal(LiteralTag::BigInt("77".into()))),
                BlockType::Boolean => values.push(Value::Literal(LiteralTag::Bool(false))),
                BlockType::Object => values.push(Value::Object),
                BlockType::Instance(Instance::Array(_)) => values.push(Value::Array),
                BlockType::Unknown => {
                    values.extend([Value::Object, Value::Array, Value::Literal(s("fresh"))])
                }
                BlockType::Symbol | BlockType::Function | BlockType::Instance(_) => {}
            }
        }
        values
    }

    #[test]
    fn every_plan_takes_the_arms_rules_7_to_9_give() {
        let mut rng = Rng(8955);
        for _ in 0..3000 {
            let case = random_case(&mut rng);
            let (literals, kinds, literal_arms, payload_arms) = case.clone();
            let complete =
                literal_arms.len() == literals.len() && payload_arms.len() == kinds.len();
            let tree = plan_of(
                literals.clone(),
                kinds.clone(),
                (!complete).then_some("default"),
                literal_arms,
                payload_arms,
            );
            for value in values(&literals, &kinds) {
                let mut class_checks = 0;
                let outcome = select(&tree, &value, &mut |test: &Test| {
                    if matches!(test, Test::Instance(Instance::Class { .. })) {
                        class_checks += 1;
                    }
                });
                // A literal or a primitive never reaches a class check.
                assert!(
                    !(matches!(value, Value::Literal(_)) && class_checks > 0),
                    "a class check on {value:?} in {}",
                    tree_to_string(&tree, tree.root())
                );
                if let Some(expected) = oracle(&case, &value) {
                    let outcome = match outcome {
                        Outcome::Arm(body) => body.to_string(),
                        Outcome::Default => "default".to_string(),
                        Outcome::Nothing => "nothing".to_string(),
                    };
                    assert_eq!(
                        outcome,
                        expected,
                        "{value:?} in {}",
                        tree_to_string(&tree, tree.root())
                    );
                }
            }
        }
    }

    #[test]
    fn a_literal_no_payload_arm_takes_skips_the_switch() {
        assert_plan(
            "switch (typeof x) {number: int; default: fallback}",
            plan_of(
                vec![s("a"), s("b")],
                vec![BlockType::Number],
                Some("default"),
                vec![],
                vec![(BlockType::Number, "int")],
            ),
        );
    }

    #[test]
    fn a_literal_a_payload_arm_takes_is_tested_first() {
        assert_plan(
            "if (x === string:a) a else string",
            plan_of(
                vec![s("a")],
                vec![BlockType::String],
                None,
                vec![(s("a"), "a")],
                vec![(BlockType::String, "string")],
            ),
        );
    }

    #[test]
    fn a_skipping_null_adds_a_null_check_to_the_object_arm() {
        assert_plan(
            "switch (typeof x) {string: string; default: if ((typeof x === object && x !== null)) object else fallback}",
            plan_of(
                vec![LiteralTag::Null],
                vec![BlockType::String, BlockType::Object],
                Some("default"),
                vec![],
                vec![(BlockType::String, "string"), (BlockType::Object, "object")],
            ),
        );
    }

    #[test]
    fn a_subclass_is_checked_before_its_superclass() {
        assert_plan(
            "switch (typeof x) {string: string; default: if ((x instanceof Animal && !(x instanceof Dog))) animal else fallback}",
            plan_of(
                vec![],
                vec![
                    class("Animal", &[]),
                    class("Dog", &["Animal"]),
                    BlockType::String,
                ],
                Some("default"),
                vec![],
                vec![
                    (class("Animal", &[]), "animal"),
                    (BlockType::String, "string"),
                ],
            ),
        );
    }

    #[test]
    fn the_last_arm_of_a_complete_match_is_not_checked() {
        assert_plan(
            "{if (x instanceof Date) date else regexp}",
            plan_of(
                vec![],
                vec![class("Date", &[]), class("RegExp", &[])],
                None,
                vec![],
                vec![
                    (class("Date", &[]), "date"),
                    (class("RegExp", &[]), "regexp"),
                ],
            ),
        );
    }

    #[test]
    fn literals_with_one_body_share_a_case() {
        assert_plan(
            "switch (x) {string:b: y; string:a: falls through; string:c: x; default: string}",
            plan_of(
                vec![s("a"), s("b"), s("c")],
                vec![BlockType::String],
                None,
                vec![(s("a"), "x"), (s("b"), "y"), (s("c"), "x")],
                vec![(BlockType::String, "string")],
            ),
        );
    }

    #[test]
    fn two_literals_with_one_body_are_one_test() {
        assert_plan(
            "if ((x === number:0x1p+0 || x === number:0x1p+1)) one else number",
            plan_of(
                vec![LiteralTag::Int(1), LiteralTag::Int(2)],
                vec![BlockType::Number],
                None,
                vec![(LiteralTag::Int(1), "one"), (LiteralTag::Int(2), "one")],
                vec![(BlockType::Number, "number")],
            ),
        );
    }

    #[test]
    fn primitive_kinds_without_an_arm_go_to_the_default_before_class_checks() {
        assert_plan(
            "switch (typeof x) {string: string; number: fallback; default: if (x instanceof Date) date else fallback}",
            plan_of(
                vec![],
                vec![BlockType::String, BlockType::Number, class("Date", &[])],
                Some("default"),
                vec![],
                vec![(BlockType::String, "string"), (class("Date", &[]), "date")],
            ),
        );
    }
}
