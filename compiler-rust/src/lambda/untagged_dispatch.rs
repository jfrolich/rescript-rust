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

mod metadata;
use crate::types::variant_runtime::{BlockType, LiteralTag, MatchingFacts};
pub(crate) use metadata::{InstanceId, Kind, Literal, LiteralId, Metadata};

#[derive(Debug, Clone, Default)]
pub(crate) struct Facts {
    pub literal_tags: Vec<LiteralId>,
    pub block_types: Vec<Kind>,
}
impl Metadata {
    pub(crate) fn import_facts(&mut self, facts: &MatchingFacts) -> Facts {
        Facts {
            literal_tags: facts
                .literal_tags
                .iter()
                .map(|tag| self.import_literal(tag))
                .collect(),
            block_types: facts
                .block_types
                .iter()
                .map(|kind| self.import_kind(kind))
                .collect(),
        }
    }
}

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
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Test {
    /// `x === literal`
    Equals(LiteralId),
    /// `typeof x === "k"`, for a kind with a `typeof` name
    Typeof(Kind),
    /// `Array.isArray(x)` or `x instanceof C`
    Instance(InstanceId),
    /// `x !== null`
    NotNull,
    Not(TestId),
    And(TestId, TestId),
    Or(TestId, TestId),
}

/// How the generated code reaches the bodies `A` (untagged_dispatch.mli
/// `tree`).
#[derive(Debug, Clone, Copy)]
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
#[derive(Debug, Clone, Copy)]
pub(crate) enum Clause<A> {
    /// An empty case falling through to the next one; the body only gives
    /// the source location.
    FallsThrough(Option<A>),
    /// A `Run` or `Fallback`.
    Body(TreeId),
}

const NONE: usize = usize::MAX;
#[derive(Debug, Clone, Default)]
struct Groups {
    heads: Vec<usize>,
    next: Vec<usize>,
    bucket_links: Vec<usize>,
    buckets: Vec<(usize, usize)>,
    steps: usize,
}
impl Groups {
    /// Stable grouping from the tail: first-created matching group wins, and
    /// its representative becomes the newly prepended arm. Buckets only narrow
    /// candidate equality tests; they never establish equality themselves.
    fn build<K, A>(
        &mut self,
        arms: &[(K, A)],
        same: &impl Fn(&A, &A) -> bool,
        shares: impl Fn(&K, &K) -> bool,
        bucket: &impl Fn(&A) -> usize,
    ) {
        self.heads.clear();
        self.bucket_links.clear();
        self.next.resize(arms.len(), NONE);
        self.next.fill(NONE);
        let buckets = arms
            .iter()
            .map(|(_, body)| bucket(body))
            .max()
            .map_or(0, |b| b + 1);
        self.buckets.resize(buckets, (NONE, NONE));
        self.buckets.fill((NONE, NONE));
        for i in (0..arms.len()).rev() {
            self.steps += 1;
            let (key, body) = &arms[i];
            let b = bucket(body);
            let (mut group, tail) = self.buckets[b];
            while group != NONE {
                self.steps += 1;
                let (other_key, other_body) = &arms[self.heads[group]];
                if shares(key, other_key) && same(body, other_body) {
                    break;
                }
                group = self.bucket_links[group];
            }
            if group == NONE {
                group = self.heads.len();
                self.heads.push(i);
                self.bucket_links.push(NONE);
                if tail == NONE {
                    self.buckets[b].0 = group;
                } else {
                    self.bucket_links[tail] = group;
                }
                self.buckets[b].1 = group;
            } else {
                self.next[i] = self.heads[group];
                self.heads[group] = i;
            }
        }
    }
}

#[derive(Debug, Clone)]
struct Scratch<A> {
    arms: Vec<(Kind, A)>,
    all: Vec<(Kind, Clause<A>)>,
    primitive: Vec<(Kind, Clause<A>)>,
    other: Vec<(Kind, Clause<A>)>,
    instances: Vec<InstanceId>,
    ordered: Vec<InstanceId>,
    entries: Vec<Entry>,
    merged: Vec<Entry>,
    missing: Vec<Kind>,
    literals: Vec<(LiteralId, A)>,
    literal_clauses: Vec<(LiteralId, Clause<A>)>,
    unnamed: Vec<LiteralId>,
    membership: Vec<u64>,
}
impl<A> Default for Scratch<A> {
    fn default() -> Self {
        Self {
            arms: Vec::new(),
            all: Vec::new(),
            primitive: Vec::new(),
            other: Vec::new(),
            instances: Vec::new(),
            ordered: Vec::new(),
            entries: Vec::new(),
            merged: Vec::new(),
            missing: Vec::new(),
            literals: Vec::new(),
            literal_clauses: Vec::new(),
            unnamed: Vec::new(),
            membership: Vec::new(),
        }
    }
}
#[derive(Debug, Clone, Copy)]
enum SelectOp {
    Test(TestId),
    Not,
    And(TestId),
    Or(TestId),
}
/// A plan: its pools and the root of its tree.
#[derive(Debug, Clone)]
pub(crate) struct Plan<A> {
    pub(crate) metadata: Metadata,
    tests: Vec<Test>,
    trees: Vec<Tree<A>>,
    value_clauses: Vec<(LiteralId, Clause<A>)>,
    typeof_clauses: Vec<(Kind, Clause<A>)>,
    root: TreeId,
    groups: Groups,
    scratch: Scratch<A>,
    simplify_work: Vec<(TreeId, bool)>,
    simplify_map: Vec<(u64, TreeId)>,
    simplify_epoch: u64,
    membership_epoch: u64,
    equal_trees: Vec<(TreeId, TreeId)>,
    equal_tests: Vec<(TestId, TestId)>,
    selector_work: Vec<SelectOp>,
}

impl<A> Default for Plan<A> {
    /// O(1): empty unit pools defer allocation until graph construction.
    fn default() -> Self {
        Self::new()
    }
}

impl<A> Plan<A> {
    fn new() -> Self {
        Plan {
            metadata: Metadata::default(),
            tests: Vec::new(),
            trees: Vec::new(),
            value_clauses: Vec::new(),
            typeof_clauses: Vec::new(),
            root: TreeId(0),
            groups: Groups::default(),
            scratch: Scratch::default(),
            simplify_work: Vec::new(),
            simplify_map: Vec::new(),
            simplify_epoch: 0,
            membership_epoch: 0,
            equal_trees: Vec::new(),
            equal_tests: Vec::new(),
            selector_work: Vec::new(),
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

    pub(crate) fn value_clauses(&self, clauses: Clauses) -> &[(LiteralId, Clause<A>)] {
        &self.value_clauses[clauses.range()]
    }

    pub(crate) fn typeof_clauses(&self, clauses: Clauses) -> &[(Kind, Clause<A>)] {
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

    fn switch_value(&mut self, clauses: &[(LiteralId, Clause<A>)], default: TreeId) -> TreeId
    where
        A: Copy,
    {
        let start = self.value_clauses.len() as u32;
        let len = clauses.len() as u32;
        self.value_clauses.extend_from_slice(clauses);
        self.add_tree(Tree::SwitchValue(Clauses { start, len }, default))
    }

    fn switch_typeof(&mut self, clauses: &[(Kind, Clause<A>)], default: TreeId) -> TreeId
    where
        A: Copy,
    {
        let start = self.typeof_clauses.len() as u32;
        let len = clauses.len() as u32;
        self.typeof_clauses.extend_from_slice(clauses);
        self.add_tree(Tree::SwitchTypeof(Clauses { start, len }, default))
    }
}

pub(crate) struct Input<'f, A> {
    pub facts: &'f MatchingFacts,
    /// The arms of the literal cases, in the order of the match.
    pub literal_arms: Vec<(LiteralTag, A)>,
    /// The arms of the payload cases, in the order of the match.
    pub payload_arms: Vec<(BlockType, A)>,
    /// Every literal case has an arm.
    pub literals_complete: bool,
    /// Every payload case has an arm.
    pub payloads_complete: bool,
    /// The default action of the match, for the cases without an arm.
    pub fallback: Option<A>,
}

/// Borrowed inputs for appending a plan to a unit-owned graph pool.
/// Metadata and arm storage need only live for the planning call.
pub(crate) struct BorrowedInput<'f, A> {
    pub facts: &'f Facts,
    pub literal_arms: &'f [(LiteralId, A)],
    pub payload_arms: &'f [(Kind, A)],
    pub literals_complete: bool,
    pub payloads_complete: bool,
    pub fallback: Option<A>,
}
type PlanInput<'f, A> = BorrowedInput<'f, A>;

/// The kinds `switch (typeof x)` tells apart; functions and objects are
/// checked after the classes.
fn is_primitive(kind: &Kind) -> bool {
    matches!(
        kind,
        Kind::Number | Kind::String | Kind::Bigint | Kind::Boolean | Kind::Symbol
    )
}

/// Stable source groups, emitted in reverse creation order with members in
/// source order. The same algorithm serves legacy and dense BIR body aliases.
fn clauses<K: Copy, A: Copy>(
    p: &mut Plan<A>,
    same: &impl Fn(&A, &A) -> bool,
    bucket: &impl Fn(&A) -> usize,
    shares: impl Fn(&K, &K) -> bool,
    arms: &[(K, A)],
    result: &mut Vec<(K, Clause<A>)>,
) {
    p.groups.build(arms, same, shares, bucket);
    result.clear();
    for group in (0..p.groups.heads.len()).rev() {
        let mut i = p.groups.heads[group];
        while i != NONE {
            let (key, body) = &arms[i];
            let next = p.groups.next[i];
            let clause = if next == NONE {
                Clause::Body(p.add_tree(Tree::Run(*body)))
            } else {
                Clause::FallsThrough(Some(*body))
            };
            result.push((*key, clause));
            i = next;
        }
    }
}

/// An entry of the payload `if` chain: the check (`None`: unchecked), whether
/// it is a class check, and the arm body (`None`: the default).
type Entry = (Option<TestId>, bool, Option<TreeId>);

/// The payload cases, after the literals: one `switch (typeof x)` over the
/// primitive kinds, whose default is an `if` chain over the classes
/// (subclasses first), arrays, functions and objects.
struct PayloadInput<'a, A> {
    block_cases: &'a [Kind],
    null_guard: bool,
    fallback: Option<&'a A>,
    has_default: bool,
    arms: &'a [(Kind, A)],
}
fn payload_part<A: Copy>(
    p: &mut Plan<A>,
    same: &impl Fn(&A, &A) -> bool,
    bucket: &impl Fn(&A) -> usize,
    input: PayloadInput<'_, A>,
) -> TreeId {
    let PayloadInput {
        block_cases,
        null_guard,
        fallback,
        has_default,
        arms,
    } = input;
    match (arms, has_default) {
        ([], true) => return p.add_tree(Tree::Fallback),
        ([], false) => return p.add_tree(Tree::Skip),
        ([(_, body)], false) => return p.add_tree(Tree::Run(*body)),
        _ => {}
    }
    let mut scratch = std::mem::take(&mut p.scratch);
    let result = (|| {
        // An arm with the default's body is the default.
        let filtered = &mut scratch.arms;
        filtered.clear();
        filtered.extend(
            arms.iter()
                .filter(|(_, body)| {
                    !(has_default && fallback.is_some_and(|fallback| same(fallback, body)))
                })
                .cloned(),
        );
        clauses(
            p,
            same,
            bucket,
            |k1, k2| is_primitive(k1) && is_primitive(k2),
            filtered,
            &mut scratch.all,
        );
        let primitive_clauses = &mut scratch.primitive;
        let other_clauses = &mut scratch.other;
        primitive_clauses.clear();
        other_clauses.clear();
        for clause in scratch.all.drain(..) {
            if is_primitive(&clause.0) {
                primitive_clauses.push(clause);
            } else {
                other_clauses.push(clause);
            }
        }
        let arm = |block_type: &Kind| -> Option<TreeId> {
            other_clauses
                .iter()
                .find_map(|(kind, clause)| match clause {
                    Clause::Body(tree) if kind == block_type => Some(*tree),
                    _ => None,
                })
        };
        scratch.instances.clear();
        scratch.ordered.clear();
        scratch
            .instances
            .extend(block_cases.iter().filter_map(|kind| match kind {
                Kind::Instance(id) => Some(*id),
                _ => None,
            }));
        while !scratch.instances.is_empty() {
            let first = *scratch
                .instances
                .iter()
                .find(|i| {
                    !scratch
                        .instances
                        .iter()
                        .any(|j| p.metadata.is_subclass(*j, **i))
                })
                .expect("subclass relation is acyclic");
            scratch.instances.retain(|i| *i != first);
            scratch.ordered.push(first);
        }
        // `null`, when it did not go to the default before.
        let is_object = if null_guard {
            let typeof_object = p.add_test(Test::Typeof(Kind::Object));
            let not_null = p.add_test(Test::NotNull);
            p.and(typeof_object, not_null)
        } else {
            p.add_test(Test::Typeof(Kind::Object))
        };
        let entries = &mut scratch.entries;
        entries.clear();
        for i in &scratch.ordered {
            let is_class = p.metadata.is_class(*i);
            match arm(&Kind::Instance(*i)) {
                Some(body) => {
                    let check = p.add_test(Test::Instance(*i));
                    entries.push((Some(check), is_class, Some(body)));
                }
                None if has_default => {
                    let check = p.add_test(Test::Instance(*i));
                    entries.push((Some(check), is_class, None));
                }
                None => {}
            }
        }
        if let Some(body) = arm(&Kind::Function) {
            let check = p.add_test(Test::Typeof(Kind::Function));
            entries.push((Some(check), false, Some(body)));
        }
        if let Some(body) = arm(&Kind::Object) {
            entries.push((Some(is_object), false, Some(body)));
        }
        if let Some(body) = arm(&Kind::Unknown) {
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
        // Consecutive checks leading to the default share one `if`.
        let merged = &mut scratch.merged;
        merged.clear();
        for entry in entries.drain(..) {
            match (merged.last_mut(), &entry) {
                (Some((Some(c1), class1, None)), (Some(c2), class2, None)) => {
                    *c1 = p.or(*c1, *c2);
                    *class1 = *class1 || *class2;
                }
                _ => merged.push(entry),
            }
        }
        let entries = merged;
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
        let chain = |p: &mut Plan<A>, entries: &mut Vec<Entry>| -> TreeId {
            let mut tree = final_tree;
            for (check, _, body) in entries.drain(..).rev() {
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
        if has_default && has_class_check {
            let kinds = &mut scratch.missing;
            kinds.clear();
            kinds.extend(
                block_cases
                    .iter()
                    .filter(|kind| {
                        is_primitive(kind) && !primitive_clauses.iter().any(|(k, _)| k == *kind)
                    })
                    .copied(),
            );
            let last = kinds.len().saturating_sub(1);
            for (index, kind) in kinds.iter().enumerate() {
                let clause = if index == last {
                    Clause::Body(p.add_tree(Tree::Fallback))
                } else {
                    Clause::FallsThrough(None)
                };
                primitive_clauses.push((*kind, clause));
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
    })();
    p.scratch = scratch;
    result
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

/// A borrowed runtime value; imported literal keys never allocate during selection.
#[derive(Clone, Copy)]
struct SelectedValue<'a> {
    key: Option<&'a str>,
    kind: Option<Kind>,
    array: bool,
    null: bool,
}
fn selected_literal(metadata: &Metadata, id: LiteralId) -> SelectedValue<'_> {
    let kind = match metadata.literal(id) {
        Literal::String(_) => Some(Kind::String),
        Literal::Int(_) | Literal::Float(_) => Some(Kind::Number),
        Literal::BigInt(_) => Some(Kind::Bigint),
        Literal::Bool(_) => Some(Kind::Boolean),
        Literal::Null => Some(Kind::Object),
        Literal::Undefined => None,
    };
    SelectedValue {
        key: Some(metadata.runtime_key(id)),
        kind,
        array: false,
        null: matches!(metadata.literal(id), Literal::Null),
    }
}

/// The owned constant-folding boundary imports its value key once; the selector
/// below borrows keys, including when planning tests unnamed imported literals.
pub(crate) fn select<A: Copy>(
    plan: &Plan<A>,
    value: &Value,
    on_test: &mut impl FnMut(&Test),
) -> Outcome<A> {
    let mut metadata = Metadata::default();
    let value = match value {
        Value::Literal(tag) => {
            let id = metadata.import_literal(tag);
            selected_literal(&metadata, id)
        }
        Value::Object | Value::Array => SelectedValue {
            key: None,
            kind: Some(Kind::Object),
            array: *value == Value::Array,
            null: false,
        },
    };
    select_tree(plan, plan.root, value, on_test, &mut Vec::new())
}
fn select_tree<A: Copy>(
    p: &Plan<A>,
    mut tree: TreeId,
    value: SelectedValue<'_>,
    on_test: &mut impl FnMut(&Test),
    work: &mut Vec<SelectOp>,
) -> Outcome<A> {
    fn holds<A>(
        p: &Plan<A>,
        test: TestId,
        value: SelectedValue<'_>,
        on_test: &mut impl FnMut(&Test),
        work: &mut Vec<SelectOp>,
    ) -> bool {
        work.clear();
        work.push(SelectOp::Test(test));
        let mut result = false;
        while let Some(op) = work.pop() {
            match op {
                SelectOp::Not => result = !result,
                SelectOp::And(right) => {
                    if result {
                        work.push(SelectOp::Test(right));
                    }
                }
                SelectOp::Or(right) => {
                    if !result {
                        work.push(SelectOp::Test(right));
                    }
                }
                SelectOp::Test(id) => {
                    let test = p.test(id);
                    on_test(test);
                    match test {
                        Test::Equals(id) => result = value.key == Some(p.metadata.runtime_key(*id)),
                        Test::Typeof(kind) => result = value.kind == Some(*kind),
                        Test::Instance(id) => result = !p.metadata.is_class(*id) && value.array,
                        Test::NotNull => result = !value.null,
                        Test::Not(t) => {
                            work.push(SelectOp::Not);
                            work.push(SelectOp::Test(*t));
                        }
                        Test::And(a, b) => {
                            work.push(SelectOp::And(*b));
                            work.push(SelectOp::Test(*a));
                        }
                        Test::Or(a, b) => {
                            work.push(SelectOp::Or(*b));
                            work.push(SelectOp::Test(*a));
                        }
                    }
                }
            }
        }
        result
    }
    fn target<K, A>(
        clauses: &[(K, Clause<A>)],
        matches: impl Fn(&K) -> bool,
        default: TreeId,
    ) -> TreeId {
        let Some(start) = clauses.iter().position(|(key, _)| matches(key)) else {
            return default;
        };
        clauses[start..]
            .iter()
            .find_map(|(_, clause)| match clause {
                Clause::Body(tree) => Some(*tree),
                _ => None,
            })
            .unwrap_or(default)
    }
    loop {
        tree = match p.tree(tree) {
            Tree::Run(body) => return Outcome::Arm(*body),
            Tree::Fallback => return Outcome::Default,
            Tree::Skip => return Outcome::Nothing,
            Tree::If(test, yes, no) => {
                if holds(p, *test, value, on_test, work) {
                    *yes
                } else {
                    *no
                }
            }
            Tree::Block(inner) => *inner,
            Tree::SwitchValue(clauses, default) => target(
                p.value_clauses(*clauses),
                |id| value.key == Some(p.metadata.runtime_key(*id)),
                *default,
            ),
            Tree::SwitchTypeof(clauses, default) => target(
                p.typeof_clauses(*clauses),
                |kind| value.kind == Some(*kind),
                *default,
            ),
        };
    }
}

/// Structural equality uses retained work stacks, and never assumes that a
/// source body compares equal to itself (some bodies are incomparable).
fn same_tree<A>(
    p: &Plan<A>,
    same: &impl Fn(&A, &A) -> bool,
    a: TreeId,
    b: TreeId,
    trees: &mut Vec<(TreeId, TreeId)>,
    tests: &mut Vec<(TestId, TestId)>,
) -> bool {
    trees.clear();
    tests.clear();
    trees.push((a, b));
    while let Some((a, b)) = trees.pop() {
        match (p.tree(a), p.tree(b)) {
            (Tree::Run(a), Tree::Run(b)) => {
                if !same(a, b) {
                    return false;
                }
            }
            (Tree::Fallback, Tree::Fallback) | (Tree::Skip, Tree::Skip) => {}
            (Tree::Block(a), Tree::Block(b)) => trees.push((*a, *b)),
            (Tree::If(a, ay, an), Tree::If(b, by, bn)) => {
                tests.push((*a, *b));
                while let Some((a, b)) = tests.pop() {
                    match (p.test(a), p.test(b)) {
                        (Test::Not(a), Test::Not(b)) => tests.push((*a, *b)),
                        (Test::And(a, aa), Test::And(b, bb))
                        | (Test::Or(a, aa), Test::Or(b, bb)) => {
                            tests.push((*aa, *bb));
                            tests.push((*a, *b));
                        }
                        (a, b) => {
                            if a != b {
                                return false;
                            }
                        }
                    }
                }
                trees.push((*an, *bn));
                trees.push((*ay, *by));
            }
            (Tree::SwitchValue(a, ad), Tree::SwitchValue(b, bd)) => {
                if a.len != b.len {
                    return false;
                }
                trees.push((*ad, *bd));
                for ((a, ac), (b, bc)) in p.value_clauses(*a).iter().zip(p.value_clauses(*b)).rev()
                {
                    if a != b {
                        return false;
                    }
                    match (ac, bc) {
                        (Clause::FallsThrough(_), Clause::FallsThrough(_)) => {}
                        (Clause::Body(a), Clause::Body(b)) => trees.push((*a, *b)),
                        _ => return false,
                    }
                }
            }
            (Tree::SwitchTypeof(a, ad), Tree::SwitchTypeof(b, bd)) => {
                if a.len != b.len {
                    return false;
                }
                trees.push((*ad, *bd));
                for ((a, ac), (b, bc)) in
                    p.typeof_clauses(*a).iter().zip(p.typeof_clauses(*b)).rev()
                {
                    if a != b {
                        return false;
                    }
                    match (ac, bc) {
                        (Clause::FallsThrough(_), Clause::FallsThrough(_)) => {}
                        (Clause::Body(a), Clause::Body(b)) => trees.push((*a, *b)),
                        _ => return false,
                    }
                }
            }
            _ => return false,
        }
    }
    true
}

/// Postorder simplifies children before appending a parent's kept clause runs.
/// No temporary clause vectors can interleave a parent's contiguous span.
fn simplify<A: Copy>(p: &mut Plan<A>, same: &impl Fn(&A, &A) -> bool, root: TreeId) -> TreeId {
    if matches!(p.tree(root), Tree::Run(_) | Tree::Fallback | Tree::Skip) {
        return root;
    }
    let mut work = std::mem::take(&mut p.simplify_work);
    let mut map = std::mem::take(&mut p.simplify_map);
    let mut equal_trees = std::mem::take(&mut p.equal_trees);
    let mut equal_tests = std::mem::take(&mut p.equal_tests);
    p.simplify_epoch += 1;
    let epoch = p.simplify_epoch;
    map.resize(p.trees.len(), (0, TreeId(0)));
    work.clear();
    work.push((root, false));
    while let Some((id, done)) = work.pop() {
        if map[id.0 as usize].0 == epoch {
            continue;
        }
        if !done {
            work.push((id, true));
            match p.tree(id) {
                Tree::If(_, yes, no) => {
                    work.push((*no, false));
                    work.push((*yes, false));
                }
                Tree::Block(inner) => work.push((*inner, false)),
                Tree::SwitchValue(c, d) => {
                    for (_, clause) in p.value_clauses(*c).iter().rev() {
                        if let Clause::Body(t) = clause {
                            work.push((*t, false));
                        }
                    }
                    work.push((*d, false));
                }
                Tree::SwitchTypeof(c, d) => {
                    for (_, clause) in p.typeof_clauses(*c).iter().rev() {
                        if let Clause::Body(t) = clause {
                            work.push((*t, false));
                        }
                    }
                    work.push((*d, false));
                }
                _ => {}
            }
            continue;
        }
        let mapped = |id: TreeId| {
            assert_eq!(map[id.0 as usize].0, epoch);
            map[id.0 as usize].1
        };
        let new = match *p.tree(id) {
            Tree::Run(_) | Tree::Fallback | Tree::Skip => id,
            Tree::If(test, yes, no) => {
                let (yes, no) = (mapped(yes), mapped(no));
                if same_tree(p, same, yes, no, &mut equal_trees, &mut equal_tests) {
                    yes
                } else {
                    p.add_tree(Tree::If(test, yes, no))
                }
            }
            Tree::Block(inner) => p.add_tree(Tree::Block(mapped(inner))),
            Tree::SwitchValue(c, d) => {
                let default = mapped(d);
                let start = p.value_clauses.len();
                let mut group = c.start as usize;
                for i in c.range() {
                    if let Clause::Body(body) = p.value_clauses[i].1 {
                        let body = mapped(body);
                        if !same_tree(p, same, body, default, &mut equal_trees, &mut equal_tests) {
                            for j in group..i {
                                p.value_clauses.push(p.value_clauses[j]);
                            }
                            p.value_clauses
                                .push((p.value_clauses[i].0, Clause::Body(body)));
                        }
                        group = i + 1;
                    }
                }
                for i in group..(c.start + c.len) as usize {
                    p.value_clauses.push(p.value_clauses[i]);
                }
                let len = p.value_clauses.len() - start;
                if len == 0 {
                    default
                } else {
                    p.add_tree(Tree::SwitchValue(
                        Clauses {
                            start: start as u32,
                            len: len as u32,
                        },
                        default,
                    ))
                }
            }
            Tree::SwitchTypeof(c, d) => {
                let default = mapped(d);
                let start = p.typeof_clauses.len();
                let mut group = c.start as usize;
                for i in c.range() {
                    if let Clause::Body(body) = p.typeof_clauses[i].1 {
                        let body = mapped(body);
                        if !same_tree(p, same, body, default, &mut equal_trees, &mut equal_tests) {
                            for j in group..i {
                                p.typeof_clauses.push(p.typeof_clauses[j]);
                            }
                            p.typeof_clauses
                                .push((p.typeof_clauses[i].0, Clause::Body(body)));
                        }
                        group = i + 1;
                    }
                }
                for i in group..(c.start + c.len) as usize {
                    p.typeof_clauses.push(p.typeof_clauses[i]);
                }
                let len = p.typeof_clauses.len() - start;
                if len == 0 {
                    default
                } else {
                    p.add_tree(Tree::SwitchTypeof(
                        Clauses {
                            start: start as u32,
                            len: len as u32,
                        },
                        default,
                    ))
                }
            }
        };
        map[id.0 as usize] = (epoch, new);
    }
    let result = map[root.0 as usize].1;
    p.simplify_work = work;
    p.simplify_map = map;
    p.equal_trees = equal_trees;
    p.equal_tests = equal_tests;
    result
}

/// untagged_dispatch.ml `plan`; `same` tells two bodies that are one body
/// apart. Cost is emitted tests/clauses plus source-body equality work.
pub(crate) fn plan<A: Copy>(same: impl Fn(&A, &A) -> bool, input: Input<'_, A>) -> Plan<A> {
    let mut p = Plan::new();
    let facts = p.metadata.import_facts(input.facts);
    let literal_arms: Vec<_> = input
        .literal_arms
        .into_iter()
        .map(|(tag, body)| (p.metadata.import_literal(&tag), body))
        .collect();
    let payload_arms: Vec<_> = input
        .payload_arms
        .into_iter()
        .map(|(kind, body)| (p.metadata.import_kind(&kind), body))
        .collect();
    append(
        &mut p,
        same,
        BorrowedInput {
            facts: &facts,
            literal_arms: &literal_arms,
            payload_arms: &payload_arms,
            literals_complete: input.literals_complete,
            payloads_complete: input.payloads_complete,
            fallback: input.fallback,
        },
    );
    p
}

/// Append to unit-owned graph pools without importing metadata or invalidating roots.
pub(crate) fn append<A: Copy>(
    p: &mut Plan<A>,
    same: impl Fn(&A, &A) -> bool,
    input: BorrowedInput<'_, A>,
) {
    append_bucketed(p, same, |_| 0, input);
}
pub(crate) fn append_bucketed<A: Copy>(
    p: &mut Plan<A>,
    same: impl Fn(&A, &A) -> bool,
    bucket: impl Fn(&A) -> usize,
    input: BorrowedInput<'_, A>,
) {
    p.root = plan_tree(p, &same, &bucket, input);
}

#[cfg(test)]
impl<A> Plan<A> {
    pub(crate) fn reserve_repeat(&mut self) {
        self.tests.reserve(self.tests.len());
        self.trees.reserve(self.trees.len());
        self.value_clauses.reserve(self.value_clauses.len());
        self.typeof_clauses.reserve(self.typeof_clauses.len());
        self.simplify_map.reserve(self.trees.len());
    }
    pub(crate) fn grouping_steps(&self) -> usize {
        self.groups.steps
    }
    pub(crate) fn capacities(&self) -> Vec<usize> {
        vec![
            self.tests.capacity(),
            self.trees.capacity(),
            self.value_clauses.capacity(),
            self.typeof_clauses.capacity(),
            self.groups.heads.capacity(),
            self.groups.next.capacity(),
            self.groups.bucket_links.capacity(),
            self.groups.buckets.capacity(),
            self.scratch.arms.capacity(),
            self.scratch.all.capacity(),
            self.scratch.primitive.capacity(),
            self.scratch.other.capacity(),
            self.scratch.instances.capacity(),
            self.scratch.ordered.capacity(),
            self.scratch.entries.capacity(),
            self.scratch.merged.capacity(),
            self.scratch.missing.capacity(),
            self.scratch.literals.capacity(),
            self.scratch.literal_clauses.capacity(),
            self.scratch.unnamed.capacity(),
            self.scratch.membership.capacity(),
            self.simplify_work.capacity(),
            self.simplify_map.capacity(),
            self.equal_trees.capacity(),
            self.equal_tests.capacity(),
            self.selector_work.capacity(),
        ]
    }
}

fn plan_tree<A: Copy>(
    p: &mut Plan<A>,
    same: &impl Fn(&A, &A) -> bool,
    bucket: &impl Fn(&A) -> usize,
    input: PlanInput<'_, A>,
) -> TreeId {
    let PlanInput {
        facts,
        literal_arms,
        payload_arms,
        literals_complete,
        payloads_complete,
        fallback,
    } = input;
    let block_cases = &facts.block_types[..];
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
            bucket,
            PayloadInput {
                block_cases,
                null_guard: false,
                fallback: fallback.as_ref(),
                has_default: payload_has_default,
                arms: payload_arms,
            },
        );
        return simplify(p, same, payload);
    }
    let mut effective = std::mem::take(&mut p.scratch.literals);
    let mut literal_clauses = std::mem::take(&mut p.scratch.literal_clauses);
    let mut unnamed = std::mem::take(&mut p.scratch.unnamed);
    let mut membership = std::mem::take(&mut p.scratch.membership);
    let mut selector_work = std::mem::take(&mut p.selector_work);
    effective.clear();
    unnamed.clear();
    p.membership_epoch += 1;
    let membership_epoch = p.membership_epoch;
    membership.resize(p.metadata.literal_count(), 0);
    for (tag, _) in literal_arms {
        membership[tag.0 as usize] = membership_epoch;
    }
    unnamed.extend(
        literal_cases
            .iter()
            .filter(|tag| membership[tag.0 as usize] != membership_epoch)
            .copied(),
    );
    let result = {
        // The literals first, compared with `===` by one switch whose default is
        // the payload dispatch. A literal without an arm goes to the match's
        // default, never to a payload arm.
        // A literal without an arm skips the switch when the payload dispatch
        // takes it to the default without a class check, which could throw when
        // the class does not exist.
        let skip_payload = literal_default.map(|_| {
            payload_part(
                p,
                same,
                bucket,
                PayloadInput {
                    block_cases,
                    null_guard: unnamed
                        .iter()
                        .any(|l| p.metadata.literal(*l) == Literal::Null),
                    fallback: fallback.as_ref(),
                    has_default: true,
                    arms: payload_arms,
                },
            )
        });
        let mut skips_the_switch = |p: &Plan<A>, literal: &LiteralId| -> bool {
            match skip_payload {
                None => false,
                Some(payload) => {
                    let mut class_check = false;
                    let outcome = select_tree(
                        p,
                        payload,
                        selected_literal(&p.metadata, *literal),
                        &mut |test| {
                            if matches!(test, Test::Instance(id) if p.metadata.is_class(*id)) {
                                class_check = true;
                            }
                        },
                        &mut selector_work,
                    );
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
            && unnamed.iter().any(|literal| {
                p.metadata.literal(*literal) == Literal::Null && skips_the_switch(p, literal)
            });
        effective.extend_from_slice(literal_arms);
        if let Some(fallback) = literal_default {
            effective.extend(
                unnamed
                    .iter()
                    .filter(|literal| !(payload_has_default && skips_the_switch(p, literal)))
                    .map(|literal| (*literal, *fallback)),
            );
        }
        let payload = payload_part(
            p,
            same,
            bucket,
            PayloadInput {
                block_cases,
                null_guard,
                fallback: fallback.as_ref(),
                has_default: payload_has_default,
                arms: payload_arms,
            },
        );
        let payload = simplify(p, same, payload);
        // A payload dispatch that runs one body unchecked takes the literals with
        // that body too.
        if let Tree::Run(body) = p.tree(payload) {
            let body = *body;
            effective.retain(|(_, other)| !same(&body, other));
        }
        if effective.len() <= 2 {
            let mut tree = payload;
            if effective.len() == 2 && same(&effective[0].1, &effective[1].1) {
                let first = p.add_test(Test::Equals(effective[0].0));
                let second = p.add_test(Test::Equals(effective[1].0));
                let test = p.or(first, second);
                let run = p.add_tree(Tree::Run(effective[0].1));
                tree = p.add_tree(Tree::If(test, run, tree));
            } else {
                for (literal, body) in effective.iter().rev() {
                    let test = p.add_test(Test::Equals(*literal));
                    let run = p.add_tree(Tree::Run(*body));
                    tree = p.add_tree(Tree::If(test, run, tree));
                }
            }
            tree
        } else {
            clauses(
                p,
                same,
                bucket,
                |_, _| true,
                &effective,
                &mut literal_clauses,
            );
            let switch = p.switch_value(&literal_clauses, payload);
            simplify(p, same, switch)
        }
    };
    p.scratch.literals = effective;
    p.scratch.literal_clauses = literal_clauses;
    p.scratch.unnamed = unnamed;
    p.scratch.membership = membership;
    p.selector_work = selector_work;
    result
}

/// Port of upstream's `tests/ounit_tests/ounit_untagged_dispatch_tests.ml`:
/// the expected plans are upstream's.
#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::variant_runtime::{Instance, same_literal_value};

    #[test]
    fn grouping_updates_representatives_and_preserves_first_created_priority() {
        let arms = [((), 0u32), ((), 1), ((), 2), ((), 8)];
        let mut groups = Groups::default();
        groups.build(&arms, &|a, b| *a + 1 == *b, |_, _| true, &|_| 0);
        assert_eq!(groups.heads, [3, 0]);
        assert_eq!(groups.next, [1, 2, NONE, NONE]);
        // Even the same source handle remains incomparable when the callback
        // says so; bucket identity is never itself equality evidence.
        groups.build(&[((), 7), ((), 7)], &|_, _| false, |_, _| true, &|_| 0);
        assert_eq!(groups.heads, [1, 0]);
        let arms = [((), 1u32), ((), 2), ((), 3)];
        groups.build(
            &arms,
            &|a, b| *a == 1 && (*b == 2 || *b == 3),
            |_, _| true,
            &|_| 0,
        );
        assert_eq!(groups.heads, [0, 1]); // joins first-created body 3, not body 2
    }

    #[test]
    fn deep_tests_and_blocks_use_iterative_selector_and_simplifier() {
        let mut p = Plan::default();
        let mut first = p.add_test(Test::NotNull);
        let mut second = p.add_test(Test::NotNull);
        for _ in 0..10_000 {
            first = p.not(first);
            second = p.not(second);
        }
        let yes = p.add_tree(Tree::Run(1));
        let no = p.add_tree(Tree::Run(2));
        let a = p.add_tree(Tree::If(first, yes, no));
        let b = p.add_tree(Tree::If(second, yes, no));
        assert!(same_tree(
            &p,
            &|a, b| a == b,
            a,
            b,
            &mut Vec::new(),
            &mut Vec::new()
        ));
        let mut root = a;
        for _ in 0..10_000 {
            root = p.add_tree(Tree::Block(root));
        }
        p.root = simplify(&mut p, &|a, b| a == b, root);
        assert!(matches!(
            select(&p, &Value::Object, &mut |_| {}),
            Outcome::Arm(1)
        ));
        assert_eq!(std::mem::size_of::<TreeId>(), 4);
        assert_eq!(std::mem::size_of::<TestId>(), 4);
        assert_eq!(std::mem::size_of::<Clauses>(), 8);
        assert_eq!(std::mem::size_of::<Tree<u32>>(), 16);
        assert_eq!(std::mem::size_of::<Clause<u32>>(), 8);
    }

    #[test]
    fn appended_plans_keep_earlier_root_handles_valid() {
        let facts = MatchingFacts {
            tag_name: None,
            literal_tags: vec![],
            block_types: vec![BlockType::Unknown],
        };
        let mut pool = Plan::default();
        let facts = pool.metadata.import_facts(&facts);
        append(
            &mut pool,
            |a: &u32, b: &u32| a == b,
            BorrowedInput {
                facts: &facts,
                literal_arms: &[],
                payload_arms: &[(Kind::Unknown, 7)],
                literals_complete: true,
                payloads_complete: true,
                fallback: None,
            },
        );
        let first = pool.root();
        append(
            &mut pool,
            |a: &u32, b: &u32| a == b,
            BorrowedInput {
                facts: &facts,
                literal_arms: &[],
                payload_arms: &[(Kind::Unknown, 8)],
                literals_complete: true,
                payloads_complete: true,
                fallback: None,
            },
        );
        assert!(matches!(pool.tree(first), Tree::Run(7)));
        assert!(matches!(pool.tree(pool.root()), Tree::Run(8)));
    }

    type P = Plan<&'static str>;

    fn test_to_string(p: &P, test: TestId) -> String {
        match p.test(test) {
            Test::Equals(literal) => {
                format!("x === {}", p.metadata.owned_literal(*literal).value_key())
            }
            Test::Typeof(block_type) => {
                format!("typeof x === {}", block_type.typeof_name().unwrap_or("?"))
            }
            Test::Instance(instance) => {
                format!("x instanceof {}", p.metadata.instance_name(*instance))
            }
            Test::NotNull => "x !== null".to_string(),
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
                        p.metadata.owned_literal(*literal).value_key(),
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
        };
        plan(
            |a: &&str, b: &&str| a == b,
            Input {
                facts: &facts,
                literals_complete: literal_arms.len() == literals.len(),
                payloads_complete: payload_arms.len() == kinds.len(),
                literal_arms,
                payload_arms,
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
                    if matches!(test, Test::Instance(id) if tree.metadata.is_class(*id)) {
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
