//! The dispatch of a `switch` on an untagged variant, as data.
//!
//! Port of `compiler/ml/untagged_dispatch.ml`: which tests the generated code
//! runs on the scrutinee, in which statements, and which body each path runs.
//! `LambdaCompiler::compile_untagged_plan` prints a plan as JavaScript, and
//! constant folding (`Lambda::switch`) evaluates it with [`select`], so a
//! folded match and the generated code agree by construction.

use crate::types::variant_runtime::{
    BlockType, Instance, LiteralTag, MatchingFacts, same_literal_value,
};

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
    Not(Box<Test>),
    And(Box<Test>, Box<Test>),
    Or(Box<Test>, Box<Test>),
}

impl Test {
    fn not(test: Test) -> Test {
        Test::Not(Box::new(test))
    }
    fn and(a: Test, b: Test) -> Test {
        Test::And(Box::new(a), Box::new(b))
    }
    fn or(a: Test, b: Test) -> Test {
        Test::Or(Box::new(a), Box::new(b))
    }
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
    If(Test, Box<Tree<A>>, Box<Tree<A>>),
    /// A statement block around the tree.
    Block(Box<Tree<A>>),
    /// `switch (x)` over literals; the tree is the `default:`.
    SwitchValue(Vec<(LiteralTag, Clause<A>)>, Box<Tree<A>>),
    /// `switch (typeof x)` over kinds with a `typeof` name; the tree is the
    /// `default:`. A switch with one clause that is not empty is printed as
    /// an `if`.
    SwitchTypeof(Vec<(BlockType, Clause<A>)>, Box<Tree<A>>),
}

/// A `case` of a switch.
#[derive(Debug, Clone)]
pub(crate) enum Clause<A> {
    /// An empty case falling through to the next one; the body only gives
    /// the source location.
    FallsThrough(Option<A>),
    /// A `Run` or `Fallback`.
    Body(Tree<A>),
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
    same: &impl Fn(&A, &A) -> bool,
    shares: impl Fn(&K, &K) -> bool,
    arms: &[(K, A)],
) -> Vec<(K, Clause<A>)> {
    stable_group(arms, |(key1, body1), (key2, body2)| {
        shares(key1, key2) && same(body1, body2)
    })
    .into_iter()
    .flat_map(|group| {
        let last = group.len() - 1;
        group
            .into_iter()
            .enumerate()
            .map(move |(index, (key, body))| {
                if index == last {
                    (key, Clause::Body(Tree::Run(body)))
                } else {
                    (key, Clause::FallsThrough(Some(body)))
                }
            })
    })
    .collect()
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
type Entry<A> = (Option<Test>, bool, Option<Tree<A>>);

/// The payload cases, after the literals: one `switch (typeof x)` over the
/// primitive kinds, whose default is an `if` chain over the classes
/// (subclasses first), arrays, functions and objects.
fn payload_part<A: Clone>(
    same: &impl Fn(&A, &A) -> bool,
    block_cases: &[BlockType],
    null_guard: bool,
    fallback: Option<&A>,
    has_default: bool,
    arms: &[(BlockType, A)],
) -> Tree<A> {
    match (arms, has_default) {
        ([], true) => return Tree::Fallback,
        ([], false) => return Tree::Skip,
        ([(_, body)], false) => return Tree::Run(body.clone()),
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
    let all_clauses = clauses(same, |k1, k2| is_primitive(k1) && is_primitive(k2), &arms);
    let (primitive_clauses, other_clauses): (Vec<_>, Vec<_>) = all_clauses
        .into_iter()
        .partition(|(kind, _)| is_primitive(kind));
    let arm = |block_type: &BlockType| -> Option<Tree<A>> {
        other_clauses
            .iter()
            .find_map(|(kind, clause)| match clause {
                Clause::Body(tree) if kind == block_type => Some(tree.clone()),
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
        Test::and(Test::Typeof(BlockType::Object), Test::NotNull)
    } else {
        Test::Typeof(BlockType::Object)
    };
    let mut entries: Vec<Entry<A>> = instances
        .iter()
        .filter_map(|i| {
            let is_class = matches!(i, Instance::Class { .. });
            match arm(&BlockType::Instance(i.clone())) {
                Some(body) => Some((Some(Test::Instance(i.clone())), is_class, Some(body))),
                None if has_default => Some((Some(Test::Instance(i.clone())), is_class, None)),
                None => None,
            }
        })
        .collect();
    if let Some(body) = arm(&BlockType::Function) {
        entries.push((Some(Test::Typeof(BlockType::Function)), false, Some(body)));
    }
    if let Some(body) = arm(&BlockType::Object) {
        entries.push((Some(is_object), false, Some(body)));
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
            check = Test::and(check, Test::not(previous.expect("checked above")));
        }
        entries.push((Some(check), is_class, body));
    }
    // Consecutive checks leading to the default share one `if`.
    let mut merged: Vec<Entry<A>> = Vec::with_capacity(entries.len());
    for entry in entries {
        match (merged.last_mut(), &entry) {
            (Some((Some(c1), class1, None)), (Some(c2), class2, None)) => {
                let c1_taken = std::mem::replace(c1, Test::NotNull);
                *c1 = Test::or(c1_taken, c2.clone());
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
        Tree::Fallback
    } else {
        match entries.pop() {
            Some((_, _, body)) => body.unwrap_or(Tree::Skip),
            None => Tree::Skip,
        }
    };
    let has_class_check = entries.iter().any(|(_, is_class, _)| *is_class);
    let chain = |entries: Vec<Entry<A>>| -> Tree<A> {
        let mut tree = final_tree.clone();
        for (check, _, body) in entries.into_iter().rev() {
            let body = body.unwrap_or(Tree::Fallback);
            tree = match check {
                Some(check) => Tree::If(check, Box::new(body), Box::new(tree)),
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
            primitive_clauses.push((
                kind.clone(),
                if index == last {
                    Clause::Body(Tree::Fallback)
                } else {
                    Clause::FallsThrough(None)
                },
            ));
        }
    }
    if primitive_clauses.is_empty() {
        return Tree::Block(Box::new(chain(entries)));
    }
    if !has_other_arms {
        // No other arm: in a complete match the last primitive arm is not
        // checked.
        if !has_default {
            let (_, last) = primitive_clauses.pop().expect("non-empty");
            let default = match last {
                Clause::Body(tree) => tree,
                Clause::FallsThrough(_) => Tree::Skip,
            };
            // The cases falling through to that arm go to the default too.
            while matches!(primitive_clauses.last(), Some((_, Clause::FallsThrough(_)))) {
                primitive_clauses.pop();
            }
            return Tree::SwitchTypeof(primitive_clauses, Box::new(default));
        }
        return Tree::SwitchTypeof(primitive_clauses, Box::new(Tree::Fallback));
    }
    Tree::SwitchTypeof(primitive_clauses, Box::new(chain(entries)))
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
    tree: &Tree<A>,
    value: &Value,
    on_test: &mut impl FnMut(&Test),
) -> Outcome<A> {
    // JavaScript semantics, including the short circuits of `&&` and `||`.
    fn holds(test: &Test, value: &Value, on_test: &mut impl FnMut(&Test)) -> bool {
        on_test(test);
        match (test, value) {
            (Test::Equals(literal), Value::Literal(v)) => same_literal_value(v, literal),
            (Test::Equals(_), Value::Object | Value::Array) => false,
            (Test::Typeof(kind), _) => kind_of(value).as_ref() == Some(kind),
            (Test::Instance(Instance::Array), _) => *value == Value::Array,
            (Test::Instance(Instance::Class { .. }), _) => false,
            (Test::NotNull, _) => *value != Value::Literal(LiteralTag::Null),
            (Test::Not(test), _) => !holds(test, value, on_test),
            (Test::And(t1, t2), _) => holds(t1, value, on_test) && holds(t2, value, on_test),
            (Test::Or(t1, t2), _) => holds(t1, value, on_test) || holds(t2, value, on_test),
        }
    }
    fn from_clauses<K, A: Clone>(
        matches: impl Fn(&K) -> bool,
        clauses: &[(K, Clause<A>)],
        default: &Tree<A>,
        value: &Value,
        on_test: &mut impl FnMut(&Test),
    ) -> Outcome<A> {
        // A matching case runs its body, or falls through to the next one.
        match clauses.iter().position(|(key, _)| matches(key)) {
            None => run(default, value, on_test),
            Some(start) => {
                for (_, clause) in &clauses[start..] {
                    if let Clause::Body(tree) = clause {
                        return run(tree, value, on_test);
                    }
                }
                run(default, value, on_test)
            }
        }
    }
    fn run<A: Clone>(tree: &Tree<A>, value: &Value, on_test: &mut impl FnMut(&Test)) -> Outcome<A> {
        match tree {
            Tree::Run(body) => Outcome::Arm(body.clone()),
            Tree::Fallback => Outcome::Default,
            Tree::Skip => Outcome::Nothing,
            Tree::If(test, then_, else_) => {
                if holds(test, value, on_test) {
                    run(then_, value, on_test)
                } else {
                    run(else_, value, on_test)
                }
            }
            Tree::Block(tree) => run(tree, value, on_test),
            Tree::SwitchValue(clauses, default) => match value {
                Value::Literal(v) => from_clauses(
                    |literal| same_literal_value(v, literal),
                    clauses,
                    default,
                    value,
                    on_test,
                ),
                Value::Object | Value::Array => run(default, value, on_test),
            },
            Tree::SwitchTypeof(clauses, default) => match kind_of(value) {
                Some(kind) => from_clauses(|k| *k == kind, clauses, default, value, on_test),
                None => run(default, value, on_test),
            },
        }
    }
    run(tree, value, on_test)
}

/// Two trees that run the same bodies after the same tests.
fn same_tree<A>(same: &impl Fn(&A, &A) -> bool, tree1: &Tree<A>, tree2: &Tree<A>) -> bool {
    match (tree1, tree2) {
        (Tree::Run(b1), Tree::Run(b2)) => same(b1, b2),
        (Tree::Fallback, Tree::Fallback) | (Tree::Skip, Tree::Skip) => true,
        (Tree::If(t1, then1, else1), Tree::If(t2, then2, else2)) => {
            t1 == t2 && same_tree(same, then1, then2) && same_tree(same, else1, else2)
        }
        (Tree::Block(t1), Tree::Block(t2)) => same_tree(same, t1, t2),
        (Tree::SwitchValue(c1, d1), Tree::SwitchValue(c2, d2)) => {
            same_clauses(same, c1, c2) && same_tree(same, d1, d2)
        }
        (Tree::SwitchTypeof(c1, d1), Tree::SwitchTypeof(c2, d2)) => {
            same_clauses(same, c1, c2) && same_tree(same, d1, d2)
        }
        _ => false,
    }
}

fn same_clauses<K: PartialEq, A>(
    same: &impl Fn(&A, &A) -> bool,
    clauses1: &[(K, Clause<A>)],
    clauses2: &[(K, Clause<A>)],
) -> bool {
    clauses1.len() == clauses2.len()
        && clauses1.iter().zip(clauses2).all(|((k1, c1), (k2, c2))| {
            k1 == k2
                && match (c1, c2) {
                    (Clause::FallsThrough(_), Clause::FallsThrough(_)) => true,
                    (Clause::Body(t1), Clause::Body(t2)) => same_tree(same, t1, t2),
                    _ => false,
                }
        })
}

/// A test whose branches run the same is not run, and a case of a switch that
/// runs what its default runs is left to the default, with the cases falling
/// through to it.
fn simplify<A: Clone>(same: &impl Fn(&A, &A) -> bool, tree: Tree<A>) -> Tree<A> {
    match tree {
        Tree::Run(_) | Tree::Fallback | Tree::Skip => tree,
        Tree::If(test, then_, else_) => {
            let then_ = simplify(same, *then_);
            let else_ = simplify(same, *else_);
            if same_tree(same, &then_, &else_) {
                then_
            } else {
                Tree::If(test, Box::new(then_), Box::new(else_))
            }
        }
        Tree::Block(tree) => Tree::Block(Box::new(simplify(same, *tree))),
        Tree::SwitchValue(clauses, default) => {
            let default = simplify(same, *default);
            let clauses = simplify_clauses(same, &default, clauses);
            if clauses.is_empty() {
                default
            } else {
                Tree::SwitchValue(clauses, Box::new(default))
            }
        }
        Tree::SwitchTypeof(clauses, default) => {
            let default = simplify(same, *default);
            let clauses = simplify_clauses(same, &default, clauses);
            if clauses.is_empty() {
                default
            } else {
                Tree::SwitchTypeof(clauses, Box::new(default))
            }
        }
    }
}

fn simplify_clauses<K, A: Clone>(
    same: &impl Fn(&A, &A) -> bool,
    default: &Tree<A>,
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
                let tree = simplify(same, tree);
                if !same_tree(same, &tree, default) {
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
pub(crate) fn plan<A: Clone>(same: impl Fn(&A, &A) -> bool, input: Input<'_, A>) -> Tree<A> {
    let same = &same;
    let Input {
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
        return simplify(
            same,
            payload_part(
                same,
                block_cases,
                false,
                fallback.as_ref(),
                payload_has_default,
                &payload_arms,
            ),
        );
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
            same,
            block_cases,
            unnamed.iter().any(|l| **l == LiteralTag::Null),
            fallback.as_ref(),
            true,
            &payload_arms,
        )
    });
    let skips_the_switch = |literal: &LiteralTag| -> bool {
        match &skip_payload {
            None => false,
            Some(payload) => {
                let mut class_check = false;
                let outcome = select(payload, &Value::Literal(literal.clone()), &mut |test| {
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
        || (literal_default.is_some() && unnamed.iter().any(|l| skips_the_switch(l)));
    let null_guard = literal_default.is_some()
        && payload_has_default
        && unnamed
            .iter()
            .any(|literal| **literal == LiteralTag::Null && skips_the_switch(literal));
    let unnamed_arms: Vec<(LiteralTag, A)> = match literal_default {
        Some(fallback) => unnamed
            .iter()
            .filter(|literal| !(payload_has_default && skips_the_switch(literal)))
            .map(|literal| ((*literal).clone(), fallback.clone()))
            .collect(),
        None => Vec::new(),
    };
    let mut literal_arms = literal_arms;
    literal_arms.extend(unnamed_arms);
    let payload = simplify(
        same,
        payload_part(
            same,
            block_cases,
            null_guard,
            fallback.as_ref(),
            payload_has_default,
            &payload_arms,
        ),
    );
    // A payload dispatch that runs one body unchecked takes the literals with
    // that body too.
    if let Tree::Run(body) = &payload {
        literal_arms.retain(|(_, other)| !same(body, other));
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
            let mut test = Test::Equals(literals.next().expect("non-empty group"));
            for literal in literals {
                test = Test::or(test, Test::Equals(literal));
            }
            tree = Tree::If(test, Box::new(Tree::Run(body)), Box::new(tree));
        }
        tree
    } else {
        simplify(
            same,
            Tree::SwitchValue(clauses(same, |_, _| true, &literal_arms), Box::new(payload)),
        )
    }
}

/// Port of upstream's `tests/ounit_tests/ounit_untagged_dispatch_tests.ml`:
/// the expected plans are upstream's.
#[cfg(test)]
mod tests {
    use super::*;

    fn test_to_string(test: &Test) -> String {
        match test {
            Test::Equals(literal) => format!("x === {}", literal.value_key()),
            Test::Typeof(block_type) => {
                format!("typeof x === {}", block_type.typeof_name().unwrap_or("?"))
            }
            Test::Instance(instance) => format!("x instanceof {}", instance.as_str()),
            Test::NotNull => "x !== null".to_string(),
            Test::Not(test) => format!("!({})", test_to_string(test)),
            Test::And(t1, t2) => format!("({} && {})", test_to_string(t1), test_to_string(t2)),
            Test::Or(t1, t2) => format!("({} || {})", test_to_string(t1), test_to_string(t2)),
        }
    }

    fn tree_to_string(tree: &Tree<&'static str>) -> String {
        match tree {
            Tree::Run(body) => body.to_string(),
            Tree::Fallback => "fallback".to_string(),
            Tree::Skip => "skip".to_string(),
            Tree::If(test, then_, else_) => format!(
                "if ({}) {} else {}",
                test_to_string(test),
                tree_to_string(then_),
                tree_to_string(else_)
            ),
            Tree::Block(tree) => format!("{{{}}}", tree_to_string(tree)),
            Tree::SwitchValue(clauses, default) => format!(
                "switch (x) {{{}default: {}}}",
                clauses
                    .iter()
                    .map(|(literal, clause)| format!(
                        "{}: {}; ",
                        literal.value_key(),
                        clause_to_string(clause)
                    ))
                    .collect::<String>(),
                tree_to_string(default)
            ),
            Tree::SwitchTypeof(clauses, default) => format!(
                "switch (typeof x) {{{}default: {}}}",
                clauses
                    .iter()
                    .map(|(block_type, clause)| format!(
                        "{}: {}; ",
                        block_type.typeof_name().unwrap_or("?"),
                        clause_to_string(clause)
                    ))
                    .collect::<String>(),
                tree_to_string(default)
            ),
        }
    }

    fn clause_to_string(clause: &Clause<&'static str>) -> String {
        match clause {
            Clause::FallsThrough(_) => "falls through".to_string(),
            Clause::Body(tree) => tree_to_string(tree),
        }
    }

    fn class(name: &str, ancestors: &[&str]) -> BlockType {
        BlockType::Instance(Instance::Class {
            name: name.to_string(),
            ancestors: ancestors.iter().map(|a| a.to_string()).collect(),
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
    ) -> Tree<&'static str> {
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

    fn assert_plan(expected: &str, tree: Tree<&'static str>) {
        assert_eq!(tree_to_string(&tree), expected);
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
                    BlockType::Instance(Instance::Array),
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
                    (rng.int(5) < 3)
                        .then(|| (case.clone(), ["b0", "b1", "b2"][rng.int(3) as usize]))
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
                    if declared(&BlockType::Instance(Instance::Array)) {
                        Some(BlockType::Instance(Instance::Array))
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
                BlockType::Instance(Instance::Array) => values.push(Value::Array),
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
                    tree_to_string(&tree)
                );
                if let Some(expected) = oracle(&case, &value) {
                    let outcome = match outcome {
                        Outcome::Arm(body) => body.to_string(),
                        Outcome::Default => "default".to_string(),
                        Outcome::Nothing => "nothing".to_string(),
                    };
                    assert_eq!(outcome, expected, "{value:?} in {}", tree_to_string(&tree));
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
