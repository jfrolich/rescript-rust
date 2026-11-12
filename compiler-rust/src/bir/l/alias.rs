//! `Lam_pass_remove_alias.simplify_alias` on the rewrite engine
//! (`lambda/lam_pass_remove_alias.rs`, compiler/core/lam_pass_remove_alias.ml):
//! field reads of known blocks, optional unwrapping, boolean folding and the
//! inlining of applications (`bir/l/beta.rs`).
//!
//! What the pass knows about a binder is what `Lam_pass_collect.collect_info`
//! recorded before it ran (BACKEND_REDESIGN.md C.2 row 1). Here that is the
//! fact the arena maintains, frozen when the round starts, and read through
//! [`Table::entry`], which turns it into the legacy table's entry the first
//! time it is asked for, or when the sweep reaches the binding, whichever
//! comes first. Nothing below a binding has been edited at either moment, so
//! the entry describes the binding as it was when the round started. The
//! entries are a dense table indexed by variable; block elements are in one
//! pool. No hash table is involved.
//!
//! Costs. The sweep enters a node once (subtrees without an application, a
//! primitive, a conditional or a string switch are not entered), an entry is
//! built once (constant time, or the number of fields of a block) and read in
//! constant time. A function that may be inlined is copied once, before the
//! first edit inside it, and only then (`Engine::guard_enter`). An inlined
//! application costs the analyses and the copy of the body (`beta.rs`).
use crate::bir::bridge::Unsupported;
use crate::bir::engine::{Changed, Engine, Facts, OpMask, Order, Round};
use crate::bir::*;
use crate::lambda::LamLoc;
use crate::lambda::lam_compat::{Comparison, FieldDbgInfo};
use crate::lambda::lam_primitive::Primitive;
use crate::lambda::lam_tag_info::TagInfo;

/// `simpl` has its own arms for applications, primitives, conditionals and
/// string switches (lam_pass_remove_alias.rs:158-220); everything else is
/// `shallow_map`. A subtree with none of the four holds nothing to rewrite.
const CANDIDATES: OpMask = OpMask::APPLY
    .or(OpMask::PRIM)
    .or(OpMask::IF)
    .or(OpMask::STR_SWITCH);

/// - `mask`: see [`CANDIDATES`].
/// - `order`: stateful. `simpl` rewrites a conditional before it visits the
///   branch it keeps, visits the arguments of an application before it
///   decides, sweeps an inlined body again with a nesting count, and reads a
///   field after its operand: neither `Pre` nor `Post` gives that.
/// - `renorm`: the default arm is `shallow_map` (lam_pass_remove_alias.rs:
///   150-152), whose rebuild goes through `apply_with`, `prim_with`,
///   `switch_with`, `string_switch_with`, `if_` and `seq`.
/// - `facts`: frozen, the pass reads `ident_tbl` as collected before it.
/// - `guard`: the bound functions that may be inlined; the driver opens the
///   scope when it enters the binding.
pub static ALIAS: Round = Round {
    name: "simplify_alias",
    mask: CANDIDATES,
    order: Order::Stateful(run),
    renorm: OpMask::SHALLOW_MAP.or(OpMask::IF).or(OpMask::SEQ),
    facts: Facts::Frozen,
    guard: Some(|e, n| may_be_inlined(e.bir(), n)),
    rule: |_, _| Changed::No,
};

/// `Lam_compile_context.rec_flag` of a bound function.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Rec {
    /// Bound by `let`.
    NonRec,
    /// The only binding of a `let rec`.
    SelfRec,
    /// One of several bindings of a `let rec`.
    Rec,
}

/// A simple expression a fact names (`Lam_util.element_of_lambda`,
/// lam_pass_collect.rs:19-33), by value: the node it was read from may be
/// rewritten later in the sweep.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Elem {
    /// Not a simple form.
    Na,
    /// A variable.
    Var(VarId),
    /// A constant.
    Const(ConstId),
    /// A module field of a module.
    FieldOfGlobal(PrimId, ImportId),
    /// A module field of a variable.
    FieldOfVar(PrimId, VarId),
}

/// `Lam_id_kind.t` as the pass reads it (`lam_stats.rs`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Entry {
    /// Not asked for yet.
    Unset,
    /// No entry. Also what the pass makes of an entry it does not read: a
    /// mutable block, an exported binding that is not a function.
    Na,
    /// `Parameter`: a function parameter.
    Param,
    /// `Constant`.
    Const(ConstId),
    /// `Module`.
    Module(ImportId),
    /// `Normal_optional`: `Some(x)`, with `x` when it is a variable or a
    /// constant.
    Optional(Elem),
    /// `OptionalBlock`: a nullable conversion of a variable.
    Nullable(VarId, BoxedNullable),
    /// `ImmutableBlock`: elements `start..start + len` of the pool.
    Block {
        /// First element.
        start: u32,
        /// Number of elements.
        len: u32,
    },
    /// `FunctionId` whose definition is a function.
    Function {
        /// The function node.
        node: NodeId,
        /// How it is bound.
        rec: Rec,
        /// [`may_be_inlined`] of the function as it was when the round
        /// started. A function that fails it is never inlined, so the round
        /// keeps no copy of it; it must not be inlined either when the sweep
        /// has since made it small.
        inlinable: bool,
    },
}

/// A necessary condition of `beta::ok_to_inline` that does not read the
/// arguments: which bound functions a round must be able to read as they
/// were when it started (BACKEND_REDESIGN.md C.2 row 1).
fn may_be_inlined(b: &Bir, function: NodeId) -> bool {
    use crate::lambda::InlineAttribute;
    let View::Fun { body, header } = b.view(function) else {
        return false;
    };
    let attr = b.function_attributes(header);
    if !crate::lambda::lam_analysis::attr_can_be_inlined(attr) {
        return false;
    }
    if attr.is_a_functor {
        return true;
    }
    match attr.inline {
        InlineAttribute::Always => true,
        InlineAttribute::Never => false,
        InlineAttribute::Default => {
            let params = b.function(header).params;
            let on_param = |n: NodeId| {
                matches!(b.view(n), View::Var { var } if params.iter().any(|p| p == var))
            };
            super::exits::size_upto(b, body, 10) < 10
                || match b.view(body) {
                    View::Switch { scrutinee, .. } => on_param(scrutinee),
                    View::If { condition, .. } => on_param(condition),
                    _ => false,
                }
        }
    }
}

/// The legacy identifier table, built on demand from the frozen facts.
#[derive(Default)]
pub(crate) struct Table {
    entries: Vec<Entry>,
    elems: Vec<Elem>,
    /// Variables from here on were created by the round: they have the
    /// entries the round registers and no other.
    fresh_from: usize,
}

/// `Lam_util.element_of_lambda` (lam_pass_collect.rs:19-33, lam_util.ml:188-196).
fn element(b: &Bir, n: NodeId) -> Elem {
    match b.view(n) {
        View::Var { var } => Elem::Var(var),
        View::Const { value } => Elem::Const(value),
        View::Prim {
            args: [x],
            primitive,
        } if matches!(
            b.primitive(primitive).primitive,
            Primitive::Pfield(_, FieldDbgInfo::Module { .. })
        ) =>
        {
            match b.view(*x) {
                View::Global { module } => Elem::FieldOfGlobal(primitive, module),
                View::Var { var } => Elem::FieldOfVar(primitive, var),
                _ => Elem::Na,
            }
        }
        _ => Elem::Na,
    }
}

impl Table {
    /// A table for a round over `e`'s unit, empty.
    pub(crate) fn new(e: &Engine<'_>) -> Self {
        Self {
            entries: Vec::new(),
            elems: Vec::new(),
            fresh_from: e.bir().vars().len(),
        }
    }

    fn set(&mut self, var: VarId, entry: Entry) {
        if self.entries.len() <= var.index() {
            self.entries.resize(var.index() + 1, Entry::Unset);
        }
        self.entries[var.index()] = entry;
    }

    /// `Lam_util.kind_of_lambda_block` (lam_pass_collect.rs:36-38).
    fn block(&mut self, b: &Bir, args: &[NodeId]) -> Entry {
        let start = self.elems.len() as u32;
        self.elems.extend(args.iter().map(|x| element(b, *x)));
        Entry::Block {
            start,
            len: args.len() as u32,
        }
    }

    /// The elements of a block entry.
    pub(crate) fn elements(&self, start: u32, len: u32) -> &[Elem] {
        &self.elems[start as usize..(start + len) as usize]
    }

    /// `Lam_pass_collect.collect_bind` (lam_pass_collect.rs:323-380,
    /// lam_pass_collect.ml:58-93) for one binder, from its maintained fact.
    /// Where the fact and the legacy entry differ by design:
    /// - a mutable block has a fact and no entry (lam_pass_collect.rs:331
    ///   matches immutable blocks only);
    /// - a nullable conversion has an entry only when its operand is a
    ///   variable (lam_pass_collect.rs:345);
    /// - the parameters of a static handler have the fact `Param` and no
    ///   entry (`Collector::params` runs for functions only);
    /// - an alias has the fact `Alias(y)` and the entry of `y`
    ///   (`alias_ident_or_global`, lam_pass_collect.rs:41-52).
    fn build(&mut self, e: &Engine<'_>, var: VarId) -> Entry {
        let b = e.bir();
        match e.fact(var) {
            Fact::Unknown | Fact::MutableBlock(_) => Entry::Na,
            // Followed by `entry`.
            Fact::Alias(_) => Entry::Na,
            Fact::Param => match b.vars().binder(var).map(|n| b.node(n).op()) {
                Some(Op::Fun) => Entry::Param,
                _ => Entry::Na,
            },
            Fact::Const(c) => Entry::Const(c),
            Fact::Module(m) => Entry::Module(ImportId(m)),
            Fact::Block(node) => match b.view(node) {
                View::Prim { args, .. } => {
                    let args: smallvec::SmallVec<[NodeId; 8]> = args.into();
                    self.block(b, &args)
                }
                _ => Entry::Na,
            },
            Fact::Optional(x) => Entry::Optional(match element(b, x) {
                simple @ (Elem::Var(_) | Elem::Const(_)) => simple,
                _ => Elem::Na,
            }),
            Fact::NullableOptional(x, kind) => match b.view(x) {
                View::Var { var } => Entry::Nullable(var, kind),
                _ => Entry::Na,
            },
            Fact::Function { node, rec } => Entry::Function {
                node,
                inlinable: may_be_inlined(b, node),
                rec: match rec {
                    RecFlag::No => Rec::NonRec,
                    RecFlag::Yes => match b.vars().binder(var).map(|n| b.view(n)) {
                        Some(View::LetRec { values, .. }) if values.len() == 1 => Rec::SelfRec,
                        _ => Rec::Rec,
                    },
                },
            },
        }
    }

    /// The entry of `var`. An alias has the entry of what it names; a chain
    /// of aliases is followed once and every link remembers the result.
    pub(crate) fn entry(&mut self, e: &Engine<'_>, var: VarId) -> Entry {
        let known = |table: &Self, var: VarId| {
            table
                .entries
                .get(var.index())
                .copied()
                .filter(|entry| *entry != Entry::Unset)
        };
        if let Some(entry) = known(self, var) {
            return entry;
        }
        let mut chain: smallvec::SmallVec<[VarId; 4]> = smallvec::SmallVec::new();
        let mut at = var;
        let entry = loop {
            if let Some(entry) = known(self, at) {
                break entry;
            }
            if at.index() >= self.fresh_from {
                break Entry::Na;
            }
            chain.push(at);
            match e.fact(at) {
                Fact::Alias(target) => at = target,
                _ => break self.build(e, at),
            }
        };
        for link in chain {
            self.set(link, entry);
        }
        entry
    }
}

/// `Constant::some_none_depth` (lam_constant.rs:197-209).
fn some_none_depth(b: &Bir, mut c: ConstId) -> bool {
    loop {
        match b.constant(c) {
            Constant::Some(inner) => c = *inner,
            Constant::ModuleAlias | Constant::Undefined(_) => return true,
            Constant::Constructor(tag) => {
                return matches!(tag.literal, crate::types::VariantLiteralTag::Undefined);
            }
            _ => return false,
        }
    }
}

/// `Constant::is_allocating` (lam_constant.rs:221-243, lambda.ml
/// `const_is_allocating`).
fn is_allocating(b: &Bir, mut c: ConstId) -> bool {
    loop {
        match b.constant(c) {
            Constant::Block { .. } => return true,
            Constant::Some(inner) => {
                if some_none_depth(b, *inner) {
                    return true;
                }
                c = *inner;
            }
            _ => return false,
        }
    }
}

fn fired(e: &mut Engine<'_>, name: &'static str) {
    *e.stats.rules.entry(name).or_default() += 1;
}

enum Work {
    Simpl(NodeId),
    /// The tail of `shallow_map`: rebuild through the smart constructor when
    /// something below changed.
    Finish(NodeId, u64),
    Field(NodeId, u64),
    Nullable(NodeId, VarId, BoxedNullable),
    StrSwitch(NodeId, ConstId),
    GuardEnter(NodeId),
    GuardExit,
    BoundaryEnter,
    BoundaryExit,
}

struct Pass {
    table: Table,
    work: Vec<Work>,
    revision: u64,
    /// Functions and loop bodies around the node being swept.
    boundaries: usize,
}

impl Pass {
    /// Replace `n` by a detached tree that holds variable uses `n` did not.
    /// Outside every function and loop no use can become captured, so the
    /// arena need not look: `Engine::replace` walks the replacement and the
    /// ancestors of `n` for that.
    fn place(&self, e: &mut Engine<'_>, n: NodeId, replacement: NodeId) {
        if self.boundaries == 0 {
            e.fill(n, replacement);
        } else {
            e.replace(n, replacement);
        }
    }

    fn sweep_children(&mut self, e: &Engine<'_>, n: NodeId, children: &[NodeId]) {
        for &child in children.iter().rev() {
            if e.bir().capture_boundary(n, child) {
                self.work.push(Work::BoundaryExit);
                self.work.push(Work::Simpl(child));
                self.work.push(Work::BoundaryEnter);
            } else {
                self.work.push(Work::Simpl(child));
            }
        }
    }

    /// The default arm (lam_pass_remove_alias.rs:219, `simpl_children`):
    /// `shallow_map` in its child order.
    fn shallow(&mut self, e: &Engine<'_>, n: NodeId) {
        self.work.push(Work::Finish(n, self.revision));
        let children = e.bir().view(n).children();
        self.sweep_children(e, n, &children);
    }

    /// `shallow_map` on a binding. The entries of the bound variables are
    /// built before their values are swept, and a bound function that may
    /// be inlined is read as it is now by every later application of it.
    fn binding(&mut self, e: &Engine<'_>, n: NodeId) {
        for var in e.bir().binders(n) {
            self.table.entry(e, var);
        }
        self.work.push(Work::Finish(n, self.revision));
        let (values, body): (smallvec::SmallVec<[NodeId; 4]>, NodeId) = match e.bir().view(n) {
            View::Let {
                value: Some(value),
                body,
                ..
            } => (smallvec::smallvec![value], body),
            View::LetRec { values, body, .. } => (values.into(), body),
            _ => unreachable!("a binding"),
        };
        self.work.push(Work::Simpl(body));
        let binders = e.bir().binders(n);
        for (index, value) in values.into_iter().enumerate().rev() {
            // `ALIAS.guard`, as decided when the entry was built.
            let guard = matches!(
                self.table.entry(e, binders[index]),
                Entry::Function { node, inlinable: true, .. } if node == value
            );
            if guard {
                self.work.push(Work::GuardExit);
            }
            self.work.push(Work::Simpl(value));
            if guard {
                self.work.push(Work::GuardEnter(value));
            }
        }
    }

    fn finish(&mut self, e: &mut Engine<'_>, n: NodeId, before: u64) {
        if self.revision != before && ALIAS.renorm.intersects(OpMask::of(e.bir().node(n).op())) {
            e.normalise(n);
        }
        e.finish_candidate(n);
    }

    /// `simpl_prim` (lam_pass_remove_alias.rs:222-296).
    fn prim(&mut self, e: &mut Engine<'_>, n: NodeId) {
        let View::Prim { args, primitive } = e.bir().view(n) else {
            unreachable!()
        };
        match (&e.bir().primitive(primitive).primitive, args) {
            // lam_pass_remove_alias.rs:230-253 (#7432): in JSX preserve mode
            // a tag that is a module field stays as it is.
            (Primitive::Pjsx(_), [tag, rest @ ..])
                if e.jsx_preserve
                    && matches!(e.bir().view(*tag), View::Prim { primitive, .. }
                        if matches!(e.bir().primitive(primitive).primitive, Primitive::Pfield(..))) =>
            {
                self.work.push(Work::Finish(n, self.revision));
                self.work.extend(rest.iter().rev().copied().map(Work::Simpl));
            }
            // lam_pass_remove_alias.rs:255-271: the operand first.
            (Primitive::Pfield(..), [arg]) => {
                self.work.push(Work::Field(n, self.revision));
                self.work.push(Work::Simpl(*arg));
            }
            (Primitive::PvalFromOption | Primitive::PvalFromOptionNotNest, [x])
                if e.bir().node(*x).op() == Op::Var =>
            {
                self.unwrap_some(e, n)
            }
            _ => self.shallow(e, n),
        }
    }

    /// Unwrapping a known optional (lam_pass_remove_alias.rs:272-293,
    /// lam_pass_remove_alias.ml:66-93).
    fn unwrap_some(&mut self, e: &mut Engine<'_>, n: NodeId) {
        let View::Prim {
            args: [x],
            primitive,
        } = e.bir().view(n)
        else {
            unreachable!()
        };
        let x = *x;
        let not_nest = matches!(
            e.bir().primitive(primitive).primitive,
            Primitive::PvalFromOptionNotNest
        );
        let View::Var { var } = e.bir().view(x) else {
            unreachable!()
        };
        let weight = e.weight(n);
        match self.table.entry(e, var) {
            Entry::Nullable(payload, _) | Entry::Optional(Elem::Var(payload)) => {
                let payload = e.node(View::Var { var: payload }, 0, weight);
                self.place(e, n, payload);
                fired(e, "unwrap-some");
            }
            // Only forms that are safe to repeat.
            Entry::Optional(Elem::Const(value)) if !is_allocating(e.bir(), value) => {
                e.put(n, View::Const { value }, 0);
                fired(e, "unwrap-some");
            }
            _ if not_nest => {
                e.promote(n, x);
                fired(e, "unwrap-not-nested");
            }
            _ => {
                e.finish_candidate(n);
                return;
            }
        }
        self.revision += 1;
        e.finish_candidate(n);
    }

    /// `Lam_util.field_flatten_get` (lam_util.rs:125-180, lam_util.ml:202-232)
    /// once the operand is swept (lam_pass_remove_alias.rs:255-271).
    fn field(&mut self, e: &mut Engine<'_>, n: NodeId, before: u64) {
        let View::Prim {
            args: [arg],
            primitive,
        } = e.bir().view(n)
        else {
            unreachable!()
        };
        let Primitive::Pfield(i, info) = e.bir().primitive(primitive).primitive else {
            unreachable!()
        };
        let View::Var { var } = e.bir().view(*arg) else {
            return self.finish(e, n, before);
        };
        let weight = e.weight(n);
        match self.table.entry(e, var) {
            // lam_util.rs:134-137.
            Entry::Module(module) => {
                let global = e.node(View::Global { module }, 0, weight);
                let primitive = e.intern_prim(Primitive::Pfield(i, info), LamLoc::NONE);
                e.put(
                    n,
                    View::Prim {
                        args: &[global],
                        primitive,
                    },
                    0,
                );
                e.normalise(n);
                fired(e, "field-of-module");
            }
            // lam_util.rs:139-142.
            Entry::Block { start, len } => {
                let element = usize::try_from(i)
                    .ok()
                    .and_then(|i| self.table.elements(start, len).get(i).copied());
                let replacement = match element {
                    Some(Elem::Var(var)) => e.node(View::Var { var }, 0, weight),
                    Some(Elem::Const(value)) => e.node(View::Const { value }, 0, weight),
                    Some(Elem::FieldOfGlobal(primitive, module)) => {
                        let global = e.node(View::Global { module }, 0, weight);
                        e.node(
                            View::Prim {
                                args: &[global],
                                primitive,
                            },
                            0,
                            weight,
                        )
                    }
                    Some(Elem::FieldOfVar(primitive, var)) => {
                        let base = e.node(View::Var { var }, 0, weight);
                        e.node(
                            View::Prim {
                                args: &[base],
                                primitive,
                            },
                            0,
                            weight,
                        )
                    }
                    Some(Elem::Na) | None => return self.finish(e, n, before),
                };
                self.place(e, n, replacement);
                fired(e, "field-of-block");
            }
            // lam_util.rs:143-175.
            Entry::Const(c) => {
                let picked = match e.bir().constant(c) {
                    Constant::Block {
                        tag: TagInfo::Record(record),
                        fields,
                    } => match info {
                        FieldDbgInfo::Record { name } => record
                            .fields
                            .iter()
                            .position(|(field, _)| *field == name)
                            .and_then(|at| e.bir().constant_fields(*fields).get(at).copied()),
                        _ => None,
                    },
                    Constant::Block { fields, .. } => usize::try_from(i)
                        .ok()
                        .and_then(|i| e.bir().constant_fields(*fields).get(i).copied()),
                    _ => None,
                };
                match picked.filter(|c| !is_allocating(e.bir(), *c)) {
                    Some(value) => {
                        e.put(n, View::Const { value }, 0);
                        fired(e, "field-of-constant");
                    }
                    None => return self.finish(e, n, before),
                }
            }
            // lam_util.rs:177-178.
            _ => return self.finish(e, n, before),
        }
        self.revision += 1;
        e.finish_candidate(n);
    }

    /// The conditional arm (lam_pass_remove_alias.rs:160-204,
    /// lam_pass_remove_alias.ml:95-123).
    fn if_(&mut self, e: &mut Engine<'_>, n: NodeId) {
        let View::If {
            condition,
            then_,
            else_,
        } = e.bir().view(n)
        else {
            unreachable!()
        };
        let keep = match e.bir().view(condition) {
            // `if Pis_not_none v then ...`
            View::Prim {
                args: [v],
                primitive,
            } if matches!(e.bir().primitive(primitive).primitive, Primitive::PisNotNone)
                && e.bir().node(*v).op() == Op::Var =>
            {
                let View::Var { var } = e.bir().view(*v) else {
                    unreachable!()
                };
                match self.table.entry(e, var) {
                    Entry::Const(c) if is_const_some(e.bir(), c) => Some(then_),
                    Entry::Block { .. } | Entry::Optional(_) => Some(then_),
                    Entry::Nullable(payload, kind) => {
                        self.work.push(Work::Nullable(n, payload, kind));
                        self.work.push(Work::Simpl(else_));
                        self.work.push(Work::Simpl(then_));
                        return;
                    }
                    _ => return self.shallow(e, n),
                }
            }
            View::Var { var } => match self.truth(e, var) {
                Some(true) => Some(then_),
                Some(false) => Some(else_),
                None => None,
            },
            _ => None,
        };
        match keep {
            Some(branch) => {
                e.promote(n, branch);
                fired(e, "if-known");
                self.revision += 1;
                self.work.push(Work::Simpl(n));
            }
            None => self.shallow(e, n),
        }
    }

    /// `id_is_for_sure_true_in_boolean` (lam_pass_remove_alias.rs:36-60,
    /// lam_pass_remove_alias.ml:27-42).
    fn truth(&mut self, e: &Engine<'_>, var: VarId) -> Option<bool> {
        let falsy = |c: ConstId| {
            matches!(
                e.bir().constant(c),
                Constant::Bool(false) | Constant::Null | Constant::Undefined(_)
            )
        };
        match self.table.entry(e, var) {
            Entry::Optional(Elem::Const(c)) if falsy(c) => Some(false),
            Entry::Const(c) => match e.bir().constant(c) {
                Constant::Bool(true) => Some(true),
                Constant::Int(i)
                | Constant::DecoratedInt {
                    value: i,
                    native: false,
                    ..
                } => Some(*i != 0),
                _ if falsy(c) => Some(false),
                _ => None,
            },
            _ => None,
        }
    }

    /// `if Pis_not_none v` on a nullable conversion of `payload`, once both
    /// branches are swept (lam_pass_remove_alias.rs:176-189): test the
    /// payload itself. `Lam.not_` (lam.ml:584-588) of a null test is `Pnot`.
    fn nullable(&mut self, e: &mut Engine<'_>, n: NodeId, payload: VarId, kind: BoxedNullable) {
        let View::If { condition, .. } = e.bir().view(n) else {
            unreachable!()
        };
        let test = match kind {
            BoxedNullable::Null => Primitive::PisNull,
            BoxedNullable::Undefined => Primitive::PisUndefined,
            BoxedNullable::Both => Primitive::PisNullUndefined,
        };
        debug_assert!(!matches!(test, Primitive::Pintcomp(Comparison::Neq)));
        let weight = e.weight(condition);
        let test = e.intern_prim(test, LamLoc::NONE);
        let not = e.intern_prim(Primitive::Pnot, LamLoc::NONE);
        let payload = e.node(View::Var { var: payload }, 0, weight);
        let is_null = e.node(
            View::Prim {
                args: &[payload],
                primitive: test,
            },
            0,
            weight,
        );
        e.normalise(is_null);
        let negated = e.node(
            View::Prim {
                args: &[is_null],
                primitive: not,
            },
            0,
            weight,
        );
        e.normalise(negated);
        self.place(e, condition, negated);
        e.normalise(n);
        fired(e, "if-nullable");
        self.revision += 1;
        e.finish_candidate(n);
    }

    /// The string switch arm (lam_pass_remove_alias.rs:206-218): switch on
    /// the constant the scrutinee is bound to.
    fn str_switch(&mut self, e: &mut Engine<'_>, n: NodeId) {
        let View::StrSwitch {
            scrutinee, actions, ..
        } = e.bir().view(n)
        else {
            unreachable!()
        };
        if let View::Var { var } = e.bir().view(scrutinee)
            && let Entry::Const(c) = self.table.entry(e, var)
        {
            let actions: smallvec::SmallVec<[NodeId; 8]> = actions.into();
            self.work.push(Work::StrSwitch(n, c));
            self.work.extend(actions.into_iter().rev().map(Work::Simpl));
        } else {
            self.shallow(e, n)
        }
    }

    fn str_switch_done(&mut self, e: &mut Engine<'_>, n: NodeId, value: ConstId) {
        let View::StrSwitch { scrutinee, .. } = e.bir().view(n) else {
            unreachable!()
        };
        e.put(scrutinee, View::Const { value }, 0);
        e.normalise(n);
        fired(e, "switch-on-constant");
        self.revision += 1;
        e.finish_candidate(n);
    }

    /// `simpl` (lam_pass_remove_alias.rs:155-220).
    fn simpl(&mut self, e: &mut Engine<'_>, n: NodeId) -> Result<(), Unsupported> {
        if !e.enter_candidate(n, CANDIDATES) {
            return Ok(());
        }
        match e.bir().node(n).op() {
            Op::Prim => self.prim(e, n),
            Op::If => self.if_(e, n),
            // Applications: `simpl_apply`, in the commits that follow.
            Op::Apply => self.shallow(e, n),
            Op::StrSwitch => self.str_switch(e, n),
            Op::Let | Op::LetRec => {
                if matches!(e.bir().view(n), View::Let { value: None, .. }) {
                    return Err(Unsupported("released let value"));
                }
                self.binding(e, n)
            }
            // lam_pass_remove_alias.rs:219: `_ => self.simpl_children(a, lam)`.
            _ => self.shallow(e, n),
        }
        Ok(())
    }
}

/// `is_const_some` (lam_pass_remove_alias.rs:62-71, lam_pass_remove_alias.ml:44-48).
fn is_const_some(b: &Bir, c: ConstId) -> bool {
    match b.constant(c) {
        Constant::Some(_) => true,
        Constant::Block { tag, .. } => matches!(tag, TagInfo::Some | TagInfo::SomeNotNested),
        _ => false,
    }
}

fn run(e: &mut Engine<'_>, root: NodeId) -> Changed {
    let mut pass = Pass {
        table: Table::new(e),
        work: vec![Work::Simpl(root)],
        revision: 0,
        boundaries: 0,
    };
    while let Some(task) = pass.work.pop() {
        let result = match task {
            Work::Simpl(n) => pass.simpl(e, n),
            Work::Finish(n, before) => {
                pass.finish(e, n, before);
                Ok(())
            }
            Work::Field(n, before) => {
                pass.field(e, n, before);
                Ok(())
            }
            Work::Nullable(n, payload, kind) => {
                pass.nullable(e, n, payload, kind);
                Ok(())
            }
            Work::StrSwitch(n, value) => {
                pass.str_switch_done(e, n, value);
                Ok(())
            }
            Work::GuardEnter(n) => {
                e.guard_enter(n);
                Ok(())
            }
            Work::GuardExit => {
                e.guard_exit();
                Ok(())
            }
            Work::BoundaryEnter => {
                pass.boundaries += 1;
                Ok(())
            }
            Work::BoundaryExit => {
                pass.boundaries -= 1;
                Ok(())
            }
        };
        if let Err(reason) = result {
            // The tree is abandoned: the caller reads `unsupported` first.
            e.stats.unsupported = Some(reason.0);
            return Changed::Yes;
        }
    }
    if pass.revision == 0 {
        Changed::No
    } else {
        Changed::Yes
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bir::bridge::import_lambda;
    use crate::bir::engine::testing::{call, id, prim};
    use crate::lambda::arena::LamArena;
    use crate::lambda::lam_compat::LetKind;
    use crate::lambda::lam_constant::Constant as C;
    use crate::lambda::lam_primitive::Mutable;
    use crate::lambda::lam_tag_info::TagInfo;

    /// Where the maintained fact and the legacy entry differ by design
    /// (`Table::build`): the fact exists, the legacy table has no entry.
    #[test]
    fn facts_the_legacy_table_does_not_hold() {
        let mut a = LamArena::new();
        let (m, n, h, x) = (id("m", 1), id("n", 2), id("h", 3), id("x", 4));
        let vx = a.var(x);
        let mutable = prim(
            &mut a,
            Primitive::Pmakeblock(TagInfo::Tuple, Mutable::Mutable),
            &[vx],
        );
        let effect = call(&mut a, "effect", 5);
        let nullable = prim(&mut a, Primitive::PnullToOpt, &[effect]);
        let one = a.const_(C::int(1));
        let raise = a.static_raise(1, &[one]);
        let vh = a.var(h);
        let caught = a.static_catch(raise, 1, &[h], vh);
        let inner = a.let_(LetKind::Strict, n, nullable, caught);
        let root = a.let_(LetKind::Strict, m, mutable, inner);
        let tree = a.export(root);
        let mut a = LamArena::new();
        let root = a.import(&tree);
        let mut imported = import_lambda(&a, root).unwrap();
        let mut meta = crate::lambda::lam_stats::LamStats::new(vec![]);
        crate::lambda::lam_pass_collect::collect_info(&a, &mut meta, root);
        assert!(meta.ident_tbl.get(&m).is_none());
        assert!(meta.ident_tbl.get(&n).is_none());
        assert!(meta.ident_tbl.get(&h).is_none());
        let e = Engine::new(&mut imported.arena);
        let vars = e.bir().vars().len() as u32;
        let facts: Vec<Fact> = (0..vars).map(|i| e.bir().vars().fact(VarId(i))).collect();
        assert!(facts.iter().any(|f| matches!(f, Fact::MutableBlock(_))));
        assert!(facts.iter().any(|f| matches!(f, Fact::NullableOptional(..))));
        assert!(facts.iter().any(|f| matches!(f, Fact::Param)));
        let mut table = Table::new(&e);
        for i in 0..vars {
            assert_eq!(table.entry(&e, VarId(i)), Entry::Na);
        }
    }
}
