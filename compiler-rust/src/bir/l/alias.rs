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
use super::beta::{self, ParamStats, Scratch};
use crate::bir::bridge::Unsupported;
use crate::bir::engine::{Changed, Engine, Facts, OpMask, Order, Round};
use crate::bir::*;
use crate::lambda::LamLoc;
use crate::lambda::lam_compat::{Comparison, FieldDbgInfo};
use crate::lambda::lam_primitive::{Mutable, Primitive};
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

/// `MAX_INLINE_DEPTH` (lam_pass_remove_alias.rs:107-112, C.2 row 2).
const MAX_INLINE_DEPTH: usize = crate::lambda::lam_pass_remove_alias::MAX_INLINE_DEPTH;

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

    /// `register_bound_param_kind` (lam_beta_reduce.rs:452-466,
    /// lam_beta_reduce.ml:66-73): a parameter bound by a reduction to an
    /// immutable block or to `Some(x)` gets an entry.
    fn register(&mut self, e: &Engine<'_>, var: VarId, value: NodeId) {
        let b = e.bir();
        let View::Prim { args, primitive } = b.view(value) else {
            return;
        };
        let entry = match (&b.primitive(primitive).primitive, args) {
            (Primitive::Pmakeblock(_, Mutable::Immutable), args) => {
                let args: smallvec::SmallVec<[NodeId; 8]> = args.into();
                self.block(b, &args)
            }
            (Primitive::Psome | Primitive::PsomeNotNest, [x]) => {
                Entry::Optional(match element(b, *x) {
                    simple @ (Elem::Var(_) | Elem::Const(_)) => simple,
                    _ => Elem::Na,
                })
            }
            _ => return,
        };
        self.set(var, entry);
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
    Apply(NodeId, u64),
    GuardEnter(NodeId),
    GuardExit,
    DepthDown,
    BoundaryEnter,
    BoundaryExit,
}

struct Pass {
    table: Table,
    scratch: Scratch,
    work: Vec<Work>,
    revision: u64,
    depth: usize,
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

    /// Replace the application `n` by the reduction of `function` on the
    /// application's arguments.
    fn inline(
        &mut self,
        e: &mut Engine<'_>,
        n: NodeId,
        function: NodeId,
        stats: Option<&[ParamStats]>,
    ) -> Result<(), Unsupported> {
        let View::Apply { args, .. } = e.bir().view(n) else {
            unreachable!()
        };
        let args: smallvec::SmallVec<[NodeId; 8]> = args.into();
        let weight = e.weight(n);
        // The application may lie inside the function it applies: the body
        // read below must not be the one the arguments are taken out of.
        e.flush_guards();
        let function = e.as_of_round_start(function);
        let View::Fun { body, header } = e.bir().view(function) else {
            unreachable!()
        };
        let params = e.bir().function(header).params;
        for &arg in &args {
            e.detach(arg);
        }
        let table = &mut self.table;
        let reduced = beta::reduce(
            e,
            &mut self.scratch,
            params,
            body,
            &args,
            stats,
            weight,
            &mut |e, var, value| table.register(e, var, value),
        )?;
        self.place(e, n, reduced);
        self.revision += 1;
        Ok(())
    }

    /// `simpl_apply` (lam_pass_remove_alias.rs:310-426,
    /// lam_pass_remove_alias.ml:125-246), before the arguments are swept.
    fn apply(&mut self, e: &mut Engine<'_>, n: NodeId) -> Result<(), Unsupported> {
        let View::Apply { callee, args, .. } = e.bir().view(n) else {
            unreachable!()
        };
        // Cross-module inlining (lam_pass_remove_alias.rs:319-339,
        // lam_pass_remove_alias.ml:131-162).
        if let Some((module, field)) = beta::module_field(e.bir(), callee) {
            let arity = args.len();
            let Some(function) = e.external_function(module, field.as_str())? else {
                self.shallow(e, n);
                return Ok(());
            };
            let View::Apply { args, .. } = e.bir().view(n) else {
                unreachable!()
            };
            let args: smallvec::SmallVec<[NodeId; 8]> = args.into();
            let View::Fun { header, .. } = e.bir().view(function) else {
                unreachable!()
            };
            // `external_inline_args_are_allowed` (lam_pass_remove_alias.rs:100-105).
            let allowed = args.iter().all(|arg| match e.bir().view(*arg) {
                View::Var { var } => self.table.entry(e, var) != Entry::Param,
                _ => true,
            });
            let inline = e.bir().function(header).params.len() == arity
                && allowed
                && crate::lambda::lam_analysis::attr_can_be_inlined(
                    e.bir().function_attributes(header),
                );
            if inline {
                self.inline(e, n, function, None)?;
                fired(e, "inline-external");
                self.work.push(Work::Simpl(n));
            } else {
                self.shallow(e, n);
            }
            e.release(function);
            return Ok(());
        }
        match e.bir().view(callee) {
            View::Var { .. } => {
                let args: smallvec::SmallVec<[NodeId; 8]> = args.into();
                self.work.push(Work::Apply(n, self.revision));
                self.work.extend(args.into_iter().rev().map(Work::Simpl));
            }
            // lam_pass_remove_alias.rs:416-423: an applied function.
            View::Fun { header, .. }
                if e.bir().function(header).params.len() == args.len()
                    && crate::lambda::lam_analysis::attr_can_be_inlined(
                        e.bir().function_attributes(header),
                    ) =>
            {
                self.inline(e, n, callee, None)?;
                fired(e, "inline-applied-function");
                self.work.push(Work::Simpl(n));
            }
            _ => self.shallow(e, n),
        }
        Ok(())
    }

    /// `simpl_apply` on a variable (lam_pass_remove_alias.rs:341-415,
    /// lam_pass_remove_alias.ml:163-240), once the arguments are swept.
    fn apply_known(&mut self, e: &mut Engine<'_>, n: NodeId, before: u64) -> Result<(), Unsupported> {
        use crate::lambda::InlineAttribute;
        let View::Apply { callee, args, .. } = e.bir().view(n) else {
            unreachable!()
        };
        let View::Var { var } = e.bir().view(callee) else {
            unreachable!()
        };
        let args: smallvec::SmallVec<[NodeId; 8]> = args.into();
        let Entry::Function {
            node,
            rec,
            inlinable: true,
        } = self.table.entry(e, var)
        else {
            self.finish(e, n, before);
            return Ok(());
        };
        let function = e.as_of_round_start(node);
        let View::Fun { body, header } = e.bir().view(function) else {
            unreachable!()
        };
        let attr = e.bir().function_attributes(header);
        let (functor, always) = (attr.is_a_functor, attr.inline == InlineAttribute::Always);
        let params = e.bir().function(header).params;
        if !crate::lambda::lam_analysis::attr_can_be_inlined(attr) || args.len() != params.len() {
            self.finish(e, n, before);
            return Ok(());
        }
        if functor {
            self.inline(e, n, node, None)?;
            fired(e, "inline-functor");
            self.work.push(Work::Simpl(n));
            return Ok(());
        }
        if !beta::ok_to_inline(e, function, &args) {
            self.finish(e, n, before);
            return Ok(());
        }
        let (closed, stats) = beta::closed_with_stats(e, &mut self.scratch, params, body);
        if e.bir().vars().flags(var).contains(VarFlags::EXPORTED) && !closed {
            self.finish(e, n, before);
            return Ok(());
        }
        match rec {
            Rec::Rec => {
                self.inline(e, n, node, Some(&stats))?;
                fired(e, "inline-recursive");
                e.finish_candidate(n);
            }
            Rec::SelfRec => self.finish(e, n, before),
            Rec::NonRec => {
                if args.iter().any(|arg| super::flatten::hit(e, *arg, var))
                    || (self.depth >= MAX_INLINE_DEPTH && !always)
                {
                    self.finish(e, n, before);
                } else {
                    self.inline(e, n, node, Some(&stats))?;
                    fired(e, "inline-application");
                    self.depth += 1;
                    self.work.push(Work::DepthDown);
                    self.work.push(Work::Simpl(n));
                }
            }
        }
        Ok(())
    }

    /// `simpl` (lam_pass_remove_alias.rs:155-220).
    fn simpl(&mut self, e: &mut Engine<'_>, n: NodeId) -> Result<(), Unsupported> {
        if !e.enter_candidate(n, CANDIDATES) {
            return Ok(());
        }
        match e.bir().node(n).op() {
            Op::Prim => self.prim(e, n),
            Op::If => self.if_(e, n),
            Op::Apply => self.apply(e, n)?,
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
        scratch: Scratch::default(),
        work: vec![Work::Simpl(root)],
        revision: 0,
        depth: 0,
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
            Work::Apply(n, before) => pass.apply_known(e, n, before),
            Work::GuardEnter(n) => {
                e.guard_enter(n);
                Ok(())
            }
            Work::GuardExit => {
                e.guard_exit();
                Ok(())
            }
            Work::DepthDown => {
                pass.depth -= 1;
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
    use crate::bir::bridge::{export_lambda, import_lambda};
    use crate::bir::engine::Stats;
    use crate::bir::engine::testing::{call, id, prim};
    use crate::bir::l::beta::testing::*;
    use crate::ident::Ident;
    use crate::lambda::arena::{Lam, LamArena};
    use crate::lambda::lam_compat::LetKind;
    use crate::lambda::lam_constant::Constant as C;
    use crate::lambda::{FunctionAttribute, InlineAttribute, Lambda};
    use crate::name::Name;

    #[derive(Default)]
    struct Setup {
        jsx_preserve: bool,
        exports: Vec<Ident>,
        externals: Vec<(&'static str, &'static str, Lambda)>,
    }

    fn dump(a: &LamArena, root: Lam) -> String {
        let mut out = Vec::new();
        crate::lambda::sexp_lambda::print_lambda(&a.export(root), &mut out).unwrap();
        String::from_utf8(out).unwrap()
    }

    /// The same input to `collect_info` + `simplify_alias` and to the round:
    /// every binder's fact, the dumps and every identifier are compared.
    fn compare_with(a: LamArena, root: Lam, setup: &Setup) -> Stats {
        let tree = a.export(root);
        let mut a = LamArena::new();
        let root = a.import(&tree);
        let mut imported = import_lambda(&a, root).unwrap();
        crate::bir::shadow::mark_exports(&mut imported, &setup.exports);
        let mut arities = crate::bir::l::arity::Arities::default();
        crate::bir::shadow::collect_arities(&mut imported, &mut arities, &mut |_, _| None);
        let stamp = a.ident_stamp_bound();
        let mut meta = crate::lambda::lam_stats::LamStats::new(setup.exports.clone());
        meta.id_gen.set_current_stamp(stamp);
        crate::lambda::lam_pass_collect::collect_info(&a, &mut meta, root);
        let table = meta.ident_tbl.clone();
        let mut resolver = |module: &Ident, field: &str| {
            setup
                .externals
                .iter()
                .find(|(m, f, _)| *m == module.name() && *f == field)
                .map(|(_, _, lambda)| lambda.clone())
        };
        let expected = crate::lambda::lam_pass_remove_alias::simplify_alias(
            &mut a,
            &mut meta,
            root,
            setup.jsx_preserve,
            &mut resolver,
        );
        let (stats, _) = crate::bir::shadow::run_alias(
            &mut imported,
            &setup.exports,
            stamp as u32,
            setup.jsx_preserve,
            &mut resolver,
            &arities,
            &a,
            &table,
            "test",
        )
        .unwrap()
        .unwrap();
        imported.arena.validate(Some(imported.root), false).unwrap();
        let actual = export_lambda(&imported).unwrap();
        assert_eq!(dump(&actual.arena, actual.root), dump(&a, expected));
        assert_eq!(
            super::super::flatten::identities(&actual.arena, actual.root),
            super::super::flatten::identities(&a, expected)
        );
        stats
    }
    fn compare(a: LamArena, root: Lam) -> Stats {
        compare_with(a, root, &Setup::default())
    }

    fn count(stats: &Stats, rule: &str) -> u64 {
        stats.rules.get(rule).copied().unwrap_or(0)
    }

    // ------------------------------------------------------ field reads

    /// `field_flatten_get` on a block (lam_util.rs:139-142): each simple
    /// form, a form that is not simple, and an index outside the block.
    #[test]
    fn a_field_of_a_known_block_is_its_simple_element() {
        for index in [0, 1, 2, 3, 4, 9, -1] {
            let mut a = LamArena::new();
            let (b, y, m) = (id("b", 1), id("y", 2), id("m", 3));
            let e0 = a.var(y);
            let e1 = int(&mut a, 7);
            let g = global(&mut a, "M");
            let e2 = module_field(&mut a, "f", g);
            let vm = a.var(m);
            let e3 = module_field(&mut a, "g", vm);
            let e4 = call(&mut a, "effect", 4);
            let block = tuple(&mut a, &[e0, e1, e2, e3, e4]);
            let vb = a.var(b);
            let got = field(&mut a, index, vb);
            let other = call(&mut a, "use", 5);
            let body = a.seq_raw(got, other);
            let root = a.let_(LetKind::Strict, b, block, body);
            let stats = compare(a, root);
            assert_eq!(count(&stats, "field-of-block"), u64::from((0..4).contains(&index)));
        }
    }

    /// lam_util.rs:134-137: a field of a variable bound to a module.
    #[test]
    fn a_field_of_a_module_alias_reads_the_module() {
        let mut a = LamArena::new();
        let m = id("m", 1);
        let g = global(&mut a, "M");
        let vm = a.var(m);
        let got = module_field(&mut a, "f", vm);
        let root = a.let_(LetKind::Alias, m, g, got);
        assert_eq!(count(&compare(a, root), "field-of-module"), 1);
    }

    /// lam_util.rs:143-175: a record constant is read by field name, another
    /// block by position, and an element that allocates is not copied.
    #[test]
    fn a_field_of_a_constant_block_is_its_element_unless_it_allocates() {
        let inner = C::Block {
            tag_info: Box::new(TagInfo::Tuple),
            elements: vec![C::int(1)],
        };
        for (record, index, name) in [
            (true, 0, "second"),
            (true, 1, "first"),
            (true, 0, "missing"),
            (true, 2, "nested"),
            (false, 1, "x"),
            (false, 2, "x"),
            (false, 7, "x"),
        ] {
            let mut a = LamArena::new();
            let c = id("c", 1);
            let tag = if record {
                TagInfo::record(
                    vec![
                        ("first".into(), false),
                        ("second".into(), false),
                        ("nested".into(), false),
                    ],
                    crate::parser::ast::MutableFlag::Immutable,
                )
            } else {
                TagInfo::Tuple
            };
            let constant = a.const_(C::Block {
                tag_info: Box::new(tag),
                elements: vec![C::int(10), C::string("s"), inner.clone()],
            });
            let vc = a.var(c);
            let info = if record {
                FieldDbgInfo::Record {
                    name: Name::new(name),
                }
            } else {
                FieldDbgInfo::Tuple
            };
            let got = prim(&mut a, Primitive::Pfield(index, info), &[vc]);
            let root = a.let_(LetKind::Alias, c, constant, got);
            compare(a, root);
        }
    }

    /// C.2 row 1: an element is read as it was when the round started. The
    /// block's element `m.f` is rewritten to `M.f` earlier in the same
    /// sweep; the read of the block still gives `m.f`.
    #[test]
    fn a_block_element_rewritten_earlier_in_the_sweep_is_read_as_it_was() {
        let mut a = LamArena::new();
        let (m, b) = (id("m", 1), id("b", 2));
        let g = global(&mut a, "M");
        let vm = a.var(m);
        let element = module_field(&mut a, "f", vm);
        let block = tuple(&mut a, &[element]);
        let vb = a.var(b);
        let got = field(&mut a, 0, vb);
        let inner = a.let_(LetKind::Strict, b, block, got);
        let root = a.let_(LetKind::Alias, m, g, inner);
        let stats = compare(a, root);
        assert_eq!(count(&stats, "field-of-module"), 1);
        assert_eq!(count(&stats, "field-of-block"), 1);
    }

    // ------------------------------------------------ optional values

    fn option_values(a: &mut LamArena, which: usize, x: Ident) -> Lam {
        let vx = a.var(x);
        match which {
            0 => prim(a, Primitive::Psome, &[vx]),
            1 => prim(a, Primitive::PsomeNotNest, &[vx]),
            2 => {
                let c = int(a, 3);
                prim(a, Primitive::Psome, &[c])
            }
            3 => {
                let c = a.const_(C::Block {
                    tag_info: Box::new(TagInfo::Tuple),
                    elements: vec![C::int(1)],
                });
                prim(a, Primitive::Psome, &[c])
            }
            4 => {
                let inner = call(a, "effect", 9);
                prim(a, Primitive::Psome, &[inner])
            }
            5 => prim(a, Primitive::PnullToOpt, &[vx]),
            6 => prim(a, Primitive::PnullUndefinedToOpt, &[vx]),
            7 => {
                let inner = call(a, "effect", 9);
                prim(a, Primitive::PnullToOpt, &[inner])
            }
            8 => a.const_(C::Some(Box::new(C::int(1)))),
            9 => tuple(a, &[vx]),
            10 => prim(
                a,
                Primitive::Pmakeblock(TagInfo::Tuple, Mutable::Mutable),
                &[vx],
            ),
            11 => {
                let c = a.const_(C::JsFalse);
                prim(a, Primitive::Psome, &[c])
            }
            _ => call(a, "unknown", 9),
        }
    }

    /// lam_pass_remove_alias.rs:272-293: both unwrapping primitives on each
    /// kind of binding.
    #[test]
    fn unwrapping_a_known_optional_gives_its_payload() {
        for which in 0..13 {
            for not_nest in [false, true] {
                let mut a = LamArena::new();
                let (v, x) = (id("v", 1), id("x", 2));
                let value = option_values(&mut a, which, x);
                let vv = a.var(v);
                let p = if not_nest {
                    Primitive::PvalFromOptionNotNest
                } else {
                    Primitive::PvalFromOption
                };
                let got = prim(&mut a, p, &[vv]);
                let root = a.let_(LetKind::Strict, v, value, got);
                compare(a, root);
            }
        }
    }

    /// lam_pass_remove_alias.rs:160-193: `if Pis_not_none v` on each kind
    /// of binding.
    #[test]
    fn a_none_test_of_a_known_binding_is_decided() {
        for which in 0..13 {
            let mut a = LamArena::new();
            let (v, x) = (id("v", 1), id("x", 2));
            let value = option_values(&mut a, which, x);
            let vv = a.var(v);
            let test = prim(&mut a, Primitive::PisNotNone, &[vv]);
            let yes = call(&mut a, "yes", 3);
            let no = call(&mut a, "no", 4);
            let cond = a.if_raw(test, yes, no);
            let root = a.let_(LetKind::Strict, v, value, cond);
            let stats = compare(a, root);
            assert_eq!(count(&stats, "if-nullable"), u64::from(matches!(which, 5 | 6)));
            assert_eq!(
                count(&stats, "if-known"),
                u64::from(matches!(which, 0..=4 | 8 | 9 | 11))
            );
        }
    }

    /// lam_pass_remove_alias.rs:194-200 with `id_is_for_sure_true_in_boolean`.
    #[test]
    fn a_condition_bound_to_a_constant_is_decided() {
        let constants = [
            Some(C::JsTrue),
            Some(C::JsFalse),
            Some(C::int(0)),
            Some(C::int(5)),
            Some(C::JsNull),
            Some(C::JsUndefined { is_unit: false }),
            Some(C::string("text")),
            None,
        ];
        for (index, constant) in constants.into_iter().enumerate() {
            for optional in [false, true] {
                let mut a = LamArena::new();
                let v = id("v", 1);
                let mut value = match constant.clone() {
                    Some(c) => a.const_(c),
                    None => call(&mut a, "unknown", 5),
                };
                if optional {
                    value = prim(&mut a, Primitive::Psome, &[value]);
                }
                let vv = a.var(v);
                let yes = call(&mut a, "yes", 3);
                let no = call(&mut a, "no", 4);
                let cond = a.if_raw(vv, yes, no);
                let root = a.let_(LetKind::Strict, v, value, cond);
                let stats = compare(a, root);
                let decided = if optional {
                    matches!(index, 1 | 4 | 5)
                } else {
                    index < 6
                };
                assert_eq!(count(&stats, "if-known"), u64::from(decided), "{index} {optional}");
            }
        }
    }

    /// lam_pass_remove_alias.rs:206-218.
    #[test]
    fn a_string_switch_on_a_bound_constant_switches_on_the_constant() {
        for constant in [C::string("b"), C::string("z"), C::int(1)] {
            for default in [false, true] {
                let mut a = LamArena::new();
                let s = id("s", 1);
                let value = a.const_(constant.clone());
                let vs = a.var(s);
                let first = call(&mut a, "a", 2);
                let second = call(&mut a, "b", 3);
                let other = call(&mut a, "other", 4);
                let info = a.add_str_switch(["a", "b"], default);
                let actions = if default {
                    a.add_list(&[first, second, other])
                } else {
                    a.add_list(&[first, second])
                };
                let switch = a.string_switch_raw(vs, actions, info);
                let root = a.let_(LetKind::Alias, s, value, switch);
                assert_eq!(count(&compare(a, root), "switch-on-constant"), 1);
            }
        }
    }

    /// The alias entry (`alias_ident_or_global`): what is known about `y`
    /// is known about `let x = y`.
    #[test]
    fn an_alias_has_the_entry_of_what_it_names() {
        let mut a = LamArena::new();
        let (b, x, y) = (id("b", 1), id("x", 2), id("y", 3));
        let vy = a.var(y);
        let block = tuple(&mut a, &[vy]);
        let vb = a.var(b);
        let vx = a.var(x);
        let got = field(&mut a, 0, vx);
        let inner = a.let_(LetKind::Alias, x, vb, got);
        let root = a.let_(LetKind::Strict, b, block, inner);
        assert_eq!(count(&compare(a, root), "field-of-block"), 1);
    }

    // --------------------------------------------------- applications

    /// `simpl_apply` on a bound function with `propagate_beta_reduce_with_map`
    /// and `simple_beta_reduce`: every body shape against every pair of
    /// argument shapes.
    #[test]
    fn an_application_of_a_bound_function_agrees_for_every_body_and_argument() {
        let mut inlined = 0;
        for body in 0..BODIES {
            for first in 0..ARGUMENTS {
                for second in 0..ARGUMENTS {
                    let mut a = LamArena::new();
                    let (f, x, y) = (id("f", 1), id("x", 2), id("y", 3));
                    let b = bodies(&mut a, body, x, y);
                    let function = fun(&mut a, &[x, y], b);
                    let vf = a.var(f);
                    let a1 = arguments(&mut a, first);
                    let a2 = arguments(&mut a, second);
                    let applied = app(&mut a, vf, &[a1, a2]);
                    let root = a.let_(LetKind::Strict, f, function, applied);
                    let stats = compare(a, root);
                    inlined += count(&stats, "inline-application");
                }
            }
        }
        assert!(inlined > 500, "{inlined}");
    }

    /// The decisions of lam_pass_remove_alias.rs:341-415 other than size:
    /// attributes, the kind of binding, exports, arity, an argument that
    /// names the function.
    #[test]
    fn the_decision_to_inline_follows_attributes_binding_and_exports() {
        let attrs = |which: usize| FunctionAttribute {
            inline: match which {
                1 => InlineAttribute::Always,
                2 => InlineAttribute::Never,
                _ => InlineAttribute::Default,
            },
            is_a_functor: which == 3,
            async_: which == 4,
            directive: (which == 5).then(|| "use server".to_string()),
            ..Default::default()
        };
        for attr in 0..6 {
            for binding in 0..5 {
                for body in [0, 4, 11] {
                    for shape in 0..4 {
                        let mut a = LamArena::new();
                        let (f, g, x, y, w) =
                            (id("f", 1), id("g", 4), id("x", 2), id("y", 3), id("w", 5));
                        let mut b = bodies(&mut a, body, x, y);
                        if binding == 3 {
                            // Not closed: uses a variable that is not a parameter.
                            let vw = a.var(w);
                            b = prim(&mut a, Primitive::Paddint, &[b, vw]);
                        }
                        let function = fun_attr(&mut a, &[x, y], b, attrs(attr));
                        let vf = a.var(f);
                        let a1 = match shape {
                            // An argument that names the function.
                            1 => a.var(f),
                            _ => arguments(&mut a, 0),
                        };
                        let a2 = arguments(&mut a, 1);
                        let applied = match shape {
                            // Too few and too many arguments.
                            2 => app(&mut a, vf, &[a1]),
                            3 => app(&mut a, vf, &[a1, a2, a2]),
                            _ => app(&mut a, vf, &[a1, a2]),
                        };
                        let tree = a.export(applied);
                        let applied = a.import(&tree);
                        let mut setup = Setup::default();
                        let root = match binding {
                            0 => a.let_(LetKind::Strict, f, function, applied),
                            1 => a.letrec(&[(f, function)], applied),
                            2 => {
                                let vx = a.var(id("p", 6));
                                let other = fun(&mut a, &[id("p", 6)], vx);
                                a.letrec(&[(f, function), (g, other)], applied)
                            }
                            _ => {
                                setup.exports = vec![f];
                                let one = int(&mut a, 1);
                                let bound = a.let_(LetKind::Strict, f, function, applied);
                                a.let_(LetKind::Strict, w, one, bound)
                            }
                        };
                        compare_with(a, root, &setup);
                    }
                }
            }
        }
    }

    /// lam_pass_remove_alias.rs:416-423: a function applied where it is
    /// written is reduced on the arguments as they are.
    #[test]
    fn an_applied_function_is_reduced() {
        for body in 0..BODIES {
            for first in [0, 1, 2, 4] {
                let mut a = LamArena::new();
                let (x, y) = (id("x", 2), id("y", 3));
                let b = bodies(&mut a, body, x, y);
                let function = fun(&mut a, &[x, y], b);
                let a1 = arguments(&mut a, first);
                let a2 = arguments(&mut a, 2);
                let root = app(&mut a, function, &[a1, a2]);
                assert_eq!(count(&compare(a, root), "inline-applied-function"), 1);
            }
        }
    }

    /// Fresh identifiers and their order: every binder of the copied body
    /// (function, `let`, `let rec`, handler, exception, the three loops) is
    /// renamed in the order `Lam_bounded_vars.rewrite` does it, a `for`
    /// loop's start expression twice. The comparison checks each stamp.
    #[test]
    fn a_copied_body_renames_every_binder_in_the_legacy_order() {
        let mut a = LamArena::new();
        let (f, x) = (id("f", 1), id("x", 2));
        let body = every_binder(&mut a, x);
        let attr = FunctionAttribute {
            inline: InlineAttribute::Always,
            ..Default::default()
        };
        let function = fun_attr(&mut a, &[x], body, attr);
        let vf = a.var(f);
        let argument = call(&mut a, "argument", 20);
        let first = app(&mut a, vf, &[argument]);
        let vf = a.var(f);
        let argument = call(&mut a, "argument", 20);
        let second = app(&mut a, vf, &[argument]);
        let both = a.seq_raw(first, second);
        let root = a.let_(LetKind::Strict, f, function, both);
        let stats = compare(a, root);
        assert_eq!(count(&stats, "inline-application"), 2);
        // x, h, exn, i, t (twice), r, p, item: nine renames a copy.
        assert_eq!(stats.renames.len(), 18);
        assert_eq!(stats.labels.len(), 2);
    }

    /// C.2 row 1 for functions. `small`'s body is a string switch on a bound
    /// constant: too big to inline. The sweep folds it to a constant before
    /// it reaches the application; the decision still reads the body as it
    /// was. `inlined` is small, and its body is rewritten before the
    /// application is reached: what is inlined is the body as it was.
    #[test]
    fn a_function_rewritten_earlier_in_the_sweep_is_read_as_it_was() {
        let mut a = LamArena::new();
        let (s, small) = (id("s", 1), id("small", 2));
        let value = a.const_(C::string("a"));
        let vs = a.var(s);
        let one = int(&mut a, 1);
        let two = int(&mut a, 2);
        let info = a.add_str_switch(["a"], true);
        let actions = a.add_list(&[one, two]);
        let switch = a.string_switch_raw(vs, actions, info);
        let unit = id("unit", 3);
        let function = fun(&mut a, &[unit], switch);
        let vf = a.var(small);
        let argument = a.unit();
        let applied = app(&mut a, vf, &[argument]);
        let bound = a.let_(LetKind::Strict, small, function, applied);
        let root = a.let_(LetKind::Alias, s, value, bound);
        let stats = compare(a, root);
        assert_eq!(count(&stats, "switch-on-constant"), 1);
        assert_eq!(count(&stats, "inline-application"), 0);

        let mut a = LamArena::new();
        let (m, inlined, x) = (id("m", 1), id("inlined", 2), id("x", 3));
        let g = global(&mut a, "M");
        let vm = a.var(m);
        let got = module_field(&mut a, "f", vm);
        let vx = a.var(x);
        let body = app(&mut a, got, &[vx]);
        let function = fun(&mut a, &[x], body);
        let vf = a.var(inlined);
        let argument = call(&mut a, "argument", 9);
        let applied = app(&mut a, vf, &[argument]);
        let bound = a.let_(LetKind::Strict, inlined, function, applied);
        let root = a.let_(LetKind::Alias, m, g, bound);
        let stats = compare(a, root);
        assert_eq!(stats.snapshots, 1);
        // Once in the definition, once more in the inlined copy.
        assert_eq!(count(&stats, "field-of-module"), 2);
    }

    /// C.2 row 2: inlining nests at most `MAX_INLINE_DEPTH` deep. Each
    /// function of the chain calls the one before; a function marked
    /// `@inline` is inlined at any depth.
    #[test]
    fn inlining_nests_at_most_four_deep() {
        for always in [false, true] {
            let mut a = LamArena::new();
            let n = 9;
            let argument = call(&mut a, "argument", 99);
            let last = a.var(id("f", n));
            let mut root = app(&mut a, last, &[argument]);
            for level in (1..=n).rev() {
                let vx = a.var(id("x", 100 + level));
                let body = if level == 1 {
                    let one = int(&mut a, 1);
                    prim(&mut a, Primitive::Paddint, &[vx, one])
                } else {
                    let previous = a.var(id("f", level - 1));
                    let call = app(&mut a, previous, &[vx]);
                    let effect = call_(&mut a);
                    a.seq_raw(effect, call)
                };
                let attr = FunctionAttribute {
                    inline: if always {
                        InlineAttribute::Always
                    } else {
                        InlineAttribute::Default
                    },
                    ..Default::default()
                };
                let function = fun_attr(&mut a, &[id("x", 100 + level)], body, attr);
                root = a.let_(LetKind::Strict, id("f", level), function, root);
            }
            let stats = compare(a, root);
            // Without the limit every body would hold the whole chain below
            // it: 8 + 7 + ... + 1 applications inlined in the definitions and
            // 9 at the call. With it, a definition inlines at most 5 levels.
            let unbounded = 8 * 9 / 2 + 9;
            if always {
                assert_eq!(count(&stats, "inline-application"), unbounded);
            } else {
                assert!(count(&stats, "inline-application") < unbounded);
            }
        }
    }
    fn call_(a: &mut LamArena) -> Lam {
        call(a, "effect", 200)
    }

    /// lam_pass_remove_alias.rs:319-339: a function another module exports.
    #[test]
    fn an_application_of_an_exported_function_of_another_module_is_inlined() {
        let external = |which: usize| {
            let mut a = LamArena::new();
            let (p, t) = (id("p", 900), id("t", 901));
            let vp = a.var(p);
            let one = int(&mut a, 1);
            let sum = prim(&mut a, Primitive::Paddint, &[vp, one]);
            let body = if which == 0 {
                sum
            } else {
                let vt = a.var(t);
                let vt2 = a.var(t);
                let twice = prim(&mut a, Primitive::Pmulint, &[vt, vt2]);
                let g = global(&mut a, "Other");
                let got = module_field(&mut a, "h", g);
                let called = app(&mut a, got, &[twice]);
                a.let_(LetKind::Strict, t, sum, called)
            };
            let attr = FunctionAttribute {
                async_: which == 2,
                ..Default::default()
            };
            let function = fun_attr(&mut a, &[p], body, attr);
            a.export(function)
        };
        for which in 0..3 {
            for shape in 0..4 {
                let mut a = LamArena::new();
                let g = global(&mut a, "M");
                let callee = module_field(&mut a, "f", g);
                let outer = id("outer", 1);
                let argument = match shape {
                    0 => call(&mut a, "argument", 2),
                    // A parameter is not passed to an inlined body.
                    1 => a.var(outer),
                    _ => a.var(id("free", 3)),
                };
                let applied = match shape {
                    3 => {
                        let extra = int(&mut a, 2);
                        app(&mut a, callee, &[argument, extra])
                    }
                    _ => app(&mut a, callee, &[argument]),
                };
                let root = fun(&mut a, &[outer], applied);
                let setup = Setup {
                    externals: vec![("M", "f", external(which)), ("M", "constant", Lambda::unit())],
                    ..Default::default()
                };
                let stats = compare_with(a, root, &setup);
                assert_eq!(
                    count(&stats, "inline-external"),
                    u64::from(which < 2 && matches!(shape, 0 | 2)),
                    "{which} {shape}"
                );
            }
        }
    }

    // ---------------------------------------------------- step counts

    fn steps(a: &LamArena, root: Lam) -> (u64, Stats) {
        let mut imported = crate::bir::engine::testing::import(a, root);
        let (steps, stats) = {
            let mut e = Engine::new(&mut imported.arena);
            e.run(&ALIAS, imported.root);
            (e.steps(), e.stats.clone())
        };
        assert_eq!(stats.unsupported, None);
        imported.arena.validate(Some(imported.root), false).unwrap();
        (steps, stats)
    }

    /// 10,000 aliases in a chain, the last one a condition: the chain is
    /// followed once.
    #[test]
    fn ten_thousand_aliases_in_a_chain_are_followed_once() {
        let mut a = LamArena::new();
        let n = 10_000;
        let last = a.var(id("x", n));
        let yes = call(&mut a, "yes", n + 1);
        let no = call(&mut a, "no", n + 2);
        let mut root = a.if_raw(last, yes, no);
        for i in (1..=n).rev() {
            let previous = a.var(id("x", i - 1));
            root = a.let_(LetKind::Alias, id("x", i), previous, root);
        }
        let truth = a.const_(C::JsTrue);
        root = a.let_(LetKind::Alias, id("x", 0), truth, root);
        let (steps, stats) = steps(&a, root);
        assert_eq!(count(&stats, "if-known"), 1);
        let nodes = 2 * (n as u64 + 1) + 7;
        assert!(steps <= 40 * nodes, "{steps}");
        eprintln!("alias chain: {steps} steps for {nodes} nodes");
    }

    /// A 10,000-field block read 10,000 times: the entry is built once and
    /// each read is constant.
    #[test]
    fn a_ten_thousand_field_block_read_ten_thousand_times_is_linear() {
        let mut a = LamArena::new();
        let n = 10_000;
        let b = id("b", 1);
        let elements: Vec<Lam> = (0..n).map(|i| a.var(id("e", 10 + i))).collect();
        let block = tuple(&mut a, &elements);
        let mut body = a.unit();
        for i in 0..n {
            let vb = a.var(b);
            let got = field(&mut a, i, vb);
            let user = a.var(id("use", 5));
            let used = app(&mut a, user, &[got]);
            body = a.seq_raw(used, body);
        }
        let root = a.let_(LetKind::Strict, b, block, body);
        let (steps, stats) = steps(&a, root);
        assert_eq!(count(&stats, "field-of-block"), n as u64);
        let nodes = 6 * n as u64 + 3;
        assert!(steps <= 40 * nodes, "{steps}");
        eprintln!("block reads: {steps} steps for {nodes} nodes");
    }

    /// 10,000 call sites of one small function: each costs the body.
    #[test]
    fn ten_thousand_inlined_call_sites_of_one_small_function_are_linear() {
        let mut a = LamArena::new();
        let n = 10_000;
        let (f, x) = (id("f", 1), id("x", 2));
        let vx = a.var(x);
        let t = id("t", 3);
        let negated = prim(&mut a, Primitive::Pnegint, &[vx]);
        let vt = a.var(t);
        let body = a.let_(LetKind::Strict, t, negated, vt);
        let function = fun(&mut a, &[x], body);
        let mut rest = a.unit();
        for i in 0..n {
            let vf = a.var(f);
            let argument = call(&mut a, "argument", 10 + i);
            let applied = app(&mut a, vf, &[argument]);
            rest = a.seq_raw(applied, rest);
        }
        let root = a.let_(LetKind::Strict, f, function, rest);
        let (steps, stats) = steps(&a, root);
        assert_eq!(count(&stats, "inline-application"), n as u64);
        assert_eq!(stats.renames.len(), 2 * n as usize);
        let nodes = 5 * n as u64 + 9;
        assert!(steps <= 150 * nodes, "{steps}");
        eprintln!("inlined call sites: {steps} steps for {nodes} nodes");
    }

    /// The skip rule: a unit with no application, primitive, conditional or
    /// string switch is not swept at all; in a unit that has some, a subtree
    /// without them is not entered.
    #[test]
    fn a_unit_with_nothing_to_do_is_not_entered() {
        let mut a = LamArena::new();
        let mut root = a.var(id("x", 0));
        for i in 1..=100 {
            let value = a.const_(C::int(i));
            root = a.let_(LetKind::Strict, id("x", i), value, root);
        }
        let (_, stats) = steps(&a, root);
        assert_eq!(stats.entered, 0);

        // One primitive at the bottom of the same chain: the spine is
        // entered (101 nodes), the 100 constants are not.
        let mut a = LamArena::new();
        let v = a.var(id("x", 0));
        let mut root = prim(&mut a, Primitive::Pnegint, &[v]);
        for i in 1..=100 {
            let value = a.const_(C::int(i));
            root = a.let_(LetKind::Strict, id("x", i), value, root);
        }
        let (_, stats) = steps(&a, root);
        assert_eq!(stats.entered, 101);
        assert_eq!(stats.pruned, 101);
        assert!(stats.rules.is_empty());
    }

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
        let one = int(&mut a, 1);
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
