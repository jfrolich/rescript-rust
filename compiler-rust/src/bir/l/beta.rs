//! Beta reduction on Bir: `lam_beta_reduce.rs` (`simple_beta_reduce`,
//! `propagate`, `rewrite_bounded_vars`) and the analyses it and the inlining
//! decision read (`lam_analysis.rs`, `lam_closure.rs`). Compiler originals:
//! compiler/core/lam_beta_reduce.ml, lam_beta_reduce_util.ml,
//! lam_bounded_vars.ml, lam_closure.ml.
//!
//! The reduced term is a copy of the function body: the function stays where
//! it is bound, as today. The copy gives every binder a fresh variable in the
//! order `Lam_bounded_vars.rewrite` renames them, and each copied node goes
//! through the normalising rule of its opcode as it is built, bottom-up,
//! which is what rebuilding through the smart constructors does.
//!
//! Costs. Every analysis is a walk of the candidate body or of an argument,
//! with an explicit stack; none walks the unit. The copy is one visit and one
//! allocation per body node. The substitution and the set of bound variables
//! are dense tables indexed by variable, kept across reductions and reset
//! through the list of entries touched, so a reduction costs its body, not
//! the variable table.
use super::exits::size_upto;
use super::flatten::{hit_with_work, pure, pure_with_work, refine};
use crate::bir::bridge::Unsupported;
use crate::bir::engine::{Engine, OpMask};
use crate::bir::*;
use crate::lambda::LamLoc;
use crate::lambda::lam_compat::FieldDbgInfo;
use crate::lambda::lam_primitive::Primitive;
use smallvec::SmallVec;

/// `Lam_analysis.small_inline_size`.
const SMALL_INLINE_SIZE: usize = 5;

/// What a parameter, or a binder of the body, becomes in the copy.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Sub {
    /// Not substituted.
    Keep,
    Var(VarId),
    Const(ConstId),
    /// `Pidentity(var)`: a nullable conversion stays boxed.
    Identity(VarId),
    /// The argument itself, moved to the parameter's one use.
    Node(NodeId),
    /// A moved argument that was used.
    Taken,
}

/// Tables reused by every reduction of a round.
#[derive(Default)]
pub(crate) struct Scratch {
    sub: Vec<Sub>,
    touched: Vec<VarId>,
    local: Vec<u32>,
    epoch: u32,
    simple: Simple,
    read_work: Vec<ReadWork>,
    read_saved: Vec<bool>,
    copy_work: Vec<CopyWork>,
    copy_values: Vec<NodeId>,
    effects_after: Vec<bool>,
    rest: Vec<(VarId, NodeId)>,
    spare: Vec<NodeId>,
    moved: Vec<(VarId, NodeId)>,
    /// Static labels of the handlers copied so far, by source label.
    labels: hashbrown::HashMap<u32, (u32, CatchId), ahash::RandomState>,
}
impl Scratch {
    #[cfg(test)]
    pub(crate) fn capacities(&self) -> [usize; 20] {
        [
            self.sub.capacity(),
            self.touched.capacity(),
            self.local.capacity(),
            self.labels.capacity(),
            self.simple.motions.capacity(),
            self.simple.used.capacity(),
            self.simple.evaluated.capacity(),
            self.simple.delay.capacity(),
            self.simple.purity.capacity(),
            self.simple.operands.capacity(),
            self.simple.built.capacity(),
            self.simple.order.capacity(),
            self.read_work.capacity(),
            self.read_saved.capacity(),
            self.copy_work.capacity(),
            self.copy_values.capacity(),
            self.effects_after.capacity(),
            self.rest.capacity(),
            self.spare.capacity(),
            self.moved.capacity(),
        ]
    }
    #[cfg(test)]
    pub(crate) fn is_clear(&self) -> bool {
        self.touched.is_empty()
            && self.labels.is_empty()
            && self.simple.motions.is_empty()
            && self.simple.used.is_empty()
            && self.simple.evaluated.is_empty()
            && self.simple.delay.is_empty()
            && self.simple.purity.is_empty()
            && self.simple.operands.is_empty()
            && self.simple.built.is_empty()
            && self.simple.order.is_empty()
            && self.read_work.is_empty()
            && self.read_saved.is_empty()
            && self.copy_work.is_empty()
            && self.copy_values.is_empty()
            && self.effects_after.is_empty()
            && self.rest.is_empty()
            && self.spare.is_empty()
            && self.moved.is_empty()
    }
    fn get(&self, var: VarId) -> Sub {
        self.sub.get(var.index()).copied().unwrap_or(Sub::Keep)
    }
    fn set(&mut self, var: VarId, sub: Sub) {
        if self.sub.len() <= var.index() {
            self.sub.resize(var.index() + 1, Sub::Keep);
        }
        if self.sub[var.index()] == Sub::Keep {
            self.touched.push(var);
        }
        self.sub[var.index()] = sub;
    }
    fn reset(&mut self) {
        for var in self.touched.drain(..) {
            self.sub[var.index()] = Sub::Keep;
        }
        self.labels.clear();
    }
    fn bind(&mut self, var: VarId) {
        if self.local.len() <= var.index() {
            self.local.resize(var.index() + 1, 0);
        }
        self.local[var.index()] = self.epoch;
    }
    fn bound(&self, var: VarId) -> bool {
        self.local.get(var.index()) == Some(&self.epoch)
    }
}

fn param_index(params: VarSpan, var: VarId) -> Option<usize> {
    (var.0 >= params.start && var.0 - params.start < params.len)
        .then(|| (var.0 - params.start) as usize)
}

/// `Lam_analysis.delay_safe` (lam_analysis.rs:264-305, lam_analysis.ml:141-193).
/// `assignable` is the `ASSIGNED` flag.
fn delay_safe(e: &Engine<'_>, root: NodeId, work: &mut Vec<NodeId>, purity: &mut Vec<NodeId>) -> bool {
    let b = e.bir();
    work.clear(); work.push(root);
    let result = (|| {
    while let Some(n) = work.pop() {
        match b.view(n) {
            View::Const { .. } | View::Fun { .. } | View::Global { .. } => continue,
            View::Var { var } => {
                if b.vars().flags(var).contains(VarFlags::ASSIGNED) {
                    return false;
                }
            }
            View::If { .. } => {}
            View::Prim { primitive, .. } => match &b.primitive(primitive).primitive {
                Primitive::Pdivint
                | Primitive::Pmodint
                | Primitive::Pdivbigint
                | Primitive::Pmodbigint
                | Primitive::Ppowbigint => {
                    if !pure_with_work(e, n, purity) {
                        return false;
                    }
                }
                p => {
                    if !crate::lambda::lam_analysis::primitive_is_delay_safe(p) {
                        return false;
                    }
                }
            },
            _ => return false,
        }
        let view = b.view(n);
        work.extend((0..view.child_count()).map(|at| view.child_at(at)));
    }
    true
    })();
    work.clear(); result
}

/// `Lam_beta_reduce_util` motion (lam_beta_reduce.rs:20-48).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Motion {
    Anywhere,
    Reads,
    Effects,
}
fn motion(e: &Engine<'_>, n: NodeId, work: &mut Vec<NodeId>, purity: &mut Vec<NodeId>) -> Motion {
    if delay_safe(e, n, work, purity) {
        Motion::Anywhere
    } else if pure_with_work(e, n, purity) {
        Motion::Reads
    } else {
        Motion::Effects
    }
}
fn conflict(a: Motion, b: Motion) -> bool {
    matches!(
        (a, b),
        (Motion::Effects, Motion::Reads | Motion::Effects) | (Motion::Reads, Motion::Effects)
    )
}

#[derive(Clone, Copy)]
enum Operand {
    Arg(usize),
    Var(VarId),
    Const(ConstId),
}

/// `SimpleReduction` (lam_beta_reduce.rs:53-143).
#[derive(Default)]
struct Simple {
    params: VarSpan,
    motions: Vec<Motion>,
    used: Vec<bool>,
    evaluated: Vec<(usize, Motion)>,
    delay: Vec<NodeId>,
    purity: Vec<NodeId>,
    operands: Vec<Operand>,
    built: Vec<NodeId>,
    order: Vec<(usize, Motion)>,
}
impl Simple {
    fn evaluate(&mut self, conditional: bool, rank: usize, motion: Motion) -> Option<()> {
        if conditional && motion == Motion::Effects {
            return None;
        }
        self.evaluated.push((rank, motion));
        Some(())
    }
    fn variable(&mut self, e: &Engine<'_>, conditional: bool, n: NodeId, x: VarId) -> Option<Operand> {
        match param_index(self.params, x).filter(|i| *i < self.used.len()) {
            Some(i) if self.used[i] => None,
            Some(i) => {
                self.used[i] = true;
                self.evaluate(conditional, i, self.motions[i])?;
                Some(Operand::Arg(i))
            }
            None => {
                let motion = motion(e, n, &mut self.delay, &mut self.purity);
                self.evaluate(conditional, self.params.len(), motion)?;
                Some(Operand::Var(x))
            }
        }
    }
    fn operands(
        &mut self,
        e: &Engine<'_>,
        conditional_from: usize,
        nodes: &[NodeId],
    ) -> Option<()> {
        self.operands.clear();
        for (i, &n) in nodes.iter().enumerate() {
            match e.bir().view(n) {
                View::Var { var } => { let operand = self.variable(e, i >= conditional_from, n, var)?; self.operands.push(operand); }
                View::Const { value } => self.operands.push(Operand::Const(value)),
                _ => return None,
            }
        }
        Some(())
    }
    fn in_call_order(&mut self) -> bool {
        self.order.clear();
        self.order.extend((0..self.used.len())
            .filter(|i| !self.used[*i])
            .map(|i| (i, self.motions[i]))
            .chain(self.evaluated.iter().copied()));
        self.order.iter().enumerate().all(|(k, &(rank, m))| {
            self.order[k + 1..]
                .iter()
                .all(|&(later_rank, later)| rank <= later_rank || !conflict(m, later))
        })
    }
}

fn leaf(e: &mut Engine<'_>, operand: Operand, args: &[NodeId], weight: u32) -> NodeId {
    match operand {
        Operand::Arg(i) => args[i],
        Operand::Var(var) => e.node(View::Var { var }, 0, weight),
        Operand::Const(value) => e.node(View::Const { value }, 0, weight),
    }
}

/// `Lam_beta_reduce_util.simple_beta_reduce` (lam_beta_reduce.rs:145-236,
/// lam_beta_reduce_util.ml:25-193). The plan is checked before anything is
/// built, so a refusal leaves the arguments untouched.
fn simple(
    e: &mut Engine<'_>,
    scratch: &mut Scratch,
    params: VarSpan,
    body: NodeId,
    args: &[NodeId],
    weight: u32,
) -> Option<NodeId> {
    let n = params.len().min(args.len());
    let mut r = std::mem::take(&mut scratch.simple);
    r.params = params;
    for &arg in &args[..n] { let motion = motion(e, arg, &mut r.delay, &mut r.purity); r.motions.push(motion); }
    r.used.resize(n, false);
    let result = (|| {
    let result = match e.bir().view(body) {
        View::Prim {
            args: operands,
            primitive,
        } => {
            let conditional_from = if e.bir().primitive(primitive).primitive.may_skip_operands() {
                1
            } else {
                usize::MAX
            };
            r.operands(e, conditional_from, operands)?;
            if !r.in_call_order() {
                return None;
            }
            r.built.extend(r.operands.iter().map(|o| leaf(e, *o, args, weight)));
            let node = e.node(
                View::Prim {
                    args: &r.built,
                    primitive,
                },
                0,
                weight,
            );
            e.copy_cold(body, node);
            e.normalise(node);
            node
        }
        View::Apply {
            callee,
            args: operands,
            info,
        } => {
            // The function is evaluated before the arguments.
            let callee_plan = match e.bir().view(callee) {
                View::Var { var } => Some(r.variable(e, false, callee, var)?),
                View::Prim {
                    args: [module],
                    primitive,
                } if matches!(e.bir().primitive(primitive).primitive, Primitive::Pfield(..))
                    && e.bir().node(*module).op() == Op::Global =>
                {
                    None
                }
                _ => return None,
            };
            r.operands(e, usize::MAX, operands)?;
            if !r.in_call_order() {
                return None;
            }
            let new_callee = match callee_plan {
                Some(operand) => leaf(e, operand, args, weight),
                None => {
                    let View::Prim {
                        args: [module],
                        primitive,
                    } = e.bir().view(callee)
                    else {
                        unreachable!()
                    };
                    let View::Global { module } = e.bir().view(*module) else {
                        unreachable!()
                    };
                    let global = e.node(View::Global { module }, 0, weight);
                    let field = e.node(
                        View::Prim {
                            args: &[global],
                            primitive,
                        },
                        0,
                        weight,
                    );
                    e.copy_cold(callee, field);
                    field
                }
            };
            r.built.extend(r.operands.iter().map(|o| leaf(e, *o, args, weight)));
            let node = e.node(
                View::Apply {
                    callee: new_callee,
                    args: &r.built,
                    info,
                },
                0,
                weight,
            );
            e.copy_cold(body, node);
            node
        }
        _ => return None,
    };
    // `Lam_beta_reduce_util.seq_unused`: the unused arguments first, in
    // parameter order.
    let mut result = result;
    for index in (0..n).rev() {
        if !r.used[index] {
            result = e.node(
                View::Seq {
                    first: args[index],
                    second: result,
                },
                0,
                weight,
            );
            e.normalise(result);
        }
    }
    Some(result)
    })();
    r.motions.clear(); r.used.clear(); r.evaluated.clear(); r.delay.clear(); r.purity.clear();
    r.operands.clear(); r.built.clear(); r.order.clear();
    scratch.simple = r;
    result
}

/// `Lam_beta_reduce.read_before_effects` (lam_beta_reduce.rs:262-336,
/// lam_beta_reduce.ml:52-92).
enum ReadWork {
        Visit(NodeId),
        PrimDone(NodeId),
        ApplyDone,
        Save,
        Swap,
        Join,
    }
fn read_before_effects(e: &Engine<'_>, scratch: &mut Scratch, param: VarId, body: NodeId) -> bool {
    let b = e.bir();
    let mut effects = false;
    let mut saved = std::mem::take(&mut scratch.read_saved);
    let mut work = std::mem::take(&mut scratch.read_work);
    work.push(ReadWork::Visit(body));
    let result = (|| {
    while let Some(task) = work.pop() {
        match task {
            ReadWork::PrimDone(n) => {
                if !pure_with_work(e, n, &mut scratch.simple.purity) {
                    effects = true;
                }
            }
            ReadWork::ApplyDone => effects = true,
            ReadWork::Save => saved.push(effects),
            ReadWork::Swap => {
                let before = saved.pop().expect("saved effects");
                saved.push(effects);
                effects = before;
            }
            ReadWork::Join => effects |= saved.pop().expect("saved effects"),
            ReadWork::Visit(n) => match b.view(n) {
                View::Var { var } => {
                    if effects && var == param {
                        return false;
                    }
                }
                View::Const { .. } | View::Global { .. } => {}
                View::Prim { args, .. } => {
                    work.push(ReadWork::PrimDone(n));
                    work.extend(args.iter().rev().copied().map(ReadWork::Visit));
                }
                View::Apply { callee, args, .. } => {
                    work.push(ReadWork::ApplyDone);
                    work.extend(args.iter().rev().copied().map(ReadWork::Visit));
                    work.push(ReadWork::Visit(callee));
                }
                View::Let { value, body, .. } => {
                    work.push(ReadWork::Visit(body));
                    work.extend(value.map(ReadWork::Visit));
                }
                View::Seq { first, second } => {
                    work.push(ReadWork::Visit(second));
                    work.push(ReadWork::Visit(first));
                }
                View::If {
                    condition,
                    then_,
                    else_,
                } => {
                    work.push(ReadWork::Join);
                    work.push(ReadWork::Visit(else_));
                    work.push(ReadWork::Swap);
                    work.push(ReadWork::Visit(then_));
                    work.push(ReadWork::Save);
                    work.push(ReadWork::Visit(condition));
                }
                // lam_beta_reduce.rs:312-333: code that may run later.
                _ => {
                    if hit_with_work(e, n, param, &mut scratch.simple.delay) {
                        return false;
                    }
                    if !pure_with_work(e, n, &mut scratch.simple.purity) {
                        effects = true;
                    }
                }
            },
        }
    }
    true
    })();
    saved.clear(); work.clear(); scratch.read_saved = saved; scratch.read_work = work;
    result
}

/// `Lam_beta_reduce.can_move` (lam_beta_reduce.rs:345-356, lam_beta_reduce.ml:94-105).
fn can_move(e: &Engine<'_>, scratch: &mut Scratch, effects_after: bool, param: VarId, body: NodeId, arg: NodeId) -> bool {
    delay_safe(e, arg, &mut scratch.simple.delay, &mut scratch.simple.purity) || (pure_with_work(e, arg, &mut scratch.simple.purity) && !effects_after && read_before_effects(e, scratch, param, body))
}

/// `Lam_closure` statistics of one parameter (lam_closure.rs:16-70).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ParamStats {
    top: bool,
    times: i32,
}
impl ParamStats {
    fn top_and_used_zero_or_one(self) -> bool {
        self.top && (self.times == 0 || self.times == 1)
    }
}
#[derive(Clone, Copy, PartialEq, Eq)]
enum Position {
    Begin,
    NotBegin,
    Sink,
}

/// `Lam_closure.is_closed_with_map` (lam_closure.rs:130-281, lam_closure.ml):
/// the statistics of each parameter, by position, and whether the body uses
/// no variable besides its parameters, its own binders and the exports.
pub(crate) fn closed_with_stats(
    e: &Engine<'_>,
    scratch: &mut Scratch,
    params: VarSpan,
    body: NodeId,
) -> (bool, SmallVec<[ParamStats; 8]>) {
    enum Work {
        Node(NodeId, Position),
        Bind(NodeId),
    }
    let b = e.bir();
    scratch.epoch = scratch.epoch.wrapping_add(1).max(1);
    let mut stats: SmallVec<[ParamStats; 8]> = SmallVec::from_elem(
        ParamStats {
            top: true,
            times: 0,
        },
        params.len(),
    );
    let mut closed = true;
    let after = |pos: Position, n: NodeId| {
        if pos != Position::Begin || pure(e, n) {
            pos
        } else {
            Position::NotBegin
        }
    };
    let mut work = vec![Work::Node(body, Position::Begin)];
    while let Some(task) = work.pop() {
        let (n, pos) = match task {
            Work::Bind(n) => {
                for var in b.binders(n) {
                    scratch.bind(var);
                }
                continue;
            }
            Work::Node(n, pos) => (n, pos),
        };
        let mut use_var = |scratch: &Scratch, var: VarId| {
            if scratch.bound(var) || b.vars().flags(var).contains(VarFlags::EXPORTED) {
                return;
            }
            let Some(i) = param_index(params, var) else {
                closed = false;
                return;
            };
            match pos {
                Position::Begin => stats[i].times += 1,
                Position::NotBegin => {
                    stats[i].top = false;
                    stats[i].times += 1;
                }
                Position::Sink => {
                    stats[i].top = false;
                    stats[i].times = 100;
                }
            }
        };
        let sink = |n: NodeId| Work::Node(n, Position::Sink);
        match b.view(n) {
            View::Var { var } => use_var(scratch, var),
            View::Const { .. } | View::Global { .. } | View::Break | View::Continue => {}
            View::Apply { callee, args, .. } => {
                let next = after(pos, callee);
                work.extend(args.iter().rev().map(|x| Work::Node(*x, next)));
                work.push(Work::Node(callee, pos));
            }
            View::Prim { args, .. } => {
                work.extend(args.iter().rev().map(|x| Work::Node(*x, pos)));
            }
            View::Fun { body, .. } => {
                for var in b.binders(n) {
                    scratch.bind(var);
                }
                work.push(sink(body));
            }
            View::Let { value, body, .. } => {
                work.push(sink(body));
                work.push(Work::Bind(n));
                work.extend(value.map(|v| Work::Node(v, pos)));
            }
            View::LetRec { values, body, .. } => {
                for var in b.binders(n) {
                    scratch.bind(var);
                }
                work.push(sink(body));
                work.extend(values.iter().rev().copied().map(sink));
            }
            View::Switch {
                scrutinee,
                actions,
                header,
            } => {
                let next = after(pos, scrutinee);
                let h = b.switch(header);
                let cases = actions.len() - usize::from(h.has_default);
                if h.has_default {
                    let default = if h.consts_full || h.blocks_full {
                        next
                    } else {
                        Position::Sink
                    };
                    work.push(Work::Node(actions[cases], default));
                }
                work.extend(actions[..cases].iter().rev().map(|x| Work::Node(*x, next)));
                work.push(Work::Node(scrutinee, pos));
            }
            View::StrSwitch {
                scrutinee, actions, ..
            } => {
                let next = after(pos, scrutinee);
                work.extend(actions.iter().rev().map(|x| Work::Node(*x, next)));
                work.push(Work::Node(scrutinee, pos));
            }
            View::Exit { args, .. } => work.extend(args.iter().rev().copied().map(sink)),
            View::Catch { body, handler, .. } => {
                work.push(sink(handler));
                work.push(Work::Bind(n));
                work.push(sink(body));
            }
            // lam_closure.rs:232-240: the exception variable is not bound.
            View::Try { body, handler, .. } => {
                work.push(sink(handler));
                work.push(Work::Node(body, pos));
            }
            View::TryFinally { body, finaliser } => {
                work.push(sink(finaliser));
                work.push(Work::Node(body, pos));
            }
            View::If {
                condition,
                then_,
                else_,
            } => {
                let next = after(pos, condition);
                work.push(Work::Node(else_, next));
                work.push(Work::Node(then_, next));
                work.push(Work::Node(condition, pos));
            }
            View::Seq { first, second } => {
                work.push(sink(second));
                work.push(Work::Node(first, pos));
            }
            View::While { condition, body } => {
                work.push(sink(body));
                work.push(sink(condition));
            }
            View::For { parts, .. } => {
                for var in b.binders(n) {
                    scratch.bind(var);
                }
                work.extend(parts.iter().rev().copied().map(sink));
            }
            View::ForOf { iterable, body, .. } | View::ForAwaitOf { iterable, body, .. } => {
                for var in b.binders(n) {
                    scratch.bind(var);
                }
                work.push(sink(body));
                work.push(sink(iterable));
            }
            View::Assign { var, value } => {
                use_var(scratch, var);
                work.push(Work::Node(value, pos));
            }
            // Level J nodes do not occur in a Lambda-level body.
            _ => closed = false,
        }
    }
    (closed, stats)
}

/// `Lam_analysis.destruct_pattern` (lam_analysis.rs:647-685).
fn destruct_pattern(e: &Engine<'_>, params: VarSpan, body: NodeId, args: &[NodeId]) -> bool {
    let b = e.bir();
    let constant_arg = |n: NodeId| match b.view(n) {
        View::Var { var } => param_index(params, var)
            .and_then(|i| args.get(i))
            .and_then(|arg| super::norm::const_of(b, *arg)),
        _ => None,
    };
    match b.view(body) {
        View::Switch {
            scrutinee,
            actions,
            header,
        } => match constant_arg(scrutinee) {
            Some(c) => {
                let compared = std::cell::Cell::new(0);
                match super::norm::decide_switch_on(b, c, actions, header, &compared) {
                    Some((action, _)) => {
                        size_upto(b, action, SMALL_INLINE_SIZE) < SMALL_INLINE_SIZE
                    }
                    None => false,
                }
            }
            None => false,
        },
        View::If {
            condition,
            then_,
            else_,
        } => match constant_arg(condition) {
            Some(c) => {
                let branch = if super::norm::eval_as_bool(b, c) {
                    then_
                } else {
                    else_
                };
                size_upto(b, branch, SMALL_INLINE_SIZE) < SMALL_INLINE_SIZE
            }
            None => false,
        },
        _ => false,
    }
}

/// `Lam_analysis.ok_to_inline_fun_when_app` (lam_analysis.rs:632-644).
pub(crate) fn ok_to_inline(e: &Engine<'_>, function: NodeId, args: &[NodeId]) -> bool {
    use crate::lambda::InlineAttribute;
    let b = e.bir();
    let View::Fun { body, header } = b.view(function) else {
        return false;
    };
    match b.function_attributes(header).inline {
        InlineAttribute::Always => true,
        InlineAttribute::Never => false,
        InlineAttribute::Default => {
            let s = size_upto(b, body, 10);
            s < SMALL_INLINE_SIZE
                || destruct_pattern(e, b.function(header).params, body, args)
                || (args.iter().all(|x| b.node(*x).op() == Op::Const) && s < 10 && pure(e, body))
        }
    }
}

const SMART: OpMask = OpMask::SHALLOW_MAP.or(OpMask::IF).or(OpMask::SEQ);

/// `Lam_bounded_vars.rewrite` (lam_beta_reduce.rs:476-645,
/// lam_bounded_vars.ml): copy `root`, substituting and renaming every binder
/// in the order the legacy function renames them. The source is not edited.
enum CopyWork {
    Enter(NodeId),
    Rebind(NodeId),
    Build(NodeId, u32),
    /// `Lambda.for_ ident (aux l1) l2 dir l3`: the start expression is
    /// rewritten a second time (lam_beta_reduce.rs:616-618).
    Again,
    Release(NodeId),
}
fn copy(
    e: &mut Engine<'_>,
    scratch: &mut Scratch,
    root: NodeId,
    weight: u32,
) -> Result<NodeId, Unsupported> {
    fn rebind(e: &mut Engine<'_>, scratch: &mut Scratch, n: NodeId) {
        let run = e.bir().binder_run(n);
        for slot in 0..run.len() {
            let Some(var) = run.at(e.bir(), slot) else {
                continue;
            };
            let fresh = e.rename_var(var);
            scratch.set(var, Sub::Var(fresh));
        }
    }
    fn renamed(scratch: &Scratch, var: VarId) -> VarId {
        match scratch.get(var) {
            Sub::Var(fresh) => fresh,
            _ => unreachable!("binder was not renamed"),
        }
    }
    let mut work = std::mem::take(&mut scratch.copy_work);
    let mut values = std::mem::take(&mut scratch.copy_values);
    work.push(CopyWork::Enter(root));
    let result = (|| {
        while let Some(task) = work.pop() {
            match task {
                CopyWork::Rebind(n) => rebind(e, scratch, n),
                CopyWork::Release(n) => e.release(n),
                CopyWork::Again => {
                    let at = values.len() - 3;
                    let start = values.remove(at);
                    work.push(CopyWork::Release(start));
                    work.push(CopyWork::Enter(start));
                }
                CopyWork::Enter(n) => {
                    let count = e.bir().view(n).child_count();
                    match e.bir().view(n) {
                        View::Var { var } => {
                            let built = match scratch.get(var) {
                                Sub::Keep => e.node(View::Var { var }, 0, weight),
                                Sub::Var(var) => e.node(View::Var { var }, 0, weight),
                                Sub::Const(value) => e.node(View::Const { value }, 0, weight),
                                Sub::Identity(var) => {
                                    let v = e.node(View::Var { var }, 0, weight);
                                    let primitive =
                                        e.intern_prim(Primitive::Pidentity, LamLoc::NONE);
                                    let boxed = e.node(
                                        View::Prim {
                                            args: &[v],
                                            primitive,
                                        },
                                        0,
                                        weight,
                                    );
                                    e.normalise(boxed);
                                    boxed
                                }
                                Sub::Node(arg) => {
                                    scratch.set(var, Sub::Taken);
                                    arg
                                }
                                Sub::Taken => {
                                    unreachable!("an argument moved to one use was used twice")
                                }
                            };
                            values.push(built);
                        }
                        View::Const { value } => {
                            let built = e.node(View::Const { value }, 0, weight);
                            values.push(built);
                        }
                        View::Global { module } => {
                            let built = e.node(View::Global { module }, 0, weight);
                            values.push(built);
                        }
                        View::Break => {
                            let built = e.node(View::Break, 0, weight);
                            values.push(built);
                        }
                        View::Continue => {
                            let built = e.node(View::Continue, 0, weight);
                            values.push(built);
                        }
                        View::Fun { .. } | View::Let { .. } | View::LetRec { .. } => {
                            if matches!(e.bir().view(n), View::Let { value: None, .. }) {
                                return Err(Unsupported("released let value"));
                            }
                            rebind(e, scratch, n);
                            work.push(CopyWork::Build(n, index(count)));
                            work.extend(
                                (0..count)
                                    .rev()
                                    .map(|at| CopyWork::Enter(e.bir().view(n).child_at(at))),
                            );
                        }
                        View::Try { body, handler, .. } => {
                            work.push(CopyWork::Build(n, 2));
                            work.push(CopyWork::Enter(handler));
                            work.push(CopyWork::Rebind(n));
                            work.push(CopyWork::Enter(body));
                        }
                        View::For { .. } => {
                            rebind(e, scratch, n);
                            work.push(CopyWork::Build(n, 3));
                            work.push(CopyWork::Again);
                            work.extend(
                                (0..count)
                                    .rev()
                                    .map(|at| CopyWork::Enter(e.bir().view(n).child_at(at))),
                            );
                        }
                        View::ForOf { .. } | View::ForAwaitOf { .. } => {
                            rebind(e, scratch, n);
                            work.push(CopyWork::Build(n, 2));
                            work.extend(
                                (0..count)
                                    .rev()
                                    .map(|at| CopyWork::Enter(e.bir().view(n).child_at(at))),
                            );
                        }
                        // The legacy copy keeps the label; Bir identifies a
                        // handler by its label, so the copy gets a new one that
                        // the bridge exports under the old name.
                        View::Catch {
                            body,
                            handler,
                            header,
                        } => {
                            let source = e.bir().catch(header).label;
                            let copied = e.copy_catch_header(source);
                            scratch.labels.insert(source, copied);
                            work.push(CopyWork::Build(n, 2));
                            work.push(CopyWork::Enter(handler));
                            work.push(CopyWork::Rebind(n));
                            work.push(CopyWork::Enter(body));
                        }
                        View::Exit { .. } => {
                            work.push(CopyWork::Build(n, index(count)));
                            work.extend(
                                (0..count)
                                    .rev()
                                    .map(|at| CopyWork::Enter(e.bir().view(n).child_at(at))),
                            );
                        }
                        View::Apply { .. }
                        | View::Prim { .. }
                        | View::Switch { .. }
                        | View::StrSwitch { .. }
                        | View::TryFinally { .. }
                        | View::If { .. }
                        | View::Seq { .. }
                        | View::While { .. }
                        | View::Assign { .. } => {
                            work.push(CopyWork::Build(n, index(count)));
                            work.extend(
                                (0..count)
                                    .rev()
                                    .map(|at| CopyWork::Enter(e.bir().view(n).child_at(at))),
                            );
                        }
                        _ => return Err(Unsupported("JS-level node in Lambda export")),
                    }
                }
                CopyWork::Build(n, count) => {
                    let count = count as usize;
                    let start = values.len() - count;
                    let c = &values[start..];
                    let aux = e.bir().node(n).aux();
                    let built = match e.bir().view(n) {
                        View::Apply { info, .. } => e.node(
                            View::Apply {
                                callee: c[0],
                                args: &c[1..],
                                info,
                            },
                            aux,
                            weight,
                        ),
                        View::Fun { header, .. } => {
                            let old = e.bir().function(header).params;
                            let params = VarSpan {
                                start: old.iter().next().map_or(0, |v| renamed(scratch, v).0),
                                len: old.len,
                            };
                            debug_assert!(
                                old.iter()
                                    .zip(params.iter())
                                    .all(|(o, p)| renamed(scratch, o) == p)
                            );
                            let header = e.function_header(params, header);
                            e.node(View::Fun { body: c[0], header }, aux, weight)
                        }
                        View::Let { var, .. } => e.node(
                            View::Let {
                                var: renamed(scratch, var),
                                value: Some(c[0]),
                                body: c[1],
                            },
                            aux,
                            weight,
                        ),
                        View::LetRec { first, .. } => e.node(
                            View::LetRec {
                                first: renamed(scratch, first),
                                values: &c[..count - 1],
                                body: c[count - 1],
                            },
                            aux,
                            weight,
                        ),
                        View::Prim { primitive, .. } => {
                            e.node(View::Prim { args: c, primitive }, aux, weight)
                        }
                        View::Switch { header, .. } => e.node(
                            View::Switch {
                                scrutinee: c[0],
                                actions: &c[1..],
                                header,
                            },
                            aux,
                            weight,
                        ),
                        View::StrSwitch { header, .. } => e.node(
                            View::StrSwitch {
                                scrutinee: c[0],
                                actions: &c[1..],
                                header,
                            },
                            aux,
                            weight,
                        ),
                        View::Exit { label, .. } => {
                            let label = scratch.labels.get(&label).map_or(label, |copied| copied.0);
                            e.node(View::Exit { label, args: c }, aux, weight)
                        }
                        View::Catch { header, .. } => {
                            let old = *e.bir().catch(header);
                            let params = VarSpan {
                                start: old
                                    .params
                                    .iter()
                                    .next()
                                    .map_or(0, |v| renamed(scratch, v).0),
                                len: old.params.len,
                            };
                            let header = scratch.labels[&old.label].1;
                            e.set_catch_params(header, params);
                            e.node(
                                View::Catch {
                                    body: c[0],
                                    handler: c[1],
                                    header,
                                },
                                aux,
                                weight,
                            )
                        }
                        View::Try { exception, .. } => e.node(
                            View::Try {
                                body: c[0],
                                exception: renamed(scratch, exception),
                                handler: c[1],
                            },
                            aux,
                            weight,
                        ),
                        View::TryFinally { .. } => e.node(
                            View::TryFinally {
                                body: c[0],
                                finaliser: c[1],
                            },
                            aux,
                            weight,
                        ),
                        View::If { .. } => e.node(
                            View::If {
                                condition: c[0],
                                then_: c[1],
                                else_: c[2],
                            },
                            aux,
                            weight,
                        ),
                        View::Seq { .. } => e.node(
                            View::Seq {
                                first: c[0],
                                second: c[1],
                            },
                            aux,
                            weight,
                        ),
                        View::While { .. } => e.node(
                            View::While {
                                condition: c[0],
                                body: c[1],
                            },
                            aux,
                            weight,
                        ),
                        // After `Again` the values are the end, the body, then
                        // the start expression rewritten twice.
                        View::For { var, .. } => e.node(
                            View::For {
                                var: renamed(scratch, var),
                                parts: &[c[2], c[0], c[1]],
                            },
                            aux,
                            weight,
                        ),
                        View::ForOf { var, .. } => e.node(
                            View::ForOf {
                                var: renamed(scratch, var),
                                iterable: c[0],
                                body: c[1],
                            },
                            aux,
                            weight,
                        ),
                        View::ForAwaitOf { var, .. } => e.node(
                            View::ForAwaitOf {
                                var: renamed(scratch, var),
                                iterable: c[0],
                                body: c[1],
                            },
                            aux,
                            weight,
                        ),
                        // lam_beta_reduce.rs:632-635: the target is not renamed.
                        View::Assign { var, .. } => {
                            e.node(View::Assign { var, value: c[0] }, aux, weight)
                        }
                        _ => unreachable!("only the nodes entered are built"),
                    };
                    e.copy_cold(n, built);
                    if SMART.intersects(OpMask::of(e.bir().node(built).op())) {
                        e.normalise(built);
                    }
                    values.truncate(start);
                    values.push(built);
                }
            }
        }
        Ok(values.pop().expect("copied root"))
    })();
    work.clear();
    values.clear();
    scratch.copy_work = work;
    scratch.copy_values = values;
    result
}

/// `Lam_beta_reduce.propagate_beta_reduce` and `..._with_map`
/// (lam_beta_reduce.rs:386-466, lam_beta_reduce.ml:47-201). `args` are
/// detached from the application and are consumed; `body` (with `params`) is
/// read, not edited. `bound` is called for each parameter that stays bound,
/// with its fresh variable and its value, before the binding is refined
/// (`register_bound_param_kind`). Returns the detached reduced term.
#[allow(clippy::too_many_arguments)]
pub(crate) fn reduce(
    e: &mut Engine<'_>,
    scratch: &mut Scratch,
    params: VarSpan,
    body: NodeId,
    args: &[NodeId],
    stats: Option<&[ParamStats]>,
    weight: u32,
    bound: &mut dyn FnMut(&Engine<'_>, VarId, NodeId),
) -> Result<NodeId, Unsupported> {
    if let Some(result) = simple(e, scratch, params, body, args, weight) {
        *e.stats.rules.entry("beta-simple").or_default() += 1;
        return Ok(result);
    }
    *e.stats.rules.entry("beta-copy").or_default() += 1;
    // `effects_after` (lam_beta_reduce.rs:361-369).
    let mut effects_after = std::mem::take(&mut scratch.effects_after);
    let mut rest = std::mem::take(&mut scratch.rest);
    let mut spare = std::mem::take(&mut scratch.spare);
    let mut moved = std::mem::take(&mut scratch.moved);
    effects_after.resize(args.len(), false);
    let result = (|| {
        let mut effects = false;
        for (i, &arg) in args.iter().enumerate().rev() {
            effects_after[i] = effects;
            effects = effects || !pure_with_work(e, arg, &mut scratch.simple.purity);
        }
        for ((param, &arg), &after) in params.iter().zip(args).zip(&effects_after) {
            let op = e.bir().node(arg).op();
            match e.bir().view(arg) {
                View::Const { value } => {
                    scratch.set(param, Sub::Const(value));
                    spare.push(arg);
                }
                View::Var { var } if can_move(e, scratch, after, param, body, arg) => {
                    scratch.set(param, Sub::Var(var));
                    spare.push(arg);
                }
                _ => {
                    if op != Op::Global
                        && let Some(stats) = stats
                        && op != Op::Var
                        && pure_with_work(e, arg, &mut scratch.simple.purity)
                        && stats[param_index(params, param).expect("parameter")]
                            .top_and_used_zero_or_one()
                        && can_move(e, scratch, after, param, body, arg)
                    {
                        scratch.set(param, Sub::Node(arg));
                        moved.push((param, arg));
                        continue;
                    }
                    let fresh = e.rename_var(param);
                    // `is_boxed_optional_binding` (lam_beta_reduce.rs:468-473).
                    let boxed = matches!(e.bir().view(arg), View::Prim { primitive, .. }
                    if matches!(e.bir().primitive(primitive).primitive,
                        Primitive::PnullToOpt | Primitive::PnullUndefinedToOpt));
                    // A module without statistics takes the same road as any
                    // other argument (lam_beta_reduce.rs:411-416 and 417-446).
                    let binding = if boxed && (op != Op::Global) {
                        let primitive = e.intern_prim(Primitive::Pidentity, LamLoc::NONE);
                        let wrapped = e.node(
                            View::Prim {
                                args: &[arg],
                                primitive,
                            },
                            0,
                            weight,
                        );
                        e.normalise(wrapped);
                        wrapped
                    } else {
                        arg
                    };
                    rest.push((fresh, binding));
                    scratch.set(
                        param,
                        if boxed {
                            Sub::Identity(fresh)
                        } else {
                            Sub::Var(fresh)
                        },
                    );
                }
            }
        }
        let copied = copy(e, scratch, body, weight);
        for (param, arg) in moved.drain(..) {
            if scratch.get(param) == Sub::Node(arg) {
                spare.push(arg);
            }
        }
        scratch.reset();
        let mut result = copied?;
        for arg in spare.drain(..) {
            e.release(arg);
        }
        // The first argument's binding is outermost.
        for (param, value) in rest.drain(..).rev() {
            bound(e, param, value);
            result = e.node(
                View::Let {
                    var: param,
                    value: Some(value),
                    body: result,
                },
                0,
                weight,
            );
            refine(e, result);
        }
        Ok(result)
    })();
    effects_after.clear();
    rest.clear();
    spare.clear();
    moved.clear();
    scratch.effects_after = effects_after;
    scratch.rest = rest;
    scratch.spare = spare;
    scratch.moved = moved;
    result
}

/// The module and field of `Pfield(_, Fld_module name) [Lglobal_module id]`
/// (`module_field_apply_target`, lam_pass_remove_alias.rs:89-98).
pub(crate) fn module_field(b: &Bir, n: NodeId) -> Option<(ImportId, crate::name::Name)> {
    let View::Prim {
        args: [module],
        primitive,
    } = b.view(n)
    else {
        return None;
    };
    let Primitive::Pfield(_, FieldDbgInfo::Module { name }) = &b.primitive(primitive).primitive
    else {
        return None;
    };
    match b.view(*module) {
        View::Global { module } => Some((module, *name)),
        _ => None,
    }
}

#[cfg(test)]
pub(crate) mod testing {
    //! Bodies and arguments for the reduction and inlining tests.
    use crate::bir::engine::testing::{call, id, prim};
    use crate::ident::Ident;
    use crate::lambda::LamLoc;
    use crate::lambda::arena::{Lam, LamArena};
    use crate::lambda::lam_compat::{FieldDbgInfo, LetKind};
    use crate::lambda::lam_constant::Constant as C;
    use crate::lambda::lam_primitive::{Mutable, Primitive};
    use crate::lambda::lam_tag_info::TagInfo;
    use crate::lambda::{ApInfo, ApplyStatus, FunctionAttribute};
    use crate::name::Name;

    pub(crate) fn int(a: &mut LamArena, i: i32) -> Lam {
        a.const_(C::int(i))
    }
    pub(crate) fn app(a: &mut LamArena, f: Lam, args: &[Lam]) -> Lam {
        a.apply_raw(
            f,
            args,
            ApInfo {
                loc: LamLoc::NONE,
                status: ApplyStatus::Uncurry,
            },
        )
    }
    pub(crate) fn fun_attr(
        a: &mut LamArena,
        params: &[Ident],
        body: Lam,
        attr: FunctionAttribute,
    ) -> Lam {
        a.function_(params.len() as i32, params, body, attr, LamLoc::NONE)
    }
    pub(crate) fn fun(a: &mut LamArena, params: &[Ident], body: Lam) -> Lam {
        fun_attr(a, params, body, FunctionAttribute::default())
    }
    pub(crate) fn tuple(a: &mut LamArena, args: &[Lam]) -> Lam {
        prim(
            a,
            Primitive::Pmakeblock(TagInfo::Tuple, Mutable::Immutable),
            args,
        )
    }
    pub(crate) fn field(a: &mut LamArena, i: i32, of: Lam) -> Lam {
        prim(a, Primitive::Pfield(i, FieldDbgInfo::Tuple), &[of])
    }
    pub(crate) fn module_field(a: &mut LamArena, name: &str, of: Lam) -> Lam {
        let info = FieldDbgInfo::Module {
            name: Name::new(name),
        };
        prim(a, Primitive::Pfield(0, info), &[of])
    }
    pub(crate) fn global(a: &mut LamArena, name: &str) -> Lam {
        a.global_module(Ident::create_persistent(name))
    }
    /// `r.contents`: no side effects, but reads state that may change.
    pub(crate) fn read(a: &mut LamArena, r: Ident) -> Lam {
        let info = FieldDbgInfo::Record {
            name: Name::new("contents"),
        };
        let r = a.var(r);
        prim(a, Primitive::Pfield(0, info), &[r])
    }
    pub(crate) fn bodies(a: &mut LamArena, which: usize, x: Ident, y: Ident) -> Lam {
        let (vx, vy) = (a.var(x), a.var(y));
        let one = int(a, 1);
        match which {
            // One primitive on the parameters: `simple_beta_reduce`.
            0 => prim(a, Primitive::Psubint, &[vy, vx]),
            1 => prim(a, Primitive::Psubint, &[vx, vy]),
            2 => prim(a, Primitive::Psequand, &[vx, vy]),
            // One call of a variable.
            3 => {
                let f = a.var(id("callee", 50));
                app(a, f, &[vy, one])
            }
            // A binder: the copy renames it.
            4 => {
                let t = id("t", 51);
                let sum = prim(a, Primitive::Paddint, &[vx, vy]);
                let vt = a.var(t);
                let vt2 = a.var(t);
                let twice = prim(a, Primitive::Pmulint, &[vt, vt2]);
                a.let_(LetKind::Strict, t, sum, twice)
            }
            // A parameter read after an effect.
            5 => {
                let effect = call(a, "effect", 52);
                let sum = prim(a, Primitive::Paddint, &[vx, vy]);
                a.seq_raw(effect, sum)
            }
            // A closure over a parameter.
            6 => {
                let z = id("z", 53);
                let vz = a.var(z);
                let sum = prim(a, Primitive::Paddint, &[vx, vz]);
                let f = fun(a, &[z], sum);
                a.seq_raw(vy, f)
            }
            // A conditional on a parameter with a large branch.
            7 => {
                let mut big = vy;
                for _ in 0..12 {
                    let c = int(a, 2);
                    big = prim(a, Primitive::Paddint, &[big, c]);
                }
                a.if_raw(vx, one, big)
            }
            // The parameter is a block that is read.
            8 => {
                let first = field(a, 0, vx);
                prim(a, Primitive::Paddint, &[first, vy])
            }
            // A field of a parameter bound to a module.
            9 => {
                let got = module_field(a, "f", vx);
                app(a, got, &[vy])
            }
            // Unwrapping a parameter.
            10 => {
                let got = prim(a, Primitive::PvalFromOption, &[vx]);
                prim(a, Primitive::Paddint, &[got, vy])
            }
            // More than nine nodes: too big unless asked for.
            _ => {
                let mut big = vx;
                for _ in 0..12 {
                    big = prim(a, Primitive::Paddint, &[big, vy]);
                    let _ = one;
                }
                big
            }
        }
    }
    pub(crate) const BODIES: usize = 12;

    pub(crate) fn arguments(a: &mut LamArena, which: usize) -> Lam {
        match which {
            0 => a.var(id("free", 60)),
            1 => int(a, 0),
            2 => call(a, "effect", 61),
            3 => read(a, id("r", 62)),
            4 => {
                let v = a.var(id("free", 60));
                tuple(a, &[v])
            }
            5 => global(a, "M"),
            6 => {
                let v = a.var(id("free", 60));
                prim(a, Primitive::Psome, &[v])
            }
            7 => {
                let v = a.var(id("free", 60));
                prim(a, Primitive::PnullToOpt, &[v])
            }
            8 => a.const_(C::JsTrue),
            _ => {
                let v = a.var(id("free", 60));
                let w = a.var(id("free", 60));
                prim(a, Primitive::Paddint, &[v, w])
            }
        }
    }
    pub(crate) const ARGUMENTS: usize = 10;

    /// A body with one binder of each kind.
    pub(crate) fn every_binder(a: &mut LamArena, x: Ident) -> Lam {
        let vx = a.var(x);
        // A static handler with a parameter, raised from its body.
        let raise = a.static_raise(7, &[vx]);
        let h = id("h", 10);
        let vh = a.var(h);
        let caught = a.static_catch(raise, 7, &[h], vh);
        // An exception handler.
        let exn = id("exn", 11);
        let vexn = a.var(exn);
        let effect = call(a, "effect", 12);
        let tried = a.try_(effect, exn, vexn);
        // A loop whose start expression binds a variable.
        let (i, t) = (id("i", 13), id("t", 14));
        let one = int(a, 1);
        let vt = a.var(t);
        let start = a.let_(LetKind::Strict, t, one, vt);
        let ten = int(a, 10);
        let vi = a.var(i);
        let looped = a.for_(i, start, ten, crate::lambda::DirectionFlag::Upto, vi);
        // A recursive group and a function.
        let (r, p) = (id("r", 15), id("p", 16));
        let vr = a.var(r);
        let vp = a.var(p);
        let rec_body = app(a, vr, &[vp]);
        let rec_fun = fun(a, &[p], rec_body);
        let vr2 = a.var(r);
        let group = a.letrec(&[(r, rec_fun)], vr2);
        let item = id("item", 17);
        let vitem = a.var(item);
        let each = a.for_of(item, group, vitem);
        let mut body = each;
        for part in [looped, tried, caught] {
            body = a.seq_raw(part, body);
        }
        body
    }
}

#[cfg(test)]
mod tests {
    use super::testing::*;
    use super::*;
    use crate::bir::bridge::{export_lambda, import_lambda};
    use crate::bir::engine::testing::{call, id, prim};
    use crate::ident::Ident;
    use crate::lambda::arena::{Lam, LamArena, Node};
    use crate::lambda::lam_compat::LetKind;

    fn dump(a: &LamArena, root: Lam) -> String {
        let mut out = Vec::new();
        crate::lambda::sexp_lambda::print_lambda(&a.export(root), &mut out).unwrap();
        String::from_utf8(out).unwrap()
    }

    /// `(fun params -> body)(args)` given to `propagate_beta_reduce`, or to
    /// `propagate_beta_reduce_with_map` with the statistics of
    /// `is_closed_with_map`, and to [`reduce`]: the dumps and every
    /// identifier (name, stamp, flags) are compared. Returns the fresh
    /// variables.
    fn compare(a: LamArena, applied: Lam, with_stats: bool) -> usize {
        let tree = a.export(applied);
        let mut a = LamArena::new();
        let root = a.import(&tree);
        let mut imported = import_lambda(&a, root).unwrap();
        let stamp = a.ident_stamp_bound();
        let Node::Apply { func, args, .. } = a.node(root) else {
            panic!("an application")
        };
        let Node::Function { body, info } = a.node(func) else {
            panic!("an applied function")
        };
        let params: Vec<Ident> = a.params(info).to_vec();
        let arguments = a.list_vec(args);
        let generator = crate::context::IdGenerator::new();
        generator.set_current_stamp(stamp);
        let mut table = Default::default();
        let assignable = Default::default();
        let env = crate::lambda::lam_beta_reduce::BetaReduceEnv {
            ident_tbl: &mut table,
            id_gen: &generator,
            assignable: &assignable,
        };
        let expected = if with_stats {
            let (_, map) = crate::lambda::lam_closure::is_closed_with_map(
                &a,
                &Default::default(),
                &params,
                body,
            );
            crate::lambda::lam_beta_reduce::propagate_beta_reduce_with_map(
                &mut a, env, &map, &params, body, &arguments,
            )
        } else {
            crate::lambda::lam_beta_reduce::propagate_beta_reduce(
                &mut a, env, &params, body, &arguments,
            )
        };
        let node = imported.root;
        let renames = {
            let mut e = Engine::new(&mut imported.arena);
            e.set_current_stamp(stamp as u32);
            let View::Apply { callee, args, .. } = e.bir().view(node) else {
                unreachable!()
            };
            let args: SmallVec<[NodeId; 8]> = args.into();
            let View::Fun { body, header } = e.bir().view(callee) else {
                unreachable!()
            };
            let params = e.bir().function(header).params;
            let mut scratch = Scratch::default();
            let stats = closed_with_stats(&e, &mut scratch, params, body).1;
            let weight = e.weight(node);
            for &arg in &args {
                e.detach(arg);
            }
            let reduced = reduce(
                &mut e,
                &mut scratch,
                params,
                body,
                &args,
                with_stats.then_some(&stats[..]),
                weight,
                &mut |_, _, _| {},
            )
            .unwrap();
            e.replace(node, reduced);
            for &(fresh, source) in &e.stats.labels {
                assert_ne!(fresh, source);
            }
            (e.stats.renames.clone(), e.stats.labels.clone())
        };
        for &(var, source) in &renames.0 {
            imported.register_rename(var, source).unwrap();
        }
        for &(fresh, source) in &renames.1 {
            imported.register_label(fresh, source);
        }
        imported.arena.validate(Some(imported.root)).unwrap();
        let actual = export_lambda(&imported).unwrap();
        assert_eq!(dump(&actual.arena, actual.root), dump(&a, expected));
        assert_eq!(
            crate::bir::l::flatten::identities(&actual.arena, actual.root),
            crate::bir::l::flatten::identities(&a, expected)
        );
        renames.0.len()
    }

    /// Every rule of `propagate` and `simple_beta_reduce`: each body shape
    /// against each pair of argument shapes, with and without statistics.
    #[test]
    fn a_reduction_agrees_for_every_body_and_argument() {
        for with_stats in [false, true] {
            for body in 0..BODIES {
                for first in 0..ARGUMENTS {
                    for second in 0..ARGUMENTS {
                        let mut a = LamArena::new();
                        let (x, y) = (id("x", 2), id("y", 3));
                        let b = bodies(&mut a, body, x, y);
                        let function = fun(&mut a, &[x, y], b);
                        let a1 = arguments(&mut a, first);
                        let a2 = arguments(&mut a, second);
                        let applied = app(&mut a, function, &[a1, a2]);
                        compare(a, applied, with_stats);
                    }
                }
            }
        }
    }

    /// Fresh identifiers and their order: every binder of the copied body
    /// (function, `let`, `let rec`, handler, exception, the three loops) is
    /// renamed in the order `Lam_bounded_vars.rewrite` does it, a `for`
    /// loop's start expression twice; the parameter bound to an argument
    /// with side effects comes first. The comparison checks each stamp.
    #[test]
    fn a_copied_body_renames_every_binder_in_the_legacy_order() {
        let mut a = LamArena::new();
        let x = id("x", 2);
        let body = every_binder(&mut a, x);
        let function = fun(&mut a, &[x], body);
        let argument = call(&mut a, "argument", 20);
        let applied = app(&mut a, function, &[argument]);
        // x, h, exn, i, t (twice), r, p, item.
        assert_eq!(compare(a, applied, false), 9);
    }

    /// The refinements of a parameter that stays bound (`refine_let`,
    /// lam_util.rs:66-121): the body is the parameter, a primitive on it, a
    /// call on it.
    #[test]
    fn a_bound_parameter_is_refined() {
        for shape in 0..4 {
            let mut a = LamArena::new();
            let (x, t) = (id("x", 2), id("t", 3));
            let vx = a.var(x);
            let body = match shape {
                0 => {
                    let vt = a.var(t);
                    a.let_(LetKind::Strict, t, vx, vt)
                }
                1 => {
                    let one = int(&mut a, 1);
                    let vt = a.var(t);
                    let negated = prim(&mut a, Primitive::Pnegint, &[vx]);
                    let bound = a.let_(LetKind::Strict, t, one, negated);
                    a.seq_raw(vt, bound)
                }
                2 => {
                    let f = a.var(id("f", 9));
                    let called = app(&mut a, f, &[vx]);
                    let vt = a.var(t);
                    let one = int(&mut a, 1);
                    let bound = a.let_(LetKind::Strict, t, one, vt);
                    a.seq_raw(bound, called)
                }
                _ => {
                    let w = a.while_(vx, vx);
                    let vx = a.var(x);
                    a.seq_raw(w, vx)
                }
            };
            let function = fun(&mut a, &[x], body);
            let argument = call(&mut a, "argument", 20);
            let applied = app(&mut a, function, &[argument]);
            compare(a, applied, shape % 2 == 0);
        }
    }
}

#[cfg(test)]
mod storage_tests {
    use super::*;
    #[test]
    fn rejected_wide_simple_plans_and_motion_walks_reuse_storage() {
        assert_eq!(std::mem::size_of::<CopyWork>(), 12);
        let mut b = Bir::default();
        let params = b.new_vars(&[crate::name::Name::new("p"); 16]);
        let operands: Vec<_> = (0..16).map(|i| b.new_node(View::Var { var: VarId(params.start + if i == 15 { 0 } else { i }) }, 0)).collect();
        let primitive = b.intern_prim(PrimPayload { primitive: Primitive::Pmakearray, loc: LamLoc::NONE });
        let body = b.new_node(View::Prim { args: &operands, primitive }, 0);
        let value = b.intern_const(Constant::Int(1));
        let args: Vec<_> = (0..16).map(|_| b.new_node(View::Const { value }, 0)).collect();
        let mut e = Engine::new(&mut b); let mut scratch = Scratch::default();
        let run = |e: &mut Engine<'_>, scratch: &mut Scratch| {
            assert!(simple(e, scratch, params, body, &args, 1).is_none());
            assert!(delay_safe(e, body, &mut scratch.simple.delay, &mut scratch.simple.purity));
            assert!(read_before_effects(e, scratch, VarId(params.start), body));
        };
        run(&mut e, &mut scratch);
        let capacities = |s: &Scratch| [s.simple.motions.capacity(), s.simple.used.capacity(), s.simple.evaluated.capacity(),
            s.simple.operands.capacity(), s.simple.built.capacity(), s.simple.order.capacity(), s.simple.delay.capacity(), s.simple.purity.capacity(),
            s.read_work.capacity(), s.read_saved.capacity()];
        let before = capacities(&scratch);
        let allocations = allocation_counter::measure(|| { for _ in 0..10_000 { run(&mut e, &mut scratch); } });
        assert_eq!(allocations.count_total, 0, "{allocations:?}"); assert_eq!(capacities(&scratch), before);
        assert!(scratch.simple.used.is_empty() && scratch.simple.operands.is_empty() && scratch.simple.delay.is_empty()
            && scratch.read_work.is_empty() && scratch.read_saved.is_empty());
    }
}
