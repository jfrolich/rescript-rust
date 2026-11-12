//! Continuations for the level-L to level-J lowering (BACKEND_LOWERING §1).
//! Context references are indices, never references into growing state pools.
mod args;
mod call;
mod cond;
mod exit;
mod expr;
mod konst;
mod prim;
mod record;
mod import;
mod jsx;
mod prim_cmp;
mod prim_block;
mod switch;
mod variant;
mod untagged;
mod location;
#[cfg(test)]
mod oracle_tests;
pub mod out;
mod unit;
pub(crate) mod scope;

use super::bridge::Unsupported;
use super::{Bir, NodeId, VarId, View};
use crate::ident::Ident;
use crate::lambda::lam_compat::LetKind;
pub use out::{Finished, Free, FreeId, FreePool, Out, Probed, Span, StatementStack};

/// K7: C:3989 compile_recursive_function_expr, function-local return record.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LoopRef(pub u32);
/// K12: C:6092 with_static_jump_handler, visible jump-stack height.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct JumpTop(pub u32);
/// K11: C:2044 push_loop, visible loop-frame height.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct LoopTop(pub u32);

/// K1–K7: the continuation, independent of the traversal machinery.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Cont {
    /// Evaluate for effects, optionally returning.
    Effect(Tail),
    /// Produce a value, optionally recognizing tail calls.
    Value(Tail),
    /// Bind the result with its declaration kind.
    Declare(LetKind, VarId),
    /// Assign the result to an existing variable.
    Assign(VarId),
}
/// K1/K6: C:1529 compile_expr and C:3067 compile_return_output.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Tail {
    /// Not in tail position.
    No,
    /// Tail position with return policy.
    Return(Ret),
}
/// K7/K8/K14: C:3543 with_try_body_context and C:3091 compile_staticcatch_in_return.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ret {
    /// Tail position protected by an exception handler.
    InTry,
    /// Ordinary function return and optional self-call loop.
    Named {
        /// Enclosing function loop record, if any.
        loop_: Option<LoopRef>,
        /// Whether a static catch encloses this return.
        in_catch: bool,
    },
}
/// K1–K14: context passed by value, including function and control boundaries.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Cx {
    /// Requested output continuation.
    pub cont: Cont,
    /// Visible jump-stack height.
    pub jumps: JumpTop,
    /// Switches since the nearest loop.
    pub switch_depth: u32,
    /// Visible loop-frame height.
    pub loops: LoopTop,
    /// Enclosing function returns unit.
    pub return_unit: bool,
    /// A conditional reads whether this output is free (1.5): a leaf stays
    /// deferred, also in the direct mode of invariant P1.
    pub probing: bool,
}
impl Cx {
    /// K10: C:1997 with_function_scope; no control state crosses a function.
    pub fn new(cont: Cont) -> Self {
        Self {
            cont,
            jumps: JumpTop(0),
            switch_depth: 0,
            loops: LoopTop(0),
            return_unit: false,
            probing: false,
        }
    }
    /// K1: C:1529 compile_expr (V).
    pub fn value() -> Self {
        Self::new(Cont::Value(Tail::No))
    }
    /// K2: C:4603 compile_effect_output (E, value retained).
    pub fn effect() -> Self {
        Self::new(Cont::Effect(Tail::No))
    }
    /// K4: C:2411 compile_let_binding_output (D).
    pub fn declare(kind: LetKind, var: VarId) -> Self {
        Self::new(Cont::Declare(kind, var))
    }
    /// K5: C:5331 compile_assign_to_target_output (A).
    pub fn assign(var: VarId) -> Self {
        Self::new(Cont::Assign(var))
    }
    /// K6: C:3067 compile_return_output (R).
    pub fn returning() -> Self {
        Self::new(Cont::Effect(Tail::Return(Ret::Named {
            loop_: None,
            in_catch: false,
        })))
    }
}

/// K1/K2/K6: deferred, already-lowered operands, not a second L tree.
/// The caller has lowered expression operands exactly once before probing.
pub enum ProbeInput {
    /// An already-lowered expression or statement result.
    Output(Out),
    /// A retained effect value followed by a probed child.
    Seq {
        /// Already-lowered effect value.
        first: NodeId,
        /// Result of probing the tail.
        second: Probed,
    },
    /// An already-lowered condition and its probed branches.
    Cond {
        /// Already-lowered test value.
        test: NodeId,
        /// Probed true branch.
        then_: Probed,
        /// Probed false branch.
        else_: Probed,
    },
}

/// K2/K6: C:4715 append_effect_output and C:5144 compile_if_return_output.
/// Construction policy is supplied by J constructors, not by the output algebra.
pub trait Realizer {
    /// K1/K6: C:6658 return_compiled; convert one lowered value.
    fn leaf(&mut self, cx: Cx, value: NodeId) -> Out;
    /// K2: C:4715 append_effect_output; join an effect and a tail's value.
    fn seq(&mut self, cx: Cx, first: NodeId, second: Out) -> Out;
    /// O:339 push_effect_expression; an effect as statements before its tail.
    fn effect(&mut self, first: NodeId) -> Span;
    /// K6: C:5144 compile_if_return_output; combine lowered branches.
    fn cond(&mut self, cx: Cx, test: NodeId, then_: Out, else_: Out) -> Out;
}

/// One source visit either completes an output or schedules child occurrences.
pub enum ProbePlan<R> {
    /// This source node has already been lowered.
    Ready(Probed),
    /// Resume after the children, without re-reading the source node.
    Children(R),
}

/// Source dispatch for the single-pass probe. Resume records contain decoded
/// operands, not source trees. The output algebra does not prescribe constructs.
pub trait ProbeRules {
    /// Decoded operands required after visiting children.
    type Resume;
    /// K1: C:1529 compile_expr; inspect and lower a source node exactly once.
    fn enter(
        &mut self,
        cx: Cx,
        node: NodeId,
    ) -> Result<ProbePlan<Self::Resume>, super::bridge::Unsupported>;
    /// K1/K2: C:1529 compile_expr / C:4603 compile_effect_output; child order.
    fn children(&self, cx: Cx, resume: &Self::Resume, into: &mut Vec<(Cx, NodeId)>);
    /// Resolve a child continuation after preceding siblings have completed.
    /// O(1); string-switch V allocates its result after lowering the scrutinee.
    fn child_context(&self, cx: Cx, _resume: &Self::Resume, _index: usize) -> Cx { cx }
    /// K4/K2: C:2411 compile_let_binding_output / C:4603 compile_effect_output.
    /// Consume a child's result before entering its next sibling when required.
    fn child(&mut self, _cx: Cx, _resume: &Self::Resume, _index: usize, output: Probed) -> Probed {
        output
    }
    /// K0/K2: C:119 append / C:4715 append_effect_output; combine child outputs.
    fn finish(
        &mut self,
        cx: Cx,
        resume: Self::Resume,
        children: impl Iterator<Item = Probed>,
    ) -> Result<Probed, super::bridge::Unsupported>;
}

/// Explicit source traversal, separate from realization of deferred J operands.
#[derive(Default)]
pub struct SourceProbe {
    /// Source occurrences offered to dispatch (one per incoming tree edge).
    pub steps: usize,
}
impl SourceProbe {
    /// K1/K6: C:1529 compile_expr / C:5144 compile_if_return_output.
    /// A source node is entered once. Finish frames receive the saved operands
    /// and child outputs, never a request to compile the same child again.
    pub fn probe(
        &mut self,
        rules: &mut impl ProbeRules,
        cx: Cx,
        node: NodeId,
    ) -> Result<Probed, super::bridge::Unsupported> {
        enum Work<R> {
            Enter(Cx, NodeId),
            EnterChild(Cx, NodeId, usize, usize),
            Finish(Cx, R, usize),
            Child(Cx, usize, usize),
        }
        let mut work = vec![Work::Enter(cx, node)];
        let mut values = Vec::new();
        let mut children = Vec::new();
        while let Some(task) = work.pop() {
            let task = match task {
                Work::EnterChild(cx, node, parent, index) => {
                    let Work::Finish(_, resume, _) = &work[parent] else { unreachable!("parent resume") };
                    Work::Enter(rules.child_context(cx, resume, index), node)
                }
                task => task,
            };
            match task {
                Work::EnterChild(..) => unreachable!("resolved child context"),
                Work::Enter(cx, node) => {
                    self.steps += 1;
                    match rules.enter(cx, node)? {
                        ProbePlan::Ready(value) => values.push(value),
                        ProbePlan::Children(resume) => {
                            rules.children(cx, &resume, &mut children);
                            let parent = work.len();
                            work.push(Work::Finish(cx, resume, children.len()));
                            for (index, (cx, node)) in children.drain(..).enumerate().rev() {
                                work.push(Work::Child(cx, parent, index));
                                work.push(Work::EnterChild(cx, node, parent, index));
                            }
                        }
                    }
                }
                Work::Child(cx, parent, index) => {
                    let Work::Finish(_, resume, _) = &work[parent] else {
                        unreachable!("parent resume frame")
                    };
                    let child = values.pop().expect("completed source child");
                    let cx = rules.child_context(cx, resume, index);
                    values.push(rules.child(cx, resume, index, child));
                }
                Work::Finish(cx, resume, count) => {
                    let start = values
                        .len()
                        .checked_sub(count)
                        .expect("source probe children");
                    let value = rules.finish(cx, resume, values.drain(start..))?;
                    values.push(value);
                }
            }
        }
        assert_eq!(values.len(), 1);
        Ok(values.pop().expect("source probe output"))
    }
}

/// N1: C:663 compile_deps_program_in_arena. The final statement is a plain
/// SExp carrying Out::value for the migration exporter, not an emitted effect.
#[derive(Clone, Copy, Default, serde::Serialize)]
pub(crate) struct SwitchStats {
    pub source_visits: usize,
    pub fingerprint_visits: usize,
    pub comparisons: usize,
    pub compared_pairs: usize,
    pub location_visits: usize,
}

pub(crate) struct Lowered {
    pub program: super::bridge_j::Imported,
    pub finished: Finished,
    pub dynamic_imports: Vec<crate::js_ir::ModuleId>,
    pub switch_stats: SwitchStats,
}

/// N1: C:663 compile_deps_program_in_arena; one fresh J arena for this migration cut.
#[cfg(test)]
pub(crate) fn lower(
    input: super::bridge::Imported,
    locations: Option<&crate::lambda::LamLocTable>,
    direct: bool,
) -> Result<Lowered, Unsupported> {
    unit::lower(input, locations, direct, None, false, true)
}

/// H2: C:1266 compile_external_field_apply; summaries are read-only inputs.
pub(crate) fn lower_with_resolver(
    input: super::bridge::Imported,
    locations: Option<&crate::lambda::LamLocTable>,
    direct: bool,
    resolver: Option<&crate::js_ir::ModulePathResolver>,
    cross_module_inline: bool,
    check_div_by_zero: bool,
) -> Result<Lowered, Unsupported> {
    unit::lower(input, locations, direct, resolver, cross_module_inline, check_div_by_zero)
}

/// One immutable summary acquisition per imported module; indexed by ImportId.
enum ModuleConstants {
    Unread,
    Missing,
    Present(std::sync::Arc<ahash::AHashMap<String, crate::cmi::persistent_env::CmjExportConstant>>),
}

struct State {
    switches: Vec<Option<switch::Plan>>,
    variants: Vec<Option<variant::Plan>>,
    untagged: Vec<Option<untagged::Plan>>,
    switch_facts: Vec<switch::Facts>,
    switch_work: Vec<(NodeId, bool)>,
    switch_pairs: Vec<(NodeId, NodeId)>,
    switch_primitive_hashes: Vec<u64>,
    switch_constant_hashes: Vec<u64>,
    switch_comparisons: usize,
    switch_compared: usize,
    switch_visits: usize,
    source: Bir,
    arena: Bir,
    idents: Vec<Ident>,
    statements: StatementStack,
    free: FreePool,
    source_steps: usize,
    invalid_module_paths: Vec<bool>,
    awaited_units: Vec<bool>,
    dynamic_imports: Vec<crate::js_ir::ModuleId>,
    module_constants: Vec<ModuleConstants>,
    direct: bool,
    located_functions: Vec<bool>,
    next_order: u32,
    resolver: Option<crate::js_ir::ModulePathResolver>,
    cross_module_inline: bool,
    check_div_by_zero: bool,
    locations: Option<crate::lambda::LamLocTable>,
    switch_locations: Vec<location::Fact>,
    location_work: Vec<(NodeId,bool)>,
    location_steps: usize,
    sequence_steps: usize,
    primitive_steps: usize,
    /// Let/Seq nodes read by row R5 step 0 of section 3.6.
    spine_steps: usize,
    /// Reused by the J rules that push onto a vector.
    scratch: Vec<NodeId>,
    /// 4.1: the jump table, indexed by catch header; sized at the first catch.
    jumps: Vec<exit::Jump>,
    /// The handlers of the catches being lowered, a stack of flattened tables.
    catch_table: Vec<(NodeId, crate::bir::CatchId)>,
    catches: Vec<Option<exit::Plan>>,
    catch_work: Vec<NodeId>,
    /// `HAS_EXIT` reads that decided a flattening or a form.
    catch_flag_reads: usize,
    /// Handler nodes read to find the label of an exit (4.1 step 1).
    catch_walk_steps: usize,
}
impl State {
    /// N1: C:481 new. Transfer cold pools, while source hot nodes/list operands
    /// remain readable. Variables retain source identities, never global stamps.
    fn new(mut input: super::bridge::Imported) -> Self {
        let mut arena = Bir::default();
        arena.begin_bulk();
        arena.pools = std::mem::take(&mut input.arena.pools);
        // The headers keep their labels and parameters; the exits they count
        // stay in the source. One write per catch of the unit.
        for header in &mut arena.pools.catches {
            header.uses = 0;
        }
        arena.func_owners.resize(arena.pools.funcs.len(), None);
        for i in 0..input.arena.vars.len() {
            let var = VarId(i as u32);
            let made = arena.new_var_id(input.arena.vars.name(var), input.arena.vars.order(var));
            assert_eq!(made, var);
            arena.vars.flags[i] = input.arena.vars.flags[i];
        }
        arena.js_scope = Some(scope::Scope::new(arena.vars.len()));
        arena.pools.j_modules = input
            .globals
            .iter()
            .map(|&id| crate::js_ir::ModuleId {
                id,
                kind: crate::js_ir::op::Kind::Ml,
                dynamic_import: false,
            })
            .collect();
        let next_order = (0..input.arena.vars.len())
            .map(|i| input.arena.vars.order(VarId(i as u32)))
            .max().unwrap_or(0).checked_add(1).expect("identifier order capacity");
        Self {
            switch_facts: vec![switch::Facts::default(); input.arena.nodes.len()],
            switches: Vec::new(), variants: Vec::new(), untagged: Vec::new(), switch_work: Vec::new(), switch_pairs: Vec::new(),
            switch_primitive_hashes: Vec::new(), switch_constant_hashes: Vec::new(),
            switch_comparisons: 0, switch_compared: 0, switch_visits: 0,
            invalid_module_paths: vec![false; input.arena.nodes.len()],
            awaited_units: vec![false; input.arena.vars.len()],
            dynamic_imports: Vec::new(),
            module_constants: (0..arena.pools.j_modules.len()).map(|_| ModuleConstants::Unread).collect(),
            source: input.arena,
            arena,
            idents: input.idents,
            statements: StatementStack::default(),
            free: FreePool::default(),
            source_steps: 0,
            direct: false,
            located_functions: Vec::new(),
            next_order,
            resolver: None,
            cross_module_inline: false,
            check_div_by_zero: true,
            locations: None,
            switch_locations: Vec::new(), location_work: Vec::new(), location_steps: 0,
            sequence_steps: 0,
            primitive_steps: 0,
            spine_steps: 0,
            scratch: Vec::new(),
            jumps: Vec::new(),
            catch_table: Vec::new(),
            catches: Vec::new(),
            catch_work: Vec::new(),
            catch_flag_reads: 0,
            catch_walk_steps: 0,
        }
    }
    /// K1: C:1529 compile_expr. Direct mode is the bounded P1 oracle: convert
    /// leaves immediately instead of allocating deferred expression records.
    fn probe_leaf(&mut self, cx: Cx, value: NodeId) -> Probed {
        if self.direct && !cx.probing {
            Probed::Out(self.leaf(cx, value))
        } else {
            Probed::Free(self.free.push(Free::Leaf(value)))
        }
    }
    /// H13: A:28 delay_safe; K1: C:1529 compile_expr. The supported literal,
    /// variable, module and function expressions are strictly pure by construction.
    /// Delay safety reads child flags or the variable's final ASSIGNED/JS_GLOBAL facts.
    fn pure_expression(&mut self, view: View<'_>, aux: u16) -> NodeId {
        super::j::pure_expression(&mut self.arena, view, aux)
    }
    /// K1: C:1529 compile_expr. SourceProbe owns the depth-independent traversal.
    fn probe(&mut self, cx: Cx, node: NodeId) -> Result<Probed, Unsupported> {
        let mut traversal = SourceProbe::default();
        let output = traversal.probe(self, cx, node);
        self.source_steps += traversal.steps;
        output
    }
    /// K2/K6: C:4715 append_effect_output / C:5144 compile_if_return_output.
    fn realize(&mut self, cx: Cx, probed: Probed) -> Out {
        let mut free = std::mem::take(&mut self.free);
        let out = free.realize(cx, probed, self);
        self.free = free;
        out
    }
    /// K0: append_output drops the tail of finished output. Release its J
    /// ownership as well as truncating its statement run. O(s + released nodes)
    /// for a discarded suffix; O(1) otherwise. No temporary statement vector.
    fn append_outputs(&mut self, first: Out, second: Out, value: Option<NodeId>) -> Out {
        if first.finished == Finished::True {
            for statement in self.statements.statements(second.stmts) { self.arena.release(statement); }
            if let Some(value) = second.value { self.arena.release(value); }
        }
        self.statements.append(first, second, value)
    }

    /// N1: C:663 compile_deps_program_in_arena. Export transports the last value
    /// in a plain sentinel SExp removed before export extraction and coercion.
    fn complete(mut self, cx: Cx, probed: Probed) -> Lowered {
        let out = self.realize(cx, probed);
        let value = out
            .value
            .unwrap_or_else(|| self.pure_expression(View::JUndefined, 0));
        let value = self.arena.new_node(View::SExp { value }, 0);
        self.statements.push(value);
        let run = self.statements.since(Span {
            start: out.stmts.start,
            len: 0,
        });
        let list = self.statements.take_list(&mut self.arena, run);
        let root = self.arena.block_from_list(list);
        self.arena.finish_bulk(root);
        Lowered {
            program: super::bridge_j::Imported::from_lowering(self.arena, root, self.idents),
            finished: out.finished,
            dynamic_imports: self.dynamic_imports,
            switch_stats: SwitchStats {
                source_visits: self.source_steps,
                fingerprint_visits: self.switch_visits,
                comparisons: self.switch_comparisons,
                compared_pairs: self.switch_compared,
                location_visits: self.location_steps,
            },
        }
    }
}

impl ProbeRules for State {
    type Resume = expr::Resume;
    /// K1/H12: C:1529 compile_expr and K:60 compile_constant.
    fn enter(&mut self, cx: Cx, node: NodeId) -> Result<ProbePlan<Self::Resume>, Unsupported> {
        let value = match self.source.view(node) {
            View::Var { var } => self.pure_expression(View::Var { var }, 0),
            View::Global { module } => self.pure_expression(
                View::JQualified {
                    module,
                    member: None,
                },
                0,
            ),
            View::Const { value } => self.constant(value),
            View::Apply { callee, args, info } => {
                // K7: C:4558 try_compile_self_tailcall_block. S3.6 owns the
                // loop record and matching callee; no such record exists yet.
                if matches!(cx.cont, Cont::Value(Tail::Return(Ret::Named { loop_: Some(_), .. }))
                    | Cont::Effect(Tail::Return(Ret::Named { loop_: Some(_), .. }))) {
                    return Err(Unsupported("let rec"));
                }
                let args = args.to_vec();
                let call = self.application(callee, &args, info)?;
                return Ok(ProbePlan::Children(expr::Resume::Call(call)));
            }
            View::Fun { body, header } => {
                return Ok(ProbePlan::Children(expr::Resume::Fun { body, header }));
            }
            View::Let { var, value, body } => {
                if let Some(value) = value { self.record_awaited_unit(var, value); }
                if !matches!(cx.cont, Cont::Declare(..)) && let Some(value) = value {
                    if let Some(record) = self.record_copy(var, value, body) {
                        return Ok(ProbePlan::Children(expr::Resume::Record(record)));
                    }
                }
                let kind = match self.source.node(node).aux() & 3 {
                    0 => LetKind::Strict,
                    1 => LetKind::Alias,
                    2 => LetKind::StrictOpt,
                    3 => LetKind::Variable,
                    _ => unreachable!("masked let kind"),
                };
                return Ok(ProbePlan::Children(expr::Resume::Let {
                    var,
                    kind,
                    value,
                    body,
                }));
            }
            View::Seq { first, second } => {
                return Ok(ProbePlan::Children(expr::Resume::Seq { first, second }));
            }
            View::LetRec { .. } => return Err(Unsupported("let rec")),
            View::Prim { primitive, args }
                if matches!(
                    self.arena.primitive(primitive).primitive,
                    crate::lambda::lam_primitive::Primitive::Psequand
                        | crate::lambda::lam_primitive::Primitive::Psequor
                ) =>
            {
                use crate::lambda::lam_primitive::Primitive;
                let kind = match self.arena.primitive(primitive).primitive {
                    Primitive::Psequand => cond::Kind::And,
                    _ => cond::Kind::Or,
                };
                let &[left, right] = args else {
                    unreachable!("a short circuit has two operands")
                };
                let conditional = self.conditional(cx, kind, left, right, right)?;
                return Ok(ProbePlan::Children(expr::Resume::If(conditional)));
            }
            View::Prim { primitive, .. } => {
                use crate::lambda::lam_primitive::Primitive;
                if matches!(self.arena.primitive(primitive).primitive,
                    Primitive::Pfield(_, crate::lambda::FieldDbgInfo::Module { name }) if name.as_str() == "make") {
                    if let Some(value) = self.flat_make_field(node) {
                        return Ok(ProbePlan::Ready(self.probe_leaf(cx, value)));
                    }
                }
                let reason = match &self.arena.primitive(primitive).primitive {
                    Primitive::Psequand | Primitive::Psequor => {
                        unreachable!("short circuits are lowered above")
                    }
                    Primitive::PjsCall(_)
                    | Primitive::PjsApply
                    | Primitive::PjsObjectCreate(_)
                    | Primitive::PjsObjectGet(_)
                    | Primitive::PjsObjectSet(_)
                    | Primitive::PjsFnMethod => "external",
                    _ => return Ok(ProbePlan::Children(expr::Resume::Prim(prim::Prim {
                        primitive, operands: self.source.node(node).primitive_arguments(),
                    }))),
                };
                return Err(Unsupported(reason));
            }
            View::If { condition, then_, else_ } => {
                let conditional = self.conditional(cx, cond::Kind::If, condition, then_, else_)?;
                return Ok(ProbePlan::Children(expr::Resume::If(conditional)));
            }
            View::Switch { scrutinee, header, .. } => {
                let operands = self.source.node(node).switch_actions();
                if matches!(self.arena.switch(header).dispatch, crate::lambda::SwitchDispatch::Variant(_)) {
                    if variant::is_untagged(self.arena.switch(header)) {
                        return Ok(ProbePlan::Children(expr::Resume::Untagged(self.untagged_switch(cx, scrutinee, operands, header)?)));
                    }
                    return Ok(ProbePlan::Children(expr::Resume::Variant(self.named_variant(cx, scrutinee, operands, header)?)));
                }
                return Ok(ProbePlan::Children(expr::Resume::Switch(self.integer_switch(cx, scrutinee, operands, header)?)));
            }
            View::StrSwitch { scrutinee, header, .. } => {
                let operands = self.source.node(node).switch_actions();
                return Ok(ProbePlan::Children(expr::Resume::Switch(self.string_switch(cx, scrutinee, operands, header)?)));
            }
            View::Catch { .. } => {
                return Ok(ProbePlan::Children(expr::Resume::Catch(self.catch(cx, node)?)));
            }
            View::Exit { label, .. } => {
                let args = self.source.node(node).exit_arguments();
                return Ok(ProbePlan::Children(expr::Resume::Exit(self.exit(label, args))));
            }
            View::Try { .. } | View::TryFinally { .. } => return Err(Unsupported("try")),
            View::While { .. }
            | View::For { .. }
            | View::ForOf { .. }
            | View::ForAwaitOf { .. }
            | View::Break
            | View::Continue => return Err(Unsupported("loop")),
            View::Assign { .. } => return Err(Unsupported("assign")),
            View::JBin { .. }
            | View::JNot { .. }
            | View::JBnot { .. }
            | View::JTypeof { .. }
            | View::JIn { .. }
            | View::JCond { .. }
            | View::JSeq { .. }
            | View::JCall { .. }
            | View::JFlatCall { .. }
            | View::JNew { .. }
            | View::JIndex { .. }
            | View::JDot { .. }
            | View::JLength { .. }
            | View::JIsNullish { .. }
            | View::JStrAppend { .. }
            | View::JFun { .. }
            | View::JObject { .. }
            | View::JArray { .. }
            | View::JBlockLit { .. }
            | View::JOptional { .. }
            | View::JJsx { .. }
            | View::JTemplate { .. }
            | View::JTagged { .. }
            | View::JRaw { .. }
            | View::JAwait { .. }
            | View::JSpread { .. }
            | View::JQualified { .. }
            | View::JNumber { .. }
            | View::JStr { .. }
            | View::JBool
            | View::JNull
            | View::JUndefined
            | View::JJson { .. }
            | View::JRecordRest { .. }
            | View::SBlock { .. }
            | View::SDecl { .. }
            | View::SExp { .. }
            | View::SIf { .. }
            | View::SWhile { .. }
            | View::SForRangeExisting { .. }
            | View::SForRange { .. }
            | View::SForOf { .. }
            | View::SForAwaitOf { .. }
            | View::SSwitch { .. }
            | View::SReturn { .. }
            | View::SThrow { .. }
            | View::STry { .. }
            | View::SBreak { .. }
            | View::SContinue { .. }
            | View::SDebugger
            | View::SRest { .. } => unreachable!("expected level-L source"),
        };
        Ok(ProbePlan::Ready(self.probe_leaf(cx, value)))
    }
    /// K4/K2/K10: C:2411 compile_let_binding_output / C:4603 compile_effect_output / C:1997 with_function_scope.
    fn children(&self, cx: Cx, resume: &Self::Resume, into: &mut Vec<(Cx, NodeId)>) {
        self.expression_children(cx, resume, into);
    }
    /// V: compile_string_switch_inner. O(1), after the scrutinee allocates
    /// its temporaries and the switch result obtains its identity.
    fn child_context(&self, cx: Cx, resume: &Self::Resume, index: usize) -> Cx {
        if let expr::Resume::Switch(frame) = resume {
            self.switch_child_context(cx, *frame, index)
        } else { cx }
    }
    /// K4/K2: C:2411 compile_let_binding_output / C:4603 compile_effect_output.
    fn child(&mut self, cx: Cx, resume: &Self::Resume, index: usize, output: Probed) -> Probed {
        self.expression_child(cx, resume, index, output)
    }
    /// K0/K2/K10: C:119 append / C:4715 append_effect_output / C:562 function_expr.
    fn finish(
        &mut self,
        cx: Cx,
        resume: Self::Resume,
        children: impl Iterator<Item = Probed>,
    ) -> Result<Probed, Unsupported> {
        match resume {
            expr::Resume::Prim(prim) => self.finish_primitive(cx, prim, children),
            expr::Resume::Record(record) => Ok(self.finish_record(cx, record, children)),
            resume => Ok(self.finish_expression(cx, resume, children)),
        }
    }
}

impl Realizer for State {
    /// K4/K5/K6: C:6648 declare_compiled, C:6667 assign_compiled, C:6658 return_compiled.
    fn leaf(&mut self, cx: Cx, value: NodeId) -> Out {
        let start = self.statements.mark();
        let mut finished = Finished::False;
        let value = match cx.cont {
            Cont::Value(Tail::No) | Cont::Value(Tail::Return(_)) | Cont::Effect(Tail::No) => {
                Some(value)
            }
            Cont::Declare(kind, var) => {
                let stmt = super::j::declare(&mut self.arena, kind, var, value);
                self.statements.push(stmt);
                None
            }
            Cont::Assign(var) => {
                let stmt = super::j::assign(&mut self.arena, var, value);
                self.statements.push(stmt);
                None
            }
            Cont::Effect(Tail::Return(_)) => {
                let stmt = super::j::return_value(&mut self.arena, value);
                self.statements.push(stmt);
                finished = Finished::True;
                None
            }
        };
        Out {
            stmts: self.statements.since(start),
            value,
            finished,
        }
    }
    /// K2: C:4715 append_effect_output, where the value is kept: a comma,
    /// or the tail alone when the head has no effect. Constant.
    fn seq(&mut self, _: Cx, first: NodeId, mut second: Out) -> Out {
        if self.arena.node(first).flags().contains(super::NodeFlags::STRICT) {
            self.arena.release(first);
        } else {
            let value = second.value.expect("the tail of a kept sequence has a value");
            second.value = Some(super::j::norm::jm1_js_seq(&mut self.arena, first, value));
        }
        second
    }
    /// O:339 push_effect_expression: the head of a deferred sequence as
    /// statements. One step per comma operand of the head.
    fn effect(&mut self, first: NodeId) -> Span {
        let mark = self.statements.mark();
        self.drop_pure_effect(first);
        self.statements.since(mark)
    }
    /// R1–R5: realize a deferred conditional from its value operands.
    fn cond(&mut self, cx: Cx, test: NodeId, yes: Out, no: Out) -> Out {
        self.realize_conditional(cx, test, yes, no)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::mem::size_of;

    #[test]
    fn context_sizes() {
        assert_eq!(size_of::<LoopRef>(), 4);
        assert_eq!(size_of::<JumpTop>(), 4);
        assert_eq!(size_of::<LoopTop>(), 4);
        assert_eq!(size_of::<Ret>(), 12);
        assert_eq!(size_of::<Tail>(), 12);
        assert_eq!(size_of::<Cont>(), 16);
        assert_eq!(size_of::<Cx>(), 32);
    }

    #[test]
    fn five_contexts_start_at_control_boundaries() {
        let var = VarId(0);
        let contexts = [
            Cx::value(),
            Cx::effect(),
            Cx::declare(LetKind::Strict, var),
            Cx::assign(var),
            Cx::returning(),
        ];
        for cx in contexts {
            assert_eq!(cx.jumps, JumpTop(0));
            assert_eq!(cx.loops, LoopTop(0));
            assert_eq!(cx.switch_depth, 0);
            assert!(!cx.return_unit);
            assert!(!cx.probing);
        }
    }
    #[test]
    fn source_probe_visits_ten_thousand_nested_nodes_once() {
        struct Rules<'a> {
            source: &'a super::super::Bir,
            seen: Vec<u8>,
        }
        impl ProbeRules for Rules<'_> {
            type Resume = (NodeId, NodeId);
            fn enter(
                &mut self,
                _: Cx,
                node: NodeId,
            ) -> Result<ProbePlan<Self::Resume>, super::super::bridge::Unsupported> {
                self.seen[node.index()] += 1;
                match self.source.view(node) {
                    super::super::View::Seq { first, second } => {
                        Ok(ProbePlan::Children((first, second)))
                    }
                    super::super::View::Const { .. } => Ok(ProbePlan::Ready(Probed::Out(Out {
                        stmts: Span::default(),
                        value: Some(node),
                        finished: Finished::False,
                    }))),
                    other => panic!("unexpected test source: {other:?}"),
                }
            }
            fn children(
                &self,
                cx: Cx,
                &(first, second): &Self::Resume,
                into: &mut Vec<(Cx, NodeId)>,
            ) {
                into.extend([(cx, first), (cx, second)]);
            }
            fn finish(
                &mut self,
                _: Cx,
                _: Self::Resume,
                mut children: impl Iterator<Item = Probed>,
            ) -> Result<Probed, super::super::bridge::Unsupported> {
                assert!(children.next().is_some());
                Ok(children.next().unwrap())
            }
        }
        for first_position in [false, true] {
            let mut source = super::super::Bir::default();
            source.begin_bulk();
            let constant = source.intern_const(super::super::Constant::Null);
            let mut root = source.new_node(super::super::View::Const { value: constant }, 0);
            for _ in 0..10_000 {
                let leaf = source.new_node(super::super::View::Const { value: constant }, 0);
                let (first, second) = if first_position {
                    (root, leaf)
                } else {
                    (leaf, root)
                };
                root = source.new_node(super::super::View::Seq { first, second }, 0);
            }
            source.finish_bulk(root);
            let mut rules = Rules {
                source: &source,
                seen: vec![0; source.nodes.len()],
            };
            let mut probe = SourceProbe::default();
            probe.probe(&mut rules, Cx::value(), root).unwrap();
            assert_eq!(probe.steps, 20_001);
            assert!(rules.seen.iter().all(|&visits| visits == 1));
        }
        assert_eq!(std::mem::size_of::<SourceProbe>(), 8);
        assert_eq!(std::mem::size_of::<ProbePlan<()>>(), 20);
    }
}
