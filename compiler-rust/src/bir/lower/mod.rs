//! Continuations for the level-L to level-J lowering (BACKEND_LOWERING §1).
//! Context references are indices, never references into growing state pools.
mod args;
mod assign;
mod loops;
mod label;
mod try_;
mod ffi_args;
mod external;
mod call;
mod close;
mod cond;
mod exit;
mod export;
mod globals;
pub(crate) mod names;
mod expr;
mod konst;
mod prim;
mod record;
mod rec;
mod tail;
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
    /// O(1): observe source entry for symbolic label scheduling.
    fn source_enter(&mut self, _cx: Cx, _node: NodeId) {}
    /// O(arity): compose symbolic events after one completed lowering.
    fn source_leave(&mut self, _output: &Probed) {}
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
    /// Cost: implementation-specific child-output combination: consumes the supplied
    /// completed outputs and delegates realization/statement/normalizer work, never requests
    /// their source compilation again.
    fn finish(
        &mut self,
        cx: Cx,
        resume: Self::Resume,
        children: impl Iterator<Item = Probed>,
    ) -> Result<Probed, super::bridge::Unsupported>;
}

/// Explicit source traversal, separate from realization of deferred J operands.
pub struct SourceProbe<R> {
    work: Vec<ProbeWork<R>>,
    values: Vec<Probed>,
    children: Vec<(Cx, NodeId)>,
    /// Source occurrences offered to dispatch (one per incoming tree edge).
    pub steps: usize,
}
enum ProbeWork<R> {
    Enter(Cx, NodeId),
    EnterChild(Cx, NodeId, usize, usize),
    Finish(Cx, R, usize),
    Child(Cx, usize, usize),
}
impl<R> Default for SourceProbe<R> {
    /// O(1): initialize empty reusable storage; backing buffers grow on demand.
    fn default() -> Self {
        Self { work: Vec::new(), values: Vec::new(), children: Vec::new(), steps: 0 }
    }
}
impl<R> SourceProbe<R> {
    /// K1/K6: C:1529 compile_expr / C:5144 compile_if_return_output.
    /// A source node is entered once. Finish frames receive the saved operands
    /// and child outputs, never a request to compile the same child again.
    /// Cost: O(N + E) scheduling events for N visited source occurrences and E scheduled
    /// edges, plus enter/child/finish callback work. Pushes each child continuation once and
    /// drains completed outputs once.
    pub fn probe(
        &mut self,
        rules: &mut impl ProbeRules<Resume = R>,
        cx: Cx,
        node: NodeId,
    ) -> Result<Probed, super::bridge::Unsupported> {
        self.work.clear();
        self.values.clear();
        self.children.clear();
        let work = &mut self.work;
        let values = &mut self.values;
        let children = &mut self.children;
        work.push(ProbeWork::Enter(cx, node));
        while let Some(task) = work.pop() {
            let task = match task {
                ProbeWork::EnterChild(cx, node, parent, index) => {
                    let ProbeWork::Finish(_, resume, _) = &work[parent] else { unreachable!("parent resume") };
                    ProbeWork::Enter(rules.child_context(cx, resume, index), node)
                }
                task => task,
            };
            match task {
                ProbeWork::EnterChild(..) => unreachable!("resolved child context"),
                ProbeWork::Enter(cx, node) => {
                    self.steps += 1;
                    rules.source_enter(cx, node);
                    match rules.enter(cx, node)? {
                        ProbePlan::Ready(value) => { rules.source_leave(&value); values.push(value); },
                        ProbePlan::Children(resume) => {
                            rules.children(cx, &resume, children);
                            let parent = work.len();
                            work.push(ProbeWork::Finish(cx, resume, children.len()));
                            for (index, (cx, node)) in children.drain(..).enumerate().rev() {
                                work.push(ProbeWork::Child(cx, parent, index));
                                work.push(ProbeWork::EnterChild(cx, node, parent, index));
                            }
                        }
                    }
                }
                ProbeWork::Child(cx, parent, index) => {
                    let ProbeWork::Finish(_, resume, _) = &work[parent] else {
                        unreachable!("parent resume frame")
                    };
                    let child = values.pop().expect("completed source child");
                    let cx = rules.child_context(cx, resume, index);
                    values.push(rules.child(cx, resume, index, child));
                }
                ProbeWork::Finish(cx, resume, count) => {
                    let start = values
                        .len()
                        .checked_sub(count)
                        .expect("source probe children");
                    let value = rules.finish(cx, resume, values.drain(start..))?;
                    rules.source_leave(&value);
                    values.push(value);
                }
            }
        }
        assert_eq!(values.len(), 1);
        Ok(values.pop().expect("source probe output"))
    }
}

#[derive(Clone, Copy, Default, serde::Serialize)]
pub(crate) struct SwitchStats {
    pub source_visits: usize,
    pub fingerprint_visits: usize,
    pub comparisons: usize,
    pub compared_pairs: usize,
    pub location_visits: usize,
    /// Steps of `close::decide` over every copied run.
    pub close_steps: usize,
    /// Statements copied into lists (`StatementStack::copied`): a moved
    /// statement is copied, and decided, once per move.
    pub statements_copied: usize,
    /// References to JavaScript globals the lowering marked to print as
    /// `globalThis.name`, and the steps of that decision
    /// (`globals::decide`).
    pub globals_qualified: usize,
    pub global_steps: usize,
    /// Step A against the legacy tail-call pass (`shadow::compare_decisions`),
    /// zero until check mode compares.
    #[serde(flatten)]
    pub decisions: DecisionStats,
    /// The naming log's replay against the naming pass on the lowering's
    /// program (THREE_TREES 11.4, "T5 part B as redesigned" (d)), zero
    /// until check mode compares.
    #[serde(flatten)]
    pub names: crate::emit::NameStats,
    /// What the replay did.
    #[serde(flatten)]
    pub replayed: names::Replayed,
    /// Nodes `names::adopt` read (`Log::adopted_nodes`).
    pub adopted_nodes: usize,
    /// The steps of the naming log (`Log::steps`) and of its replay
    /// (`Replayed::steps`), without those of the tables.
    pub name_log_steps: usize,
    pub name_replay_steps: usize,
    /// One when check mode compared the names, one in `names_uncompared`
    /// when the pass does not support the unit.
    pub names_compared: usize,
    pub names_uncompared: usize,
}

/// The decisions of step A (`close::decide`) compared with those of the
/// legacy tail-call pass on the same program after the flatten and
/// external-shadow passes, by declared identifier (THREE_TREES 11.4, "T4c
/// design" (a) and (b)).
#[derive(Clone, Copy, Default, serde::Serialize)]
pub(crate) struct DecisionStats {
    /// Declarations the lowering decided, each counted once.
    pub decision_rows: usize,
    /// Decisions replaced by a later one of the same variable: its
    /// statement was moved out of a copied list and copied again.
    pub decision_reclosed: usize,
    /// Identifiers the legacy pass gives a status.
    pub decision_legacy: usize,
    /// Rows whose identifier the legacy pass does not see declared.
    pub decision_extra: usize,
    /// Identifiers of the legacy pass without a row.
    pub decision_missing: usize,
    /// Identifiers with more than one row: copies that print alike.
    pub decision_copied: usize,
    /// Identifiers whose `built`, summed over their rows, is not the count
    /// the legacy pass reads.
    pub decision_count_differences: usize,
    /// Rows whose status is not the legacy status of their identifier.
    pub decision_status_differences: usize,
    /// Rows with the legacy status whose inline candidacy (a recorded site)
    /// is not the legacy pass's.
    pub decision_site_differences: usize,
    /// Rows the lowering would inline, and identifiers the legacy pass
    /// keeps for inlining.
    pub decision_inline: usize,
    pub decision_legacy_inline: usize,
}

pub(crate) struct Lowered {
    pub program: super::bridge_j::Imported,
    /// Read by the rule tests against the legacy output's flag.
    #[cfg(test)]
    pub finished: Finished,
    /// The exports after coercion and the names they reserve (`export.rs`).
    pub coerced: export::Coerced,
    pub dynamic_imports: Vec<crate::js_ir::ModuleId>,
    pub switch_stats: SwitchStats,
    /// The names of the naming log's replay (`names::replay`), by variable
    /// and by import; compared with the pass in check mode, not printed.
    /// What the replay did is in `SwitchStats::replayed`.
    pub printed: crate::emit::Printed,
    /// The imports the replay named in the program, in its order.
    pub name_imports: Vec<crate::bir::ImportId>,
}

/// N1: C:663 compile_deps_program_in_arena; one fresh J arena for this migration cut.
#[cfg(test)]
pub(crate) fn lower(
    input: super::bridge::ForLowering,
    locations: Option<&crate::lambda::LamLocTable>,
    direct: bool,
) -> Result<Lowered, Unsupported> {
    unit::lower(input, locations, direct, None, false, true, false)
}

/// H2: C:1266 compile_external_field_apply; summaries are read-only inputs.
pub(crate) fn lower_with_resolver(
    input: super::bridge::ForLowering,
    locations: Option<&crate::lambda::LamLocTable>,
    direct: bool,
    resolver: Option<&crate::js_ir::ModulePathResolver>,
    cross_module_inline: bool,
    check_div_by_zero: bool,
    jsx_preserve: bool,
) -> Result<Lowered, Unsupported> {
    unit::lower(input, locations, direct, resolver, cross_module_inline, check_div_by_zero, jsx_preserve)
}

/// One immutable summary acquisition per imported module; indexed by ImportId.
enum ModuleConstants {
    Unread,
    Missing,
    Present(std::sync::Arc<ahash::AHashMap<String, crate::cmi::persistent_env::CmjExportConstant>>),
}

struct State {
    tail_arguments: usize,
    tail_parameters: usize,
    tail_sort_comparisons: usize,
    tail_body_statements: usize,
    tail_frames: Vec<tail::Frame>,
    tail_functions: Vec<Option<LoopRef>>,
    tail_copies: Vec<Option<VarId>>,
    tail_assignments: Vec<NodeId>,
    tail_name: String,
    call_reversed: Vec<NodeId>,
    call_arities: Vec<i32>,
    /// A module/member pair has no canonical dense handle; individual component handles do not index their sparse Cartesian product.
    call_arity_index: std::collections::HashMap<(crate::bir::ImportId, crate::bir::StrId), Option<call::AritySpan>>,
    eta_arguments: Vec<NodeId>,
    calls: Vec<Option<call::Plan>>,
    tail_order: Vec<VarId>,
    rec_members: Vec<rec::Member>,
    rec_steps: usize,
    switches: Vec<Option<switch::Plan>>,
    variants: Vec<Option<variant::Plan>>,
    named_metadata: variant::Metadata,
    switch_spelling: String,
    untagged: Vec<Option<untagged::Plan>>,
    untagged_storage: untagged::Storage,
    untagged_dispatch: crate::bir::untagged_plan::Plan<u32>,
    switch_facts: Vec<switch::Facts>,
    switch_work: Vec<(NodeId, bool)>,
    group_indices: Vec<usize>,
    group_nodes: Vec<NodeId>,
    /// Structural body equivalence joins different NodeIds, so no existing node index identifies an equality group.
    group_table: hashbrown::HashTable<usize>,
    group_order: Vec<usize>,
    group_heads: Vec<usize>,
    switch_output_nodes: Vec<NodeId>,
    switch_output_clauses: Vec<crate::bir::ClauseMeta>,
    switch_group_steps: usize,
    switch_hash_bytes: Vec<u8>,
    switch_constant_work: Vec<(crate::bir::ConstId, crate::bir::ConstId)>,
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
    traversal: SourceProbe<expr::Resume>,
    list_block_info: Option<crate::bir::JsId>,
    constant_steps: usize,
    constant_children: Vec<NodeId>,
    constant_text: String,
    constant_encoding: String,
    constant_work: Vec<konst::Work>,
    constant_values: Vec<(NodeId, bool)>,
    argument_outputs: Vec<Out>,
    argument_values: Vec<NodeId>,
    ffi_suffix: Vec<ffi_args::LaterLiteral>,
    ffi_params: Vec<usize>,
    source_steps: usize,
    invalid_module_paths: Vec<bool>,
    awaited_units: Vec<bool>,
    dynamic_imports: Vec<crate::bir::ImportId>,
    import_storage: import::Storage,
    external_references: Vec<Option<crate::bir::ImportId>>,
    external_globals: Vec<Option<VarId>>,
    external_pending: Vec<(u32, NodeId)>,
    external_values: Vec<NodeId>,
    inline_globals: Vec<Ident>,
    inline_foreign: Vec<Ident>,
    /// Imported export templates are keyed by sparse module/member pairs, which have no existing dense template identity.
    inline_templates: std::collections::HashMap<(crate::bir::ImportId, crate::bir::StrId), call::InlineTemplate>,
    inline_param_stats: Vec<super::l::beta::ParamStats>,
    inline_engine: super::engine::Reuse,
    inline_imports: usize,
    inline_reductions: usize,
    inline_scratch: crate::bir::l::beta::Scratch,
    external_bindings: Vec<[Option<VarId>; 2]>,
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
    evaluation: args::Evaluation,
    object_scratch: record::Scratch,
    primitive_steps: usize,
    /// Let/Seq nodes read by row R5 step 0 of section 3.6.
    spine_steps: usize,
    /// Reused by the J rules that push onto a vector.
    scratch: Vec<NodeId>,
    /// 4.1: the jump table, indexed by catch header; grown where a catch is
    /// entered and the unit has more headers than entries.
    jumps: Vec<exit::Jump>,
    /// The handlers of the catches being lowered, a stack of flattened tables.
    catch_table: Vec<(NodeId, crate::bir::CatchId)>,
    catches: Vec<Option<exit::Plan>>,
    tries: Vec<try_::Plan>,
    loops: Vec<loops::Plan>,
    next_loop_label: u32,
    labels: label::Schedule,
    try_form_reads: usize,
    catch_work: Vec<NodeId>,
    /// `HAS_EXIT` reads that decided a flattening or a form.
    catch_flag_reads: usize,
    /// Handler nodes read to find the label of an exit (4.1 step 1).
    catch_walk_steps: usize,
    /// The variables of the export blocks, as the importer recorded them.
    export_vars: Vec<u32>,
    /// The tables of the export fold (`export.rs`).
    coercion: export::Tables,
}
impl State {
    /// N1: C:481 new. Transfer cold pools, while source hot nodes/list operands
    /// remain readable. Variables retain source identities, never global stamps.
    /// Cost: O(N + V + F + G) initialization for source nodes, variables, function headers
    /// and globals, plus untagged::prepare and variant::prepare metadata work. Reserves
    /// output node/list/switch domains from imported counts; moves cold pools rather than
    /// cloning them.
    fn new(mut input: super::bridge::Imported) -> Self {
        let source_nodes = input.arena.nodes.len();
        let source_operands = input.arena.lists.slot_count();
        let mut arena = Bir::default();
        arena.begin_bulk();
        arena.pools = std::mem::take(&mut input.arena.pools);
        arena.vars.funcs = std::mem::take(&mut input.arena.vars.funcs);
        arena.vars.function_params = std::mem::take(&mut input.arena.vars.function_params);
        // Import already knows the source-node and switch-arm counts. Reserve
        // the output's parallel node columns together; switch arms can emit
        // target-reference, assignment, expression statement, block and break
        // nodes in addition to their source body, plus per-switch scaffolding.
        // Inlining/FFI expansion may exceed this initial capacity.
        let switch_arms = arena.pools.switch_keys.len() + arena.pools.switches.len();
        let output_nodes = source_nodes + 5 * arena.pools.switch_keys.len()
            + 16 * arena.pools.switches.len() + 8;
        // Mixed dispatch can emit both literal and payload clause runs.
        arena.pools.switch_clauses.reserve_exact(2 * switch_arms);
        arena.pools.switch_keys.reserve_exact(switch_arms + 16 * arena.pools.switches.len());
        arena.lists.reserve_slots(2 * source_operands + 4 * arena.pools.switch_keys.len() + 8);
        arena.nodes.reserve_exact(output_nodes);
        arena.parents.reserve_exact(output_nodes);
        arena.weights.reserve_exact(output_nodes);
        arena.capture_chain.reserve_exact(output_nodes);
        arena.j_duplicable.reserve_exact(output_nodes);
        #[cfg(debug_assertions)]
        arena.checked_children.reserve_exact(output_nodes);
        // Each imported apply header can produce one ordinary JS call payload.
        // Reserve that known count; primitives/inlining retain safe growth.
        arena.pools.js.reserve_exact(arena.pools.apply.len());
        arena.func_owners.resize(arena.vars.funcs.len(), None);
        // Imported binders, export bindings and one result binding per switch.
        let output_vars = input.arena.vars.len() + input.export_vars.len() + arena.pools.switches.len();
        arena.capture_binders.reserve_exact(output_vars);
        arena.bulk_binders.reserve_exact(output_vars);
        arena.vars.j_origin.reserve_exact(output_vars);
        arena.vars.name.reserve_exact(output_vars);
        arena.vars.order.reserve_exact(output_vars);
        arena.vars.flags.reserve_exact(output_vars);
        arena.vars.uses.reserve_exact(output_vars);
        arena.vars.binder.reserve_exact(output_vars);
        arena.vars.fact.reserve_exact(output_vars);
        arena.vars.printed.reserve_exact(output_vars);
        for i in 0..input.arena.vars.len() {
            let var = VarId(i as u32);
            let made = arena.new_var_id(input.arena.vars.name(var), input.arena.vars.order(var));
            assert_eq!(made, var);
            arena.vars.flags[i] = input.arena.vars.flags[i];
        }
        let mut scope = scope::Scope::with_capacity(arena.vars.len(), output_vars);
        scope.decisions.reserve_exact(output_vars);
        // Reference sites are indexed by emitted nodes, not by source binders.
        scope.sites.reserve_exact(output_nodes);
        arena.js_scope = Some(scope);
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
        let (untagged_storage, untagged_dispatch) = untagged::prepare(&mut arena);
        let named_metadata = variant::prepare(&mut arena);
        let needs_hashes = switch_arms != 0 || !arena.pools.catches.is_empty();
        Self {
            evaluation: args::Evaluation::default(),
            object_scratch: record::Scratch::default(),
            tail_arguments: 0, tail_parameters: 0, tail_sort_comparisons: 0, tail_body_statements: 0,
            tail_frames: Vec::new(), tail_functions: Vec::new(), tail_copies: Vec::new(),
            tail_assignments: Vec::new(), tail_name: String::new(), call_reversed: Vec::new(), call_arities: Vec::new(), call_arity_index: Default::default(), eta_arguments: Vec::new(), calls: Vec::new(), tail_order: Vec::new(),
            rec_members: Vec::new(), rec_steps: 0,
            switch_facts: vec![switch::Facts::default(); input.arena.nodes.len()],
            switches: Vec::new(), variants: Vec::new(), named_metadata, switch_spelling: String::new(), untagged: Vec::new(), untagged_storage, untagged_dispatch, switch_work: Vec::new(), switch_pairs: Vec::new(),
            group_indices: Vec::with_capacity(2 * switch_arms),
            group_nodes: Vec::with_capacity(switch_arms),
            group_table: hashbrown::HashTable::with_capacity(switch_arms),
            group_order: Vec::with_capacity(switch_arms), group_heads: Vec::with_capacity(switch_arms),
            switch_output_nodes: Vec::new(), switch_output_clauses: Vec::new(), switch_group_steps: 0,
            switch_hash_bytes: Vec::new(), switch_constant_work: Vec::new(),
            switch_primitive_hashes: Vec::with_capacity(if needs_hashes { arena.pools.prims.len() } else { 0 }),
            switch_constant_hashes: Vec::with_capacity(if needs_hashes { arena.pools.consts.len() } else { 0 }),
            switch_comparisons: 0, switch_compared: 0, switch_visits: 0,
            invalid_module_paths: vec![false; input.arena.nodes.len()],
            awaited_units: vec![false; input.arena.vars.len()],
            dynamic_imports: Vec::new(), import_storage: Default::default(),
            external_references: Vec::new(),
            external_globals: Vec::new(),
            external_pending: Vec::new(),
            external_values: Vec::new(),
            inline_globals: Vec::new(), inline_foreign: Vec::new(), inline_templates: Default::default(),
            inline_param_stats: Vec::new(), inline_engine: Default::default(), inline_imports: 0, inline_reductions: 0,
            inline_scratch: Default::default(),
            external_bindings: Vec::new(),
            module_constants: (0..arena.pools.j_modules.len()).map(|_| ModuleConstants::Unread).collect(),
            source: input.arena,
            arena,
            idents: input.idents,
            statements: StatementStack::with_capacity(output_nodes),
            free: FreePool::with_source_capacity(source_nodes),
            traversal: SourceProbe {
                // Each pending child has an entry and a continuation event.
                work: Vec::with_capacity(2 * source_nodes),
                values: Vec::with_capacity(source_nodes),
                children: Vec::with_capacity(source_nodes),
                steps: 0,
            },
            list_block_info: None, constant_steps: 0, constant_children: Vec::new(), constant_text: String::new(), constant_encoding: String::new(), constant_work: Vec::new(), constant_values: Vec::new(),
            argument_outputs: Vec::with_capacity(source_operands),
            argument_values: Vec::with_capacity(source_operands),
            ffi_suffix: Vec::new(), ffi_params: Vec::new(),
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
            tries: Vec::new(),
            loops: Vec::new(),
            next_loop_label: 0,
            labels: label::Schedule::with_source_capacity(source_nodes),
            try_form_reads: 0,
            catch_work: Vec::new(),
            catch_flag_reads: 0,
            catch_walk_steps: 0,
            export_vars: input.export_vars,
            coercion: Default::default(),
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
    /// Cost: SourceProbe::probe cost: O(N + E) traversal events plus lowering callbacks;
    /// lends and restores the retained traversal buffers without an additional source walk.
    fn probe(&mut self, cx: Cx, node: NodeId) -> Result<Probed, Unsupported> {
        let mut traversal = std::mem::take(&mut self.traversal);
        let before = traversal.steps;
        let output = traversal.probe(self, cx, node);
        self.source_steps += traversal.steps - before;
        self.traversal = traversal;
        if output.is_ok() { self.finish_labels(); }
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

    /// N1: C:663 compile_deps_program_in_arena, the unit: the last value is
    /// read for the exports (`export.rs`). Cost: that of `extract_exports`
    /// and of `finish`.
    fn complete_unit(mut self, probed: Probed) -> Lowered {
        let out = self.realize(Cx::value(), probed);
        // Export coercion takes ownership of the root's identifier vector.
        // Isolate that output-boundary payload so shared source/block shapes
        // remain immutable for any other surviving block occurrence.
        if let Some(mut end) = out.value {
            while let View::JSeq { second, .. } = self.arena.view(end) { end = second; }
            if let View::JBlockLit { info, .. } = self.arena.view(end) {
                if let crate::lambda::TagInfo::ModuleExport(exports) = self.arena.block_tag(info) {
                    let tag = crate::lambda::TagInfo::ModuleExport(exports.clone());
                    let owned = self.arena.js_info(crate::bir::JsPayload::Block(tag));
                    self.arena.nodes[end.index()].set_block_info(owned);
                }
            }
        }
        let exports = self.extract_exports(out.value, out.finished);
        let run = self.statements.since(Span {
            start: out.stmts.start,
            len: 0,
        });
        let (list, coerced) = match exports {
            Some(exports) if !exports.is_empty() => {
                let coerced = self.coerce_exports(run, exports, out.finished);
                let list = self.coerced_list(run);
                self.statements.close(&mut self.arena, list);
                (list, coerced)
            }
            _ => (
                self.statements.take_list(&mut self.arena, run),
                export::Coerced::default(),
            ),
        };
        self.finish(list, out.finished, coerced)
    }

    /// The output of one construct in `cx`, for the rule tests: the value is
    /// carried by a plain sentinel SExp after the statements.
    #[cfg(test)]
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
        self.finish(list, out.finished, export::Coerced::default())
    }

    /// The root block over the top-level list. One step per statement of
    /// the list and one write per catch of the unit.
    fn finish(mut self, list: crate::bir::ListId, _finished: Finished, coerced: export::Coerced) -> Lowered {
        #[cfg(test)]
        let coerced = export::Coerced {
            steps: self.coercion.steps,
            site_visits: self.coercion.site_visits,
            ..coerced
        };
        let root = self.arena.block_from_list(list);
        // The headers keep their labels and parameters; the exits they count
        // stay in the source, which reads the counts while a function of
        // another module is inlined. One write per catch of the unit.
        for header in &mut self.arena.pools.catches {
            header.uses = 0;
        }
        self.arena.finish_bulk(root);
        // Materialize legacy-owned dependency records only at the output boundary.
        let dynamic_imports = self.dynamic_imports.iter().map(|id| self.arena.pools.j_modules[id.index()].clone()).collect();
        // THREE_TREES 11.4, "T5 design": every list is the one the flatten
        // pass receives, so the bindings around a reference are final.
        globals::decide(&mut self.arena, &self.idents);
        let mut printed = crate::emit::Printed::default();
        let (replayed, name_imports) = self.replay_names(root, &coerced, &mut printed);
        let (adopted_nodes, name_log_steps) = self.arena.js_scope.as_ref()
            .map_or((0, 0), |scope| (scope.names.adopted_nodes, scope.names.steps));
        let (close_steps, globals_qualified, global_steps) = self.arena.js_scope.as_ref()
            .map_or((0, 0, 0), |scope| (scope.close_steps, scope.globals.qualified, scope.globals.steps));
        Lowered {
            program: super::bridge_j::Imported::from_lowering(self.arena, root, self.idents),
            #[cfg(test)]
            finished: _finished,
            coerced,
            dynamic_imports,
            switch_stats: SwitchStats {
                source_visits: self.source_steps,
                fingerprint_visits: self.switch_visits,
                comparisons: self.switch_comparisons,
                compared_pairs: self.switch_compared,
                location_visits: self.location_steps,
                close_steps,
                statements_copied: self.statements.copied,
                globals_qualified,
                global_steps,
                decisions: DecisionStats::default(),
                names: crate::emit::NameStats::default(),
                replayed,
                adopted_nodes,
                name_log_steps,
                name_replay_steps: replayed.steps(),
                names_compared: 0,
                names_uncompared: 0,
            },
            printed,
            name_imports,
        }
    }

    /// The names of the finished unit whose root block is `root`
    /// (`names::replay`, after `globals::decide`), written to `printed`;
    /// what the replay did and the imports it named in the program. The
    /// program's imports are those with a live reference that are neither
    /// dynamic nor unresolved, in the order of the module list
    /// (`lam_compile::module_sort_cmp`). Cost: one step per import and a
    /// sort of the named ones, one per reservation, and `names::replay`.
    fn replay_names(&self, root: NodeId, coerced: &export::Coerced, printed: &mut crate::emit::Printed) -> (names::Replayed, Vec<crate::bir::ImportId>) {
        let scope = self.arena.js_scope.as_ref().expect("lowering scope");
        let modules = &self.arena.pools.j_modules;
        let mut imports: Vec<crate::bir::ImportId> = (0..modules.len())
            .filter(|&index| {
                let module = &modules[index];
                scope.import_uses.get(index).is_some_and(|&uses| uses > 0)
                    && !module.dynamic_import
                    && self.resolver.as_ref().is_none_or(|resolver| resolver.resolve_module_path(module).is_some())
            })
            .map(|index| crate::bir::ImportId(index as u32))
            .collect();
        imports.sort_by(|a, b| crate::lambda::lam_compile::module_sort_cmp(&modules[a.index()], &modules[b.index()]));
        let reservations: Vec<crate::emit::Subject> = coerced
            .reservations
            .iter()
            .zip(&self.coercion.reserved)
            .map(|(ident, &var)| crate::emit::Subject {
                slot: self.arena.vars.j_origin[var.index()].0,
                stamp: ident.stamp(),
                name: ident.name_atom(),
            })
            .collect();
        let program = names::Program {
            imports: &imports,
            reservations: &reservations,
            exports: &self.coercion.exported,
            raw: &scope.globals.raw,
        };
        let replayed = names::replay(
            &self.arena,
            root,
            &self.idents,
            &program,
            &mut crate::emit::Tables::default(),
            &mut names::Scratch::default(),
            printed,
        );
        (replayed, imports)
    }
}

impl ProbeRules for State {
    fn source_enter(&mut self, cx: Cx, node: NodeId) { self.label_enter(cx, node); }
    fn source_leave(&mut self, output: &Probed) { self.label_leave(output); }
    type Resume = expr::Resume;
    /// K1/H12: C:1529 compile_expr and K:60 compile_constant.
    /// Cost: O(1) tag dispatch plus the selected preparer: constant occurrences, application
    /// spine/arguments, recursive binders, function parameters, or switch metadata. Extending
    /// dense tables costs their newly initialized rows; descendant lowering is scheduled, not
    /// performed twice.
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
            View::Apply { callee, info, .. } => {
                let args = self.source.node(node).apply_args();
                let tail = self.self_call(cx, callee);
                let call = self.application(cx, callee, args, info)?;
                self.calls[call.0 as usize].as_mut().unwrap().tail = tail;
                return Ok(ProbePlan::Children(expr::Resume::Call(call)));
            }
            View::Fun { body, header } => {
                // The body is lowered next, inside the function's scope.
                names::open(&mut self.arena);
                return Ok(ProbePlan::Children(expr::Resume::Fun { body, header, loop_: self.tail_functions.get(node.index()).copied().flatten() }));
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
            View::LetRec { .. } => return Ok(ProbePlan::Children(expr::Resume::Rec(self.recursive_group(node)?))),
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
                return Ok(ProbePlan::Children(expr::Resume::Prim(prim::Prim {
                    primitive, operands: self.source.node(node).primitive_arguments(),
                })));
            }
            View::If { condition, then_, else_ } => {
                let conditional = self.conditional(cx, cond::Kind::If, condition, then_, else_)?;
                return Ok(ProbePlan::Children(expr::Resume::If(conditional)));
            }
            View::Switch { scrutinee, header, .. } => {
                let operands = self.source.node(node).switch_actions();
                if matches!(self.arena.switch(header).dispatch, crate::lambda::SwitchDispatch::Variant(_)) {
                    if variant::is_untagged(&self.arena.switch(header)) {
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
                return Ok(ProbePlan::Children(expr::Resume::Catch(self.catch(cx, node))));
            }
            View::Exit { label, .. } => {
                let args = self.source.node(node).exit_arguments();
                return Ok(ProbePlan::Children(expr::Resume::Exit(self.exit(label, args))));
            }
            View::Try { body, exception, handler } => return Ok(ProbePlan::Children(expr::Resume::Try(self.try_statement(cx, body, Some(exception), Some(handler), None)))),
            View::TryFinally { body, finaliser } => return Ok(ProbePlan::Children(expr::Resume::Try(self.compile_try_finally(cx, body, finaliser)))),
            View::While { .. } | View::For { .. } | View::ForOf { .. } | View::ForAwaitOf { .. } => return Ok(ProbePlan::Children(expr::Resume::Loop(self.loop_statement(cx, node)))),
            View::Break => return Ok(ProbePlan::Ready(self.loop_jump(cx, false)?)),
            View::Continue => return Ok(ProbePlan::Ready(self.loop_jump(cx, true)?)),
            View::Assign { var, value } => return Ok(ProbePlan::Children(expr::Resume::Assign { var, value })),
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

/// Cost: O(path segments and emitted bytes), reusing the destination.
pub(crate) fn flat_export_name_into<'a>(path: impl Iterator<Item = &'a str>, out: &mut String) {
    for (i, part) in path.enumerate() {
        if i != 0 { out.push('$'); }
        let part = if part.len() >= 3 && part.starts_with("\\\"") && part.ends_with('"') {
            &part[2..part.len() - 1]
        } else {
            part
        };
        out.push_str(part);
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
        assert_eq!(std::mem::size_of::<SourceProbe<()>>(), 80);
        assert_eq!(std::mem::size_of::<ProbePlan<()>>(), 20);
    }
}
