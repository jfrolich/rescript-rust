//! Lambda -> JS IR compilation.
//!
//! This module provides a straightforward lowering from Lambda IR into the
//! JavaScript IR used by the Rust compiler backend. The implementation favors
//! clarity over aggressive optimization; it is intended as a correct baseline
//! that can be extended with more advanced codegen passes.

use crate::lambda::{LamLoc, LamLocTable};
use ahash::{AHashMap, AHashSet};
use std::sync::Arc;

use crate::cmi::persistent_env::{CmjExportArity, CmjExportConstant};
use crate::context::IdGenerator;
use crate::ident::Ident;
use crate::js_ir::op::{IdentInfo, Kind, MutableFlag, Number, PropertyName, UsedStats};
use crate::js_ir::{
    BinOp, Block, CallArity, CallInfo, CallKind, CaseClause, DepsProgram, Expression,
    ExpressionDesc, ForDirection, ModuleId, ModulePathResolver, Program, Statement, StatementDesc,
    StringClause, VIdent, VariableDeclaration, block_last_is_terminal, unnest_block,
};
use crate::lambda::indexed::{IndexedLambdaContext, NodeId, NodeSnapshot};
use crate::lambda::js_pass_external_shadow::apply_external_shadow_pass;
use crate::lambda::js_pass_flatten_and_mark_dead::{
    apply_js_flatten_and_mark_dead_pass, apply_js_flatten_pass,
};
use crate::lambda::js_pass_record_rest::apply_js_record_rest_pass;
use crate::lambda::js_pass_tailcall_inline::apply_js_tailcall_inline_pass;
use crate::lambda::js_shake::{
    apply_js_shake_pass, keeps_declared_same_name_reusable_export_binding,
    move_reused_same_name_export_binding_to_export_tail,
    move_same_name_export_alias_to_export_tail, resolve_tail_move_replacement_expression,
};
use crate::lambda::lam_analysis;
use crate::lambda::lam_analysis::lfunction_can_be_inlined;
use crate::lambda::lam_analysis_indexed::is_closed_with_map as is_closed_with_map_indexed;
use crate::lambda::lam_arity::Arity;
use crate::lambda::lam_beta_reduce_indexed::{
    BetaDiagnostics as IndexedBetaDiagnostics,
    propagate_beta_reduce_with_map as propagate_beta_reduce_with_map_indexed,
};
use crate::lambda::lam_closure::is_closed_with_map;
use crate::lambda::lam_compat::{LetKind, SetFieldDbgInfo};
use crate::lambda::lam_compile_context::{Element, ExternalArityInfo, IdKind, LamStats};
use crate::lambda::lam_constant::{Constant, PointerInfo};
use crate::lambda::lam_exit_code::has_exit_code;
use crate::lambda::lam_free_variables::free_variables;
use crate::lambda::lam_pass_collect::get_arity;
use crate::lambda::lam_primitive::{Cst, Primitive};
use crate::lambda::lam_subst;
use crate::lambda::{
    ApInfo, Apply, ApplyStatus, LFunction, Lambda, LambdaSwitch, PrimInfo, SwitchCaseTag,
    SwitchKey, TagInfo,
};
use tracing::info_span;

use super::js_exp_make::{
    block_with_return_expr_iife, int_expr, int_literal, js_expr_no_side_effects, js_seq,
    remove_pure_subexpression, to_int32,
};
use super::js_stmt_make::{block_finishes_output, block_terminates, strict_single_return_expr};
use super::lam_coercion::{
    ExtractedExports, block_declares_initialized_ident,
    can_reuse_existing_undefined_export_binding, collect_declared_idents, extract_toplevel_exports,
    insert_rebound_export_before_equivalent_later_binding,
    keeps_declared_same_name_function_export_alias, max_ident_stamp_in_block,
    max_ident_stamp_in_expression, push_effect_expression, push_s_exp, push_s_if_empty,
    resolve_declared_same_name_self_alias_target, resolve_export_aliases,
    reusable_same_name_export_binding,
};
use super::lam_compile_variant::{empty_switch_case_clause, stable_group_switch_cases};

/// `Js_output.finished` (compiler/core/js_output.ml:28-31): whether a
/// compiled output's control has left (a `throw` from `Praise`, a `break`,
/// a `continue`, or a `return` in a return continuation), so that
/// `append_output` drops what is appended after it; `Dummy` is
/// `Js_output.dummy`'s.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum OutputFinished {
    True,
    False,
    Dummy,
}

/// A `Js_output.t` whose value is `None`: what OCaml's statement
/// continuations (`Declare`, `Assign`, `EffectCall`) produce.
#[derive(Debug, Clone)]
pub(crate) struct BlockOutput {
    pub(crate) block: Block,
    pub(crate) finished: OutputFinished,
}

impl BlockOutput {
    /// `Js_output.make block`.
    pub(crate) fn make(block: Block) -> Self {
        Self {
            block,
            finished: OutputFinished::False,
        }
    }

    /// An output whose `output_finished` is `True`: a `return`
    /// (js_output.ml:51, 59), a raise (lam_compile.ml:1682) or a jump back
    /// to a self tail call loop (lam_compile.ml:1538, 1626).
    pub(crate) fn finished(block: Block) -> Self {
        Self {
            block,
            finished: OutputFinished::True,
        }
    }

    /// `Js_output.dummy` (js_output.ml:38).
    pub(crate) fn dummy() -> Self {
        Self {
            block: vec![],
            finished: OutputFinished::Dummy,
        }
    }

    /// `Js_output.append_output` (js_output.ml:118-138) of two outputs
    /// without a value: a finished first output is kept as it is, an empty
    /// `dummy` second one is dropped, an empty first one gives the second,
    /// and otherwise the blocks are joined under the second's flag. Both
    /// outputs are compiled before this is called, as in OCaml.
    pub(crate) fn append(self, next: Self) -> Self {
        if self.finished == OutputFinished::True
            || (next.block.is_empty() && next.finished == OutputFinished::Dummy)
        {
            return self;
        }
        if self.block.is_empty() {
            return next;
        }
        let mut block = self.block;
        block.extend(next.block);
        Self {
            block,
            finished: next.finished,
        }
    }
}

/// Compilation result for an expression: prelude statements plus a value
/// expression, and the `output_finished` flag of the `Js_output.t` that
/// OCaml's `compile_lambda` returns for it.
#[derive(Debug, Clone)]
pub(crate) struct Compiled {
    pub(crate) prelude: Block,
    pub(crate) expr: Expression,
    pub(crate) finished: OutputFinished,
}

/// Owner-private result of inspecting one indexed external-field application.
/// The fallback keeps only scalar metadata and same-store IDs across resolver
/// calls; it never owns a recursive copy of an indexed child.
enum PreparedIndexedExternalApply {
    Reduced(NodeId),
    Call {
        module: ModuleId,
        field_name: String,
        args: Vec<NodeId>,
        info: ApInfo,
        known_arity: Option<Arity>,
    },
}

#[derive(Debug, Clone)]
pub(crate) struct StaticHandler {
    pub(crate) label: i32,
    pub(crate) bindings: Vec<Ident>,
    pub(crate) handler: Lambda,
}

#[derive(Debug, Clone)]
pub(crate) struct LambdaDiagnostic {
    /// `None` when the compilation is location-free: the caller must retry
    /// with locations rather than report a range it does not have.
    pub(crate) loc: Option<crate::location::Location>,
    pub(crate) message: String,
}

/// Direct port of the `handler` record in `Lam_compile_context`
/// (lam_compile_context.ml:78). Used by `flatten_nested_caches` to collect
/// multiple adjacent `Lstaticcatch` handlers into a single dispatch group.
#[derive(Debug, Clone)]
struct FlatHandler {
    label: i32,
    bindings: Vec<Ident>,
    handler: Lambda,
}

// OCaml's export coercion only reuses direct variables and module-field
// projections while folding `pairs` (`compiler/core/lam_coercion.ml:99-121`).
fn reusable_export_value_candidate(value: &Expression) -> bool {
    match &value.desc {
        ExpressionDesc::Var(_) => true,
        ExpressionDesc::StaticIndex(target, _, _) => reusable_export_value_candidate(target),
        _ => false,
    }
}

/// Direct port of `Lam_compile.flat_catches` + `flatten_nested_caches`
/// (lam_compile.ml:104-118).
///
/// Starting from the outermost `Lstaticcatch (outer_body, (outer_label,
/// outer_bindings), outer_handler)`, walks inward, collecting each adjacent
/// nested `Lstaticcatch` whose handler does NOT raise to any label already in
/// the accumulator (the #1698 safety check, lam_compile.ml:108-111). Returns
/// the collected handlers in **innermost-first** order, matching OCaml's
/// `acc` which prepends (lam_compile.ml:113), together with the residual body
/// that is no longer a flattenable `Lstaticcatch`.
fn flatten_nested_caches<'a>(
    outer_label: i32,
    outer_bindings: &[Ident],
    outer_body: &'a Lambda,
    outer_handler: &Lambda,
) -> (Vec<FlatHandler>, &'a Lambda) {
    // `acc` matches OCaml's `acc` parameter to `flat_catches`. OCaml starts
    // with `[]` and always absorbs the first (outermost) catch via the
    // `acc = []` branch of the when-clause. In Rust we skip that trivial
    // first step by seeding with the outermost handler.
    let mut acc: Vec<FlatHandler> = vec![FlatHandler {
        label: outer_label,
        bindings: outer_bindings.to_vec(),
        handler: outer_handler.clone(),
    }];
    let mut current: &Lambda = outer_body;
    loop {
        match current {
            Lambda::LstaticCatch(inner_body, (inner_label, inner_bindings), inner_handler) => {
                // lam_compile.ml:108-111 — "not (has_exit_code handler (fun exit ->
                // List.exists acc (fun x -> x.label = exit)))". OCaml also has
                // the `acc = []` short-circuit (lam_compile.ml:108) but after
                // our seeding step acc is never empty, so the safety check runs
                // unconditionally.
                if has_exit_code(inner_handler, |exit| acc.iter().any(|h| h.label == exit)) {
                    break;
                }
                acc.push(FlatHandler {
                    label: *inner_label,
                    bindings: inner_bindings.clone(),
                    handler: (**inner_handler).clone(),
                });
                current = inner_body;
            }
            _ => break,
        }
    }
    // OCaml's `acc` ends up with `[innermost; ...; outermost]` because each
    // recursion prepends (lam_compile.ml:113). Rust pushed with outermost-first,
    // so reverse to match OCaml's order — the `add_jmps` consumer iterates
    // this list with `fold_left_with_offset (cardinal + 1)`, assigning
    // sequential `order_id`s starting at innermost (lam_compile_context.ml:89-98).
    acc.reverse();
    (acc, current)
}

#[derive(Debug, Clone)]
pub(crate) struct StaticJumpHandler {
    pub(crate) label: i32,
    pub(crate) exit_id: Ident,
    pub(crate) exit_code: i32,
    pub(crate) bindings: Vec<Ident>,
}

#[derive(Debug, Clone)]
pub(crate) struct FallthroughReturnHandler {
    pub(crate) label: i32,
    pub(crate) bindings: Vec<Ident>,
}

#[derive(Debug, Clone)]
pub(crate) struct TailLoopState {
    pub(crate) tail_targets: Vec<Ident>,
    pub(crate) params: Vec<Ident>,
    pub(crate) new_params: AHashMap<Ident, Ident>,
    pub(crate) triggered: bool,
}

impl TailLoopState {
    fn new(tail_targets: Vec<Ident>, params: Vec<Ident>) -> Self {
        Self {
            tail_targets,
            params,
            new_params: AHashMap::new(),
            triggered: false,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ShortCircuitOp {
    And,
    Or,
}

impl ShortCircuitOp {
    fn default_expr(self) -> Expression {
        Expression::bool(matches!(self, Self::Or))
    }

    fn test_expr(self, lhs: Expression) -> Expression {
        match self {
            Self::And => lhs,
            Self::Or => Expression::not(lhs),
        }
    }

    fn default_lambda(self) -> Lambda {
        match self {
            Self::And => Lambda::false_(),
            Self::Or => Lambda::true_(),
        }
    }
}

fn direct_switch_int(key: SwitchKey) -> i32 {
    match key {
        SwitchKey::Int(value) => value,
        SwitchKey::Constructor(_) => unreachable!("constructor key with direct switch dispatch"),
    }
}

pub(crate) fn short_circuit_primitive<'a>(
    primitive: &'a Primitive,
    args: &'a [Lambda],
) -> Option<(ShortCircuitOp, &'a Lambda, &'a Lambda)> {
    match (primitive, args) {
        (Primitive::Psequand, [lhs, rhs]) => Some((ShortCircuitOp::And, lhs, rhs)),
        (Primitive::Psequor, [lhs, rhs]) => Some((ShortCircuitOp::Or, lhs, rhs)),
        _ => None,
    }
}

/// Direct port of `call_info_of_ap_status` (lam_compile.ml:34-40).
///
/// - `App_infer_full` → `{arity = Full; call_info = Call_ml}`.
/// - `App_na` → `{arity = NA; call_info = Call_ml}`.
/// - `App_uncurry` → `{arity = Full; call_info = Call_na}`.
///
/// The printer's eta-reduction rewrite (js_dump.ml:299-344) gates on
/// `call_info = Call_ml | Call_builtin_runtime` AND `arity = Full`.
pub(crate) fn call_info_of_apply_status(status: ApplyStatus) -> CallInfo {
    use crate::js_ir::{CallArity, CallKind};
    match status {
        ApplyStatus::InferFull => CallInfo {
            kind: CallKind::MlCall,
            arity: CallArity::Full,
            ..CallInfo::default()
        },
        ApplyStatus::Na => CallInfo {
            kind: CallKind::MlCall,
            arity: CallArity::Na,
            ..CallInfo::default()
        },
        ApplyStatus::Uncurry => CallInfo {
            kind: CallKind::Na,
            arity: CallArity::Full,
            ..CallInfo::default()
        },
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct ExternalModuleCacheKey {
    pub(crate) bundle: String,
    pub(crate) default: bool,
}

fn cmj_export_arity_to_external(info: CmjExportArity) -> ExternalArityInfo {
    match info {
        CmjExportArity::Single(arity) => ExternalArityInfo::Single(arity),
        CmjExportArity::Submodule(arities) => ExternalArityInfo::Submodule(arities),
    }
}

pub(crate) enum LambdaIdGenerator {
    Owned(IdGenerator),
    Shared(Arc<IdGenerator>),
}

impl std::ops::Deref for LambdaIdGenerator {
    type Target = IdGenerator;

    fn deref(&self) -> &Self::Target {
        match self {
            Self::Owned(generator) => generator,
            Self::Shared(generator) => generator,
        }
    }
}

struct SavedFunctionScope {
    switch_depth: i32,
    loop_stack: Vec<Option<String>>,
    static_handlers: Vec<StaticHandler>,
    static_jump_handlers: Vec<StaticJumpHandler>,
    fallthrough_return_handlers: Vec<FallthroughReturnHandler>,
    try_body_depth: usize,
}

/// Lambda compiler to JS IR.
pub struct LambdaCompiler {
    pub(crate) id_gen: LambdaIdGenerator,
    /// `Js_output.output_finished` of each `Lifthenelse` compiled in a
    /// return continuation, keyed by the address of its `then` branch: only
    /// the `return e ? a : b` arm sets it (lam_compile.ml:1514-1518).
    pub(crate) module_path_resolver: Option<ModulePathResolver>,
    pub(crate) jsx_preserve: bool,
    pub(crate) check_div_by_zero: bool,
    pub(crate) cross_module_inline: bool,
    pub(crate) source_map_enabled: bool,
    /// Intentional Rust performance cache for repeated `.cmj` resolver reads.
    ///
    /// OCaml keeps this metadata in Lam_compile_env and queries it through
    /// `query_external_id_info` during lowering
    /// (compiler/core/lam_compile.ml:234-244, 274-279). Rust's resolver can hit
    /// the filesystem, so cache the whole module export table, including
    /// misses, while keeping the same cross-module-inline gate from
    /// compiler/core/lam_stats_export.ml:53-63 and
    /// compiler/core/js_cmj_format.ml:120-128.
    pub(crate) cmj_constant_cache:
        AHashMap<String, Option<Arc<AHashMap<String, CmjExportConstant>>>>,
    pub(crate) cmj_arity_cache: AHashMap<String, Option<Arc<AHashMap<String, CmjExportArity>>>>,
    /// Same intentional cache family as above, but for exported lambda bodies.
    /// Keep this paired with the constant/arity caches so repeated cross-module
    /// inline probes do not re-read the same `.cmj` metadata
    /// (`query_external_id_info` in compiler/core/lam_compile.ml:234-244,
    /// 274-279).
    pub(crate) cmj_lambda_cache: AHashMap<String, Option<Arc<crate::lambda::CmjExportLambdas>>>,
    pub(crate) cmj_export_constants: AHashMap<String, CmjExportConstant>,
    /// Non-constant `persistent_closed_lambda` exports recorded for
    /// cross-module inlining (compiler/core/lam_stats_export.ml:53-89).
    pub(crate) cmj_export_lambdas: crate::lambda::CmjExportLambdas,
    pub(crate) cmj_export_arities: AHashMap<String, CmjExportArity>,
    /// `Translmod.implementation.flat_make_paths`.
    flat_make_paths: Vec<crate::lambda::FlatMakePath>,
    /// `Lam_stats.awaited_units`: locals bound to an awaited compilation
    /// unit, `let d = await import(Unit)`; reads of nested `make` values
    /// through them use the flat exports too.
    pub(crate) awaited_units: ahash::AHashSet<Ident>,
    /// Resolves the location handles of the Lambda being compiled and of the
    /// JS IR built from it; imported lambdas are rebased into it.
    lam_locs: LamLocTable,
    pub(crate) external_module_ids: AHashMap<ExternalModuleCacheKey, Ident>,
    /// Modules registered by dynamic imports (`Lam_compile_primitive`'s
    /// `Pimport` registers them in `Lam_compile_env.cached_tbl`), which feed
    /// `populate_required_modules` like every other cached module.
    pub(crate) dynamic_import_modules: Vec<ModuleId>,
    pub(crate) static_handlers: Vec<StaticHandler>,
    pub(crate) static_jump_handlers: Vec<StaticJumpHandler>,
    pub(crate) fallthrough_return_handlers: Vec<FallthroughReturnHandler>,
    pub(crate) return_unit_stack: Vec<bool>,
    pub(crate) try_body_depth: usize,
    /// Number of enclosing JS `switch` statements between the current
    /// expression and the closest enclosing loop. Mirrors OCaml
    /// `lambda_cxt.switch_depth`. Used to decide whether a `Lbreak` /
    /// `Lcontinue` must emit a labeled JS `break`/`continue`.
    pub(crate) switch_depth: i32,
    /// Stack of enclosing loops, innermost last. Each entry is the
    /// loop's lazily-allocated label slot (mirrors OCaml's
    /// `loop_frame`). Pushed when compiling `Lwhile`/`Lfor` bodies and
    /// popped after.
    pub(crate) loop_stack: Vec<Option<String>>,
    /// Counter used to mint unique JS labels (`loop_0`, `loop_1`, ...)
    /// on demand; reset per top-level group. Mirrors OCaml's
    /// `loop_label_counter`.
    pub(crate) loop_label_counter: i32,
    diagnostic: Option<LambdaDiagnostic>,
}

impl Default for LambdaCompiler {
    fn default() -> Self {
        Self::new()
    }
}

impl LambdaCompiler {
    pub(crate) fn grouped_switch_cases<'a, T: Clone, F>(
        &self,
        cases: &'a [(T, Lambda)],
        default: Option<&'a Lambda>,
        merge_cases: F,
    ) -> Vec<(T, &'a Lambda, bool)>
    where
        F: Fn(&T, &T) -> bool,
    {
        let filtered: Vec<_> = cases
            .iter()
            .filter(|(_, lam)| default.is_none_or(|default| !super::lambda_eq_approx(lam, default)))
            .map(|(tag, lam)| (tag.clone(), lam))
            .collect();

        stable_group_switch_cases(filtered, merge_cases)
    }

    pub(crate) fn filtered_switch_case_refs<'a, T: Clone>(
        &self,
        cases: &'a [(T, &'a Lambda)],
        default: Option<&'a Lambda>,
    ) -> Vec<(T, &'a Lambda)> {
        cases
            .iter()
            .filter(|(_, lam)| default.is_none_or(|default| !super::lambda_eq_approx(lam, default)))
            .map(|(tag, lam)| (tag.clone(), *lam))
            .collect()
    }

    /// A standalone compiler, as unit tests build one.
    ///
    /// OCaml draws every identifier from one `Ident.currentstamp`. A real
    /// compilation seeds the generator past every stamp in its input before
    /// lowering; here the input's identifiers come from `Ident::create_local`
    /// at arbitrary times, so the generator starts far above that counter and
    /// its temporaries never share a stamp (and so `Ident::same`) with them.
    pub fn new() -> Self {
        const STANDALONE_START_STAMP: i32 = 1 << 24;
        Self::with_generator_and_options(
            LambdaIdGenerator::Owned(IdGenerator::with_start_stamp(STANDALONE_START_STAMP)),
            None,
            false,
            true,
            false,
        )
    }

    fn with_generator_and_options(
        id_gen: LambdaIdGenerator,
        module_path_resolver: Option<ModulePathResolver>,
        jsx_preserve: bool,
        check_div_by_zero: bool,
        cross_module_inline: bool,
    ) -> Self {
        Self {
            id_gen,
            module_path_resolver,
            jsx_preserve,
            check_div_by_zero,
            cross_module_inline,
            source_map_enabled: false,
            cmj_constant_cache: AHashMap::new(),
            cmj_arity_cache: AHashMap::new(),
            cmj_lambda_cache: AHashMap::new(),
            cmj_export_constants: AHashMap::new(),
            cmj_export_lambdas: Default::default(),
            cmj_export_arities: AHashMap::new(),
            flat_make_paths: Vec::new(),
            awaited_units: ahash::AHashSet::new(),
            lam_locs: LamLocTable::opaque(),
            external_module_ids: AHashMap::new(),
            dynamic_import_modules: Vec::new(),
            static_handlers: Vec::new(),
            static_jump_handlers: Vec::new(),
            fallthrough_return_handlers: Vec::new(),
            return_unit_stack: Vec::new(),
            try_body_depth: 0,
            switch_depth: 0,
            loop_stack: Vec::new(),
            loop_label_counter: 0,
            diagnostic: None,
        }
    }

    pub(crate) fn with_shared_generator_and_options(
        id_gen: Arc<IdGenerator>,
        module_path_resolver: Option<ModulePathResolver>,
        jsx_preserve: bool,
        check_div_by_zero: bool,
        cross_module_inline: bool,
    ) -> Self {
        Self::with_generator_and_options(
            LambdaIdGenerator::Shared(id_gen),
            module_path_resolver,
            jsx_preserve,
            check_div_by_zero,
            cross_module_inline,
        )
    }

    /// Create a compiler with module import resolution context.
    pub fn with_module_path_resolver(module_path_resolver: Option<ModulePathResolver>) -> Self {
        Self::with_module_path_resolver_and_jsx_preserve(module_path_resolver, false)
    }

    /// Create a compiler with module import resolution context and JSX-preserve mode.
    pub fn with_module_path_resolver_and_jsx_preserve(
        module_path_resolver: Option<ModulePathResolver>,
        jsx_preserve: bool,
    ) -> Self {
        Self::with_module_path_resolver_and_options(module_path_resolver, jsx_preserve, true, false)
    }

    /// Create a compiler with the JS-backend options that affect lowering.
    pub fn with_module_path_resolver_and_options(
        module_path_resolver: Option<ModulePathResolver>,
        jsx_preserve: bool,
        check_div_by_zero: bool,
        cross_module_inline: bool,
    ) -> Self {
        Self::with_generator_and_options(
            LambdaIdGenerator::Owned(IdGenerator::new()),
            module_path_resolver,
            jsx_preserve,
            check_div_by_zero,
            cross_module_inline,
        )
    }

    pub fn set_flat_make_paths(&mut self, paths: Vec<crate::lambda::FlatMakePath>) {
        self.flat_make_paths = paths;
    }

    /// Compile a Lambda expression into a JS IR program.
    pub fn compile_program(&mut self, lam: &Lambda) -> Program {
        self.compile_deps_program(lam).program
    }

    /// Compile an owned Lambda expression into a JS IR program.
    pub fn compile_program_owned(&mut self, lam: Lambda) -> Program {
        self.compile_deps_program_owned(lam).program
    }

    /// Compile a Lambda expression into a JS IR program with module metadata.
    pub fn compile_deps_program(&mut self, lam: &Lambda) -> DepsProgram {
        self.compile_deps_program_owned(lam.clone())
    }

    /// Compile an owned Lambda expression into a JS IR program with module metadata.
    pub fn compile_deps_program_owned(&mut self, lam: Lambda) -> DepsProgram {
        let possible_required_modules = AHashSet::new();
        self.compile_deps_program_with_possible_required_modules_owned(
            lam,
            &possible_required_modules,
        )
    }

    /// Compile a Lambda expression into a JS IR program with module metadata
    /// and additional required modules captured before later coercion/simplify
    /// stages erase the original global-module reference.
    pub fn compile_deps_program_with_possible_required_modules(
        &mut self,
        lam: &Lambda,
        extra_possible_required_modules: &AHashSet<ModuleId>,
    ) -> DepsProgram {
        self.compile_deps_program_with_possible_required_modules_owned(
            lam.clone(),
            extra_possible_required_modules,
        )
    }

    /// Owned form of `compile_deps_program_with_possible_required_modules`.
    ///
    /// This follows the same `compiler/core/lam_compile_main.ml:148-200`
    /// simplify pipeline, but passes ownership into the Rust lambda passes so
    /// they can move the previous tree instead of cloning it first.
    pub fn compile_deps_program_with_possible_required_modules_owned(
        &mut self,
        lam: Lambda,
        extra_possible_required_modules: &AHashSet<ModuleId>,
    ) -> DepsProgram {
        let _span = info_span!(
            "compiler.lambda_to_js",
            extra_possible_required_modules = extra_possible_required_modules.len(),
            jsx_preserve = self.jsx_preserve
        )
        .entered();
        let mut possible_required_modules =
            crate::timing::measure(crate::timing::Phase::Codegen, || {
                let _phase = info_span!("compiler.lambda_collect_possible_modules").entered();
                collect_possible_required_modules_for_lambda(&lam)
            });
        possible_required_modules.extend(extra_possible_required_modules.iter().cloned());
        self.compile_deps_program_with_collected_possible_required_modules_owned(
            lam,
            possible_required_modules,
        )
    }

    pub fn compile_deps_program_with_collected_possible_required_modules_owned(
        &mut self,
        lam: Lambda,
        possible_required_modules: AHashSet<ModuleId>,
    ) -> DepsProgram {
        let _span = info_span!(
            "compiler.lambda_to_js_collected",
            possible_required_modules = possible_required_modules.len(),
            jsx_preserve = self.jsx_preserve
        )
        .entered();
        self.external_module_ids.clear();
        self.dynamic_import_modules.clear();
        let simplified_result = crate::timing::measure(
            crate::timing::Phase::LambdaOptimization,
            || {
                let _phase = info_span!("compiler.lambda_simplify").entered();
                let module_path_resolver = self.module_path_resolver.as_ref();
                let cross_module_inline = self.cross_module_inline;
                let mut cmj_lambda_cache: AHashMap<
                    String,
                    Option<Arc<crate::lambda::CmjExportLambdas>>,
                > = AHashMap::new();
                let lam_locs = &mut self.lam_locs;
                let mut cmj_arity_cache: AHashMap<
                    String,
                    Option<Arc<AHashMap<String, CmjExportArity>>>,
                > = AHashMap::new();
                let mut external_inline = |module_id: &Ident, field_name: &str| {
                    if !cross_module_inline {
                        return None;
                    }
                    cached_cmj_table(&mut cmj_lambda_cache, module_id.name(), || {
                        module_path_resolver.as_ref().and_then(|resolver| {
                            resolver.module_cmj_export_lambdas(module_id.name())
                        })
                    })?
                    .import(field_name, lam_locs)
                };
                let mut external_arity = |module_id: &Ident, field_name: &str| {
                    cached_cmj_table(&mut cmj_arity_cache, module_id.name(), || {
                        module_path_resolver.as_ref().and_then(|resolver| {
                            resolver.module_cmj_export_arities(module_id.name())
                        })
                    })?
                    .get(field_name)
                    .cloned()
                    .map(cmj_export_arity_to_external)
                };
                crate::lambda::lam_compile_main::simplify_for_js_backend_with_external_inline_and_meta_owned(
                    lam,
                    &mut external_inline,
                    &mut external_arity,
                )
            },
        );
        let simplified_result = crate::lambda::lam_compile_main::add_flat_make_aliases(
            simplified_result,
            &self.flat_make_paths,
        );
        // lam_compile_main.ml: `awaited_units = awaited_units groups`, after
        // the flat aliases are added.
        self.awaited_units =
            crate::lambda::lam_compile_main::awaited_units(&simplified_result.lambda);
        self.cmj_export_constants =
            collect_cmj_export_constants_from_simplified_lambda(&simplified_result.lambda);
        self.cmj_export_lambdas = if self.cross_module_inline {
            crate::lambda::CmjExportLambdas::export(
                collect_cmj_export_lambdas_from_simplified_lambda(&simplified_result.lambda),
                &self.lam_locs,
            )
        } else {
            Default::default()
        };
        self.cmj_export_arities = collect_cmj_export_arities_from_simplified_lambda(
            &simplified_result.lambda,
            &simplified_result.meta,
        );
        let simplified = drop_toplevel_pure_sequence_heads(simplified_result.lambda);
        // OCaml's `Ext_ident.create` allocations in lam_compile.ml share the
        // same global `Ident.currentstamp` as the Lambda identifiers entering
        // this phase. See compiler/core/lam_compile.ml:60, 771-782, 911 and
        // 1614. Seed Rust's JS-lowering generator past every existing Lambda
        // stamp before `compile_expr` creates temporary identifiers.
        let js_lowering_start_stamp =
            crate::lambda::lam_beta_reduce::max_ident_stamp_in_lambda(&simplified)
                .max(crate::ident::Ident::current_local_stamp());
        self.id_gen.set_current_stamp(js_lowering_start_stamp);
        crate::ident::Ident::set_current_time(js_lowering_start_stamp);
        crate::timing::measure(crate::timing::Phase::Codegen, || {
            let compiled = {
                let _phase = info_span!("compiler.lambda_compile_expr").entered();
                self.compile_expr(&simplified)
            };
            let mut block = compiled.prelude;
            let (exports, name_reservations) = {
                let _phase = info_span!("compiler.lambda_exports").entered();
                if let Some(mut exports) = extract_toplevel_exports(compiled.expr, &mut block) {
                    // lam_compile_main.ml:390-395: a finished toplevel output.
                    if compiled.finished == OutputFinished::True {
                        for value in &mut exports.values {
                            *value = Expression::undefined(false);
                        }
                    }
                    self.coerce_toplevel_exports_with_name_reservations(
                        &mut block,
                        exports,
                        compiled.finished,
                    )
                } else {
                    (vec![], vec![])
                }
            };
            // lam_compile_main.ml `declare_undeclared_exports`: when the
            // toplevel always throws, the groups after the throw are dropped
            // and the identifiers they bind are undeclared. Declare each such
            // exported identifier after the throw.
            if compiled.finished == OutputFinished::True {
                let declared: AHashSet<Ident> = block
                    .iter()
                    .filter_map(|stmt| match &stmt.desc {
                        StatementDesc::Variable(decl) => Some(decl.ident),
                        _ => None,
                    })
                    .collect();
                for id in &exports {
                    if !declared.contains(id) {
                        block.push(Statement::variable(VariableDeclaration {
                            ident: *id,
                            value: None,
                            property: LetKind::Strict,
                            ident_info: IdentInfo::default(),
                        }));
                    }
                }
            }
            let exports = resolve_export_aliases(&block, exports);
            let side_effect = module_side_effect_reason(&simplified);

            let mut deps = DepsProgram {
                program: Program::new_with_name_reservations(block, exports, name_reservations),
                modules: vec![],
                side_effect,
            };
            deps = {
                let _phase = info_span!("compiler.js_pass_flatten").entered();
                apply_js_flatten_pass(deps)
            };
            deps = {
                let _phase = info_span!("compiler.js_pass_external_shadow").entered();
                apply_external_shadow_pass(deps)
            };
            deps = {
                let _phase = info_span!("compiler.js_pass_tailcall_inline").entered();
                apply_js_tailcall_inline_pass(deps)
            };
            deps = {
                let _phase = info_span!("compiler.js_pass_record_rest").entered();
                apply_js_record_rest_pass(deps)
            };
            deps = {
                let _phase = info_span!("compiler.js_pass_flatten_mark_dead").entered();
                apply_js_flatten_and_mark_dead_pass(deps, self.jsx_preserve)
            };
            deps = {
                let _phase = info_span!("compiler.js_pass_shake").entered();
                apply_js_shake_pass(deps)
            };
            {
                let _phase = info_span!("compiler.js_required_modules").entered();
                let mut required_modules = self.collect_required_module_set(&deps.program.block);
                for module in std::mem::take(&mut self.dynamic_import_modules) {
                    if required_module_side_effect_reason(
                        self.module_path_resolver.as_ref(),
                        std::slice::from_ref(&module),
                    )
                    .is_some()
                    {
                        required_modules.insert(module);
                    }
                }
                populate_required_modules(
                    self.module_path_resolver.as_ref(),
                    &possible_required_modules,
                    &mut required_modules,
                );
                deps.modules = required_modules.to_vec();
                ocaml_sort_modules(&mut deps.modules);
                if deps.side_effect.is_none() {
                    deps.side_effect = required_module_side_effect_reason(
                        self.module_path_resolver.as_ref(),
                        &deps.modules,
                    );
                }
            }
            deps
        })
    }

    pub fn set_source_map_enabled(&mut self, enabled: bool) {
        self.source_map_enabled = enabled;
    }

    /// The Lambda/JS location table that resolves this compiler's handles.
    pub fn set_lam_locs(&mut self, lam_locs: LamLocTable) {
        self.lam_locs = lam_locs;
    }

    pub fn lam_locs(&self) -> &LamLocTable {
        &self.lam_locs
    }

    pub(crate) fn take_lam_locs(&mut self) -> LamLocTable {
        std::mem::take(&mut self.lam_locs)
    }

    /// Whether `loc` maps to a real source position (`Location.none` and
    /// ghost locations do not).
    fn mappable_loc(&self, loc: LamLoc) -> bool {
        self.lam_locs
            .get(loc)
            .is_some_and(|loc| !loc.loc_ghost && loc.loc_start.cnum >= 0)
    }

    pub(crate) fn source_loc(&self, loc: &LamLoc) -> Option<LamLoc> {
        (self.source_map_enabled && self.mappable_loc(*loc)).then_some(*loc)
    }

    pub(crate) fn source_loc_of_lam(&self, lam: &Lambda) -> Option<LamLoc> {
        if !self.source_map_enabled {
            return None;
        }
        fn find(lam: &Lambda) -> Option<LamLoc> {
            match lam {
                Lambda::Lapply(apply) => Some(apply.ap_info.loc),
                Lambda::Lprim(info) => Some(info.loc),
                Lambda::Lfunction(function) => Some(function.loc),
                Lambda::Llet(_, _, value, body) => find(value).or_else(|| find(body)),
                Lambda::Lletrec(_, body) | Lambda::Lsequence(_, body) => find(body),
                Lambda::LifThenElse(_, then_, _) => find(then_),
                Lambda::LstaticCatch(body, _, _)
                | Lambda::LtryWith(body, _, _)
                | Lambda::LtryFinally(body, _) => find(body),
                Lambda::LstringSwitch(_, cases, default) => cases
                    .first()
                    .and_then(|(_, body)| find(body))
                    .or_else(|| default.as_deref().and_then(find)),
                Lambda::Lswitch(_, switch) => switch
                    .sw_consts
                    .first()
                    .and_then(|(_, body)| find(body))
                    .or_else(|| switch.sw_blocks.first().and_then(|(_, body)| find(body)))
                    .or_else(|| switch.sw_failaction.as_deref().and_then(find)),
                Lambda::LstaticRaise(_, args) => args.first().and_then(find),
                Lambda::Lwhile(_, body)
                | Lambda::Lfor(_, _, _, _, body)
                | Lambda::Lfor_of(_, _, body)
                | Lambda::Lfor_await_of(_, _, body)
                | Lambda::Lassign(_, body) => find(body),
                Lambda::Lvar(_)
                | Lambda::LglobalModule(_)
                | Lambda::Lconst(_)
                | Lambda::Lbreak
                | Lambda::Lcontinue => None,
            }
        }
        find(lam).filter(|loc| self.mappable_loc(*loc))
    }

    pub(crate) fn take_cmj_export_constants(&mut self) -> AHashMap<String, CmjExportConstant> {
        std::mem::take(&mut self.cmj_export_constants)
    }

    pub(crate) fn take_cmj_export_lambdas(&mut self) -> crate::lambda::CmjExportLambdas {
        std::mem::take(&mut self.cmj_export_lambdas)
    }

    pub(crate) fn take_cmj_export_arities(&mut self) -> AHashMap<String, CmjExportArity> {
        std::mem::take(&mut self.cmj_export_arities)
    }

    pub(crate) fn take_module_path_resolver(&mut self) -> Option<ModulePathResolver> {
        self.module_path_resolver.take()
    }

    pub(crate) fn take_diagnostic(&mut self) -> Option<LambdaDiagnostic> {
        self.diagnostic.take()
    }

    pub(crate) fn report_diagnostic(&mut self, loc: &LamLoc, message: &str) {
        if self.diagnostic.is_none() {
            self.diagnostic = Some(LambdaDiagnostic {
                loc: self.lam_locs.get(*loc),
                message: message.to_string(),
            });
        }
    }

    fn coerce_toplevel_exports(
        &mut self,
        block: &mut Block,
        extracted: ExtractedExports,
        finished: OutputFinished,
    ) -> Vec<Ident> {
        self.coerce_toplevel_exports_with_name_reservations(block, extracted, finished)
            .0
    }

    fn coerce_toplevel_exports_with_name_reservations(
        &mut self,
        block: &mut Block,
        extracted: ExtractedExports,
        finished: OutputFinished,
    ) -> (Vec<Ident>, Vec<Ident>) {
        let mut max_stamp = max_ident_stamp_in_block(block);
        for export in &extracted.exports {
            max_stamp = max_stamp.max(export.stamp());
        }
        for value in &extracted.values {
            max_stamp = max_stamp.max(max_ident_stamp_in_expression(value));
        }
        self.id_gen.set_current_stamp(max_stamp);

        let mut declared = AHashSet::new();
        collect_declared_idents(block, &mut declared);
        let block_ended = finished == OutputFinished::True;

        let mut exports = Vec::with_capacity(extracted.exports.len());
        // OCaml `lam_coercion.ml` can replace an original export id with a
        // same-name different-stamp target (`compiler/core/lam_coercion.ml:100-110`)
        // or with `Ident.rename original_export_id`
        // (`compiler/core/lam_coercion.ml:140-156`). The JS printer then sees
        // the original id as occupying the base name and prints the selected
        // local as `$1`; carry those original ids as explicit reservations.
        let mut name_reservations = Vec::new();
        let mut rebound_exports = Vec::new();

        let extracted_len = extracted.exports.len();
        // OCaml's `compiler/core/lam_coercion.ml:82-121` folds over export ids
        // and lambda values, only allocating a renamed export when the branch
        // actually emits a rebound group (`compiler/core/lam_coercion.ml:113-120`
        // and `compiler/core/lam_coercion.ml:140-156`). Mirror that here: borrow
        // during classification and clone only for the selected output shape.
        for index in 0..extracted_len {
            let export = &extracted.exports[index];
            let value = &extracted.values[index];
            let later_exports = &extracted.exports[index + 1..];
            let exact_self_export = matches!(
                &value.desc,
                ExpressionDesc::Var(VIdent::Id(target)) if target.same(export)
            );
            // OCaml's `Lvar id` branch only changes the export list/set and
            // emits no rebound group when the value is already the same
            // physical identifier (`compiler/core/lam_coercion.ml:99-111`).
            // Keep that source binding in place instead of tail-moving it.
            if !exact_self_export {
                if let Some((late_value, property)) =
                    move_same_name_export_alias_to_export_tail(block, export, value)
                {
                    exports.push(*export);
                    rebound_exports.push(Statement::variable(VariableDeclaration {
                        ident: *export,
                        value: Some(late_value),
                        property,
                        ident_info: IdentInfo::default(),
                    }));
                    continue;
                }
            }
            if let ExpressionDesc::Var(VIdent::Id(target)) = &value.desc {
                if target.name() == export.name() {
                    if declared.contains(export) {
                        let selected =
                            if keeps_declared_same_name_function_export_alias(block, export) {
                                *export
                            } else {
                                resolve_declared_same_name_self_alias_target(block, export)
                                    .unwrap_or(*export)
                            };
                        if !selected.same(export) {
                            name_reservations.push(*export);
                        }
                        exports.push(selected);
                        continue;
                    }
                    if declared.contains(target) {
                        let resolved = resolve_tail_move_replacement_expression(
                            block,
                            &Expression::var(*target),
                            target,
                            false,
                        );
                        let selected = match resolved.desc {
                            ExpressionDesc::Var(VIdent::Id(resolved_target)) => resolved_target,
                            _ => *target,
                        };
                        if !selected.same(export) {
                            name_reservations.push(*export);
                        }
                        exports.push(selected);
                        continue;
                    }
                }
            }
            if matches!(&value.desc, ExpressionDesc::Undefined { .. })
                && ((declared.contains(export)
                    && can_reuse_existing_undefined_export_binding(block, export))
                    || block_ended)
            {
                exports.push(*export);
                continue;
            }
            if reusable_export_value_candidate(value) {
                // Same OCaml export fold as above: reusable same-name bindings
                // only arise from variable/module-field export values. See
                // compiler/core/lam_coercion.ml:99-121.
                if let Some((late_value, property)) =
                    move_reused_same_name_export_binding_to_export_tail(block, export, value)
                {
                    exports.push(*export);
                    rebound_exports.push(Statement::variable(VariableDeclaration {
                        ident: *export,
                        value: Some(late_value),
                        property,
                        ident_info: IdentInfo::default(),
                    }));
                    continue;
                }
                if keeps_declared_same_name_reusable_export_binding(block, export, value) {
                    exports.push(*export);
                    continue;
                }
                if let Some(reused) = reusable_same_name_export_binding(block, export, value) {
                    exports.push(reused);
                    continue;
                }
            }
            if let Some(inserted_export) = insert_rebound_export_before_equivalent_later_binding(
                block,
                export,
                value,
                later_exports,
            ) {
                exports.push(inserted_export);
                continue;
            }

            let rebound = self.id_gen.create(export.name());
            name_reservations.push(*export);
            let property = if matches!(&value.desc, ExpressionDesc::Var(VIdent::Id(_))) {
                LetKind::Alias
            } else {
                LetKind::Strict
            };
            exports.push(rebound);
            rebound_exports.push(Statement::variable(VariableDeclaration {
                ident: rebound,
                value: Some(value.clone()),
                property,
                ident_info: IdentInfo::default(),
            }));
        }

        // OCaml compiler/core/lam_coercion.ml:160-172 folds original flattened
        // groups back in front of rebound export groups and preserves that
        // order. Generated JS observes this, so these late bindings must not be
        // sorted by export-list order.
        block.extend(rebound_exports);
        (exports, name_reservations)
    }

    fn compile_apply_call(&mut self, apply: &Apply) -> Compiled {
        let mut compiled = self.compile_apply_call_inner(apply);
        if compiled.expr.source_loc.is_none() {
            compiled.expr.source_loc = self.source_loc(&apply.ap_info.loc);
        }
        compiled
    }

    fn compile_apply_call_inner(&mut self, apply: &Apply) -> Compiled {
        if apply.ap_info.status == ApplyStatus::Na {
            if let Lambda::Lapply(inner) = apply.ap_func.as_ref() {
                if inner.ap_info.status == ApplyStatus::Na {
                    let ap_info = apply.ap_info.clone();

                    let mut args = inner.ap_args.clone();
                    args.extend(apply.ap_args.iter().cloned());
                    let merged = Lambda::apply((*inner.ap_func).clone(), args, ap_info);
                    return self.compile_expr(&merged);
                }
            }
        }

        if let Some(compiled) = self.compile_external_field_apply(apply) {
            return compiled;
        }

        let mut prelude = vec![];
        let func = self.compile_expr(&apply.ap_func);
        prelude.extend(func.prelude);
        let mut args = Vec::new();
        for arg in &apply.ap_args {
            let compiled = self.compile_expr(arg);
            prelude.extend(compiled.prelude);
            args.push(compiled.expr);
        }

        Compiled {
            prelude,
            expr: Expression::call(
                func.expr,
                args,
                call_info_of_apply_status(apply.ap_info.status),
            ),
            finished: OutputFinished::False,
        }
    }

    fn resolve_cmj_module_field_lambda_any(
        &mut self,
        module: &ModuleId,
        field_name: &str,
    ) -> Option<Lambda> {
        if !matches!(module.kind, Kind::Ml) {
            return None;
        }

        let resolver = &self.module_path_resolver;
        cached_cmj_table(&mut self.cmj_lambda_cache, module.id.name(), || {
            resolver
                .as_ref()
                .and_then(|resolver| resolver.module_cmj_export_lambdas(module.id.name()))
        })?
        .import(field_name, &mut self.lam_locs)
    }

    fn resolve_cmj_module_field_lambda(
        &mut self,
        module: &ModuleId,
        field_name: &str,
    ) -> Option<Lambda> {
        if !self.cross_module_inline {
            return None;
        }
        self.resolve_cmj_module_field_lambda_any(module, field_name)
    }

    fn resolve_cmj_module_field_arity(
        &mut self,
        module: &ModuleId,
        field_name: &str,
    ) -> Option<Arity> {
        if !matches!(module.kind, Kind::Ml) {
            return None;
        }

        let resolver = &self.module_path_resolver;
        let arities = cached_cmj_table(&mut self.cmj_arity_cache, module.id.name(), || {
            resolver
                .as_ref()
                .and_then(|resolver| resolver.module_cmj_export_arities(module.id.name()))
        })?;
        match arities.get(field_name) {
            Some(CmjExportArity::Single(arity)) => Some(arity.clone()),
            Some(CmjExportArity::Submodule(_)) | None => None,
        }
    }

    fn module_field_apply_target<'a>(&self, lam: &'a Lambda) -> Option<(ModuleId, &'a str)> {
        let Lambda::Lprim(__prim202) = lam else {
            return None;
        };
        let crate::lambda::PrimInfo {
            primitive: Primitive::Pfield(_, crate::lambda::FieldDbgInfo::Module { name }),
            args,
            ..
        } = __prim202.as_ref()
        else {
            return None;
        };
        let [Lambda::LglobalModule(id)] = args.as_slice() else {
            return None;
        };
        Some((
            ModuleId {
                id: *id,
                kind: Kind::Ml,
                dynamic_import: false,
            },
            name.as_str(),
        ))
    }

    /// Imports an eligible CMJ function at the consumer query boundary and
    /// beta-reduces it against argument IDs already in the owning store.
    ///
    /// OCaml performs this after `query_external_id_info` and the
    /// same-length/inlineability guards in `lam_compile.ml:339-357`. The
    /// caller must run those guards before calling this method, so rejected
    /// candidates are never imported merely to inspect their payload.
    fn import_and_beta_indexed_cmj_function(
        &mut self,
        context: &mut IndexedLambdaContext,
        function: LFunction,
        args: &[NodeId],
    ) -> NodeId {
        assert_eq!(
            function.params.len(),
            args.len(),
            "indexed CMJ beta requires a fully applied function"
        );
        assert!(
            args.iter().all(|arg| context.store().contains(*arg)),
            "indexed CMJ beta argument is foreign or out of range"
        );

        let imported = context.import_cmj_function(function);
        let NodeSnapshot::Function(_, params, body, attr, _) = context.store().snapshot(imported)
        else {
            unreachable!("CMJ function import did not produce an indexed function")
        };
        debug_assert!(!attr.async_ && attr.directive.is_none());
        let exports = AHashSet::new();
        let (_, parameter_map) =
            is_closed_with_map_indexed(context.store(), &exports, &params, body);
        let mut diagnostics = IndexedBetaDiagnostics::default();
        let (store, metadata) = context.parts_mut();
        propagate_beta_reduce_with_map_indexed(
            store,
            metadata,
            &parameter_map,
            &params,
            body,
            args,
            &self.id_gen,
            &mut diagnostics,
        )
    }

    /// Performs the mutable part of indexed external-call lowering.
    ///
    /// The initial store inspection ends before the CMJ resolver is queried.
    /// A selected function is then imported into the same store and reduced
    /// with the original argument IDs. If the function is absent or rejected,
    /// the arity query runs afterwards, matching `lam_compile.ml:339-383`.
    fn prepare_indexed_external_field_apply(
        &mut self,
        context: &mut IndexedLambdaContext,
        application: NodeId,
    ) -> Option<PreparedIndexedExternalApply> {
        let (module, field_name, args, info) = {
            let NodeSnapshot::Apply(function, args, info) = context.store().snapshot(application)
            else {
                return None;
            };
            let NodeSnapshot::Prim(
                Primitive::Pfield(_, crate::lambda::FieldDbgInfo::Module { name }),
                field_args,
                _,
            ) = context.store().snapshot(function)
            else {
                return None;
            };
            let [base] = field_args.as_slice() else {
                return None;
            };
            let NodeSnapshot::GlobalModule(id) = context.store().snapshot(*base) else {
                return None;
            };
            (
                ModuleId {
                    id,
                    kind: Kind::Ml,
                    dynamic_import: false,
                },
                name,
                args,
                info,
            )
        };

        if let Some(Lambda::Lfunction(function)) =
            self.resolve_cmj_module_field_lambda(&module, &field_name)
            && function.params.len() == args.len()
            && lfunction_can_be_inlined(&function)
        {
            let reduced =
                self.import_and_beta_indexed_cmj_function(context, *function, args.as_slice());
            return Some(PreparedIndexedExternalApply::Reduced(reduced));
        }

        let known_arity = self.resolve_cmj_module_field_arity(&module, &field_name);
        Some(PreparedIndexedExternalApply::Call {
            module,
            field_name,
            args,
            info,
            known_arity,
        })
    }

    fn compile_external_field_apply(&mut self, apply: &Apply) -> Option<Compiled> {
        let (module, field_name) = self.module_field_apply_target(&apply.ap_func)?;

        if let Some(Lambda::Lfunction(func)) =
            self.resolve_cmj_module_field_lambda(&module, field_name)
        {
            if func.params.len() == apply.ap_args.len() && lfunction_can_be_inlined(&func) {
                // OCaml compiler/core/lam_compile.ml:275-290 inlines closed
                // `persistent_closed_lambda` functions from `.cmj` during
                // `compile_external_field_apply`, then beta-reduces them with
                // Lam_beta_reduce.propagate_beta_reduce_with_map.
                let exports = ahash::AHashSet::new();
                let (_, param_map) = is_closed_with_map(&exports, &func.params, &func.body);
                let mut ident_tbl = crate::lambda::lam_compile_context::IdentTable::new();
                let reduced =
                    crate::lambda::lam_beta_reduce::propagate_beta_reduce_with_map_and_meta_and_id_gen(
                        &mut ident_tbl,
                        &self.id_gen,
                        &param_map,
                        &func.params,
                        &func.body,
                        &apply.ap_args,
                    );
                return Some(self.compile_expr(&reduced));
            }
        }

        let known_arity = self.resolve_cmj_module_field_arity(&module, field_name);
        let mut prelude = Vec::new();
        let mut args = Vec::with_capacity(apply.ap_args.len());
        for arg in &apply.ap_args {
            let compiled = self.compile_expr(arg);
            prelude.extend(compiled.prelude);
            args.push(compiled.expr);
        }

        let func = Expression::qualified(module, Some(field_name.to_string()));
        let expr = match apply.ap_info.status {
            // compiler/core/lam_compile.ml:303-309 keeps the explicit
            // App_infer_full/App_uncurry call info instead of consulting CMJ
            // arity. In particular App_uncurry stays Call_na.
            ApplyStatus::InferFull | ApplyStatus::Uncurry => {
                Expression::call(func, args, call_info_of_apply_status(apply.ap_info.status))
            }
            // compiler/core/lam_compile.ml:310-316 uses
            // `ident_info.arity`; a known `Single` arity is lowered through
            // `apply_with_arity`, while missing/Submodule arity uses dummy
            // Call_na information.
            ApplyStatus::Na => match known_arity {
                Some(arity) if !arity.is_na() => self.apply_with_arity(func, arity, args),
                _ => Expression::call(func, args, CallInfo::default()),
            },
        };
        Some(Compiled {
            prelude,
            expr,
            finished: OutputFinished::False,
        })
    }

    fn apply_with_arity(
        &self,
        func: Expression,
        arity: Arity,
        args: Vec<Expression>,
    ) -> Expression {
        // Direct port of compiler/core/lam_compile.ml:42-79. The OCaml helper
        // repeatedly consumes known arity groups, emits `ml_full_call` for each
        // saturated group, eta-expands duplicable partial applications, and
        // falls back to dummy Call_na otherwise.
        fn aux(
            id_gen: &IdGenerator,
            func: Expression,
            mut arities: Vec<i32>,
            args: Vec<Expression>,
        ) -> Expression {
            let len = args.len();
            if len == 0 {
                return func;
            }

            if arities.is_empty() {
                return Expression::call(func, args, CallInfo::default());
            }

            let mut x = arities.remove(0);
            if x == 0 {
                x = 1;
            }
            let x_len = x as usize;
            if len >= x_len {
                let first_part = args[..x_len].to_vec();
                let continue_args = args[x_len..].to_vec();
                let call = Expression::call(
                    func,
                    first_part,
                    CallInfo {
                        kind: CallKind::MlCall,
                        arity: CallArity::Full,
                        ..CallInfo::default()
                    },
                );
                aux(id_gen, call, arities, continue_args)
            } else if args.iter().all(js_expr_no_side_effects) {
                let missing = x_len - len;
                let params: Vec<Ident> = (0..missing).map(|_| id_gen.create("param")).collect();
                let mut full_args = args;
                full_args.extend(params.iter().cloned().map(Expression::var));
                Expression::new(ExpressionDesc::Fun {
                    is_method: false,
                    params,
                    body: vec![Statement::return_(Expression::call(
                        func,
                        full_args,
                        CallInfo {
                            kind: CallKind::MlCall,
                            arity: CallArity::Full,
                            ..CallInfo::default()
                        },
                    ))],
                    env: Default::default(),
                    return_unit: false,
                    async_: false,
                    directive: None,
                })
            } else {
                Expression::call(func, args, CallInfo::default())
            }
        }

        aux(&self.id_gen, func, arity.extract_arity(), args)
    }

    fn try_statement(&self, body: Block, exn: &Ident, handler: Block) -> Statement {
        Statement::new(StatementDesc::Try(body, Some((*exn, handler)), None))
    }

    /// lam_compile.ml `compile_try` for `Ltryfinally`: an `Ltryfinally`
    /// around an `Ltrywith` is one JS `try`/`catch`/`finally`. `compile`
    /// compiles the body in the try's continuation; with a finally block the
    /// catch handler gets the body's context, since it is not in tail position
    /// either. The finally block is compiled in `EffectCall Not_tail`.
    fn compile_try_finally(
        &mut self,
        body: &Lambda,
        finally: &Lambda,
        mut compile: impl FnMut(&mut Self, &Lambda) -> Block,
    ) -> Statement {
        let (body, catch) = match body {
            Lambda::LtryWith(body, exn, handler) => (body.as_ref(), Some((exn, handler.as_ref()))),
            body => (body, None),
        };
        let body_block = compile(self, body);
        let catch = catch.map(|(exn, handler)| (*exn, compile(self, handler)));
        let finally_block = self.compile_effect_block(finally);
        Statement::new(StatementDesc::Try(body_block, catch, Some(finally_block)))
    }

    fn collect_record_spread_overrides<'a>(
        copy_id: &Ident,
        lam: &'a Lambda,
        overrides: &mut Vec<(&'a SetFieldDbgInfo, &'a Lambda)>,
    ) -> bool {
        match lam {
            Lambda::Lsequence(set, rest) => match set.as_ref() {
                Lambda::Lprim(__prim5)
                    if matches!(__prim5.as_ref(), PrimInfo {
                    primitive: Primitive::Psetfield(_, field_info),
                    args,
                    ..
                } if matches!(args.as_slice(), [Lambda::Lvar(id), _] if id == copy_id)) =>
                {
                    let PrimInfo {
                        primitive: Primitive::Psetfield(_, field_info),
                        args,
                        ..
                    } = __prim5.as_ref()
                    else {
                        unreachable!()
                    };

                    overrides.push((field_info, &args[1]));
                    Self::collect_record_spread_overrides(copy_id, rest, overrides)
                }
                _ => false,
            },
            Lambda::Lvar(id) => id == copy_id,
            _ => false,
        }
    }

    /// Port of `try_compile_record_spread` from
    /// `compiler/core/lam_compile.ml`: collapse a duplicated record followed
    /// by mutations of that copy into one spread object literal. Compiling the
    /// initializer and overrides from left to right preserves source effects.
    fn try_compile_record_spread(
        &mut self,
        copy_id: &Ident,
        value: &Lambda,
        body: &Lambda,
    ) -> Option<Compiled> {
        let Lambda::Lprim(__prim201) = value else {
            return None;
        };
        let PrimInfo {
            primitive: Primitive::Pduprecord,
            args,
            loc,
        } = __prim201.as_ref()
        else {
            return None;
        };
        let [init] = args.as_slice() else {
            return None;
        };

        let mut overrides = Vec::new();
        if !Self::collect_record_spread_overrides(copy_id, body, &mut overrides) {
            return None;
        }

        let Compiled {
            mut prelude,
            expr: init_expr,
            ..
        } = self.compile_expr(init);
        let mut props = Vec::with_capacity(overrides.len());
        for (field_info, override_lam) in overrides {
            let compiled = self.compile_expr(override_lam);
            prelude.extend(compiled.prelude);
            props.push((
                PropertyName::Lit(field_info.name().to_string()),
                compiled.expr,
            ));
        }

        // OCaml's fold builds object properties by prepending each compiled
        // override, so the final JS object stores them in reverse source order.
        props.reverse();
        Some(Compiled {
            prelude,
            // lam_compile.ml:1813-1815: `with_source_loc loc (E.obj ~dup:init_val props)`.
            expr: Expression {
                source_loc: self.source_loc(loc),
                ..Expression::new(ExpressionDesc::Object(crate::js_ir::object_entries(
                    Some(init_expr),
                    props,
                )))
            },
            finished: OutputFinished::False,
        })
    }

    pub(crate) fn compile_expr(&mut self, lam: &Lambda) -> Compiled {
        match lam {
            Lambda::Lvar(id) => Compiled {
                prelude: vec![],
                expr: Expression::var(*id),
                finished: OutputFinished::False,
            },
            Lambda::LglobalModule(id) => {
                let module = ModuleId {
                    id: *id,
                    kind: Kind::Ml,
                    dynamic_import: false,
                };
                Compiled {
                    prelude: vec![],
                    expr: Expression::qualified(module, None),
                    finished: OutputFinished::False,
                }
            }
            Lambda::Lconst(cst) => Compiled {
                prelude: vec![],
                expr: Self::compile_constant(cst),
                finished: OutputFinished::False,
            },
            Lambda::Lapply(apply) => {
                let mut compiled = self.compile_apply_call(apply);
                if compiled.expr.source_loc.is_none() {
                    compiled.expr.source_loc = self.source_loc(&apply.ap_info.loc);
                }
                compiled
            }
            Lambda::Lfunction(func) => {
                if let Some(expr) = self.compile_eta_wrapped_runtime_alias(func) {
                    return Compiled {
                        prelude: vec![],
                        expr,
                        finished: OutputFinished::False,
                    };
                }
                let params = if func.attr.one_unit_arg {
                    vec![]
                } else {
                    func.params.clone()
                };
                let body = self
                    .try_compile_identity_module_return_expr(&func.body)
                    .map(|expr| vec![Statement::return_(expr)])
                    .unwrap_or_else(|| {
                        // Mirror OCaml: nested function bodies start with a
                        // fresh `switch_depth = 0; loop_stack = []`.
                        self.with_function_scope(|this| {
                            this.with_return_unit_context(func.attr.return_unit, |that| {
                                that.compile_return_block(&func.body)
                            })
                        })
                    });
                let mut expr = Expression::new(ExpressionDesc::Fun {
                    is_method: false,
                    params,
                    body,
                    env: Default::default(),
                    return_unit: func.attr.return_unit,
                    async_: func.attr.async_,
                    directive: (func.attr.directive.clone()).map(Box::new),
                });
                // lam_compile.ml:1827-1829: `with_source_loc loc (E.ocaml_fun ...)`.
                expr.source_loc = self.source_loc(&func.loc);
                Compiled {
                    prelude: vec![],
                    expr,
                    finished: OutputFinished::False,
                }
            }
            Lambda::Llet(kind, id, value, body) => {
                if let Some(compiled) = self.try_compile_record_spread(id, value, body) {
                    return compiled;
                }

                // Mirror OCaml's per-Single counter reset
                // (`lam_compile_main.ml`): each top-level binding compiles
                // its RHS with `loop_label_counter = ref 0`. Inner Llets
                // inside an expression keep the surrounding counter (so
                // the OCaml flow naturally inherits across function bodies
                // within one Single group). Detect "top-level" by checking
                // whether the body is itself an Llet/Lletrec/Lsequence —
                // anything else means we're already inside an inner
                // expression context.
                let is_top_level_let = matches!(
                    body.as_ref(),
                    Lambda::Llet(..) | Lambda::Lletrec(..) | Lambda::Lsequence(..)
                ) || matches!(
                    body.as_ref(),
                    Lambda::Lprim(prim)
                        if matches!(prim.primitive, Primitive::Pmakeblock(TagInfo::ModuleExport(_), _))
                );
                let binding = if is_top_level_let {
                    self.with_fresh_loop_label_counter(|this| {
                        this.compile_let_binding_output(*kind, id, value)
                    })
                } else {
                    self.compile_let_binding_output(*kind, id, value)
                };
                // lam_compile.ml:1867-1877: the body is compiled, then
                // `append_output` keeps a finished binding alone.
                let body_compiled = self.compile_expr(body);
                let mut prelude = binding.block;
                if binding.finished == OutputFinished::True {
                    return Compiled {
                        prelude,
                        expr: body_compiled.expr,
                        finished: OutputFinished::True,
                    };
                }
                prelude.extend(body_compiled.prelude);
                Compiled {
                    prelude,
                    expr: body_compiled.expr,
                    finished: body_compiled.finished,
                }
            }
            Lambda::Lletrec(bindings, body) => {
                // Same as Llet: per-Recursive group, OCaml resets
                // `loop_label_counter` (`lam_compile_main.ml:77`).
                let is_top_level = matches!(
                    body.as_ref(),
                    Lambda::Llet(..) | Lambda::Lletrec(..) | Lambda::Lsequence(..)
                ) || matches!(
                    body.as_ref(),
                    Lambda::Lprim(prim)
                        if matches!(prim.primitive, Primitive::Pmakeblock(TagInfo::ModuleExport(_), _))
                );
                let recursive = if is_top_level {
                    self.with_fresh_loop_label_counter(|this| {
                        this.compile_recursive_bindings_output(bindings)
                    })
                } else {
                    self.compile_recursive_bindings_output(bindings)
                };
                // lam_compile.ml:1878-1895: the bindings, then the body, then
                // `append_output`.
                let body_compiled = self.compile_expr(body);
                let mut prelude = recursive.block;
                if recursive.finished == OutputFinished::True {
                    return Compiled {
                        prelude,
                        expr: body_compiled.expr,
                        finished: OutputFinished::True,
                    };
                }
                prelude.extend(body_compiled.prelude);
                Compiled {
                    prelude,
                    expr: body_compiled.expr,
                    finished: body_compiled.finished,
                }
            }
            Lambda::Lprim(info) => {
                if let Some((op, lhs, rhs)) = short_circuit_primitive(&info.primitive, &info.args) {
                    return self.compile_short_circuit_expr(op, lhs, rhs);
                }
                if let Some(compiled) = self.compile_flat_make_field(
                    &info.primitive,
                    super::lam_compile_input::LambdaInputs::Recursive(&info.args),
                ) {
                    return compiled;
                }
                let mut compiled = self.compile_primitive(&info.primitive, &info.args, &info.loc);
                // lam_compile.ml:1615-1634: only `compile_primitive_default`
                // wraps its result in `with_source_loc loc`.
                if compiled.expr.source_loc.is_none()
                    && primitive_uses_default_compilation(&info.primitive, &info.args)
                {
                    compiled.expr.source_loc = self.source_loc(&info.loc);
                }
                compiled
            }
            Lambda::Lswitch(scrut, switch) => self.compile_switch(scrut, switch),
            Lambda::LstringSwitch(scrut, cases, default) => {
                self.compile_string_switch(scrut, cases, default.as_deref())
            }
            Lambda::LstaticRaise(id, args) => {
                if let Some(output) = self.compile_static_raise_jump_output(*id, args) {
                    return Compiled {
                        prelude: output.block,
                        expr: Expression::undefined(false),
                        finished: output.finished,
                    };
                }
                if let Some(handler) = self.resolve_static_raise(*id, args) {
                    return self.compile_expr(&handler);
                }
                let expr = if let Some(arg) = args.first() {
                    self.compile_expr(arg).expr
                } else {
                    Expression::undefined(false)
                };
                Compiled {
                    prelude: vec![Statement::throw(expr)],
                    expr: Expression::undefined(false),
                    finished: OutputFinished::False,
                }
            }
            Lambda::LstaticCatch(body, (label, bindings), handler) => {
                // OCaml's `compile_staticcatch` (lam_compile.ml:937-1017)
                // gates pseudo-jmp on `EffectCall (Maybe_tail_is_return
                // (Tail_with_name {in_staticcatch=false}))`. `NeedValue _`,
                // which is what `compile_expr` models, takes the
                // explicit-jump arm at lam_compile.ml:978-993 unconditionally
                // (it allocates a tmp, assigns through it, then dispatches).
                // Take that path here; the `with_static_handler` inline
                // shortcut has no OCaml analog for NeedValue.
                let (handlers, flat_body) = flatten_nested_caches(*label, bindings, body, handler);
                if handlers.len() > 1 {
                    // lam_compile.ml:935 calls `flatten_nested_caches` at the
                    // top of `compile_staticcatch`; a `code_table` with >1
                    // entries goes through the multi-handler explicit-jump
                    // arm for `NeedValue` at lam_compile.ml:978-988.
                    // OCaml NeedValue staticcatch allocates `Ext_ident.create_tmp ()`
                    // for the result (compiler/core/lam_compile.ml:1027-1034).
                    let result = self.fresh_tmp_ident();
                    let mut prelude = vec![Statement::variable(VariableDeclaration {
                        ident: result,
                        value: None,
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    })];
                    prelude.extend(
                        self.compile_multi_staticcatch_assignment_block(
                            &result, &handlers, flat_body,
                        ),
                    );
                    Compiled {
                        prelude,
                        expr: Expression::var(result),
                        finished: OutputFinished::False,
                    }
                } else {
                    self.compile_staticcatch_expr(*label, bindings, body, handler)
                }
            }
            Lambda::LtryWith(body, exn, handler) => {
                let result = self.fresh_tmp_ident();
                let mut prelude = vec![Statement::variable(VariableDeclaration {
                    ident: result,
                    value: None,
                    property: LetKind::Variable,
                    ident_info: IdentInfo::default(),
                })];
                let body_block = self.compile_assign_to_target_block(&result, body);
                let handler_block = self.compile_assign_to_target_block(&result, handler);
                prelude.push(self.try_statement(body_block, exn, handler_block));
                Compiled {
                    prelude,
                    expr: Expression::var(result),
                    finished: OutputFinished::False,
                }
            }
            Lambda::LtryFinally(body, finally) => {
                let result = self.fresh_tmp_ident();
                let mut prelude = vec![Statement::variable(VariableDeclaration {
                    ident: result,
                    value: None,
                    property: LetKind::Variable,
                    ident_info: IdentInfo::default(),
                })];
                prelude.push(self.compile_try_finally(body, finally, |this, lam| {
                    this.compile_assign_to_target_block(&result, lam)
                }));
                Compiled {
                    prelude,
                    expr: Expression::var(result),
                    finished: OutputFinished::False,
                }
            }
            Lambda::LifThenElse(cond, then_, else_) => {
                let cond_compiled = self.compile_expr(cond);
                let mut prelude = cond_compiled.prelude;
                let then_compiled = self.compile_expr(then_);
                let else_compiled = self.compile_expr(else_);
                if then_compiled.prelude.is_empty() && else_compiled.prelude.is_empty() {
                    Compiled {
                        prelude,
                        expr: Expression::cond(
                            cond_compiled.expr,
                            then_compiled.expr,
                            else_compiled.expr,
                        ),
                        finished: OutputFinished::False,
                    }
                } else {
                    let tmp = self.fresh_tmp_ident();
                    let then_block = self.compile_assign_to_target_block(&tmp, then_);
                    let else_block = self.compile_assign_to_target_block(&tmp, else_);
                    prelude.push(Statement::variable(VariableDeclaration {
                        ident: tmp,
                        value: None,
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    }));
                    prelude.push(Statement::if_(cond_compiled.expr, then_block, else_block));
                    Compiled {
                        prelude,
                        expr: Expression::var(tmp),
                        finished: OutputFinished::False,
                    }
                }
            }
            Lambda::Lsequence(a, b) => {
                // Mirror OCaml's per-Nop counter reset: a top-level
                // sequence (its tail is itself a top-level construct)
                // compiles its head with a fresh `loop_label_counter`,
                // matching `Lam_compile_main.compile_lambda` for `Nop`
                // groups (`lam_compile_main.ml:86`).
                let head_is_top_level = matches!(
                    b.as_ref(),
                    Lambda::Llet(..) | Lambda::Lletrec(..) | Lambda::Lsequence(..)
                ) || matches!(
                    b.as_ref(),
                    Lambda::Lprim(prim)
                        if matches!(prim.primitive, Primitive::Pmakeblock(TagInfo::ModuleExport(_), _))
                );
                let first = if head_is_top_level {
                    self.with_fresh_loop_label_counter(|this| this.compile_effect_output(a))
                } else {
                    self.compile_effect_output(a)
                };
                // lam_compile.ml:1905-1910: both parts are compiled, then
                // `append_output` drops the second after a finished first.
                let second = self.compile_expr(b);
                self.append_effect_output(first, second)
            }
            Lambda::Lwhile(cond, body) => {
                let cond_compiled = self.compile_expr(cond);
                let cond_expr =
                    block_with_return_expr_iife(cond_compiled.prelude, cond_compiled.expr);
                // Mirror OCaml's `push_loop` (compiler/core/lam_compile.ml):
                // a fresh loop frame is pushed before compiling the body;
                // its label is filled in lazily if a nested switch needs
                // labeled break/continue.
                self.push_loop();
                let body_block = self.compile_block(body);
                let label = self.pop_loop();
                Compiled {
                    prelude: vec![Statement::while_with_label(label, cond_expr, body_block)],
                    expr: Expression::undefined(false),
                    finished: OutputFinished::False,
                }
            }
            Lambda::Lfor(var, start, end, dir, body) => {
                self.compile_for_loop(var, start, end, dir, body)
            }
            // Upstream #7887: `for ... of` / `for await ... of` lower to a
            // dedicated JS for-of statement. The body is compiled with a
            // fresh loop frame pushed (so nested break/continue resolve to
            // this loop) and `switch_depth = 0` reset to match OCaml's
            // `compile_for_of` (`compiler/core/lam_compile.ml`).
            Lambda::Lfor_of(var, iterable, body) => {
                self.compile_for_of(var, iterable, body, /*await=*/ false)
            }
            Lambda::Lfor_await_of(var, iterable, body) => {
                self.compile_for_of(var, iterable, body, /*await=*/ true)
            }
            Lambda::Lbreak => {
                // OCaml: see compiler/core/lam_compile.ml `Lbreak` arm.
                // When inside a switch, target the enclosing loop with a
                // labeled `break` so we don't break out of the switch.
                assert!(
                    !self.loop_stack.is_empty(),
                    "Lbreak outside a loop — typecore should reject this"
                );
                let stmt = if self.switch_depth > 0 {
                    let label = self.ensure_current_loop_label();
                    Statement::break_label(Some(label))
                } else {
                    Statement::break_()
                };
                // lam_compile.ml:1934, 1949: `~output_finished:True`.
                Compiled {
                    prelude: vec![stmt],
                    expr: Expression::undefined(false),
                    finished: OutputFinished::True,
                }
            }
            Lambda::Lcontinue => {
                assert!(
                    !self.loop_stack.is_empty(),
                    "Lcontinue outside a loop — typecore should reject this"
                );
                let stmt = if self.switch_depth > 0 {
                    let label = self.ensure_current_loop_label();
                    Statement::continue_label(Some(label))
                } else {
                    Statement::continue_()
                };
                // lam_compile.ml:1934, 1949: `~output_finished:True`.
                Compiled {
                    prelude: vec![stmt],
                    expr: Expression::undefined(false),
                    finished: OutputFinished::True,
                }
            }
            Lambda::Lassign(id, value) => {
                // lam_compile.ml:1320-1334 `compile_assign`: the assignment
                // is appended to the value's block unconditionally.
                let compiled = self.compile_expr(value);
                let mut prelude = compiled.prelude;
                prelude.push(Statement::exp(Expression::bin(
                    BinOp::Eq,
                    Expression::var(*id),
                    compiled.expr,
                )));
                Compiled {
                    prelude,
                    expr: Expression::undefined(false),
                    finished: OutputFinished::False,
                }
            }
        }
    }

    fn compile_block(&mut self, lam: &Lambda) -> Block {
        self.compile_effect_block(lam)
    }

    /// Run `f` with `switch_depth` temporarily incremented. Mirrors
    /// OCaml's `enter_switch` shadowing in `compile_switch`.
    pub(crate) fn with_switch_depth<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        self.switch_depth += 1;
        let result = f(self);
        self.switch_depth -= 1;
        result
    }

    /// Run `f` with function-local control-flow state reset. Used when
    /// entering a fresh function body.
    pub(crate) fn with_function_scope<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        // OCaml reference: compiler/core/lam_compile.ml:1840-1858 rebuilds
        // the nested-function context with `jmp_table =
        // Lam_compile_context.empty_handler_map`, `switch_depth = 0`, and
        // `loop_stack = []`. Staticcatch jump tables cannot cross function
        // boundaries, so the Rust handler stacks must be cleared here too.
        let saved = self.enter_function_scope();
        let result = f(self);
        self.leave_function_scope(saved);
        result
    }

    fn enter_function_scope(&mut self) -> SavedFunctionScope {
        SavedFunctionScope {
            switch_depth: std::mem::replace(&mut self.switch_depth, 0),
            loop_stack: std::mem::take(&mut self.loop_stack),
            static_handlers: std::mem::take(&mut self.static_handlers),
            static_jump_handlers: std::mem::take(&mut self.static_jump_handlers),
            fallthrough_return_handlers: std::mem::take(&mut self.fallthrough_return_handlers),
            try_body_depth: std::mem::replace(&mut self.try_body_depth, 0),
        }
    }

    fn leave_function_scope(&mut self, saved: SavedFunctionScope) {
        self.switch_depth = saved.switch_depth;
        self.loop_stack = saved.loop_stack;
        self.static_handlers = saved.static_handlers;
        self.static_jump_handlers = saved.static_jump_handlers;
        self.fallthrough_return_handlers = saved.fallthrough_return_handlers;
        self.try_body_depth = saved.try_body_depth;
    }

    /// Run `f` with a fresh `loop_label_counter`. Mirrors OCaml's
    /// per-`Single` / per-`Recursive` / per-`Nop` reset in
    /// `lam_compile_main.ml`: each top-level group starts label numbering
    /// from `loop_0`, so cross-group labels never collide and the JS
    /// labels reset between unrelated declarations.
    pub(crate) fn with_fresh_loop_label_counter<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        let saved = std::mem::replace(&mut self.loop_label_counter, 0);
        let result = f(self);
        self.loop_label_counter = saved;
        result
    }

    /// Push a fresh loop frame onto the stack (mirrors OCaml's
    /// `push_loop`). Its label slot is filled only if
    /// [`Self::ensure_current_loop_label`] is called from inside the body.
    pub(crate) fn push_loop(&mut self) {
        self.loop_stack.push(None);
    }

    /// Pop the innermost loop frame, returning its label if one was
    /// allocated while compiling the body.
    pub(crate) fn pop_loop(&mut self) -> Option<String> {
        self.loop_stack
            .pop()
            .expect("pop_loop without a matching push_loop")
    }

    /// Lazily allocate a JS label for the innermost loop frame. Mirrors
    /// OCaml's `ensure_loop_label`. Idempotent: subsequent calls return
    /// the same label.
    pub(crate) fn ensure_current_loop_label(&mut self) -> String {
        let next_id = self.loop_label_counter;
        let slot = self
            .loop_stack
            .last_mut()
            .expect("loop label requested outside a loop");
        if let Some(existing) = slot {
            return existing.clone();
        }
        self.loop_label_counter = next_id + 1;
        let label = format!("loop_{next_id}");
        *slot = Some(label.clone());
        label
    }

    fn compile_for_loop(
        &mut self,
        var: &Ident,
        start: &Lambda,
        end: &Lambda,
        dir: &crate::lambda::DirectionFlag,
        body: &Lambda,
    ) -> Compiled {
        let start_compiled = self.compile_expr(start);
        let (finish, direction) = lower_ocaml_for_range_direction(dir, end);
        let finish_compiled = self.compile_expr(finish);
        // Push a fresh loop frame before compiling the body so any
        // nested `Lbreak`/`Lcontinue` resolves against this for-loop.
        // See OCaml `push_loop` in compiler/core/lam_compile.ml.
        self.push_loop();
        let body_block = self.compile_block(body);
        let loop_label = self.pop_loop();

        let mut prelude = start_compiled.prelude;

        let push_loop = |block: &mut Block, init: Option<Expression>, finish: Expression| {
            block.push(Statement::for_range(
                loop_label.clone(),
                init,
                finish,
                *var,
                direction,
                body_block.clone(),
            ));
        };

        if finish_compiled.prelude.is_empty() {
            push_loop(
                &mut prelude,
                Some(start_compiled.expr),
                finish_compiled.expr,
            );
        } else if js_expr_no_side_effects(&start_compiled.expr) {
            prelude.extend(finish_compiled.prelude);
            push_loop(
                &mut prelude,
                Some(start_compiled.expr),
                finish_compiled.expr,
            );
        } else {
            prelude.push(Statement::variable(VariableDeclaration {
                ident: *var,
                value: Some(start_compiled.expr),
                property: LetKind::Variable,
                ident_info: IdentInfo::default(),
            }));
            prelude.extend(finish_compiled.prelude);
            push_loop(&mut prelude, None, finish_compiled.expr);
        }

        Compiled {
            prelude,
            expr: Expression::undefined(false),
            finished: OutputFinished::False,
        }
    }

    /// Compile a `Lfor_of` / `Lfor_await_of` lambda. Mirrors OCaml
    /// `compile_for_of` / `compile_for_await_of` in
    /// `compiler/core/lam_compile.ml` (#7887): evaluate the iterable, push
    /// a fresh loop frame, compile the body and emit a JS `for-of` /
    /// `for await ... of` statement. If the loop variable is unused in the
    /// body, mint a fresh `_for_of` / `_for_await_of` placeholder so JS
    /// dump output matches OCaml.
    fn compile_for_of(
        &mut self,
        var: &Ident,
        iterable: &Lambda,
        body: &Lambda,
        await_kw: bool,
    ) -> Compiled {
        let iterable_compiled = self.compile_expr(iterable);
        let mut prelude = iterable_compiled.prelude;

        // Match OCaml: when the loop variable is not actually used by the
        // body, emit a fresh placeholder so the source name doesn't leak.
        let body_fvs = crate::lambda::lam_free_variables::free_variables(body);
        let emitted_id = if body_fvs.contains(var) {
            *var
        } else if await_kw {
            self.fresh_ident("_for_await_of")
        } else {
            self.fresh_ident("_for_of")
        };

        self.push_loop();
        let body_block = self.compile_block(body);
        let label = self.pop_loop();

        let stmt = if await_kw {
            Statement::for_await_of(label, emitted_id, iterable_compiled.expr, body_block)
        } else {
            Statement::for_of(label, emitted_id, iterable_compiled.expr, body_block)
        };
        prelude.push(stmt);

        Compiled {
            prelude,
            expr: Expression::undefined(false),
            finished: OutputFinished::False,
        }
    }

    /// lam_compile.ml:521-539 `compile_recursive_lets_aux`: the bindings are
    /// compiled with `Ext_list.fold_right`, so the last one first, each
    /// output is `append_output`ed onto the outputs after it (starting from
    /// `Js_output.dummy`), and the collected placeholder declarations are
    /// put in front.
    fn compile_recursive_bindings_output(&mut self, bindings: &[(Ident, Lambda)]) -> BlockOutput {
        let dependencies = recursive_binding_dependencies(bindings);
        let groups = recursive_binding_groups(bindings, &dependencies);
        let mut output = BlockOutput::dummy();
        for group in groups.iter().rev() {
            if let [index] = group.as_slice() {
                if !dependencies[*index].contains(index) {
                    let (id, expr) = &bindings[*index];
                    // OCaml's `compile_recursive_let` (lam_compile.ml:380-486)
                    // routes every non-self-referencing binding through
                    // `Declare(Alias, id)`. Using `Strict` here breaks the
                    // `js_pass_flatten_and_mark_dead` skip for all-deep-constant
                    // alias bindings (lam_pass_lets_dce.ml + the implicit
                    // skip behind the Variable arm).
                    let code = self.compile_let_binding_output(LetKind::Alias, id, expr);
                    output = code.append(output);
                    continue;
                }
            }

            let recursive_functions = recursive_function_bindings_in_group(bindings, group);
            let recursive_function_tail_targets = direct_recursive_function_tail_targets_with_group(
                bindings,
                group,
                &recursive_functions,
            );
            let recursive_function_ids: AHashSet<_> =
                recursive_function_tail_targets.keys().cloned().collect();
            let mut group_output = BlockOutput::dummy();
            let mut declarations = vec![];
            for &index in group.iter().rev() {
                let (id, expr) = &bindings[index];
                let (code, binding_declarations) = self.compile_recursive_binding(
                    id,
                    expr,
                    bindings,
                    group,
                    recursive_function_tail_targets
                        .get(id)
                        .map(Vec::as_slice)
                        .unwrap_or(&[]),
                    &recursive_functions,
                    &recursive_function_ids,
                );
                group_output = code.append(group_output);
                // `Ext_list.append declare_ids ids`.
                let mut later = std::mem::take(&mut declarations);
                declarations = binding_declarations;
                declarations.append(&mut later);
            }
            if !declarations.is_empty() {
                group_output = BlockOutput::make(declarations).append(group_output);
            }
            output = group_output.append(output);
        }
        output
    }

    fn compile_recursive_binding(
        &mut self,
        id: &Ident,
        expr: &Lambda,
        all_bindings: &[(Ident, Lambda)],
        group: &[usize],
        tail_targets: &[Ident],
        recursive_functions: &AHashMap<Ident, LFunction>,
        recursive_function_ids: &AHashSet<Ident>,
    ) -> (BlockOutput, Block) {
        if let Some(func) = recursive_function_binding_value(expr) {
            return (
                BlockOutput::make(vec![Statement::variable(VariableDeclaration {
                    ident: *id,
                    value: Some(self.compile_recursive_function_expr(id, &func, tail_targets)),
                    property: LetKind::Alias,
                    ident_info: IdentInfo::default(),
                })]),
                vec![],
            );
        }

        if let Some(target) = recursive_function_binding_alias_target(expr, recursive_functions) {
            if recursive_function_ids
                .iter()
                .any(|function_id| target.same(function_id))
            {
                return (
                    BlockOutput::make(vec![Statement::variable(VariableDeclaration {
                        ident: *id,
                        value: Some(Expression::var(target)),
                        property: LetKind::Alias,
                        ident_info: IdentInfo::default(),
                    })]),
                    vec![],
                );
            }
        }

        if group.len() == 1 {
            if let Some(output) =
                self.try_compile_recursive_singleton_binding_without_placeholder(id, expr)
            {
                return (output, vec![]);
            }
        }

        match expr {
            Lambda::Lprim(info)
                if matches!(info.primitive, Primitive::Pmakeblock(_, _))
                    && info
                        .args
                        .iter()
                        .all(|arg| matches!(arg, Lambda::Lfunction(_) | Lambda::Lconst(_))) =>
            {
                // lam_compile.ml:429-431: `compile_lambda` under
                // `Declare (Alias, id)`.
                let compiled = self.compile_expr(expr);
                (declare_compiled(LetKind::Alias, id, compiled), vec![])
            }
            Lambda::Lprim(info) if matches!(info.primitive, Primitive::Pmakeblock(_, _)) => {
                if let Some(effects) =
                    self.compile_recursive_self_binding_makeblock(id, info, all_bindings, group)
                {
                    return (BlockOutput::make(effects), vec![]);
                }

                let tag_info = match &info.primitive {
                    Primitive::Pmakeblock(tag_info, _) => tag_info,
                    _ => unreachable!("guard must preserve Pmakeblock"),
                };
                // lam_compile.ml:479-495: `NeedValue Not_tail`, then
                // `Js_output.make (b @ [updateDummy])`, which is not finished.
                let compiled = self.compile_expr(expr);
                let mut effects = compiled.prelude;
                effects.push(Statement::exp(self.runtime_call_expr(
                    "Primitive_object",
                    "updateDummy",
                    vec![Expression::var(*id), compiled.expr],
                )));
                (
                    BlockOutput::make(effects),
                    vec![Statement::variable(VariableDeclaration {
                        ident: *id,
                        value: Some(Self::recursive_dummy_object_expr(tag_info)),
                        property: LetKind::Variable,
                        ident_info: IdentInfo::default(),
                    })],
                )
            }
            _ => {
                // OCaml `compile_recursive_let`'s catch-all compiles directly
                // under `Declare (Alias, id)` (lam_compile.ml:497-519): the
                // value's prelude precedes a normal declaration, and a
                // finished value keeps no declaration.
                let compiled = self.compile_expr(expr);
                (declare_compiled(LetKind::Alias, id, compiled), vec![])
            }
        }
    }

    fn try_compile_recursive_singleton_binding_without_placeholder(
        &mut self,
        id: &Ident,
        expr: &Lambda,
    ) -> Option<BlockOutput> {
        if !matches!(expr, Lambda::Llet(..)) {
            return None;
        }

        let output = self.compile_let_binding_output(LetKind::Alias, id, expr);
        if block_declares_initialized_ident(&output.block, id) {
            Some(output)
        } else {
            None
        }
    }

    fn compile_recursive_self_binding_makeblock(
        &self,
        id: &Ident,
        info: &crate::lambda::PrimInfo,
        all_bindings: &[(Ident, Lambda)],
        group: &[usize],
    ) -> Option<Block> {
        let tag_info = match &info.primitive {
            Primitive::Pmakeblock(tag_info, _) => tag_info,
            _ => return None,
        };

        if !matches!(
            tag_info,
            TagInfo::Record { .. }
                | TagInfo::Constructor {
                    num_nonconst: 1,
                    ..
                }
                | TagInfo::RecordInlined {
                    num_nonconst: 1,
                    ..
                }
        ) {
            return None;
        }

        let only_self_or_captured = info.args.iter().all(|arg| match arg {
            Lambda::Lvar(binding) => {
                binding.same(id)
                    || !group.iter().any(|&index| {
                        let (other, _) = &all_bindings[index];
                        other.same(binding) && !other.same(id)
                    })
            }
            Lambda::Lconst(_) => true,
            _ => false,
        });
        if !only_self_or_captured {
            return None;
        }

        let mut block = vec![Statement::variable(VariableDeclaration {
            ident: *id,
            value: Some(Self::recursive_dummy_object_expr(tag_info)),
            property: LetKind::Variable,
            ident_info: IdentInfo::default(),
        })];

        for (index, arg) in info.args.iter().enumerate() {
            let field_info = Self::recursive_self_binding_field_info(tag_info, index)?;
            let value = match arg {
                Lambda::Lvar(binding) => Expression::var(*binding),
                Lambda::Lconst(constant) => Self::compile_constant(constant),
                _ => return None,
            };
            block.push(Statement::exp(self.compile_set_field(
                index as i32,
                &field_info,
                &Expression::var(*id),
                &value,
            )));
        }

        Some(block)
    }

    fn recursive_dummy_object_expr(tag_info: &TagInfo) -> Expression {
        match tag_info {
            TagInfo::Record { .. }
            | TagInfo::Module(_)
            | TagInfo::Constructor { .. }
            | TagInfo::RecordInlined { .. }
            | TagInfo::PolyVar(_)
            | TagInfo::Extension
            | TagInfo::RecordExt { .. } => Expression::new(ExpressionDesc::Object(vec![])),
            TagInfo::Tuple | TagInfo::ModuleExport(_) => {
                Expression::array(vec![], MutableFlag::Mutable)
            }
            TagInfo::Some | TagInfo::SomeNotNested => {
                panic!("unexpected option block in recursive dummy-object lowering")
            }
        }
    }

    fn recursive_self_binding_field_info(
        tag_info: &TagInfo,
        index: usize,
    ) -> Option<SetFieldDbgInfo> {
        match tag_info {
            TagInfo::Record { fields, .. } => fields
                .get(index)
                .map(|(name, _)| SetFieldDbgInfo::RecordSet(name.clone())),
            TagInfo::RecordInlined { fields, .. } => fields
                .get(index)
                .map(|(name, _)| SetFieldDbgInfo::RecordInlineSet(name.clone())),
            TagInfo::Constructor { name, .. } => {
                Some(SetFieldDbgInfo::RecordInlineSet(if name == "::" {
                    match index {
                        0 => "hd".to_string(),
                        1 => "tl".to_string(),
                        _ => format!("_{}", index),
                    }
                } else {
                    format!("_{}", index)
                }))
            }
            _ => None,
        }
    }

    fn compile_let_binding(&mut self, kind: LetKind, id: &Ident, value: &Lambda) -> Block {
        self.compile_let_binding_output(kind, id, value).block
    }

    /// `compile_lambda {cxt with continuation = Declare (kind, id)} value`.
    fn compile_let_binding_output(
        &mut self,
        kind: LetKind,
        id: &Ident,
        value: &Lambda,
    ) -> BlockOutput {
        match value {
            Lambda::Llet(inner_kind, inner_id, inner_value, body) => {
                // lam_compile.ml:1867-1877: compile the binding, then the
                // body, then `append_output`.
                let binding = self.compile_let_binding_output(*inner_kind, inner_id, inner_value);
                let body = self.compile_let_binding_output(kind, id, body);
                binding.append(body)
            }
            Lambda::LstaticCatch(body, (label, bindings), handler) => {
                // OCaml's `compile_staticcatch` (lam_compile.ml:937-1017)
                // gates pseudo-jmp on `EffectCall (Maybe_tail_is_return
                // (Tail_with_name {in_staticcatch=false}))`. A `Declare (kind, id)`
                // continuation — which is what `compile_let_binding` models —
                // takes the explicit-jump arm at lam_compile.ml:996-1000
                // unconditionally. Take that path here; the
                // `with_static_handler` inline shortcut is a Rust-only
                // optimization with no OCaml analog for `Declare`.
                let declaration =
                    BlockOutput::make(vec![Statement::variable(VariableDeclaration {
                        ident: *id,
                        value: None,
                        property: kind,
                        ident_info: IdentInfo::default(),
                    })]);
                let (handlers, flat_body) = flatten_nested_caches(*label, bindings, body, handler);
                let catch = if handlers.len() > 1 {
                    // lam_compile.ml:935 + 989-996 — `Declare (kind, id)`
                    // with flattened multi-handler code_table.
                    self.compile_multi_staticcatch_assignment_output(id, &handlers, flat_body)
                } else {
                    self.compile_staticcatch_assignment_output(id, *label, bindings, body, handler)
                };
                declaration.append(catch)
            }
            Lambda::LifThenElse(cond, then_, else_) => {
                BlockOutput::make(self.compile_if_binding_block(kind, id, cond, then_, else_))
            }
            Lambda::LtryWith(body, exn, handler) => {
                let body_block = self.compile_assign_to_target_block(id, body);
                let handler_block = self.compile_assign_to_target_block(id, handler);
                BlockOutput::make(vec![
                    Statement::variable(VariableDeclaration {
                        ident: *id,
                        value: None,
                        property: kind,
                        ident_info: IdentInfo::default(),
                    }),
                    self.try_statement(body_block, exn, handler_block),
                ])
            }
            Lambda::LtryFinally(body, finally) => {
                let try_statement = self.compile_try_finally(body, finally, |this, lam| {
                    this.compile_assign_to_target_block(id, lam)
                });
                BlockOutput::make(vec![
                    Statement::variable(VariableDeclaration {
                        ident: *id,
                        value: None,
                        property: kind,
                        ident_info: IdentInfo::default(),
                    }),
                    try_statement,
                ])
            }
            Lambda::Lsequence(first, second) => {
                // OCaml compiler/core/lam_compile.ml:1862-1869 compiles an
                // `Llet` RHS with continuation `Declare(kind, id)`. Its
                // Lsequence arm at compiler/core/lam_compile.ml:1899-1903
                // emits the head as `EffectCall Not_tail`, then compiles the
                // tail in the original continuation. That lets
                // compiler/core/js_stmt_make.ml:62-67 turn a final unit
                // `Undefined` into `let id;` instead of binding a
                // `(effect, undefined)` expression.
                // lam_compile.ml:1905-1910: both parts are compiled first.
                let first = self.compile_effect_block_output(first);
                let second = self.compile_let_binding_output(kind, id, second);
                first.append(second)
            }
            Lambda::Lswitch(scrut, switch) => {
                BlockOutput::make(self.compile_switch_binding_block(kind, id, scrut, switch))
            }
            Lambda::LstringSwitch(scrut, cases, default) => {
                BlockOutput::make(self.compile_string_switch_binding_block(
                    kind,
                    id,
                    scrut,
                    cases,
                    default.as_deref(),
                ))
            }
            Lambda::Lprim(info) => {
                if let Some((op, lhs, rhs)) = short_circuit_primitive(&info.primitive, &info.args) {
                    return BlockOutput::make(
                        self.compile_short_circuit_binding_block(kind, id, op, lhs, rhs),
                    );
                }
                let value_compiled = self.compile_expr(value);
                declare_compiled(kind, id, value_compiled)
            }
            _ => {
                let value_compiled = self.compile_expr(value);
                declare_compiled(kind, id, value_compiled)
            }
        }
    }

    pub(crate) fn compile_effect_block(&mut self, lam: &Lambda) -> Block {
        // Mirror OCaml's invariant that consumers of `compile_lambda` go
        // through `Js_output.output_as_block` (js_output.ml:82-86) which
        // calls `unnest_block` (js_output.ml:77-80). The unnest peels
        // single-element `[Block ...]` wrappers so an inner `S.if_` rule 7
        // result doesn't hide its literal-last terminal from the outer
        // `block_last_is_return_throw_or_continue` check
        // (js_stmt_make.ml:186-193).
        self.compile_effect_block_output(lam).block
    }

    /// `compile_lambda {cxt with continuation = EffectCall Not_tail} lam`,
    /// with the output's `finished` flag.
    pub(crate) fn compile_effect_block_output(&mut self, lam: &Lambda) -> BlockOutput {
        let output = self.compile_effect_block_inner(lam);
        BlockOutput {
            block: unnest_block(output.block),
            finished: output.finished,
        }
    }

    /// A grouped switch case that falls through to the next one. OCaml still
    /// gives it the location of its case lambda (lam_compile.ml:676-683).
    pub(crate) fn empty_switch_case_clause_for(&self, lam: &Lambda) -> CaseClause {
        CaseClause {
            source_loc: self.source_loc_of_lam(lam),
            ..empty_switch_case_clause()
        }
    }

    /// lam_compile.ml:80-84 `with_block_source_loc`: switch-case bodies
    /// (lam_compile.ml:581-659) tag their first statement with the case
    /// lambda's location.
    pub(crate) fn with_block_source_loc(&self, lam: &Lambda, mut block: Block) -> Block {
        if let Some(first) = block.first_mut()
            && first.source_loc.is_none()
        {
            first.source_loc = self.source_loc_of_lam(lam);
        }
        block
    }

    fn compile_effect_block_inner(&mut self, lam: &Lambda) -> BlockOutput {
        match lam {
            Lambda::Llet(kind, id, value, body) => {
                if let Some(compiled) = self.try_compile_record_spread(id, value, body) {
                    let mut block = compiled.prelude;
                    push_effect_expression(&mut block, compiled.expr);
                    return BlockOutput::make(block);
                }
                // lam_compile.ml:1867-1877: compile the binding, then the
                // body, then `append_output`.
                let binding = self.compile_let_binding_output(*kind, id, value);
                let body = self.compile_effect_block_output(body);
                binding.append(body)
            }
            Lambda::Lletrec(bindings, body) => {
                // Mirror OCaml's Lletrec arm (lam_compile.ml:1770-1783): emit
                // bindings then compile body in the SAME continuation. The
                // catch-all `_ => compile_expr(lam)` would force the body
                // through `NeedValue`, losing the effect/tail context.
                let bindings = self.compile_recursive_bindings_output(bindings);
                let body = self.compile_effect_block_output(body);
                bindings.append(body)
            }
            Lambda::LifThenElse(cond, then_, else_) => {
                BlockOutput::make(self.compile_if_effect_block(cond, then_, else_))
            }
            Lambda::Lsequence(first, second) => {
                // lam_compile.ml:1905-1910: both parts are compiled first.
                let first = self.compile_effect_block_output(first);
                let second = self.compile_effect_block_output(second);
                first.append(second)
            }
            Lambda::LstaticCatch(body, (label, bindings), handler) => {
                // OCaml's `compile_staticcatch` (lam_compile.ml:937-1017) only
                // takes the pseudo-jmp path when the continuation is
                // `EffectCall (Maybe_tail_is_return (Tail_with_name
                // {in_staticcatch = false}))`. For an `EffectCall Not_tail`
                // continuation — which is where `compile_effect_block` sits —
                // it always falls through to the explicit-jump arm at
                // lam_compile.ml:963-1017. Mirror that by always taking the
                // Rust explicit-jump path here; the inline `with_static_handler`
                // shortcut is a Rust-only optimization with no OCaml analog.
                let (handlers, flat_body) = flatten_nested_caches(*label, bindings, body, handler);
                if handlers.len() > 1 {
                    // lam_compile.ml:935 + 1000-1010 — `EffectCall Not_tail`
                    // with flattened multi-handler code_table.
                    self.compile_multi_staticcatch_effect_output(&handlers, flat_body)
                } else {
                    self.compile_staticcatch_effect_output(*label, bindings, body, handler)
                }
            }
            Lambda::LtryWith(body, exn, handler) => {
                let body_block = self.compile_effect_block(body);
                let handler_block = self.compile_effect_block(handler);
                BlockOutput::make(vec![self.try_statement(body_block, exn, handler_block)])
            }
            Lambda::LtryFinally(body, finally) => {
                BlockOutput::make(vec![self.compile_try_finally(
                    body,
                    finally,
                    |this, lam| this.compile_effect_block(lam),
                )])
            }
            Lambda::Lswitch(scrut, switch) => {
                BlockOutput::make(self.compile_switch_effect_block(scrut, switch))
            }
            Lambda::LstringSwitch(scrut, cases, default) => BlockOutput::make(
                self.compile_string_switch_effect_block(scrut, cases, default.as_deref()),
            ),
            _ => {
                let compiled = self.compile_expr(lam);
                let finished = compiled.finished;
                BlockOutput {
                    block: self.compiled_to_effect_block(compiled),
                    finished,
                }
            }
        }
    }

    fn compile_if_binding_block(
        &mut self,
        kind: LetKind,
        id: &Ident,
        cond: &Lambda,
        then_: &Lambda,
        else_: &Lambda,
    ) -> Block {
        let cond_compiled = self.compile_expr(cond);
        // Mirror OCaml's `compile_ifthenelse` Declare arm
        // (lam_compile.ml:1326-1349): first try both branches in
        // `NeedValue Not_tail`. When BOTH yield `{block = []; value = Some _}`
        // (i.e. fold to a side-effect-free expression including `E.seq`-folded
        // sequences), emit `let id = cond ? out1 : out2;` via `E.econd`.
        // Otherwise compile in Assign id and emit `let id; if (cond) ...`.
        let then_compiled = self.compile_expr(then_);
        let else_compiled = self.compile_expr(else_);
        if then_compiled.prelude.is_empty() && else_compiled.prelude.is_empty() {
            let mut block = cond_compiled.prelude;
            block.push(Statement::variable(VariableDeclaration {
                ident: *id,
                value: Some(Expression::cond(
                    cond_compiled.expr,
                    then_compiled.expr,
                    else_compiled.expr,
                )),
                property: kind,
                ident_info: IdentInfo::default(),
            }));
            return block;
        }

        let then_block = self.compile_assign_to_target_block(id, then_);
        let else_block = self.compile_assign_to_target_block(id, else_);

        let mut block = cond_compiled.prelude;
        block.extend(self.compile_declared_if_block(
            kind,
            id,
            cond_compiled.expr,
            then_block,
            else_block,
        ));
        block
    }

    fn compile_switch_binding_block(
        &mut self,
        kind: LetKind,
        id: &Ident,
        scrut: &Lambda,
        switch: &LambdaSwitch,
    ) -> Block {
        // OCaml's `compile_switch` (lam_compile.ml:784-787) unconditionally
        // emits `S.declare_variable ~kind id` before compiling the switch
        // body in `Assign id` context. No `declaration` is threaded through,
        // so the switch never folds back into `let id = cond ? a : b`.
        let mut declared = vec![Statement::variable(VariableDeclaration {
            ident: *id,
            value: None,
            property: kind,
            ident_info: IdentInfo::default(),
        })];
        declared.extend(self.compile_switch_assignment_block(id, scrut, switch));
        declared
    }

    fn compile_string_switch_binding_block(
        &mut self,
        kind: LetKind,
        id: &Ident,
        scrut: &Lambda,
        cases: &[(String, Lambda)],
        default: Option<&Lambda>,
    ) -> Block {
        // OCaml's `compile_stringswitch` (lam_compile.ml:872-876) threads the
        // `Declare (kind, id)` continuation straight to `compile_string_cases`
        // -> `compile_general_cases` -> `morph_declare_to_assign` -> `S.if_`,
        // so the two-case Complete arm folds `[id = then; id = else]` into
        // `let id = cond ? then : else` via the `declaration` parameter. Mirror
        // that by folding the final `id = expr` in the emitted assignment
        // block into the pending declaration.
        let body = self.compile_string_switch_assignment_block(id, scrut, cases, default);
        Self::prepend_declaration_or_fold_final_assignment(kind, id, body)
    }

    fn compile_short_circuit_expr(
        &mut self,
        op: ShortCircuitOp,
        lhs: &Lambda,
        rhs: &Lambda,
    ) -> Compiled {
        let lhs_compiled = self.compile_expr(lhs);
        let rhs_compiled = self.compile_expr(rhs);
        self.compile_short_circuit_js(op, lhs_compiled, rhs_compiled)
    }

    fn compile_short_circuit_js(
        &mut self,
        op: ShortCircuitOp,
        lhs_compiled: Compiled,
        rhs_compiled: Compiled,
    ) -> Compiled {
        let mut prelude = lhs_compiled.prelude;

        if rhs_compiled.prelude.is_empty() {
            let expr = match op {
                ShortCircuitOp::And => {
                    Expression::bin(BinOp::And, lhs_compiled.expr, rhs_compiled.expr)
                }
                ShortCircuitOp::Or => {
                    Expression::bin(BinOp::Or, lhs_compiled.expr, rhs_compiled.expr)
                }
            };
            return Compiled {
                prelude,
                expr,
                finished: OutputFinished::False,
            };
        }

        let tmp = self.fresh_tmp_ident();
        prelude.push(Statement::variable(VariableDeclaration {
            ident: tmp,
            value: Some(op.default_expr()),
            property: LetKind::Strict,
            ident_info: IdentInfo::default(),
        }));

        let mut then_block = rhs_compiled.prelude;
        then_block.push(Statement::exp(Expression::bin(
            BinOp::Eq,
            Expression::var(tmp),
            rhs_compiled.expr,
        )));

        let test = op.test_expr(lhs_compiled.expr);
        prelude.push(Statement::if_(test, then_block, vec![]));

        Compiled {
            prelude,
            expr: Expression::var(tmp),
            finished: OutputFinished::False,
        }
    }

    fn compile_short_circuit_binding_block(
        &mut self,
        kind: LetKind,
        id: &Ident,
        op: ShortCircuitOp,
        lhs: &Lambda,
        rhs: &Lambda,
    ) -> Block {
        let lhs_compiled = self.compile_expr(lhs);
        let rhs_compiled = self.compile_expr(rhs);
        let mut block = lhs_compiled.prelude;

        if rhs_compiled.prelude.is_empty() {
            let expr = match op {
                ShortCircuitOp::And => {
                    Expression::bin(BinOp::And, lhs_compiled.expr, rhs_compiled.expr)
                }
                ShortCircuitOp::Or => {
                    Expression::bin(BinOp::Or, lhs_compiled.expr, rhs_compiled.expr)
                }
            };
            block.push(Statement::variable(VariableDeclaration {
                ident: *id,
                value: Some(expr),
                property: kind,
                ident_info: IdentInfo::default(),
            }));
            return block;
        }

        block.push(Statement::variable(VariableDeclaration {
            ident: *id,
            value: Some(op.default_expr()),
            property: kind,
            ident_info: IdentInfo::default(),
        }));

        let mut then_block = rhs_compiled.prelude;
        then_block.push(self.result_assignment(id, rhs_compiled.expr));

        block.push(Statement::if_(
            op.test_expr(lhs_compiled.expr),
            then_block,
            vec![],
        ));
        block
    }

    fn compile_short_circuit_return_output(
        &mut self,
        op: ShortCircuitOp,
        lhs: &Lambda,
        rhs: &Lambda,
    ) -> BlockOutput {
        let default = op.default_lambda();
        match op {
            ShortCircuitOp::And => self.compile_if_return_output(lhs, rhs, &default),
            ShortCircuitOp::Or => self.compile_if_return_output(lhs, &default, rhs),
        }
    }

    pub(crate) fn compile_return_block(&mut self, lam: &Lambda) -> Block {
        // Mirror OCaml's invariant that consumers go through
        // `Js_output.output_as_block` (js_output.ml:82-86) which calls
        // `unnest_block` on `compile_lambda` results.
        self.compile_return_output(lam).block
    }

    /// `compile_lambda {cxt with continuation = EffectCall
    /// (Maybe_tail_is_return _)} lam`, with the output's `finished` flag.
    pub(crate) fn compile_return_output(&mut self, lam: &Lambda) -> BlockOutput {
        let output = self.compile_return_output_inner(lam);
        BlockOutput {
            block: unnest_block(output.block),
            finished: output.finished,
        }
    }

    fn compile_return_output_inner(&mut self, lam: &Lambda) -> BlockOutput {
        match lam {
            Lambda::Llet(kind, id, value, body) => {
                if let Some(compiled) = self.try_compile_record_spread(id, value, body) {
                    return return_compiled(compiled);
                }

                // lam_compile.ml:1867-1877: compile the binding, then the
                // body, then `append_output`.
                let binding = self.compile_let_binding_output(*kind, id, value);
                let body = self.compile_return_output(body);
                binding.append(body)
            }
            Lambda::Lletrec(bindings, body) => {
                // Mirror OCaml's `Lletrec` arm in `compile_lambda`
                // (lam_compile.ml:1770-1783): emit the recursive bindings, then
                // compile the body in the SAME continuation. The catch-all
                // `_ => compile_expr(lam)` would force the body through
                // `NeedValue Not_tail`, losing the `Maybe_tail_is_return`
                // context — meaning a tail-position `Lprim Psequor` body
                // skips `compile_short_circuit_return_block` and emits a flat
                // `return cond1 || cond2 || call(args);` instead of
                // `if (cond) return true; else { return call(args); }` that
                // `js_pass_tailcall_inline` can later inline.
                let recursive = self.compile_recursive_bindings_output(bindings);
                let body = self.compile_return_output(body);
                recursive.append(body)
            }
            Lambda::Lapply(apply) => {
                let mut compiled = self.compile_apply_call(apply);
                // lam_compile.ml:1606-1609: `with_source_loc ap_loc (E.call ...)`.
                if compiled.expr.source_loc.is_none() {
                    compiled.expr.source_loc = self.source_loc(&apply.ap_info.loc);
                }
                return_compiled(compiled)
            }
            Lambda::LifThenElse(cond, then_, else_) => {
                // Both branches are `undefined`: OCaml's `return e ? undefined
                // : undefined` (lam_compile.ml:1533-1537), finished.
                match self.compile_if_unit_return_tail_block(cond, then_, else_) {
                    Some(block) => BlockOutput::finished(block),
                    None => self.compile_if_return_output(cond, then_, else_),
                }
            }
            Lambda::Lprim(info) => {
                if let Some((op, lhs, rhs)) = short_circuit_primitive(&info.primitive, &info.args) {
                    return self.compile_short_circuit_return_output(op, lhs, rhs);
                }
                return_compiled(self.compile_expr(lam))
            }
            Lambda::Lsequence(first, second) => {
                // lam_compile.ml:1905-1910: both parts are compiled first.
                let first = self.compile_effect_block_output(first);
                let second = self.compile_return_output(second);
                first.append(second)
            }
            Lambda::LstaticRaise(id, args) => {
                if let Some(output) = self.compile_static_raise_jump_output(*id, args) {
                    return output;
                }
                if let Some(output) = self.compile_fallthrough_static_raise_return_output(*id, args)
                {
                    return output;
                }
                if let Some(handler) = self.resolve_static_raise(*id, args) {
                    return self.compile_return_output(&handler);
                }
                return_compiled(self.compile_expr(lam))
            }
            Lambda::LstaticCatch(body, (label, bindings), handler)
                if flatten_nested_caches(*label, bindings, body, handler)
                    .0
                    .len()
                    > 1 =>
            {
                // lam_compile.ml:935 — `flatten_nested_caches` is the FIRST
                // thing `compile_staticcatch` does. A code_table with >1
                // entries goes through the multi-handler explicit-jump arm
                // (lam_compile.ml:1000-1010 for `EffectCall tail_type`).
                let (handlers, flat_body) = flatten_nested_caches(*label, bindings, body, handler);
                self.compile_multi_staticcatch_return_output(&handlers, flat_body)
            }
            Lambda::LstaticCatch(body, (label, bindings), handler)
                if self.uses_fallthrough_staticcatch_return(body, *label, bindings, handler) =>
            {
                self.compile_fallthrough_staticcatch_return_output(*label, bindings, body, handler)
            }
            Lambda::LstaticCatch(body, (label, bindings), handler)
                if self.uses_pseudo_fallthrough_staticcatch_return(
                    body, *label, bindings, handler,
                ) =>
            {
                self.compile_fallthrough_staticcatch_return_output(*label, bindings, body, handler)
            }
            Lambda::LstaticCatch(body, (label, bindings), handler)
                if bindings.is_empty()
                    && self.try_body_depth == 0
                    && matches!(
                        body.as_ref(),
                        Lambda::LstaticCatch(_, _, nested_handler)
                            if lambda_contains_static_raise(nested_handler)
                    )
                    && !self.handler_returns_unit_undefined(bindings, handler)
                    && no_static_raise_in_handler_like_ocaml(handler) =>
            {
                self.compile_fallthrough_staticcatch_return_output(*label, bindings, body, handler)
            }
            Lambda::LstaticCatch(body, (label, bindings), handler) => {
                let requires_explicit_jump = (self.return_unit_stack.last().copied() == Some(true)
                    && !bindings.is_empty())
                    || self.try_body_depth > 0
                    || self
                        .return_staticcatch_requires_explicit_jump(*label, bindings, body, handler);
                if requires_explicit_jump {
                    self.compile_staticcatch_return_output(*label, bindings, body, handler)
                } else if no_static_raise_in_handler_like_ocaml(handler)
                    && !lambda_contains_staticcatch(handler)
                    && lambda_contains_static_raise_to_label(body, *label, bindings.len())
                {
                    // OCaml's `compile_staticcatch` pseudo-jmp path
                    // (compiler/core/lam_compile.ml:983-1008, add_pseudo_jmp
                    // at compiler/core/lam_compile_context.ml:125-130) fires
                    // for any single code_table with `no_static_raise_in_handler`
                    // (compiler/core/lam_compile_context.ml:105-106:
                    // `has_exit_code handler
                    // (fun _ -> true)`). We mirror that here via the ported
                    // `Lam_exit_code.has_exit_code`, which STOPS at Lfunction
                    // boundaries (lam_exit_code.ml:28). Rust's prior
                    // `lambda_contains_static_raise` predicate crossed
                    // Lfunction, over-counting raises that live inside
                    // closures and can't escape, which kept this
                    // fallthrough path from firing on handlers whose
                    // tail-loop body contains an inner closure with a
                    // static_raise.
                    self.compile_fallthrough_staticcatch_return_output(
                        *label, bindings, body, handler,
                    )
                } else if lambda_contains_static_raise_to_label(body, *label, bindings.len()) {
                    // OCaml has no `with_static_handler` analog — when the
                    // handler contains static_raise or nested staticcatch
                    // and body raises to this label, OCaml's pseudo-jmp
                    // path fails its `no_static_raise_in_handler` guard
                    // (lam_compile.ml:943) and falls through to the
                    // explicit-jump arm at lam_compile.ml:963-1017. Take
                    // explicit-jump here; the `with_static_handler` path
                    // inlines the handler at every raise site via
                    // `resolve_static_raise`, while OCaml emits it ONCE
                    // gated by `if (exit === N)` after the body.
                    self.compile_staticcatch_return_output(*label, bindings, body, handler)
                } else {
                    self.with_static_handler(*label, bindings, handler, |this| {
                        this.compile_return_output(body)
                    })
                }
            }
            Lambda::LtryWith(body, exn, handler) => {
                // OCaml reference: compiler/core/lam_compile.ml:1311-1344
                // compiles the `try` body with `Tail_in_try` while the catch
                // handler keeps the surrounding return context. `Tail_in_try`
                // still returns from the JS function, but it is not the
                // `Tail_with_name {in_staticcatch=false}` context required by
                // `compile_staticcatch`'s pseudo-jump arm.
                let body_block = self.with_try_body_context(|this| this.compile_return_block(body));
                let handler_block = self.compile_return_block(handler);
                BlockOutput::make(vec![self.try_statement(body_block, exn, handler_block)])
            }
            Lambda::LtryFinally(body, finally) => {
                BlockOutput::make(vec![self.compile_try_finally(
                    body,
                    finally,
                    |this, lam| this.with_try_body_context(|this| this.compile_return_block(lam)),
                )])
            }
            // compile_switch / compile_stringswitch return `Js_output.make`
            // (lam_compile.ml:822).
            Lambda::Lswitch(scrut, switch) => {
                BlockOutput::make(self.compile_switch_return_block(scrut, switch))
            }
            Lambda::LstringSwitch(scrut, cases, default) => BlockOutput::make(
                self.compile_string_switch_return_block(scrut, cases, default.as_deref()),
            ),
            _ => return_compiled(self.compile_expr(lam)),
        }
    }

    fn with_fallthrough_return_handler<T>(
        &mut self,
        label: i32,
        bindings: &[Ident],
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        self.fallthrough_return_handlers
            .push(FallthroughReturnHandler {
                label,
                bindings: bindings.to_vec(),
            });
        let result = f(self);
        self.fallthrough_return_handlers.pop();
        result
    }

    fn with_return_unit_context<T>(
        &mut self,
        return_unit: bool,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        self.return_unit_stack.push(return_unit);
        let result = f(self);
        self.return_unit_stack.pop();
        result
    }

    fn with_try_body_context<T>(&mut self, f: impl FnOnce(&mut Self) -> T) -> T {
        self.try_body_depth += 1;
        let result = f(self);
        self.try_body_depth -= 1;
        result
    }

    fn lambda_is_trivial_unit_undefined(&self, lam: &Lambda) -> bool {
        match lam {
            Lambda::Lconst(Constant::JsUndefined { is_unit: true }) => true,
            Lambda::Lsequence(first, second) => {
                lam_analysis::no_side_effects(first)
                    && self.lambda_is_trivial_unit_undefined(second)
            }
            Lambda::Llet(_, _, value, body) => {
                lam_analysis::no_side_effects(value) && self.lambda_is_trivial_unit_undefined(body)
            }
            Lambda::Lletrec(bindings, body) => {
                bindings
                    .iter()
                    .all(|(_, value)| lam_analysis::no_side_effects(value))
                    && self.lambda_is_trivial_unit_undefined(body)
            }
            Lambda::LstaticCatch(body, (_, bindings), handler) if bindings.is_empty() => {
                self.lambda_is_trivial_unit_undefined(body)
                    && self.lambda_is_trivial_unit_undefined(handler)
            }
            Lambda::LtryWith(body, _, handler) | Lambda::LtryFinally(body, handler) => {
                self.lambda_is_trivial_unit_undefined(body)
                    && self.lambda_is_trivial_unit_undefined(handler)
            }
            _ => false,
        }
    }

    fn compile_if_unit_return_tail_block(
        &mut self,
        cond: &Lambda,
        then_: &Lambda,
        else_: &Lambda,
    ) -> Option<Block> {
        if self.return_unit_stack.last().copied() != Some(true) {
            return None;
        }

        let then_is_trivial_unit = self.lambda_is_trivial_unit_undefined(then_);
        let else_is_trivial_unit = self.lambda_is_trivial_unit_undefined(else_);
        if then_is_trivial_unit && else_is_trivial_unit {
            let cond_compiled = self.compile_expr(cond);
            let mut block = cond_compiled.prelude;
            // OCaml's `S.if_ cond [] []` keeps only a condition with side
            // effects (js_stmt_make.ml `if_`).
            push_s_if_empty(&mut block, cond_compiled.expr);
            return Some(block);
        }

        // Case 2 (else is trivial unit, then is not): intentionally not
        // short-circuited here. Falling through to `compile_if_return_block`
        // lets `try_fold_effect_only_return_tail` produce the OCaml-aligned
        // `Return(Cond(cond, Seq(effect, undef), undef))` shape via OCaml's
        // `compile_ifthenelse` `EffectCall (Maybe_tail_is_return)` arm
        // (lam_compile.ml:1422-1427). `flatten_block` later expands that to
        // `[If(cond, [Exp effect, Return undef], [Return undef])]`, preserving
        // the explicit `else { return; }` for nested-if shapes. The printer's
        // `print_function_tail_statement` (printer.rs:2714-2722) drops the
        // `else { return undefined; }` for top-level single-If bodies,
        // matching OCaml's `function_body` rule (js_dump.ml:1612-1618).
        None
    }

    fn js_block_is_simple_unit_return_tail(&self, block: &Block) -> bool {
        let Some((last, prefix)) = block.split_last() else {
            return false;
        };
        matches!(
            last,
            Statement {
                desc: StatementDesc::Return(Expression {
                    desc: ExpressionDesc::Undefined { .. },
                    ..
                }),
                ..
            }
        ) && prefix
            .iter()
            .all(|stmt| matches!(stmt.desc, StatementDesc::Exp(_)))
    }

    fn handler_returns_unit_undefined(&self, bindings: &[Ident], handler: &Lambda) -> bool {
        if !bindings.is_empty() {
            return false;
        }

        match handler {
            Lambda::Lconst(Constant::JsUndefined { is_unit: true }) => true,
            Lambda::Lsequence(_, rest) => self.handler_returns_unit_undefined(&[], rest),
            Lambda::Llet(_, _, _, body) => self.handler_returns_unit_undefined(&[], body),
            Lambda::Lletrec(_, body) => self.handler_returns_unit_undefined(&[], body),
            _ => false,
        }
    }

    fn staticcatch_handler_is_identity_binding(
        &self,
        bindings: &[Ident],
        handler: &Lambda,
    ) -> bool {
        matches!(
            (bindings, handler),
            ([binding], Lambda::Lvar(id)) if id.same(binding)
        )
    }

    /// lam_compile.ml:969-986 `compile_staticraise` to a pseudo jump
    /// (`order_id < 0`): the arguments are assigned, folded last first onto
    /// `Js_output.make []`.
    fn compile_fallthrough_static_raise_return_output(
        &mut self,
        label: i32,
        args: &[Lambda],
    ) -> Option<BlockOutput> {
        let bindings = self
            .fallthrough_return_handlers
            .iter()
            .rev()
            .find(|handler| handler.label == label)?
            .bindings
            .clone();
        if bindings.len() != args.len() {
            return None;
        }

        let output = args.iter().zip(&bindings).rev().fold(
            BlockOutput::make(vec![]),
            |acc, (arg, binding)| {
                if matches!(arg, Lambda::Lvar(id) if id.same(binding)) {
                    return acc;
                }
                self.compile_assign_to_target_output(binding, arg)
                    .append(acc)
            },
        );
        Some(output)
    }

    /// lam_compile.ml:1022-1047, the pseudo-jump arm of
    /// `compile_staticcatch`: `append_output (make declares) (append_output
    /// lbody (compile_lambda lambda_cxt handler))`, with the handler compiled
    /// after the body.
    fn compile_fallthrough_staticcatch_return_output(
        &mut self,
        label: i32,
        bindings: &[Ident],
        body: &Lambda,
        handler: &Lambda,
    ) -> BlockOutput {
        let declarations: Block = bindings
            .iter()
            .map(|binding| {
                Statement::variable(VariableDeclaration {
                    ident: *binding,
                    value: None,
                    property: LetKind::Variable,
                    ident_info: IdentInfo::default(),
                })
            })
            .collect();
        let body_output = self.with_fallthrough_return_handler(label, bindings, |this| {
            this.compile_return_output(body)
        });
        let handler_output = self.compile_return_output(handler);
        BlockOutput::make(declarations).append(body_output.append(handler_output))
    }

    /// lam_compile.ml:1022-1047, the pseudo-jump arm of
    /// `compile_staticcatch`: `append_output (make declares) (append_output
    /// lbody (compile_lambda lambda_cxt handler))`, with the handler compiled
    /// after the body.
    fn compile_fallthrough_staticcatch_tail_loop_return_output(
        &mut self,
        label: i32,
        bindings: &[Ident],
        body: &Lambda,
        handler: &Lambda,
        tail_loop: &mut TailLoopState,
    ) -> BlockOutput {
        let declarations: Block = bindings
            .iter()
            .map(|binding| {
                Statement::variable(VariableDeclaration {
                    ident: *binding,
                    value: None,
                    property: LetKind::Variable,
                    ident_info: IdentInfo::default(),
                })
            })
            .collect();
        let body_output = self.with_fallthrough_return_handler(label, bindings, |this| {
            this.compile_tail_loop_return_output(body, tail_loop)
        });
        let handler_output = self.compile_tail_loop_return_output(handler, tail_loop);
        BlockOutput::make(declarations).append(body_output.append(handler_output))
    }

    fn uses_fallthrough_staticcatch_return(
        &self,
        body: &Lambda,
        label: i32,
        bindings: &[Ident],
        handler: &Lambda,
    ) -> bool {
        // The pseudo-jump arm of OCaml compile_staticcatch (lam_compile.ml:1052-1060)
        // requires Tail_with_name {in_staticcatch = false}. A nested catch
        // compiled in an enclosing catch body has in_staticcatch = true and
        // must use the explicit exit dispatch instead of unconditionally
        // falling through to its handler.
        if self.try_body_depth > 0
            || !self.fallthrough_return_handlers.is_empty()
            || !self.static_handlers.is_empty()
            || !self.static_jump_handlers.is_empty()
        {
            return false;
        }
        // lam_compile.ml:937-962: the pseudo-jmp arm needs
        // `Tail_with_name {in_staticcatch = false}`; a staticcatch compiled
        // inside another one's body or dispatched handlers has
        // `in_staticcatch = true` and takes the exit-variable arm.
        if !self.static_handlers.is_empty() || !self.static_jump_handlers.is_empty() {
            return false;
        }
        // OCaml flattens nested staticcatch chains before deciding whether the
        // current handler can fall through after the switch. Once we're already
        // under an enclosing static handler/jump chain, keep plain handlers
        // resolved inside the switch/default instead of peeling them out.
        let inside_enclosing_staticcatch_chain =
            !self.static_handlers.is_empty() || !self.static_jump_handlers.is_empty();
        let arity = bindings.len();
        let body_has_target_exit = lambda_contains_static_raise_to_label(body, label, arity);
        let keep_complete_named_variant_plain_handler_inline = matches!(
            body,
            Lambda::Lswitch(_, switch)
                if self.uses_named_variant_switch(switch)
                    && switch.sw_failaction.is_none()
                    && switch.sw_consts_full
                    && switch.sw_blocks_full
                    && no_static_raise_in_handler_like_ocaml(handler)
                    && lambda_contains_static_raise_to_other_label(body, label)
        );
        // Lam_pass_exits can inline outward handlers away before backend
        // lowering. OCaml's compile_staticcatch pseudo-jump path still keeps a
        // shared non-raising handler outside the switch when several direct
        // exits now target the same label.
        let shared_multi_exit_fallthrough_like_ocaml = !inside_enclosing_staticcatch_chain
            && !keep_complete_named_variant_plain_handler_inline
            && !self.handler_returns_unit_undefined(bindings, handler)
            && no_static_raise_in_handler_like_ocaml(handler)
            && body_has_target_exit
            && lambda_has_multiple_static_raises_to_label(body, label, arity);
        match body {
            Lambda::Lswitch(_, switch) => match handler {
                Lambda::LstaticRaise(_, args) if args.len() == arity && body_has_target_exit => {
                    true
                }
                _ if !self.uses_untagged_variant_switch(switch)
                    && !keep_complete_named_variant_plain_handler_inline
                    && shared_multi_exit_fallthrough_like_ocaml =>
                {
                    true
                }
                _ if !self.uses_untagged_variant_switch(switch)
                    && !keep_complete_named_variant_plain_handler_inline
                    && no_static_raise_in_handler_like_ocaml(handler)
                    && !lambda_contains_staticcatch(handler)
                    && switch_cases_contain_static_raise_to_label(
                        &switch.sw_consts,
                        &switch.sw_blocks,
                        label,
                        arity,
                    )
                    && body_has_target_exit
                    && (lambda_contains_static_raise_to_other_label(body, label)
                        || switch_cases_contain_nontrivial_static_raise_to_label(
                            &switch.sw_consts,
                            &switch.sw_blocks,
                            label,
                            arity,
                        )) =>
                {
                    true
                }
                // OCaml takes the pseudo-jmp/fallthrough arm for any
                // tail-return staticcatch with a single handler whose handler
                // has no static raise (compiler/core/lam_compile.ml:983-1008).
                // It is not gated on function `return_unit`; switches reach the
                // same `compile_staticcatch` arm through
                // compiler/core/lam_compile.ml:1907-1911.
                _ if !inside_enclosing_staticcatch_chain
                    && !self.handler_returns_unit_undefined(bindings, handler)
                    && no_static_raise_in_handler_like_ocaml(handler) =>
                {
                    if !bindings.is_empty() {
                        body_has_target_exit
                    } else {
                        switch.sw_consts.len() + switch.sw_blocks.len() == 1
                            && matches!(
                                switch.sw_failaction.as_deref(),
                                Some(Lambda::LstaticRaise(id, args))
                                    if *id == label && args.len() == arity
                            )
                    }
                }
                _ => false,
            },
            Lambda::LstringSwitch(_, cases, default) => match handler {
                Lambda::LstaticRaise(_, args) if args.len() == arity && body_has_target_exit => {
                    true
                }
                _ if !keep_complete_named_variant_plain_handler_inline
                    && shared_multi_exit_fallthrough_like_ocaml =>
                {
                    true
                }
                _ if no_static_raise_in_handler_like_ocaml(handler)
                    && !keep_complete_named_variant_plain_handler_inline
                    && !lambda_contains_staticcatch(handler)
                    && string_switch_cases_contain_static_raise_to_label(cases, label, arity)
                    && body_has_target_exit
                    && (lambda_contains_static_raise_to_other_label(body, label)
                        || string_switch_cases_contain_nontrivial_static_raise_to_label(
                            cases, label, arity,
                        )) =>
                {
                    true
                }
                // OCaml takes the pseudo-jmp/fallthrough arm for any
                // tail-return staticcatch with a single handler whose handler
                // has no static raise (compiler/core/lam_compile.ml:983-1008).
                // It is not gated on function `return_unit`; string switches
                // reach the same `compile_staticcatch` arm through
                // compiler/core/lam_compile.ml:1907-1911.
                _ if !inside_enclosing_staticcatch_chain
                    && !self.handler_returns_unit_undefined(bindings, handler)
                    && no_static_raise_in_handler_like_ocaml(handler) =>
                {
                    if !bindings.is_empty() {
                        body_has_target_exit
                    } else {
                        cases.len() == 1
                            && matches!(
                                default.as_deref(),
                                Some(Lambda::LstaticRaise(id, args))
                                    if *id == label && args.len() == arity
                            )
                    }
                }
                _ => false,
            },
            Lambda::LtryWith(try_body, _, _)
                if !inside_enclosing_staticcatch_chain
                    && !bindings.is_empty()
                    && !self.staticcatch_handler_is_identity_binding(bindings, handler)
                    && !self.handler_returns_unit_undefined(bindings, handler)
                    && no_static_raise_in_handler_like_ocaml(handler)
                    && !lambda_contains_staticcatch(handler)
                    && body_has_target_exit
                    && !lambda_contains_static_raise_to_other_label(try_body, label) =>
            {
                true
            }
            _ => false,
        }
    }

    fn uses_pseudo_fallthrough_staticcatch_return(
        &self,
        body: &Lambda,
        label: i32,
        bindings: &[Ident],
        handler: &Lambda,
    ) -> bool {
        if self.try_body_depth > 0
            || !self.static_handlers.is_empty()
            || !self.static_jump_handlers.is_empty()
            || !self.fallthrough_return_handlers.is_empty()
        {
            return false;
        }
        self.return_unit_stack.last().copied() == Some(true)
            && !bindings.is_empty()
            && self.fallthrough_return_handlers.is_empty()
            && !matches!(body, Lambda::Lswitch(_, _) | Lambda::LstringSwitch(_, _, _))
            && lambda_contains_static_raise_to_label(body, label, bindings.len())
            && no_static_raise_in_handler_like_ocaml(handler)
    }

    pub(crate) fn active_fallthrough_return_handler(&self) -> Option<&FallthroughReturnHandler> {
        self.fallthrough_return_handlers.last()
    }

    pub(crate) fn reorder_fallthrough_return_clauses<T>(
        &self,
        clauses: Vec<T>,
        _body_is_empty: impl FnMut(&T) -> bool,
    ) -> Vec<T> {
        // OCaml's `group_apply` preserves the order produced by
        // `Ext_list.stable_group`; it does not partition fallthrough clauses
        // after returning clauses (compiler/core/lam_compile.ml:126-130,
        // 610-624; compiler/ext/ext_list.ml:534-547).
        clauses
    }

    pub(crate) fn grouped_return_string_clauses<T: Clone>(
        &mut self,
        grouped_cases: Vec<(T, &Lambda, bool)>,
        mut to_tag: impl FnMut(T) -> SwitchCaseTag,
    ) -> Vec<StringClause> {
        let mut clauses = Vec::with_capacity(grouped_cases.len());
        let mut group_start = 0;
        while group_start < grouped_cases.len() {
            let mut group_end = group_start;
            while !grouped_cases[group_end].2 {
                group_end += 1;
            }

            let (_, body, _) = &grouped_cases[group_end];
            let compiled_output = self.compile_return_output(body);
            let compiled_finished = compiled_output.finished;
            let compiled_body = compiled_output.block;
            let group_falls_through = compiled_body.is_empty();
            // Mirror OCaml's `compile_general_cases`: it feeds each last
            // grouped case through `Js_output.to_break_block`, then gates the
            // break bit with `Lam_exit_code.has_exit` in return continuation
            // (compiler/core/lam_compile.ml:613-624;
            // compiler/core/js_output.ml:88-100). When a case resolves to a
            // fallthrough static-raise handler, the empty body still needs a
            // `break;` so the appended handler runs once after the switch.
            let should_break = return_case_needs_break(body, compiled_finished);

            for (tag, case_lam, _) in &grouped_cases[group_start..group_end] {
                clauses.push((
                    to_tag(tag.clone()),
                    self.empty_switch_case_clause_for(case_lam),
                    group_falls_through,
                ));
            }
            clauses.push((
                to_tag(grouped_cases[group_end].0.clone()),
                CaseClause {
                    source_loc: self.source_loc_of_lam(body),
                    body: self.with_block_source_loc(body, compiled_body),
                    should_break,
                    comment: None,
                },
                group_falls_through,
            ));

            group_start = group_end + 1;
        }

        self.reorder_fallthrough_return_clauses(clauses, |(_, _, falls_through)| *falls_through)
            .into_iter()
            .map(|(tag_type, clause, _)| StringClause { tag_type, clause })
            .collect()
    }

    pub(crate) fn should_hoist_grouped_named_string_return_tail(&self, body: &Lambda) -> bool {
        match body {
            Lambda::LstaticRaise(label, args) => self
                .resolve_static_raise(*label, args)
                .as_ref()
                .is_some_and(lambda_has_exit),
            _ => false,
        }
    }

    pub(crate) fn compile_hoisted_named_string_return_tail(
        &mut self,
        body: &Lambda,
    ) -> BlockOutput {
        self.compile_hoisted_static_raise_chain_return_tail(body)
            .unwrap_or_else(|| self.compile_return_output(body))
    }

    /// Inlines the handler of a static raise in a string switch's shared
    /// return tail. The parts are joined with `append` after all of them
    /// are compiled; the arguments are compiled last first, as
    /// `compile_staticraise`'s `Ext_list.fold_right2` does
    /// (lam_compile.ml:969-986).
    fn compile_hoisted_static_raise_chain_return_tail(
        &mut self,
        lam: &Lambda,
    ) -> Option<BlockOutput> {
        match lam {
            Lambda::Llet(kind, id, value, body) => {
                let binding = self.compile_let_binding_output(*kind, id, value);
                match self.compile_hoisted_static_raise_chain_return_tail(body) {
                    Some(body) => Some(binding.append(body)),
                    None if binding.finished == OutputFinished::True => Some(binding),
                    None => None,
                }
            }
            Lambda::Lsequence(first, second) => {
                let first = self.compile_effect_block_output(first);
                match self.compile_hoisted_static_raise_chain_return_tail(second) {
                    Some(second) => Some(first.append(second)),
                    None if first.finished == OutputFinished::True => Some(first),
                    None => None,
                }
            }
            Lambda::LstaticRaise(label, args) => {
                let handler_index = self.static_handlers.iter().rposition(|handler| {
                    handler.label == *label && handler.bindings.len() == args.len()
                })?;
                let handler = self.static_handlers[handler_index].clone();
                let removed = self.static_handlers.remove(handler_index);

                let arguments = args.iter().zip(&handler.bindings).rev().fold(
                    BlockOutput::dummy(),
                    |acc, (arg, binding)| {
                        if matches!(arg, Lambda::Lvar(id) if id.same(binding)) {
                            return acc;
                        }
                        self.compile_let_binding_output(LetKind::Strict, binding, arg)
                            .append(acc)
                    },
                );
                let handler_output = self
                    .compile_hoisted_static_raise_chain_return_tail(&handler.handler)
                    .unwrap_or_else(|| self.compile_return_output(&handler.handler));
                self.static_handlers.insert(handler_index, removed);
                Some(arguments.append(handler_output))
            }
            _ => None,
        }
    }

    fn compile_recursive_function_expr(
        &mut self,
        _function: &Ident,
        func: &crate::lambda::LFunction,
        tail_targets: &[Ident],
    ) -> Expression {
        let has_self_tailcall = function_has_self_tailcall(tail_targets, &func.body);
        if !has_self_tailcall {
            return self
                .compile_expr(&Lambda::Lfunction(Box::new(func.clone())))
                .expr;
        }

        let params = if func.attr.one_unit_arg {
            vec![]
        } else {
            func.params.clone()
        };
        let mut tail_loop = TailLoopState::new(tail_targets.to_vec(), params.clone());
        let body = self.compile_tail_loop_return_block(&func.body, &mut tail_loop);

        if !tail_loop.triggered {
            return self
                .compile_expr(&Lambda::Lfunction(Box::new(func.clone())))
                .expr;
        }

        let lowered_params = params
            .iter()
            .map(|param| tail_loop.new_params.get(param).cloned().unwrap_or(*param))
            .collect();

        // OCaml reference: compiler/core/lam_compile.ml:379-381 folds
        // `ret.new_params` with `Map_ident.fold ... (fun old new_param acc ->
        // S.define_variable ... :: acc)`. `Map_ident` is ordered by
        // `Ext_ident.compare` (compiler/ext/map.cppo.ml:12-15,
        // compiler/ext/ext_ident.ml:178-180), so the prepended accumulator emits
        // declarations in descending map-key order.
        let mut lowered_param_defs: Vec<_> = tail_loop.new_params.iter().collect();
        lowered_param_defs.sort_by(|(left, _), (right, _)| ext_ident_cmp(right, left));

        let mut loop_body = Vec::new();
        for (param, new_param) in lowered_param_defs {
            loop_body.push(Statement::variable(VariableDeclaration {
                ident: *param,
                value: Some(Expression::var(*new_param)),
                property: LetKind::Alias,
                ident_info: IdentInfo::default(),
            }));
        }
        loop_body.extend(body);

        let mut expr = Expression::new(ExpressionDesc::Fun {
            is_method: false,
            params: lowered_params,
            body: vec![Statement::while_(Expression::bool(true), loop_body)],
            env: Default::default(),
            return_unit: func.attr.return_unit,
            async_: func.attr.async_,
            directive: (func.attr.directive.clone()).map(Box::new),
        });
        // lam_compile.ml:436: `with_source_loc loc result`.
        expr.source_loc = self.source_loc(&func.loc);
        expr
    }

    pub(crate) fn compile_tail_loop_return_block(
        &mut self,
        lam: &Lambda,
        tail_loop: &mut TailLoopState,
    ) -> Block {
        // Mirror OCaml's invariant that consumers of `compile_lambda` go
        // through `Js_output.output_as_block` which calls `unnest_block`.
        self.compile_tail_loop_return_output(lam, tail_loop).block
    }

    /// [`Self::compile_return_output`] in a function body compiled as a
    /// self tail call loop.
    pub(crate) fn compile_tail_loop_return_output(
        &mut self,
        lam: &Lambda,
        tail_loop: &mut TailLoopState,
    ) -> BlockOutput {
        let output = self.compile_tail_loop_return_output_inner(lam, tail_loop);
        BlockOutput {
            block: unnest_block(output.block),
            finished: output.finished,
        }
    }

    fn compile_tail_loop_return_output_inner(
        &mut self,
        lam: &Lambda,
        tail_loop: &mut TailLoopState,
    ) -> BlockOutput {
        match lam {
            Lambda::Llet(kind, id, value, body) => {
                // lam_compile.ml:1867-1877.
                let binding = self.compile_let_binding_output(*kind, id, value);
                let body = self.compile_tail_loop_return_output(body, tail_loop);
                binding.append(body)
            }
            Lambda::Lapply(apply) => {
                // lam_compile.ml:1538, 1626: the jump back to the loop is
                // finished.
                if let Some(block) = self.try_compile_self_tailcall_block(apply, tail_loop) {
                    return BlockOutput::finished(block);
                }
                return_compiled(self.compile_apply_call(apply))
            }
            Lambda::LifThenElse(cond, then_, else_) => {
                self.compile_tail_loop_if_return_output(cond, then_, else_, tail_loop)
            }
            Lambda::Lprim(info) => {
                if let Some((op, lhs, rhs)) = short_circuit_primitive(&info.primitive, &info.args) {
                    return self
                        .compile_short_circuit_tail_loop_return_output(op, lhs, rhs, tail_loop);
                }
                return_compiled(self.compile_expr(lam))
            }
            Lambda::Lsequence(first, second) => {
                // lam_compile.ml:1905-1910.
                let first = self.compile_effect_block_output(first);
                let second = self.compile_tail_loop_return_output(second, tail_loop);
                first.append(second)
            }
            Lambda::LstaticRaise(id, args) => {
                if let Some(output) = self.compile_static_raise_jump_output(*id, args) {
                    return output;
                }
                if let Some(output) = self.compile_fallthrough_static_raise_return_output(*id, args)
                {
                    return output;
                }
                if let Some(handler) = self.resolve_static_raise(*id, args) {
                    return self.compile_tail_loop_return_output(&handler, tail_loop);
                }
                return_compiled(self.compile_expr(lam))
            }
            Lambda::LstaticCatch(body, (label, bindings), handler) => {
                // lam_compile.ml:935 — `flatten_nested_caches` is the first
                // step of `compile_staticcatch`. A >1 entry code_table goes
                // through the multi-handler explicit-jump arm
                // (lam_compile.ml:1000-1010).
                let (handlers, flat_body) = flatten_nested_caches(*label, bindings, body, handler);
                if handlers.len() > 1 {
                    return self.compile_multi_staticcatch_tail_loop_return_output(
                        &handlers, flat_body, tail_loop,
                    );
                }
                let uses_fallthrough =
                    self.uses_fallthrough_staticcatch_return(body, *label, bindings, handler);
                let requires_explicit_jump = (self.return_unit_stack.last().copied() == Some(true)
                    && !bindings.is_empty())
                    || self.try_body_depth > 0
                    || self
                        .return_staticcatch_requires_explicit_jump(*label, bindings, body, handler);
                if uses_fallthrough {
                    self.compile_fallthrough_staticcatch_tail_loop_return_output(
                        *label, bindings, body, handler, tail_loop,
                    )
                } else if requires_explicit_jump {
                    self.compile_staticcatch_tail_loop_return_output(
                        *label, bindings, body, handler, tail_loop,
                    )
                } else if no_static_raise_in_handler_like_ocaml(handler)
                    && !lambda_contains_staticcatch(handler)
                    && lambda_contains_static_raise_to_label(body, *label, bindings.len())
                {
                    // Mirror the fallthrough / pseudo-jmp arm from
                    // `compile_return_block`. OCaml's pseudo-jmp path
                    // (compiler/core/lam_compile.ml:983-1008) gates on
                    // `no_static_raise_in_handler`
                    // (compiler/core/lam_compile_context.ml:105-106) which
                    // itself wraps `has_exit_code handler (fun _ -> true)`,
                    // stopping at
                    // Lfunction boundaries. Using `has_exit_code` here lets
                    // handlers whose only static_raises live inside a
                    // nested closure reach the fallthrough emission
                    // (compiler/core/lam_compile.ml:1002-1008), eliminating
                    // the spurious outer explicit-jump layer that
                    // miss_colon_test saw when `lambda_contains_static_raise`
                    // over-counted.
                    self.compile_fallthrough_staticcatch_tail_loop_return_output(
                        *label, bindings, body, handler, tail_loop,
                    )
                } else if lambda_contains_static_raise_to_label(body, *label, bindings.len()) {
                    // OCaml has no `with_static_handler` analog — when
                    // body raises to this label, OCaml emits the handler
                    // ONCE via explicit-jump (lam_compile.ml:1005-1010 for
                    // Assign / lam_compile.ml:1000-1010 for EffectCall).
                    // Rust's `with_static_handler` path inlines the handler
                    // at every raise site via `resolve_static_raise`.
                    // Prefer explicit-jump to match OCaml's single-emission
                    // shape on miss_colon_test / gpr_1698_test.
                    self.compile_staticcatch_tail_loop_return_output(
                        *label, bindings, body, handler, tail_loop,
                    )
                } else {
                    self.with_static_handler(*label, bindings, handler, |this| {
                        this.compile_tail_loop_return_output(body, tail_loop)
                    })
                }
            }
            Lambda::LtryWith(body, exn, handler) => {
                // OCaml's `compile_trywith` preserves the surrounding
                // tail-return context for the catch handler but changes only
                // the try body to `Tail_in_try` (compiler/core/lam_compile.ml:
                // 1315-1344). Compile the body through the normal return path
                // so direct self calls inside `try` stay as calls, while the
                // handler can still trigger the self-tailcall loop.
                let body_block = self.compile_return_block(body);
                let handler_block = self.compile_tail_loop_return_block(handler, tail_loop);
                BlockOutput::make(vec![self.try_statement(body_block, exn, handler_block)])
            }
            Lambda::LtryFinally(body, finally) => {
                BlockOutput::make(vec![self.compile_try_finally(
                    body,
                    finally,
                    |this, lam| this.compile_return_block(lam),
                )])
            }
            Lambda::Lswitch(scrut, switch) => BlockOutput::make(
                self.compile_tail_loop_switch_return_block(scrut, switch, tail_loop),
            ),
            Lambda::LstringSwitch(scrut, cases, default) => {
                BlockOutput::make(self.compile_tail_loop_string_switch_return_block(
                    scrut,
                    cases,
                    default.as_deref(),
                    tail_loop,
                ))
            }
            _ => return_compiled(self.compile_expr(lam)),
        }
    }

    /// [`Self::compile_if_return_output`] in a self tail call loop.
    fn compile_tail_loop_if_return_output(
        &mut self,
        cond: &Lambda,
        then_: &Lambda,
        else_: &Lambda,
        tail_loop: &mut TailLoopState,
    ) -> BlockOutput {
        let cond_compiled = self.compile_expr(cond);
        // lam_compile.ml:1514-1518: compile both branches in
        // `NeedValue should_return` first and emit `return e ? a : b` when
        // neither needs statements. A branch with a self tail call compiles
        // to the loop jump there, so it always has a block.
        if !function_has_self_tailcall(&tail_loop.tail_targets, then_)
            && !function_has_self_tailcall(&tail_loop.tail_targets, else_)
        {
            let then_value = self.compile_expr(then_);
            let else_value = self.compile_expr(else_);
            if then_value.prelude.is_empty() && else_value.prelude.is_empty() {
                let mut block = cond_compiled.prelude;
                block.push(Statement::return_(Expression::cond(
                    cond_compiled.expr,
                    then_value.expr,
                    else_value.expr,
                )));
                return BlockOutput::finished(block);
            }
        }
        let then_block = self.compile_tail_loop_return_block(then_, tail_loop);
        let else_block = self.compile_tail_loop_return_block(else_, tail_loop);

        let mut block = cond_compiled.prelude;

        // Mirror OCaml's Lifthenelse compile (lam_compile.ml:1428-1436), which
        // calls `Js_output.output_as_block` on each compiled branch — that
        // calls `unnest_block` (js_output.ml:77-80) before passing to `S.if_`.
        // OCaml's `block_last_is_return_throw_or_continue` (js_stmt_make.ml:186-193)
        // is non-recursive, so an unnested branch ending in `continue`/`return`/`throw`
        // lets rule 7 fire while a Block-wrapped branch keeps the if-else.
        let then_block = unnest_block(then_block);
        let else_block = unnest_block(else_block);
        let cond_expr = cond_compiled.expr;
        let cond_is_conjunction = matches!(&cond_expr.desc, ExpressionDesc::Bin(BinOp::And, _, _));
        if cond_is_conjunction
            && block_last_is_continue(&then_block)
            && block_last_is_non_continue_terminal(&else_block)
        {
            // OCaml's tail-call path marks self tail-calls `output_finished=True`
            // and `S.if_` rule 5/7 interactions keep the terminal fallback under
            // a negative guard before the `continue` tail
            // (compiler/core/lam_compile.ml:1582-1629,
            // compiler/core/js_stmt_make.ml:247-250). Rust represents the same
            // tail call directly as assignment statements plus `Continue`, so
            // build that shape explicitly before the generic `Statement::if_`
            // simplifier flips it back to a positive guard.
            block.push(Statement::new(StatementDesc::If(
                Expression::not(cond_expr),
                merge_terminal_guard_fallthrough_else(else_block),
                vec![],
            )));
            block.extend(then_block);
            return BlockOutput::make(block);
        }
        block.push(Statement::if_(cond_expr, then_block, else_block));
        BlockOutput::make(block)
    }

    fn compile_short_circuit_tail_loop_return_output(
        &mut self,
        op: ShortCircuitOp,
        lhs: &Lambda,
        rhs: &Lambda,
        tail_loop: &mut TailLoopState,
    ) -> BlockOutput {
        let default = op.default_lambda();
        match op {
            ShortCircuitOp::And => {
                self.compile_tail_loop_if_return_output(lhs, rhs, &default, tail_loop)
            }
            ShortCircuitOp::Or => {
                self.compile_tail_loop_if_return_output(lhs, &default, rhs, tail_loop)
            }
        }
    }

    fn compile_tail_loop_switch_return_block(
        &mut self,
        scrut: &Lambda,
        switch: &LambdaSwitch,
        tail_loop: &mut TailLoopState,
    ) -> Block {
        // As in `compile_switch_return_block`: the plan enters the switch
        // context only for the bodies of its `switch` statements.
        if let Some(plan) = super::untagged_plan(switch) {
            return self.compile_untagged_switch(
                super::lam_compile_variant::UntaggedMode::TailLoopReturn,
                Some(tail_loop),
                scrut,
                switch,
                &plan,
            );
        }
        self.with_switch_depth(|this| {
            this.compile_tail_loop_switch_return_block_inner(scrut, switch, tail_loop)
        })
    }

    fn compile_tail_loop_switch_return_block_inner(
        &mut self,
        scrut: &Lambda,
        switch: &LambdaSwitch,
        tail_loop: &mut TailLoopState,
    ) -> Block {
        if self.uses_named_variant_switch(switch) {
            let scrut_compiled = self.compile_expr(scrut);
            let (mut block, scrut_expr) = if self.named_variant_switch_needs_bound_scrutinee(switch)
            {
                self.bind_switch_scrutinee_once(scrut_compiled.prelude, scrut_compiled.expr)
            } else {
                (scrut_compiled.prelude, scrut_compiled.expr)
            };
            block.extend(
                self.compile_named_variant_switch_tail_loop_return_statements(
                    scrut_expr, switch, tail_loop,
                ),
            );
            return block;
        }

        let scrut_compiled = self.compile_expr(scrut);
        let mut block = scrut_compiled.prelude;
        let grouped_cases = self.grouped_switch_cases(
            &switch.sw_consts,
            switch.sw_failaction.as_deref(),
            |_, _| true,
        );
        let mut cases = Vec::with_capacity(grouped_cases.len());
        let mut group_start = 0;
        while group_start < grouped_cases.len() {
            let mut group_end = group_start;
            while !grouped_cases[group_end].2 {
                group_end += 1;
            }

            let (_, body, _) = &grouped_cases[group_end];
            let compiled_output = self.compile_tail_loop_return_output(body, tail_loop);
            let compiled_finished = compiled_output.finished;
            let compiled_body = compiled_output.block;
            let group_falls_through = compiled_body.is_empty();
            // Tail-loop lowering is Rust-specific, but it must preserve OCaml's
            // `compile_general_cases` break semantics: the last grouped case
            // uses `Js_output.to_break_block`, then return continuation keeps
            // that break only when the source lambda has an exit
            // (compiler/core/lam_compile.ml:613-624;
            // compiler/core/js_output.ml:88-100).
            let should_break = return_case_needs_break(body, compiled_finished);

            for (tag, case_lam, _) in &grouped_cases[group_start..group_end] {
                cases.push((
                    tag.clone(),
                    self.empty_switch_case_clause_for(case_lam),
                    group_falls_through,
                ));
            }
            cases.push((
                grouped_cases[group_end].0.clone(),
                CaseClause {
                    source_loc: self.source_loc_of_lam(body),
                    body: self.with_block_source_loc(body, compiled_body),
                    should_break,
                    comment: None,
                },
                group_falls_through,
            ));

            group_start = group_end + 1;
        }
        let cases =
            self.reorder_fallthrough_return_clauses(cases, |(_, _, falls_through)| *falls_through);
        let cases = cases
            .into_iter()
            .map(|(key, clause, _)| (direct_switch_int(key), clause))
            .collect();

        let default_block = switch
            .sw_failaction
            .as_ref()
            .map(|fallback| self.compile_tail_loop_return_block(fallback, tail_loop))
            .filter(|body| !body.is_empty());

        block.push(Statement::new(StatementDesc::IntSwitch(
            scrut_compiled.expr,
            cases,
            default_block,
        )));
        block
    }

    fn compile_tail_loop_string_switch_return_block(
        &mut self,
        scrut: &Lambda,
        cases: &[(String, Lambda)],
        default: Option<&Lambda>,
        tail_loop: &mut TailLoopState,
    ) -> Block {
        self.with_switch_depth(|this| {
            this.compile_tail_loop_string_switch_return_block_inner(
                scrut, cases, default, tail_loop,
            )
        })
    }

    fn compile_tail_loop_string_switch_return_block_inner(
        &mut self,
        scrut: &Lambda,
        cases: &[(String, Lambda)],
        default: Option<&Lambda>,
        tail_loop: &mut TailLoopState,
    ) -> Block {
        let scrut_compiled = self.compile_expr(scrut);
        let mut block = scrut_compiled.prelude;
        let borrowed_cases: Vec<_> = cases
            .iter()
            .map(|(tag, body)| (SwitchCaseTag::String(tag.clone()), body))
            .collect();

        if let Some(small) = self.compile_small_string_switch_tail_loop_return(
            scrut_compiled.expr.clone(),
            &borrowed_cases,
            default,
            default.is_none(),
            tail_loop,
        ) {
            block.extend(small);
            return block;
        }

        // Match OCaml's generic string-switch case construction
        // (compiler/core/lam_compile.ml:792-794) and its shared
        // `compile_general_cases` break logic
        // (compiler/core/lam_compile.ml:613-624). Tail-loop lowering still
        // compiles case bodies with `compile_tail_loop_return_block`, but
        // fallthrough static-raise cases must keep the same `break;` bit.
        let clauses = self.grouped_tail_loop_return_string_clauses(
            self.grouped_switch_cases(cases, default, |_, _| true),
            SwitchCaseTag::String,
            tail_loop,
        );

        let default_block = default
            .map(|fallback| self.compile_tail_loop_return_block(fallback, tail_loop))
            .filter(|body| !body.is_empty());

        block.push(Statement::new(StatementDesc::StringSwitch(
            scrut_compiled.expr,
            clauses,
            default_block,
        )));
        block
    }

    fn try_compile_self_tailcall_block(
        &mut self,
        apply: &Apply,
        tail_loop: &mut TailLoopState,
    ) -> Option<Block> {
        let Lambda::Lvar(function) = apply.ap_func.as_ref() else {
            return None;
        };
        if !tail_loop
            .tail_targets
            .iter()
            .any(|target| function.same(target))
        {
            return None;
        }

        let mut block = Vec::new();
        let mut args = Vec::new();
        for arg in &apply.ap_args {
            let compiled = self.compile_expr(arg);
            block.extend(compiled.prelude);
            args.push(compiled.expr);
        }

        tail_loop.triggered = true;
        let args = if tail_loop.params.is_empty() {
            Vec::new()
        } else {
            args
        };
        let mut assignments = Vec::new();
        for (param, arg) in tail_loop.params.iter().zip(args) {
            if matches!(&arg.desc, ExpressionDesc::Var(VIdent::Id(id)) if id.same(param)) {
                continue;
            }

            let target = *tail_loop
                .new_params
                .entry(*param)
                .or_insert_with(|| self.fresh_ident(&format!("_{}", param.name())));
            assignments.push(Statement::exp(Expression::bin(
                BinOp::Eq,
                Expression::var(target),
                arg,
            )));
        }
        block.extend(assignments.into_iter().rev());
        block.push(Statement::continue_());
        Some(block)
    }

    fn compile_effect_output(&mut self, lam: &Lambda) -> Compiled {
        match lam {
            Lambda::Llet(kind, id, value, body) => {
                if let Some(compiled) = self.try_compile_record_spread(id, value, body) {
                    return compiled;
                }

                let binding = self.compile_let_binding_output(*kind, id, value);
                let body_compiled = self.compile_effect_output(body);
                let mut prelude = binding.block;
                if binding.finished == OutputFinished::True {
                    return Compiled {
                        prelude,
                        expr: Expression::undefined(false),
                        finished: OutputFinished::True,
                    };
                }
                prelude.extend(body_compiled.prelude);
                Compiled {
                    prelude,
                    expr: body_compiled.expr,
                    finished: body_compiled.finished,
                }
            }
            Lambda::Lapply(apply) => self.compile_apply_call(apply),
            Lambda::LifThenElse(cond, then_, else_) => {
                compiled_from_effect_block(self.compile_if_effect_block(cond, then_, else_))
            }
            Lambda::Lsequence(first, second) => {
                let first = self.compile_effect_output(first);
                let second = self.compile_effect_output(second);
                self.append_effect_output(first, second)
            }
            Lambda::LtryWith(body, exn, handler) => {
                let body_block = self.compile_effect_block(body);
                let handler_block = self.compile_effect_block(handler);
                compiled_from_effect_block(vec![self.try_statement(body_block, exn, handler_block)])
            }
            Lambda::LtryFinally(body, finally) => {
                compiled_from_effect_block(vec![self.compile_try_finally(
                    body,
                    finally,
                    |this, lam| this.compile_effect_block(lam),
                )])
            }
            Lambda::LstaticCatch(body, (label, bindings), handler) => {
                let (handlers, flat_body) = flatten_nested_caches(*label, bindings, body, handler);
                if handlers.len() > 1 {
                    // lam_compile.ml:935 + 1000-1010 — multi-handler
                    // explicit-jump arm for an effect-value continuation.
                    let output = self.compile_multi_staticcatch_effect_output(&handlers, flat_body);
                    return Compiled {
                        prelude: output.block,
                        expr: Expression::undefined(false),
                        finished: output.finished,
                    };
                }
                // OCaml's `Lsequence` compiles its head with
                // `EffectCall Not_tail`; in `compile_staticcatch`
                // (lam_compile.ml:984-1059), that continuation always falls
                // through to the explicit-jump arm. Keep the same shape here
                // instead of inlining the handler at every raise site.
                let output =
                    self.compile_staticcatch_effect_output(*label, bindings, body, handler);
                Compiled {
                    prelude: output.block,
                    expr: Expression::undefined(false),
                    finished: output.finished,
                }
            }
            Lambda::Lswitch(scrut, switch) => Compiled {
                prelude: self.compile_switch_effect_block(scrut, switch),
                expr: Expression::undefined(false),
                finished: OutputFinished::False,
            },
            Lambda::LstringSwitch(scrut, cases, default) => Compiled {
                prelude: self.compile_string_switch_effect_block(scrut, cases, default.as_deref()),
                expr: Expression::undefined(false),
                finished: OutputFinished::False,
            },
            _ => self.compile_expr(lam),
        }
    }

    /// `Js_output.append_output` (js_output.ml:118-138) of two compiled
    /// outputs.
    fn append_effect_output(&self, first: Compiled, second: Compiled) -> Compiled {
        if first.finished == OutputFinished::True {
            return Compiled {
                prelude: first.prelude,
                expr: Expression::undefined(false),
                finished: OutputFinished::True,
            };
        }

        let first_is_pure = js_expr_no_side_effects(&first.expr);
        if first.prelude.is_empty() {
            if first_is_pure {
                return second;
            }
            if second.prelude.is_empty() {
                return Compiled {
                    prelude: vec![],
                    expr: js_seq(first.expr, second.expr),
                    finished: second.finished,
                };
            }
        }

        let mut prelude = first.prelude;
        if !first_is_pure {
            push_effect_expression(&mut prelude, first.expr);
        }
        prelude.extend(second.prelude);
        Compiled {
            prelude,
            expr: second.expr,
            finished: second.finished,
        }
    }

    /// `Js_output.output_as_block` (js_output.ml:82-86) of a `NeedValue`
    /// output: a finished output's value is dropped.
    fn compiled_to_effect_block(&self, compiled: Compiled) -> Block {
        let mut block = compiled.prelude;
        if compiled.finished == OutputFinished::True {
            return block;
        }
        push_effect_expression(&mut block, compiled.expr);
        block
    }

    fn compile_if_effect_block(&mut self, cond: &Lambda, then_: &Lambda, else_: &Lambda) -> Block {
        let cond_compiled = self.compile_expr(cond);
        let then_compiled = self.compile_expr(then_);
        let else_compiled = self.compile_expr(else_);

        let then_prelude_empty = then_compiled.prelude.is_empty();
        let else_prelude_empty = else_compiled.prelude.is_empty();
        let then_expr_pure = js_expr_no_side_effects(&then_compiled.expr);
        let else_expr_pure = js_expr_no_side_effects(&else_compiled.expr);

        let mut block = cond_compiled.prelude;
        let cond_expr = cond_compiled.expr;

        if then_prelude_empty && else_prelude_empty {
            match (
                remove_pure_subexpression(then_compiled.expr.clone()),
                remove_pure_subexpression(else_compiled.expr.clone()),
            ) {
                (None, None) => {
                    // OCaml's `S.if_ cond []` (lam_compile.ml `compile_ifthenelse`).
                    push_s_if_empty(&mut block, cond_expr);
                    return block;
                }
                (Some(then_expr), Some(else_expr)) => {
                    push_effect_expression(
                        &mut block,
                        Expression::cond(cond_expr, then_expr, else_expr),
                    );
                    return block;
                }
                (Some(then_expr), None) => {
                    block.push(Statement::if_(
                        cond_expr,
                        vec![Statement::exp(then_expr)],
                        vec![],
                    ));
                    return block;
                }
                (None, Some(else_expr)) => {
                    block.push(Statement::if_(
                        Expression::not(cond_expr),
                        vec![Statement::exp(else_expr)],
                        vec![],
                    ));
                    return block;
                }
            }
        }

        // Mirror OCaml's Lifthenelse compile path (lam_compile.ml:1428-1436),
        // which calls `Js_output.output_as_block` on each branch — that calls
        // `unnest_block` (js_output.ml:77-80) before passing to `S.if_`.
        // OCaml's `block_last_is_return_throw_or_continue` (js_stmt_make.ml:186-193)
        // is non-recursive, so an unnested branch ending in a terminal allows
        // rule 7 to fire while a Block-wrapped branch keeps the if-else.
        if then_prelude_empty && then_expr_pure {
            block.push(Statement::if_(
                Expression::not(cond_expr),
                unnest_block(self.compile_effect_block(else_)),
                vec![],
            ));
            return block;
        }

        if else_prelude_empty && else_expr_pure {
            block.push(Statement::if_(
                cond_expr,
                unnest_block(self.compile_effect_block(then_)),
                vec![],
            ));
            return block;
        }

        // OCaml S.if_ rule 5 (js_stmt_make.ml:247-248): when the else branch
        // is *exactly* `[Return _]`, flip to `if (!cond) { return; }` and
        // emit the then branch as sibling statements.
        let then_block = unnest_block(self.compile_effect_block(then_));
        let else_block = unnest_block(self.compile_effect_block(else_));
        if matches!(
            else_block.as_slice(),
            [stmt] if matches!(stmt.desc, StatementDesc::Return(_))
        ) {
            block.push(Statement::if_(
                Expression::not(cond_expr),
                else_block,
                vec![],
            ));
            block.extend(then_block);
            return block;
        }
        // OCaml S.if_ rule 7 (js_stmt_make.ml:249-250): when the then branch
        // ends with return/throw/continue/break, keep `if (cond) { then }`
        // and append the else branch as sibling statements.
        if !then_block.is_empty() && block_last_is_terminal(&then_block) {
            block.push(Statement::if_(cond_expr, then_block, vec![]));
            block.extend(else_block);
            return block;
        }

        block.push(Statement::if_(cond_expr, then_block, else_block));
        block
    }

    fn compile_if_assignment_block(
        &mut self,
        result: &Ident,
        cond: &Lambda,
        then_: &Lambda,
        else_: &Lambda,
    ) -> Block {
        let cond_compiled = self.compile_expr(cond);
        let then_block = self.compile_assign_to_target_block(result, then_);
        let else_block = self.compile_assign_to_target_block(result, else_);

        let mut block = cond_compiled.prelude;
        block.extend(self.compile_test_assignment_block(
            result,
            cond_compiled.expr,
            then_block,
            else_block,
        ));
        block
    }

    pub(crate) fn compile_test_assignment_block(
        &self,
        result: &Ident,
        cond: Expression,
        then_block: Block,
        else_block: Block,
    ) -> Block {
        let (cond, then_block, else_block) =
            normalize_if_assignment_merge_order(cond, then_block, else_block);
        match (
            self.take_single_result_assignment(result, then_block),
            self.take_single_result_assignment(result, else_block),
        ) {
            (Ok(then_expr), Ok(else_expr)) => {
                vec![self.result_assignment(result, Expression::cond(cond, then_expr, else_expr))]
            }
            (then_result, else_result) => {
                let then_block = match then_result {
                    Ok(expr) => vec![self.result_assignment(result, expr)],
                    Err(block) => block,
                };
                let else_block = match else_result {
                    Ok(expr) => vec![self.result_assignment(result, expr)],
                    Err(block) => block,
                };
                vec![Statement::if_(cond, then_block, else_block)]
            }
        }
    }

    fn compile_declared_if_block(
        &self,
        kind: LetKind,
        id: &Ident,
        cond: Expression,
        then_block: Block,
        else_block: Block,
    ) -> Block {
        let (cond, then_block, else_block) =
            normalize_if_assignment_merge_order(cond, then_block, else_block);
        match (
            self.take_single_result_assignment(id, then_block),
            self.take_single_result_assignment(id, else_block),
        ) {
            (Ok(then_expr), Ok(else_expr)) => {
                vec![Statement::variable(VariableDeclaration {
                    ident: *id,
                    value: Some(Expression::cond(cond, then_expr, else_expr)),
                    property: kind,
                    ident_info: IdentInfo::default(),
                })]
            }
            (then_result, else_result) => {
                let then_block = match then_result {
                    Ok(expr) => vec![self.result_assignment(id, expr)],
                    Err(block) => block,
                };
                let else_block = match else_result {
                    Ok(expr) => vec![self.result_assignment(id, expr)],
                    Err(block) => block,
                };

                vec![
                    Statement::variable(VariableDeclaration {
                        ident: *id,
                        value: None,
                        property: kind,
                        ident_info: IdentInfo::default(),
                    }),
                    Statement::if_(cond, then_block, else_block),
                ]
            }
        }
    }

    pub(crate) fn take_single_result_assignment(
        &self,
        id: &Ident,
        block: Block,
    ) -> Result<Expression, Block> {
        let [stmt] = block.as_slice() else {
            return Err(block);
        };
        let StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Bin(BinOp::Eq, lhs, ..),
            ..
        }) = &stmt.desc
        else {
            return Err(block);
        };
        let ExpressionDesc::Var(crate::js_ir::VIdent::Id(target)) = &lhs.desc else {
            return Err(block);
        };
        if !target.same(id) {
            return Err(block);
        }

        let stmt = block.into_iter().next().expect("single-statement block");
        let Statement {
            desc:
                StatementDesc::Exp(Expression {
                    desc: ExpressionDesc::Bin(BinOp::Eq, _, rhs),
                    ..
                }),
            ..
        } = stmt
        else {
            unreachable!("validated single assignment shape")
        };
        Ok(*rhs)
    }

    fn result_assignment(&self, id: &Ident, expr: Expression) -> Statement {
        Statement::exp(Expression::bin(BinOp::Eq, Expression::var(*id), expr))
    }

    /// Statement-valued forms make OCaml's preliminary `NeedValue` pass return
    /// a non-empty block before the `S.if_` fallback
    /// (compiler/core/lam_compile.ml:1495-1524), so Rust must not rebuild them
    /// from later `Return` blocks as if they were pure expressions.
    fn lambda_contains_statement_value_form(lam: &Lambda) -> bool {
        match lam {
            Lambda::Lswitch(_, _)
            | Lambda::LstringSwitch(_, _, _)
            | Lambda::LstaticCatch(_, _, _)
            | Lambda::LtryWith(_, _, _)
            | Lambda::LtryFinally(_, _)
            | Lambda::Lwhile(_, _)
            | Lambda::Lfor(_, _, _, _, _)
            | Lambda::Lfor_of(_, _, _)
            | Lambda::Lfor_await_of(_, _, _)
            | Lambda::LstaticRaise(_, _)
            | Lambda::Lbreak
            | Lambda::Lcontinue
            // OCaml `compile_assign` (lam_compile.ml) always emits the
            // assignment as a statement, whatever the continuation.
            | Lambda::Lassign(_, _) => true,
            Lambda::Llet(_, _, value, body) => {
                Self::lambda_contains_statement_value_form(value)
                    || Self::lambda_contains_statement_value_form(body)
            }
            Lambda::Lletrec(bindings, body) => {
                bindings
                    .iter()
                    .any(|(_, binding)| Self::lambda_contains_statement_value_form(binding))
                    || Self::lambda_contains_statement_value_form(body)
            }
            Lambda::Lsequence(first, second) => {
                Self::lambda_contains_statement_value_form(first)
                    || Self::lambda_contains_statement_value_form(second)
            }
            Lambda::LifThenElse(cond, then_, else_) => {
                Self::lambda_contains_statement_value_form(cond)
                    || Self::lambda_contains_statement_value_form(then_)
                    || Self::lambda_contains_statement_value_form(else_)
            }
            Lambda::Lprim(info) => info
                .args
                .iter()
                .any(Self::lambda_contains_statement_value_form),
            Lambda::Lapply(apply) => {
                Self::lambda_contains_statement_value_form(&apply.ap_func)
                    || apply
                        .ap_args
                        .iter()
                        .any(Self::lambda_contains_statement_value_form)
            }
            Lambda::Lfunction(_) => false,
            _ => false,
        }
    }

    /// Mirrors OCaml's `Js_stmt_make.if_ ~declaration` promotion
    /// (js_stmt_make.ml:304-312): when the final statement of `body` is
    /// `id = expr;`, collapse the pending `let id;` and the assignment into a
    /// single `let id = expr;`. Otherwise prepend the bare declaration.
    /// Every earlier statement in `body` was produced BEFORE `id` was brought
    /// into scope (scrut prelude, switch dispatch, etc.), so none of them can
    /// reference `id`; moving the declaration past them preserves semantics
    /// while matching OCaml's shape.
    fn prepend_declaration_or_fold_final_assignment(
        kind: LetKind,
        id: &Ident,
        mut body: Block,
    ) -> Block {
        if let Some(last) = body.last() {
            if let StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Bin(BinOp::Eq, lhs, rhs),
                ..
            }) = &last.desc
            {
                if let ExpressionDesc::Var(VIdent::Id(target)) = &lhs.desc {
                    if target.same(id) {
                        let rhs_expr = rhs.as_ref().clone();
                        body.pop();
                        body.push(Statement::variable(VariableDeclaration {
                            ident: *id,
                            value: Some(rhs_expr),
                            property: kind,
                            ident_info: IdentInfo::default(),
                        }));
                        return body;
                    }
                }
            }
        }
        let mut result = Vec::with_capacity(body.len() + 1);
        result.push(Statement::variable(VariableDeclaration {
            ident: *id,
            value: None,
            property: kind,
            ident_info: IdentInfo::default(),
        }));
        result.extend(body);
        result
    }

    /// Mirrors OCaml's Lifthenelse `EffectCall (Maybe_tail_is_return)` arm
    /// (compiler/core/lam_compile.ml:1495-1524). When both branches compile to
    /// `{block=[]; value=Some e}` via `NeedValue`, OCaml emits
    /// `Return(Cond(cond, out1, out2))` where each `out` is the branch's
    /// tail expression (e.g. `Seq(log, undef)` for `Lsequence(log, Lconst undef)`).
    /// `E.econd` then folds `Cond(Seq(a,undef), Seq(b,undef))` to
    /// `Seq(Cond(a,b), undef)`, which `js_pass_flatten`'s Return(Seq) +
    /// Exp(Cond) rules later flatten into the clean `[If(cond, [Exp a], [Exp b]);
    /// Return undef]` shape printed as `if (cond) { a; } else { b; }`.
    ///
    /// Rust's `compile_return_block` for `Lsequence(effect, Lconst undef)`
    /// pre-flattens to `[Exp effect; Return Undefined]` - losing the `Seq`
    /// shape that `take_return_tail_expr`'s undefined-rejection guard then
    /// refuses to reconstruct. Fold here explicitly so the caller can match
    /// OCaml's `Return(Cond(Seq, Seq))` construction.
    ///
    /// Returns `Some(Seq(e1, Seq(e2, ..., Return-expr)))` iff the block is
    /// exactly `[Exp e1, Exp e2, ..., Return last]`. Accept a single
    /// `[Return tail]` block as well because inner `Lifthenelse` cases can
    /// already have folded to `Return(Seq(Cond, undef))`.
    fn try_fold_effect_only_return_tail(&self, block: &Block) -> Option<Expression> {
        let (last, prefix) = block.split_last()?;
        let Statement {
            desc: StatementDesc::Return(tail_expr),
            ..
        } = last
        else {
            return None;
        };

        let mut result = tail_expr.clone();
        for stmt in prefix.iter().rev() {
            let StatementDesc::Exp(effect) = &stmt.desc else {
                return None;
            };
            result = js_seq(effect.clone(), result);
        }
        Some(result)
    }

    /// lam_compile.ml:1400-1545 `compile_ifthenelse` in a return
    /// continuation: `return e ? a : b` is finished (lines 1533-1537); the
    /// `S.if_` fallback is a plain `Js_output.make`.
    fn compile_if_return_output(
        &mut self,
        cond: &Lambda,
        then_: &Lambda,
        else_: &Lambda,
    ) -> BlockOutput {
        let cond_compiled = self.compile_expr(cond);
        let then_block_raw = self.compile_return_block(then_);
        let else_block_raw = self.compile_return_block(else_);

        // OCaml's preliminary `NeedValue should_return` pass is the reference
        // shape (compiler/core/lam_compile.ml:1495-1524). Rust's
        // `compile_expr` currently flattens short-circuit primitives to JS
        // `&&`/`||` earlier than OCaml's `compile_sequand`/`compile_sequor`
        // path (compiler/core/lam_compile.ml:1663-1664), so preserve the
        // nested conditional by folding return blocks when the original
        // branches contain no statement-valued forms. Switches/static catches
        // stay excluded because OCaml's NeedValue pass keeps their prelude,
        // which must fall through to `S.if_` below.
        if !Self::lambda_contains_statement_value_form(then_)
            && !Self::lambda_contains_statement_value_form(else_)
        {
            if let (Some(then_seq), Some(else_seq)) = (
                self.try_fold_effect_only_return_tail(&then_block_raw),
                self.try_fold_effect_only_return_tail(&else_block_raw),
            ) {
                let mut block = cond_compiled.prelude;
                block.push(Statement::return_(Expression::cond(
                    cond_compiled.expr,
                    then_seq,
                    else_seq,
                )));
                return BlockOutput::finished(block);
            }
        }

        // OCaml first compiles both branches in `NeedValue should_return` and
        // only emits `Return(E.econd ...)` when both results are exactly
        // `{block = []; value = Some _}` (compiler/core/lam_compile.ml:
        // 1495-1524). Do the same preliminary value pass instead of
        // reconstructing a value from later return blocks: switches and other
        // statement-producing forms must keep their prelude, which makes OCaml
        // fall through to `S.if_` below.
        let then_value = self.compile_expr(then_);
        let else_value = self.compile_expr(else_);
        if then_value.prelude.is_empty() && else_value.prelude.is_empty() {
            let mut block = cond_compiled.prelude;
            block.push(Statement::return_(Expression::cond(
                cond_compiled.expr,
                then_value.expr,
                else_value.expr,
            )));
            return BlockOutput::finished(block);
        }

        // Keep the raw `[Return(Seq(...))]` shape so OCaml's `S.if_` rules
        // (js_stmt_make.ml:244-250) see the same input they would in OCaml.
        // OCaml runs `js_pass_flatten` AFTER `S.if_` has committed; matching
        // that ordering is what lets the rule-247-248 flip
        // (single-Return else → flip and chain) and rule-249-250 (terminal
        // then → drop else) fire on `Return Seq(Cond, undef)`-style ELSEs
        // produced by `compile_if_return_block` for inner `Lifthenelse`
        // branches whose tails fold via `E.econd`'s Seq+Undefined rule.
        let mut block = cond_compiled.prelude;
        block.extend(self.compile_test_return_block_with_fallback(
            cond_compiled.expr,
            then_block_raw,
            else_block_raw,
        ));
        BlockOutput::make(block)
    }

    pub(crate) fn compile_test_return_block(
        &self,
        cond: Expression,
        then_block: Block,
        else_block: Block,
    ) -> Block {
        self.compile_test_return_block_with_fallback(cond, then_block, else_block)
    }

    /// Separate the raw blocks used for rule-4 folding
    /// (js_stmt_make.ml:244-246 — both branches single-return) from the
    /// pre-normalized blocks used as the `Statement::if_` fallback when
    /// rule 4 can't fire. OCaml runs `js_pass_flatten` AFTER `S.if_`, so
    /// the raw `[Return(Seq(...))]` shape survives until rule 4's chance
    /// to collapse has passed.
    fn compile_test_return_block_with_fallback(
        &self,
        cond: Expression,
        then_fallback: Block,
        else_fallback: Block,
    ) -> Block {
        // OCaml's `S.if_` rule 4 (js_stmt_make.ml:244-246) folds to
        // `return_stmt (E.econd e ret_ifso ret_ifnot)` ONLY when both
        // branches are `[Return _]` — a strictly-single-Return statement each.
        // Multi-statement effect-plus-Return shapes like
        // `[Exp e1, ..., Exp eN, Return X]` do NOT match rule 4; they take
        // rule 249-250 (`block_last_is_return_throw_or_continue ifso` → flip
        // to sequence) via the `Statement::if_` fallback, which wraps the
        // flipped sequence in `S.block` (js_stmt_make.ml:37-42) → a single
        // `Block` statement that hides the trailing Return from the OUTER
        // `S.if_`'s rule-249 check. Without this gate, `take_return_tail_expr`
        // would fold any effect-prefix via `Seq` → `Return(Cond(Seq,Seq))` →
        // after `js_pass_flatten`, a top-level `Return` that the outer
        // `Statement::if_` happily flips, collapsing OCaml's outer if/else.
        // (js_json_test's JSONNull switch callback: OCaml preserves the outer
        // `if (typeof ty !== "object") { ... } else { ... }` because the inner
        // flip produces a Block-wrapped 3-statement sequence; Rust's aggressive
        // fold lost that shape.)
        // The fold inspects the same raw blocks that are used as the
        // fallback; move the single return expressions out instead of
        // cloning both branches.
        if strict_single_return_expr(&then_fallback).is_some()
            && strict_single_return_expr(&else_fallback).is_some()
        {
            let take_return = |block: Block| match block.into_iter().next().map(|stmt| stmt.desc) {
                Some(StatementDesc::Return(expr)) => expr,
                _ => unreachable!("strict single return block"),
            };
            let then_expr = take_return(then_fallback);
            let else_expr = take_return(else_fallback);
            // Go through `S.if_` instead of calling `E.econd` directly:
            // OCaml applies the `Js_not` branch swap before the
            // single-Return fold (compiler/core/js_stmt_make.ml:237-246).
            return vec![Statement::if_(
                cond,
                vec![Statement::return_(then_expr)],
                vec![Statement::return_(else_expr)],
            )];
        }
        // OCaml S.if_ rule 5 (js_stmt_make.ml:247-248): when the
        // else branch is *exactly* `[Return _]`, flip to
        // `if (!cond) { return _; }` and emit the then branch as
        // sibling statements. This matches the `if (cond) { return; }
        // body;` early-return shape OCaml produces for function
        // bodies like `if cond then body else ()` in return context.
        if matches!(
            else_fallback.as_slice(),
            [stmt] if matches!(stmt.desc, StatementDesc::Return(_))
        ) {
            let mut out = vec![Statement::if_(Expression::not(cond), else_fallback, vec![])];
            out.extend(then_fallback);
            // OCaml wraps the rule-5 result with `block
            // ({If ...} :: ifso)` (compiler/core/js_stmt_make.ml:
            // 247-248, with `block` at lines 37-42). That block
            // boundary is observable by an outer `S.if_`: it hides the
            // trailing return until `js_pass_flatten` runs later.
            return vec![Statement::block(out)];
        }
        // Use the normalized fallback blocks when we can't collapse
        // to `Return(Cond)`, matching the previous behavior for
        // non-both-single-return cases.
        vec![Statement::if_(cond, then_fallback, else_fallback)]
    }

    /// A switch case in an `Assign result` continuation:
    /// `Js_output.to_break_block` (js_output.ml:88-100) breaks unless the
    /// output is finished.
    pub(crate) fn compile_switch_value_block(&mut self, result: &Ident, lam: &Lambda) -> Block {
        let output = self.compile_assign_to_target_output(result, lam);
        let mut block = output.block;
        if output.finished != OutputFinished::True {
            block.push(Statement::break_());
        }
        block
    }

    pub(crate) fn compile_assign_to_target_block(&mut self, result: &Ident, lam: &Lambda) -> Block {
        self.compile_assign_to_target_output(result, lam).block
    }

    /// `compile_lambda {cxt with continuation = Assign result} lam`, with
    /// the output's `finished` flag.
    pub(crate) fn compile_assign_to_target_output(
        &mut self,
        result: &Ident,
        lam: &Lambda,
    ) -> BlockOutput {
        match lam {
            Lambda::Llet(kind, id, value, body) => {
                if let Some(compiled) = self.try_compile_record_spread(id, value, body) {
                    let mut block = compiled.prelude;
                    block.push(Statement::exp(Expression::bin(
                        BinOp::Eq,
                        Expression::var(*result),
                        compiled.expr,
                    )));
                    return BlockOutput::make(block);
                }
                // lam_compile.ml:1867-1877: compile the binding, then the
                // body, then `append_output`, which keeps a finished binding
                // alone.
                let binding = self.compile_let_binding_output(*kind, id, value);
                let body = self.compile_assign_to_target_output(result, body);
                binding.append(body)
            }
            Lambda::Lsequence(first, second) => {
                // lam_compile.ml:1905-1910.
                let first = self.compile_effect_block_output(first);
                let second = self.compile_assign_to_target_output(result, second);
                first.append(second)
            }
            Lambda::LstaticCatch(body, (label, bindings), handler) => {
                // OCaml's `compile_staticcatch` (lam_compile.ml:1063-1101)
                // takes the explicit-jump arm for an `Assign` continuation.
                let (handlers, flat_body) = flatten_nested_caches(*label, bindings, body, handler);
                if handlers.len() > 1 {
                    self.compile_multi_staticcatch_assignment_output(result, &handlers, flat_body)
                } else {
                    self.compile_staticcatch_assignment_output(
                        result, *label, bindings, body, handler,
                    )
                }
            }
            Lambda::LstaticRaise(id, args) => {
                // OCaml's `compile_staticraise` (lam_compile.ml:969-986)
                // ignores the enclosing Assign continuation and emits only the
                // argument assignments + `exit = N`.
                if let Some(output) = self.compile_static_raise_jump_output(*id, args) {
                    return output;
                }
                if let Some(handler) = self.resolve_static_raise(*id, args) {
                    return self.compile_assign_to_target_output(result, &handler);
                }
                let compiled = self.compile_expr(lam);
                assign_compiled(result, compiled)
            }
            Lambda::Lapply(_)
            | Lambda::LtryWith(..)
            | Lambda::LtryFinally(..)
            | Lambda::LifThenElse(..)
            | Lambda::Lswitch(..)
            | Lambda::LstringSwitch(..) => {
                BlockOutput::make(self.compile_assign_to_target_unfinished_block(result, lam))
            }
            Lambda::Lprim(info)
                if short_circuit_primitive(&info.primitive, &info.args).is_some() =>
            {
                BlockOutput::make(self.compile_assign_to_target_unfinished_block(result, lam))
            }
            _ => {
                let compiled = self.compile_expr(lam);
                assign_compiled(result, compiled)
            }
        }
    }

    /// The arms of `compile_lambda {cxt with continuation = Assign result}`
    /// whose output is never finished.
    fn compile_assign_to_target_unfinished_block(&mut self, result: &Ident, lam: &Lambda) -> Block {
        match lam {
            Lambda::Lapply(apply) => {
                let compiled = self.compile_apply_call(apply);
                let mut block = compiled.prelude;
                block.push(Statement::exp(Expression::bin(
                    BinOp::Eq,
                    Expression::var(*result),
                    compiled.expr,
                )));
                block
            }
            Lambda::LtryWith(body, exn, handler) => {
                let body_block = self.compile_assign_to_target_block(result, body);
                let handler_block = self.compile_assign_to_target_block(result, handler);
                vec![self.try_statement(body_block, exn, handler_block)]
            }
            Lambda::LtryFinally(body, finally) => {
                vec![self.compile_try_finally(body, finally, |this, lam| {
                    this.compile_assign_to_target_block(result, lam)
                })]
            }
            Lambda::LifThenElse(cond, then_, else_) => {
                self.compile_if_assignment_block(result, cond, then_, else_)
            }
            // compile_sequand / compile_sequor with an `Assign v` continuation
            // (lam_compile.ml:1138-1210).
            Lambda::Lprim(info)
                if short_circuit_primitive(&info.primitive, &info.args).is_some() =>
            {
                let (op, lhs, rhs) =
                    short_circuit_primitive(&info.primitive, &info.args).expect("checked above");
                let lhs_compiled = self.compile_expr(lhs);
                let rhs_compiled = self.compile_expr(rhs);
                let assign = |value: Expression| {
                    Statement::exp(Expression::bin(BinOp::Eq, Expression::var(*result), value))
                };
                let mut block = lhs_compiled.prelude;
                if rhs_compiled.prelude.is_empty() {
                    let op = match op {
                        ShortCircuitOp::And => BinOp::And,
                        ShortCircuitOp::Or => BinOp::Or,
                    };
                    block.push(assign(Expression::bin(
                        op,
                        lhs_compiled.expr,
                        rhs_compiled.expr,
                    )));
                    return block;
                }
                let mut rhs_block = rhs_compiled.prelude;
                rhs_block.push(assign(rhs_compiled.expr));
                block.push(Statement::if_(
                    op.test_expr(lhs_compiled.expr),
                    rhs_block,
                    vec![assign(op.default_expr())],
                ));
                block
            }
            Lambda::Lswitch(scrut, switch) => {
                self.compile_switch_assignment_block(result, scrut, switch)
            }
            Lambda::LstringSwitch(scrut, cases, default) => self
                .compile_string_switch_assignment_block(result, scrut, cases, default.as_deref()),
            Lambda::Lprim(info)
                if short_circuit_primitive(&info.primitive, &info.args).is_some() =>
            {
                let (op, lhs, rhs) = short_circuit_primitive(&info.primitive, &info.args)
                    .expect("matched short-circuit primitive");
                let lhs = self.compile_expr(lhs);
                let rhs = self.compile_expr(rhs);
                let mut block = lhs.prelude;
                // compile_sequand/compile_sequor Assign (lam_compile.ml:1153-1162,
                // 1193-1202) write the existing target in both branches instead
                // of creating a NeedValue temporary and assigning it afterwards.
                if rhs.prelude.is_empty() {
                    let operator = match op {
                        ShortCircuitOp::And => BinOp::And,
                        ShortCircuitOp::Or => BinOp::Or,
                    };
                    block.push(
                        self.result_assignment(
                            result,
                            Expression::bin(operator, lhs.expr, rhs.expr),
                        ),
                    );
                } else {
                    let mut body = rhs.prelude;
                    body.push(self.result_assignment(result, rhs.expr));
                    block.push(Statement::if_(
                        op.test_expr(lhs.expr),
                        body,
                        vec![self.result_assignment(result, op.default_expr())],
                    ));
                }
                block
            }
            _ => unreachable!("compile_assign_to_target_output handles {lam:?}"),
        }
    }

    fn compile_switch_assignment_block(
        &mut self,
        result: &Ident,
        scrut: &Lambda,
        switch: &LambdaSwitch,
    ) -> Block {
        // An untagged plan enters the switch context only for the bodies of
        // its `switch` statements (lam_compile.ml `compile_untagged_plan`).
        if let Some(plan) = super::untagged_plan(switch) {
            return self.compile_untagged_switch(
                super::lam_compile_variant::UntaggedMode::Assign(result),
                None,
                scrut,
                switch,
                &plan,
            );
        }
        self.with_switch_depth(|this| {
            this.compile_switch_assignment_block_inner(result, scrut, switch)
        })
    }

    fn compile_switch_assignment_block_inner(
        &mut self,
        result: &Ident,
        scrut: &Lambda,
        switch: &LambdaSwitch,
    ) -> Block {
        if self.uses_named_variant_switch(switch) {
            let scrut_compiled = self.compile_expr(scrut);
            let (mut block, scrut_expr) = if self.named_variant_switch_needs_bound_scrutinee(switch)
            {
                self.bind_switch_scrutinee_once(scrut_compiled.prelude, scrut_compiled.expr)
            } else {
                (scrut_compiled.prelude, scrut_compiled.expr)
            };
            block.extend(
                self.compile_named_variant_switch_assignment_statements(result, scrut_expr, switch),
            );
            return block;
        }

        let scrut_compiled = self.compile_expr(scrut);
        let mut block = scrut_compiled.prelude;

        let cases: Vec<_> = self
            .grouped_switch_cases(
                &switch.sw_consts,
                switch.sw_failaction.as_deref(),
                |_, _| true,
            )
            .into_iter()
            .map(|(tag, body, is_last)| {
                (
                    direct_switch_int(tag),
                    if is_last {
                        crate::js_ir::CaseClause {
                            source_loc: self.source_loc_of_lam(body),
                            body: {
                                let value_block = self.compile_switch_value_block(result, body);
                                self.with_block_source_loc(body, value_block)
                            },
                            should_break: false,
                            comment: None,
                        }
                    } else {
                        self.empty_switch_case_clause_for(body)
                    },
                )
            })
            .collect();

        let default_block = switch.sw_failaction.as_ref().map(|fallback| {
            let block = self.compile_assign_to_target_block(result, fallback);
            self.with_block_source_loc(fallback, block)
        });

        block.push(Statement::new(StatementDesc::IntSwitch(
            scrut_compiled.expr,
            cases,
            default_block,
        )));
        block
    }

    fn compile_string_switch_assignment_block(
        &mut self,
        result: &Ident,
        scrut: &Lambda,
        cases: &[(String, Lambda)],
        default: Option<&Lambda>,
    ) -> Block {
        self.with_switch_depth(|this| {
            this.compile_string_switch_assignment_block_inner(result, scrut, cases, default)
        })
    }

    fn compile_string_switch_assignment_block_inner(
        &mut self,
        result: &Ident,
        scrut: &Lambda,
        cases: &[(String, Lambda)],
        default: Option<&Lambda>,
    ) -> Block {
        let scrut_compiled = self.compile_expr(scrut);
        let mut block = scrut_compiled.prelude;
        let borrowed_cases: Vec<_> = cases
            .iter()
            .map(|(tag, body)| (SwitchCaseTag::String(tag.clone()), body))
            .collect();

        if let Some(small) = self.compile_small_string_switch_assignment(
            result,
            scrut_compiled.expr.clone(),
            &borrowed_cases,
            default,
            default.is_none(),
        ) {
            block.extend(small);
            return block;
        }

        let clauses: Vec<_> = self
            .grouped_switch_cases(cases, default, |_, _| true)
            .into_iter()
            .map(|(tag, body, is_last)| crate::js_ir::StringClause {
                tag_type: SwitchCaseTag::String(tag),
                clause: if is_last {
                    crate::js_ir::CaseClause {
                        source_loc: self.source_loc_of_lam(body),
                        body: {
                            let value_block = self.compile_switch_value_block(result, body);
                            self.with_block_source_loc(body, value_block)
                        },
                        should_break: false,
                        comment: None,
                    }
                } else {
                    self.empty_switch_case_clause_for(body)
                },
            })
            .collect();

        let default_block = default.map(|fallback| {
            let block = self.compile_assign_to_target_block(result, fallback);
            self.with_block_source_loc(fallback, block)
        });

        block.push(Statement::new(StatementDesc::StringSwitch(
            scrut_compiled.expr,
            clauses,
            default_block,
        )));
        block
    }

    fn compile_switch_return_block(&mut self, scrut: &Lambda, switch: &LambdaSwitch) -> Block {
        if let Some(plan) = super::untagged_plan(switch) {
            return self.compile_untagged_switch(
                super::lam_compile_variant::UntaggedMode::Return,
                None,
                scrut,
                switch,
                &plan,
            );
        }
        self.with_switch_depth(|this| this.compile_switch_return_block_inner(scrut, switch))
    }

    fn compile_switch_return_block_inner(
        &mut self,
        scrut: &Lambda,
        switch: &LambdaSwitch,
    ) -> Block {
        if self.uses_named_variant_switch(switch) {
            let scrut_compiled = self.compile_expr(scrut);
            let (mut block, scrut_expr) = if self.named_variant_switch_needs_bound_scrutinee(switch)
            {
                self.bind_switch_scrutinee_once(scrut_compiled.prelude, scrut_compiled.expr)
            } else {
                (scrut_compiled.prelude, scrut_compiled.expr)
            };
            block.extend(self.compile_named_variant_switch_return_statements(scrut_expr, switch));
            return block;
        }

        let scrut_compiled = self.compile_expr(scrut);
        let mut block = scrut_compiled.prelude;

        let grouped_cases = self.grouped_switch_cases(
            &switch.sw_consts,
            switch.sw_failaction.as_deref(),
            |_, _| true,
        );
        let mut cases = Vec::with_capacity(grouped_cases.len());
        let mut group_start = 0;
        while group_start < grouped_cases.len() {
            let mut group_end = group_start;
            while !grouped_cases[group_end].2 {
                group_end += 1;
            }

            let (_, body, _) = &grouped_cases[group_end];
            let compiled_output = self.compile_return_output(body);
            let compiled_finished = compiled_output.finished;
            let compiled_body = compiled_output.block;
            let group_falls_through = compiled_body.is_empty();
            // Mirror OCaml's `lam_compile.ml` pseudo-jmp emission: when a
            // case body resolved away through a fallthrough static-raise
            // handler, OCaml still prints an explicit `break;` to exit the
            // switch so the subsequent appended handler reads cleanly.
            let should_break = return_case_needs_break(body, compiled_finished);

            for (tag, case_lam, _) in &grouped_cases[group_start..group_end] {
                cases.push((
                    tag.clone(),
                    self.empty_switch_case_clause_for(case_lam),
                    group_falls_through,
                ));
            }
            cases.push((
                grouped_cases[group_end].0.clone(),
                crate::js_ir::CaseClause {
                    source_loc: self.source_loc_of_lam(body),
                    body: self.with_block_source_loc(body, compiled_body),
                    should_break,
                    comment: None,
                },
                group_falls_through,
            ));

            group_start = group_end + 1;
        }
        let cases =
            self.reorder_fallthrough_return_clauses(cases, |(_, _, falls_through)| *falls_through);
        let cases = cases
            .into_iter()
            .map(|(key, clause, _)| (direct_switch_int(key), clause))
            .collect();

        let default_block = switch
            .sw_failaction
            .as_ref()
            .map(|fallback| self.compile_return_block(fallback))
            .filter(|body| !body.is_empty());

        block.push(Statement::new(StatementDesc::IntSwitch(
            scrut_compiled.expr,
            cases,
            default_block,
        )));
        block
    }

    fn compile_string_switch_return_block(
        &mut self,
        scrut: &Lambda,
        cases: &[(String, Lambda)],
        default: Option<&Lambda>,
    ) -> Block {
        self.with_switch_depth(|this| {
            this.compile_string_switch_return_block_inner(scrut, cases, default)
        })
    }

    fn compile_string_switch_return_block_inner(
        &mut self,
        scrut: &Lambda,
        cases: &[(String, Lambda)],
        default: Option<&Lambda>,
    ) -> Block {
        let scrut_compiled = self.compile_expr(scrut);
        let mut block = scrut_compiled.prelude;
        let borrowed_cases: Vec<_> = cases
            .iter()
            .map(|(tag, body)| (SwitchCaseTag::String(tag.clone()), body))
            .collect();

        if let Some(small) = self.compile_small_string_switch_return(
            scrut_compiled.expr.clone(),
            &borrowed_cases,
            default,
            default.is_none(),
        ) {
            block.extend(small);
            return block;
        }

        let clauses = self.grouped_return_string_clauses(
            self.grouped_switch_cases(cases, default, |_, _| true),
            SwitchCaseTag::String,
        );

        let default_block = default
            .map(|fallback| self.compile_return_block(fallback))
            .filter(|body| !body.is_empty());

        block.push(Statement::new(StatementDesc::StringSwitch(
            scrut_compiled.expr,
            clauses,
            default_block,
        )));
        block
    }

    fn compile_switch_effect_block(&mut self, scrut: &Lambda, switch: &LambdaSwitch) -> Block {
        if let Some(plan) = super::untagged_plan(switch) {
            return self.compile_untagged_switch(
                super::lam_compile_variant::UntaggedMode::Effect,
                None,
                scrut,
                switch,
                &plan,
            );
        }
        self.with_switch_depth(|this| this.compile_switch_effect_block_inner(scrut, switch))
    }

    fn compile_switch_effect_block_inner(
        &mut self,
        scrut: &Lambda,
        switch: &LambdaSwitch,
    ) -> Block {
        if self.uses_named_variant_switch(switch) {
            let scrut_compiled = self.compile_expr(scrut);
            let (mut block, scrut_expr) = if self.named_variant_switch_needs_bound_scrutinee(switch)
            {
                self.bind_switch_scrutinee_once(scrut_compiled.prelude, scrut_compiled.expr)
            } else {
                (scrut_compiled.prelude, scrut_compiled.expr)
            };
            let dispatch = self.compile_named_variant_switch_effect_statements(scrut_expr, switch);
            // lam_compile.ml `compile_general_cases`: the dispatch is built
            // from `S.if_`s, which keep a condition only when it has side
            // effects (js_stmt_make.ml `if_`).
            block.extend(dispatch);
            return block;
        }

        let scrut_compiled = self.compile_expr(scrut);
        let mut block = scrut_compiled.prelude;

        let cases: Vec<_> = self
            .grouped_switch_cases(
                &switch.sw_consts,
                switch.sw_failaction.as_deref(),
                |_, _| true,
            )
            .into_iter()
            .map(|(tag, body, is_last)| {
                let clause = if is_last {
                    let source_loc = self.source_loc_of_lam(body);
                    // `Js_output.to_break_block` (js_output.ml:88-100).
                    let body_output = self.compile_effect_block_output(body);
                    let should_break = body_output.finished != OutputFinished::True;
                    let body = self.with_block_source_loc(body, body_output.block);
                    crate::js_ir::CaseClause {
                        source_loc,
                        should_break,
                        body,
                        comment: None,
                    }
                } else {
                    self.empty_switch_case_clause_for(body)
                };
                (direct_switch_int(tag), clause)
            })
            .collect();

        let default_block = switch
            .sw_failaction
            .as_ref()
            .map(|fallback| {
                let block = self.compile_effect_block(fallback);
                self.with_block_source_loc(fallback, block)
            })
            .filter(|body| !body.is_empty());

        let has_effectful_case = cases.iter().any(|(_, clause)| !clause.body.is_empty())
            || default_block.as_ref().is_some_and(|body| !body.is_empty());
        if !has_effectful_case {
            // OCaml collapses an all-empty switch to `S.exp scrut`
            // (js_stmt_make.ml:45-53), preserving bare pure expressions.
            push_s_exp(&mut block, scrut_compiled.expr);
            return block;
        }

        block.push(Statement::new(StatementDesc::IntSwitch(
            scrut_compiled.expr,
            cases,
            default_block,
        )));
        block
    }

    fn compile_string_switch_effect_block(
        &mut self,
        scrut: &Lambda,
        cases: &[(String, Lambda)],
        default: Option<&Lambda>,
    ) -> Block {
        self.with_switch_depth(|this| {
            this.compile_string_switch_effect_block_inner(scrut, cases, default)
        })
    }

    fn compile_string_switch_effect_block_inner(
        &mut self,
        scrut: &Lambda,
        cases: &[(String, Lambda)],
        default: Option<&Lambda>,
    ) -> Block {
        let scrut_compiled = self.compile_expr(scrut);
        let mut block = scrut_compiled.prelude;
        let borrowed_cases: Vec<_> = cases
            .iter()
            .map(|(tag, body)| (SwitchCaseTag::String(tag.clone()), body))
            .collect();

        if let Some(small) = self.compile_small_string_switch_effect(
            scrut_compiled.expr.clone(),
            &borrowed_cases,
            default,
            false,
        ) {
            // lam_compile.ml `compile_general_cases`: the small shapes are
            // `S.if_`s, which keep a condition only when it has side effects
            // (js_stmt_make.ml `if_`), or a single branch.
            block.extend(small);
            return block;
        }

        let clauses: Vec<_> = self
            .grouped_switch_cases(cases, default, |_, _| true)
            .into_iter()
            .map(|(tag, body, is_last)| {
                let clause = if is_last {
                    let source_loc = self.source_loc_of_lam(body);
                    // `Js_output.to_break_block` (js_output.ml:88-100).
                    let body_output = self.compile_effect_block_output(body);
                    let should_break = body_output.finished != OutputFinished::True;
                    let body = self.with_block_source_loc(body, body_output.block);
                    crate::js_ir::CaseClause {
                        source_loc,
                        should_break,
                        body,
                        comment: None,
                    }
                } else {
                    self.empty_switch_case_clause_for(body)
                };
                crate::js_ir::StringClause {
                    tag_type: SwitchCaseTag::String(tag),
                    clause,
                }
            })
            .collect();

        let default_block = default
            .map(|fallback| {
                let block = self.compile_effect_block(fallback);
                self.with_block_source_loc(fallback, block)
            })
            .filter(|body| !body.is_empty());

        let has_effectful_case = clauses.iter().any(|clause| !clause.clause.body.is_empty())
            || default_block.as_ref().is_some_and(|body| !body.is_empty());
        if !has_effectful_case {
            // OCaml collapses an all-empty string switch to `S.exp scrut`
            // (js_stmt_make.ml:45-53), preserving bare pure expressions.
            push_s_exp(&mut block, scrut_compiled.expr);
            return block;
        }

        block.push(Statement::new(StatementDesc::StringSwitch(
            scrut_compiled.expr,
            clauses,
            default_block,
        )));
        block
    }

    pub(crate) fn compile_external_arg_const(&self, cst: &Cst) -> Expression {
        match cst {
            Cst::ArgIntLit(i) => Expression::number(Number::Int {
                i: *i as i32,
                c: None,
            }),
            // lam_compile_const.ml `translate_arg_cst`.
            Cst::ArgStringLit(s) => Expression::string(s.clone()),
            Cst::ArgJsonLit(s) => Expression::new(ExpressionDesc::JsonLiteral(s.clone())),
        }
    }

    pub(crate) fn runtime_member_expr(&self, module_name: &str, member: &str) -> Expression {
        Expression::qualified(
            ModuleId {
                id: Ident::create_persistent(module_name),
                kind: Kind::Runtime,
                dynamic_import: false,
            },
            Some(member.to_string()),
        )
    }

    pub(crate) fn builtin_runtime_call_info() -> CallInfo {
        // OCaml `E.runtime_call` uses `Js_call_info.builtin_runtime_call`
        // (`compiler/core/js_exp_make.ml:147-149`), defined as
        // `{arity = Full; call_info = Call_builtin_runtime}`
        // (`compiler/core/js_call_info.ml:40-42`). `js_dump.ml:299-344`
        // relies on exactly that metadata when eta-reducing wrappers like
        // `fun x y -> Primitive_int.div x y` to `Primitive_int.div`.
        CallInfo {
            kind: CallKind::BuiltinRuntime,
            arity: CallArity::Full,
            ..CallInfo::default()
        }
    }

    pub(crate) fn runtime_call_expr(
        &self,
        module_name: &str,
        member: &str,
        args: Vec<Expression>,
    ) -> Expression {
        Expression::call(
            self.runtime_member_expr(module_name, member),
            args,
            Self::builtin_runtime_call_info(),
        )
    }

    pub(crate) fn int32_div_expr(&self, left: Expression, right: Expression) -> Expression {
        match (&left.desc, int_literal(&right)) {
            (ExpressionDesc::Length(_, _), Some(2)) => {
                Expression::bin(BinOp::Asr, left, int_expr(1))
            }
            (_, Some(rhs)) if rhs != 0 => match int_literal(&left) {
                Some(lhs) => int_expr(lhs.wrapping_div(rhs)),
                None => to_int32(Expression::bin(BinOp::Div, left, right)),
            },
            _ if self.check_div_by_zero => {
                self.runtime_call_expr("Primitive_int", "div", vec![left, right])
            }
            _ => to_int32(Expression::bin(BinOp::Div, left, right)),
        }
    }

    pub(crate) fn int32_mod_expr(&self, left: Expression, right: Expression) -> Expression {
        match int_literal(&right) {
            Some(rhs) if rhs != 0 => Expression::bin(BinOp::Mod, left, right),
            _ if self.check_div_by_zero => {
                self.runtime_call_expr("Primitive_int", "mod_", vec![left, right])
            }
            _ => Expression::bin(BinOp::Mod, left, right),
        }
    }

    pub(crate) fn bigint_div_expr(&self, left: Expression, right: Expression) -> Expression {
        if self.check_div_by_zero {
            self.runtime_call_expr("Primitive_bigint", "div", vec![left, right])
        } else {
            Expression::bin(BinOp::Div, left, right)
        }
    }

    pub(crate) fn bigint_mod_expr(&self, left: Expression, right: Expression) -> Expression {
        if self.check_div_by_zero {
            self.runtime_call_expr("Primitive_bigint", "mod_", vec![left, right])
        } else {
            Expression::bin(BinOp::Mod, left, right)
        }
    }

    fn with_static_handler<T>(
        &mut self,
        label: i32,
        bindings: &[Ident],
        handler: &Lambda,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        self.static_handlers.push(StaticHandler {
            label,
            bindings: bindings.to_vec(),
            handler: handler.clone(),
        });
        let result = f(self);
        self.static_handlers.pop();
        result
    }

    fn with_static_jump_handler<T>(
        &mut self,
        label: i32,
        exit_id: &Ident,
        bindings: &[Ident],
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let exit_code = self.next_static_jump_exit_code();
        self.static_jump_handlers.push(StaticJumpHandler {
            label,
            exit_id: *exit_id,
            exit_code,
            bindings: bindings.to_vec(),
        });
        let result = f(self);
        self.static_jump_handlers.pop();
        result
    }

    fn resolve_static_raise(&self, label: i32, args: &[Lambda]) -> Option<Lambda> {
        let handler = self
            .static_handlers
            .iter()
            .rev()
            .find(|handler| handler.label == label)?;
        if handler.bindings.len() != args.len() {
            return None;
        }
        if handler.bindings.is_empty() {
            return Some(handler.handler.clone());
        }

        let subst = lam_subst::make_subst(&handler.bindings, args);
        Some(lam_subst::subst(&subst, &handler.handler))
    }

    fn return_staticcatch_requires_explicit_jump(
        &self,
        label: i32,
        bindings: &[Ident],
        body: &Lambda,
        handler: &Lambda,
    ) -> bool {
        if bindings.is_empty()
            && matches!(body, Lambda::LstaticCatch(_, _, _))
            && self.handler_is_inlineable_pure_return_static_raise_dispatch(handler)
        {
            return false;
        }

        // OCaml's `compile_staticcatch` (lam_compile.ml:937-1017) uses the
        // pseudo-jmp path only when `in_staticcatch=false` (lam_compile.ml:939).
        // Any staticcatch that OCaml compiles while `in_staticcatch=true` takes
        // the full exit_id path (lam_compile.ml:963-1017). `in_staticcatch=true`
        // is set inside the body of BOTH the inline path (lam_compile.ml:952)
        // and the explicit-jump path (lam_compile.ml:1002), so Rust must force
        // explicit-jump for any staticcatch encountered while another inline-
        // path or explicit-jump-path staticcatch's body is being compiled. The
        // handler-inline at a `LstaticRaise` site (compile.rs:2122) pops the
        // matching entry from `static_handlers` first, so the handler body sees
        // the depth as it was at the outer Lstaticcatch's entry — matching
        // OCaml's `compile_lambda lambda_cxt handler` (lam_compile.ml:962),
        // which uses the original `lambda_cxt` for the handler.
        if !self.static_handlers.is_empty()
            || !self.static_jump_handlers.is_empty()
            || !self.fallthrough_return_handlers.is_empty()
        {
            return true;
        }

        self.return_handler_requires_explicit_staticcatch_jump(handler)
            || (lambda_has_multiple_static_raises_to_label(body, label, bindings.len())
                && lambda_contains_static_raise_to_other_label(handler, label)
                && !self.handler_is_pure_outward_static_raise_forwarder(handler))
    }

    fn handler_is_pure_outward_static_raise_forwarder(&self, lam: &Lambda) -> bool {
        match lam {
            Lambda::LstaticRaise(label, args) => {
                self.active_static_raise_target_exists(*label, args.len())
                    && args.iter().all(lam_analysis::no_side_effects)
            }
            Lambda::Llet(kind, _, value, body)
                if matches!(kind, LetKind::Alias | LetKind::Strict | LetKind::StrictOpt)
                    && lam_analysis::no_side_effects(value)
                    && !self.lambda_requires_explicit_staticcatch_jump(value) =>
            {
                self.handler_is_pure_outward_static_raise_forwarder(body)
            }
            Lambda::Lsequence(first, second)
                if lam_analysis::no_side_effects(first)
                    && !self.lambda_requires_explicit_staticcatch_jump(first) =>
            {
                self.handler_is_pure_outward_static_raise_forwarder(second)
            }
            _ => false,
        }
    }

    fn active_static_raise_target_exists(&self, label: i32, arity: usize) -> bool {
        self.static_jump_handlers
            .iter()
            .rev()
            .any(|handler| handler.label == label && handler.bindings.len() == arity)
            || self
                .fallthrough_return_handlers
                .iter()
                .rev()
                .any(|handler| handler.label == label && handler.bindings.len() == arity)
            || self
                .static_handlers
                .iter()
                .rev()
                .any(|handler| handler.label == label && handler.bindings.len() == arity)
    }

    fn return_handler_requires_explicit_staticcatch_jump(&self, lam: &Lambda) -> bool {
        match lam {
            Lambda::Lvar(_) | Lambda::LglobalModule(_) | Lambda::Lconst(_) => false,
            Lambda::LifThenElse(_, _, _)
            | Lambda::Lswitch(_, _)
            | Lambda::LstringSwitch(_, _, _)
            | Lambda::Llet(_, _, _, _)
            | Lambda::Lsequence(_, _)
                if handler_has_static_raise_like_ocaml(lam)
                    && !self.handler_is_pure_outward_static_raise_forwarder(lam) =>
            {
                true
            }
            Lambda::Lapply(apply) => {
                self.return_handler_requires_explicit_staticcatch_jump(&apply.ap_func)
                    || apply
                        .ap_args
                        .iter()
                        .any(|arg| self.return_handler_requires_explicit_staticcatch_jump(arg))
            }
            Lambda::Lfunction(_) => false,
            Lambda::Llet(_, _, value, body) => {
                self.return_handler_requires_explicit_staticcatch_jump(value)
                    || self.return_handler_requires_explicit_staticcatch_jump(body)
            }
            Lambda::Lletrec(bindings, body) => {
                bindings
                    .iter()
                    .any(|(_, value)| self.return_handler_requires_explicit_staticcatch_jump(value))
                    || self.return_handler_requires_explicit_staticcatch_jump(body)
            }
            Lambda::Lprim(info) => info
                .args
                .iter()
                .any(|arg| self.return_handler_requires_explicit_staticcatch_jump(arg)),
            Lambda::Lswitch(scrut, switch) => {
                self.return_handler_requires_explicit_staticcatch_jump(scrut)
                    || switch.sw_consts.iter().any(|(_, body)| {
                        self.return_handler_requires_explicit_staticcatch_jump(body)
                    })
                    || switch.sw_blocks.iter().any(|(_, body)| {
                        self.return_handler_requires_explicit_staticcatch_jump(body)
                    })
                    || switch.sw_failaction.as_deref().is_some_and(|body| {
                        self.return_handler_requires_explicit_staticcatch_jump(body)
                    })
            }
            Lambda::LstringSwitch(scrut, cases, default) => {
                self.return_handler_requires_explicit_staticcatch_jump(scrut)
                    || cases.iter().any(|(_, body)| {
                        self.return_handler_requires_explicit_staticcatch_jump(body)
                    })
                    || default.as_deref().is_some_and(|body| {
                        self.return_handler_requires_explicit_staticcatch_jump(body)
                    })
            }
            Lambda::LstaticRaise(label, args) => {
                !self.active_static_raise_target_exists(*label, args.len())
                    || args
                        .iter()
                        .any(|arg| self.return_handler_requires_explicit_staticcatch_jump(arg))
            }
            Lambda::LstaticCatch(body, (label, bindings), handler) => {
                ((self.return_unit_stack.last().copied() == Some(true)) && !bindings.is_empty())
                    || self
                        .return_staticcatch_requires_explicit_jump(*label, bindings, body, handler)
            }
            Lambda::LtryWith(body, _, handler) | Lambda::LtryFinally(body, handler) => {
                self.return_handler_requires_explicit_staticcatch_jump(body)
                    || self.return_handler_requires_explicit_staticcatch_jump(handler)
            }
            Lambda::Lsequence(first, second) => {
                self.return_handler_requires_explicit_staticcatch_jump(first)
                    || self.return_handler_requires_explicit_staticcatch_jump(second)
            }
            Lambda::Lwhile(cond, body) => {
                self.return_handler_requires_explicit_staticcatch_jump(cond)
                    || self.return_handler_requires_explicit_staticcatch_jump(body)
            }
            Lambda::Lfor(_, start, finish, _, body) => {
                self.return_handler_requires_explicit_staticcatch_jump(start)
                    || self.return_handler_requires_explicit_staticcatch_jump(finish)
                    || self.return_handler_requires_explicit_staticcatch_jump(body)
            }
            Lambda::Lfor_of(_, iterable, body) | Lambda::Lfor_await_of(_, iterable, body) => {
                self.return_handler_requires_explicit_staticcatch_jump(iterable)
                    || self.return_handler_requires_explicit_staticcatch_jump(body)
            }
            Lambda::Lbreak | Lambda::Lcontinue => false,
            Lambda::Lassign(_, value) => {
                self.return_handler_requires_explicit_staticcatch_jump(value)
            }
            Lambda::LifThenElse(cond, then_, else_) => {
                self.return_handler_requires_explicit_staticcatch_jump(cond)
                    || self.return_handler_requires_explicit_staticcatch_jump(then_)
                    || self.return_handler_requires_explicit_staticcatch_jump(else_)
            }
        }
    }

    fn handler_is_inlineable_pure_return_static_raise_dispatch(&self, lam: &Lambda) -> bool {
        self.handler_is_pure_outward_static_raise_forwarder(lam)
            || self
                .pure_return_static_raise_dispatch_has_terminal_value(lam)
                .unwrap_or(false)
    }

    fn pure_return_static_raise_dispatch_has_terminal_value(&self, lam: &Lambda) -> Option<bool> {
        match lam {
            Lambda::LstaticRaise(label, args) => {
                let args_are_pure = args.iter().all(lam_analysis::no_side_effects);
                if self.active_static_raise_target_exists(*label, args.len()) && args_are_pure {
                    Some(false)
                } else {
                    None
                }
            }
            Lambda::Llet(kind, _, value, body)
                if matches!(kind, LetKind::Alias | LetKind::Strict | LetKind::StrictOpt)
                    && lam_analysis::no_side_effects(value) =>
            {
                self.pure_return_static_raise_dispatch_has_terminal_value(body)
            }
            Lambda::Lsequence(first, second) if lam_analysis::no_side_effects(first) => {
                self.pure_return_static_raise_dispatch_has_terminal_value(second)
            }
            Lambda::LifThenElse(cond, then_, else_) if lam_analysis::no_side_effects(cond) => {
                let then_has_value =
                    self.pure_return_static_raise_dispatch_has_terminal_value(then_)?;
                let else_has_value =
                    self.pure_return_static_raise_dispatch_has_terminal_value(else_)?;
                Some(then_has_value || else_has_value)
            }
            Lambda::Lswitch(scrut, switch) if lam_analysis::no_side_effects(scrut) => {
                let mut has_terminal_value = false;
                for (_, body) in &switch.sw_consts {
                    has_terminal_value |=
                        self.pure_return_static_raise_dispatch_has_terminal_value(body)?;
                }
                for (_, body) in &switch.sw_blocks {
                    has_terminal_value |=
                        self.pure_return_static_raise_dispatch_has_terminal_value(body)?;
                }
                if let Some(body) = switch.sw_failaction.as_deref() {
                    has_terminal_value |=
                        self.pure_return_static_raise_dispatch_has_terminal_value(body)?;
                }
                Some(has_terminal_value)
            }
            Lambda::LstringSwitch(scrut, cases, default)
                if lam_analysis::no_side_effects(scrut) =>
            {
                let mut has_terminal_value = false;
                for (_, body) in cases {
                    has_terminal_value |=
                        self.pure_return_static_raise_dispatch_has_terminal_value(body)?;
                }
                if let Some(body) = default.as_deref() {
                    has_terminal_value |=
                        self.pure_return_static_raise_dispatch_has_terminal_value(body)?;
                }
                Some(has_terminal_value)
            }
            _ if lam_analysis::no_side_effects(lam) => Some(true),
            _ => None,
        }
    }

    fn lambda_requires_explicit_staticcatch_jump(&self, lam: &Lambda) -> bool {
        match lam {
            Lambda::Lvar(_) | Lambda::LglobalModule(_) | Lambda::Lconst(_) => false,
            Lambda::Lapply(apply) => {
                self.lambda_requires_explicit_staticcatch_jump(&apply.ap_func)
                    || apply
                        .ap_args
                        .iter()
                        .any(|arg| self.lambda_requires_explicit_staticcatch_jump(arg))
            }
            Lambda::Lfunction(func) => self.lambda_requires_explicit_staticcatch_jump(&func.body),
            Lambda::Llet(_, _, value, body) => {
                self.lambda_requires_explicit_staticcatch_jump(value)
                    || self.lambda_requires_explicit_staticcatch_jump(body)
            }
            Lambda::Lletrec(bindings, body) => {
                bindings
                    .iter()
                    .any(|(_, value)| self.lambda_requires_explicit_staticcatch_jump(value))
                    || self.lambda_requires_explicit_staticcatch_jump(body)
            }
            Lambda::Lprim(info) => info
                .args
                .iter()
                .any(|arg| self.lambda_requires_explicit_staticcatch_jump(arg)),
            Lambda::Lswitch(scrut, switch) => {
                self.lambda_requires_explicit_staticcatch_jump(scrut)
                    || switch
                        .sw_consts
                        .iter()
                        .any(|(_, body)| self.lambda_requires_explicit_staticcatch_jump(body))
                    || switch
                        .sw_blocks
                        .iter()
                        .any(|(_, body)| self.lambda_requires_explicit_staticcatch_jump(body))
                    || switch
                        .sw_failaction
                        .as_deref()
                        .is_some_and(|body| self.lambda_requires_explicit_staticcatch_jump(body))
            }
            Lambda::LstringSwitch(scrut, cases, default) => {
                self.lambda_requires_explicit_staticcatch_jump(scrut)
                    || cases
                        .iter()
                        .any(|(_, body)| self.lambda_requires_explicit_staticcatch_jump(body))
                    || default
                        .as_deref()
                        .is_some_and(|body| self.lambda_requires_explicit_staticcatch_jump(body))
            }
            Lambda::LstaticRaise(label, args) => {
                !self.active_static_raise_target_exists(*label, args.len())
                    || args
                        .iter()
                        .any(|arg| self.lambda_requires_explicit_staticcatch_jump(arg))
            }
            Lambda::LstaticCatch(_, (_, _), _) => true,
            Lambda::LtryWith(body, _, handler) | Lambda::LtryFinally(body, handler) => {
                self.lambda_requires_explicit_staticcatch_jump(body)
                    || self.lambda_requires_explicit_staticcatch_jump(handler)
            }
            Lambda::Lsequence(first, second) => {
                self.lambda_requires_explicit_staticcatch_jump(first)
                    || self.lambda_requires_explicit_staticcatch_jump(second)
            }
            Lambda::Lwhile(cond, body) => {
                self.lambda_requires_explicit_staticcatch_jump(cond)
                    || self.lambda_requires_explicit_staticcatch_jump(body)
            }
            Lambda::Lfor(_, start, finish, _, body) => {
                self.lambda_requires_explicit_staticcatch_jump(start)
                    || self.lambda_requires_explicit_staticcatch_jump(finish)
                    || self.lambda_requires_explicit_staticcatch_jump(body)
            }
            Lambda::Lfor_of(_, iterable, body) | Lambda::Lfor_await_of(_, iterable, body) => {
                self.lambda_requires_explicit_staticcatch_jump(iterable)
                    || self.lambda_requires_explicit_staticcatch_jump(body)
            }
            Lambda::Lbreak | Lambda::Lcontinue => false,
            Lambda::Lassign(_, value) => self.lambda_requires_explicit_staticcatch_jump(value),
            Lambda::LifThenElse(cond, then_, else_) => {
                self.lambda_requires_explicit_staticcatch_jump(cond)
                    || self.lambda_requires_explicit_staticcatch_jump(then_)
                    || self.lambda_requires_explicit_staticcatch_jump(else_)
            }
        }
    }

    fn next_static_jump_exit_code(&self) -> i32 {
        // OCaml's `add_jmps` (lam_compile_context.ml:89-98) seeds the order_id
        // with `HandlerMap.cardinal m + 1` — i.e. the size of the existing
        // jmp_table plus one. The OCaml jmp_table accumulates entries from
        // BOTH the inline path's `add_pseudo_jmp` (lam_compile.ml:944-946)
        // and the explicit-jump path's `add_jmps` (lam_compile.ml:965-966),
        // so a nested explicit-jump staticcatch sees the outer pseudo-jmp
        // entries in its seed count. Rust's three handler stacks are the
        // moral equivalents: `static_handlers` (pure inline), `static_jump_handlers`
        // (explicit-jump), and `fallthrough_return_handlers` (inline with
        // fallthrough rewriting). Counting all three keeps the exit-code
        // numbering byte-identical with OCaml when staticcatches are nested.
        let depth = self.static_handlers.len()
            + self.static_jump_handlers.len()
            + self.fallthrough_return_handlers.len();
        i32::try_from(depth + 1).expect("static jump handler depth fits in i32")
    }

    fn compile_static_raise_jump_output(
        &mut self,
        label: i32,
        args: &[Lambda],
    ) -> Option<BlockOutput> {
        let handler = self
            .static_jump_handlers
            .iter()
            .rev()
            .find(|handler| handler.label == label)?
            .clone();
        if handler.bindings.len() != args.len() {
            return None;
        }

        // lam_compile.ml `compile_staticraise`: `Ext_list.fold_right2 largs
        // bindings exit_assignment (fun larg bind acc -> append_output
        // (compile larg) acc)`. The nested fold is an argument of `f`, so
        // the last argument is compiled first; an argument whose output is
        // finished (a `throw`) drops everything after it, the exit code
        // assignment included (`Js_output.append_output`).
        let exit_assignment = BlockOutput::make(vec![Statement::exp(Expression::bin(
            BinOp::Eq,
            Expression::var(handler.exit_id),
            Expression::number(Number::int(handler.exit_code)),
        ))]);
        let output =
            handler
                .bindings
                .iter()
                .zip(args)
                .rev()
                .fold(exit_assignment, |acc, (binding, arg)| {
                    let output = self.compile_assign_to_target_output(binding, arg);
                    output.append(acc)
                });
        Some(output)
    }

    fn staticcatch_declarations(&self, exit_id: &Ident, bindings: &[Ident]) -> Block {
        let mut declarations = vec![Statement::variable(VariableDeclaration {
            ident: *exit_id,
            value: Some(Expression::number(Number::int(0))),
            property: LetKind::Variable,
            ident_info: IdentInfo::default(),
        })];
        declarations.extend(bindings.iter().map(|binding| {
            Statement::variable(VariableDeclaration {
                ident: *binding,
                value: None,
                property: LetKind::Variable,
                ident_info: IdentInfo::default(),
            })
        }));
        declarations
    }

    fn staticcatch_exit_test(&self, exit_id: &Ident, exit_code: i32) -> Expression {
        Expression::bin(
            BinOp::EqEqEq,
            Expression::var(*exit_id),
            Expression::number(Number::int(exit_code)),
        )
    }

    fn compile_staticcatch_assignment_block(
        &mut self,
        result: &Ident,
        label: i32,
        bindings: &[Ident],
        body: &Lambda,
        handler: &Lambda,
    ) -> Block {
        self.compile_staticcatch_assignment_output(result, label, bindings, body, handler)
            .block
    }

    /// lam_compile.ml:1063-1101 `compile_staticcatch`, explicit jumps: the
    /// body and then the handler are compiled, and the output is
    /// `append_output (make declares) (append_output lbody (make cases))`,
    /// so a finished body drops the handler and finishes the catch.
    fn compile_staticcatch_assignment_output(
        &mut self,
        result: &Ident,
        label: i32,
        bindings: &[Ident],
        body: &Lambda,
        handler: &Lambda,
    ) -> BlockOutput {
        let exit_id = self.fresh_ident("exit");
        let exit_code = self.next_static_jump_exit_code();
        let declarations = self.staticcatch_declarations(&exit_id, bindings);
        let (body_output, handler_block) =
            self.with_static_jump_handler(label, &exit_id, bindings, |this| {
                let body_output = this.compile_assign_to_target_output(result, body);
                let handler_block = this.compile_assign_to_target_block(result, handler);
                (body_output, handler_block)
            });
        let cases = if handler_block.is_empty() {
            BlockOutput::make(vec![])
        } else {
            BlockOutput::make(vec![Statement::if_(
                self.staticcatch_exit_test(&exit_id, exit_code),
                handler_block,
                vec![],
            )])
        };
        BlockOutput::make(declarations).append(body_output.append(cases))
    }

    /// lam_compile.ml:1063-1101 `compile_staticcatch`, explicit jumps: the
    /// body and then the handler are compiled, and the output is
    /// `append_output (make declares) (append_output lbody (make cases))`,
    /// so a finished body drops the handler and finishes the catch.
    fn compile_staticcatch_effect_output(
        &mut self,
        label: i32,
        bindings: &[Ident],
        body: &Lambda,
        handler: &Lambda,
    ) -> BlockOutput {
        let exit_id = self.fresh_ident("exit");
        let exit_code = self.next_static_jump_exit_code();
        let declarations = self.staticcatch_declarations(&exit_id, bindings);
        let (body_output, handler_block) =
            self.with_static_jump_handler(label, &exit_id, bindings, |this| {
                let body_output = this.compile_effect_block_output(body);
                let handler_block = this.compile_effect_block(handler);
                (body_output, handler_block)
            });
        let cases = if handler_block.is_empty() {
            BlockOutput::make(vec![])
        } else {
            BlockOutput::make(vec![Statement::if_(
                self.staticcatch_exit_test(&exit_id, exit_code),
                handler_block,
                vec![],
            )])
        };
        BlockOutput::make(declarations).append(body_output.append(cases))
    }

    /// [`Self::compile_staticcatch_effect_output`] in a return continuation
    /// (lam_compile.ml:1063-1101).
    fn compile_staticcatch_return_output(
        &mut self,
        label: i32,
        bindings: &[Ident],
        body: &Lambda,
        handler: &Lambda,
    ) -> BlockOutput {
        let exit_id = self.fresh_ident("exit");
        let exit_code = self.next_static_jump_exit_code();
        let declarations = self.staticcatch_declarations(&exit_id, bindings);
        let (body_output, handler_block) =
            self.with_static_jump_handler(label, &exit_id, bindings, |this| {
                let body_output = this.compile_return_output(body);
                let handler_block = this.compile_return_output(handler).block;
                (body_output, handler_block)
            });
        let cases = if handler_block.is_empty() {
            BlockOutput::make(vec![])
        } else {
            BlockOutput::make(vec![Statement::if_(
                self.staticcatch_exit_test(&exit_id, exit_code),
                handler_block,
                vec![],
            )])
        };
        BlockOutput::make(declarations).append(body_output.append(cases))
    }

    /// [`Self::compile_staticcatch_effect_output`] in a return continuation
    /// (lam_compile.ml:1063-1101).
    fn compile_staticcatch_tail_loop_return_output(
        &mut self,
        label: i32,
        bindings: &[Ident],
        body: &Lambda,
        handler: &Lambda,
        tail_loop: &mut TailLoopState,
    ) -> BlockOutput {
        let exit_id = self.fresh_ident("exit");
        let exit_code = self.next_static_jump_exit_code();
        let declarations = self.staticcatch_declarations(&exit_id, bindings);
        let (body_output, handler_block) =
            self.with_static_jump_handler(label, &exit_id, bindings, |this| {
                let body_output = this.compile_tail_loop_return_output(body, tail_loop);
                let handler_block = this
                    .compile_tail_loop_return_output(handler, tail_loop)
                    .block;
                (body_output, handler_block)
            });
        let cases = if handler_block.is_empty() {
            BlockOutput::make(vec![])
        } else {
            BlockOutput::make(vec![Statement::if_(
                self.staticcatch_exit_test(&exit_id, exit_code),
                handler_block,
                vec![],
            )])
        };
        BlockOutput::make(declarations).append(body_output.append(cases))
    }

    fn compile_staticcatch_expr(
        &mut self,
        label: i32,
        bindings: &[Ident],
        body: &Lambda,
        handler: &Lambda,
    ) -> Compiled {
        // OCaml NeedValue staticcatch allocates `Ext_ident.create_tmp ()`
        // for the result (compiler/core/lam_compile.ml:1027-1034).
        let result = self.fresh_tmp_ident();
        let mut prelude = vec![Statement::variable(VariableDeclaration {
            ident: result,
            value: None,
            property: LetKind::Strict,
            ident_info: IdentInfo::default(),
        })];
        prelude.extend(
            self.compile_staticcatch_assignment_block(&result, label, bindings, body, handler),
        );
        Compiled {
            prelude,
            expr: Expression::var(result),
            finished: OutputFinished::False,
        }
    }

    /// Direct port of the multi-handler arm of OCaml's
    /// `compile_staticcatch` (lam_compile.ml:963-1017), specialized to the
    /// four continuation flavors below.
    ///
    /// Pre-allocates ONE `exit_id` shared across all handlers, assigns
    /// sequential `order_id`s (== Rust `exit_code`s) starting at
    /// `next_static_jump_exit_code()` (the OCaml `HandlerMap.cardinal + 1`,
    /// lam_compile_context.ml:93), and emits all handlers' bindings together
    /// at the top (lam_compile.ml:973-975). The body compiles with every
    /// handler active, so any `LstaticRaise` to any of the flattened labels
    /// assigns the corresponding exit code. After the body, a dispatch is
    /// emitted via `compile_exit_dispatch` — the OCaml `compile_cases` call
    /// with NonComplete default at lam_compile.ml:987/996/1010/1017.
    fn emit_multi_staticcatch_prelude(&mut self, handlers: &[FlatHandler]) -> (Ident, i32, Block) {
        let exit_id = self.fresh_ident("exit");
        let first_code = self.next_static_jump_exit_code();
        let mut block = vec![Statement::variable(VariableDeclaration {
            ident: exit_id,
            value: Some(Expression::number(Number::int(0))),
            property: LetKind::Variable,
            ident_info: IdentInfo::default(),
        })];
        // lam_compile.ml:973-975: `Ext_list.flat_map code_table (fun
        // {bindings} -> map bindings (fun x -> S.declare_variable))`.
        // Iterate handlers in flat-catches order (innermost first) so the
        // declarations come out in the same order OCaml emits them.
        for handler in handlers {
            for binding in &handler.bindings {
                block.push(Statement::variable(VariableDeclaration {
                    ident: *binding,
                    value: None,
                    property: LetKind::Variable,
                    ident_info: IdentInfo::default(),
                }));
            }
        }
        for (i, handler) in handlers.iter().enumerate() {
            let exit_code = first_code + i32::try_from(i).expect("exit handler index fits in i32");
            self.static_jump_handlers.push(StaticJumpHandler {
                label: handler.label,
                exit_id,
                exit_code,
                bindings: handler.bindings.clone(),
            });
        }
        (exit_id, first_code, block)
    }

    fn pop_multi_staticcatch_handlers(&mut self, count: usize) {
        for _ in 0..count {
            self.static_jump_handlers.pop();
        }
    }

    /// OCaml `compile_general_cases` groups equal Lambda bodies before
    /// compiling the final arm of each group (lam_compile.ml:668-707).
    /// Group the original handler lambdas, not their lowered JS statements:
    /// distinct compilation of identical handlers can allocate different
    /// temporaries and prevents their cases from sharing one body.
    fn compile_grouped_staticcatch_handlers<'a>(
        &mut self,
        handlers: &'a [FlatHandler],
        first_code: i32,
        mut compile: impl FnMut(&mut Self, &Lambda) -> BlockOutput,
    ) -> Vec<(i32, BlockOutput, bool, &'a Lambda)> {
        let cases = handlers
            .iter()
            .enumerate()
            .map(|(i, handler)| {
                (
                    first_code + i32::try_from(i).expect("exit handler index fits in i32"),
                    &handler.handler,
                )
            })
            .collect();
        stable_group_switch_cases(cases, |_, _| true)
            .into_iter()
            .map(|(code, handler, is_last)| {
                let output = if is_last {
                    compile(self, handler)
                } else {
                    BlockOutput::make(Vec::new())
                };
                (code, output, is_last, handler)
            })
            .collect()
    }

    /// Emit the `compile_cases ~cxt ~switch_exp:exit_expr handlers` call at
    /// lam_compile.ml:987/996/1010/1017. For a single handler + NonComplete
    /// default this reduces to `if (exit === code) { handler_block }`
    /// (compile_general_cases lam_compile.ml:551-557). For multiple handlers
    /// it becomes an `int_switch` (lam_compile.ml:567-630).
    fn compile_exit_dispatch(
        &self,
        exit_id: &Ident,
        handlers: Vec<(i32, BlockOutput, bool, &Lambda)>,
        is_return_context: bool,
    ) -> Option<Statement> {
        if handlers.is_empty() {
            return None;
        }
        if handlers.len() == 1 {
            let (code, handler_output, _, _) = handlers.into_iter().next().unwrap();
            let handler_block = handler_output.block;
            if handler_block.is_empty() {
                return None;
            }
            return Some(Statement::if_(
                self.staticcatch_exit_test(exit_id, code),
                handler_block,
                vec![],
            ));
        }
        // OCaml compile_general_cases (lam_compile.ml:668-707) emits empty
        // clauses for all but the last case of an equal-Lambda group.
        let clauses: Vec<(i32, CaseClause)> = handlers
            .into_iter()
            .map(|(code, output, is_last, handler_lam)| {
                // `Js_output.to_break_block` (js_output.ml:88-100).
                let should_break = is_last
                    && output.finished != OutputFinished::True
                    && (!is_return_context || has_exit_code(handler_lam, |_| true));
                (
                    code,
                    CaseClause {
                        source_loc: None,
                        body: output.block,
                        should_break,
                        comment: None,
                    },
                )
            })
            .collect();
        Some(Statement::new(StatementDesc::IntSwitch(
            Expression::var(*exit_id),
            clauses,
            None,
        )))
    }

    /// [`Self::compile_multi_staticcatch_effect_output`] in a return
    /// continuation.
    fn compile_multi_staticcatch_return_output(
        &mut self,
        handlers: &[FlatHandler],
        body: &Lambda,
    ) -> BlockOutput {
        let (exit_id, first_code, declarations) = self.emit_multi_staticcatch_prelude(handlers);
        let body_output = self.compile_return_output(body);
        let grouped_handlers =
            self.compile_grouped_staticcatch_handlers(handlers, first_code, |this, handler| {
                this.compile_return_output(handler)
            });
        self.pop_multi_staticcatch_handlers(handlers.len());
        let cases = BlockOutput::make(
            self.compile_exit_dispatch(&exit_id, grouped_handlers, true)
                .into_iter()
                .collect(),
        );
        BlockOutput::make(declarations).append(body_output.append(cases))
    }

    /// [`Self::compile_staticcatch_effect_output`] for a flattened code
    /// table: every handler is compiled after the body.
    fn compile_multi_staticcatch_effect_output(
        &mut self,
        handlers: &[FlatHandler],
        body: &Lambda,
    ) -> BlockOutput {
        let (exit_id, first_code, declarations) = self.emit_multi_staticcatch_prelude(handlers);
        let body_output = self.compile_effect_block_output(body);
        let grouped_handlers =
            self.compile_grouped_staticcatch_handlers(handlers, first_code, |this, handler| {
                this.compile_effect_block_output(handler)
            });
        self.pop_multi_staticcatch_handlers(handlers.len());
        let cases = BlockOutput::make(
            self.compile_exit_dispatch(&exit_id, grouped_handlers, false)
                .into_iter()
                .collect(),
        );
        BlockOutput::make(declarations).append(body_output.append(cases))
    }

    fn compile_multi_staticcatch_assignment_block(
        &mut self,
        result: &Ident,
        handlers: &[FlatHandler],
        body: &Lambda,
    ) -> Block {
        self.compile_multi_staticcatch_assignment_output(result, handlers, body)
            .block
    }

    /// [`Self::compile_staticcatch_effect_output`] for a flattened code
    /// table: every handler is compiled after the body.
    fn compile_multi_staticcatch_assignment_output(
        &mut self,
        result: &Ident,
        handlers: &[FlatHandler],
        body: &Lambda,
    ) -> BlockOutput {
        let (exit_id, first_code, declarations) = self.emit_multi_staticcatch_prelude(handlers);
        let body_output = self.compile_assign_to_target_output(result, body);
        let grouped_handlers =
            self.compile_grouped_staticcatch_handlers(handlers, first_code, |this, handler| {
                this.compile_assign_to_target_output(result, handler)
            });
        self.pop_multi_staticcatch_handlers(handlers.len());
        let cases = BlockOutput::make(
            self.compile_exit_dispatch(&exit_id, grouped_handlers, false)
                .into_iter()
                .collect(),
        );
        BlockOutput::make(declarations).append(body_output.append(cases))
    }

    /// [`Self::compile_multi_staticcatch_effect_output`] in a return
    /// continuation.
    fn compile_multi_staticcatch_tail_loop_return_output(
        &mut self,
        handlers: &[FlatHandler],
        body: &Lambda,
        tail_loop: &mut TailLoopState,
    ) -> BlockOutput {
        let (exit_id, first_code, declarations) = self.emit_multi_staticcatch_prelude(handlers);
        let body_output = self.compile_tail_loop_return_output(body, tail_loop);
        let grouped_handlers =
            self.compile_grouped_staticcatch_handlers(handlers, first_code, |this, handler| {
                this.compile_tail_loop_return_output(handler, tail_loop)
            });
        self.pop_multi_staticcatch_handlers(handlers.len());
        let cases = BlockOutput::make(
            self.compile_exit_dispatch(&exit_id, grouped_handlers, true)
                .into_iter()
                .collect(),
        );
        BlockOutput::make(declarations).append(body_output.append(cases))
    }

    fn collect_required_module_set(&self, block: &Block) -> OcamlModuleSet {
        let mut modules = OcamlModuleSet::new();
        collect_modules_from_block(block, &mut modules);
        modules
    }

    fn collect_required_modules(&self, block: &Block) -> Vec<ModuleId> {
        let mut modules = self.collect_required_module_set(block).to_vec();
        ocaml_sort_modules(&mut modules);
        modules
    }
}

fn normalize_if_assignment_merge_order(
    cond: Expression,
    then_block: Block,
    else_block: Block,
) -> (Expression, Block, Block) {
    // OCaml's `Js_stmt_make.if_` handles `Js_not` before it folds
    // same-target branch assignments (compiler/core/js_stmt_make.ml:235-286).
    // Keep that rule order for Rust's eager assignment merge, otherwise a
    // `!(x == null) ? value : undefined` conditional survives where OCaml
    // first swaps branches and emits `x == null ? undefined : value`.
    match cond.desc {
        ExpressionDesc::JsNot(inner) if !else_block.is_empty() => (*inner, else_block, then_block),
        other => (
            Expression {
                source_loc: None,
                desc: other,
                comment: cond.comment,
            },
            then_block,
            else_block,
        ),
    }
}

/// `Declare (kind, id)` of a value compiled as `NeedValue`: a finished output
/// (lam_compile.ml:1682, 1934, 1949) is kept as it is, without the
/// declaration, as `Praise` ignores its continuation.
fn declare_compiled(kind: LetKind, id: &Ident, compiled: Compiled) -> BlockOutput {
    let mut block = compiled.prelude;
    if compiled.finished == OutputFinished::True {
        return BlockOutput {
            block,
            finished: OutputFinished::True,
        };
    }
    block.push(Statement::variable(VariableDeclaration {
        ident: *id,
        value: Some(compiled.expr),
        property: kind,
        ident_info: IdentInfo::default(),
    }));
    BlockOutput::make(block)
}

/// `output_of_block_and_expression (EffectCall (Maybe_tail_is_return _))`
/// (js_output.ml:57-59) of a value compiled as `NeedValue`: a `return`,
/// which finishes the output. A finished value (a raise) stays as it is.
fn return_compiled(compiled: Compiled) -> BlockOutput {
    let mut block = compiled.prelude;
    if compiled.finished != OutputFinished::True {
        block.push(Statement::return_(compiled.expr));
    }
    BlockOutput::finished(block)
}

/// `Assign result` of a value compiled as `NeedValue`; a finished output
/// stays as it is (see [`declare_compiled`]).
fn assign_compiled(result: &Ident, compiled: Compiled) -> BlockOutput {
    let mut block = compiled.prelude;
    if compiled.finished == OutputFinished::True {
        return BlockOutput {
            block,
            finished: OutputFinished::True,
        };
    }
    block.push(Statement::exp(Expression::bin(
        BinOp::Eq,
        Expression::var(*result),
        compiled.expr,
    )));
    BlockOutput::make(block)
}

/// Per-module `.cmj` export table lookup through a memo table that also
/// caches misses, so each module is read from the resolver at most once.
pub(crate) fn cached_cmj_table<'a, T>(
    cache: &'a mut AHashMap<String, Option<Arc<T>>>,
    module_name: &str,
    load: impl FnOnce() -> Option<Arc<T>>,
) -> Option<&'a T> {
    if !cache.contains_key(module_name) {
        let table = load();
        cache.insert(module_name.to_string(), table);
    }
    cache.get(module_name)?.as_deref()
}

fn recursive_function_binding_value(expr: &Lambda) -> Option<LFunction> {
    match expr {
        Lambda::Lfunction(func) => Some(*func.clone()),
        _ => None,
    }
}

fn recursive_binding_dependencies(bindings: &[(Ident, Lambda)]) -> Vec<Vec<usize>> {
    let index_by_id = bindings
        .iter()
        .enumerate()
        .map(|(index, (id, _))| (*id, index))
        .collect::<AHashMap<_, _>>();

    // OCaml's `Lam_scc.preprocess_deps` builds `node_vec` with
    // `Array.make ... (Vec_int.empty ())`, so every slot aliases the same
    // mutable vector (`compiler/core/lam_scc.ml:73-89`). Each binding's hits
    // are therefore appended into one shared adjacency list before
    // `Ext_scc.graph` consumes it (`compiler/ext/ext_scc.ml:39-96`).
    let mut shared_dependencies = Vec::new();
    for (_, expr) in bindings {
        let mut dependencies = free_variables(expr)
            .into_iter()
            .filter_map(|id| index_by_id.get(&id).copied())
            .collect::<Vec<_>>();
        dependencies.sort_unstable();
        dependencies.dedup();
        shared_dependencies.extend(dependencies);
    }

    vec![shared_dependencies; bindings.len()]
}

fn strongly_connected_binding_components(deps: &[Vec<usize>]) -> Vec<Vec<usize>> {
    struct TarjanState {
        index: usize,
        stack: Vec<usize>,
        on_stack: Vec<bool>,
        indices: Vec<Option<usize>>,
        lowlink: Vec<usize>,
        components: Vec<Vec<usize>>,
    }

    fn strong_connect(node: usize, deps: &[Vec<usize>], state: &mut TarjanState) {
        state.indices[node] = Some(state.index);
        state.lowlink[node] = state.index;
        state.index += 1;
        state.stack.push(node);
        state.on_stack[node] = true;

        for &dep in &deps[node] {
            if state.indices[dep].is_none() {
                strong_connect(dep, deps, state);
                state.lowlink[node] = state.lowlink[node].min(state.lowlink[dep]);
            } else if state.on_stack[dep] {
                state.lowlink[node] =
                    state.lowlink[node].min(state.indices[dep].expect("visited node"));
            }
        }

        if state.lowlink[node] == state.indices[node].expect("visited node") {
            let mut component = Vec::new();
            loop {
                let current = state.stack.pop().expect("tarjan stack");
                state.on_stack[current] = false;
                component.push(current);
                if current == node {
                    break;
                }
            }
            // OCaml's `Ext_scc.graph` slices the stack from the SCC root to
            // the top (`compiler/ext/ext_scc.ml:80-92`), preserving stack
            // order inside the component. Rust pops from the top, so reverse
            // the popped list before later recursive-let compilation.
            component.reverse();
            state.components.push(component);
        }
    }

    let len = deps.len();
    let mut state = TarjanState {
        index: 1,
        stack: Vec::new(),
        on_stack: vec![false; len],
        indices: vec![None; len],
        lowlink: vec![0; len],
        components: Vec::new(),
    };

    for node in 0..len {
        if state.indices[node].is_none() {
            strong_connect(node, deps, &mut state);
        }
    }

    state.components
}

fn binding_is_ocaml_scc_function(bindings: &[(Ident, Lambda)], index: usize) -> bool {
    matches!(bindings[index].1, Lambda::Lfunction(_))
}

fn recursive_binding_group_is_function_only(bindings: &[(Ident, Lambda)], group: &[usize]) -> bool {
    group
        .iter()
        .all(|&index| binding_is_ocaml_scc_function(bindings, index))
}

fn sort_recursive_binding_group(bindings: &[(Ident, Lambda)], group: &mut [usize]) {
    if recursive_binding_group_is_function_only(bindings, group) {
        return;
    }
    group.sort_by_key(|index| !binding_is_ocaml_scc_function(bindings, *index));
}

fn recursive_binding_groups(
    bindings: &[(Ident, Lambda)],
    dependencies: &[Vec<usize>],
) -> Vec<Vec<usize>> {
    match bindings.len() {
        0 => vec![],
        1 => vec![vec![0]],
        _ => {
            let mut groups = strongly_connected_binding_components(dependencies);
            if groups.len() <= 1 {
                groups = vec![(0..bindings.len()).collect()];
            }
            for group in &mut groups {
                sort_recursive_binding_group(bindings, group);
            }
            groups
        }
    }
}

fn recursive_function_bindings(bindings: &[(Ident, Lambda)]) -> AHashMap<Ident, LFunction> {
    bindings
        .iter()
        .filter_map(|(id, expr)| recursive_function_binding_value(expr).map(|func| (*id, func)))
        .collect()
}

fn recursive_function_bindings_in_group(
    bindings: &[(Ident, Lambda)],
    group: &[usize],
) -> AHashMap<Ident, LFunction> {
    group
        .iter()
        .filter_map(|&index| {
            let (id, expr) = &bindings[index];
            recursive_function_binding_value(expr).map(|func| (*id, func))
        })
        .collect()
}

fn recursive_function_binding_alias_target(
    expr: &Lambda,
    recursive_functions: &AHashMap<Ident, LFunction>,
) -> Option<Ident> {
    let lookup = |target: &Ident| {
        recursive_functions
            .iter()
            .find(|(function_id, _)| target.same(function_id))
    };

    match expr {
        Lambda::Lvar(target) => lookup(target).map(|(function_id, _)| *function_id),
        _ => None,
    }
}

fn lower_ocaml_for_range_direction<'a>(
    direction: &crate::lambda::DirectionFlag,
    finish: &'a Lambda,
) -> (&'a Lambda, ForDirection) {
    match (direction, finish) {
        (crate::lambda::DirectionFlag::Upto, Lambda::Lprim(__prim3))
            if matches!(
                __prim3.as_ref(),
                crate::lambda::PrimInfo {
                    primitive: Primitive::Psubint,
                    args: _,
                    ..
                }
            ) =>
        {
            let crate::lambda::PrimInfo {
                primitive: Primitive::Psubint,
                args,
                ..
            } = __prim3.as_ref()
            else {
                unreachable!()
            };
            match args.as_slice() {
                [new_finish, Lambda::Lconst(Constant::Int { i: 1, .. })] => {
                    (new_finish, ForDirection::Up)
                }
                _ => (finish, ForDirection::Upto),
            }
        }
        (crate::lambda::DirectionFlag::Upto, _) => (finish, ForDirection::Upto),
        (crate::lambda::DirectionFlag::Downto, _) => (finish, ForDirection::Downto),
    }
}

fn block_last_is_continue(block: &Block) -> bool {
    matches!(
        block.last(),
        Some(Statement {
            desc: StatementDesc::Continue(_),
            ..
        })
    )
}

fn block_last_is_non_continue_terminal(block: &Block) -> bool {
    matches!(
        block.last(),
        Some(Statement {
            desc: StatementDesc::Return(_) | StatementDesc::Throw(_) | StatementDesc::Break(_),
            ..
        })
    )
}

fn merge_terminal_guard_fallthrough_else(block: Block) -> Block {
    let [first, rest @ ..] = block.as_slice() else {
        return block;
    };
    let StatementDesc::If(cond, then_block, else_block) = &first.desc else {
        return block;
    };
    if !else_block.is_empty()
        || !block_last_is_terminal(then_block)
        || !block_last_is_terminal(&rest.to_vec())
    {
        return block;
    }

    // OCaml's `S.if_` can preserve a terminal `if/else` when the branch reaches
    // it as a block-wrapped statement (compiler/core/js_stmt_make.ml:247-250).
    // Rust tail-loop lowering has already flattened that wrapper, so rebuild the
    // same terminal fallback before placing it under the outer negative guard.
    vec![Statement::new(StatementDesc::If(
        cond.clone(),
        then_block.clone(),
        rest.to_vec(),
    ))]
}

fn function_has_self_tailcall(tail_targets: &[Ident], lam: &Lambda) -> bool {
    match lam {
        Lambda::Lapply(__apply1) => {
            let Apply { ap_func, .. } = __apply1.as_ref();

            matches!(ap_func.as_ref(), Lambda::Lvar(id) if tail_targets.iter().any(|target| id.same(target)))
        }
        Lambda::Llet(_, _, _, body) => function_has_self_tailcall(tail_targets, body),
        Lambda::LifThenElse(_, then_, else_) => {
            function_has_self_tailcall(tail_targets, then_)
                || function_has_self_tailcall(tail_targets, else_)
        }
        Lambda::Lsequence(_, second) => function_has_self_tailcall(tail_targets, second),
        Lambda::Lprim(info) => short_circuit_primitive(&info.primitive, &info.args)
            .is_some_and(|(_, _, rhs)| function_has_self_tailcall(tail_targets, rhs)),
        Lambda::Lswitch(_, switch) => {
            switch
                .sw_consts
                .iter()
                .any(|(_, body)| function_has_self_tailcall(tail_targets, body))
                || switch
                    .sw_blocks
                    .iter()
                    .any(|(_, body)| function_has_self_tailcall(tail_targets, body))
                || switch
                    .sw_failaction
                    .as_ref()
                    .is_some_and(|fallback| function_has_self_tailcall(tail_targets, fallback))
        }
        Lambda::LstringSwitch(_, cases, default) => {
            cases
                .iter()
                .any(|(_, body)| function_has_self_tailcall(tail_targets, body))
                || default
                    .as_ref()
                    .is_some_and(|fallback| function_has_self_tailcall(tail_targets, fallback))
        }
        Lambda::LstaticCatch(body, _, handler) => {
            function_has_self_tailcall(tail_targets, body)
                || function_has_self_tailcall(tail_targets, handler)
        }
        // lam_compile.ml `compile_try`: with a finally block neither the body
        // nor the catch handler is in tail position.
        Lambda::LtryFinally(_, _) => false,
        Lambda::LtryWith(_, _, handler) => {
            // OCaml `compile_trywith` changes only the try body's tail type to
            // `Tail_in_try`; the handler keeps the original `Tail_with_name`
            // context (compiler/core/lam_compile.ml:1315-1344).
            function_has_self_tailcall(tail_targets, handler)
        }
        Lambda::Lvar(_)
        | Lambda::LglobalModule(_)
        | Lambda::Lconst(_)
        | Lambda::Lfunction(_)
        | Lambda::Lletrec(_, _)
        | Lambda::LstaticRaise(_, _)
        | Lambda::Lbreak
        | Lambda::Lcontinue
        | Lambda::Lwhile(_, _)
        | Lambda::Lfor(_, _, _, _, _)
        | Lambda::Lfor_of(_, _, _)
        | Lambda::Lfor_await_of(_, _, _)
        | Lambda::Lassign(_, _) => false,
    }
}

fn direct_recursive_function_tail_targets(
    bindings: &[(Ident, Lambda)],
) -> AHashMap<Ident, Vec<Ident>> {
    let recursive_functions = recursive_function_bindings(bindings);
    direct_recursive_function_tail_targets_with_bindings(bindings, &recursive_functions)
}

fn direct_recursive_function_tail_targets_with_group(
    bindings: &[(Ident, Lambda)],
    group: &[usize],
    recursive_functions: &AHashMap<Ident, LFunction>,
) -> AHashMap<Ident, Vec<Ident>> {
    let mut tail_targets: AHashMap<Ident, Vec<Ident>> = recursive_functions
        .keys()
        .cloned()
        .map(|id| {
            let targets = vec![id];
            (id, targets)
        })
        .collect();

    for &index in group {
        let (id, expr) = &bindings[index];
        let Some(function_id) = recursive_function_binding_alias_target(expr, recursive_functions)
        else {
            continue;
        };
        tail_targets.entry(function_id).or_default().push(*id);
    }

    tail_targets
}

fn direct_recursive_function_tail_targets_with_bindings(
    bindings: &[(Ident, Lambda)],
    recursive_functions: &AHashMap<Ident, LFunction>,
) -> AHashMap<Ident, Vec<Ident>> {
    let mut tail_targets: AHashMap<Ident, Vec<Ident>> = recursive_functions
        .keys()
        .cloned()
        .map(|id| {
            let targets = vec![id];
            (id, targets)
        })
        .collect();

    for (id, expr) in bindings {
        let Some(function_id) = recursive_function_binding_alias_target(expr, recursive_functions)
        else {
            continue;
        };
        tail_targets.entry(function_id).or_default().push(*id);
    }

    tail_targets
}

fn module_sort_name(module: &ModuleId) -> &str {
    match &module.kind {
        Kind::External { name, .. } => name.as_str(),
        Kind::Runtime | Kind::Ml => module.id.name(),
    }
}

fn module_sort_cmp(left: &ModuleId, right: &ModuleId) -> std::cmp::Ordering {
    let left_name = module_sort_name(left).as_bytes();
    let right_name = module_sort_name(right).as_bytes();
    left_name
        .len()
        .cmp(&right_name.len())
        .then_with(|| left_name.cmp(right_name))
        .then_with(|| module_kind_rank(left).cmp(&module_kind_rank(right)))
}

/// `Lam_module_ident.compare_same_name`: modules with the same name are
/// ordered by kind.
fn module_kind_rank(module: &ModuleId) -> u8 {
    match module.kind {
        Kind::Ml => 0,
        Kind::Runtime => 1,
        Kind::External { default: false, .. } => 2,
        Kind::External { default: true, .. } => 3,
    }
}

fn ext_ident_cmp(left: &Ident, right: &Ident) -> std::cmp::Ordering {
    // OCaml reference: compiler/ext/ext_ident.ml:178-180 compares stamp first,
    // then `Ext_string.compare`; compiler/ext/ext_string.ml:335-338 delegates
    // to `caml_string_length_based_compare`, implemented in
    // compiler/ext/ext_basic_hash_stubs.c:110-140 as length, then byte order.
    left.stamp()
        .cmp(&right.stamp())
        .then_with(|| left.name().len().cmp(&right.name().len()))
        .then_with(|| left.name().as_bytes().cmp(right.name().as_bytes()))
}

fn ocaml_hashtbl_power_2_above(mut x: usize, n: usize) -> usize {
    while x < n {
        x <<= 1;
    }
    x
}

fn ocaml_hash_mix_uint32(mut h: u32, mut d: u32) -> u32 {
    d = d.wrapping_mul(0xcc9e2d51);
    d = d.rotate_left(15);
    d = d.wrapping_mul(0x1b873593);
    h ^= d;
    h = h.rotate_left(13);
    h = h.wrapping_mul(5).wrapping_add(0xe6546b64);
    h
}

fn ocaml_hash_final_mix(mut h: u32) -> u32 {
    h ^= h >> 16;
    h = h.wrapping_mul(0x85ebca6b);
    h ^= h >> 13;
    h = h.wrapping_mul(0xc2b2ae35);
    h ^= h >> 16;
    h
}

fn ocaml_hashtbl_hash_string(s: &str) -> u32 {
    let bytes = s.as_bytes();
    let len = bytes.len();
    let mut h = 0u32;
    let mut i = 0usize;

    while i + 4 <= len {
        let word = u32::from_le_bytes([bytes[i], bytes[i + 1], bytes[i + 2], bytes[i + 3]]);
        h = ocaml_hash_mix_uint32(h, word);
        i += 4;
    }

    let rem = len & 3;
    if rem != 0 {
        let mut word = 0u32;
        if rem >= 3 {
            word |= (bytes[i + 2] as u32) << 16;
        }
        if rem >= 2 {
            word |= (bytes[i + 1] as u32) << 8;
        }
        word |= bytes[i] as u32;
        h = ocaml_hash_mix_uint32(h, word);
    }

    h ^= len as u32;
    ocaml_hash_final_mix(h) & 0x3fff_ffff
}

fn ocaml_hashtbl_hash_stamp_and_name(id: &Ident) -> u32 {
    let stamp = id.stamp();
    if stamp != 0 {
        ocaml_hash_final_mix(ocaml_hash_mix_uint32(0, stamp as u32)) & 0x3fff_ffff
    } else {
        ocaml_hashtbl_hash_string(id.name())
    }
}

fn ocaml_module_hash(module: &ModuleId) -> u32 {
    match &module.kind {
        Kind::External { name, .. } => ocaml_hashtbl_hash_string(name),
        Kind::Runtime | Kind::Ml => ocaml_hashtbl_hash_stamp_and_name(&module.id),
    }
}

fn ocaml_module_equal(left: &ModuleId, right: &ModuleId) -> bool {
    match &left.kind {
        Kind::External {
            name: left_name,
            default: left_default,
            ..
        } => {
            matches!(
                &right.kind,
                Kind::External {
                    name: right_name,
                    default: right_default,
                    ..
                } if left_name == right_name && left_default == right_default
            )
        }
        Kind::Runtime | Kind::Ml => left.id.same(&right.id),
    }
}

#[derive(Debug, Clone)]
struct OcamlModuleSet {
    size: usize,
    buckets: Vec<Vec<ModuleId>>,
}

impl OcamlModuleSet {
    fn new() -> Self {
        Self {
            size: 0,
            buckets: vec![Vec::new(); ocaml_hashtbl_power_2_above(16, 17)],
        }
    }

    fn insert(&mut self, module: ModuleId) {
        let bucket_idx = (ocaml_module_hash(&module) as usize) & (self.buckets.len() - 1);
        if self.buckets[bucket_idx]
            .iter()
            .any(|existing| ocaml_module_equal(existing, &module))
        {
            return;
        }

        self.buckets[bucket_idx].insert(0, module);
        self.size += 1;

        if self.size > (self.buckets.len() << 1) {
            self.resize();
        }
    }

    fn resize(&mut self) {
        let mut new_buckets = vec![Vec::new(); self.buckets.len() * 2];
        for bucket in &self.buckets {
            for module in bucket {
                let bucket_idx = (ocaml_module_hash(module) as usize) & (new_buckets.len() - 1);
                new_buckets[bucket_idx].push(module.clone());
            }
        }
        self.buckets = new_buckets;
    }

    fn to_vec(&self) -> Vec<ModuleId> {
        let mut ordered = Vec::with_capacity(self.size);
        for bucket in &self.buckets {
            for module in bucket {
                ordered.push(module.clone());
            }
        }
        ordered.reverse();
        ordered
    }
}

fn ocaml_sort_modules(modules: &mut [ModuleId]) {
    fn maxson(modules: &[ModuleId], len: usize, index: usize) -> Option<usize> {
        let left = index * 3 + 1;
        let middle = left + 1;
        let right = middle + 1;
        if middle < len {
            if module_sort_cmp(&modules[left], &modules[middle]).is_lt() {
                if right < len && module_sort_cmp(&modules[middle], &modules[right]).is_lt() {
                    Some(right)
                } else {
                    Some(middle)
                }
            } else if right < len && module_sort_cmp(&modules[left], &modules[right]).is_lt() {
                Some(right)
            } else {
                Some(left)
            }
        } else if left < len {
            Some(left)
        } else {
            None
        }
    }

    fn trickledown(modules: &mut [ModuleId], len: usize, index: usize, entry: ModuleId) -> usize {
        let Some(child) = maxson(modules, len, index) else {
            return index;
        };
        if module_sort_cmp(&entry, &modules[child]).is_lt() {
            modules[index] = modules[child].clone();
            trickledown(modules, len, child, entry)
        } else {
            index
        }
    }

    fn trickle(modules: &mut [ModuleId], len: usize, index: usize, entry: ModuleId) {
        let bottom = trickledown(modules, len, index, entry.clone());
        modules[bottom] = entry;
    }

    fn bubbledown(modules: &mut [ModuleId], len: usize, index: usize) -> usize {
        let Some(child) = maxson(modules, len, index) else {
            return index;
        };
        modules[index] = modules[child].clone();
        bubbledown(modules, len, child)
    }

    fn bubble(modules: &mut [ModuleId], len: usize, index: usize) -> usize {
        bubbledown(modules, len, index)
    }

    fn trickleup(modules: &mut [ModuleId], mut index: usize, entry: ModuleId) {
        loop {
            let parent = (index - 1) / 3;
            debug_assert_ne!(index, parent);
            if module_sort_cmp(&modules[parent], &entry).is_lt() {
                modules[index] = modules[parent].clone();
                if parent > 0 {
                    index = parent;
                    continue;
                }
                modules[0] = entry;
                return;
            }
            modules[index] = entry;
            return;
        }
    }

    let len = modules.len();
    if len < 2 {
        return;
    }

    for index in (0..=((len + 1) / 3).saturating_sub(1)).rev() {
        let entry = modules[index].clone();
        trickle(modules, len, index, entry);
    }
    for index in (2..len).rev() {
        let entry = modules[index].clone();
        modules[index] = modules[0].clone();
        let bubble_index = bubble(modules, index, 0);
        trickleup(modules, bubble_index, entry);
    }
    modules.swap(0, 1);
}

pub(crate) fn collect_possible_required_modules_for_lambda(lam: &Lambda) -> AHashSet<ModuleId> {
    // OCaml compiler/core/lam_compile_main.ml:277-284 collects into a hash set
    // and sorts after `populate_required_modules`, so the hash iteration order is
    // intentionally unobservable here.
    let mut seen = AHashSet::new();
    collect_modules_from_lambda(lam, &mut seen);
    seen
}

fn collect_cmj_export_constants_from_simplified_lambda(
    lam: &Lambda,
) -> AHashMap<String, CmjExportConstant> {
    let mut bindings = Vec::new();
    let Some((exports, args)) = collect_toplevel_export_bindings(lam, &mut bindings) else {
        return AHashMap::new();
    };
    let mut constants = AHashMap::new();
    for (export, arg) in exports.iter().zip(args) {
        let value = match arg {
            Lambda::Lvar(id) => bindings
                .iter()
                .rev()
                .find_map(|(binding, value)| binding.same(id).then_some(*value))
                .unwrap_or(arg),
            _ => arg,
        };
        if let Some(constant) = cmj_export_constant_from_lambda(value) {
            constants.insert(export.name().to_string(), constant);
        }
    }
    constants
}

/// The non-constant `persistent_closed_lambda` of each export under
/// `-bs-cross-module-opt` (compiler/core/lam_stats_export.ml:53-89):
/// safe-to-inline lambdas that are closed always-inline functions or
/// functors, or small (`Lam_analysis.small_inline_size`) and free of free
/// variables. Constant exports travel as `CmjExportConstant`s.
fn collect_cmj_export_lambdas_from_simplified_lambda(lam: &Lambda) -> AHashMap<String, Lambda> {
    let mut bindings = Vec::new();
    let Some((exports, args)) = collect_toplevel_export_bindings(lam, &mut bindings) else {
        return AHashMap::new();
    };
    let mut lambdas = AHashMap::new();
    for (export, arg) in exports.iter().zip(args) {
        let value = match arg {
            Lambda::Lvar(id) => bindings
                .iter()
                .rev()
                .find_map(|(binding, value)| binding.same(id).then_some(*value))
                .unwrap_or(arg),
            _ => arg,
        };
        if cmj_export_constant_from_lambda(value).is_some()
            || !crate::lambda::lam_analysis::safe_to_inline(value)
        {
            continue;
        }
        let inline = match value {
            Lambda::Lfunction(func)
                if matches!(func.attr.inline, crate::lambda::InlineAttribute::Always)
                    || func.attr.is_a_functor =>
            {
                crate::lambda::lam_closure::is_closed(value)
            }
            _ => {
                crate::lambda::lam_analysis::size_upto(
                    crate::lambda::lam_analysis::SMALL_INLINE_SIZE,
                    value,
                ) < crate::lambda::lam_analysis::SMALL_INLINE_SIZE
                    && crate::lambda::lam_closure::free_variables_with_stats(
                        &Default::default(),
                        Default::default(),
                        value,
                    )
                    .is_empty()
            }
        };
        if inline {
            lambdas.insert(export.name().to_string(), value.clone());
        }
    }
    lambdas
}

fn collect_cmj_export_arities_from_simplified_lambda(
    lam: &Lambda,
    meta: &LamStats,
) -> AHashMap<String, CmjExportArity> {
    // OCaml writes `.cmj` arity metadata from `Lam_stats_export.values_of_export`
    // (compiler/core/lam_stats_export.ml:32-49). Use the `LamStats` returned
    // by the same `Lam_coercion.coerce_and_group_big_lambda` counterpart that
    // OCaml uses, instead of recomputing `collect_info` after simplification.
    let mut bindings = Vec::new();
    let Some((exports, args)) = collect_toplevel_export_bindings(lam, &mut bindings) else {
        return AHashMap::new();
    };

    let mut arities = AHashMap::new();
    for (export, arg) in exports.iter().zip(args) {
        match meta.ident_tbl.get(export) {
            Some(IdKind::FunctionId { arity, .. }) => {
                arities.insert(
                    export.name().to_string(),
                    CmjExportArity::Single(arity.clone()),
                );
            }
            Some(IdKind::ImmutableBlock(items)) => {
                let submodule_arities = items
                    .iter()
                    .map(|item| match item {
                        Element::Na => Arity::na(),
                        Element::SimpleForm(lam) => get_arity(meta, lam),
                    })
                    .collect::<Vec<_>>();
                arities.insert(
                    export.name().to_string(),
                    CmjExportArity::Submodule(submodule_arities),
                );
            }
            _ => {
                let value = match arg {
                    Lambda::Lvar(id) => bindings
                        .iter()
                        .rev()
                        .find_map(|(binding, value)| binding.same(id).then_some(*value))
                        .unwrap_or(arg),
                    _ => arg,
                };
                if let Lambda::Lprim(__prim200) = value
                    && let PrimInfo {
                        primitive:
                            Primitive::Pmakeblock(_, crate::lambda::lam_primitive::Mutable::Immutable),
                        args,
                        ..
                    } = __prim200.as_ref()
                {
                    let submodule_arities = args
                        .iter()
                        .map(|lam| get_arity(meta, lam))
                        .collect::<Vec<_>>();
                    arities.insert(
                        export.name().to_string(),
                        CmjExportArity::Submodule(submodule_arities),
                    );
                }
            }
        }
    }
    arities
}

fn collect_toplevel_export_bindings<'a>(
    lam: &'a Lambda,
    bindings: &mut Vec<(&'a Ident, &'a Lambda)>,
) -> Option<(&'a [Ident], &'a [Lambda])> {
    match lam {
        Lambda::Llet(_, id, value, body) => {
            bindings.push((id, value));
            collect_toplevel_export_bindings(body, bindings)
        }
        Lambda::Lletrec(items, body) => {
            for (id, value) in items {
                bindings.push((id, value));
            }
            collect_toplevel_export_bindings(body, bindings)
        }
        Lambda::Lsequence(_, right) => collect_toplevel_export_bindings(right, bindings),
        Lambda::Lprim(__prim0)
            if matches!(
                __prim0.as_ref(),
                PrimInfo {
                    primitive: Primitive::Pmakeblock(TagInfo::ModuleExport(_exports), _),
                    args: _,
                    ..
                }
            ) =>
        {
            let PrimInfo {
                primitive: Primitive::Pmakeblock(TagInfo::ModuleExport(exports), _),
                args,
                ..
            } = __prim0.as_ref()
            else {
                unreachable!()
            };
            Some((exports, args))
        }
        _ => None,
    }
}

fn cmj_export_constant_from_lambda(lam: &Lambda) -> Option<CmjExportConstant> {
    // OCaml writes `.cmj` value metadata from `coerced_input.export_map`
    // (compiler/core/lam_compile_main.ml:290-295), not from the final JS program.
    // Under the default `cross_module_inline = false`, `values_of_export` keeps
    // only direct closed constants: null / undefined / true / false
    // (compiler/core/lam_stats_export.ml:53-61). Do not inspect JS IR here:
    // `compile_external_field` may inline a dependency constant during JS lowering
    // (compiler/core/lam_compile.ml:234-244), but OCaml does not record that in
    // the exporting module's `.cmj`.
    match lam {
        Lambda::Lconst(Constant::JsNull) => Some(CmjExportConstant::Null),
        Lambda::Lconst(Constant::JsUndefined { is_unit }) => {
            Some(CmjExportConstant::Undefined { is_unit: *is_unit })
        }
        Lambda::Lconst(Constant::JsTrue) => Some(CmjExportConstant::Bool(true)),
        Lambda::Lconst(Constant::JsFalse) => Some(CmjExportConstant::Bool(false)),
        _ => None,
    }
}

fn collect_modules_from_lambda(lam: &Lambda, seen: &mut AHashSet<ModuleId>) {
    match lam {
        Lambda::Lvar(_) | Lambda::Lconst(_) => {}
        Lambda::LglobalModule(id) => {
            seen.insert(ModuleId {
                id: *id,
                kind: Kind::Ml,
                dynamic_import: false,
            });
        }
        Lambda::Lapply(apply) => {
            collect_modules_from_lambda(&apply.ap_func, seen);
            for arg in &apply.ap_args {
                collect_modules_from_lambda(arg, seen);
            }
        }
        Lambda::Lfunction(func) => collect_modules_from_lambda(&func.body, seen),
        Lambda::Llet(_, _, value, body) => {
            collect_modules_from_lambda(value, seen);
            collect_modules_from_lambda(body, seen);
        }
        Lambda::Lletrec(bindings, body) => {
            for (_, binding) in bindings {
                collect_modules_from_lambda(binding, seen);
            }
            collect_modules_from_lambda(body, seen);
        }
        Lambda::Lprim(info) => {
            for arg in &info.args {
                collect_modules_from_lambda(arg, seen);
            }
        }
        Lambda::Lswitch(arg, switch) => {
            collect_modules_from_lambda(arg, seen);
            for (_, branch) in &switch.sw_consts {
                collect_modules_from_lambda(branch, seen);
            }
            for (_, branch) in &switch.sw_blocks {
                collect_modules_from_lambda(branch, seen);
            }
            if let Some(failaction) = &switch.sw_failaction {
                collect_modules_from_lambda(failaction, seen);
            }
        }
        Lambda::LstringSwitch(arg, cases, default) => {
            collect_modules_from_lambda(arg, seen);
            for (_, branch) in cases {
                collect_modules_from_lambda(branch, seen);
            }
            if let Some(default) = default {
                collect_modules_from_lambda(default, seen);
            }
        }
        Lambda::LstaticRaise(_, args) => {
            for arg in args {
                collect_modules_from_lambda(arg, seen);
            }
        }
        Lambda::LstaticCatch(body, _, handler)
        | Lambda::LtryWith(body, _, handler)
        | Lambda::LtryFinally(body, handler) => {
            collect_modules_from_lambda(body, seen);
            collect_modules_from_lambda(handler, seen);
        }
        Lambda::LifThenElse(cond, then_, else_) => {
            collect_modules_from_lambda(cond, seen);
            collect_modules_from_lambda(then_, seen);
            collect_modules_from_lambda(else_, seen);
        }
        Lambda::Lsequence(first, second) => {
            collect_modules_from_lambda(first, seen);
            collect_modules_from_lambda(second, seen);
        }
        Lambda::Lwhile(cond, body) => {
            collect_modules_from_lambda(cond, seen);
            collect_modules_from_lambda(body, seen);
        }
        Lambda::Lfor(_, start, finish, _, body) => {
            collect_modules_from_lambda(start, seen);
            collect_modules_from_lambda(finish, seen);
            collect_modules_from_lambda(body, seen);
        }
        Lambda::Lfor_of(_, iterable, body) | Lambda::Lfor_await_of(_, iterable, body) => {
            collect_modules_from_lambda(iterable, seen);
            collect_modules_from_lambda(body, seen);
        }
        Lambda::Lbreak | Lambda::Lcontinue => {}
        Lambda::Lassign(_, value) => collect_modules_from_lambda(value, seen),
    }
}

fn populate_required_modules(
    module_path_resolver: Option<&ModulePathResolver>,
    extras: &AHashSet<ModuleId>,
    modules: &mut OcamlModuleSet,
) {
    for module in extras {
        if required_module_side_effect_reason(module_path_resolver, std::slice::from_ref(module))
            .is_some()
        {
            modules.insert(module.clone());
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum TopLevelEffectGroupRef<'a> {
    Single(LetKind, &'a Ident, &'a Lambda),
    Recursive(&'a [(Ident, Lambda)]),
    Nop(&'a Lambda),
}

fn top_level_effect_group_single_ref<'a>(
    kind: LetKind,
    ident: &'a Ident,
    body: &'a Lambda,
) -> TopLevelEffectGroupRef<'a> {
    match (kind, body) {
        (LetKind::Strict | LetKind::StrictOpt, Lambda::Lvar(_) | Lambda::Lconst(_)) => {
            TopLevelEffectGroupRef::Single(LetKind::Alias, ident, body)
        }
        _ => TopLevelEffectGroupRef::Single(kind, ident, body),
    }
}

fn push_top_level_effect_nop_ref<'a>(
    lam: &'a Lambda,
    groups: &mut Vec<TopLevelEffectGroupRef<'a>>,
) {
    if !matches!(
        lam,
        Lambda::Lvar(_) | Lambda::Lconst(_) | Lambda::Lfunction(_)
    ) {
        groups.push(TopLevelEffectGroupRef::Nop(lam));
    }
}

fn collect_top_level_effect_group_refs<'a>(
    lam: &'a Lambda,
    groups: &mut Vec<TopLevelEffectGroupRef<'a>>,
) -> &'a Lambda {
    match lam {
        Lambda::Llet(kind, id, value, body) => {
            let result = collect_top_level_effect_group_refs(value, groups);
            groups.push(top_level_effect_group_single_ref(*kind, id, result));
            collect_top_level_effect_group_refs(body, groups)
        }
        Lambda::Lletrec(bindings, body) => {
            groups.push(TopLevelEffectGroupRef::Recursive(bindings));
            collect_top_level_effect_group_refs(body, groups)
        }
        Lambda::Lsequence(first, second) => {
            let result = collect_top_level_effect_group_refs(first, groups);
            push_top_level_effect_nop_ref(result, groups);
            collect_top_level_effect_group_refs(second, groups)
        }
        _ => lam,
    }
}

fn module_side_effect_reason(lam: &Lambda) -> Option<String> {
    // OCaml `Lam_coercion.flatten` builds top-level groups in source order
    // before `Lam_compile_main.compile_lambda` asks `Lam_compile.no_side_effect`
    // for each group (compiler/core/lam_coercion.ml:179-199,
    // compiler/core/lam_compile_main.ml:210-236). The Rust Lambda backend walks
    // one tree rather than OCaml's grouped list, so keep borrowed group refs in
    // the same order and avoid cloning each top-level body just to inspect it.
    let mut groups = Vec::new();
    let result = collect_top_level_effect_group_refs(lam, &mut groups);
    groups
        .iter()
        .find_map(|group| match group {
            TopLevelEffectGroupRef::Single(kind, id, body) => {
                (matches!(*kind, LetKind::Strict | LetKind::Variable)
                    && !lam_analysis::no_side_effects(body))
                .then(|| id.name().to_string())
            }
            TopLevelEffectGroupRef::Recursive(bindings) => {
                bindings.iter().find_map(|(id, body)| {
                    (!lam_analysis::no_side_effects(body)).then(|| id.name().to_string())
                })
            }
            TopLevelEffectGroupRef::Nop(body) => {
                (!lam_analysis::no_side_effects(body)).then(String::new)
            }
        })
        .or_else(|| (!lam_analysis::no_side_effects(result)).then(String::new))
}

fn required_module_side_effect_reason(
    module_path_resolver: Option<&ModulePathResolver>,
    modules: &[ModuleId],
) -> Option<String> {
    modules.iter().find_map(|module| {
        if let Some(resolver) = module_path_resolver {
            resolver.module_side_effect_reason(module)
        } else {
            match &module.kind {
                Kind::Runtime => None,
                Kind::External { name, .. } => Some(name.clone()),
                Kind::Ml => Some(module.id.name().to_string()),
            }
        }
    })
}

pub(crate) fn compiled_from_effect_block(mut block: Block) -> Compiled {
    if block.len() == 1 {
        let stmt = block.pop().expect("single-item block");
        let Statement {
            source_loc: _,
            desc,
            comment,
        } = stmt;
        return match desc {
            StatementDesc::Exp(mut expr) => {
                if expr.comment.is_none() {
                    expr.comment = comment;
                }
                Compiled {
                    prelude: vec![],
                    expr,
                    finished: OutputFinished::False,
                }
            }
            StatementDesc::Block(inner) if comment.is_none() => compiled_from_effect_block(inner),
            desc => Compiled {
                prelude: vec![Statement {
                    source_loc: None,
                    desc,
                    comment,
                }],
                expr: Expression::undefined(false),
                finished: OutputFinished::False,
            },
        };
    }

    Compiled {
        prelude: block,
        expr: Expression::undefined(false),
        finished: OutputFinished::False,
    }
}

fn lambda_contains_static_raise(lam: &Lambda) -> bool {
    match lam {
        Lambda::Lvar(_) | Lambda::LglobalModule(_) | Lambda::Lconst(_) => false,
        Lambda::Lapply(apply) => {
            lambda_contains_static_raise(&apply.ap_func)
                || apply.ap_args.iter().any(lambda_contains_static_raise)
        }
        Lambda::Lfunction(func) => lambda_contains_static_raise(&func.body),
        Lambda::Llet(_, _, value, body) => {
            lambda_contains_static_raise(value) || lambda_contains_static_raise(body)
        }
        Lambda::Lletrec(bindings, body) => {
            bindings
                .iter()
                .any(|(_, value)| lambda_contains_static_raise(value))
                || lambda_contains_static_raise(body)
        }
        Lambda::Lprim(info) => info.args.iter().any(lambda_contains_static_raise),
        Lambda::Lswitch(scrut, switch) => {
            lambda_contains_static_raise(scrut)
                || switch
                    .sw_consts
                    .iter()
                    .any(|(_, body)| lambda_contains_static_raise(body))
                || switch
                    .sw_blocks
                    .iter()
                    .any(|(_, body)| lambda_contains_static_raise(body))
                || switch
                    .sw_failaction
                    .as_deref()
                    .is_some_and(lambda_contains_static_raise)
        }
        Lambda::LstringSwitch(scrut, cases, default) => {
            lambda_contains_static_raise(scrut)
                || cases
                    .iter()
                    .any(|(_, body)| lambda_contains_static_raise(body))
                || default.as_deref().is_some_and(lambda_contains_static_raise)
        }
        Lambda::LstaticRaise(_, _) => true,
        Lambda::LstaticCatch(body, (_, _), handler)
        | Lambda::LtryWith(body, _, handler)
        | Lambda::LtryFinally(body, handler) => {
            lambda_contains_static_raise(body) || lambda_contains_static_raise(handler)
        }
        Lambda::Lsequence(first, second) => {
            lambda_contains_static_raise(first) || lambda_contains_static_raise(second)
        }
        Lambda::Lwhile(cond, body) => {
            lambda_contains_static_raise(cond) || lambda_contains_static_raise(body)
        }
        Lambda::Lfor(_, start, finish, _, body) => {
            lambda_contains_static_raise(start)
                || lambda_contains_static_raise(finish)
                || lambda_contains_static_raise(body)
        }
        Lambda::Lfor_of(_, iterable, body) | Lambda::Lfor_await_of(_, iterable, body) => {
            lambda_contains_static_raise(iterable) || lambda_contains_static_raise(body)
        }
        Lambda::Lbreak | Lambda::Lcontinue => false,
        Lambda::Lassign(_, value) => lambda_contains_static_raise(value),
        Lambda::LifThenElse(cond, then_, else_) => {
            lambda_contains_static_raise(cond)
                || lambda_contains_static_raise(then_)
                || lambda_contains_static_raise(else_)
        }
    }
}

fn handler_has_static_raise_like_ocaml(handler: &Lambda) -> bool {
    // OCaml's `Lam_compile_context.no_static_raise_in_handler`
    // (compiler/core/lam_compile_context.ml:105-106) is defined in terms of
    // `Lam_exit_code.has_exit_code`; that search stops at `Lfunction`
    // (compiler/core/lam_exit_code.ml:25-31), because static exits cannot cross
    // function boundaries. Handler guards in Rust must use the same reachability
    // rule instead of the broader `lambda_contains_static_raise`, which also
    // sees static raises nested inside closures.
    has_exit_code(handler, |_| true)
}

fn no_static_raise_in_handler_like_ocaml(handler: &Lambda) -> bool {
    !handler_has_static_raise_like_ocaml(handler)
}

pub(crate) fn lambda_has_exit(lam: &Lambda) -> bool {
    match lam {
        Lambda::Lvar(_) | Lambda::LglobalModule(_) | Lambda::Lconst(_) => false,
        Lambda::Lapply(apply) => {
            lambda_has_exit(&apply.ap_func) || apply.ap_args.iter().any(lambda_has_exit)
        }
        Lambda::Lfunction(_) => false,
        Lambda::Llet(_, _, value, body) => lambda_has_exit(value) || lambda_has_exit(body),
        Lambda::Lletrec(bindings, body) => {
            bindings.iter().any(|(_, value)| lambda_has_exit(value)) || lambda_has_exit(body)
        }
        Lambda::Lprim(info) => info.args.iter().any(lambda_has_exit),
        Lambda::Lswitch(scrut, switch) => {
            lambda_has_exit(scrut)
                || switch
                    .sw_consts
                    .iter()
                    .any(|(_, body)| lambda_has_exit(body))
                || switch
                    .sw_blocks
                    .iter()
                    .any(|(_, body)| lambda_has_exit(body))
                || switch.sw_failaction.as_deref().is_some_and(lambda_has_exit)
        }
        Lambda::LstringSwitch(scrut, cases, default) => {
            lambda_has_exit(scrut)
                || cases.iter().any(|(_, body)| lambda_has_exit(body))
                || default.as_deref().is_some_and(lambda_has_exit)
        }
        Lambda::LstaticRaise(_, _) => true,
        Lambda::LstaticCatch(body, (_, _), handler)
        | Lambda::LtryWith(body, _, handler)
        | Lambda::LtryFinally(body, handler) => lambda_has_exit(body) || lambda_has_exit(handler),
        Lambda::Lsequence(first, second) => lambda_has_exit(first) || lambda_has_exit(second),
        Lambda::Lwhile(cond, body) => lambda_has_exit(cond) || lambda_has_exit(body),
        Lambda::Lfor(_, start, finish, _, body) => {
            lambda_has_exit(start) || lambda_has_exit(finish) || lambda_has_exit(body)
        }
        Lambda::Lfor_of(_, iterable, body) | Lambda::Lfor_await_of(_, iterable, body) => {
            lambda_has_exit(iterable) || lambda_has_exit(body)
        }
        Lambda::Lbreak | Lambda::Lcontinue => false,
        Lambda::Lassign(_, value) => lambda_has_exit(value),
        Lambda::LifThenElse(cond, then_, else_) => {
            lambda_has_exit(cond) || lambda_has_exit(then_) || lambda_has_exit(else_)
        }
    }
}

/// The `should_break` of a switch case in a return continuation:
/// `Js_output.to_break_block` (js_output.ml:88-100) breaks unless the output
/// is finished, and `compile_general_cases` keeps the break only when the
/// case has an exit (lam_compile.ml:610-624).
pub(crate) fn return_case_needs_break(body: &Lambda, finished: OutputFinished) -> bool {
    lambda_has_exit(body) && finished != OutputFinished::True
}

fn lambda_contains_staticcatch(lam: &Lambda) -> bool {
    match lam {
        Lambda::Lvar(_) | Lambda::LglobalModule(_) | Lambda::Lconst(_) => false,
        Lambda::Lapply(apply) => {
            lambda_contains_staticcatch(&apply.ap_func)
                || apply.ap_args.iter().any(lambda_contains_staticcatch)
        }
        Lambda::Lfunction(func) => lambda_contains_staticcatch(&func.body),
        Lambda::Llet(_, _, value, body) => {
            lambda_contains_staticcatch(value) || lambda_contains_staticcatch(body)
        }
        Lambda::Lletrec(bindings, body) => {
            bindings
                .iter()
                .any(|(_, value)| lambda_contains_staticcatch(value))
                || lambda_contains_staticcatch(body)
        }
        Lambda::Lprim(info) => info.args.iter().any(lambda_contains_staticcatch),
        Lambda::Lswitch(scrut, switch) => {
            lambda_contains_staticcatch(scrut)
                || switch
                    .sw_consts
                    .iter()
                    .any(|(_, body)| lambda_contains_staticcatch(body))
                || switch
                    .sw_blocks
                    .iter()
                    .any(|(_, body)| lambda_contains_staticcatch(body))
                || switch
                    .sw_failaction
                    .as_deref()
                    .is_some_and(lambda_contains_staticcatch)
        }
        Lambda::LstringSwitch(scrut, cases, default) => {
            lambda_contains_staticcatch(scrut)
                || cases
                    .iter()
                    .any(|(_, body)| lambda_contains_staticcatch(body))
                || default.as_deref().is_some_and(lambda_contains_staticcatch)
        }
        Lambda::LstaticRaise(_, _) => false,
        Lambda::LstaticCatch(_, (_, _), _) => true,
        Lambda::LtryWith(body, _, handler) | Lambda::LtryFinally(body, handler) => {
            lambda_contains_staticcatch(body) || lambda_contains_staticcatch(handler)
        }
        Lambda::Lsequence(first, second) => {
            lambda_contains_staticcatch(first) || lambda_contains_staticcatch(second)
        }
        Lambda::Lwhile(cond, body) => {
            lambda_contains_staticcatch(cond) || lambda_contains_staticcatch(body)
        }
        Lambda::Lfor(_, start, finish, _, body) => {
            lambda_contains_staticcatch(start)
                || lambda_contains_staticcatch(finish)
                || lambda_contains_staticcatch(body)
        }
        Lambda::Lfor_of(_, iterable, body) | Lambda::Lfor_await_of(_, iterable, body) => {
            lambda_contains_staticcatch(iterable) || lambda_contains_staticcatch(body)
        }
        Lambda::Lbreak | Lambda::Lcontinue => false,
        Lambda::Lassign(_, value) => lambda_contains_staticcatch(value),
        Lambda::LifThenElse(cond, then_, else_) => {
            lambda_contains_staticcatch(cond)
                || lambda_contains_staticcatch(then_)
                || lambda_contains_staticcatch(else_)
        }
    }
}

fn lambda_contains_static_raise_to_label(lam: &Lambda, label: i32, arity: usize) -> bool {
    match lam {
        Lambda::Lvar(_) | Lambda::LglobalModule(_) | Lambda::Lconst(_) => false,
        Lambda::Lapply(apply) => {
            lambda_contains_static_raise_to_label(&apply.ap_func, label, arity)
                || apply
                    .ap_args
                    .iter()
                    .any(|arg| lambda_contains_static_raise_to_label(arg, label, arity))
        }
        Lambda::Lfunction(_) => false,
        Lambda::Llet(_, _, value, body) => {
            lambda_contains_static_raise_to_label(value, label, arity)
                || lambda_contains_static_raise_to_label(body, label, arity)
        }
        Lambda::Lletrec(bindings, body) => {
            bindings
                .iter()
                .any(|(_, value)| lambda_contains_static_raise_to_label(value, label, arity))
                || lambda_contains_static_raise_to_label(body, label, arity)
        }
        Lambda::Lprim(info) => info
            .args
            .iter()
            .any(|arg| lambda_contains_static_raise_to_label(arg, label, arity)),
        Lambda::Lswitch(scrut, switch) => {
            lambda_contains_static_raise_to_label(scrut, label, arity)
                || switch
                    .sw_consts
                    .iter()
                    .any(|(_, body)| lambda_contains_static_raise_to_label(body, label, arity))
                || switch
                    .sw_blocks
                    .iter()
                    .any(|(_, body)| lambda_contains_static_raise_to_label(body, label, arity))
                || switch
                    .sw_failaction
                    .as_deref()
                    .is_some_and(|body| lambda_contains_static_raise_to_label(body, label, arity))
        }
        Lambda::LstringSwitch(scrut, cases, default) => {
            lambda_contains_static_raise_to_label(scrut, label, arity)
                || cases
                    .iter()
                    .any(|(_, body)| lambda_contains_static_raise_to_label(body, label, arity))
                || default
                    .as_deref()
                    .is_some_and(|body| lambda_contains_static_raise_to_label(body, label, arity))
        }
        Lambda::LstaticRaise(raise_label, args) => *raise_label == label && args.len() == arity,
        Lambda::LstaticCatch(body, (_, _), handler)
        | Lambda::LtryWith(body, _, handler)
        | Lambda::LtryFinally(body, handler) => {
            lambda_contains_static_raise_to_label(body, label, arity)
                || lambda_contains_static_raise_to_label(handler, label, arity)
        }
        Lambda::Lsequence(first, second) => {
            lambda_contains_static_raise_to_label(first, label, arity)
                || lambda_contains_static_raise_to_label(second, label, arity)
        }
        Lambda::Lwhile(cond, body) => {
            lambda_contains_static_raise_to_label(cond, label, arity)
                || lambda_contains_static_raise_to_label(body, label, arity)
        }
        Lambda::Lfor(_, start, finish, _, body) => {
            lambda_contains_static_raise_to_label(start, label, arity)
                || lambda_contains_static_raise_to_label(finish, label, arity)
                || lambda_contains_static_raise_to_label(body, label, arity)
        }
        Lambda::Lfor_of(_, iterable, body) | Lambda::Lfor_await_of(_, iterable, body) => {
            lambda_contains_static_raise_to_label(iterable, label, arity)
                || lambda_contains_static_raise_to_label(body, label, arity)
        }
        Lambda::Lbreak | Lambda::Lcontinue => false,
        Lambda::Lassign(_, value) => lambda_contains_static_raise_to_label(value, label, arity),
        Lambda::LifThenElse(cond, then_, else_) => {
            lambda_contains_static_raise_to_label(cond, label, arity)
                || lambda_contains_static_raise_to_label(then_, label, arity)
                || lambda_contains_static_raise_to_label(else_, label, arity)
        }
    }
}

fn switch_cases_contain_static_raise_to_label<K>(
    const_cases: &[(K, Lambda)],
    block_cases: &[(K, Lambda)],
    label: i32,
    arity: usize,
) -> bool {
    const_cases
        .iter()
        .any(|(_, body)| lambda_contains_static_raise_to_label(body, label, arity))
        || block_cases
            .iter()
            .any(|(_, body)| lambda_contains_static_raise_to_label(body, label, arity))
}

fn string_switch_cases_contain_static_raise_to_label(
    cases: &[(String, Lambda)],
    label: i32,
    arity: usize,
) -> bool {
    cases
        .iter()
        .any(|(_, body)| lambda_contains_static_raise_to_label(body, label, arity))
}

fn lambda_is_direct_static_raise_to_label(lam: &Lambda, label: i32, arity: usize) -> bool {
    matches!(lam, Lambda::LstaticRaise(raise_label, args) if *raise_label == label && args.len() == arity)
}

fn switch_cases_contain_nontrivial_static_raise_to_label<K>(
    const_cases: &[(K, Lambda)],
    block_cases: &[(K, Lambda)],
    label: i32,
    arity: usize,
) -> bool {
    const_cases.iter().any(|(_, body)| {
        lambda_contains_static_raise_to_label(body, label, arity)
            && !lambda_is_direct_static_raise_to_label(body, label, arity)
    }) || block_cases.iter().any(|(_, body)| {
        lambda_contains_static_raise_to_label(body, label, arity)
            && !lambda_is_direct_static_raise_to_label(body, label, arity)
    })
}

fn string_switch_cases_contain_nontrivial_static_raise_to_label(
    cases: &[(String, Lambda)],
    label: i32,
    arity: usize,
) -> bool {
    cases.iter().any(|(_, body)| {
        lambda_contains_static_raise_to_label(body, label, arity)
            && !lambda_is_direct_static_raise_to_label(body, label, arity)
    })
}

fn lambda_has_multiple_static_raises_to_label(lam: &Lambda, label: i32, arity: usize) -> bool {
    lambda_static_raise_count_to_label(lam, label, arity) >= 2
}

fn lambda_static_raise_count_to_label(lam: &Lambda, label: i32, arity: usize) -> usize {
    let add_count = |left: usize, right: usize| left.saturating_add(right).min(2);

    match lam {
        Lambda::Lvar(_) | Lambda::LglobalModule(_) | Lambda::Lconst(_) => 0,
        Lambda::Lapply(apply) => apply.ap_args.iter().fold(
            lambda_static_raise_count_to_label(&apply.ap_func, label, arity),
            |count, arg| add_count(count, lambda_static_raise_count_to_label(arg, label, arity)),
        ),
        Lambda::Lfunction(_) => 0,
        Lambda::Llet(_, _, value, body) => add_count(
            lambda_static_raise_count_to_label(value, label, arity),
            lambda_static_raise_count_to_label(body, label, arity),
        ),
        Lambda::Lletrec(bindings, body) => bindings.iter().fold(
            lambda_static_raise_count_to_label(body, label, arity),
            |count, (_, value)| {
                add_count(
                    count,
                    lambda_static_raise_count_to_label(value, label, arity),
                )
            },
        ),
        Lambda::Lprim(info) => info.args.iter().fold(0, |count, arg| {
            add_count(count, lambda_static_raise_count_to_label(arg, label, arity))
        }),
        Lambda::Lswitch(scrut, switch) => {
            let mut count = lambda_static_raise_count_to_label(scrut, label, arity);
            for (_, body) in &switch.sw_consts {
                count = add_count(
                    count,
                    lambda_static_raise_count_to_label(body, label, arity),
                );
            }
            for (_, body) in &switch.sw_blocks {
                count = add_count(
                    count,
                    lambda_static_raise_count_to_label(body, label, arity),
                );
            }
            if let Some(body) = switch.sw_failaction.as_deref() {
                count = add_count(
                    count,
                    lambda_static_raise_count_to_label(body, label, arity),
                );
            }
            count
        }
        Lambda::LstringSwitch(scrut, cases, default) => {
            let mut count = lambda_static_raise_count_to_label(scrut, label, arity);
            for (_, body) in cases {
                count = add_count(
                    count,
                    lambda_static_raise_count_to_label(body, label, arity),
                );
            }
            if let Some(body) = default.as_deref() {
                count = add_count(
                    count,
                    lambda_static_raise_count_to_label(body, label, arity),
                );
            }
            count
        }
        Lambda::LstaticRaise(raise_label, args) => {
            let self_count = usize::from(*raise_label == label && args.len() == arity);
            args.iter().fold(self_count, |count, arg| {
                add_count(count, lambda_static_raise_count_to_label(arg, label, arity))
            })
        }
        Lambda::LstaticCatch(body, (_, _), handler)
        | Lambda::LtryWith(body, _, handler)
        | Lambda::LtryFinally(body, handler) => add_count(
            lambda_static_raise_count_to_label(body, label, arity),
            lambda_static_raise_count_to_label(handler, label, arity),
        ),
        Lambda::Lsequence(first, second) => add_count(
            lambda_static_raise_count_to_label(first, label, arity),
            lambda_static_raise_count_to_label(second, label, arity),
        ),
        Lambda::Lwhile(cond, body) => add_count(
            lambda_static_raise_count_to_label(cond, label, arity),
            lambda_static_raise_count_to_label(body, label, arity),
        ),
        Lambda::Lfor(_, start, finish, _, body) => {
            let count = add_count(
                lambda_static_raise_count_to_label(start, label, arity),
                lambda_static_raise_count_to_label(finish, label, arity),
            );
            add_count(
                count,
                lambda_static_raise_count_to_label(body, label, arity),
            )
        }
        Lambda::Lfor_of(_, iterable, body) | Lambda::Lfor_await_of(_, iterable, body) => add_count(
            lambda_static_raise_count_to_label(iterable, label, arity),
            lambda_static_raise_count_to_label(body, label, arity),
        ),
        Lambda::Lbreak | Lambda::Lcontinue => 0,
        Lambda::Lassign(_, value) => lambda_static_raise_count_to_label(value, label, arity),
        Lambda::LifThenElse(cond, then_, else_) => {
            let count = add_count(
                lambda_static_raise_count_to_label(cond, label, arity),
                lambda_static_raise_count_to_label(then_, label, arity),
            );
            add_count(
                count,
                lambda_static_raise_count_to_label(else_, label, arity),
            )
        }
    }
}

fn lambda_contains_static_raise_to_other_label(lam: &Lambda, label: i32) -> bool {
    match lam {
        Lambda::Lvar(_) | Lambda::LglobalModule(_) | Lambda::Lconst(_) => false,
        Lambda::Lapply(apply) => {
            lambda_contains_static_raise_to_other_label(&apply.ap_func, label)
                || apply
                    .ap_args
                    .iter()
                    .any(|arg| lambda_contains_static_raise_to_other_label(arg, label))
        }
        Lambda::Lfunction(_) => false,
        Lambda::Llet(_, _, value, body) => {
            lambda_contains_static_raise_to_other_label(value, label)
                || lambda_contains_static_raise_to_other_label(body, label)
        }
        Lambda::Lletrec(bindings, body) => {
            bindings
                .iter()
                .any(|(_, value)| lambda_contains_static_raise_to_other_label(value, label))
                || lambda_contains_static_raise_to_other_label(body, label)
        }
        Lambda::Lprim(info) => info
            .args
            .iter()
            .any(|arg| lambda_contains_static_raise_to_other_label(arg, label)),
        Lambda::Lswitch(scrut, switch) => {
            lambda_contains_static_raise_to_other_label(scrut, label)
                || switch
                    .sw_consts
                    .iter()
                    .any(|(_, body)| lambda_contains_static_raise_to_other_label(body, label))
                || switch
                    .sw_blocks
                    .iter()
                    .any(|(_, body)| lambda_contains_static_raise_to_other_label(body, label))
                || switch
                    .sw_failaction
                    .as_deref()
                    .is_some_and(|body| lambda_contains_static_raise_to_other_label(body, label))
        }
        Lambda::LstringSwitch(scrut, cases, default) => {
            lambda_contains_static_raise_to_other_label(scrut, label)
                || cases
                    .iter()
                    .any(|(_, body)| lambda_contains_static_raise_to_other_label(body, label))
                || default
                    .as_deref()
                    .is_some_and(|body| lambda_contains_static_raise_to_other_label(body, label))
        }
        Lambda::LstaticRaise(raise_label, _) => *raise_label != label,
        Lambda::LstaticCatch(body, (_, _), handler)
        | Lambda::LtryWith(body, _, handler)
        | Lambda::LtryFinally(body, handler) => {
            lambda_contains_static_raise_to_other_label(body, label)
                || lambda_contains_static_raise_to_other_label(handler, label)
        }
        Lambda::Lsequence(first, second) => {
            lambda_contains_static_raise_to_other_label(first, label)
                || lambda_contains_static_raise_to_other_label(second, label)
        }
        Lambda::Lwhile(cond, body) => {
            lambda_contains_static_raise_to_other_label(cond, label)
                || lambda_contains_static_raise_to_other_label(body, label)
        }
        Lambda::Lfor(_, start, finish, _, body) => {
            lambda_contains_static_raise_to_other_label(start, label)
                || lambda_contains_static_raise_to_other_label(finish, label)
                || lambda_contains_static_raise_to_other_label(body, label)
        }
        Lambda::Lfor_of(_, iterable, body) | Lambda::Lfor_await_of(_, iterable, body) => {
            lambda_contains_static_raise_to_other_label(iterable, label)
                || lambda_contains_static_raise_to_other_label(body, label)
        }
        Lambda::Lbreak | Lambda::Lcontinue => false,
        Lambda::Lassign(_, value) => lambda_contains_static_raise_to_other_label(value, label),
        Lambda::LifThenElse(cond, then_, else_) => {
            lambda_contains_static_raise_to_other_label(cond, label)
                || lambda_contains_static_raise_to_other_label(then_, label)
                || lambda_contains_static_raise_to_other_label(else_, label)
        }
    }
}

fn runtime_module_id(module_name: &str) -> ModuleId {
    ModuleId {
        id: Ident::create_persistent(module_name),
        kind: Kind::Runtime,
        dynamic_import: false,
    }
}

fn collect_modules_from_block(block: &Block, modules: &mut OcamlModuleSet) {
    for stmt in block {
        collect_modules_from_statement(stmt, modules);
    }
}

fn collect_modules_from_statement(stmt: &Statement, modules: &mut OcamlModuleSet) {
    match &stmt.desc {
        StatementDesc::Block(block) => collect_modules_from_block(block, modules),
        StatementDesc::Variable(decl) => match decl.ident_info.used_stats {
            UsedStats::DeadPure => {}
            UsedStats::DeadNonPure => {
                if let Some(value) = &decl.value
                    && !matches!(value.desc, ExpressionDesc::Var(_))
                {
                    collect_modules_from_expression(value, modules);
                }
            }
            _ => {
                if let Some(value) = &decl.value {
                    collect_modules_from_expression(value, modules);
                }
            }
        },
        StatementDesc::Exp(expr) | StatementDesc::Throw(expr) | StatementDesc::Return(expr) => {
            collect_modules_from_expression(expr, modules)
        }
        StatementDesc::If(cond, then_block, else_block) => {
            collect_modules_from_expression(cond, modules);
            collect_modules_from_block(then_block, modules);
            collect_modules_from_block(else_block, modules);
        }
        StatementDesc::While(_, cond, body) => {
            collect_modules_from_expression(cond, modules);
            collect_modules_from_block(body, modules);
        }
        StatementDesc::ForRange(_, init, finish, _, _, body) => {
            if let Some(init) = init {
                collect_modules_from_expression(init, modules);
            }
            collect_modules_from_expression(finish, modules);
            collect_modules_from_block(body, modules);
        }
        StatementDesc::ForOf(_, _, iterable, body)
        | StatementDesc::ForAwaitOf(_, _, iterable, body) => {
            collect_modules_from_expression(iterable, modules);
            collect_modules_from_block(body, modules);
        }
        StatementDesc::IntSwitch(expr, clauses, default) => {
            collect_modules_from_expression(expr, modules);
            for (_, clause) in clauses {
                collect_modules_from_block(&clause.body, modules);
            }
            if let Some(default) = default {
                collect_modules_from_block(default, modules);
            }
        }
        StatementDesc::StringSwitch(expr, clauses, default) => {
            collect_modules_from_expression(expr, modules);
            for clause in clauses {
                collect_modules_from_block(&clause.clause.body, modules);
            }
            if let Some(default) = default {
                collect_modules_from_block(default, modules);
            }
        }
        StatementDesc::Try(body, handler, finalizer) => {
            collect_modules_from_block(body, modules);
            if let Some((_, handler_block)) = handler {
                collect_modules_from_block(handler_block, modules);
            }
            if let Some(finalizer_block) = finalizer {
                collect_modules_from_block(finalizer_block, modules);
            }
        }
        StatementDesc::Debugger | StatementDesc::Break(_) | StatementDesc::Continue(_) => {}
    }
}

fn collect_modules_from_expression(expr: &Expression, modules: &mut OcamlModuleSet) {
    match &expr.desc {
        ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(module, _)) => {
            if !module.dynamic_import {
                modules.insert((**module).clone());
            }
        }
        ExpressionDesc::Length(inner, _)
        | ExpressionDesc::IsNullOrUndefined(inner)
        | ExpressionDesc::Typeof(inner)
        | ExpressionDesc::JsNot(inner)
        | ExpressionDesc::JsBnot(inner)
        | ExpressionDesc::Await(inner)
        | ExpressionDesc::Spread(inner)
        | ExpressionDesc::RecordRest(_, inner)
        | ExpressionDesc::CamlBlockTag(inner, _) => collect_modules_from_expression(inner, modules),
        ExpressionDesc::OptionalBlock(inner, identity) => {
            if !identity {
                modules.insert(runtime_module_id("Primitive_option"));
            }
            collect_modules_from_expression(inner, modules);
        }
        ExpressionDesc::StringAppend(left, right)
        | ExpressionDesc::Seq(left, right)
        | ExpressionDesc::Bin(_, left, right)
        | ExpressionDesc::ArrayIndex(left, right)
        | ExpressionDesc::In(left, right) => {
            collect_modules_from_expression(left, modules);
            collect_modules_from_expression(right, modules);
        }
        ExpressionDesc::Cond(test, consequent, alternate) => {
            collect_modules_from_expression(test, modules);
            collect_modules_from_expression(consequent, modules);
            collect_modules_from_expression(alternate, modules);
        }
        ExpressionDesc::FlatCall(func, args) => {
            collect_modules_from_expression(func, modules);
            collect_modules_from_expression(args, modules);
        }
        ExpressionDesc::Call(func, args, _) => {
            collect_modules_from_expression(func, modules);
            for arg in args {
                collect_modules_from_expression(arg, modules);
            }
        }
        ExpressionDesc::TaggedTemplate(tag, _, values) => {
            collect_modules_from_expression(tag, modules);
            for value in values {
                collect_modules_from_expression(value, modules);
            }
        }
        ExpressionDesc::InterpolatedTemplate { values, .. } => {
            for value in values {
                collect_modules_from_expression(value, modules);
            }
        }
        ExpressionDesc::StaticIndex(target, _, _) => {
            collect_modules_from_expression(target, modules)
        }
        ExpressionDesc::New(target, args) => {
            collect_modules_from_expression(target, modules);
            if let Some(args) = args {
                for arg in args {
                    collect_modules_from_expression(arg, modules);
                }
            }
        }
        ExpressionDesc::Fun { body, .. } => collect_modules_from_block(body, modules),
        ExpressionDesc::Array(items, _) => {
            for item in items {
                collect_modules_from_expression(item, modules);
            }
        }
        ExpressionDesc::CamlBlock(items, _, _) => {
            for item in items {
                collect_modules_from_expression(item, modules);
            }
        }
        ExpressionDesc::Jsx(jsx) => {
            for value in jsx.expressions() {
                collect_modules_from_expression(value, modules);
            }
        }
        ExpressionDesc::Object(entries) => {
            for entry in entries {
                let (crate::js_ir::ObjectEntry::Property(_, value)
                | crate::js_ir::ObjectEntry::Spread(value)
                | crate::js_ir::ObjectEntry::RecordSpread(value)) = entry;
                collect_modules_from_expression(value, modules);
            }
        }
        ExpressionDesc::Bool(_)
        | ExpressionDesc::Var(crate::js_ir::VIdent::Id(_))
        | ExpressionDesc::Str(_)
        | ExpressionDesc::TemplateLiteral(_)
        | ExpressionDesc::JsonLiteral(_)
        | ExpressionDesc::RawJsCode(_)
        | ExpressionDesc::Number(_)
        | ExpressionDesc::Undefined { .. }
        | ExpressionDesc::Null => {}
    }
}

pub(crate) fn pointer_info_comment_text(comment: Option<&PointerInfo>) -> Option<String> {
    match comment {
        Some(PointerInfo::None) | None => None,
        Some(PointerInfo::ShapeNone) => None,
        Some(PointerInfo::Constructor(tag)) => Some(tag.name.clone()),
        Some(PointerInfo::AssertFalse) => Some("assert_false".to_string()),
        Some(PointerInfo::Some(name)) | Some(PointerInfo::PolyVariant(name)) => Some(name.clone()),
    }
}

#[cfg(test)]
#[path = "lam_compile_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "lam_compile_allocator_tests.rs"]
mod allocator_tests;

#[cfg(test)]
#[path = "lam_compile_input_js_tests.rs"]
mod input_js_tests;

#[path = "lam_compile_indexed.rs"]
mod indexed_consumer;

/// `Lam_coercion.flatten` groups the top-level spine and `Lam_group.nop_cons`
/// drops sequence heads that are a variable, constant or function
/// (compiler/core/lam_coercion.ml:179-194, lam_group.ml:36-39), so such
/// heads are never compiled.
fn drop_toplevel_pure_sequence_heads(lam: Lambda) -> Lambda {
    match lam {
        Lambda::Llet(kind, id, value, body) => Lambda::Llet(
            kind,
            id,
            value,
            Box::new(drop_toplevel_pure_sequence_heads(*body)),
        ),
        Lambda::Lletrec(bindings, body) => {
            Lambda::Lletrec(bindings, Box::new(drop_toplevel_pure_sequence_heads(*body)))
        }
        Lambda::Lsequence(first, second) => {
            let second = drop_toplevel_pure_sequence_heads(*second);
            if matches!(
                *first,
                Lambda::Lvar(_) | Lambda::Lconst(_) | Lambda::Lfunction(_)
            ) {
                second
            } else {
                Lambda::Lsequence(first, Box::new(second))
            }
        }
        lam => lam,
    }
}

/// Whether `compile_prim` (compiler/core/lam_compile.ml:1635-1766) lowers this
/// primitive through `compile_primitive_default`, the only branch that attaches
/// the primitive's source location to the resulting expression.
fn primitive_uses_default_compilation(primitive: &Primitive, args: &[Lambda]) -> bool {
    match primitive {
        // lam_compile.ml:1637-1652: `compile_external_field` on a global
        // module carries no location (hoisted fields are handled earlier).
        Primitive::Pfield(_, crate::lambda::lam_compat::FieldDbgInfo::Module { .. }) => {
            !matches!(args, [Lambda::LglobalModule(_)])
        }
        Primitive::Praise => args.len() != 1,
        Primitive::Psequand | Primitive::Psequor => args.len() != 2,
        Primitive::Pdebugger
        | Primitive::PjsObjectGet(_)
        | Primitive::PjsObjectSet(_)
        | Primitive::PjsFnMethod
        | Primitive::PjsObjectCreate(_) => false,
        _ => true,
    }
}
