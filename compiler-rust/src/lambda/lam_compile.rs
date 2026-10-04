//! Lambda -> JS IR compilation.
//!
//! This module provides a straightforward lowering from Lambda IR into the
//! JavaScript IR used by the Rust compiler backend. The implementation favors
//! clarity over aggressive optimization; it is intended as a correct baseline
//! that can be extended with more advanced codegen passes.

use ahash::{AHashMap, AHashSet};
use ahash::{AHashMap as HashMap, AHashSet as HashSet};
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
    TailMoveInitializerKind, apply_js_shake_pass, keeps_declared_same_name_reusable_export_binding,
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
    ApInfo, Apply, ApplyStatus, FunctionAttribute, InlineAttribute, LFunction, Lambda,
    LambdaSwitch, PrimInfo, SwitchCaseTag, SwitchKey, TagInfo,
};
use crate::location::Location;
use tracing::info_span;

use super::js_exp_make::{
    block_with_return_expr_iife, direct_projection_from_pure_literal, int_expr, int_literal,
    is_optional_block, is_zero_int, js_expr_no_side_effects, js_seq, remove_pure_subexpression,
    to_int32,
};
use super::js_stmt_make::{block_finishes_output, block_terminates, strict_single_return_expr};
use super::lam_coercion::{
    ExtractedExports, block_declares_initialized_ident,
    can_reuse_existing_undefined_export_binding, collect_declared_idents, extract_toplevel_exports,
    insert_rebound_export_before_equivalent_later_binding,
    keeps_declared_same_name_function_export_alias, max_ident_stamp_in_block,
    max_ident_stamp_in_expression, push_effect_expression, push_s_exp,
    resolve_declared_same_name_self_alias_target, resolve_export_aliases,
    reusable_same_name_export_binding,
};
use super::lam_compile_variant::{empty_switch_case_clause, stable_group_switch_cases};

/// Compilation result for an expression: prelude statements plus a value expression.
#[derive(Debug, Clone)]
pub(crate) struct Compiled {
    pub(crate) prelude: Block,
    pub(crate) expr: Expression,
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
        transformed_jsx: bool,
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
    pub(crate) loc: Location,
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
    pub(crate) new_params: HashMap<Ident, Ident>,
    pub(crate) triggered: bool,
}

impl TailLoopState {
    fn new(tail_targets: Vec<Ident>, params: Vec<Ident>) -> Self {
        Self {
            tail_targets,
            params,
            new_params: HashMap::new(),
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
pub(crate) fn call_info_of_apply_status(
    call_transformed_jsx: bool,
    status: ApplyStatus,
) -> CallInfo {
    use crate::js_ir::{CallArity, CallKind};
    match status {
        ApplyStatus::InferFull => CallInfo {
            call_transformed_jsx,
            kind: CallKind::MlCall,
            arity: CallArity::Full,
            ..CallInfo::default()
        },
        ApplyStatus::Na => CallInfo {
            call_transformed_jsx,
            kind: CallKind::MlCall,
            arity: CallArity::Na,
            ..CallInfo::default()
        },
        ApplyStatus::Uncurry => CallInfo {
            call_transformed_jsx,
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
    loop_stack: Vec<crate::lambda::lam_compile_context::LoopFrame>,
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
    if_return_finished: AHashMap<usize, bool>,
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
        HashMap<String, Option<Arc<AHashMap<String, CmjExportConstant>>>>,
    pub(crate) cmj_arity_cache: HashMap<String, Option<Arc<AHashMap<String, CmjExportArity>>>>,
    /// Same intentional cache family as above, but for exported lambda bodies.
    /// Keep this paired with the constant/arity caches so repeated cross-module
    /// inline probes do not re-read the same `.cmj` metadata
    /// (`query_external_id_info` in compiler/core/lam_compile.ml:234-244,
    /// 274-279).
    pub(crate) cmj_lambda_cache: HashMap<String, Option<Arc<AHashMap<String, Lambda>>>>,
    pub(crate) cmj_export_constants: AHashMap<String, CmjExportConstant>,
    /// Non-constant `persistent_closed_lambda` exports recorded for
    /// cross-module inlining (compiler/core/lam_stats_export.ml:53-89).
    pub(crate) cmj_export_lambdas: AHashMap<String, Lambda>,
    pub(crate) cmj_export_arities: AHashMap<String, CmjExportArity>,
    hoisted_functions: Vec<crate::lambda::HoistedFunction>,
    pub(crate) external_module_ids: HashMap<ExternalModuleCacheKey, Ident>,
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
    /// Stack of enclosing loops, innermost first. Each entry is the
    /// loop's lazily-allocated label slot (mirrors OCaml's
    /// `loop_frame`). Pushed when compiling `Lwhile`/`Lfor` bodies and
    /// popped after.
    pub(crate) loop_stack: Vec<crate::lambda::lam_compile_context::LoopFrame>,
    /// Counter shared across the whole compilation unit, used to mint
    /// unique JS labels (`loop_0`, `loop_1`, ...) on demand. Mirrors
    /// OCaml's `loop_label_counter`.
    pub(crate) loop_label_counter: std::rc::Rc<std::cell::Cell<i32>>,
    diagnostic: Option<LambdaDiagnostic>,
}

impl Default for LambdaCompiler {
    fn default() -> Self {
        Self::new()
    }
}

impl LambdaCompiler {
    pub(crate) fn grouped_switch_default<'a>(
        &self,
        saturated: bool,
        failaction: Option<&'a Lambda>,
    ) -> GroupedSwitchDefault<'a> {
        if saturated {
            GroupedSwitchDefault::Complete
        } else if let Some(fallback) = failaction {
            GroupedSwitchDefault::Default(fallback)
        } else {
            GroupedSwitchDefault::NonComplete
        }
    }

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
            .filter(|(_, lam)| {
                default.map_or(true, |default| !super::lambda_eq_approx(lam, default))
            })
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
            .filter(|(_, lam)| {
                default.map_or(true, |default| !super::lambda_eq_approx(lam, default))
            })
            .map(|(tag, lam)| (tag.clone(), *lam))
            .collect()
    }

    /// Create a new compiler.
    pub fn new() -> Self {
        Self::with_generator_and_options(
            LambdaIdGenerator::Owned(IdGenerator::new()),
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
            cmj_constant_cache: HashMap::new(),
            cmj_arity_cache: HashMap::new(),
            cmj_lambda_cache: HashMap::new(),
            cmj_export_constants: AHashMap::new(),
            cmj_export_lambdas: AHashMap::new(),
            cmj_export_arities: AHashMap::new(),
            hoisted_functions: Vec::new(),
            if_return_finished: AHashMap::new(),
            external_module_ids: HashMap::new(),
            dynamic_import_modules: Vec::new(),
            static_handlers: Vec::new(),
            static_jump_handlers: Vec::new(),
            fallthrough_return_handlers: Vec::new(),
            return_unit_stack: Vec::new(),
            try_body_depth: 0,
            switch_depth: 0,
            loop_stack: Vec::new(),
            loop_label_counter: std::rc::Rc::new(std::cell::Cell::new(0)),
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

    pub fn set_hoisted_functions(&mut self, hoisted: Vec<crate::lambda::HoistedFunction>) {
        self.hoisted_functions = hoisted;
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
        self.if_return_finished.clear();
        let simplified_result = crate::timing::measure(
            crate::timing::Phase::LambdaOptimization,
            || {
                let _phase = info_span!("compiler.lambda_simplify").entered();
                let jsx_preserve = self.jsx_preserve;
                let module_path_resolver = self.module_path_resolver.as_ref();
                let cross_module_inline = self.cross_module_inline;
                let mut cmj_lambda_cache: HashMap<String, Option<Arc<AHashMap<String, Lambda>>>> =
                    HashMap::new();
                let mut cmj_arity_cache: HashMap<
                    String,
                    Option<Arc<AHashMap<String, CmjExportArity>>>,
                > = HashMap::new();
                let mut external_inline = |module_id: &Ident, field_name: &str| {
                        if !cross_module_inline {
                            return None;
                        }
                        if !cmj_lambda_cache.contains_key(module_id.name()) {
                            let lambdas = module_path_resolver.as_ref().and_then(|resolver| {
                                resolver.module_cmj_export_lambdas(module_id.name())
                            });
                            cmj_lambda_cache.insert(module_id.name().to_string(), lambdas);
                        }
                        cmj_lambda_cache
                            .get(module_id.name())
                            .and_then(|exports| exports.as_ref())
                            .and_then(|exports| exports.get(field_name).cloned())
                    };
                let mut external_arity = |module_id: &Ident, field_name: &str| {
                        if !cmj_arity_cache.contains_key(module_id.name()) {
                            let arities = module_path_resolver.as_ref().and_then(|resolver| {
                                resolver.module_cmj_export_arities(module_id.name())
                            });
                            cmj_arity_cache.insert(module_id.name().to_string(), arities);
                        }
                        cmj_arity_cache
                            .get(module_id.name())
                            .and_then(|exports| exports.as_ref())
                            .and_then(|exports| exports.get(field_name).cloned())
                            .map(cmj_export_arity_to_external)
                    };
                crate::lambda::lam_compile_main::simplify_for_js_backend_with_external_inline_and_meta_owned(
                    lam,
                    jsx_preserve,
                    &mut external_inline,
                    &mut external_arity,
                )
            },
        );
        let simplified_result = crate::lambda::lam_compile_main::add_hoisted_function_aliases(
            simplified_result,
            &self.hoisted_functions,
        );
        self.cmj_export_constants =
            collect_cmj_export_constants_from_simplified_lambda(&simplified_result.lambda);
        self.cmj_export_lambdas = if self.cross_module_inline {
            collect_cmj_export_lambdas_from_simplified_lambda(&simplified_result.lambda)
        } else {
            AHashMap::new()
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
                    if block_terminates(&block) {
                        for value in &mut exports.values {
                            *value = Expression::undefined(false);
                        }
                    }
                    self.coerce_toplevel_exports_with_name_reservations(&mut block, exports)
                } else {
                    (vec![], vec![])
                }
            };
            // lam_compile_main.ml `declare_undeclared_exports`: when the
            // toplevel always throws, the groups after the throw are dropped
            // and the identifiers they bind are undeclared. Declare each such
            // exported identifier after the throw.
            if block_terminates(&block) {
                let declared: AHashSet<Ident> = block
                    .iter()
                    .filter_map(|stmt| match &stmt.desc {
                        StatementDesc::Variable(decl) => Some(decl.ident.clone()),
                        _ => None,
                    })
                    .collect();
                for id in &exports {
                    if !declared.contains(id) {
                        block.push(Statement::variable(VariableDeclaration {
                            ident: id.clone(),
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

    pub(crate) fn source_loc(&self, loc: &Location) -> Option<Location> {
        (self.source_map_enabled && !loc.loc_ghost && loc.loc_start.cnum >= 0).then_some(*loc)
    }

    pub(crate) fn source_loc_of_lam(&self, lam: &Lambda) -> Option<Location> {
        if !self.source_map_enabled {
            return None;
        }
        fn find(lam: &Lambda) -> Option<Location> {
            match lam {
                Lambda::Lapply(apply) => Some(apply.ap_info.loc),
                Lambda::Lprim(info) => Some(info.loc),
                Lambda::Lfunction(function) => find(&function.body),
                Lambda::Llet(_, _, value, body) => find(value).or_else(|| find(body)),
                Lambda::Lletrec(_, body) | Lambda::Lsequence(_, body) => find(body),
                Lambda::LifThenElse(_, then_, _) => find(then_),
                Lambda::LstaticCatch(body, _, _) | Lambda::LtryWith(body, _, _) => find(body),
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
        find(lam).filter(|loc| !loc.loc_ghost && loc.loc_start.cnum >= 0)
    }

    pub(crate) fn take_cmj_export_constants(&mut self) -> AHashMap<String, CmjExportConstant> {
        std::mem::take(&mut self.cmj_export_constants)
    }

    pub(crate) fn take_cmj_export_lambdas(&mut self) -> AHashMap<String, Lambda> {
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

    pub(crate) fn report_diagnostic(&mut self, loc: &Location, message: &str) {
        if self.diagnostic.is_none() {
            self.diagnostic = Some(LambdaDiagnostic {
                loc: loc.clone(),
                message: message.to_string(),
            });
        }
    }

    fn coerce_toplevel_exports(
        &mut self,
        block: &mut Block,
        extracted: ExtractedExports,
    ) -> Vec<Ident> {
        self.coerce_toplevel_exports_with_name_reservations(block, extracted)
            .0
    }

    fn coerce_toplevel_exports_with_name_reservations(
        &mut self,
        block: &mut Block,
        extracted: ExtractedExports,
    ) -> (Vec<Ident>, Vec<Ident>) {
        let mut max_stamp = max_ident_stamp_in_block(block);
        for export in &extracted.exports {
            max_stamp = max_stamp.max(export.stamp());
        }
        for value in &extracted.values {
            max_stamp = max_stamp.max(max_ident_stamp_in_expression(value));
        }
        self.id_gen.set_current_stamp(max_stamp);

        let mut declared = HashSet::new();
        collect_declared_idents(block, &mut declared);
        let block_ended = block_terminates(block);

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
                    exports.push(export.clone());
                    rebound_exports.push(Statement::variable(VariableDeclaration {
                        ident: export.clone(),
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
                                export.clone()
                            } else {
                                resolve_declared_same_name_self_alias_target(block, export)
                                    .unwrap_or_else(|| export.clone())
                            };
                        if !selected.same(export) {
                            name_reservations.push(export.clone());
                        }
                        exports.push(selected);
                        continue;
                    }
                    if declared.contains(target) {
                        let resolved = resolve_tail_move_replacement_expression(
                            block,
                            &Expression::var(target.clone()),
                            target,
                            false,
                        );
                        let selected = match resolved.desc {
                            ExpressionDesc::Var(VIdent::Id(resolved_target)) => resolved_target,
                            _ => target.clone(),
                        };
                        if !selected.same(export) {
                            name_reservations.push(export.clone());
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
                exports.push(export.clone());
                continue;
            }
            if reusable_export_value_candidate(value) {
                // Same OCaml export fold as above: reusable same-name bindings
                // only arise from variable/module-field export values. See
                // compiler/core/lam_coercion.ml:99-121.
                if let Some((late_value, property)) =
                    move_reused_same_name_export_binding_to_export_tail(block, export, value)
                {
                    exports.push(export.clone());
                    rebound_exports.push(Statement::variable(VariableDeclaration {
                        ident: export.clone(),
                        value: Some(late_value),
                        property,
                        ident_info: IdentInfo::default(),
                    }));
                    continue;
                }
                if keeps_declared_same_name_reusable_export_binding(block, export, value) {
                    exports.push(export.clone());
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
            name_reservations.push(export.clone());
            let property = if matches!(&value.desc, ExpressionDesc::Var(VIdent::Id(_))) {
                LetKind::Alias
            } else {
                LetKind::Strict
            };
            exports.push(rebound.clone());
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
            compiled.expr.source_loc = (self.source_loc(&apply.ap_info.loc)).map(Box::new);
        }
        compiled
    }

    fn compile_apply_call_inner(&mut self, apply: &Apply) -> Compiled {
        if apply.ap_info.status == ApplyStatus::Na {
            if let Lambda::Lapply(inner) = apply.ap_func.as_ref() {
                if inner.ap_info.status == ApplyStatus::Na {
                    let mut ap_info = apply.ap_info.clone();
                    if ap_info.inlined != inner.ap_info.inlined {
                        ap_info.inlined = inner.ap_info.inlined;
                    }

                    let mut args = inner.ap_args.clone();
                    args.extend(apply.ap_args.iter().cloned());
                    let merged = Lambda::apply(
                        (*inner.ap_func).clone(),
                        args,
                        ap_info,
                        apply.ap_transformed_jsx,
                    );
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
                call_info_of_apply_status(apply.ap_transformed_jsx, apply.ap_info.status),
            ),
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

        if !self.cmj_lambda_cache.contains_key(module.id.name()) {
            let lambdas = self
                .module_path_resolver
                .as_ref()
                .and_then(|resolver| resolver.module_cmj_export_lambdas(module.id.name()));
            self.cmj_lambda_cache
                .insert(module.id.name().to_string(), lambdas);
        }

        self.cmj_lambda_cache
            .get(module.id.name())
            .and_then(|exports| exports.as_ref())
            .and_then(|exports| exports.get(field_name).cloned())
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

        if !self.cmj_arity_cache.contains_key(module.id.name()) {
            let arities = self
                .module_path_resolver
                .as_ref()
                .and_then(|resolver| resolver.module_cmj_export_arities(module.id.name()));
            self.cmj_arity_cache
                .insert(module.id.name().to_string(), arities);
        }

        match self
            .cmj_arity_cache
            .get(module.id.name())
            .and_then(|exports| exports.as_ref())
            .and_then(|exports| exports.get(field_name))
        {
            Some(CmjExportArity::Single(arity)) => Some(arity.clone()),
            Some(CmjExportArity::Submodule(_)) | None => None,
        }
    }

    fn module_field_apply_target<'a>(&self, lam: &'a Lambda) -> Option<(ModuleId, &'a str)> {
        let Lambda::Lprim(__prim202) = lam
        else {
            return None;
        };
        let crate::lambda::PrimInfo {
            primitive: Primitive::Pfield(_, crate::lambda::FieldDbgInfo::Module { name }),
            args,
            ..
        } = __prim202.as_ref() else {
            return None;
        };
        let [Lambda::LglobalModule(id)] = args.as_slice() else {
            return None;
        };
        Some((
            ModuleId {
                id: id.clone(),
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
        let NodeSnapshot::Function(_, params, body, attr) = context.store().snapshot(imported)
        else {
            unreachable!("CMJ function import did not produce an indexed function")
        };
        debug_assert!(!attr.async_ && attr.directive.is_none());
        let exports = AHashSet::new();
        let (_, parameter_map) =
            is_closed_with_map_indexed(context.store(), &exports, &params, body);
        let mut diagnostics = IndexedBetaDiagnostics::default();
        let (store, metadata, beta_hash_bucket_count) = context.backend_beta_parts_mut();
        propagate_beta_reduce_with_map_indexed(
            store,
            metadata,
            &parameter_map,
            &params,
            body,
            args,
            &self.id_gen,
            beta_hash_bucket_count,
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
        let (module, field_name, args, info, transformed_jsx) = {
            let NodeSnapshot::Apply(function, args, info, transformed_jsx) =
                context.store().snapshot(application)
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
            let NodeSnapshot::GlobalModule(id) = context.store().snapshot(*base)
            else {
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
                transformed_jsx,
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
            transformed_jsx,
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
                        &*self.id_gen,
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
            ApplyStatus::InferFull | ApplyStatus::Uncurry => Expression::call(
                func,
                args,
                call_info_of_apply_status(apply.ap_transformed_jsx, apply.ap_info.status),
            ),
            // compiler/core/lam_compile.ml:310-316 uses
            // `ident_info.arity`; a known `Single` arity is lowered through
            // `apply_with_arity`, while missing/Submodule arity uses dummy
            // Call_na information.
            ApplyStatus::Na => match known_arity {
                Some(arity) if !arity.is_na() => self.apply_with_arity(func, arity, args),
                _ => Expression::call(func, args, CallInfo::default()),
            },
        };
        Some(Compiled { prelude, expr })
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

        aux(&*self.id_gen, func, arity.extract_arity(), args)
    }

    fn try_statement(&self, body: Block, exn: &Ident, handler: Block) -> Statement {
        Statement::new(StatementDesc::Try(body, Some((exn.clone(), handler)), None))
    }

    fn collect_record_spread_overrides<'a>(
        copy_id: &Ident,
        lam: &'a Lambda,
        overrides: &mut Vec<(&'a SetFieldDbgInfo, &'a Lambda)>,
    ) -> bool {
        match lam {
            Lambda::Lsequence(set, rest) => match set.as_ref() {
                Lambda::Lprim(__prim5) if matches!(__prim5.as_ref(), PrimInfo {
                    primitive: Primitive::Psetfield(_, field_info),
                    args,
                    ..
                } if matches!(args.as_slice(), [Lambda::Lvar(id), _] if id == copy_id)) => {
            let PrimInfo {
                    primitive: Primitive::Psetfield(_, field_info),
                    args,
                    ..
                } = __prim5.as_ref() else {
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
        let Lambda::Lprim(__prim201) = value
        else {
            return None;
        };
        let PrimInfo {
            primitive: Primitive::Pduprecord,
            args,
            ..
        } = __prim201.as_ref() else {
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
            expr: Expression::new(ExpressionDesc::Object(Some(Box::new(init_expr)), props)),
        })
    }

    pub(crate) fn compile_expr(&mut self, lam: &Lambda) -> Compiled {
        match lam {
            Lambda::Lvar(id) => Compiled {
                prelude: vec![],
                expr: Expression::var(id.clone()),
            },
            Lambda::LglobalModule(id) => {
                let module = ModuleId {
                    id: id.clone(),
                    kind: Kind::Ml,
                    dynamic_import: false,
                };
                Compiled {
                    prelude: vec![],
                    expr: Expression::qualified(module, None),
                }
            }
            Lambda::Lconst(cst) => Compiled {
                prelude: vec![],
                expr: Self::compile_constant(cst),
            },
            Lambda::Lapply(apply) => {
                let mut compiled = self.compile_apply_call(apply);
                if compiled.expr.source_loc.is_none() {
                    compiled.expr.source_loc = (self.source_loc(&apply.ap_info.loc)).map(Box::new);
                }
                compiled
            }
            Lambda::Lfunction(func) => {
                if let Some(expr) = self.compile_eta_wrapped_runtime_alias(func) {
                    return Compiled {
                        prelude: vec![],
                        expr,
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
                let expr = Expression::new(ExpressionDesc::Fun {
                    is_method: false,
                    params,
                    body,
                    env: Default::default(),
                    return_unit: func.attr.return_unit,
                    async_: func.attr.async_,
                    directive: (func.attr.directive.clone()).map(Box::new),
                });
                Compiled {
                    prelude: vec![],
                    expr,
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
                    Lambda::Llet(..)
                        | Lambda::Lletrec(..)
                        | Lambda::Lsequence(..)
                ) || matches!(
                    body.as_ref(),
                    Lambda::Lprim(prim)
                        if matches!(prim.primitive, Primitive::Pmakeblock(TagInfo::ModuleExport(_), _))
                );
                let mut prelude = if is_top_level_let {
                    self.with_fresh_loop_label_counter(|this| {
                        this.compile_let_binding(*kind, id, value)
                    })
                } else {
                    self.compile_let_binding(*kind, id, value)
                };
                let body_compiled = self.compile_expr(body);
                if block_terminates(&prelude) {
                    return Compiled {
                        prelude,
                        expr: body_compiled.expr,
                    };
                }
                prelude.extend(body_compiled.prelude);
                Compiled {
                    prelude,
                    expr: body_compiled.expr,
                }
            }
            Lambda::Lletrec(bindings, body) => {
                // Same as Llet: per-Recursive group, OCaml resets
                // `loop_label_counter` (`lam_compile_main.ml:77`).
                let is_top_level = matches!(
                    body.as_ref(),
                    Lambda::Llet(..)
                        | Lambda::Lletrec(..)
                        | Lambda::Lsequence(..)
                ) || matches!(
                    body.as_ref(),
                    Lambda::Lprim(prim)
                        if matches!(prim.primitive, Primitive::Pmakeblock(TagInfo::ModuleExport(_), _))
                );
                let mut prelude = if is_top_level {
                    self.with_fresh_loop_label_counter(|this| {
                        this.compile_recursive_bindings(bindings)
                    })
                } else {
                    self.compile_recursive_bindings(bindings)
                };
                let body_compiled = self.compile_expr(body);
                prelude.extend(body_compiled.prelude);
                Compiled {
                    prelude,
                    expr: body_compiled.expr,
                }
            }
            Lambda::Lprim(info) => {
                if let Some((op, lhs, rhs)) = short_circuit_primitive(&info.primitive, &info.args) {
                    return self.compile_short_circuit_expr(op, lhs, rhs);
                }
                self.compile_primitive(&info.primitive, &info.args, &info.loc)
            }
            Lambda::Lswitch(scrut, switch) => self.compile_switch(scrut, switch),
            Lambda::LstringSwitch(scrut, cases, default) => {
                self.compile_string_switch(scrut, cases, default.as_deref())
            }
            Lambda::LstaticRaise(id, args) => {
                if let Some(prelude) = self.compile_static_raise_jump_block(*id, args) {
                    return Compiled {
                        prelude,
                        expr: Expression::undefined(false),
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
                        ident: result.clone(),
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
                    }
                } else {
                    self.compile_staticcatch_expr(*label, bindings, body, handler)
                }
            }
            Lambda::LtryWith(body, exn, handler) => {
                let result = self.fresh_tmp_ident();
                let mut prelude = vec![Statement::variable(VariableDeclaration {
                    ident: result.clone(),
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
                    }
                } else {
                    let tmp = self.fresh_tmp_ident();
                    let then_block = self.compile_assign_to_target_block(&tmp, then_);
                    let else_block = self.compile_assign_to_target_block(&tmp, else_);
                    prelude.push(Statement::variable(VariableDeclaration {
                        ident: tmp.clone(),
                        value: None,
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    }));
                    prelude.push(Statement::if_(cond_compiled.expr, then_block, else_block));
                    Compiled {
                        prelude,
                        expr: Expression::var(tmp),
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
                    Lambda::Llet(..)
                        | Lambda::Lletrec(..)
                        | Lambda::Lsequence(..)
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
                // OCaml's Lbreak / Lcontinue compile to `Js_output.make ...
                // ~output_finished:True` (compiler/core/lam_compile.ml:1928,
                // 1943). `Js_output.append_output` then drops the tail's
                // contribution when the head is finished. Mirror that here:
                // when the sequence head is an exit terminator, skip typing
                // the tail entirely — its statements are unreachable.
                if lambda_is_unconditional_exit(a) {
                    return first;
                }
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
                let frame = self.push_loop();
                let body_block = self.compile_block(body);
                self.pop_loop();
                let label = frame.label();
                Compiled {
                    prelude: vec![Statement::while_with_label(label, cond_expr, body_block)],
                    expr: Expression::undefined(false),
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
                let frame = self
                    .loop_stack
                    .first()
                    .cloned()
                    .expect("Lbreak outside a loop — typecore should reject this");
                let stmt = if self.switch_depth > 0 {
                    let label = self.ensure_loop_label(&frame);
                    Statement::break_label(Some(label))
                } else {
                    Statement::break_()
                };
                Compiled {
                    prelude: vec![stmt],
                    expr: Expression::undefined(false),
                }
            }
            Lambda::Lcontinue => {
                let frame = self
                    .loop_stack
                    .first()
                    .cloned()
                    .expect("Lcontinue outside a loop — typecore should reject this");
                let stmt = if self.switch_depth > 0 {
                    let label = self.ensure_loop_label(&frame);
                    Statement::continue_label(Some(label))
                } else {
                    Statement::continue_()
                };
                Compiled {
                    prelude: vec![stmt],
                    expr: Expression::undefined(false),
                }
            }
            Lambda::Lassign(id, value) => {
                let compiled = self.compile_expr(value);
                let mut prelude = compiled.prelude;
                if !block_terminates(&prelude) {
                    prelude.push(Statement::exp(Expression::bin(
                        BinOp::Eq,
                        Expression::var(id.clone()),
                        compiled.expr,
                    )));
                }
                Compiled {
                    prelude,
                    expr: Expression::undefined(false),
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
        let saved = std::mem::replace(
            &mut self.loop_label_counter,
            std::rc::Rc::new(std::cell::Cell::new(0)),
        );
        let result = f(self);
        self.loop_label_counter = saved;
        result
    }

    /// Push a fresh loop frame onto the stack (mirrors OCaml's
    /// `push_loop`). The returned frame can be queried for a label
    /// after the body has been compiled — `label()` returns `Some` only
    /// if [`Self::ensure_loop_label`] was called from inside the body.
    pub(crate) fn push_loop(&mut self) -> crate::lambda::lam_compile_context::LoopFrame {
        let frame = crate::lambda::lam_compile_context::LoopFrame::default();
        self.loop_stack.insert(0, frame.clone());
        frame
    }

    /// Pop the innermost loop frame.
    pub(crate) fn pop_loop(&mut self) {
        self.loop_stack.remove(0);
    }

    /// Lazily allocate a JS label for `frame`. Mirrors OCaml's
    /// `ensure_loop_label`. Idempotent: subsequent calls return the
    /// same label.
    pub(crate) fn ensure_loop_label(
        &self,
        frame: &crate::lambda::lam_compile_context::LoopFrame,
    ) -> String {
        if let Some(existing) = frame.label() {
            return existing;
        }
        let next_id = self.loop_label_counter.get();
        self.loop_label_counter.set(next_id + 1);
        let label = format!("loop_{next_id}");
        // We can mutate the frame's label slot through the shared Rc.
        frame.set_label(label.clone());
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
        let frame = self.push_loop();
        let body_block = self.compile_block(body);
        self.pop_loop();
        let loop_label = frame.label();

        let mut prelude = start_compiled.prelude;
        if block_terminates(&prelude) {
            return Compiled {
                prelude,
                expr: Expression::undefined(false),
            };
        }

        let push_loop = |block: &mut Block, init: Option<Expression>, finish: Expression| {
            block.push(Statement::for_range(
                loop_label.clone(),
                init,
                finish,
                var.clone(),
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
            if block_terminates(&prelude) {
                return Compiled {
                    prelude,
                    expr: Expression::undefined(false),
                };
            }
            push_loop(
                &mut prelude,
                Some(start_compiled.expr),
                finish_compiled.expr,
            );
        } else {
            prelude.push(Statement::variable(VariableDeclaration {
                ident: var.clone(),
                value: Some(start_compiled.expr),
                property: LetKind::Variable,
                ident_info: IdentInfo::default(),
            }));
            prelude.extend(finish_compiled.prelude);
            if block_terminates(&prelude) {
                return Compiled {
                    prelude,
                    expr: Expression::undefined(false),
                };
            }
            push_loop(&mut prelude, None, finish_compiled.expr);
        }

        Compiled {
            prelude,
            expr: Expression::undefined(false),
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
        if block_terminates(&prelude) {
            return Compiled {
                prelude,
                expr: Expression::undefined(false),
            };
        }

        // Match OCaml: when the loop variable is not actually used by the
        // body, emit a fresh placeholder so the source name doesn't leak.
        let body_fvs = crate::lambda::lam_free_variables::free_variables(body);
        let emitted_id = if body_fvs.contains(var) {
            var.clone()
        } else if await_kw {
            self.fresh_ident("_for_await_of")
        } else {
            self.fresh_ident("_for_of")
        };

        let frame = self.push_loop();
        let body_block = self.compile_block(body);
        self.pop_loop();
        let label = frame.label();

        let stmt = if await_kw {
            Statement::for_await_of(label, emitted_id, iterable_compiled.expr, body_block)
        } else {
            Statement::for_of(label, emitted_id, iterable_compiled.expr, body_block)
        };
        prelude.push(stmt);

        Compiled {
            prelude,
            expr: Expression::undefined(false),
        }
    }

    fn compile_recursive_bindings(&mut self, bindings: &[(Ident, Lambda)]) -> Block {
        let dependencies = recursive_binding_dependencies(bindings);
        let mut block = vec![];

        for group in recursive_binding_groups(bindings, &dependencies) {
            if let [index] = group.as_slice() {
                if !dependencies[*index].contains(index) {
                    let (id, expr) = &bindings[*index];
                    // OCaml's `compile_recursive_let` (lam_compile.ml:380-486)
                    // routes every non-self-referencing binding through
                    // `Declare(Alias, id)`. Using `Strict` here breaks the
                    // `js_pass_flatten_and_mark_dead` skip for all-deep-constant
                    // alias bindings (lam_pass_lets_dce.ml + the implicit
                    // skip behind the Variable arm).
                    block.extend(self.compile_let_binding(LetKind::Alias, id, expr));
                    continue;
                }
            }

            let recursive_functions = recursive_function_bindings_in_group(bindings, &group);
            let recursive_function_tail_targets = direct_recursive_function_tail_targets_with_group(
                bindings,
                &group,
                &recursive_functions,
            );
            let recursive_function_ids: HashSet<_> =
                recursive_function_tail_targets.keys().cloned().collect();
            let mut declarations = vec![];
            let mut effects = vec![];

            for &index in &group {
                let (id, expr) = &bindings[index];
                let (binding_decls, binding_effects) = self.compile_recursive_binding(
                    id,
                    expr,
                    bindings,
                    &group,
                    recursive_function_tail_targets
                        .get(id)
                        .map(Vec::as_slice)
                        .unwrap_or(&[]),
                    &recursive_functions,
                    &recursive_function_ids,
                );
                declarations.extend(binding_decls);
                effects.extend(binding_effects);
            }

            declarations.extend(effects);
            block.extend(declarations);
        }

        block
    }

    fn compile_recursive_binding(
        &mut self,
        id: &Ident,
        expr: &Lambda,
        all_bindings: &[(Ident, Lambda)],
        group: &[usize],
        tail_targets: &[Ident],
        recursive_functions: &HashMap<Ident, LFunction>,
        recursive_function_ids: &HashSet<Ident>,
    ) -> (Block, Block) {
        if let Some(func) = recursive_function_binding_value(expr) {
            return (
                vec![],
                vec![Statement::variable(VariableDeclaration {
                    ident: id.clone(),
                    value: Some(self.compile_recursive_function_expr(id, &func, tail_targets)),
                    property: LetKind::Alias,
                    ident_info: IdentInfo::default(),
                })],
            );
        }

        if let Some(target) = recursive_function_binding_alias_target(expr, recursive_functions) {
            if recursive_function_ids
                .iter()
                .any(|function_id| target.same(function_id))
            {
                return (
                    vec![],
                    vec![Statement::variable(VariableDeclaration {
                        ident: id.clone(),
                        value: Some(Expression::var(target)),
                        property: LetKind::Alias,
                        ident_info: IdentInfo::default(),
                    })],
                );
            }
        }

        if group.len() == 1 {
            if let Some(block) =
                self.try_compile_recursive_singleton_binding_without_placeholder(id, expr)
            {
                return (vec![], block);
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
                let compiled = self.compile_expr(expr);
                let mut effects = compiled.prelude;
                if !block_terminates(&effects) {
                    effects.push(Statement::variable(VariableDeclaration {
                        ident: id.clone(),
                        value: Some(compiled.expr),
                        property: LetKind::Alias,
                        ident_info: IdentInfo::default(),
                    }));
                }
                (vec![], effects)
            }
            Lambda::Lprim(info) if matches!(info.primitive, Primitive::Pmakeblock(_, _)) => {
                if let Some(effects) =
                    self.compile_recursive_self_binding_makeblock(id, info, all_bindings, group)
                {
                    return (vec![], effects);
                }

                let tag_info = match &info.primitive {
                    Primitive::Pmakeblock(tag_info, _) => tag_info,
                    _ => unreachable!("guard must preserve Pmakeblock"),
                };
                let compiled = self.compile_expr(expr);
                let mut effects = compiled.prelude;
                if !block_terminates(&effects) {
                    effects.push(Statement::exp(self.runtime_call_expr(
                        "Primitive_object",
                        "updateDummy",
                        vec![Expression::var(id.clone()), compiled.expr],
                    )));
                }
                (
                    vec![Statement::variable(VariableDeclaration {
                        ident: id.clone(),
                        value: Some(Self::recursive_dummy_object_expr(tag_info)),
                        property: LetKind::Variable,
                        ident_info: IdentInfo::default(),
                    })],
                    effects,
                )
            }
            _ => {
                let compiled = self.compile_expr(expr);
                let mut effects = compiled.prelude;
                if block_terminates(&effects) {
                    return (
                        vec![Statement::variable(VariableDeclaration {
                            ident: id.clone(),
                            value: None,
                            property: LetKind::Strict,
                            ident_info: IdentInfo::default(),
                        })],
                        effects,
                    );
                }
                // OCaml `compile_recursive_let`'s catch-all compiles directly
                // under `Declare (Alias, id)` (`lam_compile.ml:552-553`).  The
                // value's prelude therefore precedes a normal declaration; it
                // does not introduce a placeholder plus a later assignment.
                effects.push(Statement::variable(VariableDeclaration {
                    ident: id.clone(),
                    value: Some(compiled.expr),
                    property: LetKind::Alias,
                    ident_info: IdentInfo::default(),
                }));
                (vec![], effects)
            }
        }
    }

    fn try_compile_recursive_singleton_binding_without_placeholder(
        &mut self,
        id: &Ident,
        expr: &Lambda,
    ) -> Option<Block> {
        if !matches!(expr, Lambda::Llet(..)) {
            return None;
        }

        let block = self.compile_let_binding(LetKind::Alias, id, expr);
        if block_declares_initialized_ident(&block, id) {
            Some(block)
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
            ident: id.clone(),
            value: Some(Self::recursive_dummy_object_expr(tag_info)),
            property: LetKind::Variable,
            ident_info: IdentInfo::default(),
        })];

        for (index, arg) in info.args.iter().enumerate() {
            let field_info = Self::recursive_self_binding_field_info(tag_info, index)?;
            let value = match arg {
                Lambda::Lvar(binding) => Expression::var(binding.clone()),
                Lambda::Lconst(constant) => Self::compile_constant(constant),
                _ => return None,
            };
            block.push(Statement::exp(self.compile_set_field(
                index as i32,
                &field_info,
                &Expression::var(id.clone()),
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
            | TagInfo::RecordExt { .. } => Expression::new(ExpressionDesc::Object(None, vec![])),
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
        match value {
            Lambda::Llet(inner_kind, inner_id, inner_value, body) => {
                let mut block = self.compile_let_binding(*inner_kind, inner_id, inner_value);
                if block_terminates(&block) {
                    return block;
                }
                block.extend(self.compile_let_binding(kind, id, body));
                block
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
                let mut block = vec![Statement::variable(VariableDeclaration {
                    ident: id.clone(),
                    value: None,
                    property: kind,
                    ident_info: IdentInfo::default(),
                })];
                let (handlers, flat_body) = flatten_nested_caches(*label, bindings, body, handler);
                if handlers.len() > 1 {
                    // lam_compile.ml:935 + 989-996 — `Declare (kind, id)`
                    // with flattened multi-handler code_table.
                    block.extend(
                        self.compile_multi_staticcatch_assignment_block(id, &handlers, flat_body),
                    );
                } else {
                    block.extend(
                        self.compile_staticcatch_assignment_block(
                            id, *label, bindings, body, handler,
                        ),
                    );
                }
                block
            }
            Lambda::LifThenElse(cond, then_, else_) => {
                self.compile_if_binding_block(kind, id, cond, then_, else_)
            }
            Lambda::LtryWith(body, exn, handler) => {
                let body_block = self.compile_assign_to_target_block(id, body);
                let handler_block = self.compile_assign_to_target_block(id, handler);
                vec![
                    Statement::variable(VariableDeclaration {
                        ident: id.clone(),
                        value: None,
                        property: kind,
                        ident_info: IdentInfo::default(),
                    }),
                    self.try_statement(body_block, exn, handler_block),
                ]
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
                let mut block = self.compile_effect_block(first);
                if lambda_is_unconditional_exit(first) || block_finishes_output(&block) {
                    return block;
                }
                block.extend(self.compile_let_binding(kind, id, second));
                block
            }
            Lambda::Lswitch(scrut, switch) => {
                self.compile_switch_binding_block(kind, id, scrut, switch)
            }
            Lambda::LstringSwitch(scrut, cases, default) => {
                self.compile_string_switch_binding_block(kind, id, scrut, cases, default.as_deref())
            }
            Lambda::Lprim(info) => {
                if let Some((op, lhs, rhs)) = short_circuit_primitive(&info.primitive, &info.args) {
                    return self.compile_short_circuit_binding_block(kind, id, op, lhs, rhs);
                }
                let value_compiled = self.compile_expr(value);
                let mut block = value_compiled.prelude;
                if block_terminates(&block) {
                    return block;
                }
                block.push(Statement::variable(VariableDeclaration {
                    ident: id.clone(),
                    value: Some(value_compiled.expr),
                    property: kind,
                    ident_info: IdentInfo::default(),
                }));
                block
            }
            _ => {
                let value_compiled = self.compile_expr(value);
                let mut block = value_compiled.prelude;
                if block_terminates(&block) {
                    return block;
                }
                block.push(Statement::variable(VariableDeclaration {
                    ident: id.clone(),
                    value: Some(value_compiled.expr),
                    property: kind,
                    ident_info: IdentInfo::default(),
                }));
                block
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
        let mut block = unnest_block(self.compile_effect_block_inner(lam));
        let source_loc = self.source_loc_of_lam(lam);
        if let Some(first) = block.first_mut()
            && first.source_loc.is_none()
        {
            first.source_loc = (source_loc).map(Box::new);
        }
        block
    }

    fn compile_effect_block_inner(&mut self, lam: &Lambda) -> Block {
        match lam {
            Lambda::Llet(kind, id, value, body) => {
                if let Some(compiled) = self.try_compile_record_spread(id, value, body) {
                    let mut block = compiled.prelude;
                    push_effect_expression(&mut block, compiled.expr);
                    return block;
                }

                let mut block = self.compile_let_binding(*kind, id, value);
                // Mirror OCaml's output_finished:True from Lbreak/Lcontinue:
                // if the binding's RHS is an unconditional exit, the body is
                // unreachable and must not be emitted. block_finishes_output
                // only recognises Return/Throw (Break/Continue inside a switch
                // case must not terminate the enclosing block), so check the
                // Lambda form directly.
                if lambda_is_unconditional_exit(value) || block_finishes_output(&block) {
                    return block;
                }
                block.extend(self.compile_effect_block(body));
                block
            }
            Lambda::Lletrec(bindings, body) => {
                // Mirror OCaml's Lletrec arm (lam_compile.ml:1770-1783): emit
                // bindings then compile body in the SAME continuation. The
                // catch-all `_ => compile_expr(lam)` would force the body
                // through `NeedValue`, losing the effect/tail context.
                let mut block = self.compile_recursive_bindings(bindings);
                if block_finishes_output(&block) {
                    return block;
                }
                block.extend(self.compile_effect_block(body));
                block
            }
            Lambda::LifThenElse(cond, then_, else_) => {
                self.compile_if_effect_block(cond, then_, else_)
            }
            Lambda::Lsequence(first, second) => {
                let mut block = self.compile_effect_block(first);
                if lambda_is_unconditional_exit(first) || block_finishes_output(&block) {
                    return block;
                }
                block.extend(self.compile_effect_block(second));
                block
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
                    self.compile_multi_staticcatch_effect_block(&handlers, flat_body)
                } else {
                    self.compile_staticcatch_effect_block(*label, bindings, body, handler)
                }
            }
            Lambda::LtryWith(body, exn, handler) => {
                let body_block = self.compile_effect_block(body);
                let handler_block = self.compile_effect_block(handler);
                vec![self.try_statement(body_block, exn, handler_block)]
            }
            Lambda::Lswitch(scrut, switch) => self.compile_switch_effect_block(scrut, switch),
            Lambda::LstringSwitch(scrut, cases, default) => {
                self.compile_string_switch_effect_block(scrut, cases, default.as_deref())
            }
            _ => {
                let compiled = self.compile_expr(lam);
                self.compiled_to_effect_block(compiled)
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
                ident: id.clone(),
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
            ident: id.clone(),
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
            return Compiled { prelude, expr };
        }

        let tmp = self.fresh_tmp_ident();
        prelude.push(Statement::variable(VariableDeclaration {
            ident: tmp.clone(),
            value: Some(op.default_expr()),
            property: LetKind::Strict,
            ident_info: IdentInfo::default(),
        }));

        let mut then_block = rhs_compiled.prelude;
        if !block_terminates(&then_block) {
            then_block.push(Statement::exp(Expression::bin(
                BinOp::Eq,
                Expression::var(tmp.clone()),
                rhs_compiled.expr,
            )));
        }

        let test = op.test_expr(lhs_compiled.expr);
        prelude.push(Statement::if_(test, then_block, vec![]));

        Compiled {
            prelude,
            expr: Expression::var(tmp),
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
                ident: id.clone(),
                value: Some(expr),
                property: kind,
                ident_info: IdentInfo::default(),
            }));
            return block;
        }

        block.push(Statement::variable(VariableDeclaration {
            ident: id.clone(),
            value: Some(op.default_expr()),
            property: kind,
            ident_info: IdentInfo::default(),
        }));

        let mut then_block = rhs_compiled.prelude;
        if !block_terminates(&then_block) {
            then_block.push(self.result_assignment(id, rhs_compiled.expr));
        }

        block.push(Statement::if_(
            op.test_expr(lhs_compiled.expr),
            then_block,
            vec![],
        ));
        block
    }

    fn compile_short_circuit_return_block(
        &mut self,
        op: ShortCircuitOp,
        lhs: &Lambda,
        rhs: &Lambda,
    ) -> Block {
        let default = op.default_lambda();
        match op {
            ShortCircuitOp::And => self.compile_if_return_block(lhs, rhs, &default),
            ShortCircuitOp::Or => self.compile_if_return_block(lhs, &default, rhs),
        }
    }

    pub(crate) fn compile_return_block(&mut self, lam: &Lambda) -> Block {
        // Mirror OCaml's invariant that consumers go through
        // `Js_output.output_as_block` (js_output.ml:82-86) which calls
        // `unnest_block` on `compile_lambda` results.
        unnest_block(self.compile_return_block_inner(lam))
    }

    fn compile_return_block_inner(&mut self, lam: &Lambda) -> Block {
        match lam {
            Lambda::Llet(kind, id, value, body) => {
                if let Some(compiled) = self.try_compile_record_spread(id, value, body) {
                    let mut block = compiled.prelude;
                    block.push(Statement::return_(compiled.expr));
                    return block;
                }

                let mut block = self.compile_let_binding(*kind, id, value);
                if block_finishes_output(&block) {
                    return block;
                }
                block.extend(self.compile_return_block(body));
                block
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
                let mut block = self.compile_recursive_bindings(bindings);
                if block_finishes_output(&block) {
                    return block;
                }
                block.extend(self.compile_return_block(body));
                block
            }
            Lambda::Lapply(apply) => {
                let compiled = self.compile_apply_call(apply);
                let mut block = compiled.prelude;
                let mut statement = Statement::return_(compiled.expr);
                statement.source_loc = (self.source_loc(&apply.ap_info.loc)).map(Box::new);
                block.push(statement);
                block
            }
            Lambda::LifThenElse(cond, then_, else_) => self
                .compile_if_unit_return_tail_block(cond, then_, else_)
                .unwrap_or_else(|| self.compile_if_return_block(cond, then_, else_)),
            Lambda::Lprim(info) => {
                if let Some((op, lhs, rhs)) = short_circuit_primitive(&info.primitive, &info.args) {
                    return self.compile_short_circuit_return_block(op, lhs, rhs);
                }
                let compiled = self.compile_expr(lam);
                let mut block = compiled.prelude;
                if !block_terminates(&block) {
                    block.push(Statement::return_(compiled.expr));
                }
                block
            }
            Lambda::Lsequence(first, second) => {
                let mut block = self.compile_effect_block(first);
                if block_finishes_output(&block) {
                    return block;
                }
                block.extend(self.compile_return_block(second));
                block
            }
            Lambda::LstaticRaise(id, args) => {
                if let Some(block) = self.compile_static_raise_jump_block(*id, args) {
                    return block;
                }
                if let Some(block) = self.compile_fallthrough_static_raise_return_block(*id, args) {
                    return block;
                }
                if let Some(handler) = self.resolve_static_raise(*id, args) {
                    return self.compile_return_block(&handler);
                }
                let compiled = self.compile_expr(lam);
                let mut block = compiled.prelude;
                if !block_terminates(&block) {
                    block.push(Statement::return_(compiled.expr));
                }
                block
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
                if crate::debug_flags::debug_staticcatch_return() {
                    eprintln!(
                        "[staticcatch-return] label={label} path=flatten-multi count={} bindings={} body_kind={} handler_kind={}",
                        handlers.len(),
                        bindings.len(),
                        staticcatch_debug_kind(body),
                        staticcatch_debug_kind(handler),
                    );
                }
                self.compile_multi_staticcatch_return_block(&handlers, flat_body)
            }
            Lambda::LstaticCatch(body, (label, bindings), handler)
                if self.uses_fallthrough_staticcatch_return(body, *label, bindings, handler) =>
            {
                if crate::debug_flags::debug_staticcatch_return() {
                    eprintln!(
                        "[staticcatch-return] label={label} path=fallthrough bindings={} body_kind={} handler_kind={}",
                        bindings.len(),
                        staticcatch_debug_kind(body),
                        staticcatch_debug_kind(handler),
                    );
                }
                self.compile_fallthrough_staticcatch_return_block(*label, bindings, body, handler)
            }
            Lambda::LstaticCatch(body, (label, bindings), handler)
                if self.uses_pseudo_fallthrough_staticcatch_return(
                    body, *label, bindings, handler,
                ) =>
            {
                if crate::debug_flags::debug_staticcatch_return() {
                    eprintln!(
                        "[staticcatch-return] label={label} path=pseudo-fallthrough bindings={} body_kind={} handler_kind={}",
                        bindings.len(),
                        staticcatch_debug_kind(body),
                        staticcatch_debug_kind(handler),
                    );
                }
                self.compile_fallthrough_staticcatch_return_block(*label, bindings, body, handler)
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
                if crate::debug_flags::debug_staticcatch_return() {
                    eprintln!(
                        "[staticcatch-return] label={label} path=nested-fallthrough bindings={} body_kind={} handler_kind={}",
                        bindings.len(),
                        staticcatch_debug_kind(body),
                        staticcatch_debug_kind(handler),
                    );
                }
                self.compile_fallthrough_staticcatch_return_block(*label, bindings, body, handler)
            }
            Lambda::LstaticCatch(body, (label, bindings), handler) => {
                let requires_explicit_jump = (self.return_unit_stack.last().copied() == Some(true)
                    && !bindings.is_empty())
                    || self.try_body_depth > 0
                    || self
                        .return_staticcatch_requires_explicit_jump(*label, bindings, body, handler);
                if crate::debug_flags::debug_staticcatch_return() {
                    eprintln!(
                        "[staticcatch-return] label={label} path={} bindings={} body_kind={} handler_kind={}",
                        if requires_explicit_jump {
                            "explicit-jump"
                        } else {
                            "inline-handler"
                        },
                        bindings.len(),
                        staticcatch_debug_kind(body),
                        staticcatch_debug_kind(handler),
                    );
                }
                if requires_explicit_jump {
                    self.compile_staticcatch_return_block(*label, bindings, body, handler)
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
                    self.compile_fallthrough_staticcatch_return_block(
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
                    self.compile_staticcatch_return_block(*label, bindings, body, handler)
                } else {
                    self.with_static_handler(*label, bindings, handler, |this| {
                        this.compile_return_block(body)
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
                vec![self.try_statement(body_block, exn, handler_block)]
            }
            Lambda::Lswitch(scrut, switch) => self.compile_switch_return_block(scrut, switch),
            Lambda::LstringSwitch(scrut, cases, default) => {
                self.compile_string_switch_return_block(scrut, cases, default.as_deref())
            }
            _ => {
                let compiled = self.compile_expr(lam);
                let mut block = compiled.prelude;
                if !block_terminates(&block) {
                    block.push(Statement::return_(compiled.expr));
                }
                block
            }
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
            Lambda::LtryWith(body, _, handler) => {
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
            // OCaml's `S.if_ cond [] []` reduces to `S.exp cond`
            // (js_stmt_make.ml:242 + 45-53), which keeps pure comparisons like
            // `tmp === null` as a bare `Exp` statement.
            push_s_exp(&mut block, cond_compiled.expr);
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

    fn compile_fallthrough_static_raise_return_block(
        &mut self,
        label: i32,
        args: &[Lambda],
    ) -> Option<Block> {
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

        let mut block = Vec::new();
        for (arg, binding) in args.iter().zip(&bindings) {
            if matches!(arg, Lambda::Lvar(id) if id.same(binding)) {
                continue;
            }
            block.extend(self.compile_assign_to_target_block(binding, arg));
        }
        Some(block)
    }

    fn compile_fallthrough_staticcatch_return_block(
        &mut self,
        label: i32,
        bindings: &[Ident],
        body: &Lambda,
        handler: &Lambda,
    ) -> Block {
        let mut block: Block = bindings
            .iter()
            .map(|binding| {
                Statement::variable(VariableDeclaration {
                    ident: binding.clone(),
                    value: None,
                    property: LetKind::Variable,
                    ident_info: IdentInfo::default(),
                })
            })
            .collect();
        let body_block = self.with_fallthrough_return_handler(label, bindings, |this| {
            this.compile_return_block(body)
        });
        block.extend(body_block);
        if !block_terminates(&block) {
            block.extend(self.compile_return_block(handler));
        }
        block
    }

    fn compile_fallthrough_staticcatch_tail_loop_return_block(
        &mut self,
        label: i32,
        bindings: &[Ident],
        body: &Lambda,
        handler: &Lambda,
        tail_loop: &mut TailLoopState,
    ) -> Block {
        let mut block: Block = bindings
            .iter()
            .map(|binding| {
                Statement::variable(VariableDeclaration {
                    ident: binding.clone(),
                    value: None,
                    property: LetKind::Variable,
                    ident_info: IdentInfo::default(),
                })
            })
            .collect();
        let body_block = self.with_fallthrough_return_handler(label, bindings, |this| {
            this.compile_tail_loop_return_block(body, tail_loop)
        });
        block.extend(body_block);
        if !block_terminates(&block) {
            block.extend(self.compile_tail_loop_return_block(handler, tail_loop));
        }
        block
    }

    /// Whether the current return continuation is no longer OCaml's
    /// `Tail_with_name {in_staticcatch = false}` (lam_compile.ml:1022-1028).
    pub(crate) fn in_staticcatch_like_ocaml(&self) -> bool {
        self.try_body_depth > 0
            || !self.fallthrough_return_handlers.is_empty()
            || !self.static_handlers.is_empty()
            || !self.static_jump_handlers.is_empty()
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

    pub(crate) fn grouped_return_string_clauses<'a, T: Clone>(
        &mut self,
        grouped_cases: Vec<(T, &'a Lambda, bool)>,
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
            let compiled_body = self.compile_return_block(body);
            let group_falls_through = compiled_body.is_empty();
            // Mirror OCaml's `compile_general_cases`: it feeds each last
            // grouped case through `Js_output.to_break_block`, then gates the
            // break bit with `Lam_exit_code.has_exit` in return continuation
            // (compiler/core/lam_compile.ml:613-624;
            // compiler/core/js_output.ml:88-100). When a case resolves to a
            // fallthrough static-raise handler, the empty body still needs a
            // `break;` so the appended handler runs once after the switch.
            let should_break = self.return_case_needs_break_like_ocaml(body, &compiled_body);

            for (tag, _, _) in &grouped_cases[group_start..group_end] {
                clauses.push((
                    to_tag(tag.clone()),
                    empty_switch_case_clause(),
                    group_falls_through,
                ));
            }
            clauses.push((
                to_tag(grouped_cases[group_end].0.clone()),
                CaseClause {
                    source_loc: None,
                    body: compiled_body,
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

    pub(crate) fn compile_hoisted_named_string_return_tail(&mut self, body: &Lambda) -> Block {
        self.compile_hoisted_static_raise_chain_return_tail(body)
            .unwrap_or_else(|| self.compile_return_block(body))
    }

    fn compile_hoisted_static_raise_chain_return_tail(&mut self, lam: &Lambda) -> Option<Block> {
        match lam {
            Lambda::Llet(kind, id, value, body) => {
                let mut block = self.compile_let_binding(*kind, id, value);
                if block_finishes_output(&block) {
                    return Some(block);
                }
                block.extend(self.compile_hoisted_static_raise_chain_return_tail(body)?);
                Some(block)
            }
            Lambda::Lsequence(first, second) => {
                let mut block = self.compile_effect_block(first);
                if block_finishes_output(&block) {
                    return Some(block);
                }
                block.extend(self.compile_hoisted_static_raise_chain_return_tail(second)?);
                Some(block)
            }
            Lambda::LstaticRaise(label, args) => {
                let handler_index = self.static_handlers.iter().rposition(|handler| {
                    handler.label == *label && handler.bindings.len() == args.len()
                })?;
                let handler = self.static_handlers[handler_index].clone();
                let removed = self.static_handlers.remove(handler_index);

                let mut block = Vec::new();
                for (arg, binding) in args.iter().zip(&handler.bindings) {
                    if matches!(arg, Lambda::Lvar(id) if id.same(binding)) {
                        continue;
                    }
                    block.extend(self.compile_let_binding(LetKind::Strict, binding, arg));
                    if block_finishes_output(&block) {
                        self.static_handlers.insert(handler_index, removed);
                        return Some(block);
                    }
                }

                block.extend(
                    self.compile_hoisted_static_raise_chain_return_tail(&handler.handler)
                        .unwrap_or_else(|| self.compile_return_block(&handler.handler)),
                );
                self.static_handlers.insert(handler_index, removed);
                Some(block)
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
            return self.compile_expr(&Lambda::Lfunction(Box::new(func.clone()))).expr;
        }

        let params = if func.attr.one_unit_arg {
            vec![]
        } else {
            func.params.clone()
        };
        let mut tail_loop = TailLoopState::new(tail_targets.to_vec(), params.clone());
        let body = self.compile_tail_loop_return_block(&func.body, &mut tail_loop);

        if !tail_loop.triggered {
            return self.compile_expr(&Lambda::Lfunction(Box::new(func.clone()))).expr;
        }

        let lowered_params = params
            .iter()
            .map(|param| {
                tail_loop
                    .new_params
                    .get(param)
                    .cloned()
                    .unwrap_or_else(|| param.clone())
            })
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
                ident: param.clone(),
                value: Some(Expression::var(new_param.clone())),
                property: LetKind::Alias,
                ident_info: IdentInfo::default(),
            }));
        }
        loop_body.extend(body);

        Expression::new(ExpressionDesc::Fun {
            is_method: false,
            params: lowered_params,
            body: vec![Statement::while_(Expression::bool(true), loop_body)],
            env: Default::default(),
            return_unit: func.attr.return_unit,
            async_: func.attr.async_,
            directive: (func.attr.directive.clone()).map(Box::new),
        })
    }

    pub(crate) fn compile_tail_loop_return_block(
        &mut self,
        lam: &Lambda,
        tail_loop: &mut TailLoopState,
    ) -> Block {
        // Mirror OCaml's invariant that consumers of `compile_lambda` go
        // through `Js_output.output_as_block` which calls `unnest_block`.
        unnest_block(self.compile_tail_loop_return_block_inner(lam, tail_loop))
    }

    fn compile_tail_loop_return_block_inner(
        &mut self,
        lam: &Lambda,
        tail_loop: &mut TailLoopState,
    ) -> Block {
        match lam {
            Lambda::Llet(kind, id, value, body) => {
                let mut block = self.compile_let_binding(*kind, id, value);
                block.extend(self.compile_tail_loop_return_block(body, tail_loop));
                block
            }
            Lambda::Lapply(apply) => {
                if let Some(block) = self.try_compile_self_tailcall_block(apply, tail_loop) {
                    return block;
                }
                let compiled = self.compile_apply_call(apply);
                let mut block = compiled.prelude;
                block.push(Statement::return_(compiled.expr));
                block
            }
            Lambda::LifThenElse(cond, then_, else_) => {
                self.compile_tail_loop_if_return_block(cond, then_, else_, tail_loop)
            }
            Lambda::Lprim(info) => {
                if let Some((op, lhs, rhs)) = short_circuit_primitive(&info.primitive, &info.args) {
                    return self
                        .compile_short_circuit_tail_loop_return_block(op, lhs, rhs, tail_loop);
                }
                let compiled = self.compile_expr(lam);
                let mut block = compiled.prelude;
                if !block_terminates(&block) {
                    block.push(Statement::return_(compiled.expr));
                }
                block
            }
            Lambda::Lsequence(first, second) => {
                let mut block = self.compile_effect_block(first);
                block.extend(self.compile_tail_loop_return_block(second, tail_loop));
                block
            }
            Lambda::LstaticRaise(id, args) => {
                if let Some(block) = self.compile_static_raise_jump_block(*id, args) {
                    return block;
                }
                if let Some(block) = self.compile_fallthrough_static_raise_return_block(*id, args) {
                    return block;
                }
                if let Some(handler) = self.resolve_static_raise(*id, args) {
                    return self.compile_tail_loop_return_block(&handler, tail_loop);
                }
                let compiled = self.compile_expr(lam);
                let mut block = compiled.prelude;
                if !block_terminates(&block) {
                    block.push(Statement::return_(compiled.expr));
                }
                block
            }
            Lambda::LstaticCatch(body, (label, bindings), handler) => {
                // lam_compile.ml:935 — `flatten_nested_caches` is the first
                // step of `compile_staticcatch`. A >1 entry code_table goes
                // through the multi-handler explicit-jump arm
                // (lam_compile.ml:1000-1010).
                let (handlers, flat_body) = flatten_nested_caches(*label, bindings, body, handler);
                if handlers.len() > 1 {
                    return self.compile_multi_staticcatch_tail_loop_return_block(
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
                    self.compile_fallthrough_staticcatch_tail_loop_return_block(
                        *label, bindings, body, handler, tail_loop,
                    )
                } else if requires_explicit_jump {
                    self.compile_staticcatch_tail_loop_return_block(
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
                    self.compile_fallthrough_staticcatch_tail_loop_return_block(
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
                    self.compile_staticcatch_tail_loop_return_block(
                        *label, bindings, body, handler, tail_loop,
                    )
                } else {
                    self.with_static_handler(*label, bindings, handler, |this| {
                        this.compile_tail_loop_return_block(body, tail_loop)
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
                vec![self.try_statement(body_block, exn, handler_block)]
            }
            Lambda::Lswitch(scrut, switch) => {
                self.compile_tail_loop_switch_return_block(scrut, switch, tail_loop)
            }
            Lambda::LstringSwitch(scrut, cases, default) => self
                .compile_tail_loop_string_switch_return_block(
                    scrut,
                    cases,
                    default.as_deref(),
                    tail_loop,
                ),
            _ => {
                let compiled = self.compile_expr(lam);
                let mut block = compiled.prelude;
                if !block_terminates(&block) {
                    block.push(Statement::return_(compiled.expr));
                }
                block
            }
        }
    }

    fn compile_tail_loop_if_return_block(
        &mut self,
        cond: &Lambda,
        then_: &Lambda,
        else_: &Lambda,
        tail_loop: &mut TailLoopState,
    ) -> Block {
        let cond_compiled = self.compile_expr(cond);
        let then_block = self.compile_tail_loop_return_block(then_, tail_loop);
        let else_block = self.compile_tail_loop_return_block(else_, tail_loop);

        let mut block = cond_compiled.prelude;
        if let (Some(then_expr), Some(else_expr)) = (
            single_return_expression(&then_block),
            single_return_expression(&else_block),
        ) {
            block.push(Statement::return_(Expression::cond(
                cond_compiled.expr,
                then_expr,
                else_expr,
            )));
            return block;
        }

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
            return block;
        }
        block.push(Statement::if_(cond_expr, then_block, else_block));
        block
    }

    fn compile_short_circuit_tail_loop_return_block(
        &mut self,
        op: ShortCircuitOp,
        lhs: &Lambda,
        rhs: &Lambda,
        tail_loop: &mut TailLoopState,
    ) -> Block {
        let default = op.default_lambda();
        match op {
            ShortCircuitOp::And => {
                self.compile_tail_loop_if_return_block(lhs, rhs, &default, tail_loop)
            }
            ShortCircuitOp::Or => {
                self.compile_tail_loop_if_return_block(lhs, &default, rhs, tail_loop)
            }
        }
    }

    fn compile_tail_loop_switch_return_block(
        &mut self,
        scrut: &Lambda,
        switch: &LambdaSwitch,
        tail_loop: &mut TailLoopState,
    ) -> Block {
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
            let compiled_body = self.compile_tail_loop_return_block(body, tail_loop);
            let group_falls_through = compiled_body.is_empty();
            // Tail-loop lowering is Rust-specific, but it must preserve OCaml's
            // `compile_general_cases` break semantics: the last grouped case
            // uses `Js_output.to_break_block`, then return continuation keeps
            // that break only when the source lambda has an exit
            // (compiler/core/lam_compile.ml:613-624;
            // compiler/core/js_output.ml:88-100).
            let should_break = self.return_case_needs_break_like_ocaml(body, &compiled_body);

            for (tag, _, _) in &grouped_cases[group_start..group_end] {
                cases.push((tag.clone(), empty_switch_case_clause(), group_falls_through));
            }
            cases.push((
                grouped_cases[group_end].0.clone(),
                CaseClause {
                    source_loc: None,
                    body: compiled_body,
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

            let target = tail_loop
                .new_params
                .entry(param.clone())
                .or_insert_with(|| self.fresh_ident(&format!("_{}", param.name())))
                .clone();
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

                let mut prelude = self.compile_let_binding(*kind, id, value);
                if block_terminates(&prelude) {
                    return Compiled {
                        prelude,
                        expr: Expression::undefined(false),
                    };
                }
                let body_compiled = self.compile_effect_output(body);
                prelude.extend(body_compiled.prelude);
                Compiled {
                    prelude,
                    expr: body_compiled.expr,
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
            Lambda::LstaticCatch(body, (label, bindings), handler) => {
                let (handlers, flat_body) = flatten_nested_caches(*label, bindings, body, handler);
                if handlers.len() > 1 {
                    // lam_compile.ml:935 + 1000-1010 — multi-handler
                    // explicit-jump arm for an effect-value continuation.
                    return Compiled {
                        prelude: self.compile_multi_staticcatch_effect_block(&handlers, flat_body),
                        expr: Expression::undefined(false),
                    };
                }
                // OCaml's `Lsequence` compiles its head with
                // `EffectCall Not_tail`; in `compile_staticcatch`
                // (lam_compile.ml:984-1059), that continuation always falls
                // through to the explicit-jump arm. Keep the same shape here
                // instead of inlining the handler at every raise site.
                Compiled {
                    prelude: self.compile_staticcatch_effect_block(*label, bindings, body, handler),
                    expr: Expression::undefined(false),
                }
            }
            Lambda::Lswitch(scrut, switch) => Compiled {
                prelude: self.compile_switch_effect_block(scrut, switch),
                expr: Expression::undefined(false),
            },
            Lambda::LstringSwitch(scrut, cases, default) => Compiled {
                prelude: self.compile_string_switch_effect_block(scrut, cases, default.as_deref()),
                expr: Expression::undefined(false),
            },
            _ => self.compile_expr(lam),
        }
    }

    fn append_effect_output(&self, first: Compiled, second: Compiled) -> Compiled {
        if block_finishes_output(&first.prelude) {
            return Compiled {
                prelude: first.prelude,
                expr: Expression::undefined(false),
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
        }
    }

    fn compiled_to_effect_block(&self, compiled: Compiled) -> Block {
        let mut block = compiled.prelude;
        if block_finishes_output(&block) {
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
                    // OCaml's `S.if_ cond [] []` collapses to `S.exp cond`
                    // (js_stmt_make.ml:242 + 45-53). Preserve non-Number/
                    // Undefined pure expressions like `tmp === null;`.
                    push_s_exp(&mut block, cond_expr);
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
                    ident: id.clone(),
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
                        ident: id.clone(),
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
        Statement::exp(Expression::bin(
            BinOp::Eq,
            Expression::var(id.clone()),
            expr,
        ))
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
                            ident: id.clone(),
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
            ident: id.clone(),
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

    fn take_return_tail_expr(&self, block: Block) -> Result<Expression, Block> {
        if crate::debug_flags::debug_take_return_tail() {
            let rendered = crate::js_ir::print_block(&block);
            if rendered.contains("Invalid_argument")
                || rendered.contains("RE_EXN_ID === A")
                || rendered.contains("RE_EXN_ID === B")
            {
                eprintln!("[take-return-tail]\n{rendered}\n");
            }
        }

        let mut prefix = block.clone();
        let Some(last) = prefix.pop() else {
            return Err(block);
        };
        let Statement {
            desc: StatementDesc::Return(mut expr),
            ..
        } = last
        else {
            return Err(block);
        };

        if matches!(expr.desc, ExpressionDesc::Undefined { .. }) && !prefix.is_empty() {
            return Err(block);
        }

        if let [stmt] = prefix.as_slice() {
            if let StatementDesc::If(cond, then_block, else_block) = &stmt.desc {
                if else_block.is_empty() {
                    if let Ok(then_expr) = self.take_return_tail_expr(then_block.clone()) {
                        return Ok(Expression::cond(cond.clone(), then_expr, expr));
                    }
                    return Err(block);
                }
            }
        }

        // OCaml reaches `return cond ? (effect, value) : fallback` here for
        // simple effectful success branches, and `js_pass_flatten` later turns
        // that back into the checked-in positive `if/else` shape.
        for stmt in prefix.into_iter().rev() {
            let Statement {
                desc: StatementDesc::Exp(effect),
                ..
            } = stmt
            else {
                return Err(block);
            };
            expr = js_seq(effect, expr);
        }

        Ok(expr)
    }

    fn compile_if_return_block(&mut self, cond: &Lambda, then_: &Lambda, else_: &Lambda) -> Block {
        let key = then_ as *const Lambda as usize;
        self.if_return_finished.insert(key, false);
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
                self.if_return_finished.insert(key, true);
                let mut block = cond_compiled.prelude;
                block.push(Statement::return_(Expression::cond(
                    cond_compiled.expr,
                    then_seq,
                    else_seq,
                )));
                return block;
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
            self.if_return_finished.insert(key, true);
            let mut block = cond_compiled.prelude;
            block.push(Statement::return_(Expression::cond(
                cond_compiled.expr,
                then_value.expr,
                else_value.expr,
            )));
            return block;
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
        block
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
        if crate::debug_flags::debug_compile_test_return() {
            let cond_text = crate::js_ir::print_expression(&cond);
            if cond_text.contains("RE_EXN_ID") || cond_text.contains("_1 === \"x\"") {
                eprintln!(
                    "[compile-test-return]\ncond: {cond_text}\nthen:\n{}\nelse:\n{}\n",
                    crate::js_ir::print_block(&then_fallback),
                    crate::js_ir::print_block(&else_fallback),
                );
            }
        }

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

    pub(crate) fn compile_switch_value_block(&mut self, result: &Ident, lam: &Lambda) -> Block {
        let mut block = self.compile_assign_to_target_block(result, lam);
        if !block_terminates(&block) {
            block.push(Statement::break_());
        }
        block
    }

    pub(crate) fn compile_assign_to_target_block(&mut self, result: &Ident, lam: &Lambda) -> Block {
        match lam {
            Lambda::Llet(kind, id, value, body) => {
                if let Some(compiled) = self.try_compile_record_spread(id, value, body) {
                    let mut block = compiled.prelude;
                    block.push(Statement::exp(Expression::bin(
                        BinOp::Eq,
                        Expression::var(result.clone()),
                        compiled.expr,
                    )));
                    return block;
                }

                let mut block = self.compile_let_binding(*kind, id, value);
                block.extend(self.compile_assign_to_target_block(result, body));
                block
            }
            Lambda::Lapply(apply) => {
                let compiled = self.compile_apply_call(apply);
                let mut block = compiled.prelude;
                block.push(Statement::exp(Expression::bin(
                    BinOp::Eq,
                    Expression::var(result.clone()),
                    compiled.expr,
                )));
                block
            }
            Lambda::Lsequence(first, second) => {
                let mut block = self.compile_effect_block(first);
                block.extend(self.compile_assign_to_target_block(result, second));
                block
            }
            Lambda::LstaticCatch(body, (label, bindings), handler) => {
                // OCaml's `compile_staticcatch` (lam_compile.ml:937-1017)
                // gates pseudo-jmp on `EffectCall (Maybe_tail_is_return
                // (Tail_with_name {in_staticcatch=false}))`. For an `Assign`
                // continuation — which is where `compile_assign_to_target_block`
                // sits — the match falls into the explicit-jump arm at
                // lam_compile.ml:1005-1010 (`| Assign _ -> ...`). Take the
                // explicit-jump path unconditionally; the `with_static_handler`
                // shortcut is a Rust-only optimization with no OCaml analog in
                // this continuation.
                let (handlers, flat_body) = flatten_nested_caches(*label, bindings, body, handler);
                if handlers.len() > 1 {
                    self.compile_multi_staticcatch_assignment_block(result, &handlers, flat_body)
                } else {
                    self.compile_staticcatch_assignment_block(
                        result, *label, bindings, body, handler,
                    )
                }
            }
            Lambda::LtryWith(body, exn, handler) => {
                let body_block = self.compile_assign_to_target_block(result, body);
                let handler_block = self.compile_assign_to_target_block(result, handler);
                vec![self.try_statement(body_block, exn, handler_block)]
            }
            Lambda::LifThenElse(cond, then_, else_) => {
                self.compile_if_assignment_block(result, cond, then_, else_)
            }
            // compile_sequand / compile_sequor with an `Assign v` continuation
            // (lam_compile.ml:1138-1210).
            Lambda::Lprim(info) if short_circuit_primitive(&info.primitive, &info.args).is_some() => {
                let (op, lhs, rhs) =
                    short_circuit_primitive(&info.primitive, &info.args).expect("checked above");
                let lhs_compiled = self.compile_expr(lhs);
                let rhs_compiled = self.compile_expr(rhs);
                let assign = |value: Expression| {
                    Statement::exp(Expression::bin(
                        BinOp::Eq,
                        Expression::var(result.clone()),
                        value,
                    ))
                };
                let mut block = lhs_compiled.prelude;
                if rhs_compiled.prelude.is_empty() {
                    let op = match op {
                        ShortCircuitOp::And => BinOp::And,
                        ShortCircuitOp::Or => BinOp::Or,
                    };
                    block.push(assign(Expression::bin(op, lhs_compiled.expr, rhs_compiled.expr)));
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
            Lambda::LstaticRaise(id, args) => {
                // OCaml's `compile_staticraise` (lam_compile.ml:887-904) ignores
                // the enclosing Assign continuation and emits only the argument
                // assignments + `exit = N`. Without this arm we would fall
                // through to the generic case below, which appends a spurious
                // `result = undefined` after the jump even though control has
                // already transferred to the post-body exit dispatch.
                if let Some(block) = self.compile_static_raise_jump_block(*id, args) {
                    return block;
                }
                if let Some(handler) = self.resolve_static_raise(*id, args) {
                    return self.compile_assign_to_target_block(result, &handler);
                }
                let compiled = self.compile_expr(lam);
                let mut block = compiled.prelude;
                if !block_terminates(&block) {
                    block.push(Statement::exp(Expression::bin(
                        BinOp::Eq,
                        Expression::var(result.clone()),
                        compiled.expr,
                    )));
                }
                block
            }
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
            _ => {
                let compiled = self.compile_expr(lam);
                let mut block = compiled.prelude;
                if !block_terminates(&block) {
                    block.push(Statement::exp(Expression::bin(
                        BinOp::Eq,
                        Expression::var(result.clone()),
                        compiled.expr,
                    )));
                }
                block
            }
        }
    }

    fn compile_switch_assignment_block(
        &mut self,
        result: &Ident,
        scrut: &Lambda,
        switch: &LambdaSwitch,
    ) -> Block {
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
        if self.uses_untagged_variant_switch(switch) {
            let scrut_compiled = self.compile_expr(scrut);
            let (mut block, scrut_expr) =
                self.bind_switch_scrutinee_once(scrut_compiled.prelude, scrut_compiled.expr);
            block.extend(
                self.compile_untagged_variant_switch_assignment_statements(
                    result, scrut_expr, switch,
                ),
            );
            return block;
        }

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
                            source_loc: None,
                            body: self.compile_switch_value_block(result, body),
                            should_break: false,
                            comment: None,
                        }
                    } else {
                        empty_switch_case_clause()
                    },
                )
            })
            .collect();

        let default_block = switch
            .sw_failaction
            .as_ref()
            .map(|fallback| self.compile_assign_to_target_block(result, fallback));

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
                        source_loc: None,
                        body: self.compile_switch_value_block(result, body),
                        should_break: false,
                        comment: None,
                    }
                } else {
                    empty_switch_case_clause()
                },
            })
            .collect();

        let default_block =
            default.map(|fallback| self.compile_assign_to_target_block(result, fallback));

        block.push(Statement::new(StatementDesc::StringSwitch(
            scrut_compiled.expr,
            clauses,
            default_block,
        )));
        block
    }

    fn compile_switch_return_block(&mut self, scrut: &Lambda, switch: &LambdaSwitch) -> Block {
        self.with_switch_depth(|this| this.compile_switch_return_block_inner(scrut, switch))
    }

    fn compile_switch_return_block_inner(
        &mut self,
        scrut: &Lambda,
        switch: &LambdaSwitch,
    ) -> Block {
        if self.uses_untagged_variant_switch(switch) {
            let scrut_compiled = self.compile_expr(scrut);
            let (mut block, scrut_expr) =
                self.bind_switch_scrutinee_once(scrut_compiled.prelude, scrut_compiled.expr);
            block
                .extend(self.compile_untagged_variant_switch_return_statements(scrut_expr, switch));
            return block;
        }

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
            let compiled_body = self.compile_return_block(body);
            let group_falls_through = compiled_body.is_empty();
            // Mirror OCaml's `lam_compile.ml` pseudo-jmp emission: when a
            // case body resolved away through a fallthrough static-raise
            // handler, OCaml still prints an explicit `break;` to exit the
            // switch so the subsequent appended handler reads cleanly.
            let should_break = self.return_case_needs_break_like_ocaml(body, &compiled_body);

            for (tag, _, _) in &grouped_cases[group_start..group_end] {
                cases.push((tag.clone(), empty_switch_case_clause(), group_falls_through));
            }
            cases.push((
                grouped_cases[group_end].0.clone(),
                crate::js_ir::CaseClause {
                    source_loc: None,
                    body: compiled_body,
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
        self.with_switch_depth(|this| this.compile_switch_effect_block_inner(scrut, switch))
    }

    fn compile_switch_effect_block_inner(
        &mut self,
        scrut: &Lambda,
        switch: &LambdaSwitch,
    ) -> Block {
        if self.uses_untagged_variant_switch(switch) {
            let scrut_compiled = self.compile_expr(scrut);
            let (mut block, scrut_expr) =
                self.bind_switch_scrutinee_once(scrut_compiled.prelude, scrut_compiled.expr);
            let dispatch =
                self.compile_untagged_variant_switch_effect_statements(scrut_expr.clone(), switch);
            if dispatch.is_empty() {
                // OCaml's switch compilation collapses an empty dispatch to
                // `S.exp scrut` (via js_output.ml + js_stmt_make.ml:45-53),
                // preserving bare comparisons like `tmp === null;`.
                push_s_exp(&mut block, scrut_expr);
            } else {
                block.extend(dispatch);
            }
            return block;
        }

        if self.uses_named_variant_switch(switch) {
            let scrut_compiled = self.compile_expr(scrut);
            let (mut block, scrut_expr) = if self.named_variant_switch_needs_bound_scrutinee(switch)
            {
                self.bind_switch_scrutinee_once(scrut_compiled.prelude, scrut_compiled.expr)
            } else {
                (scrut_compiled.prelude, scrut_compiled.expr)
            };
            let dispatch =
                self.compile_named_variant_switch_effect_statements(scrut_expr.clone(), switch);
            if dispatch.is_empty() {
                // OCaml's switch collapses to `S.exp scrut` when the whole
                // dispatch is unit (js_stmt_make.ml:45-53) — keeps bare
                // comparisons as `Exp` statements.
                push_s_exp(&mut block, scrut_expr);
                return block;
            }
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
                    let body = self.compile_effect_block(body);
                    crate::js_ir::CaseClause {
                        source_loc,
                        should_break: !block_terminates(&body),
                        body,
                        comment: None,
                    }
                } else {
                    empty_switch_case_clause()
                };
                (direct_switch_int(tag), clause)
            })
            .collect();

        let default_block = switch
            .sw_failaction
            .as_ref()
            .map(|fallback| self.compile_effect_block(fallback))
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
            if small.is_empty() {
                // OCaml collapses an all-empty switch to `S.exp scrut`
                // (js_stmt_make.ml:45-53), preserving bare pure expressions.
                push_s_exp(&mut block, scrut_compiled.expr);
            } else {
                block.extend(small);
            }
            return block;
        }

        let clauses: Vec<_> = self
            .grouped_switch_cases(cases, default, |_, _| true)
            .into_iter()
            .map(|(tag, body, is_last)| {
                let clause = if is_last {
                    let source_loc = self.source_loc_of_lam(body);
                    let body = self.compile_effect_block(body);
                    crate::js_ir::CaseClause {
                        source_loc,
                        should_break: !block_terminates(&body),
                        body,
                        comment: None,
                    }
                } else {
                    empty_switch_case_clause()
                };
                crate::js_ir::StringClause {
                    tag_type: SwitchCaseTag::String(tag),
                    clause,
                }
            })
            .collect();

        let default_block = default
            .map(|fallback| self.compile_effect_block(fallback))
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
            exit_id: exit_id.clone(),
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

    fn staticcatch_requires_explicit_jump(&self, bindings: &[Ident], handler: &Lambda) -> bool {
        let _ = bindings;
        self.lambda_requires_explicit_staticcatch_jump(handler)
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
            Lambda::LtryWith(body, _, handler) => {
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
            Lambda::LtryWith(body, _, handler) => {
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

    fn compile_static_raise_jump_block(&mut self, label: i32, args: &[Lambda]) -> Option<Block> {
        let handler = self
            .static_jump_handlers
            .iter()
            .rev()
            .find(|handler| handler.label == label)?
            .clone();
        if handler.bindings.len() != args.len() {
            return None;
        }

        let mut block = Vec::new();
        for (binding, arg) in handler.bindings.iter().zip(args) {
            block.extend(self.compile_assign_to_target_block(binding, arg));
        }
        block.push(Statement::exp(Expression::bin(
            BinOp::Eq,
            Expression::var(handler.exit_id),
            Expression::number(Number::int(handler.exit_code)),
        )));
        Some(block)
    }

    fn staticcatch_declarations(&self, exit_id: &Ident, bindings: &[Ident]) -> Block {
        let mut declarations = vec![Statement::variable(VariableDeclaration {
            ident: exit_id.clone(),
            value: Some(Expression::number(Number::int(0))),
            property: LetKind::Variable,
            ident_info: IdentInfo::default(),
        })];
        declarations.extend(bindings.iter().map(|binding| {
            Statement::variable(VariableDeclaration {
                ident: binding.clone(),
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
            Expression::var(exit_id.clone()),
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
        let exit_id = self.fresh_ident("exit");
        let exit_code = self.next_static_jump_exit_code();
        let mut block = self.staticcatch_declarations(&exit_id, bindings);
        let (body_block, handler_block) =
            self.with_static_jump_handler(label, &exit_id, bindings, |this| {
                let body_block = this.compile_assign_to_target_block(result, body);
                let handler_block = if block_terminates(&body_block) {
                    vec![]
                } else {
                    this.compile_assign_to_target_block(result, handler)
                };
                (body_block, handler_block)
            });
        block.extend(body_block);
        if !block_terminates(&block) {
            if !handler_block.is_empty() {
                block.push(Statement::if_(
                    self.staticcatch_exit_test(&exit_id, exit_code),
                    handler_block,
                    vec![],
                ));
            }
        }
        block
    }

    fn compile_staticcatch_effect_block(
        &mut self,
        label: i32,
        bindings: &[Ident],
        body: &Lambda,
        handler: &Lambda,
    ) -> Block {
        let exit_id = self.fresh_ident("exit");
        let exit_code = self.next_static_jump_exit_code();
        let mut block = self.staticcatch_declarations(&exit_id, bindings);
        let (body_block, handler_block) =
            self.with_static_jump_handler(label, &exit_id, bindings, |this| {
                let body_block = this.compile_effect_block(body);
                let handler_block = if block_terminates(&body_block) {
                    vec![]
                } else {
                    this.compile_effect_block(handler)
                };
                (body_block, handler_block)
            });
        block.extend(body_block);
        if !block_terminates(&block) {
            if !handler_block.is_empty() {
                block.push(Statement::if_(
                    self.staticcatch_exit_test(&exit_id, exit_code),
                    handler_block,
                    vec![],
                ));
            }
        }
        block
    }

    fn compile_staticcatch_return_block(
        &mut self,
        label: i32,
        bindings: &[Ident],
        body: &Lambda,
        handler: &Lambda,
    ) -> Block {
        let exit_id = self.fresh_ident("exit");
        let exit_code = self.next_static_jump_exit_code();
        let mut block = self.staticcatch_declarations(&exit_id, bindings);
        let (body_block, handler_block) =
            self.with_static_jump_handler(label, &exit_id, bindings, |this| {
                let body_block = this.compile_return_block(body);
                let handler_block = if block_terminates(&body_block) {
                    vec![]
                } else {
                    this.compile_return_block(handler)
                };
                (body_block, handler_block)
            });
        block.extend(body_block);
        if !block_terminates(&block) {
            if !handler_block.is_empty() {
                block.push(Statement::if_(
                    self.staticcatch_exit_test(&exit_id, exit_code),
                    handler_block,
                    vec![],
                ));
            }
        }
        block
    }

    fn compile_staticcatch_tail_loop_return_block(
        &mut self,
        label: i32,
        bindings: &[Ident],
        body: &Lambda,
        handler: &Lambda,
        tail_loop: &mut TailLoopState,
    ) -> Block {
        let exit_id = self.fresh_ident("exit");
        let exit_code = self.next_static_jump_exit_code();
        let mut block = self.staticcatch_declarations(&exit_id, bindings);
        let (body_block, handler_block) =
            self.with_static_jump_handler(label, &exit_id, bindings, |this| {
                let body_block = this.compile_tail_loop_return_block(body, tail_loop);
                let handler_block = if block_terminates(&body_block) {
                    vec![]
                } else {
                    this.compile_tail_loop_return_block(handler, tail_loop)
                };
                (body_block, handler_block)
            });
        block.extend(body_block);
        if !block_terminates(&block) {
            if !handler_block.is_empty() {
                block.push(Statement::if_(
                    self.staticcatch_exit_test(&exit_id, exit_code),
                    handler_block,
                    vec![],
                ));
            }
        }
        block
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
            ident: result.clone(),
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
            ident: exit_id.clone(),
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
                    ident: binding.clone(),
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
                exit_id: exit_id.clone(),
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
        mut compile: impl FnMut(&mut Self, &Lambda) -> Block,
    ) -> Vec<(i32, Block, bool, &'a Lambda)> {
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
                let block = if is_last {
                    compile(self, handler)
                } else {
                    Vec::new()
                };
                (code, block, is_last, handler)
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
        handlers: Vec<(i32, Block, bool, &Lambda)>,
        is_return_context: bool,
    ) -> Option<Statement> {
        if handlers.is_empty() {
            return None;
        }
        if handlers.len() == 1 {
            let (code, handler_block, _, _) = handlers.into_iter().next().unwrap();
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
            .map(|(code, body, is_last, handler_lam)| {
                let should_break = is_last
                    && !block_terminates(&body)
                    && (!is_return_context || has_exit_code(handler_lam, |_| true));
                (
                    code,
                    CaseClause {
                        source_loc: None,
                        body,
                        should_break,
                        comment: None,
                    },
                )
            })
            .collect();
        Some(Statement::new(StatementDesc::IntSwitch(
            Expression::var(exit_id.clone()),
            clauses,
            None,
        )))
    }

    fn compile_multi_staticcatch_return_block(
        &mut self,
        handlers: &[FlatHandler],
        body: &Lambda,
    ) -> Block {
        let (exit_id, first_code, mut block) = self.emit_multi_staticcatch_prelude(handlers);
        let body_block = self.compile_return_block(body);
        // If the body already terminates (e.g. every path returned), OCaml
        // would still emit the dispatch but it'd be dead. Match
        // `compile_staticcatch_return_block`'s current behavior: skip it.
        let grouped_handlers = if block_terminates(&body_block) {
            Vec::new()
        } else {
            self.compile_grouped_staticcatch_handlers(handlers, first_code, |this, handler| {
                this.compile_return_block(handler)
            })
        };
        self.pop_multi_staticcatch_handlers(handlers.len());
        block.extend(body_block);
        if !block_terminates(&block) {
            if let Some(dispatch) = self.compile_exit_dispatch(&exit_id, grouped_handlers, true) {
                block.push(dispatch);
            }
        }
        block
    }

    fn compile_multi_staticcatch_effect_block(
        &mut self,
        handlers: &[FlatHandler],
        body: &Lambda,
    ) -> Block {
        let (exit_id, first_code, mut block) = self.emit_multi_staticcatch_prelude(handlers);
        let body_block = self.compile_effect_block(body);
        let grouped_handlers = if block_terminates(&body_block) {
            Vec::new()
        } else {
            self.compile_grouped_staticcatch_handlers(handlers, first_code, |this, handler| {
                this.compile_effect_block(handler)
            })
        };
        self.pop_multi_staticcatch_handlers(handlers.len());
        block.extend(body_block);
        if !block_terminates(&block) {
            if let Some(dispatch) = self.compile_exit_dispatch(&exit_id, grouped_handlers, false) {
                block.push(dispatch);
            }
        }
        block
    }

    fn compile_multi_staticcatch_assignment_block(
        &mut self,
        result: &Ident,
        handlers: &[FlatHandler],
        body: &Lambda,
    ) -> Block {
        let (exit_id, first_code, mut block) = self.emit_multi_staticcatch_prelude(handlers);
        let body_block = self.compile_assign_to_target_block(result, body);
        let grouped_handlers = if block_terminates(&body_block) {
            Vec::new()
        } else {
            self.compile_grouped_staticcatch_handlers(handlers, first_code, |this, handler| {
                this.compile_assign_to_target_block(result, handler)
            })
        };
        self.pop_multi_staticcatch_handlers(handlers.len());
        block.extend(body_block);
        if !block_terminates(&block) {
            if let Some(dispatch) = self.compile_exit_dispatch(&exit_id, grouped_handlers, false) {
                block.push(dispatch);
            }
        }
        block
    }

    fn compile_multi_staticcatch_tail_loop_return_block(
        &mut self,
        handlers: &[FlatHandler],
        body: &Lambda,
        tail_loop: &mut TailLoopState,
    ) -> Block {
        let (exit_id, first_code, mut block) = self.emit_multi_staticcatch_prelude(handlers);
        let body_block = self.compile_tail_loop_return_block(body, tail_loop);
        let grouped_handlers = if block_terminates(&body_block) {
            Vec::new()
        } else {
            self.compile_grouped_staticcatch_handlers(handlers, first_code, |this, handler| {
                this.compile_tail_loop_return_block(handler, tail_loop)
            })
        };
        self.pop_multi_staticcatch_handlers(handlers.len());
        block.extend(body_block);
        if !block_terminates(&block) {
            if let Some(dispatch) = self.compile_exit_dispatch(&exit_id, grouped_handlers, true) {
                block.push(dispatch);
            }
        }
        block
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

/// True if this Lambda unconditionally transfers control out of the
/// enclosing block — its compiled form has no usable fall-through. Matches
/// OCaml's `Js_output.output_finished:True`: `Lbreak` and `Lcontinue` set
/// it directly (lam_compile.ml:1928, 1943); nothing else in this code path
/// is compiled with that flag.
fn lambda_is_unconditional_exit(lam: &Lambda) -> bool {
    matches!(lam, Lambda::Lbreak | Lambda::Lcontinue)
}

fn staticcatch_debug_kind(lam: &Lambda) -> &'static str {
    match lam {
        Lambda::LstaticCatch(_, _, _) => "staticcatch",
        Lambda::LstaticRaise(_, _) => "staticraise",
        Lambda::LifThenElse(_, _, _) => "if",
        Lambda::Lswitch(_, _) => "switch",
        Lambda::LstringSwitch(_, _, _) => "stringswitch",
        Lambda::Llet(_, _, _, _) => "let",
        Lambda::Lsequence(_, _) => "sequence",
        Lambda::LtryWith(_, _, _) => "trywith",
        Lambda::Lprim(_) => "prim",
        Lambda::Lconst(_) => "const",
        Lambda::Lvar(_) => "var",
        Lambda::Lapply(_) => "apply",
        Lambda::Lfunction(_) => "function",
        Lambda::Lletrec(_, _) => "letrec",
        Lambda::Lwhile(_, _) => "while",
        Lambda::Lfor(_, _, _, _, _) => "for",
        Lambda::Lfor_of(_, _, _) => "for_of",
        Lambda::Lfor_await_of(_, _, _) => "for_await_of",
        Lambda::Lbreak => "break",
        Lambda::Lcontinue => "continue",
        Lambda::Lassign(_, _) => "assign",
        Lambda::LglobalModule(_) => "global_module",
    }
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
        .map(|(index, (id, _))| (id.clone(), index))
        .collect::<HashMap<_, _>>();

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

fn recursive_function_bindings(bindings: &[(Ident, Lambda)]) -> HashMap<Ident, LFunction> {
    bindings
        .iter()
        .filter_map(|(id, expr)| {
            recursive_function_binding_value(expr).map(|func| (id.clone(), func))
        })
        .collect()
}

fn recursive_function_bindings_in_group(
    bindings: &[(Ident, Lambda)],
    group: &[usize],
) -> HashMap<Ident, LFunction> {
    group
        .iter()
        .filter_map(|&index| {
            let (id, expr) = &bindings[index];
            recursive_function_binding_value(expr).map(|func| (id.clone(), func))
        })
        .collect()
}

fn recursive_function_binding_alias_target(
    expr: &Lambda,
    recursive_functions: &HashMap<Ident, LFunction>,
) -> Option<Ident> {
    let lookup = |target: &Ident| {
        recursive_functions
            .iter()
            .find(|(function_id, _)| target.same(function_id))
    };

    match expr {
        Lambda::Lvar(target) => lookup(target).map(|(function_id, _)| function_id.clone()),
        _ => None,
    }
}

fn lower_ocaml_for_range_direction<'a>(
    direction: &crate::lambda::DirectionFlag,
    finish: &'a Lambda,
) -> (&'a Lambda, ForDirection) {
    match (direction, finish) {
        (
            crate::lambda::DirectionFlag::Upto,
            Lambda::Lprim(__prim3),
        ) if matches!(__prim3.as_ref(), crate::lambda::PrimInfo {
                primitive: Primitive::Psubint,
                args,
                ..
            }) => {
            let crate::lambda::PrimInfo {
                primitive: Primitive::Psubint,
                args,
                ..
            } = __prim3.as_ref() else {
                unreachable!()
            };
            match args.as_slice() {
            [new_finish, Lambda::Lconst(Constant::Int { i: 1, .. })] => {
                (new_finish, ForDirection::Up)
            }
            _ => (finish, ForDirection::Upto),
        }
        },
        (crate::lambda::DirectionFlag::Upto, _) => (finish, ForDirection::Upto),
        (crate::lambda::DirectionFlag::Downto, _) => (finish, ForDirection::Downto),
    }
}

fn single_return_expression(block: &Block) -> Option<Expression> {
    let [stmt] = block.as_slice() else {
        return None;
    };
    let StatementDesc::Return(expr) = &stmt.desc else {
        return None;
    };
    Some(expr.clone())
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

pub(crate) fn trailing_return_expression(block: &[Statement]) -> Option<&Expression> {
    let stmt = block.last()?;
    let StatementDesc::Return(expr) = &stmt.desc else {
        return None;
    };
    Some(expr)
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
) -> HashMap<Ident, Vec<Ident>> {
    let recursive_functions = recursive_function_bindings(bindings);
    direct_recursive_function_tail_targets_with_bindings(bindings, &recursive_functions)
}

fn direct_recursive_function_tail_targets_with_group(
    bindings: &[(Ident, Lambda)],
    group: &[usize],
    recursive_functions: &HashMap<Ident, LFunction>,
) -> HashMap<Ident, Vec<Ident>> {
    let mut tail_targets: HashMap<Ident, Vec<Ident>> = recursive_functions
        .keys()
        .cloned()
        .map(|id| {
            let targets = vec![id.clone()];
            (id, targets)
        })
        .collect();

    for &index in group {
        let (id, expr) = &bindings[index];
        let Some(function_id) = recursive_function_binding_alias_target(expr, recursive_functions)
        else {
            continue;
        };
        tail_targets
            .entry(function_id)
            .or_default()
            .push(id.clone());
    }

    tail_targets
}

fn direct_recursive_function_tail_targets_with_bindings(
    bindings: &[(Ident, Lambda)],
    recursive_functions: &HashMap<Ident, LFunction>,
) -> HashMap<Ident, Vec<Ident>> {
    let mut tail_targets: HashMap<Ident, Vec<Ident>> = recursive_functions
        .keys()
        .cloned()
        .map(|id| {
            let targets = vec![id.clone()];
            (id, targets)
        })
        .collect();

    for (id, expr) in bindings {
        let Some(function_id) = recursive_function_binding_alias_target(expr, recursive_functions)
        else {
            continue;
        };
        tail_targets
            .entry(function_id)
            .or_default()
            .push(id.clone());
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
                crate::lambda::lam_analysis::size(value)
                    < crate::lambda::lam_analysis::SMALL_INLINE_SIZE
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
                        Element::SimpleForm(lam) => get_arity(&meta, lam),
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
                if let Lambda::Lprim(__prim200) = value && let PrimInfo {
                    primitive:
                        Primitive::Pmakeblock(_, crate::lambda::lam_primitive::Mutable::Immutable),
                    args,
                    ..
                } = __prim200.as_ref() {
                    let submodule_arities = args
                        .iter()
                        .map(|lam| get_arity(&meta, lam))
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
        Lambda::Lprim(__prim0) if matches!(__prim0.as_ref(), PrimInfo {
            primitive: Primitive::Pmakeblock(TagInfo::ModuleExport(exports), _),
            args,
            ..
        }) => {
            let PrimInfo {
            primitive: Primitive::Pmakeblock(TagInfo::ModuleExport(exports), _),
            args,
            ..
        } = __prim0.as_ref() else {
                unreachable!()
            };
            Some((exports, args))
        },
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
                id: id.clone(),
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
        Lambda::LstaticCatch(body, _, handler) | Lambda::LtryWith(body, _, handler) => {
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
            source_loc,
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
            },
        };
    }

    Compiled {
        prelude: block,
        expr: Expression::undefined(false),
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
        Lambda::LstaticCatch(body, (_, _), handler) | Lambda::LtryWith(body, _, handler) => {
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
        Lambda::LstaticCatch(body, (_, _), handler) | Lambda::LtryWith(body, _, handler) => {
            lambda_has_exit(body) || lambda_has_exit(handler)
        }
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

impl LambdaCompiler {
    pub(crate) fn return_case_needs_break_like_ocaml(&self, body: &Lambda, compiled_body: &Block) -> bool {
        return_switch_case_needs_break_like_ocaml(
            body,
            compiled_body,
            self.in_staticcatch_like_ocaml(),
            &self.if_return_finished,
        )
    }
}

fn return_switch_case_needs_break_like_ocaml(
    body: &Lambda,
    compiled_body: &Block,
    in_staticcatch: bool,
    if_finished: &AHashMap<usize, bool>,
) -> bool {
    if !lambda_has_exit(body) {
        return false;
    }
    if !block_terminates(compiled_body) {
        return true;
    }
    return_output_is_compound_like_ocaml(body, compiled_body, in_staticcatch, if_finished)
}


fn return_output_is_compound_like_ocaml(
    body: &Lambda,
    compiled_body: &Block,
    in_staticcatch: bool,
    if_finished: &AHashMap<usize, bool>,
) -> bool {
    if let Some(finished) = return_output_finished_like_ocaml(body, in_staticcatch, if_finished) {
        return !finished;
    }
    match body {
        Lambda::Llet(_, _, _, body) | Lambda::Lletrec(_, body) | Lambda::Lsequence(_, body) => {
            return_output_is_compound_like_ocaml(body, compiled_body, in_staticcatch, if_finished)
        }
        // `compile_general_cases` uses `Js_output.to_break_block`, then gates
        // it with `Lam_exit_code.has_exit` in return continuation
        // (compiler/core/lam_compile.ml:610-624). `to_break_block` only
        // suppresses `break` when `output_finished=True`
        // (compiler/core/js_output.ml:88-100); it does not do structural JS
        // termination analysis. Compound return forms like the generic
        // `Lifthenelse` EffectCall fallback keep `output_finished=False`
        // (compiler/core/lam_compile.ml:1456-1531), so OCaml prints `break;`
        // even if every generated branch returns.
        Lambda::LifThenElse(_, _, _)
        | Lambda::Lswitch(_, _)
        | Lambda::LstringSwitch(_, _, _)
        | Lambda::LstaticCatch(_, _, _)
        | Lambda::LtryWith(_, _, _) => return_block_has_multi_test_guard_chain(compiled_body),
        _ => false,
    }
}

/// `Js_output.output_finished` of `compile_lambda` in an
/// `EffectCall (Maybe_tail_is_return _)` continuation, where it does not
/// `None` means the form is not modelled here.
fn return_output_finished_like_ocaml(
    lam: &Lambda,
    in_staticcatch: bool,
    if_finished: &AHashMap<usize, bool>,
) -> Option<bool> {
    match lam {
        // `compile_let`/`compile_sequence` append the binding or effect output
        // to the body output (js_output.ml `append_output`), so the body's
        // flag wins.
        Lambda::Llet(_, _, _, body) | Lambda::Lletrec(_, body) | Lambda::Lsequence(_, body) => {
            return_output_finished_like_ocaml(body, in_staticcatch, if_finished)
        }
        // compile_ifthenelse: recorded by `compile_if_return_block`.
        Lambda::LifThenElse(_, then_, _) => {
            if_finished.get(&(then_.as_ref() as *const Lambda as usize)).copied()
        }
        // compile_switch (lam_compile.ml:822) and compile_stringswitch return
        // `Js_output.make` without `~output_finished`, and so does the
        // `S.try_` built for `Ltrywith`.
        Lambda::Lswitch(_, _) | Lambda::LstringSwitch(_, _, _) | Lambda::LtryWith(_, _, _) => {
            Some(false)
        }
        Lambda::LstaticCatch(body, (label, bindings), handler) => {
            let (code_table, inner_body) = flatten_nested_caches(*label, bindings, body, handler);
            // lam_compile.ml:1022-1047: only the single-exit pseudo-jump arm
            // (tail position, not already in a static catch, handler without
            // static raises) ends with the handler output; the exit-variable
            // arm ends with `Js_output.make (compile_cases ...)`.
            let [entry] = code_table.as_slice() else {
                return Some(false);
            };
            if in_staticcatch || !no_static_raise_in_handler_like_ocaml(&entry.handler) {
                return Some(false);
            }
            // `append_output declares (append_output lbody handler)`: a
            // finished body wins, otherwise the handler's flag is kept.
            match return_output_finished_like_ocaml(inner_body, true, if_finished)? {
                true => Some(true),
                false => {
                    return_output_finished_like_ocaml(&entry.handler, in_staticcatch, if_finished)
                }
            }
        }
        _ => None,
    }
}

fn return_block_has_multi_test_guard_chain(block: &Block) -> bool {
    // OCaml's `S.if_` folding happens while compiling each conditional
    // (compiler/core/js_stmt_make.ml:244-250). A single top-level test can
    // still be emitted as an `output_finished=True` return block, while
    // guard chains that leave multiple sibling tests in the switch case are
    // the `output_finished=False` shape observed by `to_break_block`.
    count_top_level_if_statements(block) > 1
}

fn count_top_level_if_statements(block: &Block) -> usize {
    block
        .iter()
        .map(count_top_level_if_statements_in_stmt)
        .sum()
}

fn count_top_level_if_statements_in_stmt(stmt: &Statement) -> usize {
    match &stmt.desc {
        StatementDesc::If(_, _, _) => 1,
        StatementDesc::Block(block) => count_top_level_if_statements(block),
        _ => 0,
    }
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
        Lambda::LtryWith(body, _, handler) => {
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
        Lambda::LstaticCatch(body, (_, _), handler) | Lambda::LtryWith(body, _, handler) => {
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
        Lambda::LstaticCatch(body, (_, _), handler) | Lambda::LtryWith(body, _, handler) => {
            add_count(
                lambda_static_raise_count_to_label(body, label, arity),
                lambda_static_raise_count_to_label(handler, label, arity),
            )
        }
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
        Lambda::LstaticCatch(body, (_, _), handler) | Lambda::LtryWith(body, _, handler) => {
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
        | ExpressionDesc::StringIndex(left, right)
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
        ExpressionDesc::Object(dup, props) => {
            if let Some(dup) = dup {
                collect_modules_from_expression(dup, modules);
            }
            for (_, value) in props {
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

#[derive(Clone, Copy)]
pub(crate) enum GroupedSwitchDefault<'a> {
    Complete,
    NonComplete,
    Default(&'a Lambda),
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
        Lambda::Llet(kind, id, value, body) => {
            Lambda::Llet(kind, id, value, Box::new(drop_toplevel_pure_sequence_heads(*body)))
        }
        Lambda::Lletrec(bindings, body) => {
            Lambda::Lletrec(bindings, Box::new(drop_toplevel_pure_sequence_heads(*body)))
        }
        Lambda::Lsequence(first, second) => {
            let second = drop_toplevel_pure_sequence_heads(*second);
            if matches!(*first, Lambda::Lvar(_) | Lambda::Lconst(_) | Lambda::Lfunction(_)) {
                second
            } else {
                Lambda::Lsequence(first, Box::new(second))
            }
        }
        lam => lam,
    }
}

