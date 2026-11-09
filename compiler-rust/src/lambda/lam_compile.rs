//! Lambda -> JS IR compilation.
//!
//! Lowers the optimized Lambda program, held in a [`LamArena`], into the
//! JavaScript IR used by the Rust compiler backend. Compilation reads nodes
//! through `Copy` handles; the arena is borrowed mutably only because a few
//! rewrites (`Lambda.apply` merging, static-raise handler substitution)
//! append nodes.

use ahash::{AHashMap, AHashSet};
use std::sync::Arc;

use crate::cmi::persistent_env::{CmjExportArity, CmjExportConstant};
use crate::context::IdGenerator;
use crate::ident::Ident;
use crate::js_ir::arena::{
    Block, Clause, Expr, ExprKind, JsArena, JsDepsProgram as DepsProgram, JsProgram as Program,
    Stmt, StmtKind, StringClauseInfo, VarDecl,
};
use crate::js_ir::build::{exp as JE, stmt as JS};
use crate::js_ir::op::{IdentInfo, Kind, MutableFlag, Number, PropertyName, UsedStats};
use crate::js_ir::{
    BinOp, CallArity, CallInfo, CallKind, ForDirection, ModuleId, ModulePathResolver,
};
use crate::lambda::arena::{
    ApplyId, CatchId, IdentId, Lam, LamArena, LamList, Node, PrimId, StrSwitchId, SwitchId, View,
};
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
use crate::lambda::lam_analysis::{free_variables, has_exit_code};
use crate::lambda::lam_arity::Arity;
use crate::lambda::lam_closure::is_closed_with_map;
use crate::lambda::lam_compat::{LetKind, SetFieldDbgInfo};
use crate::lambda::lam_compile_context::ExternalArityInfo;
use crate::lambda::lam_constant::{Constant, PointerInfo};
use crate::lambda::lam_primitive::{Cst, Primitive};
use crate::lambda::{ApplyStatus, Lambda, SwitchCaseTag, SwitchKey, TagInfo};
use crate::lambda::{LamLoc, LamLocTable};
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
    max_ident_stamp_in_expression, push_effect_expression, push_s_exp,
    resolve_declared_same_name_self_alias_target, resolve_export_aliases,
    reusable_same_name_export_binding,
};

use super::lam_compile_variant::{empty_switch_case_clause, stable_group_switch_cases};

/// Compilation result for an expression: prelude statements plus a value expression.
#[derive(Debug, Clone)]
pub(crate) struct Compiled {
    pub(crate) prelude: Block,
    pub(crate) expr: Expr,
}

#[derive(Debug, Clone)]
pub(crate) struct StaticHandler {
    pub(crate) label: i32,
    pub(crate) bindings: Vec<Ident>,
    pub(crate) handler: Lam,
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
    handler: Lam,
}

// OCaml's export coercion only reuses direct variables and module-field
// projections while folding `pairs` (`compiler/core/lam_coercion.ml:99-121`).
fn reusable_export_value_candidate(j: &JsArena, value: Expr) -> bool {
    match j.ek(value) {
        ExprKind::Var(_) | ExprKind::Qualified(_) => true,
        ExprKind::StaticIndex(target, _, _) => reusable_export_value_candidate(j, target),
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
fn flatten_nested_caches(
    a: &LamArena,
    outer_label: i32,
    outer_bindings: &[Ident],
    outer_body: Lam,
    outer_handler: Lam,
) -> (Vec<FlatHandler>, Lam) {
    // `acc` matches OCaml's `acc` parameter to `flat_catches`. OCaml starts
    // with `[]` and always absorbs the first (outermost) catch via the
    // `acc = []` branch of the when-clause. In Rust we skip that trivial
    // first step by seeding with the outermost handler.
    let mut acc: Vec<FlatHandler> = vec![FlatHandler {
        label: outer_label,
        bindings: outer_bindings.to_vec(),
        handler: outer_handler,
    }];
    let mut current = outer_body;
    while let View::StaticCatch(inner_body, inner_label, inner_bindings, inner_handler) =
        a.view(current)
    {
        // lam_compile.ml:108-111 — "not (has_exit_code handler (fun exit ->
        // List.exists acc (fun x -> x.label = exit)))". OCaml also has
        // the `acc = []` short-circuit (lam_compile.ml:108) but after
        // our seeding step acc is never empty, so the safety check runs
        // unconditionally.
        if has_exit_code(a, inner_handler, &|exit| {
            acc.iter().any(|h| h.label == exit)
        }) {
            break;
        }
        acc.push(FlatHandler {
            label: inner_label,
            bindings: inner_bindings.to_vec(),
            handler: inner_handler,
        });
        current = inner_body;
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
    fn default_expr(self, j: &mut JsArena) -> Expr {
        JE::bool(matches!(self, Self::Or), j)
    }

    fn test_expr(self, lhs: Expr, j: &mut JsArena) -> Expr {
        match self {
            Self::And => lhs,
            Self::Or => JE::not(lhs, j),
        }
    }

    fn default_lambda(self, a: &mut LamArena) -> Lam {
        match self {
            Self::And => a.false_(),
            Self::Or => a.true_(),
        }
    }
}

fn direct_switch_int(key: SwitchKey) -> i32 {
    match key {
        SwitchKey::Int(value) => value,
        SwitchKey::Constructor(_) => unreachable!("constructor key with direct switch dispatch"),
    }
}

pub(crate) fn short_circuit_primitive(
    primitive: &Primitive,
    args: &[Lam],
) -> Option<(ShortCircuitOp, Lam, Lam)> {
    match (primitive, args) {
        (Primitive::Psequand, [lhs, rhs]) => Some((ShortCircuitOp::And, *lhs, *rhs)),
        (Primitive::Psequor, [lhs, rhs]) => Some((ShortCircuitOp::Or, *lhs, *rhs)),
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
    pub(crate) id_gen: IdGenerator,
    /// The JS IR built by this compiler: `Compiled` values and blocks hold
    /// handles into it, and `compile_deps_program_in_arena` moves it into
    /// the resulting program.
    pub(crate) j: JsArena,
    /// `Js_output.output_finished` of each `Lifthenelse` compiled in a
    /// return continuation, keyed by its `then` branch: only the
    /// `return e ? a : b` arm sets it (lam_compile.ml:1514-1518).
    if_return_finished: AHashMap<Lam, bool>,
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
    hoisted_functions: Vec<crate::lambda::HoistedFunction>,
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
    pub(crate) fn grouped_switch_default(
        &self,
        saturated: bool,
        failaction: Option<Lam>,
    ) -> GroupedSwitchDefault {
        if saturated {
            GroupedSwitchDefault::Complete
        } else if let Some(fallback) = failaction {
            GroupedSwitchDefault::Default(fallback)
        } else {
            GroupedSwitchDefault::NonComplete
        }
    }

    pub(crate) fn grouped_switch_cases<T: Clone, F>(
        &self,
        a: &LamArena,
        cases: &[(T, Lam)],
        default: Option<Lam>,
        merge_cases: F,
    ) -> Vec<(T, Lam, bool)>
    where
        F: Fn(&T, &T) -> bool,
    {
        let filtered: Vec<_> = cases
            .iter()
            .filter(|(_, lam)| default.is_none_or(|default| !a.eq_approx(*lam, default)))
            .map(|(tag, lam)| (tag.clone(), *lam))
            .collect();

        stable_group_switch_cases(a, filtered, merge_cases)
    }

    pub(crate) fn filtered_switch_case_refs<T: Clone>(
        &self,
        a: &LamArena,
        cases: &[(T, Lam)],
        default: Option<Lam>,
    ) -> Vec<(T, Lam)> {
        cases
            .iter()
            .filter(|(_, lam)| default.is_none_or(|default| !a.eq_approx(*lam, default)))
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
            IdGenerator::with_start_stamp(STANDALONE_START_STAMP),
            None,
            false,
            true,
            false,
        )
    }

    fn with_generator_and_options(
        id_gen: IdGenerator,
        module_path_resolver: Option<ModulePathResolver>,
        jsx_preserve: bool,
        check_div_by_zero: bool,
        cross_module_inline: bool,
    ) -> Self {
        Self {
            id_gen,
            j: JsArena::new(),
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
            hoisted_functions: Vec::new(),
            lam_locs: LamLocTable::opaque(),
            if_return_finished: AHashMap::new(),
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
            IdGenerator::new(),
            module_path_resolver,
            jsx_preserve,
            check_div_by_zero,
            cross_module_inline,
        )
    }

    /// A non-method function expression (`E.ocaml_fun`).
    pub(crate) fn function_expr(
        &mut self,
        params: &[Ident],
        body: &[Stmt],
        return_unit: bool,
        async_: bool,
        directive: Option<&str>,
        source_loc: Option<LamLoc>,
    ) -> Expr {
        let params = self.j.ident_list(params);
        let body = self.j.stmt_list(body);
        let directive = directive.map(|d| self.j.str(d));
        let f = self.j.fun_id(crate::js_ir::arena::FunInfo {
            is_method: false,
            params,
            body,
            return_unit,
            async_,
            directive,
        });
        let e = self.j.expr(ExprKind::Fun(f));
        self.j.with_expr_loc(e, source_loc)
    }

    /// Interns a property name into the JS arena.
    pub(crate) fn prop_name(&mut self, name: PropertyName) -> crate::js_ir::arena::PropName {
        match name {
            PropertyName::Lit(s) => crate::js_ir::arena::PropName::Lit(self.j.str(&s)),
            PropertyName::Symbol => crate::js_ir::arena::PropName::Symbol,
        }
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
        self.compile_deps_program_with_possible_required_modules(lam, &AHashSet::new())
    }

    /// Compile an owned Lambda expression into a JS IR program with module metadata.
    pub fn compile_deps_program_owned(&mut self, lam: Lambda) -> DepsProgram {
        self.compile_deps_program(&lam)
    }

    /// Compile a Lambda expression into a JS IR program with module metadata
    /// and additional required modules captured before later coercion/simplify
    /// stages erase the original global-module reference.
    pub fn compile_deps_program_with_possible_required_modules(
        &mut self,
        lam: &Lambda,
        extra_possible_required_modules: &AHashSet<ModuleId>,
    ) -> DepsProgram {
        let mut arena = LamArena::with_capacity(1024);
        let root = arena.import(lam);
        let mut possible_required_modules =
            collect_possible_required_modules_in_arena(&arena, root);
        possible_required_modules.extend(extra_possible_required_modules.iter().cloned());
        self.compile_deps_program_in_arena(arena, root, possible_required_modules)
    }

    /// Owned form of `compile_deps_program_with_possible_required_modules`.
    pub fn compile_deps_program_with_possible_required_modules_owned(
        &mut self,
        lam: Lambda,
        extra_possible_required_modules: &AHashSet<ModuleId>,
    ) -> DepsProgram {
        self.compile_deps_program_with_possible_required_modules(
            &lam,
            extra_possible_required_modules,
        )
    }

    pub fn compile_deps_program_with_collected_possible_required_modules_owned(
        &mut self,
        lam: Lambda,
        possible_required_modules: AHashSet<ModuleId>,
    ) -> DepsProgram {
        let mut arena = LamArena::with_capacity(1024);
        let root = arena.import(&lam);
        drop(lam);
        self.compile_deps_program_in_arena(arena, root, possible_required_modules)
    }

    /// Simplify `lam` in its arena (lam_compile_main.ml:148-200) and lower
    /// the result to a JS program with module metadata.
    pub fn compile_deps_program_in_arena(
        &mut self,
        arena: LamArena,
        lam: Lam,
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
        self.j = JsArena::new();
        let mut simplified =
            crate::timing::measure(crate::timing::Phase::LambdaOptimization, || {
                let _phase = info_span!("compiler.lambda_simplify").entered();
                let jsx_preserve = self.jsx_preserve;
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
                crate::lambda::lam_compile_main::simplify_in_arena(
                    arena,
                    lam,
                    jsx_preserve,
                    &mut external_inline,
                    &mut external_arity,
                )
            });
        crate::lambda::lam_compile_main::add_hoisted_function_aliases(
            &mut simplified,
            &self.hoisted_functions,
        );
        self.cmj_export_arities = crate::lambda::lam_compile_main::cmj_export_arities(&simplified);
        let crate::lambda::lam_compile_main::Simplified {
            arena: mut a,
            lam: root,
            meta,
        } = simplified;
        drop(meta);
        self.cmj_export_constants = collect_cmj_export_constants_from_simplified_lambda(&a, root);
        self.cmj_export_lambdas = if self.cross_module_inline {
            crate::lambda::CmjExportLambdas::export(
                collect_cmj_export_lambdas_from_simplified_lambda(&a, root),
                &self.lam_locs,
            )
        } else {
            Default::default()
        };
        let root = drop_toplevel_pure_sequence_heads(&mut a, root);
        // OCaml's `Ext_ident.create` allocations in lam_compile.ml share the
        // same global `Ident.currentstamp` as the Lambda identifiers entering
        // this phase. See compiler/core/lam_compile.ml:60, 771-782, 911 and
        // 1614. Seed Rust's JS-lowering generator past every existing Lambda
        // stamp before `compile_expr` creates temporary identifiers.
        let js_lowering_start_stamp =
            crate::lambda::lam_beta_reduce::max_ident_stamp_in_lambda(&a, root)
                .max(crate::ident::Ident::current_local_stamp());
        self.id_gen.set_current_stamp(js_lowering_start_stamp);
        crate::ident::Ident::set_current_time(js_lowering_start_stamp);
        crate::timing::measure(crate::timing::Phase::Codegen, || {
            let compiled = {
                let _phase = info_span!("compiler.lambda_compile_expr").entered();
                self.compile_expr(&mut a, root)
            };
            let mut j = std::mem::take(&mut self.j);
            let mut block = compiled.prelude;
            let compiled_expr = compiled.expr;
            let (exports, name_reservations) = {
                let _phase = info_span!("compiler.lambda_exports").entered();
                if let Some(mut exports) =
                    extract_toplevel_exports(&mut j, compiled_expr, &mut block)
                {
                    if block_terminates(&j, &block) {
                        for value in &mut exports.values {
                            *value = JE::undefined(false, &mut j);
                        }
                    }
                    self.coerce_toplevel_exports_with_name_reservations(&mut j, &mut block, exports)
                } else {
                    (vec![], vec![])
                }
            };
            // lam_compile_main.ml `declare_undeclared_exports`: when the
            // toplevel always throws, the groups after the throw are dropped
            // and the identifiers they bind are undeclared. Declare each such
            // exported identifier after the throw.
            if block_terminates(&j, &block) {
                let declared: AHashSet<Ident> = block
                    .iter()
                    .filter_map(|stmt| match j.sk(*stmt) {
                        StmtKind::Variable(v) => Some(j.var(v).ident),
                        _ => None,
                    })
                    .collect();
                for id in &exports {
                    if !declared.contains(id) {
                        let stmt = JS::define(*id, None, LetKind::Strict, &mut j);
                        block.push(stmt);
                    }
                }
            }
            let exports = resolve_export_aliases(&mut j, &block, exports);
            let side_effect = module_side_effect_reason(&a, root);
            drop(a);

            let export_set = exports.iter().copied().collect();
            let mut deps = DepsProgram {
                program: Program {
                    arena: j,
                    block,
                    exports,
                    export_set,
                    name_reservations,
                },
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
                let mut required_modules = OcamlModuleSet::new();
                collect_modules_from_js_block(
                    &deps.program.arena,
                    &deps.program.block,
                    &mut required_modules,
                );
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

    pub(crate) fn source_loc_of_lam(&self, a: &LamArena, lam: Lam) -> Option<LamLoc> {
        if !self.source_map_enabled {
            return None;
        }
        fn find(a: &LamArena, lam: Lam) -> Option<LamLoc> {
            match a.view(lam) {
                View::Apply { info, .. } => Some(info.loc),
                View::Prim(_, _, loc) => Some(loc),
                View::Function { func, .. } => Some(func.loc),
                View::Let(_, _, value, body) => find(a, value).or_else(|| find(a, body)),
                View::LetRec(_, _, body) | View::Sequence(_, body) => find(a, body),
                View::If(_, then_, _) => find(a, then_),
                View::StaticCatch(body, ..) | View::TryWith(body, ..) => find(a, body),
                View::StringSwitch(_, sw) => sw
                    .actions
                    .first()
                    .and_then(|body| find(a, *body))
                    .or_else(|| sw.default.and_then(|d| find(a, d))),
                View::Switch(_, sw) => sw
                    .actions
                    .consts
                    .first()
                    .and_then(|body| find(a, *body))
                    .or_else(|| sw.actions.blocks.first().and_then(|body| find(a, *body)))
                    .or_else(|| sw.actions.fail.and_then(|f| find(a, f))),
                View::StaticRaise(_, args) => args.first().and_then(|x| find(a, *x)),
                View::While(_, body)
                | View::For(_, _, _, _, body)
                | View::ForOf(_, _, body)
                | View::ForAwaitOf(_, _, body)
                | View::Assign(_, body) => find(a, body),
                View::Var(_)
                | View::GlobalModule(_)
                | View::Const(_)
                | View::Break
                | View::Continue => None,
            }
        }
        find(a, lam).filter(|loc| self.mappable_loc(*loc))
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

    fn coerce_toplevel_exports_with_name_reservations(
        &mut self,
        j: &mut JsArena,
        block: &mut Block,
        extracted: ExtractedExports,
    ) -> (Vec<Ident>, Vec<Ident>) {
        let mut max_stamp = max_ident_stamp_in_block(j, block);
        for export in &extracted.exports {
            max_stamp = max_stamp.max(export.stamp());
        }
        for value in &extracted.values {
            max_stamp = max_stamp.max(max_ident_stamp_in_expression(j, *value));
        }
        self.id_gen.set_current_stamp(max_stamp);

        let mut declared = AHashSet::new();
        collect_declared_idents(j, block, &mut declared);
        let block_ended = block_terminates(j, block);

        let mut exports = Vec::with_capacity(extracted.exports.len());
        // OCaml `lam_coercion.ml` can replace an original export id with a
        // same-name different-stamp target (`compiler/core/lam_coercion.ml:100-110`)
        // or with `Ident.rename original_export_id`
        // (`compiler/core/lam_coercion.ml:140-156`). The JS printer then sees
        // the original id as occupying the base name and prints the selected
        // local as `$1`; carry those original ids as explicit reservations.
        let mut name_reservations = Vec::new();
        let mut rebound_exports = Vec::new();

        // OCaml's `compiler/core/lam_coercion.ml:82-121` folds over export ids
        // and lambda values, only allocating a renamed export when the branch
        // actually emits a rebound group (`compiler/core/lam_coercion.ml:113-120`
        // and `compiler/core/lam_coercion.ml:140-156`).
        for index in 0..extracted.exports.len() {
            let export = &extracted.exports[index];
            let value = extracted.values[index];
            let later_exports = &extracted.exports[index + 1..];
            let value_var = match j.ek(value) {
                ExprKind::Var(target) => Some(j.ident(target)),
                _ => None,
            };
            let exact_self_export = value_var.is_some_and(|target| target.same(export));
            // OCaml's `Lvar id` branch only changes the export list/set and
            // emits no rebound group when the value is already the same
            // physical identifier (`compiler/core/lam_coercion.ml:99-111`).
            // Keep that source binding in place instead of tail-moving it.
            if !exact_self_export
                && let Some((late_value, property)) =
                    move_same_name_export_alias_to_export_tail(j, block, export, value)
            {
                exports.push(*export);
                rebound_exports.push(JS::define(*export, Some(late_value), property, j));
                continue;
            }
            if let Some(target) = value_var
                && target.name() == export.name()
            {
                if declared.contains(export) {
                    let selected =
                        if keeps_declared_same_name_function_export_alias(j, block, export) {
                            *export
                        } else {
                            resolve_declared_same_name_self_alias_target(j, block, export)
                                .unwrap_or(*export)
                        };
                    if !selected.same(export) {
                        name_reservations.push(*export);
                    }
                    exports.push(selected);
                    continue;
                }
                if declared.contains(&target) {
                    let start = JE::var(target, j);
                    let resolved =
                        resolve_tail_move_replacement_expression(j, block, start, &target, false);
                    let selected = match j.ek(resolved) {
                        ExprKind::Var(resolved_target) => j.ident(resolved_target),
                        _ => target,
                    };
                    if !selected.same(export) {
                        name_reservations.push(*export);
                    }
                    exports.push(selected);
                    continue;
                }
            }
            if matches!(j.ek(value), ExprKind::Undefined { .. })
                && ((declared.contains(export)
                    && can_reuse_existing_undefined_export_binding(j, block, export))
                    || block_ended)
            {
                exports.push(*export);
                continue;
            }
            if reusable_export_value_candidate(j, value) {
                // Same OCaml export fold as above: reusable same-name bindings
                // only arise from variable/module-field export values. See
                // compiler/core/lam_coercion.ml:99-121.
                if let Some((late_value, property)) =
                    move_reused_same_name_export_binding_to_export_tail(j, block, export, value)
                {
                    exports.push(*export);
                    rebound_exports.push(JS::define(*export, Some(late_value), property, j));
                    continue;
                }
                if keeps_declared_same_name_reusable_export_binding(j, block, export, value) {
                    exports.push(*export);
                    continue;
                }
                if let Some(reused) = reusable_same_name_export_binding(j, block, export, value) {
                    exports.push(reused);
                    continue;
                }
            }
            if let Some(inserted_export) = insert_rebound_export_before_equivalent_later_binding(
                j,
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
            let property = if value_var.is_some() {
                LetKind::Alias
            } else {
                LetKind::Strict
            };
            exports.push(rebound);
            rebound_exports.push(JS::define(rebound, Some(value), property, j));
        }

        // OCaml compiler/core/lam_coercion.ml:160-172 folds original flattened
        // groups back in front of rebound export groups and preserves that
        // order. Generated JS observes this, so these late bindings must not be
        // sorted by export-list order.
        block.extend(rebound_exports);
        (exports, name_reservations)
    }

    fn compile_apply_call(
        &mut self,
        a: &mut LamArena,
        func: Lam,
        args: LamList,
        info: ApplyId,
    ) -> Compiled {
        let mut compiled = self.compile_apply_call_inner(a, func, args, info);
        if self.j.expr_loc(compiled.expr).is_none() {
            let loc = self.source_loc(&a.apply_payload(info).info.loc);
            compiled.expr = self.j.with_expr_loc(compiled.expr, loc);
        }
        compiled
    }

    fn compile_apply_call_inner(
        &mut self,
        a: &mut LamArena,
        func: Lam,
        args: LamList,
        info: ApplyId,
    ) -> Compiled {
        let apply = a.apply_payload(info).clone();
        if apply.info.status == ApplyStatus::Na
            && let Node::Apply {
                func: inner_func,
                args: inner_args,
                info: inner_info,
            } = a.node(func)
        {
            let inner = a.apply_payload(inner_info);
            if inner.info.status == ApplyStatus::Na {
                let mut ap_info = apply.info.clone();
                if ap_info.inlined != inner.info.inlined {
                    ap_info.inlined = inner.info.inlined;
                }
                let mut merged_args = a.list_small(inner_args);
                merged_args.extend_from_slice(a.list(args));
                let merged = a.apply(inner_func, &merged_args, ap_info, apply.transformed_jsx);
                return self.compile_expr(a, merged);
            }
        }

        if let Some(compiled) = self.compile_external_field_apply(a, func, args, info) {
            return compiled;
        }

        let mut prelude = vec![];
        let func = self.compile_expr(a, func);
        prelude.extend(func.prelude);
        let mut compiled_args = Vec::new();
        for arg in a.list_small(args) {
            let compiled = self.compile_expr(a, arg);
            prelude.extend(compiled.prelude);
            compiled_args.push(compiled.expr);
        }

        Compiled {
            prelude,
            expr: JE::call(
                func.expr,
                &compiled_args,
                call_info_of_apply_status(apply.transformed_jsx, apply.info.status),
                &mut self.j,
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

    fn module_field_apply_target(
        &self,
        a: &LamArena,
        lam: Lam,
    ) -> Option<(ModuleId, crate::name::Name)> {
        let (Primitive::Pfield(_, crate::lambda::FieldDbgInfo::Module { name }), [m], _) =
            a.as_prim(lam)?
        else {
            return None;
        };
        let Node::GlobalModule(id) = a.node(*m) else {
            return None;
        };
        Some((
            ModuleId {
                id: a.ident(id),
                kind: Kind::Ml,
                dynamic_import: false,
            },
            *name,
        ))
    }

    fn compile_external_field_apply(
        &mut self,
        a: &mut LamArena,
        func: Lam,
        args: LamList,
        info: ApplyId,
    ) -> Option<Compiled> {
        let (module, field_name) = self.module_field_apply_target(a, func)?;

        if let Some(Lambda::Lfunction(f)) =
            self.resolve_cmj_module_field_lambda(&module, field_name.as_str())
            && f.params.len() == a.list_len(args)
            && lam_analysis::attr_can_be_inlined(&f.attr)
        {
            // OCaml compiler/core/lam_compile.ml:275-290 inlines closed
            // `persistent_closed_lambda` functions from `.cmj` during
            // `compile_external_field_apply`, then beta-reduces them with
            // Lam_beta_reduce.propagate_beta_reduce_with_map.
            let body = a.import(&f.body);
            let exports = ahash::AHashSet::new();
            let (_, param_map) = is_closed_with_map(a, &exports, &f.params, body);
            let mut ident_tbl = crate::lambda::lam_stats::IdentTable::new();
            let arg_list = a.list_small(args);
            let reduced = crate::lambda::lam_beta_reduce::propagate_beta_reduce_with_map(
                a,
                &mut ident_tbl,
                &self.id_gen,
                &param_map,
                &f.params,
                body,
                &arg_list,
            );
            return Some(self.compile_expr(a, reduced));
        }

        let known_arity = self.resolve_cmj_module_field_arity(&module, field_name.as_str());
        let mut prelude = Vec::new();
        let mut compiled_args = Vec::with_capacity(a.list_len(args));
        for arg in a.list_small(args) {
            let compiled = self.compile_expr(a, arg);
            prelude.extend(compiled.prelude);
            compiled_args.push(compiled.expr);
        }

        let apply = a.apply_payload(info);
        let func = JE::qualified(module, Some(field_name.to_string()), &mut self.j);
        let expr = match apply.info.status {
            // compiler/core/lam_compile.ml:303-309 keeps the explicit
            // App_infer_full/App_uncurry call info instead of consulting CMJ
            // arity. In particular App_uncurry stays Call_na.
            ApplyStatus::InferFull | ApplyStatus::Uncurry => JE::call(
                func,
                &compiled_args,
                call_info_of_apply_status(apply.transformed_jsx, apply.info.status),
                &mut self.j,
            ),
            // compiler/core/lam_compile.ml:310-316 uses
            // `ident_info.arity`; a known `Single` arity is lowered through
            // `apply_with_arity`, while missing/Submodule arity uses dummy
            // Call_na information.
            ApplyStatus::Na => match known_arity {
                Some(arity) if !arity.is_na() => self.apply_with_arity(func, arity, compiled_args),
                _ => JE::call(func, &compiled_args, CallInfo::default(), &mut self.j),
            },
        };
        Some(Compiled { prelude, expr })
    }

    fn apply_with_arity(&mut self, func: Expr, arity: Arity, args: Vec<Expr>) -> Expr {
        // Direct port of compiler/core/lam_compile.ml:42-79. The OCaml helper
        // repeatedly consumes known arity groups, emits `ml_full_call` for each
        // saturated group, eta-expands duplicable partial applications, and
        // falls back to dummy Call_na otherwise.
        fn aux(
            id_gen: &IdGenerator,
            j: &mut JsArena,
            func: Expr,
            mut arities: crate::lambda::lam_arity::Arities,
            args: Vec<Expr>,
        ) -> Expr {
            let len = args.len();
            if len == 0 {
                return func;
            }

            if arities.is_empty() {
                return JE::call(func, &args, CallInfo::default(), j);
            }

            let mut x = arities.remove(0);
            if x == 0 {
                x = 1;
            }
            let x_len = x as usize;
            let full = CallInfo {
                kind: CallKind::MlCall,
                arity: CallArity::Full,
                ..CallInfo::default()
            };
            if len >= x_len {
                let call = JE::call(func, &args[..x_len], full, j);
                aux(id_gen, j, call, arities, args[x_len..].to_vec())
            } else if args.iter().all(|arg| js_expr_no_side_effects(j, *arg)) {
                let missing = x_len - len;
                let params: Vec<Ident> = (0..missing).map(|_| id_gen.create("param")).collect();
                let mut full_args = args;
                full_args.extend(params.iter().map(|p| JE::var(*p, j)));
                let call = JE::call(func, &full_args, full, j);
                let body = [JS::return_(call, j)];
                crate::lambda::js_exp_make::fun_expr(false, &params, &body, false, false, j)
            } else {
                JE::call(func, &args, CallInfo::default(), j)
            }
        }

        aux(&self.id_gen, &mut self.j, func, arity.extract_arity(), args)
    }

    fn try_statement(&mut self, body: Block, exn: &Ident, handler: Block) -> Stmt {
        JS::try_(&body, Some((*exn, &handler)), None, &mut self.j)
    }

    /// The `Psetfield` field writes of `copy_id` that `lam` is a sequence of,
    /// ending in `copy_id` itself, as (primitive, value) pairs.
    fn collect_record_spread_overrides(
        a: &LamArena,
        copy_id: &Ident,
        lam: Lam,
        overrides: &mut Vec<(PrimId, Lam)>,
    ) -> bool {
        match a.node(lam) {
            Node::Sequence(set, rest) => match a.node(set) {
                Node::Prim { args, info }
                    if matches!(a.prim_payload(info).primitive, Primitive::Psetfield(_, _))
                        && matches!(a.list(args), [v, _] if a.as_var(*v).is_some_and(|id| id == *copy_id)) =>
                {
                    overrides.push((info, a.list(args)[1]));
                    Self::collect_record_spread_overrides(a, copy_id, rest, overrides)
                }
                _ => false,
            },
            Node::Var(id) => a.ident(id) == *copy_id,
            _ => false,
        }
    }

    /// Port of `try_compile_record_spread` from
    /// `compiler/core/lam_compile.ml`: collapse a duplicated record followed
    /// by mutations of that copy into one spread object literal. Compiling the
    /// initializer and overrides from left to right preserves source effects.
    fn try_compile_record_spread(
        &mut self,
        a: &mut LamArena,
        copy_id: &Ident,
        value: Lam,
        body: Lam,
    ) -> Option<Compiled> {
        let (Primitive::Pduprecord, [init], loc) = a.as_prim(value)? else {
            return None;
        };
        let (init, loc) = (*init, loc);

        let mut overrides = Vec::new();
        if !Self::collect_record_spread_overrides(a, copy_id, body, &mut overrides) {
            return None;
        }

        let Compiled {
            mut prelude,
            expr: init_expr,
        } = self.compile_expr(a, init);
        let mut props = Vec::with_capacity(overrides.len());
        for (field, override_lam) in overrides {
            let compiled = self.compile_expr(a, override_lam);
            prelude.extend(compiled.prelude);
            let Primitive::Psetfield(_, field_info) = &a.prim_payload(field).primitive else {
                unreachable!("collected field writes are Psetfield")
            };
            props.push((
                PropertyName::Lit(SetFieldDbgInfo::name(field_info).to_string()),
                compiled.expr,
            ));
        }

        // OCaml's fold builds object properties by prepending each compiled
        // override, so the final JS object stores them in reverse source order.
        props.reverse();
        Some(Compiled {
            prelude,
            // lam_compile.ml:1813-1815: `with_source_loc loc (E.obj ~dup:init_val props)`.
            expr: {
                let props: Vec<_> = props
                    .into_iter()
                    .map(|(name, value)| (self.prop_name(name), value))
                    .collect();
                let props = self.j.prop_list(&props);
                let obj = JE::new(ExprKind::Object(Some(init_expr), props), &mut self.j);
                let loc = self.source_loc(&loc);
                self.j.with_expr_loc(obj, loc)
            },
        })
    }

    /// Whether `body` continues a top-level group spine: OCaml compiles each
    /// `Single`/`Recursive`/`Nop` group with a fresh `loop_label_counter`
    /// (`lam_compile_main.ml`), and a binding is top-level exactly when its
    /// body is another group or the module-export block.
    fn continues_toplevel_spine(a: &LamArena, body: Lam) -> bool {
        match a.view(body) {
            View::Let(..) | View::LetRec(..) | View::Sequence(..) => true,
            View::Prim(primitive, _, _) => {
                matches!(
                    primitive,
                    Primitive::Pmakeblock(TagInfo::ModuleExport(_), _)
                )
            }
            _ => false,
        }
    }

    pub(crate) fn compile_expr(&mut self, a: &mut LamArena, lam: Lam) -> Compiled {
        match a.node(lam) {
            Node::Var(id) => Compiled {
                prelude: vec![],
                expr: JE::var(a.ident(id), &mut self.j),
            },
            Node::GlobalModule(id) => {
                let module = ModuleId {
                    id: a.ident(id),
                    kind: Kind::Ml,
                    dynamic_import: false,
                };
                Compiled {
                    prelude: vec![],
                    expr: JE::qualified(module, None, &mut self.j),
                }
            }
            Node::Const(cst) => Compiled {
                prelude: vec![],
                expr: Self::compile_constant(a.constant(cst), &mut self.j),
            },
            Node::Apply { func, args, info } => {
                let mut compiled = self.compile_apply_call(a, func, args, info);
                if self.j.expr_loc(compiled.expr).is_none() {
                    let loc = self.source_loc(&a.apply_payload(info).info.loc);
                    compiled.expr = self.j.with_expr_loc(compiled.expr, loc);
                }
                compiled
            }
            Node::Function { body, info } => {
                if let Some(expr) = self.compile_eta_wrapped_runtime_alias(a, info, body) {
                    return Compiled {
                        prelude: vec![],
                        expr,
                    };
                }
                let f = a.func_payload(info);
                let (return_unit, async_, directive, loc) = (
                    f.attr.return_unit,
                    f.attr.async_,
                    f.attr.directive.clone(),
                    f.loc,
                );
                let params = if f.attr.one_unit_arg {
                    vec![]
                } else {
                    a.params(info).to_vec()
                };
                let body = self
                    .try_compile_identity_module_return_expr(a, body)
                    .map(|expr| vec![JS::return_(expr, &mut self.j)])
                    .unwrap_or_else(|| {
                        // Mirror OCaml: nested function bodies start with a
                        // fresh `switch_depth = 0; loop_stack = []`.
                        self.with_function_scope(|this| {
                            this.with_return_unit_context(return_unit, |that| {
                                that.compile_return_block(a, body)
                            })
                        })
                    });
                // lam_compile.ml:1827-1829: `with_source_loc loc (E.ocaml_fun ...)`.
                let source_loc = self.source_loc(&loc);
                let expr = self.function_expr(
                    &params,
                    &body,
                    return_unit,
                    async_,
                    directive.as_deref(),
                    source_loc,
                );
                Compiled {
                    prelude: vec![],
                    expr,
                }
            }
            Node::Let {
                kind,
                id,
                value,
                body,
            } => {
                let id = a.ident(id);
                if let Some(compiled) = self.try_compile_record_spread(a, &id, value, body) {
                    return compiled;
                }

                // Mirror OCaml's per-Single counter reset
                // (`lam_compile_main.ml`): each top-level binding compiles
                // its RHS with `loop_label_counter = ref 0`. Inner Llets
                // inside an expression keep the surrounding counter (so
                // the OCaml flow naturally inherits across function bodies
                // within one Single group).
                let mut prelude = if Self::continues_toplevel_spine(a, body) {
                    self.with_fresh_loop_label_counter(|this| {
                        this.compile_let_binding(a, kind, &id, value)
                    })
                } else {
                    self.compile_let_binding(a, kind, &id, value)
                };
                let body_compiled = self.compile_expr(a, body);
                if block_terminates(&self.j, &prelude) {
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
            Node::LetRec { ids, values, body } => {
                let bindings = letrec_bindings(a, ids, values);
                // Same as Llet: per-Recursive group, OCaml resets
                // `loop_label_counter` (`lam_compile_main.ml:77`).
                let mut prelude = if Self::continues_toplevel_spine(a, body) {
                    self.with_fresh_loop_label_counter(|this| {
                        this.compile_recursive_bindings(a, &bindings)
                    })
                } else {
                    self.compile_recursive_bindings(a, &bindings)
                };
                let body_compiled = self.compile_expr(a, body);
                prelude.extend(body_compiled.prelude);
                Compiled {
                    prelude,
                    expr: body_compiled.expr,
                }
            }
            Node::Prim { args, info } => {
                if let Some((op, lhs, rhs)) =
                    short_circuit_primitive(&a.prim_payload(info).primitive, a.list(args))
                {
                    return self.compile_short_circuit_expr(a, op, lhs, rhs);
                }
                if let Some(compiled) = self.compile_hoisted_external_field(a, info, args) {
                    return compiled;
                }
                let mut compiled = self.compile_primitive(a, info, args);
                // lam_compile.ml:1615-1634: only `compile_primitive_default`
                // wraps its result in `with_source_loc loc`.
                let p = a.prim_payload(info);
                if self.j.expr_loc(compiled.expr).is_none()
                    && primitive_uses_default_compilation(a, &p.primitive, a.list(args))
                {
                    let loc = self.source_loc(&p.loc);
                    compiled.expr = self.j.with_expr_loc(compiled.expr, loc);
                }
                compiled
            }
            Node::Switch {
                scrut,
                actions,
                info,
            } => self.compile_switch(a, scrut, Sw { actions, info }),
            Node::StringSwitch {
                scrut,
                actions,
                info,
            } => self.compile_string_switch(a, scrut, StrSw { actions, info }),
            Node::StaticRaise { label, args } => {
                if let Some(prelude) = self.compile_static_raise_jump_block(a, label, args) {
                    return Compiled {
                        prelude,
                        expr: JE::undefined(false, &mut self.j),
                    };
                }
                if let Some(handler) = self.resolve_static_raise(a, label, args) {
                    return self.compile_expr(a, handler);
                }
                let expr = if let Some(&arg) = a.list(args).first() {
                    self.compile_expr(a, arg).expr
                } else {
                    JE::undefined(false, &mut self.j)
                };
                Compiled {
                    prelude: vec![JS::throw(expr, &mut self.j)],
                    expr: JE::undefined(false, &mut self.j),
                }
            }
            Node::StaticCatch {
                body,
                handler,
                info,
            } => {
                let label = a.catch_payload(info).label;
                let bindings = catch_bindings(a, info);
                // OCaml's `compile_staticcatch` (lam_compile.ml:937-1017)
                // gates pseudo-jmp on `EffectCall (Maybe_tail_is_return
                // (Tail_with_name {in_staticcatch=false}))`. `NeedValue _`,
                // which is what `compile_expr` models, takes the
                // explicit-jump arm at lam_compile.ml:978-993 unconditionally
                // (it allocates a tmp, assigns through it, then dispatches).
                // Take that path here; the `with_static_handler` inline
                // shortcut has no OCaml analog for NeedValue.
                let (handlers, flat_body) =
                    flatten_nested_caches(a, label, &bindings, body, handler);
                if handlers.len() > 1 {
                    // lam_compile.ml:935 calls `flatten_nested_caches` at the
                    // top of `compile_staticcatch`; a `code_table` with >1
                    // entries goes through the multi-handler explicit-jump
                    // arm for `NeedValue` at lam_compile.ml:978-988.
                    // OCaml NeedValue staticcatch allocates `Ext_ident.create_tmp ()`
                    // for the result (compiler/core/lam_compile.ml:1027-1034).
                    let result = self.fresh_tmp_ident();
                    let mut prelude = vec![JS::variable(
                        VarDecl {
                            ident: result,
                            value: None,
                            property: LetKind::Strict,
                            ident_info: IdentInfo::default(),
                        },
                        &mut self.j,
                    )];
                    prelude.extend(self.compile_multi_staticcatch_assignment_block(
                        a, &result, &handlers, flat_body,
                    ));
                    Compiled {
                        prelude,
                        expr: JE::var(result, &mut self.j),
                    }
                } else {
                    self.compile_staticcatch_expr(a, label, &bindings, body, handler)
                }
            }
            Node::TryWith { body, id, handler } => {
                let exn = a.ident(id);
                let result = self.fresh_tmp_ident();
                let mut prelude = vec![JS::variable(
                    VarDecl {
                        ident: result,
                        value: None,
                        property: LetKind::Variable,
                        ident_info: IdentInfo::default(),
                    },
                    &mut self.j,
                )];
                let body_block = self.compile_assign_to_target_block(a, &result, body);
                let handler_block = self.compile_assign_to_target_block(a, &result, handler);
                prelude.push(self.try_statement(body_block, &exn, handler_block));
                Compiled {
                    prelude,
                    expr: JE::var(result, &mut self.j),
                }
            }
            Node::If { cond, then_, else_ } => {
                let cond_compiled = self.compile_expr(a, cond);
                let mut prelude = cond_compiled.prelude;
                let then_compiled = self.compile_expr(a, then_);
                let else_compiled = self.compile_expr(a, else_);
                if then_compiled.prelude.is_empty() && else_compiled.prelude.is_empty() {
                    Compiled {
                        prelude,
                        expr: JE::cond(
                            cond_compiled.expr,
                            then_compiled.expr,
                            else_compiled.expr,
                            &mut self.j,
                        ),
                    }
                } else {
                    let tmp = self.fresh_tmp_ident();
                    let then_block = self.compile_assign_to_target_block(a, &tmp, then_);
                    let else_block = self.compile_assign_to_target_block(a, &tmp, else_);
                    prelude.push(JS::variable(
                        VarDecl {
                            ident: tmp,
                            value: None,
                            property: LetKind::Strict,
                            ident_info: IdentInfo::default(),
                        },
                        &mut self.j,
                    ));
                    prelude.push(JS::if_(
                        cond_compiled.expr,
                        &then_block,
                        &else_block,
                        &mut self.j,
                    ));
                    Compiled {
                        prelude,
                        expr: JE::var(tmp, &mut self.j),
                    }
                }
            }
            Node::Sequence(first, second) => {
                // Mirror OCaml's per-Nop counter reset: a top-level
                // sequence (its tail is itself a top-level construct)
                // compiles its head with a fresh `loop_label_counter`,
                // matching `Lam_compile_main.compile_lambda` for `Nop`
                // groups (`lam_compile_main.ml:86`).
                let head = if Self::continues_toplevel_spine(a, second) {
                    self.with_fresh_loop_label_counter(|this| this.compile_effect_output(a, first))
                } else {
                    self.compile_effect_output(a, first)
                };
                // OCaml's Lbreak / Lcontinue compile to `Js_output.make ...
                // ~output_finished:True` (compiler/core/lam_compile.ml:1928,
                // 1943). `Js_output.append_output` then drops the tail's
                // contribution when the head is finished. Mirror that here:
                // when the sequence head is an exit terminator, skip typing
                // the tail entirely — its statements are unreachable.
                if lambda_is_unconditional_exit(a, first) {
                    return head;
                }
                let tail = self.compile_expr(a, second);
                self.append_effect_output(head, tail)
            }
            Node::While(cond, body) => {
                let cond_compiled = self.compile_expr(a, cond);
                let cond_expr = block_with_return_expr_iife(
                    cond_compiled.prelude,
                    cond_compiled.expr,
                    &mut self.j,
                );
                // Mirror OCaml's `push_loop` (compiler/core/lam_compile.ml):
                // a fresh loop frame is pushed before compiling the body;
                // its label is filled in lazily if a nested switch needs
                // labeled break/continue.
                self.push_loop();
                let body_block = self.compile_block(a, body);
                let label = self.pop_loop();
                Compiled {
                    prelude: vec![JS::while_(
                        label.as_deref(),
                        cond_expr,
                        &body_block,
                        &mut self.j,
                    )],
                    expr: JE::undefined(false, &mut self.j),
                }
            }
            Node::For { dir, id, kids } => {
                let (start, end, body) = a.for_parts(kids);
                let var = a.ident(id);
                self.compile_for_loop(a, &var, start, end, &dir, body)
            }
            // Upstream #7887: `for ... of` / `for await ... of` lower to a
            // dedicated JS for-of statement. The body is compiled with a
            // fresh loop frame pushed (so nested break/continue resolve to
            // this loop) and `switch_depth = 0` reset to match OCaml's
            // `compile_for_of` (`compiler/core/lam_compile.ml`).
            Node::ForOf { id, iter, body } => {
                let var = a.ident(id);
                self.compile_for_of(a, &var, iter, body, /*await=*/ false)
            }
            Node::ForAwaitOf { id, iter, body } => {
                let var = a.ident(id);
                self.compile_for_of(a, &var, iter, body, /*await=*/ true)
            }
            Node::Break => {
                // OCaml: see compiler/core/lam_compile.ml `Lbreak` arm.
                // When inside a switch, target the enclosing loop with a
                // labeled `break` so we don't break out of the switch.
                assert!(
                    !self.loop_stack.is_empty(),
                    "Lbreak outside a loop — typecore should reject this"
                );
                let stmt = if self.switch_depth > 0 {
                    let label = self.ensure_current_loop_label();
                    JS::break_(Some(&label), &mut self.j)
                } else {
                    JS::break_(None, &mut self.j)
                };
                Compiled {
                    prelude: vec![stmt],
                    expr: JE::undefined(false, &mut self.j),
                }
            }
            Node::Continue => {
                assert!(
                    !self.loop_stack.is_empty(),
                    "Lcontinue outside a loop — typecore should reject this"
                );
                let stmt = if self.switch_depth > 0 {
                    let label = self.ensure_current_loop_label();
                    JS::continue_(Some(&label), &mut self.j)
                } else {
                    JS::continue_(None, &mut self.j)
                };
                Compiled {
                    prelude: vec![stmt],
                    expr: JE::undefined(false, &mut self.j),
                }
            }
            Node::Assign { id, value } => {
                let id = a.ident(id);
                let compiled = self.compile_expr(a, value);
                let mut prelude = compiled.prelude;
                if !block_terminates(&self.j, &prelude) {
                    prelude.push(JS::exp(
                        JE::bin(
                            BinOp::Eq,
                            JE::var(id, &mut self.j),
                            compiled.expr,
                            &mut self.j,
                        ),
                        &mut self.j,
                    ));
                }
                Compiled {
                    prelude,
                    expr: JE::undefined(false, &mut self.j),
                }
            }
        }
    }

    fn compile_block(&mut self, a: &mut LamArena, lam: Lam) -> Block {
        self.compile_effect_block(a, lam)
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
        a: &mut LamArena,
        var: &Ident,
        start: Lam,
        end: Lam,
        dir: &crate::lambda::DirectionFlag,
        body: Lam,
    ) -> Compiled {
        let start_compiled = self.compile_expr(a, start);
        let (finish, direction) = lower_ocaml_for_range_direction(a, dir, end);
        let finish_compiled = self.compile_expr(a, finish);
        // Push a fresh loop frame before compiling the body so any
        // nested `Lbreak`/`Lcontinue` resolves against this for-loop.
        // See OCaml `push_loop` in compiler/core/lam_compile.ml.
        self.push_loop();
        let body_block = self.compile_block(a, body);
        let loop_label = self.pop_loop();

        let mut prelude = start_compiled.prelude;
        if block_terminates(&self.j, &prelude) {
            return Compiled {
                prelude,
                expr: JE::undefined(false, &mut self.j),
            };
        }

        let push_loop = |j: &mut JsArena, block: &mut Block, init: Option<Expr>, finish: Expr| {
            block.push(JS::for_range(
                loop_label.as_deref(),
                init,
                finish,
                *var,
                direction,
                &body_block,
                j,
            ));
        };

        if finish_compiled.prelude.is_empty() {
            push_loop(
                &mut self.j,
                &mut prelude,
                Some(start_compiled.expr),
                finish_compiled.expr,
            );
        } else if js_expr_no_side_effects(&self.j, start_compiled.expr) {
            prelude.extend(finish_compiled.prelude);
            if block_terminates(&self.j, &prelude) {
                return Compiled {
                    prelude,
                    expr: JE::undefined(false, &mut self.j),
                };
            }
            push_loop(
                &mut self.j,
                &mut prelude,
                Some(start_compiled.expr),
                finish_compiled.expr,
            );
        } else {
            prelude.push(JS::variable(
                VarDecl {
                    ident: *var,
                    value: Some(start_compiled.expr),
                    property: LetKind::Variable,
                    ident_info: IdentInfo::default(),
                },
                &mut self.j,
            ));
            prelude.extend(finish_compiled.prelude);
            if block_terminates(&self.j, &prelude) {
                return Compiled {
                    prelude,
                    expr: JE::undefined(false, &mut self.j),
                };
            }
            push_loop(&mut self.j, &mut prelude, None, finish_compiled.expr);
        }

        Compiled {
            prelude,
            expr: JE::undefined(false, &mut self.j),
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
        a: &mut LamArena,
        var: &Ident,
        iterable: Lam,
        body: Lam,
        await_kw: bool,
    ) -> Compiled {
        let iterable_compiled = self.compile_expr(a, iterable);
        let mut prelude = iterable_compiled.prelude;
        if block_terminates(&self.j, &prelude) {
            return Compiled {
                prelude,
                expr: JE::undefined(false, &mut self.j),
            };
        }

        // Match OCaml: when the loop variable is not actually used by the
        // body, emit a fresh placeholder so the source name doesn't leak.
        let body_fvs = free_variables(a, body);
        let emitted_id = if body_fvs.contains(var) {
            *var
        } else if await_kw {
            self.fresh_ident("_for_await_of")
        } else {
            self.fresh_ident("_for_of")
        };

        self.push_loop();
        let body_block = self.compile_block(a, body);
        let label = self.pop_loop();

        let stmt = if await_kw {
            JS::for_of(
                true,
                label.as_deref(),
                emitted_id,
                iterable_compiled.expr,
                &body_block,
                &mut self.j,
            )
        } else {
            JS::for_of(
                false,
                label.as_deref(),
                emitted_id,
                iterable_compiled.expr,
                &body_block,
                &mut self.j,
            )
        };
        prelude.push(stmt);

        Compiled {
            prelude,
            expr: JE::undefined(false, &mut self.j),
        }
    }

    fn compile_recursive_bindings(&mut self, a: &mut LamArena, bindings: &[(Ident, Lam)]) -> Block {
        let dependencies = recursive_binding_dependencies(a, bindings);
        let mut block = vec![];

        for group in recursive_binding_groups(a, bindings, &dependencies) {
            if let [index] = group.as_slice()
                && !dependencies[*index].contains(index)
            {
                let (id, expr) = bindings[*index];
                // OCaml's `compile_recursive_let` (lam_compile.ml:380-486)
                // routes every non-self-referencing binding through
                // `Declare(Alias, id)`. Using `Strict` here breaks the
                // `js_pass_flatten_and_mark_dead` skip for all-deep-constant
                // alias bindings (lam_pass_lets_dce.ml + the implicit
                // skip behind the Variable arm).
                block.extend(self.compile_let_binding(a, LetKind::Alias, &id, expr));
                continue;
            }

            let recursive_functions = recursive_function_bindings_in_group(a, bindings, &group);
            let recursive_function_tail_targets = direct_recursive_function_tail_targets_with_group(
                a,
                bindings,
                &group,
                &recursive_functions,
            );
            let recursive_function_ids: AHashSet<_> =
                recursive_function_tail_targets.keys().cloned().collect();
            let mut declarations = vec![];
            let mut effects = vec![];

            for &index in &group {
                let (id, expr) = bindings[index];
                let (binding_decls, binding_effects) = self.compile_recursive_binding(
                    a,
                    &id,
                    expr,
                    bindings,
                    &group,
                    recursive_function_tail_targets
                        .get(&id)
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

    #[allow(clippy::too_many_arguments)]
    fn compile_recursive_binding(
        &mut self,
        a: &mut LamArena,
        id: &Ident,
        expr: Lam,
        all_bindings: &[(Ident, Lam)],
        group: &[usize],
        tail_targets: &[Ident],
        recursive_functions: &AHashMap<Ident, Lam>,
        recursive_function_ids: &AHashSet<Ident>,
    ) -> (Block, Block) {
        if let Some(func) = recursive_function_binding_value(a, expr) {
            return (
                vec![],
                vec![JS::variable(
                    VarDecl {
                        ident: *id,
                        value: Some(self.compile_recursive_function_expr(
                            a,
                            id,
                            func,
                            tail_targets,
                        )),
                        property: LetKind::Alias,
                        ident_info: IdentInfo::default(),
                    },
                    &mut self.j,
                )],
            );
        }

        if let Some(target) = recursive_function_binding_alias_target(a, expr, recursive_functions)
            && recursive_function_ids
                .iter()
                .any(|function_id| target.same(function_id))
        {
            return (
                vec![],
                vec![JS::variable(
                    VarDecl {
                        ident: *id,
                        value: Some(JE::var(target, &mut self.j)),
                        property: LetKind::Alias,
                        ident_info: IdentInfo::default(),
                    },
                    &mut self.j,
                )],
            );
        }

        if group.len() == 1
            && let Some(block) =
                self.try_compile_recursive_singleton_binding_without_placeholder(a, id, expr)
        {
            return (vec![], block);
        }

        let makeblock = match a.view(expr) {
            View::Prim(Primitive::Pmakeblock(tag_info, _), args, _) => Some((
                tag_info.clone(),
                args.iter()
                    .all(|arg| matches!(a.node(*arg), Node::Function { .. } | Node::Const(_))),
            )),
            _ => None,
        };
        match makeblock {
            Some((_, true)) => {
                let compiled = self.compile_expr(a, expr);
                let mut effects = compiled.prelude;
                if !block_terminates(&self.j, &effects) {
                    effects.push(JS::variable(
                        VarDecl {
                            ident: *id,
                            value: Some(compiled.expr),
                            property: LetKind::Alias,
                            ident_info: IdentInfo::default(),
                        },
                        &mut self.j,
                    ));
                }
                (vec![], effects)
            }
            Some((tag_info, false)) => {
                if let Some(effects) =
                    self.compile_recursive_self_binding_makeblock(a, id, expr, all_bindings, group)
                {
                    return (vec![], effects);
                }

                let compiled = self.compile_expr(a, expr);
                let mut effects = compiled.prelude;
                if !block_terminates(&self.j, &effects) {
                    let target = JE::var(*id, &mut self.j);
                    let call = self.runtime_call_expr(
                        "Primitive_object",
                        "updateDummy",
                        vec![target, compiled.expr],
                    );
                    effects.push(JS::exp(call, &mut self.j));
                }
                (
                    vec![JS::variable(
                        VarDecl {
                            ident: *id,
                            value: Some(self.recursive_dummy_object_expr(&tag_info)),
                            property: LetKind::Variable,
                            ident_info: IdentInfo::default(),
                        },
                        &mut self.j,
                    )],
                    effects,
                )
            }
            None => {
                let compiled = self.compile_expr(a, expr);
                let mut effects = compiled.prelude;
                if block_terminates(&self.j, &effects) {
                    return (
                        vec![JS::variable(
                            VarDecl {
                                ident: *id,
                                value: None,
                                property: LetKind::Strict,
                                ident_info: IdentInfo::default(),
                            },
                            &mut self.j,
                        )],
                        effects,
                    );
                }
                // OCaml `compile_recursive_let`'s catch-all compiles directly
                // under `Declare (Alias, id)` (`lam_compile.ml:552-553`).  The
                // value's prelude therefore precedes a normal declaration; it
                // does not introduce a placeholder plus a later assignment.
                effects.push(JS::variable(
                    VarDecl {
                        ident: *id,
                        value: Some(compiled.expr),
                        property: LetKind::Alias,
                        ident_info: IdentInfo::default(),
                    },
                    &mut self.j,
                ));
                (vec![], effects)
            }
        }
    }

    fn try_compile_recursive_singleton_binding_without_placeholder(
        &mut self,
        a: &mut LamArena,
        id: &Ident,
        expr: Lam,
    ) -> Option<Block> {
        if !matches!(a.node(expr), Node::Let { .. }) {
            return None;
        }

        let block = self.compile_let_binding(a, LetKind::Alias, id, expr);
        if block_declares_initialized_ident(&self.j, &block, id) {
            Some(block)
        } else {
            None
        }
    }

    fn compile_recursive_self_binding_makeblock(
        &mut self,
        a: &LamArena,
        id: &Ident,
        expr: Lam,
        all_bindings: &[(Ident, Lam)],
        group: &[usize],
    ) -> Option<Block> {
        let (Primitive::Pmakeblock(tag_info, _), args, _) = a.as_prim(expr)? else {
            return None;
        };

        if !matches!(tag_info, TagInfo::Record(_))
            && !matches!(tag_info, TagInfo::Constructor(c) if c.num_nonconst == 1)
            && !matches!(tag_info, TagInfo::RecordInlined(r) if r.num_nonconst == 1)
        {
            return None;
        }

        let only_self_or_captured = args.iter().all(|arg| match a.view(*arg) {
            View::Var(binding) => {
                binding.same(id)
                    || !group.iter().any(|&index| {
                        let (other, _) = &all_bindings[index];
                        other.same(&binding) && !other.same(id)
                    })
            }
            View::Const(_) => true,
            _ => false,
        });
        if !only_self_or_captured {
            return None;
        }

        let dummy = self.recursive_dummy_object_expr(tag_info);
        let mut block = vec![JS::define(*id, Some(dummy), LetKind::Variable, &mut self.j)];

        for (index, arg) in args.iter().enumerate() {
            let field_info = Self::recursive_self_binding_field_info(tag_info, index)?;
            let value = match a.view(*arg) {
                View::Var(binding) => JE::var(binding, &mut self.j),
                View::Const(constant) => Self::compile_constant(constant, &mut self.j),
                _ => return None,
            };
            let target = JE::var(*id, &mut self.j);
            let set = self.compile_set_field(index as i32, &field_info, target, value);
            block.push(JS::exp(set, &mut self.j));
        }

        Some(block)
    }

    fn recursive_dummy_object_expr(&mut self, tag_info: &TagInfo) -> Expr {
        match tag_info {
            TagInfo::Record(_)
            | TagInfo::Module(_)
            | TagInfo::Constructor(_)
            | TagInfo::RecordInlined(_)
            | TagInfo::PolyVar(_)
            | TagInfo::Extension
            | TagInfo::RecordExt { .. } => {
                let props = self.j.prop_list(&[]);
                JE::new(ExprKind::Object(None, props), &mut self.j)
            }
            TagInfo::Tuple | TagInfo::ModuleExport(_) => {
                JE::array(&[], MutableFlag::Mutable, &mut self.j)
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
            TagInfo::Record(record) => record
                .fields
                .get(index)
                .map(|(name, _)| SetFieldDbgInfo::RecordSet(crate::name::Name::new(name))),
            TagInfo::RecordInlined(inlined) => inlined
                .fields
                .get(index)
                .map(|(name, _)| SetFieldDbgInfo::RecordInlineSet(crate::name::Name::new(name))),
            TagInfo::Constructor(constructor) => Some(SetFieldDbgInfo::RecordInlineSet(
                crate::name::Name::new(&if constructor.name == "::" {
                    match index {
                        0 => "hd".to_string(),
                        1 => "tl".to_string(),
                        _ => format!("_{}", index),
                    }
                } else {
                    format!("_{}", index)
                }),
            )),
            _ => None,
        }
    }

    fn compile_let_binding(
        &mut self,
        a: &mut LamArena,
        kind: LetKind,
        id: &Ident,
        value: Lam,
    ) -> Block {
        match a.node(value) {
            Node::Let {
                kind: inner_kind,
                id: inner_id,
                value: inner_value,
                body,
            } => {
                let inner_id = a.ident(inner_id);
                let mut block = self.compile_let_binding(a, inner_kind, &inner_id, inner_value);
                if block_terminates(&self.j, &block) {
                    return block;
                }
                block.extend(self.compile_let_binding(a, kind, id, body));
                block
            }
            Node::StaticCatch {
                body,
                handler,
                info,
            } => {
                let label = a.catch_payload(info).label;
                let bindings = catch_bindings(a, info);
                // OCaml's `compile_staticcatch` (lam_compile.ml:937-1017)
                // gates pseudo-jmp on `EffectCall (Maybe_tail_is_return
                // (Tail_with_name {in_staticcatch=false}))`. A `Declare (kind, id)`
                // continuation — which is what `compile_let_binding` models —
                // takes the explicit-jump arm at lam_compile.ml:996-1000
                // unconditionally. Take that path here; the
                // `with_static_handler` inline shortcut is a Rust-only
                // optimization with no OCaml analog for `Declare`.
                let mut block = vec![JS::variable(
                    VarDecl {
                        ident: *id,
                        value: None,
                        property: kind,
                        ident_info: IdentInfo::default(),
                    },
                    &mut self.j,
                )];
                let (handlers, flat_body) =
                    flatten_nested_caches(a, label, &bindings, body, handler);
                if handlers.len() > 1 {
                    // lam_compile.ml:935 + 989-996 — `Declare (kind, id)`
                    // with flattened multi-handler code_table.
                    block.extend(
                        self.compile_multi_staticcatch_assignment_block(
                            a, id, &handlers, flat_body,
                        ),
                    );
                } else {
                    block.extend(self.compile_staticcatch_assignment_block(
                        a, id, label, &bindings, body, handler,
                    ));
                }
                block
            }
            Node::If { cond, then_, else_ } => {
                self.compile_if_binding_block(a, kind, id, cond, then_, else_)
            }
            Node::TryWith {
                body,
                id: exn,
                handler,
            } => {
                let exn = a.ident(exn);
                let body_block = self.compile_assign_to_target_block(a, id, body);
                let handler_block = self.compile_assign_to_target_block(a, id, handler);
                vec![
                    JS::variable(
                        VarDecl {
                            ident: *id,
                            value: None,
                            property: kind,
                            ident_info: IdentInfo::default(),
                        },
                        &mut self.j,
                    ),
                    self.try_statement(body_block, &exn, handler_block),
                ]
            }
            Node::Sequence(first, second) => {
                // OCaml compiler/core/lam_compile.ml:1862-1869 compiles an
                // `Llet` RHS with continuation `Declare(kind, id)`. Its
                // Lsequence arm at compiler/core/lam_compile.ml:1899-1903
                // emits the head as `EffectCall Not_tail`, then compiles the
                // tail in the original continuation. That lets
                // compiler/core/js_stmt_make.ml:62-67 turn a final unit
                // `Undefined` into `let id;` instead of binding a
                // `(effect, undefined)` expression.
                let mut block = self.compile_effect_block(a, first);
                if lambda_is_unconditional_exit(a, first) || block_finishes_output(&self.j, &block)
                {
                    return block;
                }
                block.extend(self.compile_let_binding(a, kind, id, second));
                block
            }
            Node::Switch {
                scrut,
                actions,
                info,
            } => self.compile_switch_binding_block(a, kind, id, scrut, Sw { actions, info }),
            Node::StringSwitch {
                scrut,
                actions,
                info,
            } => self.compile_string_switch_binding_block(
                a,
                kind,
                id,
                scrut,
                StrSw { actions, info },
            ),
            Node::Prim { args, info }
                if short_circuit_primitive(&a.prim_payload(info).primitive, a.list(args))
                    .is_some() =>
            {
                let (op, lhs, rhs) =
                    short_circuit_primitive(&a.prim_payload(info).primitive, a.list(args))
                        .expect("checked short-circuit primitive");
                self.compile_short_circuit_binding_block(a, kind, id, op, lhs, rhs)
            }
            _ => {
                let value_compiled = self.compile_expr(a, value);
                let mut block = value_compiled.prelude;
                if block_terminates(&self.j, &block) {
                    return block;
                }
                block.push(JS::variable(
                    VarDecl {
                        ident: *id,
                        value: Some(value_compiled.expr),
                        property: kind,
                        ident_info: IdentInfo::default(),
                    },
                    &mut self.j,
                ));
                block
            }
        }
    }

    pub(crate) fn compile_effect_block(&mut self, a: &mut LamArena, lam: Lam) -> Block {
        // Mirror OCaml's invariant that consumers of `compile_lambda` go
        // through `Js_output.output_as_block` (js_output.ml:82-86) which
        // calls `unnest_block` (js_output.ml:77-80). The unnest peels
        // single-element `[Block ...]` wrappers so an inner `S.if_` rule 7
        // result doesn't hide its literal-last terminal from the outer
        // `block_last_is_return_throw_or_continue` check
        // (js_stmt_make.ml:186-193).
        JS::unnest_block(self.compile_effect_block_inner(a, lam), &self.j)
    }

    /// A grouped switch case that falls through to the next one. OCaml still
    /// gives it the location of its case lambda (lam_compile.ml:676-683).
    pub(crate) fn empty_switch_case_clause_for(&self, a: &LamArena, lam: Lam) -> Clause {
        Clause {
            source_loc: self.source_loc_of_lam(a, lam),
            ..empty_switch_case_clause()
        }
    }

    /// lam_compile.ml:80-84 `with_block_source_loc`: switch-case bodies
    /// (lam_compile.ml:581-659) tag their first statement with the case
    /// lambda's location.
    pub(crate) fn with_block_source_loc(
        &mut self,
        a: &LamArena,
        lam: Lam,
        mut block: Block,
    ) -> Block {
        if let Some(first) = block.first().copied()
            && self.j.stmt_loc(first).is_none()
        {
            let loc = self.source_loc_of_lam(a, lam);
            block[0] = self.j.with_stmt_loc(first, loc);
        }
        block
    }

    fn compile_effect_block_inner(&mut self, a: &mut LamArena, lam: Lam) -> Block {
        match a.node(lam) {
            Node::Let {
                kind,
                id,
                value,
                body,
            } => {
                let id = a.ident(id);
                if let Some(compiled) = self.try_compile_record_spread(a, &id, value, body) {
                    let mut block = compiled.prelude;
                    push_effect_expression(&mut self.j, &mut block, compiled.expr);
                    return block;
                }

                let mut block = self.compile_let_binding(a, kind, &id, value);
                // Mirror OCaml's output_finished:True from Lbreak/Lcontinue:
                // if the binding's RHS is an unconditional exit, the body is
                // unreachable and must not be emitted. block_finishes_output
                // only recognises Return/Throw (Break/Continue inside a switch
                // case must not terminate the enclosing block), so check the
                // Lambda form directly.
                if lambda_is_unconditional_exit(a, value) || block_finishes_output(&self.j, &block)
                {
                    return block;
                }
                block.extend(self.compile_effect_block(a, body));
                block
            }
            Node::LetRec { ids, values, body } => {
                // Mirror OCaml's Lletrec arm (lam_compile.ml:1770-1783): emit
                // bindings then compile body in the SAME continuation. The
                // catch-all `_ => compile_expr(lam)` would force the body
                // through `NeedValue`, losing the effect/tail context.
                let bindings = letrec_bindings(a, ids, values);
                let mut block = self.compile_recursive_bindings(a, &bindings);
                if block_finishes_output(&self.j, &block) {
                    return block;
                }
                block.extend(self.compile_effect_block(a, body));
                block
            }
            Node::If { cond, then_, else_ } => self.compile_if_effect_block(a, cond, then_, else_),
            Node::Sequence(first, second) => {
                let mut block = self.compile_effect_block(a, first);
                if lambda_is_unconditional_exit(a, first) || block_finishes_output(&self.j, &block)
                {
                    return block;
                }
                block.extend(self.compile_effect_block(a, second));
                block
            }
            Node::StaticCatch {
                body,
                handler,
                info,
            } => {
                let label = a.catch_payload(info).label;
                let bindings = catch_bindings(a, info);
                // OCaml's `compile_staticcatch` (lam_compile.ml:937-1017) only
                // takes the pseudo-jmp path when the continuation is
                // `EffectCall (Maybe_tail_is_return (Tail_with_name
                // {in_staticcatch = false}))`. For an `EffectCall Not_tail`
                // continuation — which is where `compile_effect_block` sits —
                // it always falls through to the explicit-jump arm at
                // lam_compile.ml:963-1017. Mirror that by always taking the
                // Rust explicit-jump path here; the inline `with_static_handler`
                // shortcut is a Rust-only optimization with no OCaml analog.
                let (handlers, flat_body) =
                    flatten_nested_caches(a, label, &bindings, body, handler);
                if handlers.len() > 1 {
                    // lam_compile.ml:935 + 1000-1010 — `EffectCall Not_tail`
                    // with flattened multi-handler code_table.
                    self.compile_multi_staticcatch_effect_block(a, &handlers, flat_body)
                } else {
                    self.compile_staticcatch_effect_block(a, label, &bindings, body, handler)
                }
            }
            Node::TryWith { body, id, handler } => {
                let exn = a.ident(id);
                let body_block = self.compile_effect_block(a, body);
                let handler_block = self.compile_effect_block(a, handler);
                vec![self.try_statement(body_block, &exn, handler_block)]
            }
            Node::Switch {
                scrut,
                actions,
                info,
            } => self.compile_switch_effect_block(a, scrut, Sw { actions, info }),
            Node::StringSwitch {
                scrut,
                actions,
                info,
            } => self.compile_string_switch_effect_block(a, scrut, StrSw { actions, info }),
            _ => {
                let compiled = self.compile_expr(a, lam);
                self.compiled_to_effect_block(compiled)
            }
        }
    }

    fn compile_if_binding_block(
        &mut self,
        a: &mut LamArena,
        kind: LetKind,
        id: &Ident,
        cond: Lam,
        then_: Lam,
        else_: Lam,
    ) -> Block {
        let cond_compiled = self.compile_expr(a, cond);
        // Mirror OCaml's `compile_ifthenelse` Declare arm
        // (lam_compile.ml:1326-1349): first try both branches in
        // `NeedValue Not_tail`. When BOTH yield `{block = []; value = Some _}`
        // (i.e. fold to a side-effect-free expression including `E.seq`-folded
        // sequences), emit `let id = cond ? out1 : out2;` via `E.econd`.
        // Otherwise compile in Assign id and emit `let id; if (cond) ...`.
        let then_compiled = self.compile_expr(a, then_);
        let else_compiled = self.compile_expr(a, else_);
        if then_compiled.prelude.is_empty() && else_compiled.prelude.is_empty() {
            let mut block = cond_compiled.prelude;
            block.push(JS::variable(
                VarDecl {
                    ident: *id,
                    value: Some(JE::cond(
                        cond_compiled.expr,
                        then_compiled.expr,
                        else_compiled.expr,
                        &mut self.j,
                    )),
                    property: kind,
                    ident_info: IdentInfo::default(),
                },
                &mut self.j,
            ));
            return block;
        }

        let then_block = self.compile_assign_to_target_block(a, id, then_);
        let else_block = self.compile_assign_to_target_block(a, id, else_);

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

    #[allow(clippy::too_many_arguments)]
    fn compile_switch_binding_block(
        &mut self,
        a: &mut LamArena,
        kind: LetKind,
        id: &Ident,
        scrut: Lam,
        sw: Sw,
    ) -> Block {
        // OCaml's `compile_switch` (lam_compile.ml:784-787) unconditionally
        // emits `S.declare_variable ~kind id` before compiling the switch
        // body in `Assign id` context. No `declaration` is threaded through,
        // so the switch never folds back into `let id = cond ? a : b`.
        let mut declared = vec![JS::variable(
            VarDecl {
                ident: *id,
                value: None,
                property: kind,
                ident_info: IdentInfo::default(),
            },
            &mut self.j,
        )];
        declared.extend(self.compile_switch_assignment_block(a, id, scrut, sw));
        declared
    }

    #[allow(clippy::too_many_arguments)]
    fn compile_string_switch_binding_block(
        &mut self,
        a: &mut LamArena,
        kind: LetKind,
        id: &Ident,
        scrut: Lam,
        sw: StrSw,
    ) -> Block {
        // OCaml's `compile_stringswitch` (lam_compile.ml:872-876) threads the
        // `Declare (kind, id)` continuation straight to `compile_string_cases`
        // -> `compile_general_cases` -> `morph_declare_to_assign` -> `S.if_`,
        // so the two-case Complete arm folds `[id = then; id = else]` into
        // `let id = cond ? then : else` via the `declaration` parameter. Mirror
        // that by folding the final `id = expr` in the emitted assignment
        // block into the pending declaration.
        let body = self.compile_string_switch_assignment_block(a, id, scrut, sw);
        self.prepend_declaration_or_fold_final_assignment(kind, id, body)
    }

    fn compile_short_circuit_expr(
        &mut self,
        a: &mut LamArena,
        op: ShortCircuitOp,
        lhs: Lam,
        rhs: Lam,
    ) -> Compiled {
        let lhs_compiled = self.compile_expr(a, lhs);
        let rhs_compiled = self.compile_expr(a, rhs);
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
                ShortCircuitOp::And => JE::bin(
                    BinOp::And,
                    lhs_compiled.expr,
                    rhs_compiled.expr,
                    &mut self.j,
                ),
                ShortCircuitOp::Or => {
                    JE::bin(BinOp::Or, lhs_compiled.expr, rhs_compiled.expr, &mut self.j)
                }
            };
            return Compiled { prelude, expr };
        }

        let tmp = self.fresh_tmp_ident();
        prelude.push(JS::variable(
            VarDecl {
                ident: tmp,
                value: Some(op.default_expr(&mut self.j)),
                property: LetKind::Strict,
                ident_info: IdentInfo::default(),
            },
            &mut self.j,
        ));

        let mut then_block = rhs_compiled.prelude;
        if !block_terminates(&self.j, &then_block) {
            then_block.push(JS::exp(
                JE::bin(
                    BinOp::Eq,
                    JE::var(tmp, &mut self.j),
                    rhs_compiled.expr,
                    &mut self.j,
                ),
                &mut self.j,
            ));
        }

        let test = op.test_expr(lhs_compiled.expr, &mut self.j);
        prelude.push(JS::if_(test, &then_block, &[], &mut self.j));

        Compiled {
            prelude,
            expr: JE::var(tmp, &mut self.j),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn compile_short_circuit_binding_block(
        &mut self,
        a: &mut LamArena,
        kind: LetKind,
        id: &Ident,
        op: ShortCircuitOp,
        lhs: Lam,
        rhs: Lam,
    ) -> Block {
        let lhs_compiled = self.compile_expr(a, lhs);
        let rhs_compiled = self.compile_expr(a, rhs);
        let mut block = lhs_compiled.prelude;

        if rhs_compiled.prelude.is_empty() {
            let expr = match op {
                ShortCircuitOp::And => JE::bin(
                    BinOp::And,
                    lhs_compiled.expr,
                    rhs_compiled.expr,
                    &mut self.j,
                ),
                ShortCircuitOp::Or => {
                    JE::bin(BinOp::Or, lhs_compiled.expr, rhs_compiled.expr, &mut self.j)
                }
            };
            block.push(JS::variable(
                VarDecl {
                    ident: *id,
                    value: Some(expr),
                    property: kind,
                    ident_info: IdentInfo::default(),
                },
                &mut self.j,
            ));
            return block;
        }

        block.push(JS::variable(
            VarDecl {
                ident: *id,
                value: Some(op.default_expr(&mut self.j)),
                property: kind,
                ident_info: IdentInfo::default(),
            },
            &mut self.j,
        ));

        let mut then_block = rhs_compiled.prelude;
        if !block_terminates(&self.j, &then_block) {
            then_block.push(self.result_assignment(id, rhs_compiled.expr));
        }

        let test = op.test_expr(lhs_compiled.expr, &mut self.j);
        block.push(JS::if_(test, &then_block, &[], &mut self.j));
        block
    }

    fn compile_short_circuit_return_block(
        &mut self,
        a: &mut LamArena,
        op: ShortCircuitOp,
        lhs: Lam,
        rhs: Lam,
    ) -> Block {
        let default = op.default_lambda(a);
        match op {
            ShortCircuitOp::And => self.compile_if_return_block(a, lhs, rhs, default),
            ShortCircuitOp::Or => self.compile_if_return_block(a, lhs, default, rhs),
        }
    }

    pub(crate) fn compile_return_block(&mut self, a: &mut LamArena, lam: Lam) -> Block {
        // Mirror OCaml's invariant that consumers go through
        // `Js_output.output_as_block` (js_output.ml:82-86) which calls
        // `unnest_block` on `compile_lambda` results.
        JS::unnest_block(self.compile_return_block_inner(a, lam), &self.j)
    }

    fn compile_return_block_inner(&mut self, a: &mut LamArena, lam: Lam) -> Block {
        match a.node(lam) {
            Node::Let {
                kind,
                id,
                value,
                body,
            } => {
                let id = a.ident(id);
                if let Some(compiled) = self.try_compile_record_spread(a, &id, value, body) {
                    let mut block = compiled.prelude;
                    block.push(JS::return_(compiled.expr, &mut self.j));
                    return block;
                }

                let mut block = self.compile_let_binding(a, kind, &id, value);
                if block_finishes_output(&self.j, &block) {
                    return block;
                }
                block.extend(self.compile_return_block(a, body));
                block
            }
            Node::LetRec { ids, values, body } => {
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
                let bindings = letrec_bindings(a, ids, values);
                let mut block = self.compile_recursive_bindings(a, &bindings);
                if block_finishes_output(&self.j, &block) {
                    return block;
                }
                block.extend(self.compile_return_block(a, body));
                block
            }
            Node::Apply { func, args, info } => {
                let mut compiled = self.compile_apply_call(a, func, args, info);
                // lam_compile.ml:1606-1609: `with_source_loc ap_loc (E.call ...)`.
                if self.j.expr_loc(compiled.expr).is_none() {
                    let loc = self.source_loc(&a.apply_payload(info).info.loc);
                    compiled.expr = self.j.with_expr_loc(compiled.expr, loc);
                }
                let mut block = compiled.prelude;
                block.push(JS::return_(compiled.expr, &mut self.j));
                block
            }
            Node::If { cond, then_, else_ } => self
                .compile_if_unit_return_tail_block(a, cond, then_, else_)
                .unwrap_or_else(|| self.compile_if_return_block(a, cond, then_, else_)),
            Node::Prim { args, info }
                if short_circuit_primitive(&a.prim_payload(info).primitive, a.list(args))
                    .is_some() =>
            {
                let (op, lhs, rhs) =
                    short_circuit_primitive(&a.prim_payload(info).primitive, a.list(args))
                        .expect("checked short-circuit primitive");
                self.compile_short_circuit_return_block(a, op, lhs, rhs)
            }
            Node::Sequence(first, second) => {
                let mut block = self.compile_effect_block(a, first);
                if block_finishes_output(&self.j, &block) {
                    return block;
                }
                block.extend(self.compile_return_block(a, second));
                block
            }
            Node::StaticRaise { label, args } => {
                if let Some(block) = self.compile_static_raise_jump_block(a, label, args) {
                    return block;
                }
                if let Some(block) =
                    self.compile_fallthrough_static_raise_return_block(a, label, args)
                {
                    return block;
                }
                if let Some(handler) = self.resolve_static_raise(a, label, args) {
                    return self.compile_return_block(a, handler);
                }
                let compiled = self.compile_expr(a, lam);
                let mut block = compiled.prelude;
                if !block_terminates(&self.j, &block) {
                    block.push(JS::return_(compiled.expr, &mut self.j));
                }
                block
            }
            Node::StaticCatch {
                body,
                handler,
                info,
            } => {
                let label = a.catch_payload(info).label;
                let bindings = catch_bindings(a, info);
                self.compile_staticcatch_in_return(a, label, &bindings, body, handler)
            }
            Node::TryWith { body, id, handler } => {
                let exn = a.ident(id);
                // OCaml reference: compiler/core/lam_compile.ml:1311-1344
                // compiles the `try` body with `Tail_in_try` while the catch
                // handler keeps the surrounding return context. `Tail_in_try`
                // still returns from the JS function, but it is not the
                // `Tail_with_name {in_staticcatch=false}` context required by
                // `compile_staticcatch`'s pseudo-jump arm.
                let body_block =
                    self.with_try_body_context(|this| this.compile_return_block(a, body));
                let handler_block = self.compile_return_block(a, handler);
                vec![self.try_statement(body_block, &exn, handler_block)]
            }
            Node::Switch {
                scrut,
                actions,
                info,
            } => self.compile_switch_return_block(a, scrut, Sw { actions, info }),
            Node::StringSwitch {
                scrut,
                actions,
                info,
            } => self.compile_string_switch_return_block(a, scrut, StrSw { actions, info }),
            _ => {
                let compiled = self.compile_expr(a, lam);
                let mut block = compiled.prelude;
                if !block_terminates(&self.j, &block) {
                    block.push(JS::return_(compiled.expr, &mut self.j));
                }
                block
            }
        }
    }

    /// The `Lstaticcatch` arms of `compile_return_block_inner`, tried in
    /// order.
    fn compile_staticcatch_in_return(
        &mut self,
        a: &mut LamArena,
        label: i32,
        bindings: &[Ident],
        body: Lam,
        handler: Lam,
    ) -> Block {
        // lam_compile.ml:935 — `flatten_nested_caches` is the FIRST
        // thing `compile_staticcatch` does. A code_table with >1
        // entries goes through the multi-handler explicit-jump arm
        // (lam_compile.ml:1000-1010 for `EffectCall tail_type`).
        let (handlers, flat_body) = flatten_nested_caches(a, label, bindings, body, handler);
        if handlers.len() > 1 {
            return self.compile_multi_staticcatch_return_block(a, &handlers, flat_body);
        }
        if self.uses_fallthrough_staticcatch_return(a, body, label, bindings, handler) {
            return self
                .compile_fallthrough_staticcatch_return_block(a, label, bindings, body, handler);
        }
        if self.uses_pseudo_fallthrough_staticcatch_return(a, body, label, bindings, handler) {
            return self
                .compile_fallthrough_staticcatch_return_block(a, label, bindings, body, handler);
        }
        if bindings.is_empty()
            && self.try_body_depth == 0
            && matches!(
                a.view(body),
                View::StaticCatch(_, _, _, nested_handler)
                    if lambda_contains_static_raise(a, nested_handler)
            )
            && !self.handler_returns_unit_undefined(a, bindings, handler)
            && no_static_raise_in_handler_like_ocaml(a, handler)
        {
            return self
                .compile_fallthrough_staticcatch_return_block(a, label, bindings, body, handler);
        }
        let requires_explicit_jump = (self.return_unit_stack.last().copied() == Some(true)
            && !bindings.is_empty())
            || self.try_body_depth > 0
            || self.return_staticcatch_requires_explicit_jump(a, label, bindings, body, handler);
        if requires_explicit_jump {
            self.compile_staticcatch_return_block(a, label, bindings, body, handler)
        } else if no_static_raise_in_handler_like_ocaml(a, handler)
            && !lambda_contains_staticcatch(a, handler)
            && lambda_contains_static_raise_to_label(a, body, label, bindings.len())
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
            self.compile_fallthrough_staticcatch_return_block(a, label, bindings, body, handler)
        } else if lambda_contains_static_raise_to_label(a, body, label, bindings.len()) {
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
            self.compile_staticcatch_return_block(a, label, bindings, body, handler)
        } else {
            self.with_static_handler(label, bindings, handler, |this| {
                this.compile_return_block(a, body)
            })
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

    fn lambda_is_trivial_unit_undefined(&self, a: &LamArena, lam: Lam) -> bool {
        match a.view(lam) {
            View::Const(Constant::JsUndefined { is_unit: true }) => true,
            View::Sequence(first, second) => {
                lam_analysis::no_side_effects(a, first)
                    && self.lambda_is_trivial_unit_undefined(a, second)
            }
            View::Let(_, _, value, body) => {
                lam_analysis::no_side_effects(a, value)
                    && self.lambda_is_trivial_unit_undefined(a, body)
            }
            View::LetRec(_, values, body) => {
                values
                    .iter()
                    .all(|value| lam_analysis::no_side_effects(a, *value))
                    && self.lambda_is_trivial_unit_undefined(a, body)
            }
            View::StaticCatch(body, _, bindings, handler) if bindings.is_empty() => {
                self.lambda_is_trivial_unit_undefined(a, body)
                    && self.lambda_is_trivial_unit_undefined(a, handler)
            }
            View::TryWith(body, _, handler) => {
                self.lambda_is_trivial_unit_undefined(a, body)
                    && self.lambda_is_trivial_unit_undefined(a, handler)
            }
            _ => false,
        }
    }

    fn compile_if_unit_return_tail_block(
        &mut self,
        a: &mut LamArena,
        cond: Lam,
        then_: Lam,
        else_: Lam,
    ) -> Option<Block> {
        if self.return_unit_stack.last().copied() != Some(true) {
            return None;
        }

        let then_is_trivial_unit = self.lambda_is_trivial_unit_undefined(a, then_);
        let else_is_trivial_unit = self.lambda_is_trivial_unit_undefined(a, else_);
        if then_is_trivial_unit && else_is_trivial_unit {
            let cond_compiled = self.compile_expr(a, cond);
            let mut block = cond_compiled.prelude;
            // OCaml's `S.if_ cond [] []` reduces to `S.exp cond`
            // (js_stmt_make.ml:242 + 45-53), which keeps pure comparisons like
            // `tmp === null` as a bare `Exp` statement.
            push_s_exp(&mut self.j, &mut block, cond_compiled.expr);
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

    fn handler_returns_unit_undefined(
        &self,
        a: &LamArena,
        bindings: &[Ident],
        handler: Lam,
    ) -> bool {
        if !bindings.is_empty() {
            return false;
        }

        match a.view(handler) {
            View::Const(Constant::JsUndefined { is_unit: true }) => true,
            View::Sequence(_, rest) => self.handler_returns_unit_undefined(a, &[], rest),
            View::Let(_, _, _, body) => self.handler_returns_unit_undefined(a, &[], body),
            View::LetRec(_, _, body) => self.handler_returns_unit_undefined(a, &[], body),
            _ => false,
        }
    }

    fn staticcatch_handler_is_identity_binding(
        &self,
        a: &LamArena,
        bindings: &[Ident],
        handler: Lam,
    ) -> bool {
        matches!(
            (bindings, a.view(handler)),
            ([binding], View::Var(id)) if id.same(binding)
        )
    }

    fn compile_fallthrough_static_raise_return_block(
        &mut self,
        a: &mut LamArena,
        label: i32,
        args: LamList,
    ) -> Option<Block> {
        let bindings = self
            .fallthrough_return_handlers
            .iter()
            .rev()
            .find(|handler| handler.label == label)?
            .bindings
            .clone();
        if bindings.len() != a.list_len(args) {
            return None;
        }

        let mut block = Vec::new();
        for (arg, binding) in a.list_small(args).into_iter().zip(&bindings) {
            if a.as_var(arg).is_some_and(|id| id.same(binding)) {
                continue;
            }
            block.extend(self.compile_assign_to_target_block(a, binding, arg));
        }
        Some(block)
    }

    fn compile_fallthrough_staticcatch_return_block(
        &mut self,
        a: &mut LamArena,
        label: i32,
        bindings: &[Ident],
        body: Lam,
        handler: Lam,
    ) -> Block {
        let mut block: Block = bindings
            .iter()
            .map(|binding| {
                JS::variable(
                    VarDecl {
                        ident: *binding,
                        value: None,
                        property: LetKind::Variable,
                        ident_info: IdentInfo::default(),
                    },
                    &mut self.j,
                )
            })
            .collect();
        let body_block = self.with_fallthrough_return_handler(label, bindings, |this| {
            this.compile_return_block(a, body)
        });
        block.extend(body_block);
        if !block_terminates(&self.j, &block) {
            block.extend(self.compile_return_block(a, handler));
        }
        block
    }

    #[allow(clippy::too_many_arguments)]
    fn compile_fallthrough_staticcatch_tail_loop_return_block(
        &mut self,
        a: &mut LamArena,
        label: i32,
        bindings: &[Ident],
        body: Lam,
        handler: Lam,
        tail_loop: &mut TailLoopState,
    ) -> Block {
        let mut block: Block = bindings
            .iter()
            .map(|binding| {
                JS::variable(
                    VarDecl {
                        ident: *binding,
                        value: None,
                        property: LetKind::Variable,
                        ident_info: IdentInfo::default(),
                    },
                    &mut self.j,
                )
            })
            .collect();
        let body_block = self.with_fallthrough_return_handler(label, bindings, |this| {
            this.compile_tail_loop_return_block(a, body, tail_loop)
        });
        block.extend(body_block);
        if !block_terminates(&self.j, &block) {
            block.extend(self.compile_tail_loop_return_block(a, handler, tail_loop));
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
        a: &LamArena,
        body: Lam,
        label: i32,
        bindings: &[Ident],
        handler: Lam,
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
        let body_has_target_exit = lambda_contains_static_raise_to_label(a, body, label, arity);
        let keep_complete_named_variant_plain_handler_inline = matches!(
            a.view(body),
            View::Switch(_, switch)
                if self.uses_named_variant_dispatch(switch.payload)
                    && switch.actions.fail.is_none()
                    && switch.payload.consts_full
                    && switch.payload.blocks_full
                    && no_static_raise_in_handler_like_ocaml(a, handler)
                    && lambda_contains_static_raise_to_other_label(a, body, label)
        );
        // Lam_pass_exits can inline outward handlers away before backend
        // lowering. OCaml's compile_staticcatch pseudo-jump path still keeps a
        // shared non-raising handler outside the switch when several direct
        // exits now target the same label.
        let shared_multi_exit_fallthrough_like_ocaml = !inside_enclosing_staticcatch_chain
            && !keep_complete_named_variant_plain_handler_inline
            && !self.handler_returns_unit_undefined(a, bindings, handler)
            && no_static_raise_in_handler_like_ocaml(a, handler)
            && body_has_target_exit
            && lambda_has_multiple_static_raises_to_label(a, body, label, arity);
        let handler_is_raise_of_arity =
            matches!(a.view(handler), View::StaticRaise(_, args) if args.len() == arity);
        match a.view(body) {
            View::Switch(_, switch) => {
                let (consts, blocks) = (switch.actions.consts, switch.actions.blocks);
                if handler_is_raise_of_arity && body_has_target_exit {
                    true
                } else if !self.uses_untagged_variant_dispatch(switch.payload)
                    && !keep_complete_named_variant_plain_handler_inline
                    && shared_multi_exit_fallthrough_like_ocaml
                {
                    true
                } else if !self.uses_untagged_variant_dispatch(switch.payload)
                    && !keep_complete_named_variant_plain_handler_inline
                    && no_static_raise_in_handler_like_ocaml(a, handler)
                    && !lambda_contains_staticcatch(a, handler)
                    && switch_cases_contain_static_raise_to_label(a, consts, blocks, label, arity)
                    && body_has_target_exit
                    && (lambda_contains_static_raise_to_other_label(a, body, label)
                        || switch_cases_contain_nontrivial_static_raise_to_label(
                            a, consts, blocks, label, arity,
                        ))
                {
                    true
                }
                // OCaml takes the pseudo-jmp/fallthrough arm for any
                // tail-return staticcatch with a single handler whose handler
                // has no static raise (compiler/core/lam_compile.ml:983-1008).
                // It is not gated on function `return_unit`; switches reach the
                // same `compile_staticcatch` arm through
                // compiler/core/lam_compile.ml:1907-1911.
                else if !inside_enclosing_staticcatch_chain
                    && !self.handler_returns_unit_undefined(a, bindings, handler)
                    && no_static_raise_in_handler_like_ocaml(a, handler)
                {
                    if !bindings.is_empty() {
                        body_has_target_exit
                    } else {
                        consts.len() + blocks.len() == 1
                            && switch.actions.fail.is_some_and(|fail| {
                                matches!(a.view(fail), View::StaticRaise(id, args)
                                    if id == label && args.len() == arity)
                            })
                    }
                } else {
                    false
                }
            }
            View::StringSwitch(_, sw) => {
                if handler_is_raise_of_arity && body_has_target_exit {
                    true
                } else if !keep_complete_named_variant_plain_handler_inline
                    && shared_multi_exit_fallthrough_like_ocaml
                {
                    true
                } else if no_static_raise_in_handler_like_ocaml(a, handler)
                    && !keep_complete_named_variant_plain_handler_inline
                    && !lambda_contains_staticcatch(a, handler)
                    && string_switch_cases_contain_static_raise_to_label(
                        a, sw.actions, label, arity,
                    )
                    && body_has_target_exit
                    && (lambda_contains_static_raise_to_other_label(a, body, label)
                        || string_switch_cases_contain_nontrivial_static_raise_to_label(
                            a, sw.actions, label, arity,
                        ))
                {
                    true
                }
                // OCaml takes the pseudo-jmp/fallthrough arm for any
                // tail-return staticcatch with a single handler whose handler
                // has no static raise (compiler/core/lam_compile.ml:983-1008).
                // It is not gated on function `return_unit`; string switches
                // reach the same `compile_staticcatch` arm through
                // compiler/core/lam_compile.ml:1907-1911.
                else if !inside_enclosing_staticcatch_chain
                    && !self.handler_returns_unit_undefined(a, bindings, handler)
                    && no_static_raise_in_handler_like_ocaml(a, handler)
                {
                    if !bindings.is_empty() {
                        body_has_target_exit
                    } else {
                        sw.len() == 1
                            && sw.default.is_some_and(|default| {
                                matches!(a.view(default), View::StaticRaise(id, args)
                                    if id == label && args.len() == arity)
                            })
                    }
                } else {
                    false
                }
            }
            View::TryWith(try_body, _, _)
                if !inside_enclosing_staticcatch_chain
                    && !bindings.is_empty()
                    && !self.staticcatch_handler_is_identity_binding(a, bindings, handler)
                    && !self.handler_returns_unit_undefined(a, bindings, handler)
                    && no_static_raise_in_handler_like_ocaml(a, handler)
                    && !lambda_contains_staticcatch(a, handler)
                    && body_has_target_exit
                    && !lambda_contains_static_raise_to_other_label(a, try_body, label) =>
            {
                true
            }
            _ => false,
        }
    }

    fn uses_pseudo_fallthrough_staticcatch_return(
        &self,
        a: &LamArena,
        body: Lam,
        label: i32,
        bindings: &[Ident],
        handler: Lam,
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
            && !matches!(
                a.node(body),
                Node::Switch { .. } | Node::StringSwitch { .. }
            )
            && lambda_contains_static_raise_to_label(a, body, label, bindings.len())
            && no_static_raise_in_handler_like_ocaml(a, handler)
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
        a: &mut LamArena,
        grouped_cases: Vec<(T, Lam, bool)>,
        mut to_tag: impl FnMut(T) -> SwitchCaseTag,
    ) -> Vec<StringClauseInfo> {
        let mut clauses = Vec::with_capacity(grouped_cases.len());
        let mut group_start = 0;
        while group_start < grouped_cases.len() {
            let mut group_end = group_start;
            while !grouped_cases[group_end].2 {
                group_end += 1;
            }

            let body = grouped_cases[group_end].1;
            let compiled_body = self.compile_return_block(a, body);
            let group_falls_through = compiled_body.is_empty();
            // Mirror OCaml's `compile_general_cases`: it feeds each last
            // grouped case through `Js_output.to_break_block`, then gates the
            // break bit with `Lam_exit_code.has_exit` in return continuation
            // (compiler/core/lam_compile.ml:613-624;
            // compiler/core/js_output.ml:88-100). When a case resolves to a
            // fallthrough static-raise handler, the empty body still needs a
            // `break;` so the appended handler runs once after the switch.
            let should_break = self.return_case_needs_break_like_ocaml(a, body, &compiled_body);

            for (tag, case_lam, _) in &grouped_cases[group_start..group_end] {
                clauses.push((
                    to_tag(tag.clone()),
                    self.empty_switch_case_clause_for(a, *case_lam),
                    group_falls_through,
                ));
            }
            clauses.push((
                to_tag(grouped_cases[group_end].0.clone()),
                Clause {
                    source_loc: self.source_loc_of_lam(a, body),
                    body: {
                        let body = self.with_block_source_loc(a, body, compiled_body);
                        JS::list(&body, &mut self.j)
                    },
                    should_break,
                    comment: None,
                },
                group_falls_through,
            ));

            group_start = group_end + 1;
        }

        self.reorder_fallthrough_return_clauses(clauses, |(_, _, falls_through)| *falls_through)
            .into_iter()
            .map(|(tag_type, clause, _)| StringClauseInfo { tag_type, clause })
            .collect()
    }

    pub(crate) fn should_hoist_grouped_named_string_return_tail(
        &self,
        a: &mut LamArena,
        body: Lam,
    ) -> bool {
        match a.node(body) {
            Node::StaticRaise { label, args } => self
                .resolve_static_raise(a, label, args)
                .is_some_and(|handler| lambda_has_exit(a, handler)),
            _ => false,
        }
    }

    pub(crate) fn compile_hoisted_named_string_return_tail(
        &mut self,
        a: &mut LamArena,
        body: Lam,
    ) -> Block {
        self.compile_hoisted_static_raise_chain_return_tail(a, body)
            .unwrap_or_else(|| self.compile_return_block(a, body))
    }

    fn compile_hoisted_static_raise_chain_return_tail(
        &mut self,
        a: &mut LamArena,
        lam: Lam,
    ) -> Option<Block> {
        match a.node(lam) {
            Node::Let {
                kind,
                id,
                value,
                body,
            } => {
                let id = a.ident(id);
                let mut block = self.compile_let_binding(a, kind, &id, value);
                if block_finishes_output(&self.j, &block) {
                    return Some(block);
                }
                block.extend(self.compile_hoisted_static_raise_chain_return_tail(a, body)?);
                Some(block)
            }
            Node::Sequence(first, second) => {
                let mut block = self.compile_effect_block(a, first);
                if block_finishes_output(&self.j, &block) {
                    return Some(block);
                }
                block.extend(self.compile_hoisted_static_raise_chain_return_tail(a, second)?);
                Some(block)
            }
            Node::StaticRaise { label, args } => {
                let args = a.list_small(args);
                let handler_index = self.static_handlers.iter().rposition(|handler| {
                    handler.label == label && handler.bindings.len() == args.len()
                })?;
                let handler = self.static_handlers[handler_index].clone();
                let removed = self.static_handlers.remove(handler_index);

                let mut block = Vec::new();
                for (arg, binding) in args.iter().zip(&handler.bindings) {
                    if a.as_var(*arg).is_some_and(|id| id.same(binding)) {
                        continue;
                    }
                    block.extend(self.compile_let_binding(a, LetKind::Strict, binding, *arg));
                    if block_finishes_output(&self.j, &block) {
                        self.static_handlers.insert(handler_index, removed);
                        return Some(block);
                    }
                }

                block.extend(
                    self.compile_hoisted_static_raise_chain_return_tail(a, handler.handler)
                        .unwrap_or_else(|| self.compile_return_block(a, handler.handler)),
                );
                self.static_handlers.insert(handler_index, removed);
                Some(block)
            }
            _ => None,
        }
    }

    /// `func` is the binding's function node.
    fn compile_recursive_function_expr(
        &mut self,
        a: &mut LamArena,
        _function: &Ident,
        func: Lam,
        tail_targets: &[Ident],
    ) -> Expr {
        let Node::Function { body, info } = a.node(func) else {
            unreachable!("recursive function binding is a function")
        };
        let has_self_tailcall = function_has_self_tailcall(a, tail_targets, body);
        if !has_self_tailcall {
            return self.compile_expr(a, func).expr;
        }

        let f = a.func_payload(info);
        let (return_unit, async_, directive, loc) = (
            f.attr.return_unit,
            f.attr.async_,
            f.attr.directive.clone(),
            f.loc,
        );
        let params = if f.attr.one_unit_arg {
            vec![]
        } else {
            a.params(info).to_vec()
        };
        let mut tail_loop = TailLoopState::new(tail_targets.to_vec(), params.clone());
        // OCaml compiler/core/lam_compile.ml:398-407 compiles the body with
        // `jmp_table = empty_handler_map; switch_depth = 0; loop_stack = []`,
        // like any other function body: the enclosing function's handlers
        // and loops do not reach into it.
        let body = self.with_function_scope(|this| {
            this.with_return_unit_context(return_unit, |that| {
                that.compile_tail_loop_return_block(a, body, &mut tail_loop)
            })
        });

        if !tail_loop.triggered {
            return self.compile_expr(a, func).expr;
        }

        let lowered_params: Vec<Ident> = params
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
            loop_body.push(JS::variable(
                VarDecl {
                    ident: *param,
                    value: Some(JE::var(*new_param, &mut self.j)),
                    property: LetKind::Alias,
                    ident_info: IdentInfo::default(),
                },
                &mut self.j,
            ));
        }
        loop_body.extend(body);

        let always = JE::bool(true, &mut self.j);
        let body = [JS::while_(None, always, &loop_body, &mut self.j)];
        // lam_compile.ml:436: `with_source_loc loc result`.
        let source_loc = self.source_loc(&loc);
        self.function_expr(
            &lowered_params,
            &body,
            return_unit,
            async_,
            directive.as_deref(),
            source_loc,
        )
    }

    pub(crate) fn compile_tail_loop_return_block(
        &mut self,
        a: &mut LamArena,
        lam: Lam,
        tail_loop: &mut TailLoopState,
    ) -> Block {
        // Mirror OCaml's invariant that consumers of `compile_lambda` go
        // through `Js_output.output_as_block` which calls `unnest_block`.
        JS::unnest_block(
            self.compile_tail_loop_return_block_inner(a, lam, tail_loop),
            &self.j,
        )
    }

    fn compile_tail_loop_return_block_inner(
        &mut self,
        a: &mut LamArena,
        lam: Lam,
        tail_loop: &mut TailLoopState,
    ) -> Block {
        match a.node(lam) {
            Node::Let {
                kind,
                id,
                value,
                body,
            } => {
                let id = a.ident(id);
                let mut block = self.compile_let_binding(a, kind, &id, value);
                block.extend(self.compile_tail_loop_return_block(a, body, tail_loop));
                block
            }
            Node::Apply { func, args, info } => {
                if let Some(block) = self.try_compile_self_tailcall_block(a, func, args, tail_loop)
                {
                    return block;
                }
                let compiled = self.compile_apply_call(a, func, args, info);
                let mut block = compiled.prelude;
                block.push(JS::return_(compiled.expr, &mut self.j));
                block
            }
            Node::If { cond, then_, else_ } => {
                self.compile_tail_loop_if_return_block(a, cond, then_, else_, tail_loop)
            }
            Node::Prim { args, info }
                if short_circuit_primitive(&a.prim_payload(info).primitive, a.list(args))
                    .is_some() =>
            {
                let (op, lhs, rhs) =
                    short_circuit_primitive(&a.prim_payload(info).primitive, a.list(args))
                        .expect("checked short-circuit primitive");
                self.compile_short_circuit_tail_loop_return_block(a, op, lhs, rhs, tail_loop)
            }
            Node::Sequence(first, second) => {
                let mut block = self.compile_effect_block(a, first);
                block.extend(self.compile_tail_loop_return_block(a, second, tail_loop));
                block
            }
            Node::StaticRaise { label, args } => {
                if let Some(block) = self.compile_static_raise_jump_block(a, label, args) {
                    return block;
                }
                if let Some(block) =
                    self.compile_fallthrough_static_raise_return_block(a, label, args)
                {
                    return block;
                }
                if let Some(handler) = self.resolve_static_raise(a, label, args) {
                    return self.compile_tail_loop_return_block(a, handler, tail_loop);
                }
                let compiled = self.compile_expr(a, lam);
                let mut block = compiled.prelude;
                if !block_terminates(&self.j, &block) {
                    block.push(JS::return_(compiled.expr, &mut self.j));
                }
                block
            }
            Node::StaticCatch {
                body,
                handler,
                info,
            } => {
                let label = a.catch_payload(info).label;
                let bindings = catch_bindings(a, info);
                // lam_compile.ml:935 — `flatten_nested_caches` is the first
                // step of `compile_staticcatch`. A >1 entry code_table goes
                // through the multi-handler explicit-jump arm
                // (lam_compile.ml:1000-1010).
                let (handlers, flat_body) =
                    flatten_nested_caches(a, label, &bindings, body, handler);
                if handlers.len() > 1 {
                    return self.compile_multi_staticcatch_tail_loop_return_block(
                        a, &handlers, flat_body, tail_loop,
                    );
                }
                let uses_fallthrough =
                    self.uses_fallthrough_staticcatch_return(a, body, label, &bindings, handler);
                let requires_explicit_jump = (self.return_unit_stack.last().copied() == Some(true)
                    && !bindings.is_empty())
                    || self.try_body_depth > 0
                    || self.return_staticcatch_requires_explicit_jump(
                        a, label, &bindings, body, handler,
                    );
                if uses_fallthrough {
                    self.compile_fallthrough_staticcatch_tail_loop_return_block(
                        a, label, &bindings, body, handler, tail_loop,
                    )
                } else if requires_explicit_jump {
                    self.compile_staticcatch_tail_loop_return_block(
                        a, label, &bindings, body, handler, tail_loop,
                    )
                } else if no_static_raise_in_handler_like_ocaml(a, handler)
                    && !lambda_contains_staticcatch(a, handler)
                    && lambda_contains_static_raise_to_label(a, body, label, bindings.len())
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
                        a, label, &bindings, body, handler, tail_loop,
                    )
                } else if lambda_contains_static_raise_to_label(a, body, label, bindings.len()) {
                    // OCaml has no `with_static_handler` analog — when
                    // body raises to this label, OCaml emits the handler
                    // ONCE via explicit-jump (lam_compile.ml:1005-1010 for
                    // Assign / lam_compile.ml:1000-1010 for EffectCall).
                    // Rust's `with_static_handler` path inlines the handler
                    // at every raise site via `resolve_static_raise`.
                    // Prefer explicit-jump to match OCaml's single-emission
                    // shape on miss_colon_test / gpr_1698_test.
                    self.compile_staticcatch_tail_loop_return_block(
                        a, label, &bindings, body, handler, tail_loop,
                    )
                } else {
                    self.with_static_handler(label, &bindings, handler, |this| {
                        this.compile_tail_loop_return_block(a, body, tail_loop)
                    })
                }
            }
            Node::TryWith { body, id, handler } => {
                let exn = a.ident(id);
                // OCaml's `compile_trywith` preserves the surrounding
                // tail-return context for the catch handler but changes only
                // the try body to `Tail_in_try` (compiler/core/lam_compile.ml:
                // 1315-1344). Compile the body through the normal return path
                // so direct self calls inside `try` stay as calls, while the
                // handler can still trigger the self-tailcall loop.
                let body_block = self.compile_return_block(a, body);
                let handler_block = self.compile_tail_loop_return_block(a, handler, tail_loop);
                vec![self.try_statement(body_block, &exn, handler_block)]
            }
            Node::Switch {
                scrut,
                actions,
                info,
            } => self.compile_tail_loop_switch_return_block(
                a,
                scrut,
                Sw { actions, info },
                tail_loop,
            ),
            Node::StringSwitch {
                scrut,
                actions,
                info,
            } => self.compile_tail_loop_string_switch_return_block(
                a,
                scrut,
                StrSw { actions, info },
                tail_loop,
            ),
            _ => {
                let compiled = self.compile_expr(a, lam);
                let mut block = compiled.prelude;
                if !block_terminates(&self.j, &block) {
                    block.push(JS::return_(compiled.expr, &mut self.j));
                }
                block
            }
        }
    }

    fn compile_tail_loop_if_return_block(
        &mut self,
        a: &mut LamArena,
        cond: Lam,
        then_: Lam,
        else_: Lam,
        tail_loop: &mut TailLoopState,
    ) -> Block {
        let cond_compiled = self.compile_expr(a, cond);
        // lam_compile.ml:1514-1518: compile both branches in
        // `NeedValue should_return` first and emit `return e ? a : b` when
        // neither needs statements. A branch with a self tail call compiles
        // to the loop jump there, so it always has a block.
        if !function_has_self_tailcall(a, &tail_loop.tail_targets, then_)
            && !function_has_self_tailcall(a, &tail_loop.tail_targets, else_)
        {
            let then_value = self.compile_expr(a, then_);
            let else_value = self.compile_expr(a, else_);
            if then_value.prelude.is_empty() && else_value.prelude.is_empty() {
                let mut block = cond_compiled.prelude;
                block.push(JS::return_(
                    JE::cond(
                        cond_compiled.expr,
                        then_value.expr,
                        else_value.expr,
                        &mut self.j,
                    ),
                    &mut self.j,
                ));
                return block;
            }
        }
        let then_block = self.compile_tail_loop_return_block(a, then_, tail_loop);
        let else_block = self.compile_tail_loop_return_block(a, else_, tail_loop);

        let mut block = cond_compiled.prelude;
        if let (Some(then_expr), Some(else_expr)) = (
            single_return_expression(&self.j, &then_block),
            single_return_expression(&self.j, &else_block),
        ) {
            let value = JE::cond(cond_compiled.expr, then_expr, else_expr, &mut self.j);
            block.push(JS::return_(value, &mut self.j));
            return block;
        }

        // Mirror OCaml's Lifthenelse compile (lam_compile.ml:1428-1436), which
        // calls `Js_output.output_as_block` on each compiled branch — that
        // calls `unnest_block` (js_output.ml:77-80) before passing to `S.if_`.
        // OCaml's `block_last_is_return_throw_or_continue` (js_stmt_make.ml:186-193)
        // is non-recursive, so an unnested branch ending in `continue`/`return`/`throw`
        // lets rule 7 fire while a Block-wrapped branch keeps the if-else.
        let then_block = JS::unnest_block(then_block, &self.j);
        let else_block = JS::unnest_block(else_block, &self.j);
        let cond_expr = cond_compiled.expr;
        let cond_is_conjunction = matches!(self.j.ek(cond_expr), ExprKind::Bin(BinOp::And, _, _));
        if cond_is_conjunction
            && block_last_is_continue(&self.j, &then_block)
            && block_last_is_non_continue_terminal(&self.j, &else_block)
        {
            // OCaml's tail-call path marks self tail-calls `output_finished=True`
            // and `S.if_` rule 5/7 interactions keep the terminal fallback under
            // a negative guard before the `continue` tail
            // (compiler/core/lam_compile.ml:1582-1629,
            // compiler/core/js_stmt_make.ml:247-250). Rust represents the same
            // tail call directly as assignment statements plus `Continue`, so
            // build that shape explicitly before the generic `Statement::if_`
            // simplifier flips it back to a positive guard.
            let else_block = merge_terminal_guard_fallthrough_else(&mut self.j, else_block);
            let test = JE::not(cond_expr, &mut self.j);
            block.push(JS::if_(test, &else_block, &[], &mut self.j));
            block.extend(then_block);
            return block;
        }
        block.push(JS::if_(cond_expr, &then_block, &else_block, &mut self.j));
        block
    }

    fn compile_short_circuit_tail_loop_return_block(
        &mut self,
        a: &mut LamArena,
        op: ShortCircuitOp,
        lhs: Lam,
        rhs: Lam,
        tail_loop: &mut TailLoopState,
    ) -> Block {
        let default = op.default_lambda(a);
        match op {
            ShortCircuitOp::And => {
                self.compile_tail_loop_if_return_block(a, lhs, rhs, default, tail_loop)
            }
            ShortCircuitOp::Or => {
                self.compile_tail_loop_if_return_block(a, lhs, default, rhs, tail_loop)
            }
        }
    }

    fn compile_tail_loop_switch_return_block(
        &mut self,
        a: &mut LamArena,
        scrut: Lam,
        sw: Sw,
        tail_loop: &mut TailLoopState,
    ) -> Block {
        self.with_switch_depth(|this| {
            this.compile_tail_loop_switch_return_block_inner(a, scrut, sw, tail_loop)
        })
    }

    fn compile_tail_loop_switch_return_block_inner(
        &mut self,
        a: &mut LamArena,
        scrut: Lam,
        sw: Sw,
        tail_loop: &mut TailLoopState,
    ) -> Block {
        if self.uses_named_variant_switch(a, sw) {
            let scrut_compiled = self.compile_expr(a, scrut);
            let (mut block, scrut_expr) = if self.named_variant_switch_needs_bound_scrutinee(a, sw)
            {
                self.bind_switch_scrutinee_once(scrut_compiled.prelude, scrut_compiled.expr)
            } else {
                (scrut_compiled.prelude, scrut_compiled.expr)
            };
            let switch = sw.decode(a);
            block.extend(
                self.compile_named_variant_switch_tail_loop_return_statements(
                    a, scrut_expr, &switch, tail_loop,
                ),
            );
            return block;
        }

        let scrut_compiled = self.compile_expr(a, scrut);
        let mut block = scrut_compiled.prelude;
        let fail = sw.fail(a);
        let grouped_cases = self.grouped_switch_cases(a, &sw.consts(a), fail, |_, _| true);
        let mut cases = Vec::with_capacity(grouped_cases.len());
        let mut group_start = 0;
        while group_start < grouped_cases.len() {
            let mut group_end = group_start;
            while !grouped_cases[group_end].2 {
                group_end += 1;
            }

            let body = grouped_cases[group_end].1;
            let compiled_body = self.compile_tail_loop_return_block(a, body, tail_loop);
            let group_falls_through = compiled_body.is_empty();
            // Tail-loop lowering is Rust-specific, but it must preserve OCaml's
            // `compile_general_cases` break semantics: the last grouped case
            // uses `Js_output.to_break_block`, then return continuation keeps
            // that break only when the source lambda has an exit
            // (compiler/core/lam_compile.ml:613-624;
            // compiler/core/js_output.ml:88-100).
            let should_break = self.return_case_needs_break_like_ocaml(a, body, &compiled_body);

            for (tag, case_lam, _) in &grouped_cases[group_start..group_end] {
                cases.push((
                    tag.clone(),
                    self.empty_switch_case_clause_for(a, *case_lam),
                    group_falls_through,
                ));
            }
            cases.push((
                grouped_cases[group_end].0.clone(),
                Clause {
                    source_loc: self.source_loc_of_lam(a, body),
                    body: {
                        let body = self.with_block_source_loc(a, body, compiled_body);
                        JS::list(&body, &mut self.j)
                    },
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

        let default_block = fail
            .map(|fallback| self.compile_tail_loop_return_block(a, fallback, tail_loop))
            .filter(|body| !body.is_empty());

        block.push(JS::int_switch(
            scrut_compiled.expr,
            cases,
            default_block.map(|b| JS::list(&b, &mut self.j)),
            &mut self.j,
        ));
        block
    }

    fn compile_tail_loop_string_switch_return_block(
        &mut self,
        a: &mut LamArena,
        scrut: Lam,
        sw: StrSw,
        tail_loop: &mut TailLoopState,
    ) -> Block {
        self.with_switch_depth(|this| {
            this.compile_tail_loop_string_switch_return_block_inner(a, scrut, sw, tail_loop)
        })
    }

    fn compile_tail_loop_string_switch_return_block_inner(
        &mut self,
        a: &mut LamArena,
        scrut: Lam,
        sw: StrSw,
        tail_loop: &mut TailLoopState,
    ) -> Block {
        let scrut_compiled = self.compile_expr(a, scrut);
        let mut block = scrut_compiled.prelude;
        let cases = sw.cases(a);
        let default = sw.default(a);
        let borrowed_cases: Vec<_> = cases
            .iter()
            .map(|(tag, body)| (SwitchCaseTag::String(tag.clone()), *body))
            .collect();

        if let Some(small) = self.compile_small_string_switch_tail_loop_return(
            a,
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
        let grouped = self.grouped_switch_cases(a, &cases, default, |_, _| true);
        let clauses = self.grouped_tail_loop_return_string_clauses(
            a,
            grouped,
            SwitchCaseTag::String,
            tail_loop,
        );

        let default_block = default
            .map(|fallback| self.compile_tail_loop_return_block(a, fallback, tail_loop))
            .filter(|body| !body.is_empty());

        block.push(JS::string_switch(
            scrut_compiled.expr,
            clauses,
            default_block.map(|b| JS::list(&b, &mut self.j)),
            &mut self.j,
        ));
        block
    }

    fn try_compile_self_tailcall_block(
        &mut self,
        a: &mut LamArena,
        func: Lam,
        args: LamList,
        tail_loop: &mut TailLoopState,
    ) -> Option<Block> {
        let function = a.as_var(func)?;
        if !tail_loop
            .tail_targets
            .iter()
            .any(|target| function.same(target))
        {
            return None;
        }

        let mut block = Vec::new();
        let mut compiled_args = Vec::new();
        for arg in a.list_small(args) {
            let compiled = self.compile_expr(a, arg);
            block.extend(compiled.prelude);
            compiled_args.push(compiled.expr);
        }
        tail_loop.triggered = true;
        let args = if tail_loop.params.is_empty() {
            Vec::new()
        } else {
            compiled_args
        };
        let mut assignments = Vec::new();
        for (param, arg) in tail_loop.params.iter().zip(args) {
            if matches!(self.j.ek(arg), ExprKind::Var(id) if self.j.ident(id).same(param)) {
                continue;
            }

            let target = *tail_loop
                .new_params
                .entry(*param)
                .or_insert_with(|| self.fresh_ident(&format!("_{}", param.name())));
            let target = JE::var(target, &mut self.j);
            let assign = JE::bin(BinOp::Eq, target, arg, &mut self.j);
            assignments.push(JS::exp(assign, &mut self.j));
        }
        block.extend(assignments.into_iter().rev());
        block.push(JS::continue_(None, &mut self.j));
        Some(block)
    }

    fn compile_effect_output(&mut self, a: &mut LamArena, lam: Lam) -> Compiled {
        match a.node(lam) {
            Node::Let {
                kind,
                id,
                value,
                body,
            } => {
                let id = a.ident(id);
                if let Some(compiled) = self.try_compile_record_spread(a, &id, value, body) {
                    return compiled;
                }

                let mut prelude = self.compile_let_binding(a, kind, &id, value);
                if block_terminates(&self.j, &prelude) {
                    return Compiled {
                        prelude,
                        expr: JE::undefined(false, &mut self.j),
                    };
                }
                let body_compiled = self.compile_effect_output(a, body);
                prelude.extend(body_compiled.prelude);
                Compiled {
                    prelude,
                    expr: body_compiled.expr,
                }
            }
            Node::Apply { func, args, info } => self.compile_apply_call(a, func, args, info),
            Node::If { cond, then_, else_ } => {
                let block = self.compile_if_effect_block(a, cond, then_, else_);
                compiled_from_effect_block(&mut self.j, block)
            }
            Node::Sequence(first, second) => {
                let first = self.compile_effect_output(a, first);
                let second = self.compile_effect_output(a, second);
                self.append_effect_output(first, second)
            }
            Node::TryWith { body, id, handler } => {
                let exn = a.ident(id);
                let body_block = self.compile_effect_block(a, body);
                let handler_block = self.compile_effect_block(a, handler);
                let stmt = self.try_statement(body_block, &exn, handler_block);
                compiled_from_effect_block(&mut self.j, vec![stmt])
            }
            Node::StaticCatch {
                body,
                handler,
                info,
            } => {
                let label = a.catch_payload(info).label;
                let bindings = catch_bindings(a, info);
                let (handlers, flat_body) =
                    flatten_nested_caches(a, label, &bindings, body, handler);
                if handlers.len() > 1 {
                    // lam_compile.ml:935 + 1000-1010 — multi-handler
                    // explicit-jump arm for an effect-value continuation.
                    return Compiled {
                        prelude: self
                            .compile_multi_staticcatch_effect_block(a, &handlers, flat_body),
                        expr: JE::undefined(false, &mut self.j),
                    };
                }
                // OCaml's `Lsequence` compiles its head with
                // `EffectCall Not_tail`; in `compile_staticcatch`
                // (lam_compile.ml:984-1059), that continuation always falls
                // through to the explicit-jump arm. Keep the same shape here
                // instead of inlining the handler at every raise site.
                Compiled {
                    prelude: self
                        .compile_staticcatch_effect_block(a, label, &bindings, body, handler),
                    expr: JE::undefined(false, &mut self.j),
                }
            }
            Node::Switch {
                scrut,
                actions,
                info,
            } => Compiled {
                prelude: self.compile_switch_effect_block(a, scrut, Sw { actions, info }),
                expr: JE::undefined(false, &mut self.j),
            },
            Node::StringSwitch {
                scrut,
                actions,
                info,
            } => Compiled {
                prelude: self.compile_string_switch_effect_block(a, scrut, StrSw { actions, info }),
                expr: JE::undefined(false, &mut self.j),
            },
            _ => self.compile_expr(a, lam),
        }
    }

    fn append_effect_output(&mut self, first: Compiled, second: Compiled) -> Compiled {
        if block_finishes_output(&mut self.j, &first.prelude) {
            return Compiled {
                prelude: first.prelude,
                expr: JE::undefined(false, &mut self.j),
            };
        }

        let first_is_pure = js_expr_no_side_effects(&self.j, first.expr);
        if first.prelude.is_empty() {
            if first_is_pure {
                return second;
            }
            if second.prelude.is_empty() {
                return Compiled {
                    prelude: vec![],
                    expr: js_seq(first.expr, second.expr, &mut self.j),
                };
            }
        }

        let mut prelude = first.prelude;
        if !first_is_pure {
            push_effect_expression(&mut self.j, &mut prelude, first.expr);
        }
        prelude.extend(second.prelude);
        Compiled {
            prelude,
            expr: second.expr,
        }
    }

    fn compiled_to_effect_block(&mut self, compiled: Compiled) -> Block {
        let mut block = compiled.prelude;
        if block_finishes_output(&self.j, &block) {
            return block;
        }
        push_effect_expression(&mut self.j, &mut block, compiled.expr);
        block
    }

    fn compile_if_effect_block(
        &mut self,
        a: &mut LamArena,
        cond: Lam,
        then_: Lam,
        else_: Lam,
    ) -> Block {
        let cond_compiled = self.compile_expr(a, cond);
        let then_compiled = self.compile_expr(a, then_);
        let else_compiled = self.compile_expr(a, else_);

        let then_prelude_empty = then_compiled.prelude.is_empty();
        let else_prelude_empty = else_compiled.prelude.is_empty();
        let then_expr_pure = js_expr_no_side_effects(&self.j, then_compiled.expr);
        let else_expr_pure = js_expr_no_side_effects(&self.j, else_compiled.expr);

        let mut block = cond_compiled.prelude;
        let cond_expr = cond_compiled.expr;

        if then_prelude_empty && else_prelude_empty {
            match (
                remove_pure_subexpression(then_compiled.expr.clone(), &mut self.j),
                remove_pure_subexpression(else_compiled.expr.clone(), &mut self.j),
            ) {
                (None, None) => {
                    // OCaml's `S.if_ cond [] []` collapses to `S.exp cond`
                    // (js_stmt_make.ml:242 + 45-53). Preserve non-Number/
                    // Undefined pure expressions like `tmp === null;`.
                    push_s_exp(&mut self.j, &mut block, cond_expr);
                    return block;
                }
                (Some(then_expr), Some(else_expr)) => {
                    let value = JE::cond(cond_expr, then_expr, else_expr, &mut self.j);
                    push_effect_expression(&mut self.j, &mut block, value);
                    return block;
                }
                (Some(then_expr), None) => {
                    block.push(JS::if_(
                        cond_expr,
                        &[JS::exp(then_expr, &mut self.j)],
                        &[],
                        &mut self.j,
                    ));
                    return block;
                }
                (None, Some(else_expr)) => {
                    block.push(JS::if_(
                        JE::not(cond_expr, &mut self.j),
                        &[JS::exp(else_expr, &mut self.j)],
                        &[],
                        &mut self.j,
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
            block.push(JS::if_(
                JE::not(cond_expr, &mut self.j),
                &JS::unnest_block(self.compile_effect_block(a, else_), &self.j),
                &[],
                &mut self.j,
            ));
            return block;
        }

        if else_prelude_empty && else_expr_pure {
            block.push(JS::if_(
                cond_expr,
                &JS::unnest_block(self.compile_effect_block(a, then_), &self.j),
                &[],
                &mut self.j,
            ));
            return block;
        }

        // OCaml S.if_ rule 5 (js_stmt_make.ml:247-248): when the else branch
        // is *exactly* `[Return _]`, flip to `if (!cond) { return; }` and
        // emit the then branch as sibling statements.
        let then_block = JS::unnest_block(self.compile_effect_block(a, then_), &self.j);
        let else_block = JS::unnest_block(self.compile_effect_block(a, else_), &self.j);
        if matches!(
            else_block.as_slice(),
            [stmt] if matches!(self.j.sk(*stmt), StmtKind::Return(_))
        ) {
            block.push(JS::if_(
                JE::not(cond_expr, &mut self.j),
                &else_block,
                &[],
                &mut self.j,
            ));
            block.extend(then_block);
            return block;
        }
        // OCaml S.if_ rule 7 (js_stmt_make.ml:249-250): when the then branch
        // ends with return/throw/continue/break, keep `if (cond) { then }`
        // and append the else branch as sibling statements.
        if !then_block.is_empty() && JS::block_last_is_terminal(&self.j, &then_block) {
            block.push(JS::if_(cond_expr, &then_block, &[], &mut self.j));
            block.extend(else_block);
            return block;
        }

        block.push(JS::if_(cond_expr, &then_block, &else_block, &mut self.j));
        block
    }

    fn compile_if_assignment_block(
        &mut self,
        a: &mut LamArena,
        result: &Ident,
        cond: Lam,
        then_: Lam,
        else_: Lam,
    ) -> Block {
        let cond_compiled = self.compile_expr(a, cond);
        let then_block = self.compile_assign_to_target_block(a, result, then_);
        let else_block = self.compile_assign_to_target_block(a, result, else_);

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
        &mut self,
        result: &Ident,
        cond: Expr,
        then_block: Block,
        else_block: Block,
    ) -> Block {
        let (cond, then_block, else_block) =
            normalize_if_assignment_merge_order(&mut self.j, cond, then_block, else_block);
        match (
            self.take_single_result_assignment(result, then_block),
            self.take_single_result_assignment(result, else_block),
        ) {
            (Ok(then_expr), Ok(else_expr)) => {
                let value = JE::cond(cond, then_expr, else_expr, &mut self.j);
                vec![self.result_assignment(result, value)]
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
                vec![JS::if_(cond, &then_block, &else_block, &mut self.j)]
            }
        }
    }

    fn compile_declared_if_block(
        &mut self,
        kind: LetKind,
        id: &Ident,
        cond: Expr,
        then_block: Block,
        else_block: Block,
    ) -> Block {
        let (cond, then_block, else_block) =
            normalize_if_assignment_merge_order(&mut self.j, cond, then_block, else_block);
        match (
            self.take_single_result_assignment(id, then_block),
            self.take_single_result_assignment(id, else_block),
        ) {
            (Ok(then_expr), Ok(else_expr)) => {
                vec![JS::variable(
                    VarDecl {
                        ident: *id,
                        value: Some(JE::cond(cond, then_expr, else_expr, &mut self.j)),
                        property: kind,
                        ident_info: IdentInfo::default(),
                    },
                    &mut self.j,
                )]
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
                    JS::variable(
                        VarDecl {
                            ident: *id,
                            value: None,
                            property: kind,
                            ident_info: IdentInfo::default(),
                        },
                        &mut self.j,
                    ),
                    JS::if_(cond, &then_block, &else_block, &mut self.j),
                ]
            }
        }
    }

    /// `(target, rhs)` of an assignment statement `target = rhs`.
    fn assignment_parts(&self, stmt: Stmt) -> Option<(Ident, Expr)> {
        let StmtKind::Exp(e) = self.j.sk(stmt) else {
            return None;
        };
        let ExprKind::Bin(BinOp::Eq, lhs, rhs) = self.j.ek(e) else {
            return None;
        };
        match self.j.ek(lhs) {
            ExprKind::Var(target) => Some((self.j.ident(target), rhs)),
            _ => None,
        }
    }

    pub(crate) fn take_single_result_assignment(
        &self,
        id: &Ident,
        block: Block,
    ) -> Result<Expr, Block> {
        match block.as_slice() {
            [stmt] => match self.assignment_parts(*stmt) {
                Some((target, rhs)) if target.same(id) => Ok(rhs),
                _ => Err(block),
            },
            _ => Err(block),
        }
    }

    fn result_assignment(&mut self, id: &Ident, expr: Expr) -> Stmt {
        JS::exp(
            JE::bin(BinOp::Eq, JE::var(*id, &mut self.j), expr, &mut self.j),
            &mut self.j,
        )
    }

    /// Stmt-valued forms make OCaml's preliminary `NeedValue` pass return
    /// a non-empty block before the `S.if_` fallback
    /// (compiler/core/lam_compile.ml:1495-1524), so Rust must not rebuild them
    /// from later `Return` blocks as if they were pure expressions.
    fn lambda_contains_statement_value_form(a: &LamArena, lam: Lam) -> bool {
        let any = |xs: &[Lam]| {
            xs.iter()
                .any(|x| Self::lambda_contains_statement_value_form(a, *x))
        };
        match a.view(lam) {
            View::Switch(..)
            | View::StringSwitch(..)
            | View::StaticCatch(..)
            | View::TryWith(..)
            | View::While(..)
            | View::For(..)
            | View::ForOf(..)
            | View::ForAwaitOf(..)
            | View::StaticRaise(..)
            | View::Break
            | View::Continue
            // OCaml `compile_assign` (lam_compile.ml) always emits the
            // assignment as a statement, whatever the continuation.
            | View::Assign(..) => true,
            View::Let(_, _, value, body) => {
                Self::lambda_contains_statement_value_form(a, value)
                    || Self::lambda_contains_statement_value_form(a, body)
            }
            View::LetRec(_, values, body) => {
                any(values) || Self::lambda_contains_statement_value_form(a, body)
            }
            View::Sequence(first, second) => {
                Self::lambda_contains_statement_value_form(a, first)
                    || Self::lambda_contains_statement_value_form(a, second)
            }
            View::If(cond, then_, else_) => {
                Self::lambda_contains_statement_value_form(a, cond)
                    || Self::lambda_contains_statement_value_form(a, then_)
                    || Self::lambda_contains_statement_value_form(a, else_)
            }
            View::Prim(_, args, _) => any(args),
            View::Apply { func, args, .. } => {
                Self::lambda_contains_statement_value_form(a, func) || any(args)
            }
            View::Function { .. } => false,
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
        &mut self,
        kind: LetKind,
        id: &Ident,
        mut body: Block,
    ) -> Block {
        if let Some(last) = body.last().copied()
            && let Some((target, rhs)) = self.assignment_parts(last)
            && target.same(id)
        {
            body.pop();
            body.push(JS::define(*id, Some(rhs), kind, &mut self.j));
            return body;
        }
        let mut result = Vec::with_capacity(body.len() + 1);
        result.push(JS::variable(
            VarDecl {
                ident: *id,
                value: None,
                property: kind,
                ident_info: IdentInfo::default(),
            },
            &mut self.j,
        ));
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
    fn try_fold_effect_only_return_tail(&mut self, block: &Block) -> Option<Expr> {
        let (last, prefix) = block.split_last()?;
        let StmtKind::Return(tail_expr) = self.j.sk(*last) else {
            return None;
        };
        // Check the shape before building any node.
        if !prefix
            .iter()
            .all(|stmt| matches!(self.j.sk(*stmt), StmtKind::Exp(_)))
        {
            return None;
        }

        let mut result = tail_expr;
        for stmt in prefix.iter().rev() {
            let StmtKind::Exp(effect) = self.j.sk(*stmt) else {
                unreachable!("checked above")
            };
            result = js_seq(effect, result, &mut self.j);
        }
        Some(result)
    }

    fn compile_if_return_block(
        &mut self,
        a: &mut LamArena,
        cond: Lam,
        then_: Lam,
        else_: Lam,
    ) -> Block {
        let key = then_;
        self.if_return_finished.insert(key, false);
        let cond_compiled = self.compile_expr(a, cond);
        let then_block_raw = self.compile_return_block(a, then_);
        let else_block_raw = self.compile_return_block(a, else_);

        // OCaml's preliminary `NeedValue should_return` pass is the reference
        // shape (compiler/core/lam_compile.ml:1495-1524). Rust's
        // `compile_expr` currently flattens short-circuit primitives to JS
        // `&&`/`||` earlier than OCaml's `compile_sequand`/`compile_sequor`
        // path (compiler/core/lam_compile.ml:1663-1664), so preserve the
        // nested conditional by folding return blocks when the original
        // branches contain no statement-valued forms. Switches/static catches
        // stay excluded because OCaml's NeedValue pass keeps their prelude,
        // which must fall through to `S.if_` below.
        if !Self::lambda_contains_statement_value_form(a, then_)
            && !Self::lambda_contains_statement_value_form(a, else_)
        {
            if let (Some(then_seq), Some(else_seq)) = (
                self.try_fold_effect_only_return_tail(&then_block_raw),
                self.try_fold_effect_only_return_tail(&else_block_raw),
            ) {
                self.if_return_finished.insert(key, true);
                let mut block = cond_compiled.prelude;
                block.push(JS::return_(
                    JE::cond(cond_compiled.expr, then_seq, else_seq, &mut self.j),
                    &mut self.j,
                ));
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
        let then_value = self.compile_expr(a, then_);
        let else_value = self.compile_expr(a, else_);
        if then_value.prelude.is_empty() && else_value.prelude.is_empty() {
            self.if_return_finished.insert(key, true);
            let mut block = cond_compiled.prelude;
            block.push(JS::return_(
                JE::cond(
                    cond_compiled.expr,
                    then_value.expr,
                    else_value.expr,
                    &mut self.j,
                ),
                &mut self.j,
            ));
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
        &mut self,
        cond: Expr,
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
        &mut self,
        cond: Expr,
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
        if strict_single_return_expr(&self.j, &then_fallback).is_some()
            && strict_single_return_expr(&self.j, &else_fallback).is_some()
        {
            let take_return = |block: Block| match block.first().map(|stmt| self.j.sk(*stmt)) {
                Some(StmtKind::Return(expr)) => expr,
                _ => unreachable!("strict single return block"),
            };
            let then_expr = take_return(then_fallback);
            let else_expr = take_return(else_fallback);
            // Go through `S.if_` instead of calling `E.econd` directly:
            // OCaml applies the `Js_not` branch swap before the
            // single-Return fold (compiler/core/js_stmt_make.ml:237-246).
            return vec![JS::if_(
                cond,
                &[JS::return_(then_expr, &mut self.j)],
                &[JS::return_(else_expr, &mut self.j)],
                &mut self.j,
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
            [stmt] if matches!(self.j.sk(*stmt), StmtKind::Return(_))
        ) {
            let mut out = vec![JS::if_(
                JE::not(cond, &mut self.j),
                &else_fallback,
                &[],
                &mut self.j,
            )];
            out.extend(then_fallback);
            // OCaml wraps the rule-5 result with `block
            // ({If ...} :: ifso)` (compiler/core/js_stmt_make.ml:
            // 247-248, with `block` at lines 37-42). That block
            // boundary is observable by an outer `S.if_`: it hides the
            // trailing return until `js_pass_flatten` runs later.
            return vec![JS::block(&out, &mut self.j)];
        }
        // Use the normalized fallback blocks when we can't collapse
        // to `Return(Cond)`, matching the previous behavior for
        // non-both-single-return cases.
        vec![JS::if_(cond, &then_fallback, &else_fallback, &mut self.j)]
    }

    pub(crate) fn compile_switch_value_block(
        &mut self,
        a: &mut LamArena,
        result: &Ident,
        lam: Lam,
    ) -> Block {
        let mut block = self.compile_assign_to_target_block(a, result, lam);
        if !block_terminates(&self.j, &block) {
            block.push(JS::break_(None, &mut self.j));
        }
        block
    }

    pub(crate) fn compile_assign_to_target_block(
        &mut self,
        a: &mut LamArena,
        result: &Ident,
        lam: Lam,
    ) -> Block {
        match a.node(lam) {
            Node::Let {
                kind,
                id,
                value,
                body,
            } => {
                let id = a.ident(id);
                if let Some(compiled) = self.try_compile_record_spread(a, &id, value, body) {
                    let mut block = compiled.prelude;
                    block.push(JS::exp(
                        JE::bin(
                            BinOp::Eq,
                            JE::var(*result, &mut self.j),
                            compiled.expr,
                            &mut self.j,
                        ),
                        &mut self.j,
                    ));
                    return block;
                }

                let mut block = self.compile_let_binding(a, kind, &id, value);
                block.extend(self.compile_assign_to_target_block(a, result, body));
                block
            }
            Node::Apply { func, args, info } => {
                let compiled = self.compile_apply_call(a, func, args, info);
                let mut block = compiled.prelude;
                block.push(JS::exp(
                    JE::bin(
                        BinOp::Eq,
                        JE::var(*result, &mut self.j),
                        compiled.expr,
                        &mut self.j,
                    ),
                    &mut self.j,
                ));
                block
            }
            Node::Sequence(first, second) => {
                let mut block = self.compile_effect_block(a, first);
                block.extend(self.compile_assign_to_target_block(a, result, second));
                block
            }
            Node::StaticCatch {
                body,
                handler,
                info,
            } => {
                let label = a.catch_payload(info).label;
                let bindings = catch_bindings(a, info);
                // OCaml's `compile_staticcatch` (lam_compile.ml:937-1017)
                // gates pseudo-jmp on `EffectCall (Maybe_tail_is_return
                // (Tail_with_name {in_staticcatch=false}))`. For an `Assign`
                // continuation — which is where `compile_assign_to_target_block`
                // sits — the match falls into the explicit-jump arm at
                // lam_compile.ml:1005-1010 (`| Assign _ -> ...`). Take the
                // explicit-jump path unconditionally; the `with_static_handler`
                // shortcut is a Rust-only optimization with no OCaml analog in
                // this continuation.
                let (handlers, flat_body) =
                    flatten_nested_caches(a, label, &bindings, body, handler);
                if handlers.len() > 1 {
                    self.compile_multi_staticcatch_assignment_block(a, result, &handlers, flat_body)
                } else {
                    self.compile_staticcatch_assignment_block(
                        a, result, label, &bindings, body, handler,
                    )
                }
            }
            Node::TryWith { body, id, handler } => {
                let exn = a.ident(id);
                let body_block = self.compile_assign_to_target_block(a, result, body);
                let handler_block = self.compile_assign_to_target_block(a, result, handler);
                vec![self.try_statement(body_block, &exn, handler_block)]
            }
            Node::If { cond, then_, else_ } => {
                self.compile_if_assignment_block(a, result, cond, then_, else_)
            }
            // compile_sequand / compile_sequor with an `Assign v` continuation
            // (lam_compile.ml:1138-1210).
            Node::Prim { args, info }
                if short_circuit_primitive(&a.prim_payload(info).primitive, a.list(args))
                    .is_some() =>
            {
                let (op, lhs, rhs) =
                    short_circuit_primitive(&a.prim_payload(info).primitive, a.list(args))
                        .expect("checked above");
                let lhs_compiled = self.compile_expr(a, lhs);
                let rhs_compiled = self.compile_expr(a, rhs);
                let assign = |j: &mut JsArena, value: Expr| {
                    let target = JE::var(*result, j);
                    let assign = JE::bin(BinOp::Eq, target, value, j);
                    JS::exp(assign, j)
                };
                let mut block = lhs_compiled.prelude;
                if rhs_compiled.prelude.is_empty() {
                    let op = match op {
                        ShortCircuitOp::And => BinOp::And,
                        ShortCircuitOp::Or => BinOp::Or,
                    };
                    let value = JE::bin(op, lhs_compiled.expr, rhs_compiled.expr, &mut self.j);
                    block.push(assign(&mut self.j, value));
                    return block;
                }
                let mut rhs_block = rhs_compiled.prelude;
                rhs_block.push(assign(&mut self.j, rhs_compiled.expr));
                let test = op.test_expr(lhs_compiled.expr, &mut self.j);
                let default = op.default_expr(&mut self.j);
                let else_block = [assign(&mut self.j, default)];
                block.push(JS::if_(test, &rhs_block, &else_block, &mut self.j));
                block
            }
            Node::Switch {
                scrut,
                actions,
                info,
            } => self.compile_switch_assignment_block(a, result, scrut, Sw { actions, info }),
            Node::StringSwitch {
                scrut,
                actions,
                info,
            } => self.compile_string_switch_assignment_block(
                a,
                result,
                scrut,
                StrSw { actions, info },
            ),
            Node::StaticRaise { label, args } => {
                // OCaml's `compile_staticraise` (lam_compile.ml:887-904) ignores
                // the enclosing Assign continuation and emits only the argument
                // assignments + `exit = N`. Without this arm we would fall
                // through to the generic case below, which appends a spurious
                // `result = undefined` after the jump even though control has
                // already transferred to the post-body exit dispatch.
                if let Some(block) = self.compile_static_raise_jump_block(a, label, args) {
                    return block;
                }
                if let Some(handler) = self.resolve_static_raise(a, label, args) {
                    return self.compile_assign_to_target_block(a, result, handler);
                }
                let compiled = self.compile_expr(a, lam);
                let mut block = compiled.prelude;
                if !block_terminates(&self.j, &block) {
                    block.push(JS::exp(
                        JE::bin(
                            BinOp::Eq,
                            JE::var(*result, &mut self.j),
                            compiled.expr,
                            &mut self.j,
                        ),
                        &mut self.j,
                    ));
                }
                block
            }
            _ => {
                let compiled = self.compile_expr(a, lam);
                let mut block = compiled.prelude;
                if !block_terminates(&self.j, &block) {
                    block.push(JS::exp(
                        JE::bin(
                            BinOp::Eq,
                            JE::var(*result, &mut self.j),
                            compiled.expr,
                            &mut self.j,
                        ),
                        &mut self.j,
                    ));
                }
                block
            }
        }
    }

    fn compile_switch_assignment_block(
        &mut self,
        a: &mut LamArena,
        result: &Ident,
        scrut: Lam,
        sw: Sw,
    ) -> Block {
        self.with_switch_depth(|this| {
            this.compile_switch_assignment_block_inner(a, result, scrut, sw)
        })
    }

    fn compile_switch_assignment_block_inner(
        &mut self,
        a: &mut LamArena,
        result: &Ident,
        scrut: Lam,
        sw: Sw,
    ) -> Block {
        if self.uses_untagged_variant_switch(a, sw) {
            let scrut_compiled = self.compile_expr(a, scrut);
            let (mut block, scrut_expr) =
                self.bind_switch_scrutinee_once(scrut_compiled.prelude, scrut_compiled.expr);
            block.extend({
                let switch = sw.decode(a);
                self.compile_untagged_variant_switch_assignment_statements(
                    a, result, scrut_expr, &switch,
                )
            });
            return block;
        }

        if self.uses_named_variant_switch(a, sw) {
            let scrut_compiled = self.compile_expr(a, scrut);
            let (mut block, scrut_expr) = if self.named_variant_switch_needs_bound_scrutinee(a, sw)
            {
                self.bind_switch_scrutinee_once(scrut_compiled.prelude, scrut_compiled.expr)
            } else {
                (scrut_compiled.prelude, scrut_compiled.expr)
            };
            block.extend({
                let switch = sw.decode(a);
                self.compile_named_variant_switch_assignment_statements(
                    a, result, scrut_expr, &switch,
                )
            });
            return block;
        }

        let scrut_compiled = self.compile_expr(a, scrut);
        let mut block = scrut_compiled.prelude;

        let fail = sw.fail(a);
        let grouped = self.grouped_switch_cases(a, &sw.consts(a), fail, |_, _| true);
        let mut cases = Vec::with_capacity(grouped.len());
        for (tag, body, is_last) in grouped {
            let clause = if is_last {
                crate::js_ir::arena::Clause {
                    source_loc: self.source_loc_of_lam(a, body),
                    body: {
                        let body = {
                            let value_block = self.compile_switch_value_block(a, result, body);
                            self.with_block_source_loc(a, body, value_block)
                        };
                        JS::list(&body, &mut self.j)
                    },
                    should_break: false,
                    comment: None,
                }
            } else {
                self.empty_switch_case_clause_for(a, body)
            };
            cases.push((direct_switch_int(tag), clause));
        }

        let default_block = fail.map(|fallback| {
            let block = self.compile_assign_to_target_block(a, result, fallback);
            self.with_block_source_loc(a, fallback, block)
        });

        block.push(JS::int_switch(
            scrut_compiled.expr,
            cases,
            default_block.map(|b| JS::list(&b, &mut self.j)),
            &mut self.j,
        ));
        block
    }

    fn compile_string_switch_assignment_block(
        &mut self,
        a: &mut LamArena,
        result: &Ident,
        scrut: Lam,
        sw: StrSw,
    ) -> Block {
        self.with_switch_depth(|this| {
            this.compile_string_switch_assignment_block_inner(a, result, scrut, sw)
        })
    }

    fn compile_string_switch_assignment_block_inner(
        &mut self,
        a: &mut LamArena,
        result: &Ident,
        scrut: Lam,
        sw: StrSw,
    ) -> Block {
        let scrut_compiled = self.compile_expr(a, scrut);
        let mut block = scrut_compiled.prelude;
        let cases = sw.cases(a);
        let default = sw.default(a);
        let borrowed_cases: Vec<_> = cases
            .iter()
            .map(|(tag, body)| (SwitchCaseTag::String(tag.clone()), *body))
            .collect();

        if let Some(small) = self.compile_small_string_switch_assignment(
            a,
            result,
            scrut_compiled.expr.clone(),
            &borrowed_cases,
            default,
            default.is_none(),
        ) {
            block.extend(small);
            return block;
        }

        let grouped = self.grouped_switch_cases(a, &cases, default, |_, _| true);
        let mut clauses = Vec::with_capacity(grouped.len());
        for (tag, body, is_last) in grouped {
            let clause = if is_last {
                crate::js_ir::arena::Clause {
                    source_loc: self.source_loc_of_lam(a, body),
                    body: {
                        let body = {
                            let value_block = self.compile_switch_value_block(a, result, body);
                            self.with_block_source_loc(a, body, value_block)
                        };
                        JS::list(&body, &mut self.j)
                    },
                    should_break: false,
                    comment: None,
                }
            } else {
                self.empty_switch_case_clause_for(a, body)
            };
            clauses.push(crate::js_ir::arena::StringClauseInfo {
                tag_type: SwitchCaseTag::String(tag),
                clause,
            });
        }

        let default_block = default.map(|fallback| {
            let block = self.compile_assign_to_target_block(a, result, fallback);
            self.with_block_source_loc(a, fallback, block)
        });

        block.push(JS::string_switch(
            scrut_compiled.expr,
            clauses,
            default_block.map(|b| JS::list(&b, &mut self.j)),
            &mut self.j,
        ));
        block
    }

    fn compile_switch_return_block(&mut self, a: &mut LamArena, scrut: Lam, sw: Sw) -> Block {
        self.with_switch_depth(|this| this.compile_switch_return_block_inner(a, scrut, sw))
    }

    fn compile_switch_return_block_inner(&mut self, a: &mut LamArena, scrut: Lam, sw: Sw) -> Block {
        if self.uses_untagged_variant_switch(a, sw) {
            let scrut_compiled = self.compile_expr(a, scrut);
            let (mut block, scrut_expr) =
                self.bind_switch_scrutinee_once(scrut_compiled.prelude, scrut_compiled.expr);
            let switch = sw.decode(a);
            block.extend(
                self.compile_untagged_variant_switch_return_statements(a, scrut_expr, &switch),
            );
            return block;
        }

        if self.uses_named_variant_switch(a, sw) {
            let scrut_compiled = self.compile_expr(a, scrut);
            let (mut block, scrut_expr) = if self.named_variant_switch_needs_bound_scrutinee(a, sw)
            {
                self.bind_switch_scrutinee_once(scrut_compiled.prelude, scrut_compiled.expr)
            } else {
                (scrut_compiled.prelude, scrut_compiled.expr)
            };
            let switch = sw.decode(a);
            block.extend(
                self.compile_named_variant_switch_return_statements(a, scrut_expr, &switch),
            );
            return block;
        }

        let scrut_compiled = self.compile_expr(a, scrut);
        let mut block = scrut_compiled.prelude;

        let fail = sw.fail(a);
        let grouped_cases = self.grouped_switch_cases(a, &sw.consts(a), fail, |_, _| true);
        let mut cases = Vec::with_capacity(grouped_cases.len());
        let mut group_start = 0;
        while group_start < grouped_cases.len() {
            let mut group_end = group_start;
            while !grouped_cases[group_end].2 {
                group_end += 1;
            }

            let body = grouped_cases[group_end].1;
            let compiled_body = self.compile_return_block(a, body);
            let group_falls_through = compiled_body.is_empty();
            // Mirror OCaml's `lam_compile.ml` pseudo-jmp emission: when a
            // case body resolved away through a fallthrough static-raise
            // handler, OCaml still prints an explicit `break;` to exit the
            // switch so the subsequent appended handler reads cleanly.
            let should_break = self.return_case_needs_break_like_ocaml(a, body, &compiled_body);

            for (tag, case_lam, _) in &grouped_cases[group_start..group_end] {
                cases.push((
                    tag.clone(),
                    self.empty_switch_case_clause_for(a, *case_lam),
                    group_falls_through,
                ));
            }
            cases.push((
                grouped_cases[group_end].0.clone(),
                crate::js_ir::arena::Clause {
                    source_loc: self.source_loc_of_lam(a, body),
                    body: {
                        let body = self.with_block_source_loc(a, body, compiled_body);
                        JS::list(&body, &mut self.j)
                    },
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

        let default_block = fail
            .map(|fallback| self.compile_return_block(a, fallback))
            .filter(|body| !body.is_empty());

        block.push(JS::int_switch(
            scrut_compiled.expr,
            cases,
            default_block.map(|b| JS::list(&b, &mut self.j)),
            &mut self.j,
        ));
        block
    }

    fn compile_string_switch_return_block(
        &mut self,
        a: &mut LamArena,
        scrut: Lam,
        sw: StrSw,
    ) -> Block {
        self.with_switch_depth(|this| this.compile_string_switch_return_block_inner(a, scrut, sw))
    }

    fn compile_string_switch_return_block_inner(
        &mut self,
        a: &mut LamArena,
        scrut: Lam,
        sw: StrSw,
    ) -> Block {
        let scrut_compiled = self.compile_expr(a, scrut);
        let mut block = scrut_compiled.prelude;
        let cases = sw.cases(a);
        let default = sw.default(a);
        let borrowed_cases: Vec<_> = cases
            .iter()
            .map(|(tag, body)| (SwitchCaseTag::String(tag.clone()), *body))
            .collect();

        if let Some(small) = self.compile_small_string_switch_return(
            a,
            scrut_compiled.expr.clone(),
            &borrowed_cases,
            default,
            default.is_none(),
        ) {
            block.extend(small);
            return block;
        }

        let grouped = self.grouped_switch_cases(a, &cases, default, |_, _| true);
        let clauses = self.grouped_return_string_clauses(a, grouped, SwitchCaseTag::String);

        let default_block = default
            .map(|fallback| self.compile_return_block(a, fallback))
            .filter(|body| !body.is_empty());

        block.push(JS::string_switch(
            scrut_compiled.expr,
            clauses,
            default_block.map(|b| JS::list(&b, &mut self.j)),
            &mut self.j,
        ));
        block
    }

    fn compile_switch_effect_block(&mut self, a: &mut LamArena, scrut: Lam, sw: Sw) -> Block {
        self.with_switch_depth(|this| this.compile_switch_effect_block_inner(a, scrut, sw))
    }

    fn compile_switch_effect_block_inner(&mut self, a: &mut LamArena, scrut: Lam, sw: Sw) -> Block {
        if self.uses_untagged_variant_switch(a, sw) {
            let scrut_compiled = self.compile_expr(a, scrut);
            let (mut block, scrut_expr) =
                self.bind_switch_scrutinee_once(scrut_compiled.prelude, scrut_compiled.expr);
            let dispatch = {
                let switch = sw.decode(a);
                self.compile_untagged_variant_switch_effect_statements(
                    a,
                    scrut_expr.clone(),
                    &switch,
                )
            };
            if dispatch.is_empty() {
                // OCaml's switch compilation collapses an empty dispatch to
                // `S.exp scrut` (via js_output.ml + js_stmt_make.ml:45-53),
                // preserving bare comparisons like `tmp === null;`.
                push_s_exp(&mut self.j, &mut block, scrut_expr);
            } else {
                block.extend(dispatch);
            }
            return block;
        }

        if self.uses_named_variant_switch(a, sw) {
            let scrut_compiled = self.compile_expr(a, scrut);
            let (mut block, scrut_expr) = if self.named_variant_switch_needs_bound_scrutinee(a, sw)
            {
                self.bind_switch_scrutinee_once(scrut_compiled.prelude, scrut_compiled.expr)
            } else {
                (scrut_compiled.prelude, scrut_compiled.expr)
            };
            let dispatch = {
                let switch = sw.decode(a);
                self.compile_named_variant_switch_effect_statements(a, scrut_expr.clone(), &switch)
            };
            if dispatch.is_empty() {
                // OCaml's switch collapses to `S.exp scrut` when the whole
                // dispatch is unit (js_stmt_make.ml:45-53) — keeps bare
                // comparisons as `Exp` statements.
                push_s_exp(&mut self.j, &mut block, scrut_expr);
                return block;
            }
            block.extend(dispatch);
            return block;
        }

        let scrut_compiled = self.compile_expr(a, scrut);
        let mut block = scrut_compiled.prelude;

        let fail = sw.fail(a);
        let grouped = self.grouped_switch_cases(a, &sw.consts(a), fail, |_, _| true);
        let mut cases = Vec::with_capacity(grouped.len());
        for (tag, body, is_last) in grouped {
            let clause = if is_last {
                let source_loc = self.source_loc_of_lam(a, body);
                let body_block = self.compile_effect_block(a, body);
                let body = self.with_block_source_loc(a, body, body_block);
                crate::js_ir::arena::Clause {
                    source_loc,
                    should_break: !block_terminates(&self.j, &body),
                    body: JS::list(&body, &mut self.j),
                    comment: None,
                }
            } else {
                self.empty_switch_case_clause_for(a, body)
            };
            cases.push((direct_switch_int(tag), clause));
        }

        let default_block = fail
            .map(|fallback| {
                let block = self.compile_effect_block(a, fallback);
                self.with_block_source_loc(a, fallback, block)
            })
            .filter(|body| !body.is_empty());

        let has_effectful_case = cases
            .iter()
            .any(|(_, clause)| !self.j.stmts(clause.body).is_empty())
            || default_block.as_ref().is_some_and(|body| !body.is_empty());
        if !has_effectful_case {
            // OCaml collapses an all-empty switch to `S.exp scrut`
            // (js_stmt_make.ml:45-53), preserving bare pure expressions.
            push_s_exp(&mut self.j, &mut block, scrut_compiled.expr);
            return block;
        }

        block.push(JS::int_switch(
            scrut_compiled.expr,
            cases,
            default_block.map(|b| JS::list(&b, &mut self.j)),
            &mut self.j,
        ));
        block
    }

    fn compile_string_switch_effect_block(
        &mut self,
        a: &mut LamArena,
        scrut: Lam,
        sw: StrSw,
    ) -> Block {
        self.with_switch_depth(|this| this.compile_string_switch_effect_block_inner(a, scrut, sw))
    }

    fn compile_string_switch_effect_block_inner(
        &mut self,
        a: &mut LamArena,
        scrut: Lam,
        sw: StrSw,
    ) -> Block {
        let scrut_compiled = self.compile_expr(a, scrut);
        let mut block = scrut_compiled.prelude;
        let cases = sw.cases(a);
        let default = sw.default(a);
        let borrowed_cases: Vec<_> = cases
            .iter()
            .map(|(tag, body)| (SwitchCaseTag::String(tag.clone()), *body))
            .collect();

        if let Some(small) = self.compile_small_string_switch_effect(
            a,
            scrut_compiled.expr.clone(),
            &borrowed_cases,
            default,
            false,
        ) {
            if small.is_empty() {
                // OCaml collapses an all-empty switch to `S.exp scrut`
                // (js_stmt_make.ml:45-53), preserving bare pure expressions.
                push_s_exp(&mut self.j, &mut block, scrut_compiled.expr);
            } else {
                block.extend(small);
            }
            return block;
        }

        let grouped = self.grouped_switch_cases(a, &cases, default, |_, _| true);
        let mut clauses = Vec::with_capacity(grouped.len());
        for (tag, body, is_last) in grouped {
            let clause = if is_last {
                let source_loc = self.source_loc_of_lam(a, body);
                let body_block = self.compile_effect_block(a, body);
                let body = self.with_block_source_loc(a, body, body_block);
                crate::js_ir::arena::Clause {
                    source_loc,
                    should_break: !block_terminates(&self.j, &body),
                    body: JS::list(&body, &mut self.j),
                    comment: None,
                }
            } else {
                self.empty_switch_case_clause_for(a, body)
            };
            clauses.push(crate::js_ir::arena::StringClauseInfo {
                tag_type: SwitchCaseTag::String(tag),
                clause,
            });
        }

        let default_block = default
            .map(|fallback| {
                let block = self.compile_effect_block(a, fallback);
                self.with_block_source_loc(a, fallback, block)
            })
            .filter(|body| !body.is_empty());

        let has_effectful_case = clauses
            .iter()
            .any(|clause| !self.j.stmts(clause.clause.body).is_empty())
            || default_block.as_ref().is_some_and(|body| !body.is_empty());
        if !has_effectful_case {
            // OCaml collapses an all-empty string switch to `S.exp scrut`
            // (js_stmt_make.ml:45-53), preserving bare pure expressions.
            push_s_exp(&mut self.j, &mut block, scrut_compiled.expr);
            return block;
        }

        block.push(JS::string_switch(
            scrut_compiled.expr,
            clauses,
            default_block.map(|b| JS::list(&b, &mut self.j)),
            &mut self.j,
        ));
        block
    }

    pub(crate) fn compile_external_arg_const(&mut self, cst: &Cst) -> Expr {
        match cst {
            Cst::ArgIntLit(i) => JE::number(
                Number::Int {
                    i: *i as i32,
                    c: None,
                },
                &mut self.j,
            ),
            // lam_compile_const.ml `translate_arg_cst`.
            Cst::ArgStringLit(s) => JE::string(&s, &mut self.j),
            Cst::ArgJsonLit(s) => JE::new(
                ExprKind::JsonLiteral(JE::str_id(&s, &mut self.j)),
                &mut self.j,
            ),
        }
    }

    pub(crate) fn runtime_member_expr(&mut self, module_name: &str, member: &str) -> Expr {
        JE::qualified(
            ModuleId {
                id: Ident::create_persistent(module_name),
                kind: Kind::Runtime,
                dynamic_import: false,
            },
            Some(member.to_string()),
            &mut self.j,
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
        &mut self,
        module_name: &str,
        member: &str,
        args: Vec<Expr>,
    ) -> Expr {
        JE::call(
            self.runtime_member_expr(module_name, member),
            &args,
            Self::builtin_runtime_call_info(),
            &mut self.j,
        )
    }

    pub(crate) fn int32_div_expr(&mut self, left: Expr, right: Expr) -> Expr {
        match (self.j.ek(left), int_literal(&mut self.j, right)) {
            (ExprKind::Length(_, _), Some(2)) => {
                JE::bin(BinOp::Asr, left, int_expr(1, &mut self.j), &mut self.j)
            }
            (_, Some(rhs)) if rhs != 0 => match int_literal(&self.j, left) {
                Some(lhs) => int_expr(lhs.wrapping_div(rhs), &mut self.j),
                None => to_int32(JE::bin(BinOp::Div, left, right, &mut self.j), &mut self.j),
            },
            _ if self.check_div_by_zero => {
                self.runtime_call_expr("Primitive_int", "div", vec![left, right])
            }
            _ => to_int32(JE::bin(BinOp::Div, left, right, &mut self.j), &mut self.j),
        }
    }

    pub(crate) fn int32_mod_expr(&mut self, left: Expr, right: Expr) -> Expr {
        match int_literal(&mut self.j, right) {
            Some(rhs) if rhs != 0 => JE::bin(BinOp::Mod, left, right, &mut self.j),
            _ if self.check_div_by_zero => {
                self.runtime_call_expr("Primitive_int", "mod_", vec![left, right])
            }
            _ => JE::bin(BinOp::Mod, left, right, &mut self.j),
        }
    }

    pub(crate) fn bigint_div_expr(&mut self, left: Expr, right: Expr) -> Expr {
        if self.check_div_by_zero {
            self.runtime_call_expr("Primitive_bigint", "div", vec![left, right])
        } else {
            JE::bin(BinOp::Div, left, right, &mut self.j)
        }
    }

    pub(crate) fn bigint_mod_expr(&mut self, left: Expr, right: Expr) -> Expr {
        if self.check_div_by_zero {
            self.runtime_call_expr("Primitive_bigint", "mod_", vec![left, right])
        } else {
            JE::bin(BinOp::Mod, left, right, &mut self.j)
        }
    }

    fn with_static_handler<T>(
        &mut self,
        label: i32,
        bindings: &[Ident],
        handler: Lam,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        self.static_handlers.push(StaticHandler {
            label,
            bindings: bindings.to_vec(),
            handler,
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

    /// The handler a static raise to `label` with `args` runs, its
    /// parameters substituted by the arguments.
    fn resolve_static_raise(&self, a: &mut LamArena, label: i32, args: LamList) -> Option<Lam> {
        let handler = self
            .static_handlers
            .iter()
            .rev()
            .find(|handler| handler.label == label)?;
        if handler.bindings.len() != a.list_len(args) {
            return None;
        }
        if handler.bindings.is_empty() {
            return Some(handler.handler);
        }

        let subst: crate::lambda::lam_subst::Subst = handler
            .bindings
            .iter()
            .copied()
            .zip(a.list(args).iter().copied())
            .collect();
        Some(crate::lambda::lam_subst::subst(a, &subst, handler.handler))
    }

    fn return_staticcatch_requires_explicit_jump(
        &self,
        a: &LamArena,
        label: i32,
        bindings: &[Ident],
        body: Lam,
        handler: Lam,
    ) -> bool {
        if bindings.is_empty()
            && matches!(a.node(body), Node::StaticCatch { .. })
            && self.handler_is_inlineable_pure_return_static_raise_dispatch(a, handler)
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
        // handler-inline at a `LstaticRaise` site pops the matching entry from
        // `static_handlers` first, so the handler body sees the depth as it
        // was at the outer Lstaticcatch's entry — matching OCaml's
        // `compile_lambda lambda_cxt handler` (lam_compile.ml:962),
        // which uses the original `lambda_cxt` for the handler.
        if !self.static_handlers.is_empty()
            || !self.static_jump_handlers.is_empty()
            || !self.fallthrough_return_handlers.is_empty()
        {
            return true;
        }

        self.return_handler_requires_explicit_staticcatch_jump(a, handler)
            || (lambda_has_multiple_static_raises_to_label(a, body, label, bindings.len())
                && lambda_contains_static_raise_to_other_label(a, handler, label)
                && !self.handler_is_pure_outward_static_raise_forwarder(a, handler))
    }

    fn handler_is_pure_outward_static_raise_forwarder(&self, a: &LamArena, lam: Lam) -> bool {
        match a.view(lam) {
            View::StaticRaise(label, args) => {
                self.active_static_raise_target_exists(label, args.len())
                    && args.iter().all(|x| lam_analysis::no_side_effects(a, *x))
            }
            View::Let(kind, _, value, body)
                if matches!(kind, LetKind::Alias | LetKind::Strict | LetKind::StrictOpt)
                    && lam_analysis::no_side_effects(a, value)
                    && !self.lambda_requires_explicit_staticcatch_jump(a, value) =>
            {
                self.handler_is_pure_outward_static_raise_forwarder(a, body)
            }
            View::Sequence(first, second)
                if lam_analysis::no_side_effects(a, first)
                    && !self.lambda_requires_explicit_staticcatch_jump(a, first) =>
            {
                self.handler_is_pure_outward_static_raise_forwarder(a, second)
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

    fn return_handler_requires_explicit_staticcatch_jump(&self, a: &LamArena, lam: Lam) -> bool {
        match a.view(lam) {
            View::Var(_) | View::GlobalModule(_) | View::Const(_) => false,
            View::If(..)
            | View::Switch(..)
            | View::StringSwitch(..)
            | View::Let(..)
            | View::Sequence(..)
                if handler_has_static_raise_like_ocaml(a, lam)
                    && !self.handler_is_pure_outward_static_raise_forwarder(a, lam) =>
            {
                true
            }
            View::Function { .. } => false,
            View::StaticRaise(label, args) => {
                !self.active_static_raise_target_exists(label, args.len())
                    || args
                        .iter()
                        .any(|arg| self.return_handler_requires_explicit_staticcatch_jump(a, *arg))
            }
            View::StaticCatch(body, label, bindings, handler) => {
                ((self.return_unit_stack.last().copied() == Some(true)) && !bindings.is_empty())
                    || self.return_staticcatch_requires_explicit_jump(
                        a, label, bindings, body, handler,
                    )
            }
            _ => any_child(a, lam, |x| {
                self.return_handler_requires_explicit_staticcatch_jump(a, x)
            }),
        }
    }

    fn handler_is_inlineable_pure_return_static_raise_dispatch(
        &self,
        a: &LamArena,
        lam: Lam,
    ) -> bool {
        self.handler_is_pure_outward_static_raise_forwarder(a, lam)
            || self
                .pure_return_static_raise_dispatch_has_terminal_value(a, lam)
                .unwrap_or(false)
    }

    fn pure_return_static_raise_dispatch_has_terminal_value(
        &self,
        a: &LamArena,
        lam: Lam,
    ) -> Option<bool> {
        match a.view(lam) {
            View::StaticRaise(label, args) => {
                let args_are_pure = args.iter().all(|x| lam_analysis::no_side_effects(a, *x));
                if self.active_static_raise_target_exists(label, args.len()) && args_are_pure {
                    Some(false)
                } else {
                    None
                }
            }
            View::Let(kind, _, value, body)
                if matches!(kind, LetKind::Alias | LetKind::Strict | LetKind::StrictOpt)
                    && lam_analysis::no_side_effects(a, value) =>
            {
                self.pure_return_static_raise_dispatch_has_terminal_value(a, body)
            }
            View::Sequence(first, second) if lam_analysis::no_side_effects(a, first) => {
                self.pure_return_static_raise_dispatch_has_terminal_value(a, second)
            }
            View::If(cond, then_, else_) if lam_analysis::no_side_effects(a, cond) => {
                let then_has_value =
                    self.pure_return_static_raise_dispatch_has_terminal_value(a, then_)?;
                let else_has_value =
                    self.pure_return_static_raise_dispatch_has_terminal_value(a, else_)?;
                Some(then_has_value || else_has_value)
            }
            View::Switch(scrut, switch) if lam_analysis::no_side_effects(a, scrut) => {
                let mut has_terminal_value = false;
                for body in switch
                    .actions
                    .consts
                    .iter()
                    .chain(switch.actions.blocks)
                    .copied()
                    .chain(switch.actions.fail)
                {
                    has_terminal_value |=
                        self.pure_return_static_raise_dispatch_has_terminal_value(a, body)?;
                }
                Some(has_terminal_value)
            }
            View::StringSwitch(scrut, sw) if lam_analysis::no_side_effects(a, scrut) => {
                let mut has_terminal_value = false;
                for body in sw.actions.iter().copied().chain(sw.default) {
                    has_terminal_value |=
                        self.pure_return_static_raise_dispatch_has_terminal_value(a, body)?;
                }
                Some(has_terminal_value)
            }
            _ if lam_analysis::no_side_effects(a, lam) => Some(true),
            _ => None,
        }
    }

    fn lambda_requires_explicit_staticcatch_jump(&self, a: &LamArena, lam: Lam) -> bool {
        match a.view(lam) {
            View::Var(_) | View::GlobalModule(_) | View::Const(_) => false,
            View::StaticRaise(label, args) => {
                !self.active_static_raise_target_exists(label, args.len())
                    || args
                        .iter()
                        .any(|arg| self.lambda_requires_explicit_staticcatch_jump(a, *arg))
            }
            View::StaticCatch(..) => true,
            // Including function bodies.
            _ => any_child(a, lam, |x| {
                self.lambda_requires_explicit_staticcatch_jump(a, x)
            }),
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

    fn compile_static_raise_jump_block(
        &mut self,
        a: &mut LamArena,
        label: i32,
        args: LamList,
    ) -> Option<Block> {
        let handler = self
            .static_jump_handlers
            .iter()
            .rev()
            .find(|handler| handler.label == label)?
            .clone();
        if handler.bindings.len() != a.list_len(args) {
            return None;
        }

        let mut block = Vec::new();
        for (binding, arg) in handler.bindings.iter().zip(a.list_small(args)) {
            block.extend(self.compile_assign_to_target_block(a, binding, arg));
        }
        block.push(JS::exp(
            JE::bin(
                BinOp::Eq,
                JE::var(handler.exit_id, &mut self.j),
                JE::number(Number::int(handler.exit_code), &mut self.j),
                &mut self.j,
            ),
            &mut self.j,
        ));
        Some(block)
    }

    fn staticcatch_declarations(&mut self, exit_id: &Ident, bindings: &[Ident]) -> Block {
        let mut declarations = vec![JS::variable(
            VarDecl {
                ident: *exit_id,
                value: Some(JE::number(Number::int(0), &mut self.j)),
                property: LetKind::Variable,
                ident_info: IdentInfo::default(),
            },
            &mut self.j,
        )];
        declarations.extend(bindings.iter().map(|binding| {
            JS::variable(
                VarDecl {
                    ident: *binding,
                    value: None,
                    property: LetKind::Variable,
                    ident_info: IdentInfo::default(),
                },
                &mut self.j,
            )
        }));
        declarations
    }

    fn staticcatch_exit_test(&mut self, exit_id: &Ident, exit_code: i32) -> Expr {
        JE::bin(
            BinOp::EqEqEq,
            JE::var(*exit_id, &mut self.j),
            JE::number(Number::int(exit_code), &mut self.j),
            &mut self.j,
        )
    }

    fn compile_staticcatch_assignment_block(
        &mut self,
        a: &mut LamArena,
        result: &Ident,
        label: i32,
        bindings: &[Ident],
        body: Lam,
        handler: Lam,
    ) -> Block {
        let exit_id = self.fresh_ident("exit");
        let exit_code = self.next_static_jump_exit_code();
        let mut block = self.staticcatch_declarations(&exit_id, bindings);
        let (body_block, handler_block) =
            self.with_static_jump_handler(label, &exit_id, bindings, |this| {
                let body_block = this.compile_assign_to_target_block(a, result, body);
                let handler_block = if block_terminates(&this.j, &body_block) {
                    vec![]
                } else {
                    this.compile_assign_to_target_block(a, result, handler)
                };
                (body_block, handler_block)
            });
        block.extend(body_block);
        if !block_terminates(&self.j, &block) && !handler_block.is_empty() {
            block.push(JS::if_(
                self.staticcatch_exit_test(&exit_id, exit_code),
                &handler_block,
                &[],
                &mut self.j,
            ));
        }
        block
    }

    fn compile_staticcatch_effect_block(
        &mut self,
        a: &mut LamArena,
        label: i32,
        bindings: &[Ident],
        body: Lam,
        handler: Lam,
    ) -> Block {
        let exit_id = self.fresh_ident("exit");
        let exit_code = self.next_static_jump_exit_code();
        let mut block = self.staticcatch_declarations(&exit_id, bindings);
        let (body_block, handler_block) =
            self.with_static_jump_handler(label, &exit_id, bindings, |this| {
                let body_block = this.compile_effect_block(a, body);
                let handler_block = if block_terminates(&this.j, &body_block) {
                    vec![]
                } else {
                    this.compile_effect_block(a, handler)
                };
                (body_block, handler_block)
            });
        block.extend(body_block);
        if !block_terminates(&self.j, &block) && !handler_block.is_empty() {
            block.push(JS::if_(
                self.staticcatch_exit_test(&exit_id, exit_code),
                &handler_block,
                &[],
                &mut self.j,
            ));
        }
        block
    }

    fn compile_staticcatch_return_block(
        &mut self,
        a: &mut LamArena,
        label: i32,
        bindings: &[Ident],
        body: Lam,
        handler: Lam,
    ) -> Block {
        let exit_id = self.fresh_ident("exit");
        let exit_code = self.next_static_jump_exit_code();
        let mut block = self.staticcatch_declarations(&exit_id, bindings);
        let (body_block, handler_block) =
            self.with_static_jump_handler(label, &exit_id, bindings, |this| {
                let body_block = this.compile_return_block(a, body);
                let handler_block = if block_terminates(&this.j, &body_block) {
                    vec![]
                } else {
                    this.compile_return_block(a, handler)
                };
                (body_block, handler_block)
            });
        block.extend(body_block);
        if !block_terminates(&self.j, &block) && !handler_block.is_empty() {
            block.push(JS::if_(
                self.staticcatch_exit_test(&exit_id, exit_code),
                &handler_block,
                &[],
                &mut self.j,
            ));
        }
        block
    }

    fn compile_staticcatch_tail_loop_return_block(
        &mut self,
        a: &mut LamArena,
        label: i32,
        bindings: &[Ident],
        body: Lam,
        handler: Lam,
        tail_loop: &mut TailLoopState,
    ) -> Block {
        let exit_id = self.fresh_ident("exit");
        let exit_code = self.next_static_jump_exit_code();
        let mut block = self.staticcatch_declarations(&exit_id, bindings);
        let (body_block, handler_block) =
            self.with_static_jump_handler(label, &exit_id, bindings, |this| {
                let body_block = this.compile_tail_loop_return_block(a, body, tail_loop);
                let handler_block = if block_terminates(&this.j, &body_block) {
                    vec![]
                } else {
                    this.compile_tail_loop_return_block(a, handler, tail_loop)
                };
                (body_block, handler_block)
            });
        block.extend(body_block);
        if !block_terminates(&self.j, &block) && !handler_block.is_empty() {
            block.push(JS::if_(
                self.staticcatch_exit_test(&exit_id, exit_code),
                &handler_block,
                &[],
                &mut self.j,
            ));
        }
        block
    }

    fn compile_staticcatch_expr(
        &mut self,
        a: &mut LamArena,
        label: i32,
        bindings: &[Ident],
        body: Lam,
        handler: Lam,
    ) -> Compiled {
        // OCaml NeedValue staticcatch allocates `Ext_ident.create_tmp ()`
        // for the result (compiler/core/lam_compile.ml:1027-1034).
        let result = self.fresh_tmp_ident();
        let mut prelude = vec![JS::variable(
            VarDecl {
                ident: result,
                value: None,
                property: LetKind::Strict,
                ident_info: IdentInfo::default(),
            },
            &mut self.j,
        )];
        prelude.extend(
            self.compile_staticcatch_assignment_block(a, &result, label, bindings, body, handler),
        );
        Compiled {
            prelude,
            expr: JE::var(result, &mut self.j),
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
        let mut block = vec![JS::variable(
            VarDecl {
                ident: exit_id,
                value: Some(JE::number(Number::int(0), &mut self.j)),
                property: LetKind::Variable,
                ident_info: IdentInfo::default(),
            },
            &mut self.j,
        )];
        // lam_compile.ml:973-975: `Ext_list.flat_map code_table (fun
        // {bindings} -> map bindings (fun x -> S.declare_variable))`.
        // Iterate handlers in flat-catches order (innermost first) so the
        // declarations come out in the same order OCaml emits them.
        for handler in handlers {
            for binding in &handler.bindings {
                block.push(JS::variable(
                    VarDecl {
                        ident: *binding,
                        value: None,
                        property: LetKind::Variable,
                        ident_info: IdentInfo::default(),
                    },
                    &mut self.j,
                ));
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
    fn compile_grouped_staticcatch_handlers(
        &mut self,
        a: &mut LamArena,
        handlers: &[FlatHandler],
        first_code: i32,
        mut compile: impl FnMut(&mut Self, &mut LamArena, Lam) -> Block,
    ) -> Vec<(i32, Block, bool, Lam)> {
        let cases = handlers
            .iter()
            .enumerate()
            .map(|(i, handler)| {
                (
                    first_code + i32::try_from(i).expect("exit handler index fits in i32"),
                    handler.handler,
                )
            })
            .collect();
        let grouped = stable_group_switch_cases(a, cases, |_, _| true);
        let mut out = Vec::with_capacity(grouped.len());
        for (code, handler, is_last) in grouped {
            let block = if is_last {
                compile(self, a, handler)
            } else {
                Vec::new()
            };
            out.push((code, block, is_last, handler));
        }
        out
    }

    /// Emit the `compile_cases ~cxt ~switch_exp:exit_expr handlers` call at
    /// lam_compile.ml:987/996/1010/1017. For a single handler + NonComplete
    /// default this reduces to `if (exit === code) { handler_block }`
    /// (compile_general_cases lam_compile.ml:551-557). For multiple handlers
    /// it becomes an `int_switch` (lam_compile.ml:567-630).
    fn compile_exit_dispatch(
        &mut self,
        a: &LamArena,
        exit_id: &Ident,
        handlers: Vec<(i32, Block, bool, Lam)>,
        is_return_context: bool,
    ) -> Option<Stmt> {
        if handlers.is_empty() {
            return None;
        }
        if handlers.len() == 1 {
            let (code, handler_block, _, _) = handlers.into_iter().next().unwrap();
            if handler_block.is_empty() {
                return None;
            }
            let test = self.staticcatch_exit_test(exit_id, code);
            return Some(JS::if_(test, &handler_block, &[], &mut self.j));
        }
        // OCaml compile_general_cases (lam_compile.ml:668-707) emits empty
        // clauses for all but the last case of an equal-Lambda group.
        let clauses: Vec<(i32, Clause)> = handlers
            .into_iter()
            .map(|(code, body, is_last, handler_lam)| {
                let should_break = is_last
                    && !block_terminates(&self.j, &body)
                    && (!is_return_context || has_exit_code(a, handler_lam, &|_| true));
                (
                    code,
                    Clause {
                        source_loc: None,
                        body: JS::list(&body, &mut self.j),
                        should_break,
                        comment: None,
                    },
                )
            })
            .collect();
        Some(JS::int_switch(
            JE::var(*exit_id, &mut self.j),
            clauses,
            None,
            &mut self.j,
        ))
    }

    fn compile_multi_staticcatch_return_block(
        &mut self,
        a: &mut LamArena,
        handlers: &[FlatHandler],
        body: Lam,
    ) -> Block {
        let (exit_id, first_code, mut block) = self.emit_multi_staticcatch_prelude(handlers);
        let body_block = self.compile_return_block(a, body);
        // If the body already terminates (e.g. every path returned), OCaml
        // would still emit the dispatch but it'd be dead. Match
        // `compile_staticcatch_return_block`'s current behavior: skip it.
        let grouped_handlers = if block_terminates(&self.j, &body_block) {
            Vec::new()
        } else {
            self.compile_grouped_staticcatch_handlers(
                a,
                handlers,
                first_code,
                |this, a, handler| this.compile_return_block(a, handler),
            )
        };
        self.pop_multi_staticcatch_handlers(handlers.len());
        block.extend(body_block);
        if !block_terminates(&self.j, &block) {
            if let Some(dispatch) = self.compile_exit_dispatch(a, &exit_id, grouped_handlers, true)
            {
                block.push(dispatch);
            }
        }
        block
    }

    fn compile_multi_staticcatch_effect_block(
        &mut self,
        a: &mut LamArena,
        handlers: &[FlatHandler],
        body: Lam,
    ) -> Block {
        let (exit_id, first_code, mut block) = self.emit_multi_staticcatch_prelude(handlers);
        let body_block = self.compile_effect_block(a, body);
        let grouped_handlers = if block_terminates(&self.j, &body_block) {
            Vec::new()
        } else {
            self.compile_grouped_staticcatch_handlers(
                a,
                handlers,
                first_code,
                |this, a, handler| this.compile_effect_block(a, handler),
            )
        };
        self.pop_multi_staticcatch_handlers(handlers.len());
        block.extend(body_block);
        if !block_terminates(&self.j, &block) {
            if let Some(dispatch) = self.compile_exit_dispatch(a, &exit_id, grouped_handlers, false)
            {
                block.push(dispatch);
            }
        }
        block
    }

    fn compile_multi_staticcatch_assignment_block(
        &mut self,
        a: &mut LamArena,
        result: &Ident,
        handlers: &[FlatHandler],
        body: Lam,
    ) -> Block {
        let (exit_id, first_code, mut block) = self.emit_multi_staticcatch_prelude(handlers);
        let body_block = self.compile_assign_to_target_block(a, result, body);
        let grouped_handlers = if block_terminates(&self.j, &body_block) {
            Vec::new()
        } else {
            self.compile_grouped_staticcatch_handlers(
                a,
                handlers,
                first_code,
                |this, a, handler| this.compile_assign_to_target_block(a, result, handler),
            )
        };
        self.pop_multi_staticcatch_handlers(handlers.len());
        block.extend(body_block);
        if !block_terminates(&self.j, &block) {
            if let Some(dispatch) = self.compile_exit_dispatch(a, &exit_id, grouped_handlers, false)
            {
                block.push(dispatch);
            }
        }
        block
    }

    fn compile_multi_staticcatch_tail_loop_return_block(
        &mut self,
        a: &mut LamArena,
        handlers: &[FlatHandler],
        body: Lam,
        tail_loop: &mut TailLoopState,
    ) -> Block {
        let (exit_id, first_code, mut block) = self.emit_multi_staticcatch_prelude(handlers);
        let body_block = self.compile_tail_loop_return_block(a, body, tail_loop);
        let grouped_handlers = if block_terminates(&self.j, &body_block) {
            Vec::new()
        } else {
            self.compile_grouped_staticcatch_handlers(
                a,
                handlers,
                first_code,
                |this, a, handler| this.compile_tail_loop_return_block(a, handler, tail_loop),
            )
        };
        self.pop_multi_staticcatch_handlers(handlers.len());
        block.extend(body_block);
        if !block_terminates(&self.j, &block) {
            if let Some(dispatch) = self.compile_exit_dispatch(a, &exit_id, grouped_handlers, true)
            {
                block.push(dispatch);
            }
        }
        block
    }

    #[cfg(test)]
    fn collect_required_modules(&self, block: &[Stmt]) -> Vec<ModuleId> {
        let mut set = OcamlModuleSet::new();
        collect_modules_from_js_block(&self.j, block, &mut set);
        let mut modules = set.to_vec();
        ocaml_sort_modules(&mut modules);
        modules
    }
}

fn normalize_if_assignment_merge_order(
    j: &mut JsArena,
    cond: Expr,
    then_block: Block,
    else_block: Block,
) -> (Expr, Block, Block) {
    // OCaml's `Js_stmt_make.if_` handles `Js_not` before it folds
    // same-target branch assignments (compiler/core/js_stmt_make.ml:235-286).
    // Keep that rule order for Rust's eager assignment merge, otherwise a
    // `!(x == null) ? value : undefined` conditional survives where OCaml
    // first swaps branches and emits `x == null ? undefined : value`.
    match j.ek(cond) {
        ExprKind::JsNot(inner) if !else_block.is_empty() => (inner, else_block, then_block),
        _ => (j.with_expr_loc(cond, None), then_block, else_block),
    }
}

/// True if this Lambda unconditionally transfers control out of the
/// enclosing block — its compiled form has no usable fall-through. Matches
/// OCaml's `Js_output.output_finished:True`: `Lbreak` and `Lcontinue` set
/// it directly (lam_compile.ml:1928, 1943); nothing else in this code path
/// is compiled with that flag.
fn lambda_is_unconditional_exit(a: &LamArena, lam: Lam) -> bool {
    matches!(a.node(lam), Node::Break | Node::Continue)
}

/// Whether `f` holds for some direct child of `lam` (any order: callers only
/// combine pure predicates with `||`).
fn any_child(a: &LamArena, lam: Lam, mut f: impl FnMut(Lam) -> bool) -> bool {
    let mut hit = false;
    a.iter_children(lam, |x| {
        if !hit && f(x) {
            hit = true;
        }
    });
    hit
}

/// The `let rec` bindings of a node, as `(id, value)` pairs.
fn letrec_bindings(a: &LamArena, ids: IdentId, values: LamList) -> Vec<(Ident, Lam)> {
    let values = a.list(values);
    a.ident_run(ids, values.len())
        .iter()
        .copied()
        .zip(values.iter().copied())
        .collect()
}

/// The parameters of a static-catch handler.
fn catch_bindings(a: &LamArena, info: CatchId) -> Vec<Ident> {
    a.idents(a.catch_payload(info).params).to_vec()
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

fn recursive_function_binding_value(a: &LamArena, expr: Lam) -> Option<Lam> {
    matches!(a.node(expr), Node::Function { .. }).then_some(expr)
}

fn recursive_binding_dependencies(a: &LamArena, bindings: &[(Ident, Lam)]) -> Vec<Vec<usize>> {
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
        let mut dependencies = free_variables(a, *expr)
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

fn binding_is_ocaml_scc_function(a: &LamArena, bindings: &[(Ident, Lam)], index: usize) -> bool {
    matches!(a.node(bindings[index].1), Node::Function { .. })
}

fn recursive_binding_group_is_function_only(
    a: &LamArena,
    bindings: &[(Ident, Lam)],
    group: &[usize],
) -> bool {
    group
        .iter()
        .all(|&index| binding_is_ocaml_scc_function(a, bindings, index))
}

fn sort_recursive_binding_group(a: &LamArena, bindings: &[(Ident, Lam)], group: &mut [usize]) {
    if recursive_binding_group_is_function_only(a, bindings, group) {
        return;
    }
    group.sort_by_key(|index| !binding_is_ocaml_scc_function(a, bindings, *index));
}

fn recursive_binding_groups(
    a: &LamArena,
    bindings: &[(Ident, Lam)],
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
                sort_recursive_binding_group(a, bindings, group);
            }
            groups
        }
    }
}

fn recursive_function_bindings_in_group(
    a: &LamArena,
    bindings: &[(Ident, Lam)],
    group: &[usize],
) -> AHashMap<Ident, Lam> {
    group
        .iter()
        .filter_map(|&index| {
            let (id, expr) = bindings[index];
            recursive_function_binding_value(a, expr).map(|func| (id, func))
        })
        .collect()
}

fn recursive_function_binding_alias_target(
    a: &LamArena,
    expr: Lam,
    recursive_functions: &AHashMap<Ident, Lam>,
) -> Option<Ident> {
    let target = a.as_var(expr)?;
    recursive_functions
        .keys()
        .find(|function_id| target.same(function_id))
        .copied()
}

fn lower_ocaml_for_range_direction(
    a: &LamArena,
    direction: &crate::lambda::DirectionFlag,
    finish: Lam,
) -> (Lam, ForDirection) {
    match direction {
        crate::lambda::DirectionFlag::Upto => match a.as_prim(finish) {
            Some((Primitive::Psubint, [new_finish, one], _))
                if matches!(a.as_const(*one), Some(Constant::Int { i: 1, .. })) =>
            {
                (*new_finish, ForDirection::Up)
            }
            _ => (finish, ForDirection::Upto),
        },
        crate::lambda::DirectionFlag::Downto => (finish, ForDirection::Downto),
    }
}

fn single_return_expression(j: &JsArena, block: &[Stmt]) -> Option<Expr> {
    let [stmt] = block else {
        return None;
    };
    match j.sk(*stmt) {
        StmtKind::Return(expr) => Some(expr),
        _ => None,
    }
}

fn block_last_is_continue(j: &JsArena, block: &[Stmt]) -> bool {
    block
        .last()
        .is_some_and(|s| matches!(j.sk(*s), StmtKind::Continue(_)))
}

fn block_last_is_non_continue_terminal(j: &JsArena, block: &[Stmt]) -> bool {
    block.last().is_some_and(|s| {
        matches!(
            j.sk(*s),
            StmtKind::Return(_) | StmtKind::Throw(_) | StmtKind::Break(_)
        )
    })
}

fn merge_terminal_guard_fallthrough_else(j: &mut JsArena, block: Block) -> Block {
    let [first, rest @ ..] = block.as_slice() else {
        return block;
    };
    let StmtKind::If(cond, then_block, else_block) = j.sk(*first) else {
        return block;
    };
    if !j.stmts(else_block).is_empty()
        || !JS::block_last_is_terminal(j, j.stmts(then_block))
        || !JS::block_last_is_terminal(j, rest)
    {
        return block;
    }

    // OCaml's `S.if_` can preserve a terminal `if/else` when the branch reaches
    // it as a block-wrapped statement (compiler/core/js_stmt_make.ml:247-250).
    // Rust tail-loop lowering has already flattened that wrapper, so rebuild the
    // same terminal fallback before placing it under the outer negative guard.
    let rest = JS::list(rest, j);
    vec![JS::new(StmtKind::If(cond, then_block, rest), j)]
}

pub(crate) fn trailing_return_expression(j: &JsArena, block: &[Stmt]) -> Option<Expr> {
    match j.sk(*block.last()?) {
        StmtKind::Return(expr) => Some(expr),
        _ => None,
    }
}

fn function_has_self_tailcall(a: &LamArena, tail_targets: &[Ident], lam: Lam) -> bool {
    match a.view(lam) {
        View::Apply { func, .. } => a
            .as_var(func)
            .is_some_and(|id| tail_targets.iter().any(|target| id.same(target))),
        View::Let(_, _, _, body) => function_has_self_tailcall(a, tail_targets, body),
        View::If(_, then_, else_) => {
            function_has_self_tailcall(a, tail_targets, then_)
                || function_has_self_tailcall(a, tail_targets, else_)
        }
        View::Sequence(_, second) => function_has_self_tailcall(a, tail_targets, second),
        View::Prim(primitive, args, _) => short_circuit_primitive(primitive, args)
            .is_some_and(|(_, _, rhs)| function_has_self_tailcall(a, tail_targets, rhs)),
        View::Switch(_, switch) => switch
            .actions
            .consts
            .iter()
            .chain(switch.actions.blocks)
            .copied()
            .chain(switch.actions.fail)
            .any(|body| function_has_self_tailcall(a, tail_targets, body)),
        View::StringSwitch(_, sw) => sw
            .actions
            .iter()
            .copied()
            .chain(sw.default)
            .any(|body| function_has_self_tailcall(a, tail_targets, body)),
        View::StaticCatch(body, _, _, handler) => {
            function_has_self_tailcall(a, tail_targets, body)
                || function_has_self_tailcall(a, tail_targets, handler)
        }
        View::TryWith(_, _, handler) => {
            // OCaml `compile_trywith` changes only the try body's tail type to
            // `Tail_in_try`; the handler keeps the original `Tail_with_name`
            // context (compiler/core/lam_compile.ml:1315-1344).
            function_has_self_tailcall(a, tail_targets, handler)
        }
        View::Var(_)
        | View::GlobalModule(_)
        | View::Const(_)
        | View::Function { .. }
        | View::LetRec(..)
        | View::StaticRaise(..)
        | View::Break
        | View::Continue
        | View::While(..)
        | View::For(..)
        | View::ForOf(..)
        | View::ForAwaitOf(..)
        | View::Assign(..) => false,
    }
}

fn direct_recursive_function_tail_targets_with_group(
    a: &LamArena,
    bindings: &[(Ident, Lam)],
    group: &[usize],
    recursive_functions: &AHashMap<Ident, Lam>,
) -> AHashMap<Ident, Vec<Ident>> {
    let mut tail_targets: AHashMap<Ident, Vec<Ident>> = recursive_functions
        .keys()
        .map(|id| (*id, vec![*id]))
        .collect();

    for &index in group {
        let (id, expr) = bindings[index];
        let Some(function_id) =
            recursive_function_binding_alias_target(a, expr, recursive_functions)
        else {
            continue;
        };
        tail_targets.entry(function_id).or_default().push(id);
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

/// [`collect_possible_required_modules_for_lambda`] over the nodes reachable
/// from `lam`.
pub(crate) fn collect_possible_required_modules_in_arena(
    a: &LamArena,
    lam: Lam,
) -> AHashSet<ModuleId> {
    fn go(a: &LamArena, lam: Lam, seen: &mut AHashSet<ModuleId>) {
        if let Node::GlobalModule(id) = a.node(lam) {
            seen.insert(ModuleId {
                id: a.ident(id),
                kind: Kind::Ml,
                dynamic_import: false,
            });
        }
        a.iter_children(lam, |x| go(a, x, seen));
    }
    let mut seen = AHashSet::new();
    go(a, lam, &mut seen);
    seen
}

pub(crate) fn collect_possible_required_modules_for_lambda(lam: &Lambda) -> AHashSet<ModuleId> {
    // OCaml compiler/core/lam_compile_main.ml:277-284 collects into a hash set
    // and sorts after `populate_required_modules`, so the hash iteration order is
    // intentionally unobservable here.
    let mut seen = AHashSet::new();
    collect_modules_from_lambda(lam, &mut seen);
    seen
}

/// The value an export argument denotes: the bound value of a top-level
/// variable, else the argument itself.
fn export_binding_value(a: &LamArena, bindings: &[(Ident, Lam)], arg: Lam) -> Lam {
    match a.as_var(arg) {
        Some(id) => bindings
            .iter()
            .rev()
            .find_map(|(binding, value)| binding.same(&id).then_some(*value))
            .unwrap_or(arg),
        None => arg,
    }
}

fn collect_cmj_export_constants_from_simplified_lambda(
    a: &LamArena,
    lam: Lam,
) -> AHashMap<String, CmjExportConstant> {
    let mut bindings = Vec::new();
    let Some((exports, args)) = collect_toplevel_export_bindings(a, lam, &mut bindings) else {
        return AHashMap::new();
    };
    let mut constants = AHashMap::new();
    for (export, arg) in exports.iter().zip(args) {
        let value = export_binding_value(a, &bindings, *arg);
        if let Some(constant) = cmj_export_constant_from_lambda(a, value) {
            constants.insert(export.name().to_string(), constant);
        }
    }
    constants
}

/// The non-constant `persistent_closed_lambda` of each export under
/// `-bs-cross-module-opt` (compiler/core/lam_stats_export.ml:53-89):
/// safe-to-inline lambdas that are closed always-inline functions or
/// functors, or small (`Lam_analysis.small_inline_size`) and free of free
/// variables. Constant exports travel as `CmjExportConstant`s. The `.cmj`
/// stores recursive Lambda, so the selected values are exported as trees.
fn collect_cmj_export_lambdas_from_simplified_lambda(
    a: &LamArena,
    lam: Lam,
) -> AHashMap<String, Lambda> {
    let mut bindings = Vec::new();
    let Some((exports, args)) = collect_toplevel_export_bindings(a, lam, &mut bindings) else {
        return AHashMap::new();
    };
    let mut lambdas = AHashMap::new();
    for (export, arg) in exports.iter().zip(args) {
        let value = export_binding_value(a, &bindings, *arg);
        if cmj_export_constant_from_lambda(a, value).is_some()
            || !lam_analysis::safe_to_inline(a, value)
        {
            continue;
        }
        let inline = match a.view(value) {
            View::Function { func, .. }
                if matches!(func.attr.inline, crate::lambda::InlineAttribute::Always)
                    || func.attr.is_a_functor =>
            {
                crate::lambda::lam_closure::is_closed(a, value)
            }
            _ => {
                lam_analysis::size(a, value) < lam_analysis::SMALL_INLINE_SIZE
                    && crate::lambda::lam_closure::free_variables_with_stats(
                        a,
                        &Default::default(),
                        Default::default(),
                        value,
                    )
                    .is_empty()
            }
        };
        if inline {
            lambdas.insert(export.name().to_string(), a.export(value));
        }
    }
    lambdas
}

fn collect_toplevel_export_bindings<'a>(
    a: &'a LamArena,
    lam: Lam,
    bindings: &mut Vec<(Ident, Lam)>,
) -> Option<(&'a [Ident], &'a [Lam])> {
    match a.view(lam) {
        View::Let(_, id, value, body) => {
            bindings.push((id, value));
            collect_toplevel_export_bindings(a, body, bindings)
        }
        View::LetRec(ids, values, body) => {
            bindings.extend(ids.iter().copied().zip(values.iter().copied()));
            collect_toplevel_export_bindings(a, body, bindings)
        }
        View::Sequence(_, right) => collect_toplevel_export_bindings(a, right, bindings),
        View::Prim(Primitive::Pmakeblock(TagInfo::ModuleExport(exports), _), args, _) => {
            Some((&exports[..], args))
        }
        _ => None,
    }
}

fn cmj_export_constant_from_lambda(a: &LamArena, lam: Lam) -> Option<CmjExportConstant> {
    // OCaml writes `.cmj` value metadata from `coerced_input.export_map`
    // (compiler/core/lam_compile_main.ml:290-295), not from the final JS program.
    // Under the default `cross_module_inline = false`, `values_of_export` keeps
    // only direct closed constants: null / undefined / true / false
    // (compiler/core/lam_stats_export.ml:53-61). Do not inspect JS IR here:
    // `compile_external_field` may inline a dependency constant during JS lowering
    // (compiler/core/lam_compile.ml:234-244), but OCaml does not record that in
    // the exporting module's `.cmj`.
    match a.as_const(lam)? {
        Constant::JsNull => Some(CmjExportConstant::Null),
        Constant::JsUndefined { is_unit } => {
            Some(CmjExportConstant::Undefined { is_unit: *is_unit })
        }
        Constant::JsTrue => Some(CmjExportConstant::Bool(true)),
        Constant::JsFalse => Some(CmjExportConstant::Bool(false)),
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
enum TopLevelEffectGroupRef {
    Single(LetKind, Ident, Lam),
    Recursive(IdentId, LamList),
    Nop(Lam),
}

fn top_level_effect_group_single_ref(
    a: &LamArena,
    kind: LetKind,
    ident: Ident,
    body: Lam,
) -> TopLevelEffectGroupRef {
    match (kind, a.node(body)) {
        (LetKind::Strict | LetKind::StrictOpt, Node::Var(_) | Node::Const(_)) => {
            TopLevelEffectGroupRef::Single(LetKind::Alias, ident, body)
        }
        _ => TopLevelEffectGroupRef::Single(kind, ident, body),
    }
}

fn push_top_level_effect_nop_ref(a: &LamArena, lam: Lam, groups: &mut Vec<TopLevelEffectGroupRef>) {
    if !matches!(
        a.node(lam),
        Node::Var(_) | Node::Const(_) | Node::Function { .. }
    ) {
        groups.push(TopLevelEffectGroupRef::Nop(lam));
    }
}

fn collect_top_level_effect_group_refs(
    a: &LamArena,
    lam: Lam,
    groups: &mut Vec<TopLevelEffectGroupRef>,
) -> Lam {
    match a.node(lam) {
        Node::Let {
            kind,
            id,
            value,
            body,
        } => {
            let result = collect_top_level_effect_group_refs(a, value, groups);
            groups.push(top_level_effect_group_single_ref(
                a,
                kind,
                a.ident(id),
                result,
            ));
            collect_top_level_effect_group_refs(a, body, groups)
        }
        Node::LetRec { ids, values, body } => {
            groups.push(TopLevelEffectGroupRef::Recursive(ids, values));
            collect_top_level_effect_group_refs(a, body, groups)
        }
        Node::Sequence(first, second) => {
            let result = collect_top_level_effect_group_refs(a, first, groups);
            push_top_level_effect_nop_ref(a, result, groups);
            collect_top_level_effect_group_refs(a, second, groups)
        }
        _ => lam,
    }
}

fn module_side_effect_reason(a: &LamArena, lam: Lam) -> Option<String> {
    // OCaml `Lam_coercion.flatten` builds top-level groups in source order
    // before `Lam_compile_main.compile_lambda` asks `Lam_compile.no_side_effect`
    // for each group (compiler/core/lam_coercion.ml:179-199,
    // compiler/core/lam_compile_main.ml:210-236). The Rust Lambda backend walks
    // one term rather than OCaml's grouped list, so collect the group handles
    // in the same order.
    let mut groups = Vec::new();
    let result = collect_top_level_effect_group_refs(a, lam, &mut groups);
    groups
        .iter()
        .find_map(|group| match *group {
            TopLevelEffectGroupRef::Single(kind, id, body) => {
                (matches!(kind, LetKind::Strict | LetKind::Variable)
                    && !lam_analysis::no_side_effects(a, body))
                .then(|| id.name().to_string())
            }
            TopLevelEffectGroupRef::Recursive(ids, values) => letrec_bindings(a, ids, values)
                .into_iter()
                .find_map(|(id, body)| {
                    (!lam_analysis::no_side_effects(a, body)).then(|| id.name().to_string())
                }),
            TopLevelEffectGroupRef::Nop(body) => {
                (!lam_analysis::no_side_effects(a, body)).then(String::new)
            }
        })
        .or_else(|| (!lam_analysis::no_side_effects(a, result)).then(String::new))
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

pub(crate) fn compiled_from_effect_block(j: &mut JsArena, block: Block) -> Compiled {
    if let [stmt] = block.as_slice() {
        let stmt = *stmt;
        let comment = j.stmt_comment(stmt).map(str::to_string);
        return match j.sk(stmt) {
            StmtKind::Exp(expr) => {
                let expr = if j.expr_comment(expr).is_none() && comment.is_some() {
                    j.with_expr_comment(expr, comment.as_deref())
                } else {
                    expr
                };
                Compiled {
                    prelude: vec![],
                    expr,
                }
            }
            StmtKind::Block(inner) if comment.is_none() => {
                let inner = j.block_vec(inner);
                compiled_from_effect_block(j, inner)
            }
            _ => Compiled {
                prelude: vec![j.with_stmt_loc(stmt, None)],
                expr: JE::undefined(false, j),
            },
        };
    }

    Compiled {
        prelude: block,
        expr: JE::undefined(false, j),
    }
}

fn lambda_contains_static_raise(a: &LamArena, lam: Lam) -> bool {
    // Including function bodies.
    match a.node(lam) {
        Node::StaticRaise { .. } => true,
        _ => any_child(a, lam, |x| lambda_contains_static_raise(a, x)),
    }
}

fn handler_has_static_raise_like_ocaml(a: &LamArena, handler: Lam) -> bool {
    // OCaml's `Lam_compile_context.no_static_raise_in_handler`
    // (compiler/core/lam_compile_context.ml:105-106) is defined in terms of
    // `Lam_exit_code.has_exit_code`; that search stops at `Lfunction`
    // (compiler/core/lam_exit_code.ml:25-31), because static exits cannot cross
    // function boundaries. Handler guards in Rust must use the same reachability
    // rule instead of the broader `lambda_contains_static_raise`, which also
    // sees static raises nested inside closures.
    has_exit_code(a, handler, &|_| true)
}

fn no_static_raise_in_handler_like_ocaml(a: &LamArena, handler: Lam) -> bool {
    !handler_has_static_raise_like_ocaml(a, handler)
}

pub(crate) fn lambda_has_exit(a: &LamArena, lam: Lam) -> bool {
    match a.node(lam) {
        Node::Function { .. } => false,
        Node::StaticRaise { .. } => true,
        _ => any_child(a, lam, |x| lambda_has_exit(a, x)),
    }
}

impl LambdaCompiler {
    pub(crate) fn return_case_needs_break_like_ocaml(
        &self,
        a: &LamArena,
        body: Lam,
        compiled_body: &Block,
    ) -> bool {
        return_switch_case_needs_break_like_ocaml(
            &self.j,
            a,
            body,
            compiled_body,
            self.in_staticcatch_like_ocaml(),
            &self.if_return_finished,
        )
    }
}

fn return_switch_case_needs_break_like_ocaml(
    j: &JsArena,
    a: &LamArena,
    body: Lam,
    compiled_body: &Block,
    in_staticcatch: bool,
    if_finished: &AHashMap<Lam, bool>,
) -> bool {
    if !lambda_has_exit(a, body) {
        return false;
    }
    if !block_terminates(j, compiled_body) {
        return true;
    }
    return_output_is_compound_like_ocaml(j, a, body, compiled_body, in_staticcatch, if_finished)
}

fn return_output_is_compound_like_ocaml(
    j: &JsArena,
    a: &LamArena,
    body: Lam,
    compiled_body: &Block,
    in_staticcatch: bool,
    if_finished: &AHashMap<Lam, bool>,
) -> bool {
    if let Some(finished) = return_output_finished_like_ocaml(a, body, in_staticcatch, if_finished)
    {
        return !finished;
    }
    match a.node(body) {
        Node::Let { body, .. } | Node::LetRec { body, .. } | Node::Sequence(_, body) => {
            return_output_is_compound_like_ocaml(
                j,
                a,
                body,
                compiled_body,
                in_staticcatch,
                if_finished,
            )
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
        Node::If { .. }
        | Node::Switch { .. }
        | Node::StringSwitch { .. }
        | Node::StaticCatch { .. }
        | Node::TryWith { .. } => return_block_has_multi_test_guard_chain(j, compiled_body),
        _ => false,
    }
}

/// `Js_output.output_finished` of `compile_lambda` in an
/// `EffectCall (Maybe_tail_is_return _)` continuation, where it does not
/// `None` means the form is not modelled here.
fn return_output_finished_like_ocaml(
    a: &LamArena,
    lam: Lam,
    in_staticcatch: bool,
    if_finished: &AHashMap<Lam, bool>,
) -> Option<bool> {
    match a.view(lam) {
        // `compile_let`/`compile_sequence` append the binding or effect output
        // to the body output (js_output.ml `append_output`), so the body's
        // flag wins.
        View::Let(_, _, _, body) | View::LetRec(_, _, body) | View::Sequence(_, body) => {
            return_output_finished_like_ocaml(a, body, in_staticcatch, if_finished)
        }
        // compile_ifthenelse: recorded by `compile_if_return_block`.
        View::If(_, then_, _) => if_finished.get(&then_).copied(),
        // compile_switch (lam_compile.ml:822) and compile_stringswitch return
        // `Js_output.make` without `~output_finished`, and so does the
        // `S.try_` built for `Ltrywith`.
        View::Switch(..) | View::StringSwitch(..) | View::TryWith(..) => Some(false),
        View::StaticCatch(body, label, bindings, handler) => {
            let (code_table, inner_body) = flatten_nested_caches(a, label, bindings, body, handler);
            // lam_compile.ml:1022-1047: only the single-exit pseudo-jump arm
            // (tail position, not already in a static catch, handler without
            // static raises) ends with the handler output; the exit-variable
            // arm ends with `Js_output.make (compile_cases ...)`.
            let [entry] = code_table.as_slice() else {
                return Some(false);
            };
            if in_staticcatch || !no_static_raise_in_handler_like_ocaml(a, entry.handler) {
                return Some(false);
            }
            // `append_output declares (append_output lbody handler)`: a
            // finished body wins, otherwise the handler's flag is kept.
            match return_output_finished_like_ocaml(a, inner_body, true, if_finished)? {
                true => Some(true),
                false => {
                    return_output_finished_like_ocaml(a, entry.handler, in_staticcatch, if_finished)
                }
            }
        }
        _ => None,
    }
}

fn return_block_has_multi_test_guard_chain(j: &JsArena, block: &[Stmt]) -> bool {
    // OCaml's `S.if_` folding happens while compiling each conditional
    // (compiler/core/js_stmt_make.ml:244-250). A single top-level test can
    // still be emitted as an `output_finished=True` return block, while
    // guard chains that leave multiple sibling tests in the switch case are
    // the `output_finished=False` shape observed by `to_break_block`.
    count_top_level_if_statements(j, block) > 1
}

fn count_top_level_if_statements(j: &JsArena, block: &[Stmt]) -> usize {
    block
        .iter()
        .map(|stmt| match j.sk(*stmt) {
            StmtKind::If(_, _, _) => 1,
            StmtKind::Block(block) => count_top_level_if_statements(j, j.stmts(block)),
            _ => 0,
        })
        .sum()
}

fn lambda_contains_staticcatch(a: &LamArena, lam: Lam) -> bool {
    // Including function bodies.
    match a.node(lam) {
        Node::StaticCatch { .. } => true,
        _ => any_child(a, lam, |x| lambda_contains_staticcatch(a, x)),
    }
}

fn lambda_contains_static_raise_to_label(a: &LamArena, lam: Lam, label: i32, arity: usize) -> bool {
    match a.node(lam) {
        Node::Function { .. } => false,
        Node::StaticRaise {
            label: raise_label,
            args,
        } => raise_label == label && a.list_len(args) == arity,
        _ => any_child(a, lam, |x| {
            lambda_contains_static_raise_to_label(a, x, label, arity)
        }),
    }
}

fn switch_cases_contain_static_raise_to_label(
    a: &LamArena,
    const_cases: &[Lam],
    block_cases: &[Lam],
    label: i32,
    arity: usize,
) -> bool {
    const_cases
        .iter()
        .chain(block_cases)
        .any(|body| lambda_contains_static_raise_to_label(a, *body, label, arity))
}

fn string_switch_cases_contain_static_raise_to_label(
    a: &LamArena,
    cases: &[Lam],
    label: i32,
    arity: usize,
) -> bool {
    cases
        .iter()
        .any(|body| lambda_contains_static_raise_to_label(a, *body, label, arity))
}

fn lambda_is_direct_static_raise_to_label(
    a: &LamArena,
    lam: Lam,
    label: i32,
    arity: usize,
) -> bool {
    matches!(a.node(lam), Node::StaticRaise { label: raise_label, args }
        if raise_label == label && a.list_len(args) == arity)
}

fn switch_cases_contain_nontrivial_static_raise_to_label(
    a: &LamArena,
    const_cases: &[Lam],
    block_cases: &[Lam],
    label: i32,
    arity: usize,
) -> bool {
    string_switch_cases_contain_nontrivial_static_raise_to_label(a, const_cases, label, arity)
        || string_switch_cases_contain_nontrivial_static_raise_to_label(
            a,
            block_cases,
            label,
            arity,
        )
}

fn string_switch_cases_contain_nontrivial_static_raise_to_label(
    a: &LamArena,
    cases: &[Lam],
    label: i32,
    arity: usize,
) -> bool {
    cases.iter().any(|body| {
        lambda_contains_static_raise_to_label(a, *body, label, arity)
            && !lambda_is_direct_static_raise_to_label(a, *body, label, arity)
    })
}

fn lambda_has_multiple_static_raises_to_label(
    a: &LamArena,
    lam: Lam,
    label: i32,
    arity: usize,
) -> bool {
    lambda_static_raise_count_to_label(a, lam, label, arity) >= 2
}

/// Static raises to `label` with `arity` arguments outside function bodies,
/// saturated at 2.
fn lambda_static_raise_count_to_label(a: &LamArena, lam: Lam, label: i32, arity: usize) -> usize {
    let mut count = match a.node(lam) {
        Node::Function { .. } => return 0,
        Node::StaticRaise {
            label: raise_label,
            args,
        } => usize::from(raise_label == label && a.list_len(args) == arity),
        _ => 0,
    };
    a.iter_children(lam, |x| {
        if count < 2 {
            count = (count + lambda_static_raise_count_to_label(a, x, label, arity)).min(2);
        }
    });
    count
}

fn lambda_contains_static_raise_to_other_label(a: &LamArena, lam: Lam, label: i32) -> bool {
    match a.node(lam) {
        Node::Function { .. } => false,
        Node::StaticRaise {
            label: raise_label, ..
        } => raise_label != label,
        _ => any_child(a, lam, |x| {
            lambda_contains_static_raise_to_other_label(a, x, label)
        }),
    }
}

fn runtime_module_id(module_name: &str) -> ModuleId {
    ModuleId {
        id: Ident::create_persistent(module_name),
        kind: Kind::Runtime,
        dynamic_import: false,
    }
}

fn collect_modules_from_js_list(
    j: &JsArena,
    block: crate::js_ir::arena::StmtList,
    modules: &mut OcamlModuleSet,
) {
    collect_modules_from_js_block(j, j.stmts(block), modules);
}

fn collect_modules_from_js_block(j: &JsArena, block: &[Stmt], modules: &mut OcamlModuleSet) {
    for stmt in block {
        collect_modules_from_js_statement(j, *stmt, modules);
    }
}

fn collect_modules_from_js_statement(j: &JsArena, stmt: Stmt, modules: &mut OcamlModuleSet) {
    let list = |b, m: &mut OcamlModuleSet| collect_modules_from_js_list(j, b, m);
    match j.sk(stmt) {
        StmtKind::Block(block) => list(block, modules),
        StmtKind::Variable(v) => {
            let decl = j.var(v);
            match decl.ident_info.used_stats {
                UsedStats::DeadPure => {}
                UsedStats::DeadNonPure => {
                    if let Some(value) = decl.value
                        && !matches!(j.ek(value), ExprKind::Var(_) | ExprKind::Qualified(_))
                    {
                        collect_modules_from_js_expression(j, value, modules);
                    }
                }
                _ => {
                    if let Some(value) = decl.value {
                        collect_modules_from_js_expression(j, value, modules);
                    }
                }
            }
        }
        StmtKind::Exp(expr) | StmtKind::Throw(expr) | StmtKind::Return(expr) => {
            collect_modules_from_js_expression(j, expr, modules)
        }
        StmtKind::If(cond, then_block, else_block) => {
            collect_modules_from_js_expression(j, cond, modules);
            list(then_block, modules);
            list(else_block, modules);
        }
        StmtKind::While(_, cond, body) => {
            collect_modules_from_js_expression(j, cond, modules);
            list(body, modules);
        }
        StmtKind::ForRange(info) => {
            let info = j.for_range(info);
            if let Some(init) = info.init {
                collect_modules_from_js_expression(j, init, modules);
            }
            collect_modules_from_js_expression(j, info.end, modules);
            list(info.body, modules);
        }
        StmtKind::ForOf(info) | StmtKind::ForAwaitOf(info) => {
            let info = j.for_of(info);
            collect_modules_from_js_expression(j, info.iterable, modules);
            list(info.body, modules);
        }
        StmtKind::IntSwitch(expr, info) => {
            collect_modules_from_js_expression(j, expr, modules);
            let info = j.int_switch(info);
            for (_, clause) in &info.clauses {
                list(clause.body, modules);
            }
            if let Some(default) = info.default {
                list(default, modules);
            }
        }
        StmtKind::StringSwitch(expr, info) => {
            collect_modules_from_js_expression(j, expr, modules);
            let info = j.string_switch(info);
            for clause in &info.clauses {
                list(clause.clause.body, modules);
            }
            if let Some(default) = info.default {
                list(default, modules);
            }
        }
        StmtKind::Try(info) => {
            let info = j.try_info(info);
            list(info.body, modules);
            if let Some((_, handler_block)) = info.catch {
                list(handler_block, modules);
            }
            if let Some(finalizer_block) = info.finally {
                list(finalizer_block, modules);
            }
        }
        StmtKind::Debugger | StmtKind::Break(_) | StmtKind::Continue(_) => {}
    }
}

fn collect_modules_from_js_expression(j: &JsArena, expr: Expr, modules: &mut OcamlModuleSet) {
    match j.ek(expr) {
        ExprKind::Qualified(q) => {
            let (module, _) = j.qual(q);
            if !module.dynamic_import {
                modules.insert(module.clone());
            }
        }
        ExprKind::OptionalBlock(inner, identity) => {
            if !identity {
                modules.insert(runtime_module_id("Primitive_option"));
            }
            collect_modules_from_js_expression(j, inner, modules);
        }
        ExprKind::Fun(f) => collect_modules_from_js_list(j, j.fun(f).body, modules),
        _ => crate::js_ir::walk::each_child(j, expr, |child| {
            collect_modules_from_js_expression(j, child, modules)
        }),
    }
}

#[derive(Clone, Copy)]
pub(crate) enum GroupedSwitchDefault {
    Complete,
    NonComplete,
    Default(Lam),
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
#[path = "lam_compile_test_support.rs"]
mod test_support;

#[cfg(test)]
#[path = "lam_compile_tests.rs"]
mod tests;

/// `Lam_coercion.flatten` groups the top-level spine and `Lam_group.nop_cons`
/// drops sequence heads that are a variable, constant or function
/// (compiler/core/lam_coercion.ml:179-194, lam_group.ml:36-39), so such
/// heads are never compiled.
fn drop_toplevel_pure_sequence_heads(a: &mut LamArena, lam: Lam) -> Lam {
    match a.node(lam) {
        Node::Let {
            kind,
            id,
            value,
            body,
        } => {
            let new_body = drop_toplevel_pure_sequence_heads(a, body);
            if new_body == body {
                lam
            } else {
                a.let_with(kind, id, value, new_body)
            }
        }
        Node::LetRec { ids, values, body } => {
            let new_body = drop_toplevel_pure_sequence_heads(a, body);
            if new_body == body {
                lam
            } else {
                a.letrec_with(ids, values, new_body)
            }
        }
        Node::Sequence(first, second) => {
            let new_second = drop_toplevel_pure_sequence_heads(a, second);
            if matches!(
                a.node(first),
                Node::Var(_) | Node::Const(_) | Node::Function { .. }
            ) {
                new_second
            } else if new_second == second {
                lam
            } else {
                a.seq_raw(first, new_second)
            }
        }
        _ => lam,
    }
}

/// Whether `compile_prim` (compiler/core/lam_compile.ml:1635-1766) lowers this
/// primitive through `compile_primitive_default`, the only branch that attaches
/// the primitive's source location to the resulting expression.
fn primitive_uses_default_compilation(a: &LamArena, primitive: &Primitive, args: &[Lam]) -> bool {
    match primitive {
        // lam_compile.ml:1637-1652: `compile_external_field` on a global
        // module carries no location (hoisted fields are handled earlier).
        Primitive::Pfield(_, crate::lambda::lam_compat::FieldDbgInfo::Module { .. }) => {
            !matches!(args, [m] if matches!(a.node(*m), Node::GlobalModule(_)))
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

/// A `Lswitch` node's actions and metadata, passed to the switch compilers.
#[derive(Clone, Copy)]
pub(crate) struct Sw {
    pub(crate) actions: LamList,
    pub(crate) info: SwitchId,
}

impl Sw {
    pub(crate) fn payload(self, a: &LamArena) -> &crate::lambda::arena::SwitchPayload {
        a.switch_payload(self.info)
    }

    pub(crate) fn consts(self, a: &LamArena) -> Vec<(SwitchKey, Lam)> {
        let actions = a.switch_actions(self.info, self.actions);
        a.switch_const_keys(self.info)
            .iter()
            .cloned()
            .zip(actions.consts.iter().copied())
            .collect()
    }

    pub(crate) fn blocks(self, a: &LamArena) -> Vec<(SwitchKey, Lam)> {
        let actions = a.switch_actions(self.info, self.actions);
        a.switch_block_keys(self.info)
            .iter()
            .cloned()
            .zip(actions.blocks.iter().copied())
            .collect()
    }

    pub(crate) fn fail(self, a: &LamArena) -> Option<Lam> {
        a.switch_actions(self.info, self.actions).fail
    }
}

/// A `Lstringswitch` node's actions and metadata.
#[derive(Clone, Copy)]
pub(crate) struct StrSw {
    pub(crate) actions: LamList,
    pub(crate) info: StrSwitchId,
}

impl StrSw {
    pub(crate) fn cases(self, a: &LamArena) -> Vec<(String, Lam)> {
        let all = a.list(self.actions);
        let n = a.str_switch_payload(self.info).n_cases();
        all[..n]
            .iter()
            .enumerate()
            .map(|(i, lam)| (a.str_switch_key(self.info, i).to_string(), *lam))
            .collect()
    }

    pub(crate) fn default(self, a: &LamArena) -> Option<Lam> {
        let p = a.str_switch_payload(self.info);
        p.has_default.then(|| a.list(self.actions)[p.n_cases()])
    }
}
