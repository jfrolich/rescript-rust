//! Lambda -> JS IR compilation.
//!
//! This module provides a straightforward lowering from Lambda IR into the
//! JavaScript IR used by the Rust compiler backend. The implementation favors
//! clarity over aggressive optimization; it is intended as a correct baseline
//! that can be extended with more advanced codegen passes.

use std::collections::{HashMap, HashSet};

use crate::cmi::persistent_env::CmjExportConstant;
use crate::context::IdGenerator;
use crate::ident::Ident;
use crate::js_ir::op::{
    IdentInfo, ImportAttributes as JsImportAttributes, Kind, LengthObject, MutableFlag, Number,
    PropertyName, UsedStats,
};
use crate::js_ir::printer::{convert_ident_name, is_js_keyword_or_global};
use crate::js_ir::{
    BinOp, Block, CallInfo, CaseClause, Delim, DepsProgram, Expression, ExpressionDesc,
    ForDirection, ModuleId, ModulePathResolver, Program, Statement, StatementDesc, StringClause,
    VIdent, VariableDeclaration, expression_has_no_side_effects, ocaml_eq_expression, unnest_block,
};
use crate::lambda::analysis;
use crate::lambda::compat::{Comparison, FieldDbgInfo, LetKind, SetFieldDbgInfo};
use crate::lambda::constant::{Constant, ConstructorRuntimeTag, PointerInfo, StringDelim};
use crate::lambda::free_variables::free_variables;
use crate::lambda::lam_exit_code::has_exit_code;
use crate::lambda::primitive::{
    ExternalArgAttr, ExternalArgConst, ExternalArgDelim, ExternalArgLabel, ExternalArgSpec,
    ExternalModuleBindName, ExternalModuleName, ExternalObjLabel, ExternalObjSpec, ExternalSpec,
    Mutable, Primitive,
};
use crate::lambda::js_pass_external_shadow::{apply_external_shadow_pass, is_lexical_binding_kind};
use crate::lambda::js_pass_flatten_and_mark_dead::{
    apply_js_flatten_and_mark_dead_pass, apply_js_flatten_pass,
};
use crate::lambda::js_pass_tailcall_inline::apply_js_tailcall_inline_pass;
use crate::lambda::js_shake::{
    apply_js_shake_pass, flatten_toplevel_block, keeps_declared_same_name_reusable_export_binding,
    move_reused_same_name_export_binding_to_export_tail, move_same_name_export_alias_to_export_tail,
    resolve_tail_move_initializer_kind, resolve_tail_move_replacement_expression,
    statement_mentions_ident_anywhere, tail_move_materialized_root_ident,
    TailMoveInitializerKind,
};
use crate::lambda::subst;
use crate::lambda::{
    ApInfo, Apply, ApplyStatus, FunctionAttribute, InlineAttribute, LFunction, Lambda,
    LambdaSwitch, SwitchBlock, SwitchBlockType, SwitchCaseTag, TagInfo,
};
use crate::location::Location;

use super::js_exp_make::{
    block_with_return_expr_iife, bool_literal, both_bigint_literals, both_bool_literals,
    both_float_literals, both_int_literals, both_string_literals, compare_bigint_literals,
    compare_bool_literals, compare_int_literals, compare_string_literals,
    comparison_to_binop, comparison_to_runtime_member, compile_int_equality,
    compile_nullish_strict_comparison, compile_raw_comparison,
    direct_projection_from_pure_literal, eta_wrapped_args_match_params,
    external_polyvar_int_dispatch, external_polyvar_string_dispatch, int32_add, int32_band,
    int32_bor, int32_bxor, int32_lsl, int32_lsr, int32_minus, int32_mul, int32_offset,
    int32_pow, int_bnot, int_expr, int_literal, is_optional_block, is_out_expr,
    is_type_number_expr, is_type_object_expr, is_zero_int, js_expr_no_side_effects, js_seq,
    ocaml_typeof_expr, poly_var_tag_access, poly_var_value_access,
    pure_indexed_block_item, range_exclusion_or, raw_typeof_comparison,
    is_nullish_literal, is_pure_subexpression, remove_pure_subexpression,
    runtime_compare_call_args, runtime_member_for_eta_wrapped_primitive, strict_eq_int,
    string_switch_iife, to_int32,
};
use super::lam_compile_coercion::{
    block_declares_ident, block_declares_initialized_ident,
    can_reuse_existing_undefined_export_binding,
    collect_declared_idents, collect_export_aliases, count_materialized_same_name_binding_roots,
    extract_toplevel_exports, insert_rebound_export_before_equivalent_later_binding,
    keeps_declared_same_name_function_export_alias, max_ident_stamp_in_block,
    max_ident_stamp_in_expression, max_ident_stamp_in_statement,
    push_effect_expression, push_s_exp,
    reorder_trailing_export_bindings_by_export_order,
    resolve_declared_same_name_self_alias_target, resolve_export_alias, resolve_export_aliases,
    resolve_rewriteable_toplevel_alias_initializer, reusable_declared_same_name_export_alias,
    reusable_same_name_export_binding,
    rewrite_toplevel_variable_initializers_through_rewriteable_aliases,
    same_reusable_export_value, statement_allows_undefined_export_reuse, variable_initializer,
    ExtractedExports,
};
use super::js_stmt_make::{
    block_finishes_output, block_terminates, statement_finishes_output, statement_terminates,
    strict_single_return_expr,
};

/// Compilation result for an expression: prelude statements plus a value expression.
#[derive(Debug, Clone)]
struct Compiled {
    prelude: Block,
    expr: Expression,
}

#[derive(Debug, Clone)]
struct StaticHandler {
    label: i32,
    bindings: Vec<Ident>,
    handler: Lambda,
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
struct StaticJumpHandler {
    label: i32,
    exit_id: Ident,
    exit_code: i32,
    bindings: Vec<Ident>,
}

#[derive(Debug, Clone)]
struct FallthroughReturnHandler {
    label: i32,
    bindings: Vec<Ident>,
}

#[derive(Debug, Clone)]
struct TailLoopState {
    tail_targets: Vec<Ident>,
    params: Vec<Ident>,
    new_params: HashMap<Ident, Ident>,
    triggered: bool,
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
enum ShortCircuitOp {
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

fn short_circuit_primitive<'a>(
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
fn call_info_of_apply_status(call_transformed_jsx: bool, status: ApplyStatus) -> CallInfo {
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

fn empty_switch_case_clause() -> CaseClause {
    CaseClause {
        body: vec![],
        should_break: false,
        comment: None,
    }
}

fn stable_group_switch_cases<'a, T: Clone, F>(
    filtered: Vec<(T, &'a Lambda)>,
    merge_cases: F,
) -> Vec<(T, &'a Lambda, bool)>
where
    F: Fn(&T, &T) -> bool,
{
    let mut groups: Vec<Vec<(T, &'a Lambda)>> = Vec::new();

    // OCaml's Ext_list.stable_group walks from the tail and inserts each case
    // into the first matching group so equal bodies can be coalesced even when
    // they are separated by a different branch.
    for (tag, lam) in filtered.into_iter().rev() {
        let mut placed = false;
        for group in &mut groups {
            let Some((head_tag, head_lam)) = group.first() else {
                continue;
            };
            if merge_cases(&tag, head_tag) && super::lambda_eq_approx(lam, head_lam) {
                group.insert(0, (tag.clone(), lam));
                placed = true;
                break;
            }
        }
        if !placed {
            groups.push(vec![(tag, lam)]);
        }
    }

    groups.reverse();

    let mut grouped = Vec::with_capacity(groups.iter().map(Vec::len).sum());
    for group in groups {
        let last_idx = group.len().saturating_sub(1);
        for (idx, (tag, lam)) in group.into_iter().enumerate() {
            grouped.push((tag, lam, idx == last_idx));
        }
    }

    grouped
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct ExternalModuleCacheKey {
    bundle: String,
    default: bool,
}

/// Lambda compiler to JS IR.
pub struct LambdaCompiler {
    id_gen: IdGenerator,
    module_path_resolver: Option<ModulePathResolver>,
    jsx_preserve: bool,
    check_div_by_zero: bool,
    cmj_constant_cache: HashMap<String, Option<HashMap<String, CmjExportConstant>>>,
    external_module_ids: HashMap<ExternalModuleCacheKey, Ident>,
    static_handlers: Vec<StaticHandler>,
    static_jump_handlers: Vec<StaticJumpHandler>,
    fallthrough_return_handlers: Vec<FallthroughReturnHandler>,
    return_unit_stack: Vec<bool>,
}

impl Default for LambdaCompiler {
    fn default() -> Self {
        Self::new()
    }
}

impl LambdaCompiler {
    fn grouped_switch_default<'a>(
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

    fn grouped_switch_cases<'a, T: Clone, F>(
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

    fn filtered_switch_case_refs<'a, T: Clone>(
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
        Self {
            id_gen: IdGenerator::new(),
            module_path_resolver: None,
            jsx_preserve: false,
            check_div_by_zero: true,
            cmj_constant_cache: HashMap::new(),
            external_module_ids: HashMap::new(),
            static_handlers: Vec::new(),
            static_jump_handlers: Vec::new(),
            fallthrough_return_handlers: Vec::new(),
            return_unit_stack: Vec::new(),
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
        Self::with_module_path_resolver_and_options(module_path_resolver, jsx_preserve, true)
    }

    /// Create a compiler with the JS-backend options that affect lowering.
    pub fn with_module_path_resolver_and_options(
        module_path_resolver: Option<ModulePathResolver>,
        jsx_preserve: bool,
        check_div_by_zero: bool,
    ) -> Self {
        Self {
            id_gen: IdGenerator::new(),
            module_path_resolver,
            jsx_preserve,
            check_div_by_zero,
            cmj_constant_cache: HashMap::new(),
            external_module_ids: HashMap::new(),
            static_handlers: Vec::new(),
            static_jump_handlers: Vec::new(),
            fallthrough_return_handlers: Vec::new(),
            return_unit_stack: Vec::new(),
        }
    }

    /// Compile a Lambda expression into a JS IR program.
    pub fn compile_program(&mut self, lam: &Lambda) -> Program {
        self.compile_deps_program(lam).program
    }

    /// Compile a Lambda expression into a JS IR program with module metadata.
    pub fn compile_deps_program(&mut self, lam: &Lambda) -> DepsProgram {
        let possible_required_modules = std::collections::HashSet::new();
        self.compile_deps_program_with_possible_required_modules(lam, &possible_required_modules)
    }

    /// Compile a Lambda expression into a JS IR program with module metadata
    /// and additional required modules captured before later coercion/simplify
    /// stages erase the original global-module reference.
    pub fn compile_deps_program_with_possible_required_modules(
        &mut self,
        lam: &Lambda,
        extra_possible_required_modules: &std::collections::HashSet<ModuleId>,
    ) -> DepsProgram {
        self.external_module_ids.clear();
        let mut possible_required_modules = collect_possible_required_modules(lam);
        possible_required_modules.extend(extra_possible_required_modules.iter().cloned());
        let simplified = crate::lambda::simplify::simplify_for_js_backend_with_jsx_preserve(
            lam,
            self.jsx_preserve,
        );
        let compiled = self.compile_expr(&simplified);
        let mut block = compiled.prelude;
        let exports = if let Some(mut exports) = extract_toplevel_exports(compiled.expr, &mut block)
        {
            if block_terminates(&block) {
                for value in &mut exports.values {
                    *value = Expression::undefined(false);
                }
            }
            self.coerce_toplevel_exports(&mut block, exports)
        } else {
            vec![]
        };
        rewrite_toplevel_variable_initializers_through_rewriteable_aliases(&mut block, &exports);
        let exports = resolve_export_aliases(&block, exports);
        let side_effect = module_side_effect_reason(&simplified);

        let mut deps = apply_js_flatten_and_mark_dead_pass(
            apply_js_tailcall_inline_pass(apply_external_shadow_pass(apply_js_flatten_pass(
                DepsProgram {
                    program: Program::new(block, exports),
                    modules: vec![],
                    side_effect,
                },
            ))),
            self.jsx_preserve,
        );
        deps = apply_js_shake_pass(deps);
        let mut required_modules = self.collect_required_module_set(&deps.program.block);
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
        deps
    }

    fn coerce_toplevel_exports(
        &mut self,
        block: &mut Block,
        extracted: ExtractedExports,
    ) -> Vec<Ident> {
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
        let mut rebound_exports = Vec::new();

        let extracted_len = extracted.exports.len();
        for index in 0..extracted_len {
            let export = extracted.exports[index].clone();
            let value = extracted.values[index].clone();
            let later_exports = &extracted.exports[index + 1..];
            if let Some((late_value, property)) =
                move_same_name_export_alias_to_export_tail(block, &export, &value)
            {
                exports.push(export.clone());
                rebound_exports.push(Statement::variable(VariableDeclaration {
                    ident: export,
                    value: Some(late_value),
                    property,
                    ident_info: IdentInfo::default(),
                }));
                continue;
            }
            if let ExpressionDesc::Var(VIdent::Id(target)) = &value.desc {
                if target.name() == export.name() {
                    if declared.contains(&export) {
                        exports.push(
                            if keeps_declared_same_name_function_export_alias(block, &export) {
                                export
                            } else {
                                resolve_declared_same_name_self_alias_target(block, &export)
                                    .unwrap_or(export)
                            },
                        );
                        continue;
                    }
                    if declared.contains(target) {
                        let resolved = resolve_tail_move_replacement_expression(
                            block,
                            &Expression::var(target.clone()),
                            target,
                            false,
                        );
                        match resolved.desc {
                            ExpressionDesc::Var(VIdent::Id(resolved_target)) => {
                                exports.push(resolved_target);
                            }
                            _ => exports.push(target.clone()),
                        }
                        continue;
                    }
                }
            }
            if matches!(value.desc, ExpressionDesc::Undefined { .. })
                && ((declared.contains(&export)
                    && can_reuse_existing_undefined_export_binding(block, &export))
                    || block_ended)
            {
                exports.push(export);
                continue;
            }
            if let Some((late_value, property)) =
                move_reused_same_name_export_binding_to_export_tail(block, &export, &value)
            {
                exports.push(export.clone());
                rebound_exports.push(Statement::variable(VariableDeclaration {
                    ident: export,
                    value: Some(late_value),
                    property,
                    ident_info: IdentInfo::default(),
                }));
                continue;
            }
            if keeps_declared_same_name_reusable_export_binding(block, &export, &value) {
                exports.push(export);
                continue;
            }
            if let Some(reused) = reusable_same_name_export_binding(block, &export, &value) {
                exports.push(reused);
                continue;
            }
            if let Some(inserted_export) = insert_rebound_export_before_equivalent_later_binding(
                block,
                &export,
                &value,
                later_exports,
            ) {
                exports.push(inserted_export);
                continue;
            }

            let rebound = self.id_gen.create(export.name());
            let property = if matches!(value.desc, ExpressionDesc::Var(VIdent::Id(_))) {
                LetKind::Alias
            } else {
                LetKind::Strict
            };
            exports.push(rebound.clone());
            rebound_exports.push(Statement::variable(VariableDeclaration {
                ident: rebound,
                value: Some(value),
                property,
                ident_info: IdentInfo::default(),
            }));
        }

        block.extend(rebound_exports);
        reorder_trailing_export_bindings_by_export_order(block, &exports);
        exports
    }

    fn compile_apply_call(&mut self, apply: &Apply) -> Compiled {
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

    fn try_statement(&self, body: Block, exn: &Ident, handler: Block) -> Statement {
        Statement::new(StatementDesc::Try(body, Some((exn.clone(), handler)), None))
    }

    fn compile_expr(&mut self, lam: &Lambda) -> Compiled {
        match lam {
            Lambda::Lvar(id) => Compiled {
                prelude: vec![],
                expr: Expression::var(id.clone()),
            },
            Lambda::LglobalModule(id, dynamic_import) => {
                let module = ModuleId {
                    id: id.clone(),
                    kind: Kind::Ml,
                    dynamic_import: *dynamic_import,
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
            Lambda::Lapply(apply) => self.compile_apply_call(apply),
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
                        self.with_return_unit_context(func.attr.return_unit, |this| {
                            this.compile_return_block(&func.body)
                        })
                    });
                let expr = Expression::new(ExpressionDesc::Fun {
                    is_method: false,
                    params,
                    body,
                    env: Default::default(),
                    return_unit: func.attr.return_unit,
                    async_: func.attr.async_,
                    directive: func.attr.directive.clone(),
                });
                Compiled {
                    prelude: vec![],
                    expr,
                }
            }
            Lambda::Llet(kind, id, value, body) => {
                let mut prelude = self.compile_let_binding(*kind, id, value);
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
                let mut prelude = self.compile_recursive_bindings(bindings);
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
                self.compile_primitive(&info.primitive, &info.args)
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
                let (handlers, flat_body) =
                    flatten_nested_caches(*label, bindings, body, handler);
                if handlers.len() > 1 {
                    // lam_compile.ml:935 calls `flatten_nested_caches` at the
                    // top of `compile_staticcatch`; a `code_table` with >1
                    // entries goes through the multi-handler explicit-jump
                    // arm for `NeedValue` at lam_compile.ml:978-988.
                    let result = self.fresh_ident("catch");
                    let mut prelude = vec![Statement::variable(VariableDeclaration {
                        ident: result.clone(),
                        value: None,
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    })];
                    prelude.extend(self.compile_multi_staticcatch_assignment_block(
                        &result, &handlers, flat_body,
                    ));
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
                let first = self.compile_effect_output(a);
                let second = self.compile_expr(b);
                self.append_effect_output(first, second)
            }
            Lambda::Lwhile(cond, body) => {
                let cond_compiled = self.compile_expr(cond);
                let cond_expr =
                    block_with_return_expr_iife(cond_compiled.prelude, cond_compiled.expr);
                let body_block = self.compile_block(body);
                Compiled {
                    prelude: vec![Statement::while_(cond_expr, body_block)],
                    expr: Expression::undefined(false),
                }
            }
            Lambda::Lfor(var, start, end, dir, body) => {
                self.compile_for_loop(var, start, end, dir, body)
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
        let body_block = self.compile_block(body);

        let mut prelude = start_compiled.prelude;
        if block_terminates(&prelude) {
            return Compiled {
                prelude,
                expr: Expression::undefined(false),
            };
        }

        let push_loop = |block: &mut Block, init: Option<Expression>, finish: Expression| {
            block.push(Statement::new(StatementDesc::ForRange(
                init,
                finish,
                var.clone(),
                direction,
                body_block.clone(),
            )));
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
                if matches!(info.primitive, Primitive::Pmakeblock(_, _, _))
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
            Lambda::Lprim(info) if matches!(info.primitive, Primitive::Pmakeblock(_, _, _)) => {
                if let Some(effects) =
                    self.compile_recursive_self_binding_makeblock(id, info, all_bindings, group)
                {
                    return (vec![], effects);
                }

                let tag_info = match &info.primitive {
                    Primitive::Pmakeblock(_, tag_info, _) => tag_info,
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
                // OCaml's `compile_recursive_let` catch-all (lam_compile.ml:485-486)
                // wraps the value via `Declare (Alias, id)`. When the value is a
                // function expression, the printer (js_dump.ml:1294-1310 +
                // pp_function `Name_top`) emits a `function name(...) {...}`
                // declaration, which JS hoists to the top of the enclosing scope.
                // Hoisting is *load-bearing* for recursive value bindings whose
                // prelude references the binding before the assignment site, e.g.
                // `let rec r = (let x = makeblock(A, r); fun () => x)` lowers to
                // `let x = {VAL: r}; <r-binding>`. Without hoisting `r` is
                // `undefined` when `let x` runs and `x.VAL` captures the wrong
                // value. Mirror that here by emitting `let r = function_expr`
                // as a single Variable declaration (printer turns it into
                // `function r(...) {...}` at top level) instead of splitting
                // into `let r; ...; r = function_expr;`.
                if matches!(&compiled.expr.desc, ExpressionDesc::Fun { .. }) {
                    effects.push(Statement::variable(VariableDeclaration {
                        ident: id.clone(),
                        value: Some(compiled.expr),
                        property: LetKind::Alias,
                        ident_info: IdentInfo::default(),
                    }));
                    return (vec![], effects);
                }
                effects.push(Statement::exp(Expression::bin(
                    BinOp::Eq,
                    Expression::var(id.clone()),
                    compiled.expr,
                )));
                (
                    vec![Statement::variable(VariableDeclaration {
                        ident: id.clone(),
                        value: None,
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    })],
                    effects,
                )
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
            Primitive::Pmakeblock(_, tag_info, _) => tag_info,
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
                let (handlers, flat_body) =
                    flatten_nested_caches(*label, bindings, body, handler);
                if handlers.len() > 1 {
                    // lam_compile.ml:935 + 989-996 — `Declare (kind, id)`
                    // with flattened multi-handler code_table.
                    block.extend(self.compile_multi_staticcatch_assignment_block(
                        id, &handlers, flat_body,
                    ));
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

    fn compile_effect_block(&mut self, lam: &Lambda) -> Block {
        // Mirror OCaml's invariant that consumers of `compile_lambda` go
        // through `Js_output.output_as_block` (js_output.ml:82-86) which
        // calls `unnest_block` (js_output.ml:77-80). The unnest peels
        // single-element `[Block ...]` wrappers so an inner `S.if_` rule 7
        // result doesn't hide its literal-last terminal from the outer
        // `block_last_is_return_throw_or_continue` check
        // (js_stmt_make.ml:186-193).
        unnest_block(self.compile_effect_block_inner(lam))
    }

    fn compile_effect_block_inner(&mut self, lam: &Lambda) -> Block {
        match lam {
            Lambda::Llet(kind, id, value, body) => {
                let mut block = self.compile_let_binding(*kind, id, value);
                if block_finishes_output(&block) {
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
                if block_finishes_output(&block) {
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
                let (handlers, flat_body) =
                    flatten_nested_caches(*label, bindings, body, handler);
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

    fn compile_return_block(&mut self, lam: &Lambda) -> Block {
        // Mirror OCaml's invariant that consumers go through
        // `Js_output.output_as_block` (js_output.ml:82-86) which calls
        // `unnest_block` on `compile_lambda` results.
        unnest_block(self.compile_return_block_inner(lam))
    }

    fn compile_return_block_inner(&mut self, lam: &Lambda) -> Block {
        match lam {
            Lambda::Llet(kind, id, value, body) => {
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
                block.push(Statement::return_(compiled.expr));
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
                if flatten_nested_caches(*label, bindings, body, handler).0.len() > 1 =>
            {
                // lam_compile.ml:935 — `flatten_nested_caches` is the FIRST
                // thing `compile_staticcatch` does. A code_table with >1
                // entries goes through the multi-handler explicit-jump arm
                // (lam_compile.ml:1000-1010 for `EffectCall tail_type`).
                let (handlers, flat_body) =
                    flatten_nested_caches(*label, bindings, body, handler);
                if std::env::var_os("RUST_DEBUG_STATICCATCH_RETURN").is_some() {
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
                if std::env::var_os("RUST_DEBUG_STATICCATCH_RETURN").is_some() {
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
                if std::env::var_os("RUST_DEBUG_STATICCATCH_RETURN").is_some() {
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
                    && matches!(
                        body.as_ref(),
                        Lambda::LstaticCatch(_, _, nested_handler)
                            if lambda_contains_static_raise(nested_handler)
                    )
                    && !self.handler_returns_unit_undefined(bindings, handler)
                    && !lambda_contains_static_raise(handler) =>
            {
                if std::env::var_os("RUST_DEBUG_STATICCATCH_RETURN").is_some() {
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
                let requires_explicit_jump =
                    (self.return_unit_stack.last().copied() == Some(true) && !bindings.is_empty())
                        || self.return_staticcatch_requires_explicit_jump(
                            *label, bindings, body, handler,
                        );
                if std::env::var_os("RUST_DEBUG_STATICCATCH_RETURN").is_some() {
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
                } else if !has_exit_code(handler, |_| true)
                    && !lambda_contains_staticcatch(handler)
                    && lambda_contains_static_raise_to_label(body, *label, bindings.len())
                {
                    // OCaml's `compile_staticcatch` pseudo-jmp path
                    // (lam_compile.ml:937-962, add_pseudo_jmp at
                    // lam_compile_context.ml:99-104) fires for any single
                    // code_table with `no_static_raise_in_handler`
                    // (lam_compile_context.ml:80-81 — `has_exit_code handler
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
                let body_block = self.compile_return_block(body);
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

    fn lambda_is_trivial_unit_undefined(&self, lam: &Lambda) -> bool {
        match lam {
            Lambda::Lconst(Constant::JsUndefined { is_unit: true }) => true,
            Lambda::Lsequence(first, second) => {
                analysis::no_side_effects(first) && self.lambda_is_trivial_unit_undefined(second)
            }
            Lambda::Llet(_, _, value, body) => {
                analysis::no_side_effects(value) && self.lambda_is_trivial_unit_undefined(body)
            }
            Lambda::Lletrec(bindings, body) => {
                bindings
                    .iter()
                    .all(|(_, value)| analysis::no_side_effects(value))
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

    fn uses_fallthrough_staticcatch_return(
        &self,
        body: &Lambda,
        label: i32,
        bindings: &[Ident],
        handler: &Lambda,
    ) -> bool {
        if !self.fallthrough_return_handlers.is_empty() {
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
                    && !lambda_contains_static_raise(handler)
                    && lambda_contains_static_raise_to_other_label(body, label)
        );
        // Lam_pass_exits can inline outward handlers away before backend
        // lowering. OCaml's compile_staticcatch pseudo-jump path still keeps a
        // shared non-raising handler outside the switch when several direct
        // exits now target the same label.
        let shared_multi_exit_fallthrough_like_ocaml = !inside_enclosing_staticcatch_chain
            && !keep_complete_named_variant_plain_handler_inline
            && !self.handler_returns_unit_undefined(bindings, handler)
            && !lambda_contains_static_raise(handler)
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
                    && !lambda_contains_static_raise(handler)
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
                _ if self.return_unit_stack.last().copied() == Some(true)
                    && !inside_enclosing_staticcatch_chain
                    && !self.handler_returns_unit_undefined(bindings, handler)
                    && !lambda_contains_static_raise(handler) =>
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
                _ if !lambda_contains_static_raise(handler)
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
                _ if self.return_unit_stack.last().copied() == Some(true)
                    && !inside_enclosing_staticcatch_chain
                    && !self.handler_returns_unit_undefined(bindings, handler)
                    && !lambda_contains_static_raise(handler) =>
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
                    && !lambda_contains_static_raise(handler)
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
        self.return_unit_stack.last().copied() == Some(true)
            && !bindings.is_empty()
            && self.fallthrough_return_handlers.is_empty()
            && !matches!(body, Lambda::Lswitch(_, _) | Lambda::LstringSwitch(_, _, _))
            && lambda_contains_static_raise_to_label(body, label, bindings.len())
            && !lambda_contains_static_raise(handler)
    }

    fn active_fallthrough_return_handler(&self) -> Option<&FallthroughReturnHandler> {
        self.fallthrough_return_handlers.last()
    }

    fn reorder_fallthrough_return_clauses<T>(
        &self,
        clauses: Vec<T>,
        mut body_is_empty: impl FnMut(&T) -> bool,
    ) -> Vec<T> {
        if self.active_fallthrough_return_handler().is_none() {
            return clauses;
        }

        let mut fallthrough = Vec::new();
        let mut returning = Vec::new();
        for clause in clauses {
            if body_is_empty(&clause) {
                fallthrough.push(clause);
            } else {
                returning.push(clause);
            }
        }

        if fallthrough.is_empty() || returning.is_empty() {
            returning.extend(fallthrough);
            return returning;
        }

        returning.extend(fallthrough);
        returning
    }

    fn grouped_return_string_clauses<'a, T: Clone>(
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
            // Mirror OCaml's `lam_compile.ml` pseudo-jmp emission: when a
            // case body resolved away through a fallthrough static-raise
            // handler, OCaml still prints an explicit `break;` to exit the
            // switch so the subsequent appended handler reads cleanly.
            let should_break =
                !block_terminates(&compiled_body) && lambda_has_exit(body);

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

    fn should_hoist_grouped_named_string_return_tail(&self, body: &Lambda) -> bool {
        match body {
            Lambda::LstaticRaise(label, args) => self
                .resolve_static_raise(*label, args)
                .as_ref()
                .is_some_and(lambda_has_exit),
            _ => false,
        }
    }

    fn compile_hoisted_named_string_return_tail(&mut self, body: &Lambda) -> Block {
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
            return self.compile_expr(&Lambda::Lfunction(func.clone())).expr;
        }

        let params = if func.attr.one_unit_arg {
            vec![]
        } else {
            func.params.clone()
        };
        let mut tail_loop = TailLoopState::new(tail_targets.to_vec(), params.clone());
        let body = self.compile_tail_loop_return_block(&func.body, &mut tail_loop);

        if !tail_loop.triggered {
            return self.compile_expr(&Lambda::Lfunction(func.clone())).expr;
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

        let mut loop_body = Vec::new();
        for param in params.iter().rev() {
            let Some(new_param) = tail_loop.new_params.get(param) else {
                continue;
            };
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
            directive: func.attr.directive.clone(),
        })
    }

    fn compile_tail_loop_return_block(
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
                let (handlers, flat_body) =
                    flatten_nested_caches(*label, bindings, body, handler);
                if handlers.len() > 1 {
                    return self.compile_multi_staticcatch_tail_loop_return_block(
                        &handlers, flat_body, tail_loop,
                    );
                }
                let uses_fallthrough =
                    self.uses_fallthrough_staticcatch_return(body, *label, bindings, handler);
                let requires_explicit_jump = (self.return_unit_stack.last().copied() == Some(true)
                    && !bindings.is_empty())
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
                } else if !has_exit_code(handler, |_| true)
                    && !lambda_contains_staticcatch(handler)
                    && lambda_contains_static_raise_to_label(body, *label, bindings.len())
                {
                    // Mirror the fallthrough / pseudo-jmp arm from
                    // `compile_return_block`. OCaml's pseudo-jmp path
                    // (lam_compile.ml:937-962) gates on
                    // `no_static_raise_in_handler`
                    // (lam_compile_context.ml:80-81) which itself wraps
                    // `has_exit_code handler (fun _ -> true)` — stopping at
                    // Lfunction boundaries. Using `has_exit_code` here lets
                    // handlers whose only static_raises live inside a
                    // nested closure reach the fallthrough emission
                    // (lam_compile.ml:957-962), eliminating the spurious
                    // outer explicit-jump layer that miss_colon_test saw
                    // when `lambda_contains_static_raise` over-counted.
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
            Lambda::LtryWith(body, exn, handler)
                if !self.fallthrough_return_handlers.is_empty() =>
            {
                let body_block = self.compile_tail_loop_return_block(body, tail_loop);
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
        block.push(Statement::if_(
            cond_compiled.expr,
            unnest_block(then_block),
            unnest_block(else_block),
        ));
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
        let cases: Vec<_> = self
            .grouped_switch_cases(
                &switch.sw_consts,
                switch.sw_failaction.as_deref(),
                |_, _| true,
            )
            .into_iter()
            .map(|(tag, body, is_last)| {
                (
                    tag,
                    if is_last {
                        CaseClause {
                            body: self.compile_tail_loop_return_block(body, tail_loop),
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
        let scrut_compiled = self.compile_expr(scrut);
        let mut block = scrut_compiled.prelude;
        let clauses = self
            .grouped_switch_cases(cases, default, |_, _| true)
            .into_iter()
            .map(|(tag, body, is_last)| StringClause {
                tag_type: SwitchCaseTag::String(tag),
                clause: if is_last {
                    CaseClause {
                        body: self.compile_tail_loop_return_block(body, tail_loop),
                        should_break: false,
                        comment: None,
                    }
                } else {
                    empty_switch_case_clause()
                },
            })
            .collect();

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
                let (handlers, flat_body) =
                    flatten_nested_caches(*label, bindings, body, handler);
                if handlers.len() > 1 {
                    // lam_compile.ml:935 + 1000-1010 — multi-handler
                    // explicit-jump arm for an effect-value continuation.
                    return Compiled {
                        prelude: self
                            .compile_multi_staticcatch_effect_block(&handlers, flat_body),
                        expr: Expression::undefined(false),
                    };
                }
                if !bindings.is_empty()
                    || self.staticcatch_requires_explicit_jump(bindings, handler)
                {
                    Compiled {
                        prelude: self
                            .compile_staticcatch_effect_block(*label, bindings, body, handler),
                        expr: Expression::undefined(false),
                    }
                } else {
                    self.with_static_handler(*label, bindings, handler, |this| {
                        this.compile_effect_output(body)
                    })
                }
            }
            Lambda::Lswitch(scrut, switch) => {
                compiled_from_effect_block(self.compile_switch_effect_block(scrut, switch))
            }
            Lambda::LstringSwitch(scrut, cases, default) => compiled_from_effect_block(
                self.compile_string_switch_effect_block(scrut, cases, default.as_deref()),
            ),
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

        block.push(Statement::if_(
            cond_expr,
            unnest_block(self.compile_effect_block(then_)),
            unnest_block(self.compile_effect_block(else_)),
        ));
        block
    }

    fn compile_switch(&mut self, scrut: &Lambda, switch: &LambdaSwitch) -> Compiled {
        if self.uses_untagged_variant_switch(switch) {
            let scrut_compiled = self.compile_expr(scrut);
            let (mut prelude, scrut_expr) =
                self.bind_switch_scrutinee_once(scrut_compiled.prelude, scrut_compiled.expr);
            let tmp = self.fresh_tmp_ident();
            prelude.push(Statement::variable(VariableDeclaration {
                ident: tmp.clone(),
                value: None,
                property: LetKind::Strict,
                ident_info: IdentInfo::default(),
            }));
            prelude.extend(
                self.compile_untagged_variant_switch_assignment_statements(
                    &tmp, scrut_expr, switch,
                ),
            );
            return Compiled {
                prelude,
                expr: Expression::var(tmp),
            };
        }

        if self.uses_named_variant_switch(switch) {
            let scrut_compiled = self.compile_expr(scrut);
            let (mut prelude, scrut_expr) =
                if self.named_variant_switch_needs_bound_scrutinee(switch) {
                    self.bind_switch_scrutinee_once(scrut_compiled.prelude, scrut_compiled.expr)
                } else {
                    (scrut_compiled.prelude, scrut_compiled.expr)
                };
            let tmp = self.fresh_tmp_ident();
            prelude.push(Statement::variable(VariableDeclaration {
                ident: tmp.clone(),
                value: None,
                property: LetKind::Strict,
                ident_info: IdentInfo::default(),
            }));
            prelude.extend(
                self.compile_named_variant_switch_assignment_statements(&tmp, scrut_expr, switch),
            );

            return Compiled {
                prelude,
                expr: Expression::var(tmp),
            };
        }

        let scrut_compiled = self.compile_expr(scrut);
        let mut prelude = scrut_compiled.prelude;
        let tmp = self.fresh_tmp_ident();
        prelude.push(Statement::variable(VariableDeclaration {
            ident: tmp.clone(),
            value: None,
            property: LetKind::Strict,
            ident_info: IdentInfo::default(),
        }));

        let cases: Vec<_> = self
            .grouped_switch_cases(
                &switch.sw_consts,
                switch.sw_failaction.as_deref(),
                |_, _| true,
            )
            .into_iter()
            .map(|(tag, body, is_last)| {
                (
                    tag,
                    if is_last {
                        crate::js_ir::CaseClause {
                            body: self.compile_switch_value_block(&tmp, body),
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
            .map(|fallback| self.compile_switch_value_block(&tmp, fallback));

        prelude.push(Statement::new(StatementDesc::IntSwitch(
            scrut_compiled.expr,
            cases,
            default_block,
        )));

        Compiled {
            prelude,
            expr: Expression::var(tmp),
        }
    }

    fn compile_string_switch(
        &mut self,
        scrut: &Lambda,
        cases: &[(String, Lambda)],
        default: Option<&Lambda>,
    ) -> Compiled {
        let scrut_compiled = self.compile_expr(scrut);
        let mut prelude = scrut_compiled.prelude;
        let tmp = self.fresh_tmp_ident();
        prelude.push(Statement::variable(VariableDeclaration {
            ident: tmp.clone(),
            value: None,
            property: LetKind::Strict,
            ident_info: IdentInfo::default(),
        }));
        let borrowed_cases: Vec<_> = cases
            .iter()
            .map(|(tag, body)| (SwitchCaseTag::String(tag.clone()), body))
            .collect();

        if let Some(small) = self.compile_small_string_switch_assignment(
            &tmp,
            scrut_compiled.expr.clone(),
            &borrowed_cases,
            default,
            default.is_none(),
        ) {
            prelude.extend(small);
            return Compiled {
                prelude,
                expr: Expression::var(tmp),
            };
        }

        let clauses: Vec<_> = self
            .grouped_switch_cases(cases, default, |_, _| true)
            .into_iter()
            .map(|(tag, body, is_last)| crate::js_ir::StringClause {
                tag_type: SwitchCaseTag::String(tag),
                clause: if is_last {
                    crate::js_ir::CaseClause {
                        body: self.compile_switch_value_block(&tmp, body),
                        should_break: false,
                        comment: None,
                    }
                } else {
                    empty_switch_case_clause()
                },
            })
            .collect();

        let default_block = default.map(|fallback| self.compile_switch_value_block(&tmp, fallback));

        prelude.push(Statement::new(StatementDesc::StringSwitch(
            scrut_compiled.expr,
            clauses,
            default_block,
        )));

        Compiled {
            prelude,
            expr: Expression::var(tmp),
        }
    }

    fn uses_untagged_variant_switch(&self, switch: &LambdaSwitch) -> bool {
        switch
            .sw_names
            .as_ref()
            .is_some_and(|names| names.blocks.iter().any(|block| block.block_type.is_some()))
    }

    fn uses_named_variant_switch(&self, switch: &LambdaSwitch) -> bool {
        if self.uses_untagged_variant_switch(switch) {
            return false;
        }
        let Some(names) = switch.sw_names.as_ref() else {
            return false;
        };
        !(names.consts.is_empty() && names.blocks.is_empty())
    }

    fn switch_tag_value(tag: &crate::lambda::SwitchTag) -> SwitchCaseTag {
        tag.tag_type
            .clone()
            .unwrap_or_else(|| SwitchCaseTag::String(tag.name.clone()))
    }

    fn literal_cases(&self, switch: &LambdaSwitch) -> Option<Vec<SwitchCaseTag>> {
        let names = switch.sw_names.as_ref()?;
        Some(
            names
                .consts
                .iter()
                .rev()
                .map(Self::switch_tag_value)
                .collect(),
        )
    }

    fn untagged_block_types(&self, switch: &LambdaSwitch) -> Option<Vec<SwitchBlockType>> {
        let names = switch.sw_names.as_ref()?;
        Some(
            names
                .blocks
                .iter()
                .rev()
                .filter_map(|block| block.block_type.clone())
                .collect(),
        )
    }

    fn block_type_switch_tag(block_type: &SwitchBlockType) -> Option<SwitchCaseTag> {
        match block_type {
            SwitchBlockType::String => Some(SwitchCaseTag::String("string".to_string())),
            SwitchBlockType::Int | SwitchBlockType::Float => {
                Some(SwitchCaseTag::String("number".to_string()))
            }
            SwitchBlockType::BigInt => Some(SwitchCaseTag::String("bigint".to_string())),
            SwitchBlockType::Boolean => Some(SwitchCaseTag::String("boolean".to_string())),
            SwitchBlockType::Function => Some(SwitchCaseTag::String("function".to_string())),
            SwitchBlockType::Object => Some(SwitchCaseTag::String("object".to_string())),
            SwitchBlockType::Instance(_) | SwitchBlockType::Unknown => None,
        }
    }

    fn literal_case_dispatch_test(
        &self,
        expr: Expression,
        switch: &LambdaSwitch,
    ) -> Option<Expression> {
        let literal_cases = self.literal_cases(switch)?;
        let block_cases = self.untagged_block_types(switch)?;
        if literal_cases.is_empty() || block_cases.is_empty() {
            return None;
        }

        fn bin(
            op: BinOp,
            lhs: (Expression, usize),
            rhs: (Expression, usize),
        ) -> (Expression, usize) {
            (Expression::bin(op, lhs.0, rhs.0), 1 + lhs.1 + rhs.1)
        }

        fn ocaml_literal_case_or(
            compiler: &LambdaCompiler,
            expr: &Expression,
            cases: &[&SwitchCaseTag],
        ) -> (Expression, usize) {
            let mut reversed = cases.iter().rev().copied();
            let current_case = reversed.next().expect("literal cases are non-empty");
            let rest: Vec<_> = reversed.collect();
            let current = (
                compiler.switch_case_test(expr.clone(), current_case),
                3usize,
            );
            if rest.is_empty() {
                current
            } else {
                bin(
                    BinOp::Or,
                    current,
                    ocaml_literal_case_or(compiler, expr, &rest),
                )
            }
        }

        fn ocaml_literal_fold_right_or(
            compiler: &LambdaCompiler,
            expr: &Expression,
            cases: &[SwitchCaseTag],
        ) -> (Expression, usize) {
            let (first, others) = cases.split_first().expect("literal cases are non-empty");
            let mut acc = (compiler.switch_case_test(expr.clone(), first), 3usize);
            for literal in others.iter().rev() {
                acc = bin(
                    BinOp::Or,
                    (compiler.switch_case_test(expr.clone(), literal), 3usize),
                    acc,
                );
            }
            acc
        }

        let literals_overlap_with_string = literal_cases
            .iter()
            .any(|tag| matches!(tag, SwitchCaseTag::String(_)));
        let literals_overlap_with_number = literal_cases
            .iter()
            .any(|tag| matches!(tag, SwitchCaseTag::Int(_) | SwitchCaseTag::Float(_)));
        let literals_overlap_with_bigint = literal_cases
            .iter()
            .any(|tag| matches!(tag, SwitchCaseTag::BigInt(_)));
        let literals_overlap_with_boolean = literal_cases
            .iter()
            .any(|tag| matches!(tag, SwitchCaseTag::Bool(_)));
        let literals_overlap_with_object = literal_cases
            .iter()
            .any(|tag| matches!(tag, SwitchCaseTag::Null));

        let literal_case = |tag: &SwitchCaseTag| (self.switch_case_test(expr.clone(), tag), 3usize);
        let with_literal_cases = {
            let literal_cases: Vec<_> = literal_cases.iter().collect();
            ocaml_literal_case_or(self, &expr, &literal_cases)
        };
        let overlap_literal_disjunction =
            || ocaml_literal_fold_right_or(self, &expr, &literal_cases);
        let typeof_neq = |type_name: &str| {
            (
                raw_typeof_comparison(expr.clone(), BinOp::NotEqEq, type_name),
                4usize,
            )
        };

        let is_not_block_case = |block_type: &SwitchBlockType| -> (Expression, usize) {
            match block_type {
                SwitchBlockType::String if !literals_overlap_with_string => typeof_neq("string"),
                SwitchBlockType::Int | SwitchBlockType::Float if !literals_overlap_with_number => {
                    typeof_neq("number")
                }
                SwitchBlockType::BigInt if !literals_overlap_with_bigint => typeof_neq("bigint"),
                SwitchBlockType::Boolean if !literals_overlap_with_boolean => typeof_neq("boolean"),
                SwitchBlockType::Function => typeof_neq("function"),
                SwitchBlockType::Instance(name) => {
                    let instance_test = self
                        .builtin_untagged_instance_test(expr.clone(), name)
                        .expect("instance-backed block types stay supported");
                    (Expression::not(instance_test), 3usize)
                }
                SwitchBlockType::Object if !literals_overlap_with_object => typeof_neq("object"),
                SwitchBlockType::Object => bin(
                    BinOp::Or,
                    literal_case(&SwitchCaseTag::Null),
                    typeof_neq("object"),
                ),
                SwitchBlockType::String
                | SwitchBlockType::Int
                | SwitchBlockType::Float
                | SwitchBlockType::BigInt
                | SwitchBlockType::Boolean
                | SwitchBlockType::Unknown => overlap_literal_disjunction(),
            }
        };

        let without_literal_cases = {
            let (last, rest) = block_cases.split_last().expect("block cases are non-empty");
            let mut acc = is_not_block_case(last);
            for block_case in rest.iter().rev() {
                acc = bin(BinOp::And, is_not_block_case(block_case), acc);
            }
            acc
        };

        Some(if with_literal_cases.1 <= without_literal_cases.1 {
            with_literal_cases.0
        } else {
            without_literal_cases.0
        })
    }

    fn named_const_cases<'a>(
        &self,
        switch: &'a LambdaSwitch,
    ) -> Option<Vec<(SwitchCaseTag, &'a Lambda)>> {
        let names = switch.sw_names.as_ref()?;
        switch
            .sw_consts
            .iter()
            .map(|(tag, body)| {
                let index = usize::try_from(*tag).ok()?;
                Some((Self::switch_tag_value(names.consts.get(index)?), body))
            })
            .collect()
    }

    fn named_block_cases<'a>(
        &self,
        switch: &'a LambdaSwitch,
    ) -> Option<Vec<(SwitchCaseTag, &'a Lambda)>> {
        let names = switch.sw_names.as_ref()?;
        switch
            .sw_blocks
            .iter()
            .map(|(tag, body)| {
                let index = usize::try_from(*tag).ok()?;
                Some((Self::switch_tag_value(&names.blocks.get(index)?.tag), body))
            })
            .collect()
    }

    fn untagged_block_cases<'a>(
        &self,
        switch: &'a LambdaSwitch,
    ) -> Option<Vec<(&'a SwitchBlock, &'a Lambda)>> {
        let names = switch.sw_names.as_ref()?;
        switch
            .sw_blocks
            .iter()
            .map(|(tag, body)| {
                let index = usize::try_from(*tag).ok()?;
                Some((names.blocks.get(index)?, body))
            })
            .collect()
    }

    fn const_switch_default<'a>(&self, switch: &'a LambdaSwitch) -> Option<&'a Lambda> {
        if switch.sw_consts_full {
            None
        } else {
            switch.sw_failaction.as_deref()
        }
    }

    fn const_switch_complete(&self, switch: &LambdaSwitch) -> bool {
        switch.sw_consts_full || switch.sw_failaction.is_none()
    }

    fn block_switch_default<'a>(&self, switch: &'a LambdaSwitch) -> Option<&'a Lambda> {
        if switch.sw_blocks_full {
            None
        } else {
            switch.sw_failaction.as_deref()
        }
    }

    fn block_switch_complete(&self, switch: &LambdaSwitch) -> bool {
        switch.sw_blocks_full || switch.sw_failaction.is_none()
    }

    fn untagged_literal_and_block_defaults_match(&self, switch: &LambdaSwitch) -> bool {
        let failaction = switch.sw_failaction.as_deref();
        let const_default = self.grouped_switch_default(switch.sw_consts_full, failaction);
        let block_default = self.grouped_switch_default(switch.sw_blocks_full, failaction);
        match (const_default, block_default) {
            (GroupedSwitchDefault::Complete, GroupedSwitchDefault::Complete)
            | (GroupedSwitchDefault::NonComplete, GroupedSwitchDefault::NonComplete) => true,
            (GroupedSwitchDefault::Default(lhs), GroupedSwitchDefault::Default(rhs)) => {
                super::lambda_eq_approx(lhs, rhs)
            }
            _ => false,
        }
    }

    fn variant_tag_name(&self, switch: &LambdaSwitch) -> String {
        switch
            .sw_names
            .as_ref()
            .and_then(|names| {
                names
                    .blocks
                    .iter()
                    .find_map(|block| block.tag_name.as_ref().cloned())
            })
            .unwrap_or_else(|| "TAG".to_string())
    }

    fn builtin_untagged_typeof_test(&self, expr: Expression, type_name: &str) -> Expression {
        raw_typeof_comparison(expr, BinOp::EqEqEq, type_name)
    }

    fn builtin_untagged_instance_test(
        &self,
        expr: Expression,
        case_name: &str,
    ) -> Option<Expression> {
        match case_name {
            "Array" => Some(Expression::call(
                self.static_index(
                    Expression::var(Ident::create_persistent("Array")),
                    "isArray",
                ),
                vec![expr],
                CallInfo::default(),
            )),
            "ArrayBuffer" | "BigInt64Array" | "BigUint64Array" | "Blob" | "DataView" | "Date"
            | "File" | "Float32Array" | "Float64Array" | "Int16Array" | "Int32Array"
            | "Int8Array" | "Promise" | "RegExp" | "Set" | "Map" | "Uint16Array"
            | "Uint32Array" | "Uint8Array" | "Uint8ClampedArray" | "WeakSet" | "WeakMap" => {
                Some(Expression::bin(
                    BinOp::InstanceOf,
                    expr,
                    Expression::var(Ident::create_persistent(case_name)),
                ))
            }
            _ => None,
        }
    }

    fn builtin_untagged_block_test(
        &self,
        expr: Expression,
        case: &SwitchBlock,
        all_block_types: &[SwitchBlockType],
        has_null_case: bool,
    ) -> Option<Expression> {
        let test = match case.block_type.as_ref()? {
            SwitchBlockType::String => self.builtin_untagged_typeof_test(expr, "string"),
            SwitchBlockType::Int | SwitchBlockType::Float => {
                self.builtin_untagged_typeof_test(expr, "number")
            }
            SwitchBlockType::BigInt => self.builtin_untagged_typeof_test(expr, "bigint"),
            SwitchBlockType::Boolean => self.builtin_untagged_typeof_test(expr, "boolean"),
            SwitchBlockType::Function => self.builtin_untagged_typeof_test(expr, "function"),
            SwitchBlockType::Instance(name) => self.builtin_untagged_instance_test(expr, name)?,
            SwitchBlockType::Object => {
                let mut test = self.builtin_untagged_typeof_test(expr.clone(), "object");
                if has_null_case {
                    test = Expression::bin(
                        BinOp::And,
                        test,
                        Expression::bin(BinOp::NotEqEq, expr.clone(), Expression::null()),
                    );
                }
                for other in all_block_types {
                    let SwitchBlockType::Instance(name) = other else {
                        continue;
                    };
                    if let Some(instance_test) =
                        self.builtin_untagged_instance_test(expr.clone(), name)
                    {
                        test = Expression::bin(BinOp::And, test, Expression::not(instance_test));
                    }
                }
                test
            }
            SwitchBlockType::Unknown => return None,
        };
        Some(test)
    }

    fn compile_builtin_untagged_block_chain<F>(
        &mut self,
        scrut_expr: Expression,
        switch: &LambdaSwitch,
        block_cases: &[(&SwitchBlock, &Lambda)],
        default_block: Block,
        mut build_body: F,
    ) -> Option<Block>
    where
        F: FnMut(&mut Self, &Lambda) -> Block,
    {
        let const_cases = self.named_const_cases(switch)?;
        let all_block_types = self.untagged_block_types(switch).unwrap_or_default();
        if const_cases.is_empty() && block_cases.is_empty() {
            return Some(default_block);
        }

        if const_cases.is_empty()
            && self.block_switch_complete(switch)
            && block_cases.len() == 1
            && default_block.is_empty()
            && matches!(block_cases[0].0.block_type, Some(SwitchBlockType::Unknown))
        {
            return Some(build_body(self, block_cases[0].1));
        }

        let has_null_case = const_cases
            .iter()
            .any(|(tag, _)| matches!(tag, SwitchCaseTag::Null));
        let mut current_else = default_block;
        for (case, body) in block_cases.iter().rev() {
            let body_block = build_body(self, body);
            if matches!(case.block_type, Some(SwitchBlockType::Unknown)) {
                current_else = body_block;
                continue;
            }
            let test = self.builtin_untagged_block_test(
                scrut_expr.clone(),
                case,
                &all_block_types,
                has_null_case,
            )?;
            current_else = vec![Statement::if_(test, body_block, current_else)];
        }
        for (tag, body) in const_cases.iter().rev() {
            current_else = vec![Statement::if_(
                self.switch_case_test(scrut_expr.clone(), tag),
                build_body(self, body),
                current_else,
            )];
        }
        Some(current_else)
    }

    fn compile_builtin_untagged_switch_assignment_statements(
        &mut self,
        result: &Ident,
        scrut_expr: Expression,
        switch: &LambdaSwitch,
    ) -> Option<Block> {
        if !self.uses_untagged_variant_switch(switch) {
            return None;
        }
        let block_cases = self.untagged_block_cases(switch)?;
        let default_block = self
            .block_switch_default(switch)
            .map(|fallback| self.compile_assign_to_target_block(result, fallback))
            .unwrap_or_default();
        self.compile_builtin_untagged_block_chain(
            scrut_expr,
            switch,
            &block_cases,
            default_block,
            |this, body| this.compile_assign_to_target_block(result, body),
        )
    }

    fn compile_builtin_untagged_switch_return_statements(
        &mut self,
        scrut_expr: Expression,
        switch: &LambdaSwitch,
    ) -> Option<Block> {
        if !self.uses_untagged_variant_switch(switch) {
            return None;
        }
        let block_cases = self.untagged_block_cases(switch)?;
        let default_block = self
            .block_switch_default(switch)
            .map(|fallback| self.compile_return_block(fallback))
            .unwrap_or_default();
        self.compile_builtin_untagged_block_chain(
            scrut_expr,
            switch,
            &block_cases,
            default_block,
            |this, body| this.compile_return_block(body),
        )
    }

    fn compile_builtin_untagged_switch_effect_statements(
        &mut self,
        scrut_expr: Expression,
        switch: &LambdaSwitch,
    ) -> Option<Block> {
        if !self.uses_untagged_variant_switch(switch) {
            return None;
        }
        let block_cases = self.untagged_block_cases(switch)?;
        let default_block = self
            .block_switch_default(switch)
            .map(|fallback| self.compile_effect_block(fallback))
            .unwrap_or_default();

        let mut has_effectful_case = !default_block.is_empty();
        for (_, body) in &block_cases {
            if !self.compile_effect_block(body).is_empty() {
                has_effectful_case = true;
                break;
            }
        }
        if !has_effectful_case {
            return Some(vec![]);
        }

        self.compile_builtin_untagged_block_chain(
            scrut_expr,
            switch,
            &block_cases,
            default_block,
            |this, body| this.compile_effect_block(body),
        )
    }

    fn compile_untagged_block_switch_assignment_statements(
        &mut self,
        result: &Ident,
        scrut_expr: Expression,
        switch: &LambdaSwitch,
        has_null_case: bool,
    ) -> Block {
        let Some(block_cases) = self.untagged_block_cases(switch) else {
            return self
                .block_switch_default(switch)
                .map(|fallback| self.compile_assign_to_target_block(result, fallback))
                .unwrap_or_default();
        };
        if let Some(block) = self.compile_small_untagged_block_switch_assignment(
            result,
            scrut_expr.clone(),
            switch,
            &block_cases,
            has_null_case,
        ) {
            return block;
        }
        let all_block_types = self.untagged_block_types(switch).unwrap_or_default();
        if let Some((_, body)) = block_cases
            .iter()
            .find(|(case, _)| matches!(case.block_type, Some(SwitchBlockType::Unknown)))
        {
            return self.compile_assign_to_target_block(result, body);
        }
        if block_cases.len() == 1 && self.block_switch_complete(switch) {
            return self.compile_assign_to_target_block(result, block_cases[0].1);
        }

        let mut runtime_test_cases = Vec::new();
        let mut typeof_cases = Vec::new();
        for (case, body) in block_cases.iter().copied() {
            match case.block_type.as_ref() {
                Some(SwitchBlockType::Instance(_)) => runtime_test_cases.push((case, body)),
                Some(block_type) => {
                    if let Some(tag) = Self::block_type_switch_tag(block_type) {
                        typeof_cases.push((tag, body));
                    }
                }
                None => {}
            }
        }
        let allow_small_typeof_tail = runtime_test_cases.is_empty();

        let mut tail = if typeof_cases.is_empty() {
            self.block_switch_default(switch)
                .map(|fallback| self.compile_assign_to_target_block(result, fallback))
                .unwrap_or_default()
        } else {
            self.compile_named_string_switch_assignment_with_strategy(
                result,
                ocaml_typeof_expr(scrut_expr.clone()),
                &typeof_cases,
                self.block_switch_default(switch),
                self.block_switch_complete(switch),
                allow_small_typeof_tail,
            )
        };

        for (case, body) in runtime_test_cases.into_iter().rev() {
            let test = self
                .builtin_untagged_block_test(
                    scrut_expr.clone(),
                    case,
                    &all_block_types,
                    has_null_case,
                )
                .expect("instance cases stay supported");
            tail = vec![Statement::if_(
                test,
                self.compile_assign_to_target_block(result, body),
                tail,
            )];
        }

        tail
    }

    fn compile_small_untagged_block_switch_assignment(
        &mut self,
        result: &Ident,
        scrut_expr: Expression,
        switch: &LambdaSwitch,
        block_cases: &[(&SwitchBlock, &Lambda)],
        has_null_case: bool,
    ) -> Option<Block> {
        let all_block_types = self.untagged_block_types(switch).unwrap_or_default();
        let default = self.block_switch_default(switch);

        match block_cases {
            [] => Some(
                default
                    .map(|fallback| self.compile_assign_to_target_block(result, fallback))
                    .unwrap_or_default(),
            ),
            [(_, body)] if self.block_switch_complete(switch) && default.is_none() => {
                Some(self.compile_assign_to_target_block(result, body))
            }
            [(case, body)] => {
                let cond = self.builtin_untagged_block_test(
                    scrut_expr,
                    case,
                    &all_block_types,
                    has_null_case,
                )?;
                Some(vec![Statement::if_(
                    cond,
                    self.compile_assign_to_target_block(result, body),
                    default
                        .map(|fallback| self.compile_assign_to_target_block(result, fallback))
                        .unwrap_or_default(),
                )])
            }
            [(case, then_body), (_, else_body)]
                if self.block_switch_complete(switch) && default.is_none() =>
            {
                let cond = self.builtin_untagged_block_test(
                    scrut_expr,
                    case,
                    &all_block_types,
                    has_null_case,
                )?;
                Some(vec![Statement::if_(
                    cond,
                    self.compile_assign_to_target_block(result, then_body),
                    self.compile_assign_to_target_block(result, else_body),
                )])
            }
            _ => None,
        }
    }

    fn compile_untagged_block_switch_return_statements(
        &mut self,
        scrut_expr: Expression,
        switch: &LambdaSwitch,
        has_null_case: bool,
    ) -> Block {
        let Some(block_cases) = self.untagged_block_cases(switch) else {
            return self
                .block_switch_default(switch)
                .map(|fallback| self.compile_return_block(fallback))
                .unwrap_or_default();
        };
        if let Some(block) = self.compile_small_untagged_block_switch_return(
            scrut_expr.clone(),
            switch,
            &block_cases,
            has_null_case,
        ) {
            return block;
        }
        let all_block_types = self.untagged_block_types(switch).unwrap_or_default();
        if let Some((_, body)) = block_cases
            .iter()
            .find(|(case, _)| matches!(case.block_type, Some(SwitchBlockType::Unknown)))
        {
            return self.compile_return_block(body);
        }
        if block_cases.len() == 1 && self.block_switch_complete(switch) {
            return self.compile_return_block(block_cases[0].1);
        }

        let mut runtime_test_cases = Vec::new();
        let mut typeof_cases = Vec::new();
        for (case, body) in block_cases.iter().copied() {
            match case.block_type.as_ref() {
                Some(SwitchBlockType::Instance(_)) => runtime_test_cases.push((case, body)),
                Some(block_type) => {
                    if let Some(tag) = Self::block_type_switch_tag(block_type) {
                        typeof_cases.push((tag, body));
                    }
                }
                None => {}
            }
        }
        let allow_small_typeof_tail = runtime_test_cases.is_empty();

        let mut tail = if typeof_cases.is_empty() {
            self.block_switch_default(switch)
                .map(|fallback| self.compile_return_block(fallback))
                .unwrap_or_default()
        } else {
            self.compile_named_string_switch_return_with_strategy(
                ocaml_typeof_expr(scrut_expr.clone()),
                &typeof_cases,
                self.block_switch_default(switch),
                self.block_switch_complete(switch),
                allow_small_typeof_tail,
            )
        };

        for (case, body) in runtime_test_cases.into_iter().rev() {
            let test = self
                .builtin_untagged_block_test(
                    scrut_expr.clone(),
                    case,
                    &all_block_types,
                    has_null_case,
                )
                .expect("instance cases stay supported");
            tail = Self::normalized_if_block(
                test,
                Self::normalize_runtime_test_return_body(self.compile_return_block(body)),
                tail,
            );
        }

        tail
    }

    fn compile_small_untagged_block_switch_return(
        &mut self,
        scrut_expr: Expression,
        switch: &LambdaSwitch,
        block_cases: &[(&SwitchBlock, &Lambda)],
        has_null_case: bool,
    ) -> Option<Block> {
        let all_block_types = self.untagged_block_types(switch).unwrap_or_default();
        let default = self.block_switch_default(switch);

        match block_cases {
            [] => Some(
                default
                    .map(|fallback| self.compile_return_block(fallback))
                    .unwrap_or_default(),
            ),
            [(_, body)] if self.block_switch_complete(switch) && default.is_none() => {
                Some(self.compile_return_block(body))
            }
            [(case, body)] => {
                let cond = self.builtin_untagged_block_test(
                    scrut_expr,
                    case,
                    &all_block_types,
                    has_null_case,
                )?;
                Some(Self::normalized_if_block(
                    cond,
                    Self::normalize_runtime_test_return_body(self.compile_return_block(body)),
                    default
                        .map(|fallback| self.compile_return_block(fallback))
                        .unwrap_or_default(),
                ))
            }
            [(case, then_body), (_, else_body)]
                if self.block_switch_complete(switch) && default.is_none() =>
            {
                let cond = self.builtin_untagged_block_test(
                    scrut_expr,
                    case,
                    &all_block_types,
                    has_null_case,
                )?;
                Some(Self::normalized_if_block(
                    cond,
                    Self::normalize_runtime_test_return_body(self.compile_return_block(then_body)),
                    self.compile_return_block(else_body),
                ))
            }
            _ => None,
        }
    }

    fn compile_untagged_block_switch_effect_statements(
        &mut self,
        scrut_expr: Expression,
        switch: &LambdaSwitch,
        has_null_case: bool,
    ) -> Block {
        let Some(block_cases) = self.untagged_block_cases(switch) else {
            return self
                .block_switch_default(switch)
                .map(|fallback| self.compile_effect_block(fallback))
                .unwrap_or_default();
        };
        let all_block_types = self.untagged_block_types(switch).unwrap_or_default();
        if let Some((_, body)) = block_cases
            .iter()
            .find(|(case, _)| matches!(case.block_type, Some(SwitchBlockType::Unknown)))
        {
            return self.compile_effect_block(body);
        }
        if block_cases.len() == 1 && self.block_switch_complete(switch) {
            return self.compile_effect_block(block_cases[0].1);
        }
        if let Some(block) = self.compile_small_untagged_block_switch_effect(
            scrut_expr.clone(),
            switch,
            &block_cases,
            has_null_case,
        ) {
            return block;
        }

        let mut runtime_test_cases = Vec::new();
        let mut typeof_cases = Vec::new();
        for (case, body) in block_cases.iter().copied() {
            match case.block_type.as_ref() {
                Some(SwitchBlockType::Instance(_)) => runtime_test_cases.push((case, body)),
                Some(block_type) => {
                    if let Some(tag) = Self::block_type_switch_tag(block_type) {
                        typeof_cases.push((tag, body));
                    }
                }
                None => {}
            }
        }
        let allow_small_typeof_tail = runtime_test_cases.is_empty();

        let mut tail = if typeof_cases.is_empty() {
            self.block_switch_default(switch)
                .map(|fallback| self.compile_effect_block(fallback))
                .unwrap_or_default()
        } else {
            self.compile_named_string_switch_effect_with_strategy(
                ocaml_typeof_expr(scrut_expr.clone()),
                &typeof_cases,
                self.block_switch_default(switch),
                self.block_switch_complete(switch),
                allow_small_typeof_tail,
            )
        };

        for (case, body) in runtime_test_cases.into_iter().rev() {
            let test = self
                .builtin_untagged_block_test(
                    scrut_expr.clone(),
                    case,
                    &all_block_types,
                    has_null_case,
                )
                .expect("instance cases stay supported");
            let body_block = self.compile_effect_block(body);
            tail = self.compile_effect_if(test, body_block, tail);
        }

        tail
    }

    fn compile_small_untagged_block_switch_effect(
        &mut self,
        scrut_expr: Expression,
        switch: &LambdaSwitch,
        block_cases: &[(&SwitchBlock, &Lambda)],
        has_null_case: bool,
    ) -> Option<Block> {
        let all_block_types = self.untagged_block_types(switch).unwrap_or_default();
        let default = self.block_switch_default(switch);

        match block_cases {
            [] => Some(
                default
                    .map(|fallback| self.compile_effect_block(fallback))
                    .unwrap_or_default(),
            ),
            [(_, body)] if self.block_switch_complete(switch) && default.is_none() => {
                Some(self.compile_effect_block(body))
            }
            [(case, body)] => {
                let cond = self.builtin_untagged_block_test(
                    scrut_expr,
                    case,
                    &all_block_types,
                    has_null_case,
                )?;
                let then_block = self.compile_effect_block(body);
                let else_block = default
                    .map(|fallback| self.compile_effect_block(fallback))
                    .unwrap_or_default();
                Some(self.compile_effect_if(cond, then_block, else_block))
            }
            [(case, then_body), (_, else_body)]
                if self.block_switch_complete(switch) && default.is_none() =>
            {
                let cond = self.builtin_untagged_block_test(
                    scrut_expr,
                    case,
                    &all_block_types,
                    has_null_case,
                )?;
                let then_block = self.compile_effect_block(then_body);
                let else_block = self.compile_effect_block(else_body);
                Some(self.compile_effect_if(cond, then_block, else_block))
            }
            _ => None,
        }
    }

    fn compile_untagged_variant_switch_assignment_statements(
        &mut self,
        result: &Ident,
        scrut_expr: Expression,
        switch: &LambdaSwitch,
    ) -> Block {
        if switch.sw_consts.is_empty() && self.untagged_literal_and_block_defaults_match(switch) {
            let has_null_case = self
                .literal_cases(switch)
                .is_some_and(|cases| cases.iter().any(|tag| matches!(tag, SwitchCaseTag::Null)));
            return self.compile_untagged_block_switch_assignment_statements(
                result,
                scrut_expr,
                switch,
                has_null_case,
            );
        }

        if switch.sw_consts_full && switch.sw_consts.is_empty() {
            let has_null_case = self
                .literal_cases(switch)
                .is_some_and(|cases| cases.iter().any(|tag| matches!(tag, SwitchCaseTag::Null)));
            return self.compile_untagged_block_switch_assignment_statements(
                result,
                scrut_expr,
                switch,
                has_null_case,
            );
        }

        if switch.sw_blocks_full && switch.sw_blocks.is_empty() {
            let const_cases = self.named_const_cases(switch).unwrap_or_default();
            return self.compile_named_string_switch_assignment(
                result,
                scrut_expr,
                &const_cases,
                self.const_switch_default(switch),
                self.const_switch_complete(switch),
            );
        }

        let literal_cases = self.literal_cases(switch).unwrap_or_default();
        let const_cases = self.named_const_cases(switch).unwrap_or_default();
        let has_null_case = literal_cases
            .iter()
            .any(|tag| matches!(tag, SwitchCaseTag::Null));
        let const_complete = self.const_switch_complete(switch);
        let const_default = self.const_switch_default(switch);
        let const_branch = if const_cases.is_empty() {
            const_default
                .map(|fallback| self.compile_assign_to_target_block(result, fallback))
                .unwrap_or_default()
        } else {
            self.compile_named_string_switch_assignment(
                result,
                scrut_expr.clone(),
                &const_cases,
                const_default,
                const_complete,
            )
        };
        let block_branch = self.compile_untagged_block_switch_assignment_statements(
            result,
            scrut_expr.clone(),
            switch,
            has_null_case,
        );

        let Some(dispatch_test) = self.literal_case_dispatch_test(scrut_expr.clone(), switch)
        else {
            return block_branch;
        };

        if const_branch.is_empty() {
            vec![Statement::if_(
                Expression::not(dispatch_test),
                block_branch,
                vec![],
            )]
        } else if block_branch.is_empty() {
            vec![Statement::if_(dispatch_test, const_branch, vec![])]
        } else {
            vec![Statement::if_(dispatch_test, const_branch, block_branch)]
        }
    }

    fn compile_untagged_variant_switch_return_statements(
        &mut self,
        scrut_expr: Expression,
        switch: &LambdaSwitch,
    ) -> Block {
        if switch.sw_consts.is_empty() && self.untagged_literal_and_block_defaults_match(switch) {
            let has_null_case = self
                .literal_cases(switch)
                .is_some_and(|cases| cases.iter().any(|tag| matches!(tag, SwitchCaseTag::Null)));
            return self.compile_untagged_block_switch_return_statements(
                scrut_expr,
                switch,
                has_null_case,
            );
        }

        if switch.sw_consts_full && switch.sw_consts.is_empty() {
            let has_null_case = self
                .literal_cases(switch)
                .is_some_and(|cases| cases.iter().any(|tag| matches!(tag, SwitchCaseTag::Null)));
            return self.compile_untagged_block_switch_return_statements(
                scrut_expr,
                switch,
                has_null_case,
            );
        }

        if switch.sw_blocks_full && switch.sw_blocks.is_empty() {
            let const_cases = self.named_const_cases(switch).unwrap_or_default();
            return self.compile_named_string_switch_return(
                scrut_expr,
                &const_cases,
                self.const_switch_default(switch),
                self.const_switch_complete(switch),
            );
        }

        let literal_cases = self.literal_cases(switch).unwrap_or_default();
        let const_cases = self.named_const_cases(switch).unwrap_or_default();
        let has_null_case = literal_cases
            .iter()
            .any(|tag| matches!(tag, SwitchCaseTag::Null));
        let const_complete = self.const_switch_complete(switch);
        let const_default = self.const_switch_default(switch);
        let const_branch = if const_cases.is_empty() {
            const_default
                .map(|fallback| self.compile_return_block(fallback))
                .unwrap_or_default()
        } else {
            self.compile_named_string_switch_return(
                scrut_expr.clone(),
                &const_cases,
                const_default,
                const_complete,
            )
        };
        let block_branch = self.compile_untagged_block_switch_return_statements(
            scrut_expr.clone(),
            switch,
            has_null_case,
        );

        let Some(dispatch_test) = self.literal_case_dispatch_test(scrut_expr.clone(), switch)
        else {
            return block_branch;
        };

        if const_branch.is_empty() {
            vec![Statement::if_(
                Expression::not(dispatch_test),
                block_branch,
                vec![],
            )]
        } else if block_branch.is_empty() {
            vec![Statement::if_(dispatch_test, const_branch, vec![])]
        } else {
            vec![Statement::if_(dispatch_test, const_branch, block_branch)]
        }
    }

    fn compile_untagged_variant_switch_effect_statements(
        &mut self,
        scrut_expr: Expression,
        switch: &LambdaSwitch,
    ) -> Block {
        if switch.sw_consts.is_empty() && self.untagged_literal_and_block_defaults_match(switch) {
            let has_null_case = self
                .literal_cases(switch)
                .is_some_and(|cases| cases.iter().any(|tag| matches!(tag, SwitchCaseTag::Null)));
            return self.compile_untagged_block_switch_effect_statements(
                scrut_expr,
                switch,
                has_null_case,
            );
        }

        if switch.sw_consts_full && switch.sw_consts.is_empty() {
            let has_null_case = self
                .literal_cases(switch)
                .is_some_and(|cases| cases.iter().any(|tag| matches!(tag, SwitchCaseTag::Null)));
            return self.compile_untagged_block_switch_effect_statements(
                scrut_expr,
                switch,
                has_null_case,
            );
        }

        if switch.sw_blocks_full && switch.sw_blocks.is_empty() {
            let const_cases = self.named_const_cases(switch).unwrap_or_default();
            return self.compile_named_string_switch_effect(
                scrut_expr,
                &const_cases,
                self.const_switch_default(switch),
                self.const_switch_complete(switch),
            );
        }

        let literal_cases = self.literal_cases(switch).unwrap_or_default();
        let const_cases = self.named_const_cases(switch).unwrap_or_default();
        let has_null_case = literal_cases
            .iter()
            .any(|tag| matches!(tag, SwitchCaseTag::Null));
        let const_complete = self.const_switch_complete(switch);
        let const_default = self.const_switch_default(switch);
        let const_branch = if const_cases.is_empty() {
            const_default
                .map(|fallback| self.compile_effect_block(fallback))
                .unwrap_or_default()
        } else {
            self.compile_named_string_switch_effect(
                scrut_expr.clone(),
                &const_cases,
                const_default,
                const_complete,
            )
        };
        let block_branch = self.compile_untagged_block_switch_effect_statements(
            scrut_expr.clone(),
            switch,
            has_null_case,
        );

        let Some(dispatch_test) = self.literal_case_dispatch_test(scrut_expr.clone(), switch)
        else {
            return block_branch;
        };

        if const_branch.is_empty() {
            block_branch
        } else if block_branch.is_empty() {
            const_branch
        } else {
            self.compile_effect_if(dispatch_test, const_branch, block_branch)
        }
    }

    fn bind_switch_scrutinee_once(
        &mut self,
        mut prelude: Block,
        expr: Expression,
    ) -> (Block, Expression) {
        if matches!(expr.desc, ExpressionDesc::Var(_)) {
            return (prelude, expr);
        }

        let ident = self.fresh_tmp_ident();
        prelude.push(Statement::variable(VariableDeclaration {
            ident: ident.clone(),
            value: Some(expr),
            property: LetKind::Strict,
            ident_info: IdentInfo::default(),
        }));
        (prelude, Expression::var(ident))
    }

    fn named_variant_switch_needs_bound_scrutinee(&self, switch: &LambdaSwitch) -> bool {
        let const_case_count = self
            .named_const_cases(switch)
            .map_or(0, |cases| cases.len());
        let block_case_count = self
            .named_block_cases(switch)
            .map_or(0, |cases| cases.len());

        match (const_case_count > 0, block_case_count > 0) {
            // OCaml only forces a temp here when the backend needs to reuse the
            // scrutinee across both const and payload dispatch.
            (true, true) => true,
            (true, false) => !self.block_switch_complete(switch),
            (false, true) => !self.const_switch_complete(switch),
            (false, false) => false,
        }
    }

    fn variant_object_test(&self, expr: Expression) -> Expression {
        raw_typeof_comparison(expr, BinOp::EqEqEq, "object")
    }

    fn variant_non_object_test(&self, expr: Expression) -> Expression {
        raw_typeof_comparison(expr, BinOp::NotEqEq, "object")
    }

    fn dispatch_named_variant_branches(
        &self,
        scrut_expr: Expression,
        const_branch: Block,
        block_branch: Block,
    ) -> Block {
        if const_branch.is_empty() {
            vec![Statement::if_(
                self.variant_object_test(scrut_expr),
                block_branch,
                vec![],
            )]
        } else if block_branch.is_empty() {
            vec![Statement::if_(
                self.variant_non_object_test(scrut_expr),
                const_branch,
                vec![],
            )]
        } else {
            vec![Statement::if_(
                self.variant_non_object_test(scrut_expr),
                const_branch,
                block_branch,
            )]
        }
    }

    fn variant_tag_expr(&self, expr: Expression, field_name: &str) -> Expression {
        Expression::new(ExpressionDesc::StaticIndex(
            Box::new(expr),
            field_name.to_string(),
            None,
        ))
    }

    fn switch_case_expr(tag: &SwitchCaseTag) -> Expression {
        match tag {
            SwitchCaseTag::String(value) => Expression::new(ExpressionDesc::Str {
                delim: Delim::StarJ,
                txt: value.clone(),
            }),
            SwitchCaseTag::Int(value) => Expression::number(Number::int(*value)),
            SwitchCaseTag::Float(value) => Expression::number(Number::float(value.clone())),
            SwitchCaseTag::BigInt(value) => {
                let positive = !value.starts_with('-');
                let digits = value.strip_prefix('-').unwrap_or(value);
                Expression::number(Number::bigint(positive, digits.to_string()))
            }
            SwitchCaseTag::Bool(value) => Expression::bool(*value),
            SwitchCaseTag::Null => Expression::null(),
            SwitchCaseTag::Undefined => Expression::undefined(false),
        }
    }

    fn switch_case_test(&self, test: Expression, tag: &SwitchCaseTag) -> Expression {
        Expression::bin(BinOp::EqEqEq, test, Self::switch_case_expr(tag))
    }

    fn compile_small_string_switch_assignment(
        &mut self,
        result: &Ident,
        test: Expression,
        cases: &[(SwitchCaseTag, &Lambda)],
        default: Option<&Lambda>,
        complete: bool,
    ) -> Option<Block> {
        match cases {
            [] => Some(
                default
                    .map(|fallback| self.compile_assign_to_target_block(result, fallback))
                    .unwrap_or_default(),
            ),
            [(_tag, body)] if complete && default.is_none() => {
                Some(self.compile_assign_to_target_block(result, body))
            }
            [(tag, body)] => {
                let cond = self.switch_case_test(test, tag);
                let then_block = self.compile_assign_to_target_block(result, body);
                let else_block = default
                    .map(|fallback| self.compile_assign_to_target_block(result, fallback))
                    .unwrap_or_default();
                Some(self.compile_test_assignment_block(result, cond, then_block, else_block))
            }
            [(tag, then_body), (_, else_body)] if complete && default.is_none() => {
                let cond = self.switch_case_test(test, tag);
                let then_block = self.compile_assign_to_target_block(result, then_body);
                let else_block = self.compile_assign_to_target_block(result, else_body);
                Some(self.compile_test_assignment_block(result, cond, then_block, else_block))
            }
            _ => None,
        }
    }

    fn compile_small_string_switch_return(
        &mut self,
        test: Expression,
        cases: &[(SwitchCaseTag, &Lambda)],
        default: Option<&Lambda>,
        complete: bool,
    ) -> Option<Block> {
        match cases {
            [] => Some(
                default
                    .map(|fallback| self.compile_return_block(fallback))
                    .unwrap_or_default(),
            ),
            [(_tag, body)] if complete && default.is_none() => {
                Some(self.compile_return_block(body))
            }
            [(tag, body)] => {
                let cond = self.switch_case_test(test, tag);
                let then_block = self.compile_return_block(body);
                let else_block = default
                    .map(|fallback| self.compile_return_block(fallback))
                    .unwrap_or_default();
                Some(self.compile_test_return_block(cond, then_block, else_block))
            }
            [(tag, then_body), (_, else_body)] if complete && default.is_none() => {
                let cond = self.switch_case_test(test, tag);
                let then_block = self.compile_return_block(then_body);
                let else_block = self.compile_return_block(else_body);
                Some(self.compile_test_return_block(cond, then_block, else_block))
            }
            _ => None,
        }
    }

    fn compile_effect_if(&self, cond: Expression, then_block: Block, else_block: Block) -> Block {
        if then_block.is_empty() {
            if else_block.is_empty() {
                // OCaml's `S.if_ cond [] []` collapses to `S.exp cond`
                // (js_stmt_make.ml:242 + 45-53). Preserves bare comparisons
                // like `tmp === null;` that come from a switch where every
                // dispatched arm falls through to the same continuation.
                let mut block = vec![];
                push_s_exp(&mut block, cond);
                block
            } else {
                vec![Statement::if_(Expression::not(cond), else_block, vec![])]
            }
        } else if else_block.is_empty() {
            vec![Statement::if_(cond, then_block, vec![])]
        } else {
            vec![Statement::if_(cond, then_block, else_block)]
        }
    }

    fn normalized_if_block(cond: Expression, then_block: Block, else_block: Block) -> Block {
        match Statement::if_(cond, then_block, else_block).desc {
            StatementDesc::Block(block) => block,
            desc => vec![Statement::new(desc)],
        }
    }

    fn peel_single_block_statement(block: Block) -> Block {
        match block.as_slice() {
            [
                Statement {
                    desc: StatementDesc::Block(inner),
                    ..
                },
            ] => Self::peel_single_block_statement(inner.clone()),
            _ => block,
        }
    }

    fn normalize_runtime_test_return_body(block: Block) -> Block {
        let block = Self::peel_single_block_statement(block);
        Self::shared_trailing_return_guard_block(&block).unwrap_or(block)
    }

    fn shared_trailing_return_guard_block(block: &Block) -> Option<Block> {
        let (first, rest) = block.split_first()?;
        let StatementDesc::If(cond, then_block, else_block) = &first.desc else {
            return None;
        };
        if !else_block.is_empty() || rest.is_empty() {
            return None;
        }

        let then_return = trailing_return_expression(then_block)?;
        let else_return = trailing_return_expression(rest)?;
        if !ocaml_eq_expression(then_return, else_return) {
            return None;
        }
        if then_block.len() != 2 || rest.len() != 2 {
            return None;
        }

        let then_block = then_block[..then_block.len() - 1].to_vec();
        let else_block = rest[..rest.len() - 1].to_vec();
        if then_block.is_empty() || else_block.is_empty() {
            return None;
        }

        Some(vec![
            Statement::new(StatementDesc::If(cond.clone(), then_block, else_block)),
            Statement::return_(then_return.clone()),
        ])
    }

    fn compile_small_string_switch_effect(
        &mut self,
        test: Expression,
        cases: &[(SwitchCaseTag, &Lambda)],
        default: Option<&Lambda>,
        complete: bool,
    ) -> Option<Block> {
        match cases {
            [] => Some(
                default
                    .map(|fallback| self.compile_effect_block(fallback))
                    .unwrap_or_default(),
            ),
            [(_tag, body)] if complete && default.is_none() => {
                Some(self.compile_effect_block(body))
            }
            [(tag, body)] => {
                let cond = self.switch_case_test(test, tag);
                let then_block = self.compile_effect_block(body);
                let else_block = default
                    .map(|fallback| self.compile_effect_block(fallback))
                    .unwrap_or_default();
                Some(self.compile_effect_if(cond, then_block, else_block))
            }
            [(tag, then_body), (_, else_body)] if complete && default.is_none() => {
                let cond = self.switch_case_test(test, tag);
                let then_block = self.compile_effect_block(then_body);
                let else_block = self.compile_effect_block(else_body);
                Some(self.compile_effect_if(cond, then_block, else_block))
            }
            _ => None,
        }
    }

    fn compile_named_string_switch_assignment_with_strategy(
        &mut self,
        result: &Ident,
        test: Expression,
        cases: &[(SwitchCaseTag, &Lambda)],
        default: Option<&Lambda>,
        complete: bool,
        allow_small: bool,
    ) -> Block {
        if allow_small {
            // OCaml's `compile_general_cases` (lam_compile.ml:540-566) pattern-
            // matches the UNFILTERED cases list against `[(id, lam)], Default x`
            // etc. Cases that equal the default are only filtered out in the
            // `_, _` switch arm (lam_compile.ml:587-592), AFTER the small-arm
            // selection. Pre-filtering would let `[("Pow", 1), ("Sum", -1)]`
            // with `Default(-1)` collapse to `[(Pow, 1)] + Default(-1)` and
            // hit the 1-case-Default S.if_ arm, where OCaml stays in the
            // switch arm and emits `switch { case "Pow": 1; default: -1 }`.
            if let Some(block) = self.compile_small_string_switch_assignment(
                result,
                test.clone(),
                cases,
                default,
                complete,
            ) {
                return block;
            }
        }

        let filtered_cases = self.filtered_switch_case_refs(cases, default);
        let clauses = stable_group_switch_cases(filtered_cases, |_, _| true)
            .into_iter()
            .map(|(tag, body, is_last)| StringClause {
                tag_type: tag,
                clause: if is_last {
                    CaseClause {
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
        vec![Statement::new(StatementDesc::StringSwitch(
            test,
            clauses,
            default_block,
        ))]
    }

    fn compile_named_string_switch_assignment(
        &mut self,
        result: &Ident,
        test: Expression,
        cases: &[(SwitchCaseTag, &Lambda)],
        default: Option<&Lambda>,
        complete: bool,
    ) -> Block {
        self.compile_named_string_switch_assignment_with_strategy(
            result, test, cases, default, complete, true,
        )
    }

    fn compile_named_string_switch_return_with_strategy(
        &mut self,
        test: Expression,
        cases: &[(SwitchCaseTag, &Lambda)],
        default: Option<&Lambda>,
        complete: bool,
        allow_small: bool,
    ) -> Block {
        if complete
            && default.is_none()
            && expression_has_no_side_effects(&test)
            && cases.split_first().is_some_and(|((_, first_body), rest)| {
                rest.iter()
                    .all(|(_, body)| super::lambda_eq_approx(first_body, body))
            })
        {
            let body = self.compile_return_block(cases[0].1);
            if !body.is_empty() {
                // OCaml's two-case Complete arm (lam_compile.ml:558) emits
                // `S.if_ (test === id1) then else`. When every case is
                // `Lstaticraise X` and Rust's `compile_return_block` resolved
                // it via `with_static_handler` -> `resolve_static_raise`
                // inline, the inlined handler body fills both branches.
                // OCaml instead leaves the raises as fallthrough -> empty
                // and emits the staticcatch handler body once after the
                // dispatch, so `S.if_ test [] []` collapses to `S.exp test`
                // (js_stmt_make.ml:242 + 45-53) and the bare comparison
                // (`tmp === null;`) survives in front of the handler.
                // Prepend `S.exp (test === id1)` here to recover that
                // shape when the dispatched cases are all `Lstaticraise`.
                if cases.len() >= 2
                    && cases
                        .iter()
                        .all(|(_, body)| matches!(body, Lambda::LstaticRaise(_, _)))
                {
                    let test_expr = self.switch_case_test(test, &cases[0].0);
                    let mut prefix = vec![];
                    push_s_exp(&mut prefix, test_expr);
                    prefix.extend(body);
                    return prefix;
                }
                // The general "all cases equal → just return body" collapse is
                // only valid when OCaml's `compile_general_cases` would reduce
                // to a body-only return via `S.if_` + `E.econd`. That path is
                // the 1-case Complete arm (lam_compile.ml:543) or the 2-case
                // Complete arm (lam_compile.ml:558) — both handled by
                // `compile_small_string_switch_return`. For 3+ cases OCaml
                // takes the `_, _` arm (lam_compile.ml:567+) which uses
                // `group_apply` + `S.string_switch` and KEEPS the switch form
                // even when all bodies are identical. Gate on `allow_small` to
                // match: when a caller disables the small path (e.g. the
                // untagged block switch wrapping a typeof tail in an instance
                // if-chain, compile.rs:3614), the typeof switch stays as a
                // switch statement so the outer `Statement::if_` rule
                // "block_last_is_terminal → flip to sequence" (mod.rs:1550)
                // mirrors OCaml's `S.if_` rule 249-250 and produces the
                // `if (instance) return X; switch (typeof e) { ... }` shape
                // OCaml emits (UntaggedVariants.res `awaitUser`, `can_merge`).
                if allow_small && cases.len() <= 2 {
                    return body;
                }
            }
            // Body compiles to empty (e.g. all dispatched cases are
            // fallthrough static raises). Fall through to the regular
            // dispatch path so OCaml's `S.if_ cond [] []` -> `S.exp cond`
            // rule (js_stmt_make.ml:242 + 45-53) preserves bare comparisons
            // like `tmp === null;`.
        }

        if allow_small {
            if let Some(block) =
                self.compile_small_string_switch_return(test.clone(), cases, default, complete)
            {
                return block;
            }
        }

        let filtered_cases = self.filtered_switch_case_refs(cases, default);
        let grouped_cases = stable_group_switch_cases(filtered_cases, |_, _| true);
        let mut shared_tail = None;
        let clauses = if default.is_none() && self.active_fallthrough_return_handler().is_none() {
            let mut clauses = Vec::with_capacity(grouped_cases.len());
            let mut group_start = 0;
            while group_start < grouped_cases.len() {
                let mut group_end = group_start;
                while !grouped_cases[group_end].2 {
                    group_end += 1;
                }

                let (_, body, _) = &grouped_cases[group_end];
                let compiled_body = self.compile_hoisted_named_string_return_tail(body);
                let hoist_shared_tail = group_start != group_end
                    && group_end + 1 == grouped_cases.len()
                    && self.should_hoist_grouped_named_string_return_tail(body)
                    && !compiled_body.is_empty()
                    && block_terminates(&compiled_body);

                for (tag, _, _) in &grouped_cases[group_start..group_end] {
                    clauses.push(StringClause {
                        tag_type: tag.clone(),
                        clause: empty_switch_case_clause(),
                    });
                }
                clauses.push(StringClause {
                    tag_type: grouped_cases[group_end].0.clone(),
                    clause: if hoist_shared_tail {
                        shared_tail = Some(compiled_body);
                        CaseClause {
                            body: vec![],
                            should_break: true,
                            comment: None,
                        }
                    } else {
                        // Mirror `grouped_return_string_clauses`'s break
                        // calculation: a body that doesn't terminate but
                        // contains a static raise compiles to an exit
                        // assignment (`exit$N = N`) that needs an explicit
                        // `break;` to leave the switch. Without it the
                        // next clause falls through.
                        let should_break =
                            !block_terminates(&compiled_body) && lambda_has_exit(body);
                        CaseClause {
                            body: compiled_body,
                            should_break,
                            comment: None,
                        }
                    },
                });

                group_start = group_end + 1;
            }
            clauses
        } else {
            self.grouped_return_string_clauses(grouped_cases, |tag| tag)
        };

        let default_block = default
            .map(|fallback| self.compile_return_block(fallback))
            .filter(|body| !body.is_empty());
        let mut block = vec![Statement::new(StatementDesc::StringSwitch(
            test,
            clauses,
            default_block,
        ))];
        if let Some(tail) = shared_tail {
            block.extend(tail);
        }
        block
    }

    fn compile_named_string_switch_return(
        &mut self,
        test: Expression,
        cases: &[(SwitchCaseTag, &Lambda)],
        default: Option<&Lambda>,
        complete: bool,
    ) -> Block {
        self.compile_named_string_switch_return_with_strategy(test, cases, default, complete, true)
    }

    fn compile_small_string_switch_tail_loop_return(
        &mut self,
        test: Expression,
        cases: &[(SwitchCaseTag, &Lambda)],
        default: Option<&Lambda>,
        complete: bool,
        tail_loop: &mut TailLoopState,
    ) -> Option<Block> {
        match cases {
            [] => Some(
                default
                    .map(|fallback| self.compile_tail_loop_return_block(fallback, tail_loop))
                    .unwrap_or_default(),
            ),
            [(_tag, body)] if complete && default.is_none() => {
                Some(self.compile_tail_loop_return_block(body, tail_loop))
            }
            [(tag, body)] => Some(vec![Statement::if_(
                self.switch_case_test(test, tag),
                self.compile_tail_loop_return_block(body, tail_loop),
                default
                    .map(|fallback| self.compile_tail_loop_return_block(fallback, tail_loop))
                    .unwrap_or_default(),
            )]),
            [(tag, then_body), (_, else_body)] if complete && default.is_none() => {
                Some(vec![Statement::if_(
                    self.switch_case_test(test, tag),
                    self.compile_tail_loop_return_block(then_body, tail_loop),
                    self.compile_tail_loop_return_block(else_body, tail_loop),
                )])
            }
            _ => None,
        }
    }

    fn grouped_tail_loop_return_string_clauses<'a, T: Clone>(
        &mut self,
        grouped_cases: Vec<(T, &'a Lambda, bool)>,
        mut to_tag: impl FnMut(T) -> SwitchCaseTag,
        tail_loop: &mut TailLoopState,
    ) -> Vec<StringClause> {
        let mut clauses = Vec::with_capacity(grouped_cases.len());
        let mut group_start = 0;
        while group_start < grouped_cases.len() {
            let mut group_end = group_start;
            while !grouped_cases[group_end].2 {
                group_end += 1;
            }

            let (_, body, _) = &grouped_cases[group_end];
            let compiled_body = self.compile_tail_loop_return_block(body, tail_loop);
            let group_falls_through = compiled_body.is_empty();
            // Mirror `grouped_return_string_clauses`'s break calculation:
            // a body that doesn't terminate but contains a static raise
            // compiles to an exit assignment (`exit$N = N`) that needs an
            // explicit `break;` to leave the switch — otherwise the next
            // case clause falls through and overwrites the exit value.
            let should_break =
                !block_terminates(&compiled_body) && lambda_has_exit(body);

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

    fn compile_named_string_switch_tail_loop_return(
        &mut self,
        test: Expression,
        cases: &[(SwitchCaseTag, &Lambda)],
        default: Option<&Lambda>,
        complete: bool,
        tail_loop: &mut TailLoopState,
    ) -> Block {
        // OCaml's `compile_general_cases` (lam_compile.ml:540-566) selects the
        // small `S.if_` arms against the UNFILTERED cases list. Filtering
        // happens only inside the `_, _` switch arm (lam_compile.ml:587-592).
        // Pass the original cases here so a 2-cases-with-Default that filters
        // down to 1 still emits a `switch` (matching OCaml), instead of
        // collapsing to `if/else`.
        if let Some(block) = self.compile_small_string_switch_tail_loop_return(
            test.clone(),
            cases,
            default,
            complete,
            tail_loop,
        ) {
            return block;
        }

        let filtered_cases = self.filtered_switch_case_refs(cases, default);
        let clauses = self.grouped_tail_loop_return_string_clauses(
            stable_group_switch_cases(filtered_cases, |_, _| true),
            |tag| tag,
            tail_loop,
        );

        let default_block = default
            .map(|fallback| self.compile_tail_loop_return_block(fallback, tail_loop))
            .filter(|body| !body.is_empty());

        vec![Statement::new(StatementDesc::StringSwitch(
            test,
            clauses,
            default_block,
        ))]
    }

    fn compile_named_string_switch_effect_with_strategy(
        &mut self,
        test: Expression,
        cases: &[(SwitchCaseTag, &Lambda)],
        default: Option<&Lambda>,
        complete: bool,
        allow_small: bool,
    ) -> Block {
        if allow_small {
            // OCaml's `compile_general_cases` (lam_compile.ml:540-566) selects
            // the small `S.if_` arms against the UNFILTERED cases list.
            // Filtering happens only inside the `_, _` switch arm
            // (lam_compile.ml:587-592). Pass `cases` here, not the filtered
            // list, so `[(case, body)] + Default(eq body)` shapes derived from
            // a >1-case input keep emitting a switch.
            if let Some(block) = self.compile_small_string_switch_effect(
                test.clone(),
                cases,
                default,
                complete,
            ) {
                return block;
            }
        }

        let filtered_cases = self.filtered_switch_case_refs(cases, default);
        let clauses: Vec<_> = stable_group_switch_cases(filtered_cases, |_, _| true)
            .into_iter()
            .map(|(tag, body, is_last)| {
                let clause = if is_last {
                    let body = self.compile_effect_block(body);
                    CaseClause {
                        should_break: !block_terminates(&body),
                        body,
                        comment: None,
                    }
                } else {
                    empty_switch_case_clause()
                };
                StringClause {
                    tag_type: tag,
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
            return vec![];
        }

        vec![Statement::new(StatementDesc::StringSwitch(
            test,
            clauses,
            default_block,
        ))]
    }

    fn compile_named_string_switch_effect(
        &mut self,
        test: Expression,
        cases: &[(SwitchCaseTag, &Lambda)],
        default: Option<&Lambda>,
        complete: bool,
    ) -> Block {
        self.compile_named_string_switch_effect_with_strategy(test, cases, default, complete, true)
    }

    fn compile_named_variant_switch_assignment_statements(
        &mut self,
        result: &Ident,
        scrut_expr: Expression,
        switch: &LambdaSwitch,
    ) -> Block {
        let Some(const_cases) = self.named_const_cases(switch) else {
            return vec![];
        };
        let Some(block_cases) = self.named_block_cases(switch) else {
            return vec![];
        };

        let const_default = self.const_switch_default(switch);
        let block_default = self.block_switch_default(switch);
        let tag_name = self.variant_tag_name(switch);

        if const_cases.is_empty() && block_cases.is_empty() {
            return const_default
                .map(|fallback| self.compile_assign_to_target_block(result, fallback))
                .unwrap_or_default();
        }

        let const_complete = self.const_switch_complete(switch);
        let block_complete = self.block_switch_complete(switch);
        let const_branch = if const_cases.is_empty() {
            const_default
                .map(|fallback| self.compile_assign_to_target_block(result, fallback))
                .unwrap_or_default()
        } else {
            self.compile_named_string_switch_assignment(
                result,
                scrut_expr.clone(),
                &const_cases,
                const_default,
                const_complete,
            )
        };
        let block_branch = if block_cases.is_empty() {
            block_default
                .map(|fallback| self.compile_assign_to_target_block(result, fallback))
                .unwrap_or_default()
        } else {
            self.compile_named_string_switch_assignment(
                result,
                self.variant_tag_expr(scrut_expr.clone(), &tag_name),
                &block_cases,
                block_default,
                block_complete,
            )
        };

        if const_cases.is_empty() && const_complete {
            block_branch
        } else if block_cases.is_empty() && block_complete {
            const_branch
        } else {
            self.dispatch_named_variant_branches(scrut_expr, const_branch, block_branch)
        }
    }

    fn compile_named_variant_switch_return_statements(
        &mut self,
        scrut_expr: Expression,
        switch: &LambdaSwitch,
    ) -> Block {
        let Some(const_cases) = self.named_const_cases(switch) else {
            return vec![];
        };
        let Some(block_cases) = self.named_block_cases(switch) else {
            return vec![];
        };

        let const_default = self.const_switch_default(switch);
        let block_default = self.block_switch_default(switch);
        let tag_name = self.variant_tag_name(switch);

        if const_cases.is_empty() && block_cases.is_empty() {
            return const_default
                .map(|fallback| self.compile_return_block(fallback))
                .unwrap_or_default();
        }

        let const_complete = self.const_switch_complete(switch);
        let block_complete = self.block_switch_complete(switch);
        let const_branch = if const_cases.is_empty() {
            const_default
                .map(|fallback| self.compile_return_block(fallback))
                .unwrap_or_default()
        } else {
            self.compile_named_string_switch_return(
                scrut_expr.clone(),
                &const_cases,
                const_default,
                const_complete,
            )
        };
        let block_branch = if block_cases.is_empty() {
            block_default
                .map(|fallback| self.compile_return_block(fallback))
                .unwrap_or_default()
        } else {
            self.compile_named_string_switch_return(
                self.variant_tag_expr(scrut_expr.clone(), &tag_name),
                &block_cases,
                block_default,
                block_complete,
            )
        };

        if const_cases.is_empty() && const_complete {
            block_branch
        } else if block_cases.is_empty() && block_complete {
            const_branch
        } else {
            self.dispatch_named_variant_branches(scrut_expr, const_branch, block_branch)
        }
    }

    fn compile_named_variant_switch_tail_loop_return_statements(
        &mut self,
        scrut_expr: Expression,
        switch: &LambdaSwitch,
        tail_loop: &mut TailLoopState,
    ) -> Block {
        let Some(const_cases) = self.named_const_cases(switch) else {
            return vec![];
        };
        let Some(block_cases) = self.named_block_cases(switch) else {
            return vec![];
        };

        let const_default = self.const_switch_default(switch);
        let block_default = self.block_switch_default(switch);
        let tag_name = self.variant_tag_name(switch);

        if const_cases.is_empty() && block_cases.is_empty() {
            return const_default
                .map(|fallback| self.compile_tail_loop_return_block(fallback, tail_loop))
                .unwrap_or_default();
        }

        let const_complete = self.const_switch_complete(switch);
        let block_complete = self.block_switch_complete(switch);
        let const_branch = if const_cases.is_empty() {
            const_default
                .map(|fallback| self.compile_tail_loop_return_block(fallback, tail_loop))
                .unwrap_or_default()
        } else {
            self.compile_named_string_switch_tail_loop_return(
                scrut_expr.clone(),
                &const_cases,
                const_default,
                const_complete,
                tail_loop,
            )
        };
        let block_branch = if block_cases.is_empty() {
            block_default
                .map(|fallback| self.compile_tail_loop_return_block(fallback, tail_loop))
                .unwrap_or_default()
        } else {
            self.compile_named_string_switch_tail_loop_return(
                self.variant_tag_expr(scrut_expr.clone(), &tag_name),
                &block_cases,
                block_default,
                block_complete,
                tail_loop,
            )
        };

        if const_cases.is_empty() && const_complete {
            block_branch
        } else if block_cases.is_empty() && block_complete {
            const_branch
        } else {
            self.dispatch_named_variant_branches(scrut_expr, const_branch, block_branch)
        }
    }

    fn compile_named_variant_switch_effect_statements(
        &mut self,
        scrut_expr: Expression,
        switch: &LambdaSwitch,
    ) -> Block {
        let Some(const_cases) = self.named_const_cases(switch) else {
            return vec![];
        };
        let Some(block_cases) = self.named_block_cases(switch) else {
            return vec![];
        };

        let const_default = self.const_switch_default(switch);
        let block_default = self.block_switch_default(switch);
        let tag_name = self.variant_tag_name(switch);

        if const_cases.is_empty() && block_cases.is_empty() {
            return const_default
                .map(|fallback| self.compile_effect_block(fallback))
                .unwrap_or_default();
        }

        let const_complete = self.const_switch_complete(switch);
        let block_complete = self.block_switch_complete(switch);
        let const_branch = if const_cases.is_empty() {
            const_default
                .map(|fallback| self.compile_effect_block(fallback))
                .unwrap_or_default()
        } else {
            self.compile_named_string_switch_effect(
                scrut_expr.clone(),
                &const_cases,
                const_default,
                const_complete,
            )
        };
        let block_branch = if block_cases.is_empty() {
            block_default
                .map(|fallback| self.compile_effect_block(fallback))
                .unwrap_or_default()
        } else {
            self.compile_named_string_switch_effect(
                self.variant_tag_expr(scrut_expr.clone(), &tag_name),
                &block_cases,
                block_default,
                block_complete,
            )
        };

        if const_cases.is_empty() && const_complete {
            block_branch
        } else if block_cases.is_empty() && block_complete {
            const_branch
        } else {
            self.compile_effect_if(
                self.variant_non_object_test(scrut_expr),
                const_branch,
                block_branch,
            )
        }
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

    fn compile_test_assignment_block(
        &self,
        result: &Ident,
        cond: Expression,
        then_block: Block,
        else_block: Block,
    ) -> Block {
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

    fn take_single_result_assignment(&self, id: &Ident, block: Block) -> Result<Expression, Block> {
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
    /// (lam_compile.ml:1422-1427). When both branches compile to
    /// `{block=[]; value=Some e}` via `NeedValue`, OCaml emits
    /// `Return(Cond(cond, out1, out2))` where each `out` is the branch's
    /// tail expression (e.g. `Seq(log, undef)` for `Lsequence(log, Lconst undef)`).
    /// `E.econd` then folds `Cond(Seq(a,undef), Seq(b,undef))` to
    /// `Seq(Cond(a,b), undef)`, which `js_pass_flatten`'s Return(Seq) +
    /// Exp(Cond) rules later flatten into the clean `[If(cond, [Exp a], [Exp b]);
    /// Return undef]` shape printed as `if (cond) { a; } else { b; }`.
    ///
    /// Rust's `compile_return_block` for `Lsequence(effect, Lconst undef)`
    /// pre-flattens to `[Exp effect; Return Undefined]` — losing the `Seq`
    /// shape that `take_return_tail_expr`'s undefined-rejection guard then
    /// refuses to reconstruct. Fold here explicitly so the caller can match
    /// OCaml's `Return(Cond(Seq, Seq))` construction.
    ///
    /// Returns `Some(Seq(e1, Seq(e2, ..., Return-expr)))` iff the block is
    /// exactly `[Exp e1, Exp e2, ..., Return last]`. The prefix must be
    /// non-empty — for a single `[Return]` block the generic
    /// `take_return_tail_expr` path is sufficient.
    fn try_fold_effect_only_return_tail(&self, block: &Block) -> Option<Expression> {
        let (last, prefix) = block.split_last()?;
        let Statement {
            desc: StatementDesc::Return(tail_expr),
            ..
        } = last
        else {
            return None;
        };
        // Accept both a single `[Return tail]` (empty prefix — the inner
        // Lifthenelse case where `compile_if_return_block` has already
        // folded into `Return(Seq(Cond, undef))`) and the multi-statement
        // `[Exp e1, ..., Exp eN, Return tail]` case. Reject any prefix
        // statement that isn't a plain `Exp` — control-flow stmts like
        // Return/Throw/If would break the `Seq` fold.
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
        if std::env::var_os("RUST_DEBUG_TAKE_RETURN_TAIL").is_some() {
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
        let cond_compiled = self.compile_expr(cond);
        let then_block_raw = self.compile_return_block(then_);
        let else_block_raw = self.compile_return_block(else_);

        // Mirror OCaml's Lifthenelse `EffectCall (Maybe_tail_is_return)` arm
        // (lam_compile.ml:1422-1427). When both branches are pure
        // effect-plus-Return-tail shapes like `[Exp e1, ..., Return tail]`
        // (produced by `Lsequence(effect, Lconst undef)` tails), fold each
        // into a `Seq` expression and build
        // `Return(Expression::cond(cond, then_seq, else_seq))`.
        // `Expression::cond` folds `Cond(Seq(a, undef), Seq(b, undef))` to
        // `Seq(Cond(a, b), undef)` (js_ir/mod.rs:784-805, matching OCaml's
        // `E.econd` at js_exp_make.ml:1201-1204). The subsequent
        // `flatten_block` pass rewrites `Return(Seq(_, _))` and `Exp(Cond)`
        // into the clean `[If(cond, [Exp a], [Exp b]); Return undef]` shape
        // that `print_function_body` drops to `if (cond) { a; } else { b; }`.
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
            then_block_raw.clone(),
            else_block_raw.clone(),
            then_block_raw,
            else_block_raw,
        ));
        block
    }

    fn compile_test_return_block(
        &self,
        cond: Expression,
        then_block: Block,
        else_block: Block,
    ) -> Block {
        self.compile_test_return_block_with_fallback(
            cond,
            then_block.clone(),
            else_block.clone(),
            then_block,
            else_block,
        )
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
        then_for_fold: Block,
        else_for_fold: Block,
        then_fallback: Block,
        else_fallback: Block,
    ) -> Block {
        if std::env::var_os("RUST_DEBUG_COMPILE_TEST_RETURN").is_some() {
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
        let folded = match (
            strict_single_return_expr(&then_for_fold),
            strict_single_return_expr(&else_for_fold),
        ) {
            (Some(then_expr), Some(else_expr)) => Some((then_expr.clone(), else_expr.clone())),
            _ => None,
        };
        match folded {
            Some((then_expr, else_expr)) => {
                vec![Statement::return_(Expression::cond(cond, then_expr, else_expr))]
            }
            None => {
                // Use the normalized fallback blocks when we can't collapse
                // to `Return(Cond)`, matching the previous behavior for
                // non-both-single-return cases.
                vec![Statement::if_(cond, then_fallback, else_fallback)]
            }
        }
    }

    fn compile_switch_value_block(&mut self, result: &Ident, lam: &Lambda) -> Block {
        let mut block = self.compile_assign_to_target_block(result, lam);
        if !block_terminates(&block) {
            block.push(Statement::break_());
        }
        block
    }

    fn compile_assign_to_target_block(&mut self, result: &Ident, lam: &Lambda) -> Block {
        match lam {
            Lambda::Llet(kind, id, value, body) => {
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
                let (handlers, flat_body) =
                    flatten_nested_caches(*label, bindings, body, handler);
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
                    tag,
                    if is_last {
                        crate::js_ir::CaseClause {
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
            let should_break =
                !block_terminates(&compiled_body) && lambda_has_exit(body);

            for (tag, _, _) in &grouped_cases[group_start..group_end] {
                cases.push((tag.clone(), empty_switch_case_clause(), group_falls_through));
            }
            cases.push((
                grouped_cases[group_end].0,
                crate::js_ir::CaseClause {
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
            .map(|(tag, clause, _)| (tag, clause))
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
                    let body = self.compile_effect_block(body);
                    crate::js_ir::CaseClause {
                        should_break: !block_terminates(&body),
                        body,
                        comment: None,
                    }
                } else {
                    empty_switch_case_clause()
                };
                (tag, clause)
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
                    let body = self.compile_effect_block(body);
                    crate::js_ir::CaseClause {
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

    fn dynamic_import_body(&self, lam: &Lambda) -> Option<Lambda> {
        let call = match lam {
            Lambda::Lfunction(func) => match func.body.as_ref() {
                Lambda::Lprim(prim) => prim,
                Lambda::Lsequence(first, second)
                    if matches!(
                        second.as_ref(),
                        Lambda::Lconst(Constant::JsUndefined { .. })
                    ) =>
                {
                    match first.as_ref() {
                        Lambda::Lprim(prim) => prim,
                        _ => return None,
                    }
                }
                _ => return None,
            },
            _ => return None,
        };

        match &call.primitive {
            Primitive::PjsCall {
                prim_name,
                arg_types,
                ffi,
                transformed_jsx,
                ..
            } => Some(Lambda::prim(
                Primitive::PjsCall {
                    prim_name: prim_name.clone(),
                    arg_types: arg_types.clone(),
                    ffi: ffi.clone(),
                    dynamic_import: true,
                    transformed_jsx: *transformed_jsx,
                },
                call.args.clone(),
                call.loc.clone(),
            )),
            _ => None,
        }
    }

    fn compile_import_primitive(&mut self, args: &[Lambda]) -> Compiled {
        let target = match args {
            [arg] => self.dynamic_import_body(arg).unwrap_or_else(|| arg.clone()),
            _ => {
                let mut prelude = vec![];
                let mut compiled_args = Vec::new();
                for arg in args {
                    let compiled = self.compile_expr(arg);
                    prelude.extend(compiled.prelude);
                    compiled_args.push(compiled.expr);
                }
                return Compiled {
                    prelude,
                    expr: self.compile_import(compiled_args),
                };
            }
        };

        let compiled = self.compile_expr(&target);
        let prelude = compiled.prelude;
        let expr = self.compile_import(vec![compiled.expr]);
        Compiled { prelude, expr }
    }

    fn compile_primitive(&mut self, prim: &Primitive, args: &[Lambda]) -> Compiled {
        if matches!(prim, Primitive::Pimport) {
            return self.compile_import_primitive(args);
        }

        use Primitive::*;
        let mut prelude = vec![];
        let mut compiled_args = Vec::new();
        for arg in args {
            let compiled = self.compile_expr(arg);
            prelude.extend(compiled.prelude);
            compiled_args.push(compiled.expr);
        }

        let expr = match prim {
            Pstringlength => Expression::length(compiled_args[0].clone(), LengthObject::String),
            Parraylength => Expression::length(compiled_args[0].clone(), LengthObject::Array),
            Pstringrefs | Pstringrefu => {
                self.runtime_call_expr("Primitive_string", "getChar", compiled_args)
            }
            Parrayrefu => match compiled_args.as_slice() {
                [array, index] => Expression::new(ExpressionDesc::ArrayIndex(
                    Box::new(array.clone()),
                    Box::new(index.clone()),
                )),
                _ => Expression::undefined(false),
            },
            Parrayrefs => self.runtime_call_expr("Primitive_array", "get", compiled_args),
            Parraysetu => match compiled_args.as_slice() {
                [array, index, value] => Expression::new(ExpressionDesc::Seq(
                    Box::new(Expression::bin(
                        BinOp::Eq,
                        Expression::new(ExpressionDesc::ArrayIndex(
                            Box::new(array.clone()),
                            Box::new(index.clone()),
                        )),
                        value.clone(),
                    )),
                    Box::new(Expression::undefined(false)),
                )),
                _ => Expression::undefined(false),
            },
            Parraysets => self.runtime_call_expr("Primitive_array", "set", compiled_args),
            Paddint => int32_add(compiled_args[0].clone(), compiled_args[1].clone()),
            Paddfloat => Expression::bin(
                BinOp::Plus,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Paddbigint => Expression::bin(
                BinOp::Plus,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Psubint => int32_minus(compiled_args[0].clone(), compiled_args[1].clone()),
            Psubfloat => Expression::bin(
                BinOp::Minus,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Psubbigint => Expression::bin(
                BinOp::Minus,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Pmulint => int32_mul(compiled_args[0].clone(), compiled_args[1].clone()),
            Pmulfloat => Expression::bin(
                BinOp::Mul,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Pmulbigint => Expression::bin(
                BinOp::Mul,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Pdivint => self.int32_div_expr(compiled_args[0].clone(), compiled_args[1].clone()),
            Pdivfloat => Expression::bin(
                BinOp::Div,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Pdivbigint => self.bigint_div_expr(compiled_args[0].clone(), compiled_args[1].clone()),
            Pmodint => self.int32_mod_expr(compiled_args[0].clone(), compiled_args[1].clone()),
            Pmodfloat => Expression::bin(
                BinOp::Mod,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Pmodbigint => self.bigint_mod_expr(compiled_args[0].clone(), compiled_args[1].clone()),
            Ppowint => int32_pow(compiled_args[0].clone(), compiled_args[1].clone()),
            Ppowfloat => Expression::bin(
                BinOp::Pow,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Ppowbigint => Expression::bin(
                BinOp::Pow,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Pobjcomp(cmp) => self.compile_object_comparison(
                *cmp,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Pboolcomp(cmp) => self.compile_bool_comparison(
                *cmp,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Pintcomp(cmp) | Pfloatcomp(cmp) => self.compile_int_comparison(
                *cmp,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Pbigintcomp(cmp) => self.compile_bigint_comparison(
                *cmp,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Pjscomp(cmp) => {
                compile_raw_comparison(*cmp, compiled_args[0].clone(), compiled_args[1].clone())
            }
            Pstringcomp(cmp) => self.compile_string_comparison(
                *cmp,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Pobjorder => self.runtime_call_expr("Primitive_object", "compare", compiled_args),
            Pobjmin => self.runtime_call_expr("Primitive_object", "min", compiled_args),
            Pobjmax => self.runtime_call_expr("Primitive_object", "max", compiled_args),
            Pobjtag => Expression::new(ExpressionDesc::CamlBlockTag(
                Box::new(compiled_args[0].clone()),
                "TAG".to_string(),
            )),
            Pobjsize => Expression::length(compiled_args[0].clone(), LengthObject::CamlBlock),
            Pboolorder => match (
                bool_literal(&compiled_args[0]),
                bool_literal(&compiled_args[1]),
            ) {
                (Some(left), Some(right)) => {
                    let result = match left.cmp(&right) {
                        std::cmp::Ordering::Less => -1,
                        std::cmp::Ordering::Equal => 0,
                        std::cmp::Ordering::Greater => 1,
                    };
                    int_expr(result)
                }
                _ => self.runtime_call_expr("Primitive_bool", "compare", compiled_args),
            },
            Pboolmin => self.compile_typed_min_max(
                "Primitive_bool",
                "min",
                Comparison::Lt,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
                both_bool_literals,
            ),
            Pboolmax => self.compile_typed_min_max(
                "Primitive_bool",
                "max",
                Comparison::Gt,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
                both_bool_literals,
            ),
            Pintorder => self.runtime_call_expr("Primitive_int", "compare", compiled_args),
            Pintmin => self.compile_typed_min_max(
                "Primitive_int",
                "min",
                Comparison::Lt,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
                both_int_literals,
            ),
            Pintmax => self.compile_typed_min_max(
                "Primitive_int",
                "max",
                Comparison::Gt,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
                both_int_literals,
            ),
            Pfloatorder => self.runtime_call_expr("Primitive_float", "compare", compiled_args),
            Pfloatmin => self.compile_typed_min_max(
                "Primitive_float",
                "min",
                Comparison::Lt,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
                both_float_literals,
            ),
            Pfloatmax => self.compile_typed_min_max(
                "Primitive_float",
                "max",
                Comparison::Gt,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
                both_float_literals,
            ),
            Pbigintorder => self.runtime_call_expr("Primitive_bigint", "compare", compiled_args),
            Pbigintmin => self.compile_typed_min_max(
                "Primitive_bigint",
                "min",
                Comparison::Lt,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
                both_bigint_literals,
            ),
            Pbigintmax => self.compile_typed_min_max(
                "Primitive_bigint",
                "max",
                Comparison::Gt,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
                both_bigint_literals,
            ),
            Pstringorder => self.runtime_call_expr("Primitive_string", "compare", compiled_args),
            Pstringmin => self.compile_typed_min_max(
                "Primitive_string",
                "min",
                Comparison::Lt,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
                both_string_literals,
            ),
            Pstringmax => self.compile_typed_min_max(
                "Primitive_string",
                "max",
                Comparison::Gt,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
                both_string_literals,
            ),
            Phash => self.runtime_call_expr("Primitive_hash", "hash", compiled_args),
            PhashMixint => self.runtime_call_expr("Primitive_hash", "hash_mix_int", compiled_args),
            PhashMixstring => {
                self.runtime_call_expr("Primitive_hash", "hash_mix_string", compiled_args)
            }
            PhashFinalmix => {
                self.runtime_call_expr("Primitive_hash", "hash_final_mix", compiled_args)
            }
            Psequand => Expression::bin(
                BinOp::And,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Psequor => Expression::bin(
                BinOp::Or,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Pnot => Expression::not(compiled_args[0].clone()),
            Pnegint => int32_minus(int_expr(0), compiled_args[0].clone()),
            // `Pnegfloat` must emit `0. - x` (not `0 - x`) so the printer
            // rule at `js_dump.ml` / `printer.rs:1520-1531` produces `- x`
            // with the OCaml-style space. Mirrors
            // `lam_compile_primitive.ml:179`: `E.float_minus E.zero_float_lit`.
            Pnegfloat => Expression::bin(
                BinOp::Minus,
                Expression::number(Number::float("0.")),
                compiled_args[0].clone(),
            ),
            Pnegbigint => Expression::bin(
                BinOp::Minus,
                Expression::number(Number::bigint(true, "0")),
                compiled_args[0].clone(),
            ),
            Pnotint => int_bnot(compiled_args[0].clone()),
            Pnotbigint => int_bnot(compiled_args[0].clone()),
            Pandint => int32_band(compiled_args[0].clone(), compiled_args[1].clone()),
            Pandbigint => Expression::bin(
                BinOp::Band,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Porint => int32_bor(compiled_args[0].clone(), compiled_args[1].clone()),
            Porbigint => Expression::bin(
                BinOp::Bor,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Pxorint => int32_bxor(compiled_args[0].clone(), compiled_args[1].clone()),
            Pxorbigint => Expression::bin(
                BinOp::Bxor,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Plslint => int32_lsl(compiled_args[0].clone(), compiled_args[1].clone()),
            Plslbigint => Expression::bin(
                BinOp::Lsl,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Plsrint => int32_lsr(compiled_args[0].clone(), compiled_args[1].clone()),
            Pasrint => Expression::bin(
                BinOp::Asr,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Pasrbigint => Expression::bin(
                BinOp::Asr,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Poffsetint(offset) => int32_offset(compiled_args[0].clone(), *offset),
            Poffsetref(offset) => {
                let field = Expression::new(ExpressionDesc::StaticIndex(
                    Box::new(compiled_args[0].clone()),
                    "contents".to_string(),
                    None,
                ));
                Expression::new(ExpressionDesc::Seq(
                    Box::new(Expression::bin(
                        BinOp::Eq,
                        field.clone(),
                        int32_offset(field, *offset),
                    )),
                    Box::new(Expression::undefined(false)),
                ))
            }
            Pisint => is_type_number_expr(compiled_args[0].clone()),
            PisPolyVarBlock => is_type_object_expr(compiled_args[0].clone()),
            Pisout(offset) => match compiled_args.as_slice() {
                [range, value] => is_out_expr(int32_offset(value.clone(), *offset), range.clone()),
                _ => Expression::undefined(false),
            },
            Pmakearray => Expression::array(compiled_args, MutableFlag::Mutable),
            Pmakedict => match compiled_args.as_slice() {
                [
                    Expression {
                        desc: ExpressionDesc::Array(items, _),
                        ..
                    },
                ] => {
                    let props = items
                        .iter()
                        .filter_map(|item| match &item.desc {
                            ExpressionDesc::CamlBlock(fields, _, _, _)
                                if matches!(
                                    fields.as_slice(),
                                    [
                                        Expression {
                                            desc: ExpressionDesc::Str { .. },
                                            ..
                                        },
                                        _
                                    ]
                                ) =>
                            {
                                let [
                                    Expression {
                                        desc: ExpressionDesc::Str { txt, .. },
                                        ..
                                    },
                                    value,
                                ] = fields.as_slice()
                                else {
                                    unreachable!("checked by matches! above");
                                };
                                Some((PropertyName::lit(txt.clone()), value.clone()))
                            }
                            _ => None,
                        })
                        .collect();
                    Expression::new(ExpressionDesc::Object(None, props))
                }
                _ => Expression::undefined(false),
            },
            PdictHas => match compiled_args.as_slice() {
                [obj, prop] => Expression::new(ExpressionDesc::In(
                    Box::new(prop.clone()),
                    Box::new(obj.clone()),
                )),
                _ => Expression::undefined(false),
            },
            Pduprecord => match compiled_args.as_slice() {
                [source] => Expression::new(ExpressionDesc::Object(
                    Some(Box::new(source.clone())),
                    vec![],
                )),
                _ => Expression::undefined(false),
            },
            Pstringadd => {
                Expression::string_append(compiled_args[0].clone(), compiled_args[1].clone())
            }
            PinitMod => self.runtime_call_expr("Primitive_module", "init", compiled_args),
            PupdateMod => self.runtime_call_expr("Primitive_module", "update", compiled_args),
            PnullToOpt => self.null_to_opt_expr(compiled_args[0].clone()),
            PnullUndefinedToOpt => self.null_undefined_to_opt_expr(compiled_args[0].clone()),
            PisNotNone => self.is_not_none_expr(compiled_args[0].clone()),
            PisNull => self.is_null_expr(compiled_args[0].clone()),
            PisUndefined => self.is_undefined_expr(compiled_args[0].clone()),
            PisNullUndefined => self.is_null_or_undefined_expr(compiled_args[0].clone()),
            PvalFromOption => self.val_from_option_expr(compiled_args[0].clone()),
            PvalFromOptionNotNest => compiled_args[0].clone(),
            Psome => self.some_expr(compiled_args[0].clone()),
            PsomeNotNest => self.optional_block(compiled_args[0].clone(), true),
            Pfield(idx, info) => self.compile_field_access(*idx, info, &compiled_args[0]),
            Psetfield(idx, info) => {
                let target =
                    self.compile_set_field(*idx, info, &compiled_args[0], &compiled_args[1]);
                Expression::new(ExpressionDesc::Seq(
                    Box::new(target),
                    Box::new(Expression::undefined(false)),
                ))
            }
            Pmakeblock(tag, tag_info, mutable_flag) => {
                let js_mutable = match mutable_flag {
                    Mutable::Mutable => MutableFlag::Mutable,
                    Mutable::Immutable => MutableFlag::Immutable,
                };
                Expression::new(ExpressionDesc::CamlBlock(
                    compiled_args,
                    js_mutable,
                    Box::new(Expression::number(Number::int(*tag))),
                    tag_info.clone(),
                ))
            }
            PrawJsCode(info) => {
                Expression::new(ExpressionDesc::RawJsCode(crate::js_ir::JsRawInfo {
                    code: info.code.trim().to_string(),
                    is_stmt: info.is_stmt,
                }))
            }
            Pdebugger => {
                prelude.push(Statement::debugger());
                Expression::undefined(false)
            }
            Praise => {
                let expr = compiled_args
                    .first()
                    .cloned()
                    .unwrap_or_else(|| Expression::undefined(false));
                prelude.push(Statement::throw(expr));
                Expression::undefined(false)
            }
            Pidentity => compiled_args
                .first()
                .cloned()
                .unwrap_or_else(|| Expression::undefined(false)),
            Pignore => Expression::new(ExpressionDesc::Seq(
                Box::new(
                    compiled_args
                        .first()
                        .cloned()
                        .unwrap_or_else(|| Expression::undefined(false)),
                ),
                Box::new(Expression::undefined(true)),
            )),
            Ptypeof => ocaml_typeof_expr(compiled_args[0].clone()),
            Pintoffloat => to_int32(compiled_args[0].clone()),
            Pfloatofint => compiled_args
                .first()
                .cloned()
                .unwrap_or_else(|| Expression::undefined(false)),
            Pawait => Expression::new(ExpressionDesc::Await(Box::new(compiled_args[0].clone()))),
            PwrapExn => {
                self.runtime_call_expr("Primitive_exceptions", "internalToException", compiled_args)
            }
            PcreateExtension(name) => self.pure_runtime_call_expr(
                "Primitive_exceptions",
                "create",
                vec![Expression::string(name.clone())],
            ),
            PjsObjectCreate(obj_params) => {
                self.compile_js_object_create(obj_params, compiled_args, &mut prelude)
            }
            PjsFnMake(_) | PjsFnMakeUnit => compiled_args
                .first()
                .cloned()
                .unwrap_or_else(|| Expression::undefined(false)),
            PjsFnMethod => match compiled_args.first().cloned() {
                Some(Expression {
                    desc:
                        ExpressionDesc::Fun {
                            params,
                            body,
                            env,
                            return_unit,
                            async_,
                            directive,
                            ..
                        },
                    comment,
                }) => Expression {
                    desc: ExpressionDesc::Fun {
                        is_method: true,
                        params,
                        body,
                        env,
                        return_unit,
                        async_,
                        directive,
                    },
                    comment,
                },
                Some(expr) => expr,
                None => Expression::undefined(false),
            },
            PjsUnsafeDowngrade { name, setter } => match (*setter, compiled_args.as_slice()) {
                (false, [receiver]) => self.static_index(receiver.clone(), name),
                (true, [receiver, value]) => Expression::new(ExpressionDesc::Seq(
                    Box::new(Expression::bin(
                        BinOp::Eq,
                        self.static_index(receiver.clone(), name),
                        value.clone(),
                    )),
                    Box::new(Expression::undefined(true)),
                )),
                _ => Expression::undefined(false),
            },
            Pimport => self.compile_import(compiled_args),
            PjsCall {
                prim_name,
                arg_types,
                ffi,
                dynamic_import,
                transformed_jsx,
            } => self.compile_js_call(
                prim_name,
                arg_types,
                ffi,
                *dynamic_import,
                *transformed_jsx,
                compiled_args,
                &mut prelude,
            ),
            Pnull => Expression::null(),
            Pundefined => Expression::undefined(false),
            _ => Expression::undefined(false),
        };

        Compiled { prelude, expr }
    }

    fn some_none_depth(cst: &Constant) -> Option<usize> {
        match cst {
            Constant::Some(inner) => Self::some_none_depth(inner).map(|depth| depth + 1),
            Constant::ModuleAlias | Constant::JsUndefined { .. } => Some(0),
            _ => None,
        }
    }

    fn nested_some_none(depth: usize, none: Expression) -> Expression {
        if depth == 0 {
            none
        } else {
            Self::nested_some_none(
                depth - 1,
                Expression::new(ExpressionDesc::OptionalBlock(Box::new(none), false)),
            )
        }
    }

    fn compile_some_constant(inner: &Constant) -> Expression {
        match Self::some_none_depth(inner) {
            Some(depth) => Self::nested_some_none(
                depth,
                Expression::new(ExpressionDesc::OptionalBlock(
                    Box::new(Expression::undefined(false)),
                    false,
                )),
            ),
            None => Expression::new(ExpressionDesc::OptionalBlock(
                Box::new(Self::compile_constant(inner)),
                true,
            )),
        }
    }

    fn compile_constant(cst: &Constant) -> Expression {
        match cst {
            Constant::JsNull => Expression::null(),
            Constant::JsUndefined { is_unit } => Expression::undefined(*is_unit),
            Constant::JsTrue => Expression::bool(true),
            Constant::JsFalse => Expression::bool(false),
            Constant::Int {
                i,
                comment: Some(PointerInfo::Constructor(tag)),
            } => match &tag.runtime_tag {
                Some(ConstructorRuntimeTag::Int(value)) => Expression::number(Number::int(*value)),
                Some(ConstructorRuntimeTag::String(value)) => Expression::string(value.clone()),
                Some(ConstructorRuntimeTag::Float(value)) => {
                    Expression::number(Number::float(value.clone()))
                }
                Some(ConstructorRuntimeTag::BigInt(value)) => {
                    Expression::number(Number::bigint(true, value.clone()))
                }
                Some(ConstructorRuntimeTag::Bool(value)) => Expression::bool(*value),
                Some(ConstructorRuntimeTag::Null) => Expression::null(),
                Some(ConstructorRuntimeTag::Undefined) => Expression::undefined(false),
                None if tag.name != "[]" => Expression::string(tag.name.clone()),
                None => Expression::with_comment(
                    ExpressionDesc::Number(Number::int(*i)),
                    tag.name.clone(),
                ),
            },
            Constant::Int { i, comment } => match pointer_info_comment_text(comment.as_ref()) {
                Some(comment) => {
                    Expression::with_comment(ExpressionDesc::Number(Number::int(*i)), comment)
                }
                None => Expression::number(Number::int(*i)),
            },
            Constant::NativeInt { i, comment } => {
                match pointer_info_comment_text(comment.as_ref()) {
                    Some(comment) => Expression::with_comment(
                        ExpressionDesc::Number(Number::float(i.to_string())),
                        comment,
                    ),
                    None => Expression::number(Number::float(i.to_string())),
                }
            }
            Constant::Char(c) => Expression::number(Number::Int { i: *c, c: Some(*c) }),
            Constant::String { s, delim } => {
                let delim = match delim {
                    Some(StringDelim::StarJ) => Delim::StarJ,
                    // OCaml's lam_compile_const.ml lowers lambda string constants with
                    // DNoQuotes through E.str, so they stay ordinary quoted JS strings.
                    Some(StringDelim::NoQuotes) => Delim::None,
                    Some(StringDelim::Backtick) => Delim::BackQuotes,
                    Some(StringDelim::Plain) | None => Delim::None,
                };
                Expression::new(ExpressionDesc::Str {
                    delim,
                    txt: s.clone(),
                })
            }
            Constant::ImmString(s) => Expression::new(ExpressionDesc::Str {
                delim: Delim::None,
                txt: s.clone(),
            }),
            Constant::Float(f) => Expression::number(Number::float(f.clone())),
            Constant::BigInt { negative, value } => {
                Expression::number(Number::bigint(!negative, value.clone()))
            }
            Constant::Pointer(name) => Expression::string(name.clone()),
            Constant::Block {
                tag,
                tag_info,
                elements,
            } => {
                let elems = elements.iter().map(Self::compile_constant).collect();
                // OCaml's `Lam_compile_const.translate` (lam_compile_const.ml:67-69)
                // calls `Js_of_lam_block.make_block NA tag_info ...` — `NA`, not
                // `Immutable`. Downstream JS-pass rules that match
                // `Caml_block(_, Immutable, _, _)` (notably the binding-hoist rule
                // in `js_pass_flatten_and_mark_dead.ml:172-183`) deliberately skip
                // `NA`, so e.g. `let h = list{1,2,3,4}` (a `Lconst Const_block`)
                // stays inline as `{hd: 1, tl: {hd: 2, ...}}` while
                // `let CustomizeTags = Pmakeblock(...)` (which IS `Immutable`) gets
                // its inner `Caml_block(NA)` constants hoisted to
                // `let CustomizeTags_d = ...`. Mirror the OCaml convention here.
                Expression::new(ExpressionDesc::CamlBlock(
                    elems,
                    MutableFlag::NA,
                    Box::new(Expression::number(Number::int(*tag))),
                    tag_info.clone(),
                ))
            }
            Constant::Some(inner) => Self::compile_some_constant(inner),
            Constant::ModuleAlias => Expression::undefined(false),
        }
    }

    fn cmj_export_constant_expr(constant: CmjExportConstant) -> Expression {
        match constant {
            CmjExportConstant::Bool(value) => Expression::bool(value),
            CmjExportConstant::Null => Expression::null(),
            CmjExportConstant::Undefined { is_unit } => Expression::undefined(is_unit),
        }
    }

    fn resolve_cmj_module_field_constant(
        &mut self,
        module: &ModuleId,
        field_name: &str,
    ) -> Option<Expression> {
        if !matches!(module.kind, Kind::Ml) {
            return None;
        }

        if !self.cmj_constant_cache.contains_key(module.id.name()) {
            let constants = self
                .module_path_resolver
                .as_ref()
                .and_then(|resolver| resolver.module_cmj_export_constants(module.id.name()));
            self.cmj_constant_cache
                .insert(module.id.name().to_string(), constants);
        }

        let constants = self
            .cmj_constant_cache
            .get(module.id.name())
            .and_then(|constants| constants.as_ref())?;
        let constant = constants.get(field_name).copied()?;
        Some(Self::cmj_export_constant_expr(constant))
    }

    fn compile_field_access(
        &mut self,
        idx: i32,
        info: &FieldDbgInfo,
        target: &Expression,
    ) -> Expression {
        match info {
            FieldDbgInfo::Module { name } => match &target.desc {
                ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(module, None)) => {
                    if let Some(constant) = self.resolve_cmj_module_field_constant(module, name) {
                        return constant;
                    }
                    Expression::qualified(module.clone(), Some(name.clone()))
                }
                _ => pure_indexed_block_item(target, idx).unwrap_or_else(|| {
                    Expression::new(ExpressionDesc::StaticIndex(
                        Box::new(target.clone()),
                        convert_ident_name(name),
                        Some(idx),
                    ))
                }),
            },
            FieldDbgInfo::Record { name, .. }
            | FieldDbgInfo::RecordInline { name }
            | FieldDbgInfo::RecordExtension { name } => pure_indexed_block_item(target, idx)
                .unwrap_or_else(|| {
                    Expression::new(ExpressionDesc::StaticIndex(
                        Box::new(target.clone()),
                        name.clone(),
                        None,
                    ))
                }),
            FieldDbgInfo::Extension => pure_indexed_block_item(target, idx).unwrap_or_else(|| {
                Expression::new(ExpressionDesc::StaticIndex(
                    Box::new(target.clone()),
                    format!("_{}", idx),
                    Some(idx),
                ))
            }),
            FieldDbgInfo::Cons => pure_indexed_block_item(target, idx).unwrap_or_else(|| {
                Expression::new(ExpressionDesc::StaticIndex(
                    Box::new(target.clone()),
                    match idx {
                        0 => "hd".to_string(),
                        1 => "tl".to_string(),
                        _ => format!("_{}", idx),
                    },
                    None,
                ))
            }),
            FieldDbgInfo::PolyVarTag => poly_var_tag_access(target),
            FieldDbgInfo::PolyVarContent => poly_var_value_access(target),
            FieldDbgInfo::VariantTag => pure_indexed_block_item(target, idx).unwrap_or_else(|| {
                Expression::new(ExpressionDesc::StaticIndex(
                    Box::new(target.clone()),
                    "TAG".to_string(),
                    None,
                ))
            }),
            FieldDbgInfo::Variant => pure_indexed_block_item(target, idx).unwrap_or_else(|| {
                // Variant fields are accessed as _0, _1, _2, ...
                Expression::new(ExpressionDesc::StaticIndex(
                    Box::new(target.clone()),
                    format!("_{}", idx),
                    None,
                ))
            }),
            _ => pure_indexed_block_item(target, idx).unwrap_or_else(|| {
                Expression::new(ExpressionDesc::ArrayIndex(
                    Box::new(target.clone()),
                    Box::new(Expression::number(Number::int(idx))),
                ))
            }),
        }
    }

    fn compile_set_field(
        &self,
        _idx: i32,
        info: &crate::lambda::compat::SetFieldDbgInfo,
        target: &Expression,
        value: &Expression,
    ) -> Expression {
        if js_expr_no_side_effects(target)
            && matches!(
                target.desc,
                ExpressionDesc::Array(_, _) | ExpressionDesc::CamlBlock(_, _, _, _)
            )
        {
            return value.clone();
        }

        let field = match info {
            crate::lambda::compat::SetFieldDbgInfo::RecordSet(name)
            | crate::lambda::compat::SetFieldDbgInfo::RecordInlineSet(name)
            | crate::lambda::compat::SetFieldDbgInfo::RecordExtensionSet(name) => Expression::new(
                ExpressionDesc::StaticIndex(Box::new(target.clone()), name.clone(), None),
            ),
        };
        Expression::bin(BinOp::Eq, field, value.clone())
    }

    fn compile_external_arg_const(&self, cst: &ExternalArgConst) -> Expression {
        match cst {
            ExternalArgConst::IntLit(i) => Expression::number(Number::Int {
                i: *i as i32,
                c: None,
            }),
            ExternalArgConst::StringLit(s, delim) => {
                let delim = match delim {
                    ExternalArgDelim::None => Delim::None,
                    ExternalArgDelim::StarJ => Delim::StarJ,
                    ExternalArgDelim::NoQuotes => Delim::NoQuotes,
                    ExternalArgDelim::BackQuotes => Delim::BackQuotes,
                };
                Expression::new(ExpressionDesc::Str {
                    delim,
                    txt: s.clone(),
                })
            }
        }
    }

    fn runtime_member_expr(&self, module_name: &str, member: &str) -> Expression {
        Expression::qualified(
            ModuleId {
                id: Ident::create_persistent(module_name),
                kind: Kind::Runtime,
                dynamic_import: false,
            },
            Some(member.to_string()),
        )
    }

    fn runtime_call_expr(
        &self,
        module_name: &str,
        member: &str,
        args: Vec<Expression>,
    ) -> Expression {
        Expression::call(
            self.runtime_member_expr(module_name, member),
            args,
            CallInfo::default(),
        )
    }

    fn int32_div_expr(&self, left: Expression, right: Expression) -> Expression {
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

    fn int32_mod_expr(&self, left: Expression, right: Expression) -> Expression {
        match int_literal(&right) {
            Some(rhs) if rhs != 0 => Expression::bin(BinOp::Mod, left, right),
            _ if self.check_div_by_zero => {
                self.runtime_call_expr("Primitive_int", "mod_", vec![left, right])
            }
            _ => Expression::bin(BinOp::Mod, left, right),
        }
    }

    fn bigint_div_expr(&self, left: Expression, right: Expression) -> Expression {
        if self.check_div_by_zero {
            self.runtime_call_expr("Primitive_bigint", "div", vec![left, right])
        } else {
            Expression::bin(BinOp::Div, left, right)
        }
    }

    fn bigint_mod_expr(&self, left: Expression, right: Expression) -> Expression {
        if self.check_div_by_zero {
            self.runtime_call_expr("Primitive_bigint", "mod_", vec![left, right])
        } else {
            Expression::bin(BinOp::Mod, left, right)
        }
    }

    fn external_optional_to_undefined_expr(&self, arg: Expression) -> Expression {
        match arg.desc {
            ExpressionDesc::Undefined { .. } => Expression::undefined(false),
            ExpressionDesc::OptionalBlock(inner, _) => *inner,
            _ if expression_has_no_side_effects(&arg) => Expression::cond(
                self.is_not_none_expr(arg.clone()),
                self.val_from_option_expr(arg),
                Expression::undefined(false),
            ),
            _ => self.runtime_call_expr("Primitive_option", "toUndefined", vec![arg]),
        }
    }

    fn external_option_unwrap_expr(&self, arg: Expression) -> Expression {
        match arg.desc {
            ExpressionDesc::Undefined { .. } => Expression::undefined(false),
            ExpressionDesc::OptionalBlock(inner, _) => self.external_polyvar_unwrap_expr(*inner),
            _ => self.runtime_call_expr("Primitive_option", "unwrapPolyVar", vec![arg]),
        }
    }

    fn external_polyvar_string_expr(
        &self,
        arg: Expression,
        dispatches: &[(String, String)],
    ) -> Expression {
        match &arg.desc {
            ExpressionDesc::Undefined { .. } => Expression::undefined(false),
            ExpressionDesc::Str { txt, .. } => {
                Expression::string(external_polyvar_string_dispatch(dispatches, txt))
            }
            _ => string_switch_iife(
                arg,
                dispatches
                    .iter()
                    .map(|(source, target)| (source.clone(), Expression::string(target.clone())))
                    .collect(),
            ),
        }
    }

    fn external_polyvar_event_exprs(
        &self,
        arg: Expression,
        dispatches: Option<&[(String, String)]>,
    ) -> Vec<Expression> {
        match &arg.desc {
            ExpressionDesc::CamlBlock(items, _, _, TagInfo::PolyVar(_))
                if matches!(
                    items.as_slice(),
                    [
                        Expression {
                            desc: ExpressionDesc::Str { .. },
                            ..
                        },
                        value,
                    ] if expression_has_no_side_effects(value)
                ) =>
            {
                let [
                    Expression {
                        desc: ExpressionDesc::Str { txt, .. },
                        ..
                    },
                    value,
                ] = items.as_slice()
                else {
                    unreachable!();
                };
                let tag = match dispatches {
                    Some(dispatches) => {
                        Expression::string(external_polyvar_string_dispatch(dispatches, txt))
                    }
                    None => Expression::string(txt.clone()),
                };
                vec![tag, value.clone()]
            }
            _ => {
                let tag = match dispatches {
                    Some(dispatches) => {
                        self.external_polyvar_string_expr(poly_var_tag_access(&arg), dispatches)
                    }
                    None => poly_var_tag_access(&arg),
                };
                vec![tag, poly_var_value_access(&arg)]
            }
        }
    }

    fn external_polyvar_int_expr(
        &self,
        arg: Expression,
        dispatches: &[(String, i64)],
    ) -> Expression {
        match &arg.desc {
            ExpressionDesc::Undefined { .. } => Expression::undefined(false),
            ExpressionDesc::Str { txt, .. } => {
                int_expr(external_polyvar_int_dispatch(dispatches, txt) as i32)
            }
            _ => string_switch_iife(
                arg,
                dispatches
                    .iter()
                    .map(|(source, target)| (source.clone(), int_expr(*target as i32)))
                    .collect(),
            ),
        }
    }

    fn external_polyvar_unwrap_expr(&self, arg: Expression) -> Expression {
        match &arg.desc {
            ExpressionDesc::CamlBlock(items, _, _, _)
                if matches!(
                    items.as_slice(),
                    [
                        Expression {
                            desc: ExpressionDesc::Number(_),
                            ..
                        },
                        _,
                    ]
                ) =>
            {
                items[1].clone()
            }
            _ => poly_var_value_access(&arg),
        }
    }

    fn pure_runtime_call_expr(
        &self,
        module_name: &str,
        member: &str,
        args: Vec<Expression>,
    ) -> Expression {
        Expression::with_comment(
            ExpressionDesc::Call(
                Box::new(self.runtime_member_expr(module_name, member)),
                args,
                CallInfo::default(),
            ),
            "@__PURE__",
        )
    }

    fn compile_eta_wrapped_runtime_alias(
        &self,
        func: &crate::lambda::LFunction,
    ) -> Option<Expression> {
        if func.attr.one_unit_arg || func.attr.async_ || func.attr.directive.is_some() {
            return None;
        }

        let Lambda::Lprim(info) = func.body.as_ref() else {
            return None;
        };
        if !eta_wrapped_args_match_params(&func.params, &info.args) {
            return None;
        }
        let (module_name, member) = runtime_member_for_eta_wrapped_primitive(&info.primitive)?;
        Some(self.runtime_member_expr(module_name, member))
    }

    fn try_compile_identity_module_return_expr(&mut self, lam: &Lambda) -> Option<Expression> {
        let mut module_target_var: Option<Ident> = None;
        let mut module_target_global: Option<(Ident, bool)> = None;
        let mut alias_chain = Vec::new();
        let mut cursor = lam;

        let mut note_target = |target: &Lambda| -> Option<()> {
            match target {
                Lambda::Lvar(id) => {
                    if module_target_global.is_some()
                        || module_target_var
                            .as_ref()
                            .is_some_and(|current| !current.same(id))
                    {
                        return None;
                    }
                    module_target_var.get_or_insert_with(|| id.clone());
                    Some(())
                }
                Lambda::LglobalModule(id, dynamic_import) => {
                    if module_target_var.is_some()
                        || module_target_global.as_ref().is_some_and(
                            |(current_id, current_dynamic_import)| {
                                !current_id.same(id) || *current_dynamic_import != *dynamic_import
                            },
                        )
                    {
                        return None;
                    }
                    module_target_global.get_or_insert_with(|| (id.clone(), *dynamic_import));
                    Some(())
                }
                _ => None,
            }
        };

        loop {
            match cursor {
                Lambda::Llet(kind, alias_id, value, body)
                    if matches!(kind, LetKind::Alias | LetKind::Strict | LetKind::StrictOpt) =>
                {
                    let Lambda::Lprim(info) = value.as_ref() else {
                        return None;
                    };
                    let Primitive::Pfield(index, FieldDbgInfo::Module { name }) = &info.primitive
                    else {
                        return None;
                    };
                    let [target] = info.args.as_slice() else {
                        return None;
                    };
                    note_target(target)?;

                    alias_chain.push((alias_id.clone(), *index, name.clone()));
                    cursor = body.as_ref();
                }
                Lambda::Lprim(info) => {
                    let Primitive::Pmakeblock(_, TagInfo::Module(fields), Mutable::Immutable) =
                        &info.primitive
                    else {
                        return None;
                    };
                    if alias_chain.len() != fields.len() || info.args.len() != fields.len() {
                        // The simplifier can inline the alias chain into the final
                        // Pmakeblock args, so only the final runtime field count is exact.
                        if info.args.len() != fields.len() {
                            return None;
                        }
                    }

                    for (position, arg) in info.args.iter().enumerate() {
                        let expected_field = &fields[position];
                        match arg {
                            Lambda::Lvar(arg_id) => {
                                let Some((_, field_index, field_name)) = alias_chain
                                    .iter()
                                    .find(|(alias_id, _, _)| alias_id.same(arg_id))
                                else {
                                    return None;
                                };
                                if *field_index != position as i32 || field_name != expected_field {
                                    return None;
                                }
                            }
                            Lambda::Lprim(crate::lambda::PrimInfo {
                                primitive:
                                    Primitive::Pfield(
                                        field_index,
                                        FieldDbgInfo::Module { name: field_name },
                                    ),
                                args,
                                ..
                            }) => {
                                if *field_index != position as i32 || field_name != expected_field {
                                    return None;
                                }
                                let [target] = args.as_slice() else {
                                    return None;
                                };
                                note_target(target)?;
                            }
                            _ => return None,
                        }
                    }

                    return if let Some(id) = module_target_var {
                        Some(Expression::var(id))
                    } else if let Some((id, dynamic_import)) = module_target_global {
                        Some(Expression::qualified(
                            ModuleId {
                                id,
                                kind: Kind::Ml,
                                dynamic_import,
                            },
                            None,
                        ))
                    } else {
                        None
                    };
                }
                _ => return None,
            }
        }
    }

    fn compile_object_comparison(
        &self,
        cmp: Comparison,
        left: Expression,
        right: Expression,
    ) -> Expression {
        match cmp {
            Comparison::Eq | Comparison::Neq
                if is_nullish_literal(&left).is_some() || is_nullish_literal(&right).is_some() =>
            {
                compile_nullish_strict_comparison(cmp, left, right)
            }
            _ => self.runtime_call_expr(
                "Primitive_object",
                comparison_to_runtime_member(cmp),
                vec![left, right],
            ),
        }
    }

    fn compile_bool_comparison(
        &self,
        cmp: Comparison,
        left: Expression,
        right: Expression,
    ) -> Expression {
        match (bool_literal(&left), bool_literal(&right)) {
            (Some(lhs), Some(rhs)) => Expression::bool(compare_bool_literals(cmp, lhs, rhs)),
            (Some(true), _) | (_, Some(false)) => match cmp {
                Comparison::Lt => js_seq(
                    if matches!(bool_literal(&left), Some(true)) {
                        right
                    } else {
                        left
                    },
                    Expression::bool(false),
                ),
                Comparison::Ge => js_seq(
                    if matches!(bool_literal(&left), Some(true)) {
                        right
                    } else {
                        left
                    },
                    Expression::bool(true),
                ),
                Comparison::Eq | Comparison::Neq | Comparison::Le | Comparison::Gt => {
                    compile_raw_comparison(cmp, left, right)
                }
            },
            (_, Some(true)) | (Some(false), _) => match cmp {
                Comparison::Le => js_seq(
                    if matches!(bool_literal(&right), Some(true)) {
                        left
                    } else {
                        right
                    },
                    Expression::bool(true),
                ),
                Comparison::Gt => js_seq(
                    if matches!(bool_literal(&right), Some(true)) {
                        left
                    } else {
                        right
                    },
                    Expression::bool(false),
                ),
                Comparison::Eq | Comparison::Neq | Comparison::Lt | Comparison::Ge => {
                    compile_raw_comparison(cmp, left, right)
                }
            },
            _ => compile_raw_comparison(cmp, left, right),
        }
    }

    fn compile_int_comparison(
        &self,
        cmp: Comparison,
        left: Expression,
        right: Expression,
    ) -> Expression {
        if let (Some(lhs), Some(rhs)) = (int_literal(&left), int_literal(&right)) {
            return Expression::bool(compare_int_literals(cmp, lhs, rhs));
        }

        // OCaml's Js_exp_make.int_comp strips Runtime.compare(..., ...) when
        // the RHS is the integer literal 0, so compare(x, y) > 0 lowers to x > y.
        if int_literal(&right) == Some(0) {
            if let Some((compare_left, compare_right)) = runtime_compare_call_args(&left) {
                return self.compile_int_comparison(
                    cmp,
                    compare_left.clone(),
                    compare_right.clone(),
                );
            }
        }

        match cmp {
            Comparison::Eq => {
                if ((is_optional_block(&left)
                    && matches!(&right.desc, ExpressionDesc::Undefined { .. }))
                    || (matches!(&left.desc, ExpressionDesc::Undefined { .. })
                        && is_optional_block(&right)))
                    && js_expr_no_side_effects(&left)
                    && js_expr_no_side_effects(&right)
                {
                    return Expression::bool(false);
                }

                compile_int_equality(left, right)
            }
            Comparison::Neq => {
                if ((is_optional_block(&left)
                    && matches!(&right.desc, ExpressionDesc::Undefined { .. }))
                    || (matches!(&left.desc, ExpressionDesc::Undefined { .. })
                        && is_optional_block(&right))
                    || (matches!(&left.desc, ExpressionDesc::CamlBlock(_, _, _, _))
                        && matches!(&right.desc, ExpressionDesc::Number(_)))
                    || (matches!(&left.desc, ExpressionDesc::Number(_))
                        && matches!(&right.desc, ExpressionDesc::CamlBlock(_, _, _, _))))
                    && js_expr_no_side_effects(&left)
                    && js_expr_no_side_effects(&right)
                {
                    return Expression::bool(true);
                }

                // Fold literal string!==string, mirroring OCaml's
                // `string_comp Cneq` at `js_exp_make.ml:1355-1362`.
                if let (
                    ExpressionDesc::Str { txt: left_txt, delim: left_delim },
                    ExpressionDesc::Str { txt: right_txt, delim: right_delim },
                ) = (&left.desc, &right.desc)
                {
                    if let Some(equal) = crate::js_ir::fold_strict_string_equality_pub(
                        left_txt, left_delim, right_txt, right_delim,
                    ) {
                        return Expression::bool(!equal);
                    }
                }

                // OCaml's `Js_exp_make.int_comp` falls through to
                // `bin NotEqEq e0 e1` for the non-special Cneq cases — and
                // OCaml's `bin` has no NotEqEq case, so the construction is
                // effectively raw. `Expression::bin`'s `fold_strict_comparison`
                // would fold `3 !== null` to `true` via the nullish-impossible
                // rule, diverging from OCaml. Use a raw `Bin` here.
                crate::js_ir::raw_bin_expression(comparison_to_binop(cmp), left, right)
            }
            Comparison::Lt | Comparison::Le | Comparison::Gt | Comparison::Ge => {
                compile_raw_comparison(cmp, left, right)
            }
        }
    }

    fn compile_string_comparison(
        &self,
        cmp: Comparison,
        left: Expression,
        right: Expression,
    ) -> Expression {
        match compare_string_literals(&left, &right) {
            Some(equal) => match cmp {
                Comparison::Eq => Expression::bool(equal),
                Comparison::Neq => Expression::bool(!equal),
                Comparison::Lt | Comparison::Le | Comparison::Gt | Comparison::Ge => {
                    compile_raw_comparison(cmp, left, right)
                }
            },
            None => compile_raw_comparison(cmp, left, right),
        }
    }

    fn compile_bigint_comparison(
        &self,
        cmp: Comparison,
        left: Expression,
        right: Expression,
    ) -> Expression {
        match compare_bigint_literals(&left, &right) {
            Some(equal) => match cmp {
                Comparison::Eq => Expression::bool(equal),
                Comparison::Neq => Expression::bool(!equal),
                Comparison::Lt | Comparison::Le | Comparison::Gt | Comparison::Ge => {
                    compile_raw_comparison(cmp, left, right)
                }
            },
            None => compile_raw_comparison(cmp, left, right),
        }
    }

    fn compile_typed_min_max(
        &self,
        module_name: &str,
        member: &str,
        compare: Comparison,
        left: Expression,
        right: Expression,
        literal_fast_path: fn(&Expression, &Expression) -> bool,
    ) -> Expression {
        if literal_fast_path(&left, &right) {
            Expression::cond(
                Expression::bin(comparison_to_binop(compare), left.clone(), right.clone()),
                left,
                right,
            )
        } else {
            self.runtime_call_expr(module_name, member, vec![left, right])
        }
    }

    fn external_module_id(
        &mut self,
        module_name: &ExternalModuleName,
        default: bool,
        dynamic_import: bool,
    ) -> ModuleId {
        let key = ExternalModuleCacheKey {
            // OCaml interns external imports by bundle/default, not by the
            // latest hint name, so later aliases reuse the first binding id.
            bundle: module_name.bundle.clone(),
            default,
        };
        let id = self
            .external_module_ids
            .entry(key)
            .or_insert_with(|| self.id_gen.create(&external_module_ident_name(module_name)))
            .clone();

        ModuleId {
            id,
            kind: Kind::External {
                name: module_name.bundle.clone(),
                default,
                import_attributes: external_module_import_attributes(module_name),
            },
            dynamic_import,
        }
    }

    fn external_module_binding(
        &mut self,
        module_name: &ExternalModuleName,
        default: bool,
        dynamic_import: bool,
    ) -> Expression {
        Expression::qualified(
            self.external_module_id(module_name, default, dynamic_import),
            None,
        )
    }

    fn translate_scoped_module_value(
        &mut self,
        module_name: Option<&ExternalModuleName>,
        name: &str,
        scopes: &[String],
        dynamic_import: bool,
    ) -> Expression {
        match module_name {
            Some(module_name) => match scopes.split_first() {
                None => {
                    let default = name == "default";
                    Expression::qualified(
                        self.external_module_id(module_name, default, dynamic_import),
                        Some(name.to_string()),
                    )
                }
                Some((first_scope, rest_scopes)) => {
                    let mut expr = Expression::qualified(
                        self.external_module_id(module_name, false, dynamic_import),
                        Some(first_scope.clone()),
                    );
                    for scope in rest_scopes {
                        expr = self.static_index(expr, scope);
                    }
                    self.static_index(expr, name)
                }
            },
            None => self.translate_scoped_global_value(name, scopes),
        }
    }

    fn optional_block(&self, value: Expression, identity: bool) -> Expression {
        Expression::new(ExpressionDesc::OptionalBlock(Box::new(value), identity))
    }

    fn can_inline_null_to_opt(&self, expr: &Expression) -> bool {
        matches!(
            expr.desc,
            ExpressionDesc::Var(_) | ExpressionDesc::Undefined { .. } | ExpressionDesc::Null
        )
    }

    fn null_to_opt_expr(&self, expr: Expression) -> Expression {
        if self.can_inline_null_to_opt(&expr) {
            Expression::cond(
                self.is_null_expr(expr.clone()),
                Expression::undefined(false),
                self.optional_block(expr, false),
            )
        } else {
            self.runtime_call_expr("Primitive_option", "fromNull", vec![expr])
        }
    }

    fn null_undefined_to_opt_expr(&self, expr: Expression) -> Expression {
        if self.can_inline_null_to_opt(&expr) {
            Expression::cond(
                self.is_null_or_undefined_expr(expr.clone()),
                Expression::undefined(false),
                self.optional_block(expr, false),
            )
        } else {
            self.runtime_call_expr("Primitive_option", "fromNullable", vec![expr])
        }
    }

    fn is_null_expr(&self, expr: Expression) -> Expression {
        Expression::bin(BinOp::EqEqEq, expr, Expression::null())
    }

    fn is_undefined_expr(&self, expr: Expression) -> Expression {
        Expression::bin(BinOp::EqEqEq, expr, Expression::undefined(false))
    }

    fn is_null_or_undefined_expr(&self, expr: Expression) -> Expression {
        Expression::is_null_or_undefined(expr)
    }

    fn some_expr(&self, value: Expression) -> Expression {
        let identity = matches!(
            value.desc,
            ExpressionDesc::Null
                | ExpressionDesc::Object(_, _)
                | ExpressionDesc::Number(_)
                | ExpressionDesc::CamlBlock(_, _, _, _)
                | ExpressionDesc::Array(_, _)
                | ExpressionDesc::Str { .. }
        );
        self.optional_block(value, identity)
    }

    fn val_from_option_expr(&self, arg: Expression) -> Expression {
        match arg.desc {
            ExpressionDesc::OptionalBlock(inner, _) => *inner,
            _ => self.runtime_call_expr("Primitive_option", "valFromOption", vec![arg]),
        }
    }

    fn is_not_none_expr(&self, arg: Expression) -> Expression {
        match arg.desc {
            ExpressionDesc::Undefined { .. } => Expression::bool(false),
            ExpressionDesc::OptionalBlock(_, _) => Expression::bool(true),
            _ => Expression::bin(BinOp::NotEqEq, arg, Expression::undefined(false)),
        }
    }

    fn external_arg_effect(&self, arg: &Expression) -> Option<Expression> {
        if expression_has_no_side_effects(arg) {
            None
        } else {
            Some(arg.clone())
        }
    }

    fn fuse_external_effects(&self, effects: Vec<Expression>) -> Option<Expression> {
        let mut effects = effects.into_iter();
        let first = effects.next()?;
        Some(effects.fold(first, js_seq))
    }

    fn add_external_effect(&self, effect: Option<Expression>, expr: Expression) -> Expression {
        match effect {
            Some(effect) => js_seq(effect, expr),
            None => expr,
        }
    }

    fn lower_object_external_arg_value_and_effect(
        &self,
        raw_arg: Expression,
        arg_label: ExternalArgLabel,
        arg_type: &ExternalArgAttr,
    ) -> (Expression, Option<Expression>) {
        let (values, effect) =
            self.lower_external_arg_values_and_effect(raw_arg, arg_label, arg_type);
        match values.as_slice() {
            [value] => (value.clone(), effect),
            [] => panic!("object field lowering expected one JS arg for {arg_type:?}"),
            _ => panic!(
                "object field lowering expected one JS arg, got {:?}",
                values
            ),
        }
    }

    fn lower_external_arg_values_and_effect(
        &self,
        raw_arg: Expression,
        arg_label: ExternalArgLabel,
        arg_type: &ExternalArgAttr,
    ) -> (Vec<Expression>, Option<Expression>) {
        let arg = match arg_label {
            ExternalArgLabel::Optional => self.external_optional_to_undefined_expr(raw_arg.clone()),
            ExternalArgLabel::Label | ExternalArgLabel::Empty => raw_arg.clone(),
        };

        match arg_type {
            ExternalArgAttr::ArgCst(_) => (Vec::new(), None),
            ExternalArgAttr::ExternUnit => {
                let effect = self.external_arg_effect(&arg);
                let values = if matches!(arg_label, ExternalArgLabel::Empty) {
                    Vec::new()
                } else {
                    vec![Expression::undefined(true)]
                };
                (values, effect)
            }
            ExternalArgAttr::Ignore => (Vec::new(), self.external_arg_effect(&arg)),
            ExternalArgAttr::PolyVarString { descr } => {
                (vec![self.external_polyvar_string_expr(arg, descr)], None)
            }
            ExternalArgAttr::PolyVar { descr } => (
                self.external_polyvar_event_exprs(arg, descr.as_deref()),
                None,
            ),
            ExternalArgAttr::Int(dispatches) => {
                (vec![self.external_polyvar_int_expr(arg, dispatches)], None)
            }
            ExternalArgAttr::Unwrap => {
                let value = match arg_label {
                    ExternalArgLabel::Optional => self.external_option_unwrap_expr(raw_arg),
                    ExternalArgLabel::Label | ExternalArgLabel::Empty => {
                        self.external_polyvar_unwrap_expr(arg)
                    }
                };
                (vec![value], None)
            }
            ExternalArgAttr::Nothing => (vec![arg], None),
        }
    }

    fn assemble_external_args_no_splice(
        &self,
        arg_types: &[ExternalArgSpec],
        args: Vec<Expression>,
    ) -> (Vec<Expression>, Option<Expression>) {
        let mut runtime_args = args.into_iter();
        let mut assembled = Vec::new();
        let mut effects = Vec::new();

        for arg_spec in arg_types {
            match &arg_spec.arg_type {
                ExternalArgAttr::ArgCst(cst) => {
                    assembled.push(self.compile_external_arg_const(cst));
                }
                _ => {
                    let arg = runtime_args
                        .next()
                        .unwrap_or_else(|| Expression::undefined(false));
                    let (values, effect) = self.lower_external_arg_values_and_effect(
                        arg,
                        arg_spec.arg_label,
                        &arg_spec.arg_type,
                    );
                    if let Some(effect) = effect {
                        effects.push(effect);
                    }
                    assembled.extend(values);
                }
            }
        }

        debug_assert!(runtime_args.next().is_none());
        (
            self.keep_non_undefined_external_args(arg_types, assembled),
            self.fuse_external_effects(effects),
        )
    }

    fn keep_non_undefined_external_args(
        &self,
        arg_types: &[ExternalArgSpec],
        mut args: Vec<Expression>,
    ) -> Vec<Expression> {
        let trailing_optional_undefined_count = arg_types
            .iter()
            .rev()
            .zip(args.iter().rev())
            .take_while(|(arg_spec, arg)| {
                matches!(arg_spec.arg_label, ExternalArgLabel::Optional)
                    && matches!(arg.desc, ExpressionDesc::Undefined { is_unit: false })
            })
            .count();

        if trailing_optional_undefined_count > 0 {
            args.truncate(args.len() - trailing_optional_undefined_count);
        }

        args
    }

    fn assemble_external_args_with_splice(
        &self,
        arg_types: &[ExternalArgSpec],
        args: Vec<Expression>,
    ) -> (Vec<Expression>, Option<Expression>) {
        let mut runtime_args = args.into_iter().peekable();
        let mut assembled = Vec::new();
        let mut needs_spread = false;
        let mut effects = Vec::new();

        for arg_spec in arg_types {
            match &arg_spec.arg_type {
                ExternalArgAttr::ArgCst(cst) => {
                    assembled.push(self.compile_external_arg_const(cst));
                }
                _ => {
                    let arg = runtime_args
                        .next()
                        .unwrap_or_else(|| Expression::undefined(false));
                    let is_last_runtime_arg = runtime_args.peek().is_none();

                    if is_last_runtime_arg {
                        match arg {
                            Expression {
                                desc: ExpressionDesc::Array(items, _),
                                ..
                            } => {
                                assembled.extend(items);
                            }
                            arg => {
                                needs_spread = true;
                                let (values, effect) = self.lower_external_arg_values_and_effect(
                                    arg,
                                    arg_spec.arg_label,
                                    &arg_spec.arg_type,
                                );
                                if let Some(effect) = effect {
                                    effects.push(effect);
                                }
                                assembled.extend(values);
                            }
                        }
                    } else {
                        let (values, effect) = self.lower_external_arg_values_and_effect(
                            arg,
                            arg_spec.arg_label,
                            &arg_spec.arg_type,
                        );
                        if let Some(effect) = effect {
                            effects.push(effect);
                        }
                        assembled.extend(values);
                    }
                }
            }
        }

        debug_assert!(runtime_args.next().is_none());

        if needs_spread {
            if let Some(last) = assembled.pop() {
                assembled.push(Expression::new(ExpressionDesc::Spread(Box::new(last))));
            }
        }

        (assembled, self.fuse_external_effects(effects))
    }

    fn assemble_external_args(
        &self,
        arg_types: &[ExternalArgSpec],
        args: Vec<Expression>,
        splice: bool,
    ) -> (Vec<Expression>, Option<Expression>) {
        if splice {
            self.assemble_external_args_with_splice(arg_types, args)
        } else {
            self.assemble_external_args_no_splice(arg_types, args)
        }
    }

    fn compile_js_object_create(
        &mut self,
        obj_params: &[ExternalObjSpec],
        args: Vec<Expression>,
        prelude: &mut Block,
    ) -> Expression {
        #[derive(Clone)]
        struct PendingOptionalAssignment {
            name: String,
            arg: Expression,
            arg_type: ExternalArgAttr,
            for_sure_no_nested_option: bool,
        }

        let mut runtime_args = args.into_iter();
        let mut props = Vec::new();
        let mut effects = Vec::new();
        let mut optional_assignments: Vec<PendingOptionalAssignment> = Vec::new();

        for obj_param in obj_params {
            match &obj_param.obj_arg_label {
                ExternalObjLabel::Empty => {
                    if !matches!(obj_param.obj_arg_type, ExternalArgAttr::ArgCst(_)) {
                        let arg = runtime_args
                            .next()
                            .unwrap_or_else(|| Expression::undefined(false));
                        if let Some(effect) = self.external_arg_effect(&arg) {
                            effects.push(effect);
                        }
                    }
                }
                ExternalObjLabel::Label { name } => match &obj_param.obj_arg_type {
                    ExternalArgAttr::ArgCst(cst) => {
                        props.push((
                            PropertyName::lit(name.clone()),
                            self.compile_external_arg_const(cst),
                        ));
                    }
                    _ => {
                        let arg = runtime_args
                            .next()
                            .unwrap_or_else(|| Expression::undefined(false));
                        let (value, effect) = self.lower_object_external_arg_value_and_effect(
                            arg,
                            ExternalArgLabel::Label,
                            &obj_param.obj_arg_type,
                        );
                        if let Some(effect) = effect {
                            effects.push(effect);
                        }
                        props.push((PropertyName::lit(name.clone()), value));
                    }
                },
                ExternalObjLabel::Optional {
                    name,
                    for_sure_no_nested_option,
                } => {
                    let arg = runtime_args
                        .next()
                        .unwrap_or_else(|| Expression::undefined(false));

                    match arg.desc {
                        ExpressionDesc::Undefined { .. } => continue,
                        // Match OCaml's Js_of_lam_option.destruct_optional:
                        // statically-known `Some x` goes straight into the
                        // object literal, while unknown option values keep the
                        // temp-object plus conditional assignment path.
                        ExpressionDesc::OptionalBlock(inner, _) => {
                            let (value, effect) = self.lower_object_external_arg_value_and_effect(
                                *inner,
                                ExternalArgLabel::Label,
                                &obj_param.obj_arg_type,
                            );
                            if let Some(effect) = effect {
                                effects.push(effect);
                            }
                            props.push((PropertyName::lit(name.clone()), value));
                        }
                        other => {
                            optional_assignments.push(PendingOptionalAssignment {
                                name: name.clone(),
                                arg: Expression::new(other),
                                arg_type: obj_param.obj_arg_type.clone(),
                                for_sure_no_nested_option: *for_sure_no_nested_option,
                            });
                        }
                    }
                }
            }
        }

        debug_assert!(runtime_args.next().is_none());

        let object = self.add_external_effect(
            self.fuse_external_effects(effects),
            Expression::new(ExpressionDesc::Object(None, props)),
        );

        if optional_assignments.is_empty() {
            return object;
        }

        let obj = self.fresh_tmp_ident();
        prelude.push(Statement::variable(VariableDeclaration {
            ident: obj.clone(),
            value: Some(object),
            property: LetKind::Variable,
            ident_info: IdentInfo::default(),
        }));

        for pending in optional_assignments {
            let prepared = if self.expr_is_simple(&pending.arg) {
                pending.arg
            } else {
                let tmp = self.fresh_tmp_ident();
                prelude.push(Statement::variable(VariableDeclaration {
                    ident: tmp.clone(),
                    value: Some(pending.arg),
                    property: LetKind::Strict,
                    ident_info: IdentInfo::default(),
                }));
                Expression::var(tmp)
            };

            let value_arg = if pending.for_sure_no_nested_option {
                prepared.clone()
            } else {
                self.val_from_option_expr(prepared.clone())
            };
            let (value, effect) = self.lower_object_external_arg_value_and_effect(
                value_arg,
                ExternalArgLabel::Empty,
                &pending.arg_type,
            );
            let cond = Expression::bin(BinOp::NotEqEq, prepared, Expression::undefined(false));
            let assign = Expression::bin(
                BinOp::Eq,
                self.static_index(Expression::var(obj.clone()), &pending.name),
                self.add_external_effect(effect, value),
            );
            prelude.push(Statement::if_(cond, vec![Statement::exp(assign)], vec![]));
        }

        Expression::var(obj)
    }

    fn expr_is_simple(&self, expr: &Expression) -> bool {
        matches!(
            expr.desc,
            ExpressionDesc::Var(_)
                | ExpressionDesc::Undefined { .. }
                | ExpressionDesc::Null
                | ExpressionDesc::Bool(_)
                | ExpressionDesc::Number(_)
                | ExpressionDesc::Str { .. }
        )
    }

    fn compile_js_call(
        &mut self,
        prim_name: &str,
        arg_types: &[ExternalArgSpec],
        ffi: &crate::lambda::primitive::ExternalFfiSpec,
        dynamic_import: bool,
        transformed_jsx: bool,
        args: Vec<Expression>,
        _prelude: &mut Block,
    ) -> Expression {
        let transformed_jsx_call_info = CallInfo {
            call_transformed_jsx: transformed_jsx,
            ..CallInfo::default()
        };

        match ffi.spec.as_ref() {
            Some(ExternalSpec::JsVar {
                name,
                external_module_name,
                scopes,
            }) => {
                let value = self.translate_scoped_module_value(
                    external_module_name.as_ref(),
                    name,
                    scopes,
                    dynamic_import,
                );
                if args.is_empty() {
                    value
                } else {
                    Expression::call(value, args, transformed_jsx_call_info.clone())
                }
            }
            Some(ExternalSpec::JsCall {
                name,
                external_module_name,
                splice,
                scopes,
                tagged_template,
            }) => {
                let target = self.translate_scoped_module_value(
                    external_module_name.as_ref(),
                    name,
                    scopes,
                    dynamic_import,
                );

                if *tagged_template {
                    match args.as_slice() {
                        [
                            Expression {
                                desc: ExpressionDesc::Array(strings, _),
                                ..
                            },
                            Expression {
                                desc: ExpressionDesc::Array(values, _),
                                ..
                            },
                        ] => {
                            return Expression::new(ExpressionDesc::TaggedTemplate(
                                Box::new(target),
                                strings.clone(),
                                values.clone(),
                            ));
                        }
                        _ => {}
                    }
                }

                let (args, effect) = self.assemble_external_args(arg_types, args, *splice);
                self.add_external_effect(
                    effect,
                    Expression::call(target, args, transformed_jsx_call_info.clone()),
                )
            }
            Some(ExternalSpec::JsNew {
                name,
                external_module_name,
                splice,
                scopes,
                ..
            }) => {
                let (args, effect) = self.assemble_external_args(arg_types, args, *splice);
                let target = self.translate_scoped_module_value(
                    external_module_name.as_ref(),
                    name,
                    scopes,
                    dynamic_import,
                );
                let expr = Expression::new(ExpressionDesc::New(Box::new(target), Some(args)));
                self.add_external_effect(effect, expr)
            }
            Some(ExternalSpec::JsSend {
                name,
                splice,
                js_send_scopes,
                ..
            }) => match args.split_first() {
                Some((receiver, rest)) => {
                    let (rest_args, effect) = self.assemble_external_args(
                        arg_types.get(1..).unwrap_or(&[]),
                        rest.to_vec(),
                        *splice,
                    );
                    self.add_external_effect(
                        effect,
                        Expression::call(
                            self.static_index(
                                self.apply_scoped_access(receiver.clone(), js_send_scopes),
                                name,
                            ),
                            rest_args,
                            transformed_jsx_call_info.clone(),
                        ),
                    )
                }
                None => self.compile_plain_js_call(prim_name, args, transformed_jsx),
            },
            Some(ExternalSpec::JsGet {
                js_get_name,
                js_get_scopes,
            }) => {
                let (assembled, effect) = self.assemble_external_args_no_splice(arg_types, args);
                let expr = match assembled.as_slice() {
                    [receiver] => self.static_index(
                        self.apply_scoped_access(receiver.clone(), js_get_scopes),
                        js_get_name,
                    ),
                    _ => self.compile_plain_js_call(prim_name, assembled, transformed_jsx),
                };
                self.add_external_effect(effect, expr)
            }
            Some(ExternalSpec::JsSet {
                js_set_name,
                js_set_scopes,
            }) => {
                let (assembled, effect) = self.assemble_external_args_no_splice(arg_types, args);
                let expr = match assembled.as_slice() {
                    [receiver, value] => Expression::bin(
                        BinOp::Eq,
                        self.static_index(
                            self.apply_scoped_access(receiver.clone(), js_set_scopes),
                            js_set_name,
                        ),
                        value.clone(),
                    ),
                    _ => self.compile_plain_js_call(prim_name, assembled, transformed_jsx),
                };
                self.add_external_effect(effect, expr)
            }
            Some(ExternalSpec::JsGetIndex {
                js_get_index_scopes,
            }) => {
                let (assembled, effect) = self.assemble_external_args_no_splice(arg_types, args);
                let expr = match assembled.as_slice() {
                    [receiver, index] => Expression::new(ExpressionDesc::ArrayIndex(
                        Box::new(self.apply_scoped_access(receiver.clone(), js_get_index_scopes)),
                        Box::new(index.clone()),
                    )),
                    _ => self.compile_plain_js_call(prim_name, assembled, transformed_jsx),
                };
                self.add_external_effect(effect, expr)
            }
            Some(ExternalSpec::JsSetIndex {
                js_set_index_scopes,
            }) => {
                let (assembled, effect) = self.assemble_external_args_no_splice(arg_types, args);
                let expr = match assembled.as_slice() {
                    [receiver, index, value] => Expression::bin(
                        BinOp::Eq,
                        Expression::new(ExpressionDesc::ArrayIndex(
                            Box::new(
                                self.apply_scoped_access(receiver.clone(), js_set_index_scopes),
                            ),
                            Box::new(index.clone()),
                        )),
                        value.clone(),
                    ),
                    _ => self.compile_plain_js_call(prim_name, assembled, transformed_jsx),
                };
                self.add_external_effect(effect, expr)
            }
            Some(ExternalSpec::JsModuleAsVar(module_name)) => {
                let value = self.external_module_binding(module_name, false, dynamic_import);
                let (args, effect) = self.assemble_external_args_no_splice(arg_types, args);
                let expr = if args.is_empty() {
                    value
                } else {
                    Expression::call(value, args, transformed_jsx_call_info.clone())
                };
                self.add_external_effect(effect, expr)
            }
            Some(ExternalSpec::JsModuleAsFn {
                external_module_name,
                splice,
            }) => {
                let (args, effect) = self.assemble_external_args(arg_types, args, *splice);
                let target =
                    self.external_module_binding(external_module_name, false, dynamic_import);
                let expr = Expression::call(target, args, transformed_jsx_call_info.clone());
                self.add_external_effect(effect, expr)
            }
            Some(ExternalSpec::JsModuleAsClass(module_name)) => {
                let (args, effect) = self.assemble_external_args_no_splice(arg_types, args);
                let target = self.external_module_binding(module_name, false, dynamic_import);
                let expr = Expression::new(ExpressionDesc::New(Box::new(target), Some(args)));
                self.add_external_effect(effect, expr)
            }
            _ => self.compile_plain_js_call(prim_name, args, transformed_jsx),
        }
    }

    fn compile_plain_js_call(
        &self,
        prim_name: &str,
        args: Vec<Expression>,
        transformed_jsx: bool,
    ) -> Expression {
        Expression::call(
            Expression::var(Ident::create_persistent(prim_name)),
            args,
            CallInfo {
                call_transformed_jsx: transformed_jsx,
                ..CallInfo::default()
            },
        )
    }

    fn compile_import(&self, args: Vec<Expression>) -> Expression {
        let arg = match args.as_slice() {
            [arg] => arg,
            [
                arg,
                Expression {
                    desc: ExpressionDesc::Undefined { is_unit: true },
                    ..
                },
            ] => arg,
            _ => {
                return Expression::call(
                    Expression::var(Ident::create_persistent("import")),
                    args,
                    CallInfo::default(),
                );
            }
        };

        let Some((module, member)) = self.module_of_expression(arg) else {
            return Expression::call(
                Expression::var(Ident::create_persistent("import")),
                args,
                CallInfo::default(),
            );
        };

        let path = match &module.kind {
            Kind::External { name, .. } => Some(name.clone()),
            _ => self
                .module_path_resolver
                .as_ref()
                .and_then(|resolver| resolver.resolve_module_path(&module)),
        };

        let Some(path) = path else {
            return Expression::call(
                Expression::var(Ident::create_persistent("import")),
                args,
                CallInfo::default(),
            );
        };

        let import_expr = Expression::call(
            Expression::var(Ident::create_persistent("import")),
            vec![Expression::string(path)],
            CallInfo::default(),
        );

        let member = member.or_else(|| match &module.kind {
            Kind::External { default: true, .. } => Some("default".to_string()),
            _ => None,
        });

        match member {
            Some(member) => {
                let param = self.fresh_ident("m");
                let body = vec![Statement::return_(
                    self.static_index(Expression::var(param.clone()), &member),
                )];
                let callback = Expression::new(ExpressionDesc::Fun {
                    is_method: false,
                    params: vec![param],
                    body,
                    env: Default::default(),
                    return_unit: false,
                    async_: false,
                    directive: None,
                });
                Expression::call(
                    self.static_index(import_expr, "then"),
                    vec![callback],
                    CallInfo::default(),
                )
            }
            None => import_expr,
        }
    }

    fn module_of_expression(&self, expr: &Expression) -> Option<(ModuleId, Option<String>)> {
        match &expr.desc {
            ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(module, member)) => {
                Some((module.clone(), member.clone()))
            }
            ExpressionDesc::StaticIndex(target, field, _) => match &target.desc {
                ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(module, None)) => {
                    Some((module.clone(), Some(field.clone())))
                }
                _ => None,
            },
            ExpressionDesc::Call(func, _, _) => match &func.desc {
                ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(module, member)) => {
                    Some((module.clone(), member.clone()))
                }
                _ => None,
            },
            _ => None,
        }
    }

    fn translate_scoped_global_value(&self, name: &str, scopes: &[String]) -> Expression {
        let mut expr = match scopes.split_first() {
            Some((head, rest)) => {
                let mut expr = Expression::var(Ident::create_persistent(head));
                for scope in rest {
                    expr = self.static_index(expr, scope);
                }
                expr
            }
            None => Expression::var(Ident::create_persistent(name)),
        };
        if !scopes.is_empty() {
            expr = self.static_index(expr, name);
        }
        expr
    }

    fn apply_scoped_access(&self, mut expr: Expression, scopes: &[String]) -> Expression {
        for scope in scopes {
            expr = self.static_index(expr, scope);
        }
        expr
    }

    fn static_index(&self, target: Expression, field: &str) -> Expression {
        Expression::new(ExpressionDesc::StaticIndex(
            Box::new(target),
            field.to_string(),
            None,
        ))
    }

    fn fresh_ident(&self, prefix: &str) -> Ident {
        self.id_gen.create(prefix)
    }

    fn fresh_tmp_ident(&self) -> Ident {
        self.fresh_ident("tmp")
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

        let subst = subst::make_subst(&handler.bindings, args);
        Some(subst::subst(&subst, &handler.handler))
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
                    && args.iter().all(analysis::no_side_effects)
            }
            Lambda::Llet(kind, _, value, body)
                if matches!(kind, LetKind::Alias | LetKind::Strict | LetKind::StrictOpt)
                    && analysis::no_side_effects(value)
                    && !self.lambda_requires_explicit_staticcatch_jump(value) =>
            {
                self.handler_is_pure_outward_static_raise_forwarder(body)
            }
            Lambda::Lsequence(first, second)
                if analysis::no_side_effects(first)
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
            Lambda::Lvar(_) | Lambda::LglobalModule(_, _) | Lambda::Lconst(_) => false,
            Lambda::LifThenElse(_, _, _)
            | Lambda::Lswitch(_, _)
            | Lambda::LstringSwitch(_, _, _)
            | Lambda::Llet(_, _, _, _)
            | Lambda::Lsequence(_, _)
                if lambda_contains_static_raise(lam)
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
            Lambda::Lprim(info) => info.args.iter().any(|arg| {
                self.return_handler_requires_explicit_staticcatch_jump(arg)
            }),
            Lambda::Lswitch(scrut, switch) => {
                self.return_handler_requires_explicit_staticcatch_jump(scrut)
                    || switch
                        .sw_consts
                        .iter()
                        .any(|(_, body)| self.return_handler_requires_explicit_staticcatch_jump(body))
                    || switch
                        .sw_blocks
                        .iter()
                        .any(|(_, body)| self.return_handler_requires_explicit_staticcatch_jump(body))
                    || switch.sw_failaction.as_deref().is_some_and(|body| {
                        self.return_handler_requires_explicit_staticcatch_jump(body)
                    })
            }
            Lambda::LstringSwitch(scrut, cases, default) => {
                self.return_handler_requires_explicit_staticcatch_jump(scrut)
                    || cases
                        .iter()
                        .any(|(_, body)| self.return_handler_requires_explicit_staticcatch_jump(body))
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
                    || self.return_staticcatch_requires_explicit_jump(
                        *label, bindings, body, handler,
                    )
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
            Lambda::Lassign(_, value) => self.return_handler_requires_explicit_staticcatch_jump(value),
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
                let args_are_pure = args.iter().all(analysis::no_side_effects);
                if self.active_static_raise_target_exists(*label, args.len()) && args_are_pure {
                    Some(false)
                } else {
                    None
                }
            }
            Lambda::Llet(kind, _, value, body)
                if matches!(kind, LetKind::Alias | LetKind::Strict | LetKind::StrictOpt)
                    && analysis::no_side_effects(value) =>
            {
                self.pure_return_static_raise_dispatch_has_terminal_value(body)
            }
            Lambda::Lsequence(first, second) if analysis::no_side_effects(first) => {
                self.pure_return_static_raise_dispatch_has_terminal_value(second)
            }
            Lambda::LifThenElse(cond, then_, else_) if analysis::no_side_effects(cond) => {
                let then_has_value =
                    self.pure_return_static_raise_dispatch_has_terminal_value(then_)?;
                let else_has_value =
                    self.pure_return_static_raise_dispatch_has_terminal_value(else_)?;
                Some(then_has_value || else_has_value)
            }
            Lambda::Lswitch(scrut, switch) if analysis::no_side_effects(scrut) => {
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
            Lambda::LstringSwitch(scrut, cases, default) if analysis::no_side_effects(scrut) => {
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
            _ if analysis::no_side_effects(lam) => Some(true),
            _ => None,
        }
    }

    fn lambda_requires_explicit_staticcatch_jump(&self, lam: &Lambda) -> bool {
        match lam {
            Lambda::Lvar(_) | Lambda::LglobalModule(_, _) | Lambda::Lconst(_) => false,
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
        let result = self.fresh_ident("catch");
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
    fn emit_multi_staticcatch_prelude(
        &mut self,
        handlers: &[FlatHandler],
    ) -> (Ident, i32, Block) {
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

    /// Emit the `compile_cases ~cxt ~switch_exp:exit_expr handlers` call at
    /// lam_compile.ml:987/996/1010/1017. For a single handler + NonComplete
    /// default this reduces to `if (exit === code) { handler_block }`
    /// (compile_general_cases lam_compile.ml:551-557). For multiple handlers
    /// it becomes an `int_switch` (lam_compile.ml:567-630).
    fn compile_exit_dispatch(
        &self,
        exit_id: &Ident,
        first_code: i32,
        handler_blocks: Vec<Block>,
        handler_lambdas: &[&Lambda],
        is_return_context: bool,
    ) -> Option<Statement> {
        if handler_blocks.is_empty() {
            return None;
        }
        if handler_blocks.len() == 1 {
            let handler_block = handler_blocks.into_iter().next().unwrap();
            if handler_block.is_empty() {
                return None;
            }
            return Some(Statement::if_(
                self.staticcatch_exit_test(exit_id, first_code),
                handler_block,
                vec![],
            ));
        }
        // Multi-handler: emit an Int_switch. Per OCaml's `compile_general_cases`
        // (lam_compile.ml:607-624), every per-group last clause computes
        // `should_break` from `Js_output.to_break_block` (~ `!block_terminates`)
        // and, when the surrounding continuation `continuation_is_return`
        // (lam_compile_context.ml:68-72), additionally ANDs with
        // `Lam_exit_code.has_exit lam`. In `compile_exit_dispatch` each handler
        // is its own group, so the same per-clause logic applies uniformly —
        // including the trailing case (mario_game's `process_collision` case 3).
        debug_assert_eq!(handler_blocks.len(), handler_lambdas.len());
        let clauses: Vec<(i32, CaseClause)> = handler_blocks
            .into_iter()
            .zip(handler_lambdas.iter())
            .enumerate()
            .map(|(i, (body, handler_lam))| {
                let should_break = if block_terminates(&body) {
                    false
                } else if is_return_context {
                    has_exit_code(handler_lam, |_| true)
                } else {
                    true
                };
                (
                    first_code + i32::try_from(i).expect("exit handler index fits in i32"),
                    CaseClause {
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
        let handler_blocks: Vec<Block> = if block_terminates(&body_block) {
            Vec::new()
        } else {
            handlers
                .iter()
                .map(|h| self.compile_return_block(&h.handler))
                .collect()
        };
        self.pop_multi_staticcatch_handlers(handlers.len());
        block.extend(body_block);
        if !block_terminates(&block) {
            let handler_lambdas: Vec<&Lambda> = handlers.iter().map(|h| &h.handler).collect();
            if let Some(dispatch) = self.compile_exit_dispatch(
                &exit_id,
                first_code,
                handler_blocks,
                &handler_lambdas,
                true,
            ) {
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
        let handler_blocks: Vec<Block> = if block_terminates(&body_block) {
            Vec::new()
        } else {
            handlers
                .iter()
                .map(|h| self.compile_effect_block(&h.handler))
                .collect()
        };
        self.pop_multi_staticcatch_handlers(handlers.len());
        block.extend(body_block);
        if !block_terminates(&block) {
            let handler_lambdas: Vec<&Lambda> = handlers.iter().map(|h| &h.handler).collect();
            if let Some(dispatch) = self.compile_exit_dispatch(
                &exit_id,
                first_code,
                handler_blocks,
                &handler_lambdas,
                false,
            ) {
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
        let handler_blocks: Vec<Block> = if block_terminates(&body_block) {
            Vec::new()
        } else {
            handlers
                .iter()
                .map(|h| self.compile_assign_to_target_block(result, &h.handler))
                .collect()
        };
        self.pop_multi_staticcatch_handlers(handlers.len());
        block.extend(body_block);
        if !block_terminates(&block) {
            let handler_lambdas: Vec<&Lambda> = handlers.iter().map(|h| &h.handler).collect();
            if let Some(dispatch) = self.compile_exit_dispatch(
                &exit_id,
                first_code,
                handler_blocks,
                &handler_lambdas,
                false,
            ) {
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
        let handler_blocks: Vec<Block> = if block_terminates(&body_block) {
            Vec::new()
        } else {
            handlers
                .iter()
                .map(|h| self.compile_tail_loop_return_block(&h.handler, tail_loop))
                .collect()
        };
        self.pop_multi_staticcatch_handlers(handlers.len());
        block.extend(body_block);
        if !block_terminates(&block) {
            let handler_lambdas: Vec<&Lambda> = handlers.iter().map(|h| &h.handler).collect();
            if let Some(dispatch) = self.compile_exit_dispatch(
                &exit_id,
                first_code,
                handler_blocks,
                &handler_lambdas,
                true,
            ) {
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
        Lambda::Lassign(_, _) => "assign",
        Lambda::LglobalModule(_, _) => "global_module",
    }
}

fn recursive_function_binding_value(expr: &Lambda) -> Option<LFunction> {
    match expr {
        Lambda::Lfunction(func) => Some(func.clone()),
        Lambda::Lprim(info) => match (&info.primitive, info.args.as_slice()) {
            (Primitive::PjsFnMake(arity), [Lambda::Lfunction(func)]) => Some(
                adjust_recursive_js_fn_make_function(func, *arity, &info.loc),
            ),
            (Primitive::PjsFnMakeUnit, [Lambda::Lfunction(func)]) => {
                let mut func = func.clone();
                if func.arity == 1
                    && matches!(func.params.as_slice(), [param] if param.name() == "param")
                {
                    func.attr.one_unit_arg = true;
                }
                Some(func)
            }
            _ => None,
        },
        _ => None,
    }
}

fn recursive_binding_dependencies(bindings: &[(Ident, Lambda)]) -> Vec<Vec<usize>> {
    let index_by_id = bindings
        .iter()
        .enumerate()
        .map(|(index, (id, _))| (id.clone(), index))
        .collect::<HashMap<_, _>>();

    bindings
        .iter()
        .map(|(_, expr)| {
            let mut dependencies = free_variables(expr)
                .into_iter()
                .filter_map(|id| index_by_id.get(&id).copied())
                .collect::<Vec<_>>();
            dependencies.sort_unstable();
            dependencies.dedup();
            dependencies
        })
        .collect()
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

fn recursive_binding_group_is_function_only(bindings: &[(Ident, Lambda)], group: &[usize]) -> bool {
    group
        .iter()
        .all(|&index| matches!(bindings[index].1, Lambda::Lfunction(_)))
}

fn sort_recursive_binding_group(bindings: &[(Ident, Lambda)], group: &mut [usize]) {
    if recursive_binding_group_is_function_only(bindings, group) {
        return;
    }
    group.sort_by_key(|index| !matches!(bindings[*index].1, Lambda::Lfunction(_)));
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
        Lambda::Lprim(info) => match (&info.primitive, info.args.as_slice()) {
            (Primitive::PjsFnMake(arity), [Lambda::Lvar(target)]) => {
                let (function_id, func) = lookup(target)?;
                if func.attr.async_ || func.arity == *arity {
                    Some(function_id.clone())
                } else {
                    None
                }
            }
            (Primitive::PjsFnMakeUnit, [Lambda::Lvar(target)]) => {
                lookup(target).map(|(function_id, _)| function_id.clone())
            }
            _ => None,
        },
        _ => None,
    }
}

fn adjust_recursive_js_fn_make_function(func: &LFunction, to_: i32, loc: &Location) -> LFunction {
    let from = func.arity;
    if from == to_ || func.attr.async_ {
        return func.clone();
    }

    if to_ == 0 {
        let [param] = func.params.as_slice() else {
            unreachable!("direct recursive js fn make adjustment should preserve a body")
        };
        let Lambda::Lfunction(adjusted) = Lambda::function_(
            0,
            vec![],
            Lambda::let_(
                LetKind::Alias,
                param.clone(),
                Lambda::unit(),
                (*func.body).clone(),
            ),
            FunctionAttribute::default(),
        ) else {
            unreachable!("function constructor must return an Lfunction")
        };
        return adjusted;
    }

    if to_ > from {
        let mut params = func.params.clone();
        let extra_args = (0..(to_ - from))
            .map(|_| Ident::create_local("param"))
            .collect::<Vec<_>>();
        let mut body = (*func.body).clone();
        for extra_arg in &extra_args {
            body = Lambda::Lapply(Apply {
                ap_func: Box::new(body),
                ap_args: vec![Lambda::var(extra_arg.clone())],
                ap_info: ApInfo {
                    loc: loc.clone(),
                    inlined: InlineAttribute::Default,
                    status: ApplyStatus::Na,
                },
                ap_transformed_jsx: false,
            });
        }
        params.extend(extra_args);
        let Lambda::Lfunction(adjusted) =
            Lambda::function_(to_, params, body, FunctionAttribute::default())
        else {
            unreachable!("function constructor must return an Lfunction")
        };
        return adjusted;
    }

    let outer_arity = to_ as usize;
    let outer_params = func.params[..outer_arity].to_vec();
    let inner_params = func.params[outer_arity..].to_vec();
    let inner = Lambda::function_(
        from - to_,
        inner_params,
        (*func.body).clone(),
        FunctionAttribute::default(),
    );
    let Lambda::Lfunction(adjusted) =
        Lambda::function_(to_, outer_params, inner, FunctionAttribute::default())
    else {
        unreachable!("function constructor must return an Lfunction")
    };
    adjusted
}

fn lower_ocaml_for_range_direction<'a>(
    direction: &crate::lambda::DirectionFlag,
    finish: &'a Lambda,
) -> (&'a Lambda, ForDirection) {
    match (direction, finish) {
        (
            crate::lambda::DirectionFlag::Upto,
            Lambda::Lprim(crate::lambda::PrimInfo {
                primitive: Primitive::Psubint,
                args,
                ..
            }),
        ) => match args.as_slice() {
            [new_finish, Lambda::Lconst(Constant::Int { i: 1, .. })] => {
                (new_finish, ForDirection::Up)
            }
            _ => (finish, ForDirection::Upto),
        },
        (
            crate::lambda::DirectionFlag::Upto,
            Lambda::Lprim(crate::lambda::PrimInfo {
                primitive: Primitive::Poffsetint(-1),
                args,
                ..
            }),
        ) => match args.as_slice() {
            [new_finish] => (new_finish, ForDirection::Up),
            _ => (finish, ForDirection::Upto),
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

fn trailing_return_expression(block: &[Statement]) -> Option<&Expression> {
    let stmt = block.last()?;
    let StatementDesc::Return(expr) = &stmt.desc else {
        return None;
    };
    Some(expr)
}

fn function_has_self_tailcall(tail_targets: &[Ident], lam: &Lambda) -> bool {
    match lam {
        Lambda::Lapply(Apply { ap_func, .. }) => {
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
        Lambda::LtryWith(_, _, _) => false,
        Lambda::Lvar(_)
        | Lambda::LglobalModule(_, _)
        | Lambda::Lconst(_)
        | Lambda::Lfunction(_)
        | Lambda::Lletrec(_, _)
        | Lambda::LstaticRaise(_, _)
        | Lambda::Lwhile(_, _)
        | Lambda::Lfor(_, _, _, _, _)
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

fn collect_possible_required_modules(lam: &Lambda) -> std::collections::HashSet<ModuleId> {
    let mut seen = std::collections::HashSet::new();
    collect_modules_from_lambda(lam, &mut seen);
    seen
}

fn collect_modules_from_lambda(lam: &Lambda, seen: &mut std::collections::HashSet<ModuleId>) {
    match lam {
        Lambda::Lvar(_) | Lambda::Lconst(_) => {}
        Lambda::LglobalModule(id, dynamic_import) => {
            if !*dynamic_import {
                seen.insert(ModuleId {
                    id: id.clone(),
                    kind: Kind::Ml,
                    dynamic_import: false,
                });
            }
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
        Lambda::Lassign(_, value) => collect_modules_from_lambda(value, seen),
    }
}

fn populate_required_modules(
    module_path_resolver: Option<&ModulePathResolver>,
    extras: &std::collections::HashSet<ModuleId>,
    modules: &mut OcamlModuleSet,
) {
    for module in extras {
        if !module.dynamic_import
            && required_module_side_effect_reason(
                module_path_resolver,
                std::slice::from_ref(module),
            )
            .is_some()
        {
            modules.insert(module.clone());
        }
    }
}

#[derive(Debug, Clone)]
enum TopLevelEffectGroup {
    Single(LetKind, Ident, Lambda),
    Recursive(Vec<(Ident, Lambda)>),
    Nop(Lambda),
}

fn top_level_effect_group_single(kind: LetKind, ident: Ident, body: Lambda) -> TopLevelEffectGroup {
    match (kind, &body) {
        (LetKind::Strict | LetKind::StrictOpt, Lambda::Lvar(_) | Lambda::Lconst(_)) => {
            TopLevelEffectGroup::Single(LetKind::Alias, ident, body)
        }
        _ => TopLevelEffectGroup::Single(kind, ident, body),
    }
}

fn push_top_level_effect_nop(lam: Lambda, groups: &mut Vec<TopLevelEffectGroup>) {
    if !matches!(
        lam,
        Lambda::Lvar(_) | Lambda::Lconst(_) | Lambda::Lfunction(_)
    ) {
        groups.push(TopLevelEffectGroup::Nop(lam));
    }
}

fn flatten_top_level_effect_groups(
    acc: Vec<TopLevelEffectGroup>,
    lam: &Lambda,
) -> (Lambda, Vec<TopLevelEffectGroup>) {
    match lam {
        Lambda::Llet(kind, id, value, body) => {
            let (result, groups) = flatten_top_level_effect_groups(acc, value);
            let mut next = Vec::with_capacity(groups.len() + 1);
            next.push(top_level_effect_group_single(*kind, id.clone(), result));
            next.extend(groups);
            flatten_top_level_effect_groups(next, body)
        }
        Lambda::Lletrec(bindings, body) => {
            let mut next = Vec::with_capacity(acc.len() + 1);
            next.push(TopLevelEffectGroup::Recursive(bindings.clone()));
            next.extend(acc);
            flatten_top_level_effect_groups(next, body)
        }
        Lambda::Lsequence(first, second) => {
            let (result, groups) = flatten_top_level_effect_groups(acc, first);
            let mut next = Vec::with_capacity(groups.len() + 1);
            push_top_level_effect_nop(result, &mut next);
            next.extend(groups);
            flatten_top_level_effect_groups(next, second)
        }
        _ => (lam.clone(), acc),
    }
}

fn module_side_effect_reason(lam: &Lambda) -> Option<String> {
    let (result, groups) = flatten_top_level_effect_groups(Vec::new(), lam);
    groups
        .into_iter()
        .rev()
        .find_map(|group| match group {
            TopLevelEffectGroup::Single(kind, id, body) => {
                (matches!(kind, LetKind::Strict | LetKind::Variable)
                    && !analysis::no_side_effects(&body))
                .then(|| id.name().to_string())
            }
            TopLevelEffectGroup::Recursive(bindings) => {
                bindings.into_iter().find_map(|(id, body)| {
                    (!analysis::no_side_effects(&body)).then(|| id.name().to_string())
                })
            }
            TopLevelEffectGroup::Nop(body) => (!analysis::no_side_effects(&body)).then(String::new),
        })
        .or_else(|| (!analysis::no_side_effects(&result)).then(String::new))
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

fn external_module_import_attributes(
    module_name: &ExternalModuleName,
) -> Option<JsImportAttributes> {
    let entries = module_name.import_attributes.clone()?;
    Some(JsImportAttributes { entries })
}

fn external_module_ident_name(module_name: &ExternalModuleName) -> String {
    match &module_name.module_bind_name {
        ExternalModuleBindName::HintName(hint) => capitalize_ascii_first(hint),
        ExternalModuleBindName::Nothing => js_id_name_of_hint_name(&module_name.bundle),
    }
}

fn capitalize_ascii_first(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        None => String::new(),
        Some(first) => {
            let mut out = String::new();
            out.push(first.to_ascii_uppercase());
            out.push_str(chars.as_str());
            out
        }
    }
}

fn good_hint_name(module_name: &str, offset: usize) -> bool {
    let bytes = module_name.as_bytes();
    offset < bytes.len()
        && bytes[offset].is_ascii_alphabetic()
        && bytes[offset + 1..]
            .iter()
            .all(|byte| byte.is_ascii_alphanumeric() || *byte == b'_')
}

fn collect_start(buf: &mut String, s: &[u8], mut offset: usize) {
    while offset < s.len() {
        match s[offset] {
            b'a'..=b'z' => {
                buf.push((s[offset] as char).to_ascii_uppercase());
                collect_next(buf, s, offset + 1);
                return;
            }
            b'A'..=b'Z' => {
                buf.push(s[offset] as char);
                collect_next(buf, s, offset + 1);
                return;
            }
            _ => offset += 1,
        }
    }
}

fn collect_next(buf: &mut String, s: &[u8], mut offset: usize) {
    while offset < s.len() {
        match s[offset] {
            b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' | b'_' => {
                buf.push(s[offset] as char);
                offset += 1;
            }
            b'.' | b'-' => {
                collect_start(buf, s, offset + 1);
                return;
            }
            _ => offset += 1,
        }
    }
}

fn js_id_name_of_hint_name(module_name: &str) -> String {
    let offset = module_name.rfind('/').map_or(0, |index| index + 1);
    if good_hint_name(module_name, offset) {
        capitalize_ascii_first(&module_name[offset..])
    } else {
        let bytes = module_name.as_bytes();
        let mut buf = String::new();
        collect_start(&mut buf, bytes, offset);
        if buf.is_empty() {
            if offset == 0 {
                module_name.to_string()
            } else {
                capitalize_ascii_first(module_name)
            }
        } else {
            buf
        }
    }
}


fn compiled_from_effect_block(mut block: Block) -> Compiled {
    if block.len() == 1 {
        let stmt = block.pop().expect("single-item block");
        let Statement { desc, comment } = stmt;
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
                prelude: vec![Statement { desc, comment }],
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
        Lambda::Lvar(_) | Lambda::LglobalModule(_, _) | Lambda::Lconst(_) => false,
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
        Lambda::Lassign(_, value) => lambda_contains_static_raise(value),
        Lambda::LifThenElse(cond, then_, else_) => {
            lambda_contains_static_raise(cond)
                || lambda_contains_static_raise(then_)
                || lambda_contains_static_raise(else_)
        }
    }
}

fn lambda_has_exit(lam: &Lambda) -> bool {
    match lam {
        Lambda::Lvar(_) | Lambda::LglobalModule(_, _) | Lambda::Lconst(_) => false,
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
        Lambda::Lassign(_, value) => lambda_has_exit(value),
        Lambda::LifThenElse(cond, then_, else_) => {
            lambda_has_exit(cond) || lambda_has_exit(then_) || lambda_has_exit(else_)
        }
    }
}

fn lambda_contains_staticcatch(lam: &Lambda) -> bool {
    match lam {
        Lambda::Lvar(_) | Lambda::LglobalModule(_, _) | Lambda::Lconst(_) => false,
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
        Lambda::Lvar(_) | Lambda::LglobalModule(_, _) | Lambda::Lconst(_) => false,
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
        Lambda::Lassign(_, value) => lambda_contains_static_raise_to_label(value, label, arity),
        Lambda::LifThenElse(cond, then_, else_) => {
            lambda_contains_static_raise_to_label(cond, label, arity)
                || lambda_contains_static_raise_to_label(then_, label, arity)
                || lambda_contains_static_raise_to_label(else_, label, arity)
        }
    }
}

fn switch_cases_contain_static_raise_to_label(
    const_cases: &[(i32, Lambda)],
    block_cases: &[(i32, Lambda)],
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

fn switch_cases_contain_nontrivial_static_raise_to_label(
    const_cases: &[(i32, Lambda)],
    block_cases: &[(i32, Lambda)],
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
        Lambda::Lvar(_) | Lambda::LglobalModule(_, _) | Lambda::Lconst(_) => 0,
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
        Lambda::Lvar(_) | Lambda::LglobalModule(_, _) | Lambda::Lconst(_) => false,
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
        StatementDesc::While(cond, body) => {
            collect_modules_from_expression(cond, modules);
            collect_modules_from_block(body, modules);
        }
        StatementDesc::ForRange(init, finish, _, _, body) => {
            if let Some(init) = init {
                collect_modules_from_expression(init, modules);
            }
            collect_modules_from_expression(finish, modules);
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
        StatementDesc::Debugger | StatementDesc::Break | StatementDesc::Continue => {}
    }
}

fn collect_modules_from_expression(expr: &Expression, modules: &mut OcamlModuleSet) {
    match &expr.desc {
        ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(module, _)) => {
            if !module.dynamic_import {
                modules.insert(module.clone());
            }
        }
        ExpressionDesc::Length(inner, _)
        | ExpressionDesc::IsNullOrUndefined(inner)
        | ExpressionDesc::Typeof(inner)
        | ExpressionDesc::JsNot(inner)
        | ExpressionDesc::JsBnot(inner)
        | ExpressionDesc::Await(inner)
        | ExpressionDesc::Spread(inner)
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
        ExpressionDesc::TaggedTemplate(tag, strings, values) => {
            collect_modules_from_expression(tag, modules);
            for string in strings {
                collect_modules_from_expression(string, modules);
            }
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
        ExpressionDesc::CamlBlock(items, _, tag, _) => {
            for item in items {
                collect_modules_from_expression(item, modules);
            }
            collect_modules_from_expression(tag, modules);
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
        | ExpressionDesc::Str { .. }
        | ExpressionDesc::RawJsCode(_)
        | ExpressionDesc::Number(_)
        | ExpressionDesc::Undefined { .. }
        | ExpressionDesc::Null => {}
    }
}

fn is_builtin_untagged_switch_name(name: &str) -> bool {
    matches!(
        name,
        "Null"
            | "Undefined"
            | "Boolean"
            | "String"
            | "Number"
            | "BigInt"
            | "Object"
            | "Array"
            | "Function"
            | "ArrayBuffer"
            | "BigInt64Array"
            | "BigUint64Array"
            | "Blob"
            | "DataView"
            | "Date"
            | "File"
            | "Float32Array"
            | "Float64Array"
            | "Int16Array"
            | "Int32Array"
            | "Int8Array"
            | "Promise"
            | "RegExp"
            | "Set"
            | "Map"
            | "Uint16Array"
            | "Uint32Array"
            | "Uint8Array"
            | "Uint8ClampedArray"
            | "WeakSet"
            | "WeakMap"
    )
}

#[derive(Clone, Copy)]
enum GroupedSwitchDefault<'a> {
    Complete,
    NonComplete,
    Default(&'a Lambda),
}

fn pointer_info_comment_text(comment: Option<&PointerInfo>) -> Option<String> {
    match comment {
        Some(PointerInfo::None) | None => None,
        Some(PointerInfo::Constructor(tag)) => Some(tag.name.clone()),
        Some(PointerInfo::AssertFalse) => Some("assert_false".to_string()),
        Some(PointerInfo::Some(name)) | Some(PointerInfo::PolyVariant(name)) => Some(name.clone()),
    }
}

#[cfg(test)]
#[path = "compile_tests.rs"]
mod tests;

