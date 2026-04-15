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
    VIdent, VariableDeclaration, expression_has_no_side_effects,
};
use crate::lambda::analysis;
use crate::lambda::compat::{Comparison, FieldDbgInfo, LetKind, SetFieldDbgInfo};
use crate::lambda::constant::{Constant, ConstructorRuntimeTag, PointerInfo, StringDelim};
use crate::lambda::free_variables::free_variables;
use crate::lambda::primitive::{
    ExternalArgAttr, ExternalArgConst, ExternalArgDelim, ExternalArgLabel, ExternalArgSpec,
    ExternalModuleBindName, ExternalModuleName, ExternalObjLabel, ExternalObjSpec, ExternalSpec,
    Mutable, Primitive,
};
use crate::lambda::subst;
use crate::lambda::{
    ApInfo, Apply, ApplyStatus, FunctionAttribute, InlineAttribute, LFunction, Lambda,
    LambdaSwitch, SwitchBlock, SwitchBlockType, SwitchCaseTag, TagInfo,
};
use crate::location::Location;

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

fn call_info_of_apply_status(call_transformed_jsx: bool, status: ApplyStatus) -> CallInfo {
    match status {
        ApplyStatus::InferFull | ApplyStatus::Na | ApplyStatus::Uncurry => CallInfo {
            call_transformed_jsx,
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

    fn grouped_switch_case_refs<'a, T: Clone, F>(
        &self,
        cases: &'a [(T, &'a Lambda)],
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
            .map(|(tag, lam)| (tag.clone(), *lam))
            .collect();

        stable_group_switch_cases(filtered, merge_cases)
    }

    /// Create a new compiler.
    pub fn new() -> Self {
        Self {
            id_gen: IdGenerator::new(),
            module_path_resolver: None,
            jsx_preserve: false,
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
        Self {
            id_gen: IdGenerator::new(),
            module_path_resolver,
            jsx_preserve,
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
        let simplified = crate::lambda::simplify::simplify_for_js_backend(lam);
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
        let exports = resolve_export_aliases(&block, exports);
        let side_effect = module_side_effect_reason(&simplified);

        let mut deps = apply_js_shake_pass(apply_js_flatten_and_mark_dead_pass(
            apply_js_tailcall_inline_pass(apply_external_shadow_pass(apply_js_flatten_pass(
                DepsProgram {
                    program: Program::new(block, exports),
                    modules: vec![],
                    side_effect,
                },
            ))),
            self.jsx_preserve,
        ));
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

        for (export, value) in extracted.exports.into_iter().zip(extracted.values) {
            if let ExpressionDesc::Var(VIdent::Id(target)) = &value.desc {
                if target.name() == export.name() {
                    if declared.contains(&export) {
                        exports.push(export);
                        continue;
                    }
                    if declared.contains(target) {
                        exports.push(target.clone());
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
                if !bindings.is_empty() || self.staticcatch_requires_explicit_jump(bindings, handler)
                {
                    self.compile_staticcatch_expr(*label, bindings, body, handler)
                } else {
                    self.with_static_handler(*label, bindings, handler, |this| {
                        this.compile_expr(body)
                    })
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
                    let tmp = self.fresh_ident("ifres");
                    let then_block = self.compile_assign_to_target_block(&tmp, then_);
                    let else_block = self.compile_assign_to_target_block(&tmp, else_);
                    prelude.extend(self.compile_declared_if_block(
                        LetKind::Strict,
                        &tmp,
                        cond_compiled.expr,
                        then_block,
                        else_block,
                    ));
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
                let cond_expr = self.compile_expr(cond).expr;
                let body_block = self.compile_block(body);
                Compiled {
                    prelude: vec![Statement::while_(cond_expr, body_block)],
                    expr: Expression::undefined(false),
                }
            }
            Lambda::Lfor(var, start, end, dir, body) => {
                let start_expr = self.compile_expr(start).expr;
                let (end, dir) = lower_ocaml_for_range_direction(dir, end);
                let end_expr = self.compile_expr(end).expr;
                let body_block = self.compile_block(body);
                let stmt = Statement::new(StatementDesc::ForRange(
                    Some(start_expr),
                    end_expr,
                    var.clone(),
                    dir,
                    body_block,
                ));
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

    fn compile_recursive_bindings(&mut self, bindings: &[(Ident, Lambda)]) -> Block {
        let dependencies = recursive_binding_dependencies(bindings);
        let mut block = vec![];

        for group in recursive_binding_groups(bindings, &dependencies) {
            if let [index] = group.as_slice() {
                if !dependencies[*index].contains(index) {
                    let (id, expr) = &bindings[*index];
                    block.extend(self.compile_let_binding(LetKind::Strict, id, expr));
                    continue;
                }
            }

            let recursive_functions = recursive_function_bindings_in_group(bindings, &group);
            let recursive_function_tail_targets =
                direct_recursive_function_tail_targets_with_group(
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
                let (binding_decls, binding_effects) =
                    self.compile_recursive_binding(
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
                    value: Some(self.compile_recursive_function_expr(
                        id,
                        &func,
                        tail_targets,
                    )),
                    property: LetKind::Alias,
                    ident_info: IdentInfo::default(),
                })],
            );
        }

        if let Some(target) = recursive_function_binding_alias_target(expr, recursive_functions) {
            if recursive_function_ids.iter().any(|function_id| target.same(function_id)) {
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
                if !block_terminates(&effects) {
                    effects.push(Statement::exp(Expression::bin(
                        BinOp::Eq,
                        Expression::var(id.clone()),
                        compiled.expr,
                    )));
                }
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
                if !bindings.is_empty() || self.staticcatch_requires_explicit_jump(bindings, handler)
                {
                    let mut block = vec![Statement::variable(VariableDeclaration {
                        ident: id.clone(),
                        value: None,
                        property: kind,
                        ident_info: IdentInfo::default(),
                    })];
                    block.extend(self.compile_staticcatch_assignment_block(
                        id, *label, bindings, body, handler,
                    ));
                    block
                } else {
                    self.with_static_handler(*label, bindings, handler, |this| {
                        this.compile_let_binding(kind, id, body)
                    })
                }
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
                let mut block = vec![Statement::variable(VariableDeclaration {
                    ident: id.clone(),
                    value: None,
                    property: kind,
                    ident_info: IdentInfo::default(),
                })];
                block.extend(self.compile_switch_assignment_block(id, scrut, switch));
                block
            }
            Lambda::LstringSwitch(scrut, cases, default) => {
                let mut block = vec![Statement::variable(VariableDeclaration {
                    ident: id.clone(),
                    value: None,
                    property: kind,
                    ident_info: IdentInfo::default(),
                })];
                block.extend(self.compile_string_switch_assignment_block(
                    id,
                    scrut,
                    cases,
                    default.as_deref(),
                ));
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
        match lam {
            Lambda::Llet(kind, id, value, body) => {
                let mut block = self.compile_let_binding(*kind, id, value);
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
                if !bindings.is_empty() || self.staticcatch_requires_explicit_jump(bindings, handler)
                {
                    self.compile_staticcatch_effect_block(*label, bindings, body, handler)
                } else {
                    self.with_static_handler(*label, bindings, handler, |this| {
                        this.compile_effect_block(body)
                    })
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

        let test = match op {
            ShortCircuitOp::And => lhs_compiled.expr,
            ShortCircuitOp::Or => Expression::not(lhs_compiled.expr),
        };
        prelude.push(Statement::if_(test, then_block, vec![]));

        Compiled {
            prelude,
            expr: Expression::var(tmp),
        }
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
        match lam {
            Lambda::Llet(kind, id, value, body) => {
                let mut block = self.compile_let_binding(*kind, id, value);
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
            Lambda::LifThenElse(cond, then_, else_) => {
                self.compile_if_return_block(cond, then_, else_)
            }
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
                if self.uses_fallthrough_staticcatch_return(body, *label, bindings, handler) =>
            {
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
                let body_block = self.with_fallthrough_return_handler(*label, bindings, |this| {
                    this.compile_return_block(body)
                });
                block.extend(body_block);
                if !block_terminates(&block) {
                    block.extend(self.compile_return_block(handler));
                }
                block
            }
            Lambda::LstaticCatch(body, (label, bindings), handler) => {
                if (self.return_unit_stack.last().copied() == Some(true) && !bindings.is_empty())
                    || self.return_staticcatch_requires_explicit_jump(
                        *label, bindings, body, handler,
                    )
                {
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
        match body {
            Lambda::Lswitch(_, switch) => match handler {
                Lambda::LstaticRaise(_, args)
                    if args.len() == bindings.len()
                        && lambda_contains_static_raise_to_label(body, label, bindings.len()) =>
                {
                    true
                }
                _ if !self.uses_untagged_variant_switch(switch)
                    && !inside_enclosing_staticcatch_chain
                    && !lambda_contains_static_raise(handler)
                    && !lambda_contains_staticcatch(handler)
                    && switch_cases_contain_static_raise_to_label(
                        &switch.sw_consts,
                        &switch.sw_blocks,
                        label,
                        bindings.len(),
                    )
                    && lambda_contains_static_raise_to_label(body, label, bindings.len())
                    && lambda_contains_static_raise_to_other_label(body, label) =>
                {
                    true
                }
                _ if self.return_unit_stack.last().copied() == Some(true)
                    && !inside_enclosing_staticcatch_chain
                    && !lambda_contains_static_raise(handler) =>
                {
                    if !bindings.is_empty() {
                        lambda_contains_static_raise_to_label(body, label, bindings.len())
                    } else {
                        switch.sw_consts.len() + switch.sw_blocks.len() == 1
                            && matches!(
                                switch.sw_failaction.as_deref(),
                                Some(Lambda::LstaticRaise(id, args))
                                    if *id == label && args.len() == bindings.len()
                            )
                    }
                }
                _ => false,
            },
            Lambda::LstringSwitch(_, cases, default) => match handler {
                Lambda::LstaticRaise(_, args)
                    if args.len() == bindings.len()
                        && lambda_contains_static_raise_to_label(body, label, bindings.len()) =>
                {
                    true
                }
                _ if !lambda_contains_static_raise(handler)
                    && !lambda_contains_staticcatch(handler)
                    && string_switch_cases_contain_static_raise_to_label(
                        cases,
                        label,
                        bindings.len(),
                    )
                    && lambda_contains_static_raise_to_label(body, label, bindings.len())
                    && lambda_contains_static_raise_to_other_label(body, label) =>
                {
                    true
                }
                _ if self.return_unit_stack.last().copied() == Some(true)
                    && !inside_enclosing_staticcatch_chain
                    && !lambda_contains_static_raise(handler) =>
                {
                    if !bindings.is_empty() {
                        lambda_contains_static_raise_to_label(body, label, bindings.len())
                    } else {
                        cases.len() == 1
                            && matches!(
                                default.as_deref(),
                                Some(Lambda::LstaticRaise(id, args))
                                    if *id == label && args.len() == bindings.len()
                            )
                    }
                }
                _ => false,
            },
            _ => false,
        }
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

            for (tag, _, _) in &grouped_cases[group_start..group_end] {
                clauses.push((to_tag(tag.clone()), empty_switch_case_clause(), group_falls_through));
            }
            clauses.push((
                to_tag(grouped_cases[group_end].0.clone()),
                CaseClause {
                    body: compiled_body,
                    should_break: false,
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
                let handler_index = self
                    .static_handlers
                    .iter()
                    .rposition(|handler| handler.label == *label && handler.bindings.len() == args.len())?;
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
        if !function_has_self_tailcall(tail_targets, &func.body) {
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
                if (self.return_unit_stack.last().copied() == Some(true) && !bindings.is_empty())
                    || self.return_staticcatch_requires_explicit_jump(
                        *label, bindings, body, handler,
                    )
                {
                    self.compile_staticcatch_tail_loop_return_block(
                        *label,
                        bindings,
                        body,
                        handler,
                        tail_loop,
                    )
                } else {
                    self.with_static_handler(*label, bindings, handler, |this| {
                        this.compile_tail_loop_return_block(body, tail_loop)
                    })
                }
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

        block.push(Statement::if_(cond_compiled.expr, then_block, else_block));
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
                if !bindings.is_empty() || self.staticcatch_requires_explicit_jump(bindings, handler)
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
            match (then_expr_pure, else_expr_pure) {
                (true, true) => {
                    push_effect_expression(&mut block, cond_expr);
                    return block;
                }
                (false, false) => {
                    push_effect_expression(
                        &mut block,
                        Expression::cond(cond_expr, then_compiled.expr, else_compiled.expr),
                    );
                    return block;
                }
                (false, true) => {
                    block.push(Statement::if_(
                        cond_expr,
                        self.compiled_to_effect_block(then_compiled),
                        vec![],
                    ));
                    return block;
                }
                (true, false) => {
                    block.push(Statement::if_(
                        Expression::not(cond_expr),
                        self.compiled_to_effect_block(else_compiled),
                        vec![],
                    ));
                    return block;
                }
            }
        }

        if then_prelude_empty && then_expr_pure {
            block.push(Statement::if_(
                Expression::not(cond_expr),
                self.compiled_to_effect_block(else_compiled),
                vec![],
            ));
            return block;
        }

        if else_prelude_empty && else_expr_pure {
            block.push(Statement::if_(
                cond_expr,
                self.compiled_to_effect_block(then_compiled),
                vec![],
            ));
            return block;
        }

        block.push(Statement::if_(
            cond_expr,
            self.compiled_to_effect_block(then_compiled),
            self.compiled_to_effect_block(else_compiled),
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
            false,
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
        Some(names.consts.iter().map(Self::switch_tag_value).collect())
    }

    fn untagged_block_types(&self, switch: &LambdaSwitch) -> Option<Vec<SwitchBlockType>> {
        let names = switch.sw_names.as_ref()?;
        Some(
            names
                .blocks
                .iter()
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
        let literal_disjunction = || {
            literal_cases
                .iter()
                .map(literal_case)
                .reduce(|acc, next| bin(BinOp::Or, next, acc))
                .expect("literal cases are non-empty")
        };
        let typeof_neq = |type_name: &str| {
            (
                Expression::bin(
                    BinOp::NotEqEq,
                    Expression::new(ExpressionDesc::Typeof(Box::new(expr.clone()))),
                    Expression::string(type_name),
                ),
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
                SwitchBlockType::Object => {
                    let mut object_case = if literals_overlap_with_object {
                        bin(
                            BinOp::Or,
                            literal_case(&SwitchCaseTag::Null),
                            typeof_neq("object"),
                        )
                    } else {
                        typeof_neq("object")
                    };
                    for other in &block_cases {
                        let SwitchBlockType::Instance(name) = other else {
                            continue;
                        };
                        let instance_test = self
                            .builtin_untagged_instance_test(expr.clone(), name)
                            .expect("instance-backed block types stay supported");
                        object_case =
                            bin(BinOp::Or, (instance_test, 3usize), object_case);
                    }
                    object_case
                }
                SwitchBlockType::String
                | SwitchBlockType::Int
                | SwitchBlockType::Float
                | SwitchBlockType::BigInt
                | SwitchBlockType::Boolean
                | SwitchBlockType::Unknown => literal_disjunction(),
            }
        };

        let with_literal_cases = literal_disjunction();
        let without_literal_cases = block_cases
            .iter()
            .rev()
            .map(is_not_block_case)
            .reduce(|acc, next| bin(BinOp::And, next, acc))
            .expect("block cases are non-empty");

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
        Expression::bin(
            BinOp::EqEqEq,
            Expression::new(ExpressionDesc::Typeof(Box::new(expr))),
            Expression::string(type_name),
        )
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

        let mut tail = if typeof_cases.is_empty() {
            self.block_switch_default(switch)
                .map(|fallback| self.compile_assign_to_target_block(result, fallback))
                .unwrap_or_default()
        } else {
            self.compile_named_string_switch_assignment(
                result,
                Expression::new(ExpressionDesc::Typeof(Box::new(scrut_expr.clone()))),
                &typeof_cases,
                self.block_switch_default(switch),
                self.block_switch_complete(switch),
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

        let mut tail = if typeof_cases.is_empty() {
            self.block_switch_default(switch)
                .map(|fallback| self.compile_return_block(fallback))
                .unwrap_or_default()
        } else {
            self.compile_named_string_switch_return(
                Expression::new(ExpressionDesc::Typeof(Box::new(scrut_expr.clone()))),
                &typeof_cases,
                self.block_switch_default(switch),
                self.block_switch_complete(switch),
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
            tail = vec![Statement::if_(test, self.compile_return_block(body), tail)];
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
                Some(vec![Statement::if_(
                    cond,
                    self.compile_return_block(body),
                    default
                        .map(|fallback| self.compile_return_block(fallback))
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
                    self.compile_return_block(then_body),
                    self.compile_return_block(else_body),
                )])
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

        let mut tail = if typeof_cases.is_empty() {
            self.block_switch_default(switch)
                .map(|fallback| self.compile_effect_block(fallback))
                .unwrap_or_default()
        } else {
            self.compile_named_string_switch_effect(
                Expression::new(ExpressionDesc::Typeof(Box::new(scrut_expr.clone()))),
                &typeof_cases,
                self.block_switch_default(switch),
                self.block_switch_complete(switch),
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
        let const_cases_are_complete = const_cases.len() == literal_cases.len();
        let const_default = if const_cases_are_complete {
            None
        } else {
            self.const_switch_default(switch)
        };
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
                const_cases_are_complete,
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
        let const_cases_are_complete = const_cases.len() == literal_cases.len();
        let const_default = if const_cases_are_complete {
            None
        } else {
            self.const_switch_default(switch)
        };
        let const_branch = if const_cases.is_empty() {
            const_default
                .map(|fallback| self.compile_return_block(fallback))
                .unwrap_or_default()
        } else {
            self.compile_named_string_switch_return(
                scrut_expr.clone(),
                &const_cases,
                const_default,
                const_cases_are_complete,
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
        let const_cases_are_complete = const_cases.len() == literal_cases.len();
        let const_default = if const_cases_are_complete {
            None
        } else {
            self.const_switch_default(switch)
        };
        let const_branch = if const_cases.is_empty() {
            const_default
                .map(|fallback| self.compile_effect_block(fallback))
                .unwrap_or_default()
        } else {
            self.compile_named_string_switch_effect(
                scrut_expr.clone(),
                &const_cases,
                const_default,
                const_cases_are_complete,
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
            self.compile_effect_if(Expression::not(dispatch_test), block_branch, vec![])
        } else if block_branch.is_empty() {
            self.compile_effect_if(dispatch_test, const_branch, vec![])
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
        Expression::bin(
            BinOp::EqEqEq,
            Expression::new(ExpressionDesc::Typeof(Box::new(expr))),
            Expression::string("object"),
        )
    }

    fn variant_non_object_test(&self, expr: Expression) -> Expression {
        Expression::bin(
            BinOp::NotEqEq,
            Expression::new(ExpressionDesc::Typeof(Box::new(expr))),
            Expression::string("object"),
        )
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
            [(tag, body)] => Some(vec![Statement::if_(
                self.switch_case_test(test, tag),
                self.compile_assign_to_target_block(result, body),
                default
                    .map(|fallback| self.compile_assign_to_target_block(result, fallback))
                    .unwrap_or_default(),
            )]),
            [(tag, then_body), (_, else_body)] if complete && default.is_none() => {
                Some(vec![Statement::if_(
                    self.switch_case_test(test, tag),
                    self.compile_assign_to_target_block(result, then_body),
                    self.compile_assign_to_target_block(result, else_body),
                )])
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
            [(tag, body)] => Some(vec![Statement::if_(
                self.switch_case_test(test, tag),
                self.compile_return_block(body),
                default
                    .map(|fallback| self.compile_return_block(fallback))
                    .unwrap_or_default(),
            )]),
            [(tag, then_body), (_, else_body)] if complete && default.is_none() => {
                Some(vec![Statement::if_(
                    self.switch_case_test(test, tag),
                    self.compile_return_block(then_body),
                    self.compile_return_block(else_body),
                )])
            }
            _ => None,
        }
    }

    fn compile_effect_if(&self, cond: Expression, then_block: Block, else_block: Block) -> Block {
        if then_block.is_empty() {
            if else_block.is_empty() {
                vec![]
            } else {
                vec![Statement::if_(Expression::not(cond), else_block, vec![])]
            }
        } else if else_block.is_empty() {
            vec![Statement::if_(cond, then_block, vec![])]
        } else {
            vec![Statement::if_(cond, then_block, else_block)]
        }
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

    fn compile_named_string_switch_assignment(
        &mut self,
        result: &Ident,
        test: Expression,
        cases: &[(SwitchCaseTag, &Lambda)],
        default: Option<&Lambda>,
        complete: bool,
    ) -> Block {
        if let Some(block) = self.compile_small_string_switch_assignment(
            result,
            test.clone(),
            cases,
            default,
            complete,
        ) {
            return block;
        }

        let clauses = self
            .grouped_switch_case_refs(cases, default, |_, _| true)
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

    fn compile_named_string_switch_return(
        &mut self,
        test: Expression,
        cases: &[(SwitchCaseTag, &Lambda)],
        default: Option<&Lambda>,
        complete: bool,
    ) -> Block {
        if let Some(block) =
            self.compile_small_string_switch_return(test.clone(), cases, default, complete)
        {
            return block;
        }

        let grouped_cases = self.grouped_switch_case_refs(cases, default, |_, _| true);
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
                        CaseClause {
                            body: compiled_body,
                            should_break: false,
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

    fn compile_named_string_switch_effect(
        &mut self,
        test: Expression,
        cases: &[(SwitchCaseTag, &Lambda)],
        default: Option<&Lambda>,
        complete: bool,
    ) -> Block {
        if let Some(block) =
            self.compile_small_string_switch_effect(test.clone(), cases, default, complete)
        {
            return block;
        }

        let clauses: Vec<_> = self
            .grouped_switch_case_refs(cases, default, |_, _| true)
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
        match (
            self.take_single_result_assignment(result, then_block),
            self.take_single_result_assignment(result, else_block),
        ) {
            (Ok(then_expr), Ok(else_expr)) => {
                block.push(self.result_assignment(
                    result,
                    Expression::cond(cond_compiled.expr, then_expr, else_expr),
                ));
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
                block.push(Statement::if_(cond_compiled.expr, then_block, else_block));
            }
        }
        block
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

    fn take_single_result_assignment(
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
            desc: StatementDesc::Exp(Expression {
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

    fn take_single_return_expr(&self, block: Block) -> Result<Expression, Block> {
        let [stmt] = block.as_slice() else {
            return Err(block);
        };
        if !matches!(stmt.desc, StatementDesc::Return(_)) {
            return Err(block);
        }

        let stmt = block.into_iter().next().expect("single-statement block");
        let Statement {
            desc: StatementDesc::Return(expr),
            ..
        } = stmt
        else {
            unreachable!("validated single return shape")
        };
        Ok(expr)
    }

    fn compile_if_return_block(&mut self, cond: &Lambda, then_: &Lambda, else_: &Lambda) -> Block {
        let cond_compiled = self.compile_expr(cond);
        let then_block = self.compile_return_block(then_);
        let else_block = self.compile_return_block(else_);

        let mut block = cond_compiled.prelude;
        match (
            self.take_single_return_expr(then_block),
            self.take_single_return_expr(else_block),
        ) {
            (Ok(then_expr), Ok(else_expr)) => {
                block.push(Statement::return_(Expression::cond(
                    cond_compiled.expr,
                    then_expr,
                    else_expr,
                )));
            }
            (then_result, else_result) => {
                let then_block = match then_result {
                    Ok(expr) => vec![Statement::return_(expr)],
                    Err(block) => block,
                };
                let else_block = match else_result {
                    Ok(expr) => vec![Statement::return_(expr)],
                    Err(block) => block,
                };
                block.push(Statement::if_(cond_compiled.expr, then_block, else_block));
            }
        }
        block
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
                if !bindings.is_empty() || self.staticcatch_requires_explicit_jump(bindings, handler)
                {
                    self.compile_staticcatch_assignment_block(result, *label, bindings, body, handler)
                } else {
                    self.with_static_handler(*label, bindings, handler, |this| {
                        this.compile_assign_to_target_block(result, body)
                    })
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
            let (mut block, scrut_expr) =
                self.bind_switch_scrutinee_once(scrut_compiled.prelude, scrut_compiled.expr);
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
            false,
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

        let grouped_cases =
            self.grouped_switch_cases(&switch.sw_consts, switch.sw_failaction.as_deref(), |_, _| {
                true
            });
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

            for (tag, _, _) in &grouped_cases[group_start..group_end] {
                cases.push((tag.clone(), empty_switch_case_clause(), group_falls_through));
            }
            cases.push((
                grouped_cases[group_end].0,
                crate::js_ir::CaseClause {
                    body: compiled_body,
                    should_break: false,
                    comment: None,
                },
                group_falls_through,
            ));

            group_start = group_end + 1;
        }
        let cases = self.reorder_fallthrough_return_clauses(cases, |(_, _, falls_through)| {
            *falls_through
        });
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
            false,
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
                push_effect_expression(&mut block, scrut_expr);
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
                push_effect_expression(&mut block, scrut_expr);
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
            push_effect_expression(&mut block, scrut_compiled.expr);
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
                push_effect_expression(&mut block, scrut_compiled.expr);
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
            push_effect_expression(&mut block, scrut_compiled.expr);
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
            Pdivint => int32_div(compiled_args[0].clone(), compiled_args[1].clone()),
            Pdivfloat => Expression::bin(
                BinOp::Div,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Pdivbigint => Expression::bin(
                BinOp::Div,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Pmodint => int32_mod(compiled_args[0].clone(), compiled_args[1].clone()),
            Pmodfloat => Expression::bin(
                BinOp::Mod,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
            Pmodbigint => Expression::bin(
                BinOp::Mod,
                compiled_args[0].clone(),
                compiled_args[1].clone(),
            ),
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
            Pbigintcomp(cmp) | Pjscomp(cmp) => {
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
            Pnegfloat => Expression::bin(BinOp::Minus, int_expr(0), compiled_args[0].clone()),
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
            Ptypeof => Expression::new(ExpressionDesc::Typeof(Box::new(compiled_args[0].clone()))),
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
                Expression::new(ExpressionDesc::CamlBlock(
                    elems,
                    MutableFlag::Immutable,
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
                ExpressionDesc::CamlBlock(items, _, _, _) if js_expr_no_side_effects(target) => {
                    items.get(idx as usize).cloned().unwrap_or_else(|| {
                        Expression::new(ExpressionDesc::StaticIndex(
                            Box::new(target.clone()),
                            convert_ident_name(name),
                            Some(idx),
                        ))
                    })
                }
                _ => Expression::new(ExpressionDesc::StaticIndex(
                    Box::new(target.clone()),
                    convert_ident_name(name),
                    Some(idx),
                )),
            },
            FieldDbgInfo::Record { name, .. }
            | FieldDbgInfo::RecordInline { name }
            | FieldDbgInfo::RecordExtension { name } => Expression::new(
                ExpressionDesc::StaticIndex(Box::new(target.clone()), name.clone(), None),
            ),
            FieldDbgInfo::Extension => Expression::new(ExpressionDesc::StaticIndex(
                Box::new(target.clone()),
                format!("_{}", idx),
                Some(idx),
            )),
            FieldDbgInfo::Cons => Expression::new(ExpressionDesc::StaticIndex(
                Box::new(target.clone()),
                match idx {
                    0 => "hd".to_string(),
                    1 => "tl".to_string(),
                    _ => format!("_{}", idx),
                },
                None,
            )),
            FieldDbgInfo::PolyVarTag => poly_var_tag_access(target),
            FieldDbgInfo::PolyVarContent => poly_var_value_access(target),
            FieldDbgInfo::VariantTag => Expression::new(ExpressionDesc::StaticIndex(
                Box::new(target.clone()),
                "TAG".to_string(),
                None,
            )),
            FieldDbgInfo::Variant => {
                // Variant fields are accessed as _0, _1, _2, ...
                Expression::new(ExpressionDesc::StaticIndex(
                    Box::new(target.clone()),
                    format!("_{}", idx),
                    None,
                ))
            }
            _ => Expression::new(ExpressionDesc::ArrayIndex(
                Box::new(target.clone()),
                Box::new(Expression::number(Number::int(idx))),
            )),
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

                compile_raw_comparison(cmp, left, right)
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
            _ => panic!("object field lowering expected one JS arg, got {:?}", values),
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
        let mut runtime_args = args.into_iter();
        let mut props = Vec::new();
        let mut effects = Vec::new();
        let mut optional_assignments = Vec::new();

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
                            let arg = Expression::new(other);
                            let prepared = if self.expr_is_simple(&arg) {
                                arg
                            } else {
                                let tmp = self.fresh_ident("obj");
                                prelude.push(Statement::variable(VariableDeclaration {
                                    ident: tmp.clone(),
                                    value: Some(arg),
                                    property: LetKind::Variable,
                                    ident_info: IdentInfo::default(),
                                }));
                                Expression::var(tmp)
                            };

                            let value_arg = if *for_sure_no_nested_option {
                                prepared.clone()
                            } else {
                                self.val_from_option_expr(prepared.clone())
                            };
                            let (value, effect) = self.lower_object_external_arg_value_and_effect(
                                value_arg,
                                ExternalArgLabel::Empty,
                                &obj_param.obj_arg_type,
                            );
                            optional_assignments.push((
                                name.clone(),
                                prepared,
                                self.add_external_effect(effect, value),
                            ));
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

        let obj = self.fresh_ident("obj");
        prelude.push(Statement::variable(VariableDeclaration {
            ident: obj.clone(),
            value: Some(object),
            property: LetKind::Variable,
            ident_info: IdentInfo::default(),
        }));

        for (name, arg, value) in optional_assignments {
            let cond = Expression::bin(BinOp::NotEqEq, arg, Expression::undefined(false));
            let assign = Expression::bin(
                BinOp::Eq,
                self.static_index(Expression::var(obj.clone()), &name),
                value,
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
        self.lambda_requires_explicit_staticcatch_jump(handler)
            || (lambda_has_multiple_static_raises_to_label(body, label, bindings.len())
                && lambda_contains_static_raise_to_other_label(handler, label))
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
                    || switch.sw_failaction.as_deref().is_some_and(|body| {
                        self.lambda_requires_explicit_staticcatch_jump(body)
                    })
            }
            Lambda::LstringSwitch(scrut, cases, default) => {
                self.lambda_requires_explicit_staticcatch_jump(scrut)
                    || cases
                        .iter()
                        .any(|(_, body)| self.lambda_requires_explicit_staticcatch_jump(body))
                    || default.as_deref().is_some_and(|body| {
                        self.lambda_requires_explicit_staticcatch_jump(body)
                    })
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
        i32::try_from(self.static_jump_handlers.len() + 1)
            .expect("static jump handler depth fits in i32")
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
        prelude.extend(self.compile_staticcatch_assignment_block(
            &result, label, bindings, body, handler,
        ));
        Compiled {
            prelude,
            expr: Expression::var(result),
        }
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

fn recursive_function_binding_value(expr: &Lambda) -> Option<LFunction> {
    match expr {
        Lambda::Lfunction(func) => Some(func.clone()),
        Lambda::Lprim(info) => match (&info.primitive, info.args.as_slice()) {
            (Primitive::PjsFnMake(arity), [Lambda::Lfunction(func)]) => {
                Some(adjust_recursive_js_fn_make_function(func, *arity, &info.loc))
            }
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

fn recursive_binding_group_is_function_only(
    bindings: &[(Ident, Lambda)],
    group: &[usize],
) -> bool {
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
        .filter_map(|(id, expr)| recursive_function_binding_value(expr).map(|func| (id.clone(), func)))
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
        Lambda::Lvar(_)
        | Lambda::LglobalModule(_, _)
        | Lambda::Lconst(_)
        | Lambda::Lfunction(_)
        | Lambda::Lletrec(_, _)
        | Lambda::LstaticRaise(_, _)
        | Lambda::LtryWith(_, _, _)
        | Lambda::Lwhile(_, _)
        | Lambda::Lfor(_, _, _, _, _)
        | Lambda::Lassign(_, _) => false,
    }
}

fn direct_recursive_function_tail_targets(bindings: &[(Ident, Lambda)]) -> HashMap<Ident, Vec<Ident>> {
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
        tail_targets.entry(function_id).or_default().push(id.clone());
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
        tail_targets.entry(function_id).or_default().push(id.clone());
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

fn js_expr_no_side_effects(expr: &Expression) -> bool {
    match &expr.desc {
        ExpressionDesc::Undefined { .. }
        | ExpressionDesc::Null
        | ExpressionDesc::Bool(_)
        | ExpressionDesc::Var(_)
        | ExpressionDesc::Fun { .. }
        | ExpressionDesc::Number(_)
        | ExpressionDesc::Str { .. } => true,
        ExpressionDesc::StaticIndex(target, _, _) => js_expr_no_side_effects(target),
        ExpressionDesc::StringIndex(left, right)
        | ExpressionDesc::ArrayIndex(left, right)
        | ExpressionDesc::In(left, right)
        | ExpressionDesc::StringAppend(left, right)
        | ExpressionDesc::Seq(left, right) => {
            js_expr_no_side_effects(left) && js_expr_no_side_effects(right)
        }
        ExpressionDesc::IsNullOrUndefined(inner)
        | ExpressionDesc::Length(inner, _)
        | ExpressionDesc::Typeof(inner)
        | ExpressionDesc::JsNot(inner)
        | ExpressionDesc::JsBnot(inner)
        | ExpressionDesc::CamlBlockTag(inner, _)
        | ExpressionDesc::OptionalBlock(inner, _) => js_expr_no_side_effects(inner),
        ExpressionDesc::Array(items, _) => items.iter().all(js_expr_no_side_effects),
        ExpressionDesc::CamlBlock(items, _, _, _) => items.iter().all(js_expr_no_side_effects),
        ExpressionDesc::Object(dup, props) => {
            dup.as_deref().is_none_or(js_expr_no_side_effects)
                && props
                    .iter()
                    .all(|(_, value)| js_expr_no_side_effects(value))
        }
        ExpressionDesc::Cond(test, consequent, alternate) => {
            js_expr_no_side_effects(test)
                && js_expr_no_side_effects(consequent)
                && js_expr_no_side_effects(alternate)
        }
        ExpressionDesc::Bin(op, left, right) => {
            *op != BinOp::Eq && js_expr_no_side_effects(left) && js_expr_no_side_effects(right)
        }
        ExpressionDesc::TaggedTemplate(tag, strings, values) => {
            js_expr_no_side_effects(tag)
                && strings.iter().all(js_expr_no_side_effects)
                && values.iter().all(js_expr_no_side_effects)
        }
        ExpressionDesc::FlatCall(_, _)
        | ExpressionDesc::Call(_, _, _)
        | ExpressionDesc::New(_, _)
        | ExpressionDesc::RawJsCode(_)
        | ExpressionDesc::Await(_)
        | ExpressionDesc::Spread(_) => false,
    }
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

fn resolve_export_aliases(block: &Block, exports: Vec<Ident>) -> Vec<Ident> {
    let mut declared = HashSet::new();
    collect_declared_idents(block, &mut declared);
    let mut aliases = HashMap::new();
    collect_export_aliases(block, &mut aliases);
    exports
        .into_iter()
        .map(|export| resolve_export_alias(&export, &aliases, &declared))
        .collect()
}

fn collect_declared_idents(block: &Block, declared: &mut HashSet<Ident>) {
    for stmt in block {
        match &stmt.desc {
            StatementDesc::Variable(VariableDeclaration { ident, .. }) => {
                declared.insert(ident.clone());
            }
            StatementDesc::Block(inner) => collect_declared_idents(inner, declared),
            StatementDesc::If(_, then_block, else_block) => {
                collect_declared_idents(then_block, declared);
                collect_declared_idents(else_block, declared);
            }
            _ => {}
        }
    }
}

fn collect_export_aliases(block: &Block, aliases: &mut HashMap<Ident, Ident>) {
    for stmt in block {
        match &stmt.desc {
            StatementDesc::Variable(VariableDeclaration {
                ident,
                value:
                    Some(Expression {
                        desc: ExpressionDesc::Var(VIdent::Id(target)),
                        ..
                    }),
                ..
            }) => {
                aliases.insert(ident.clone(), target.clone());
            }
            StatementDesc::Block(inner) => collect_export_aliases(inner, aliases),
            StatementDesc::If(_, then_block, else_block) => {
                collect_export_aliases(then_block, aliases);
                collect_export_aliases(else_block, aliases);
            }
            _ => {}
        }
    }
}

fn max_ident_stamp_in_block(block: &Block) -> i32 {
    block.iter().fold(0, |max_stamp, stmt| {
        max_stamp.max(max_ident_stamp_in_statement(stmt))
    })
}

fn max_ident_stamp_in_statement(stmt: &Statement) -> i32 {
    match &stmt.desc {
        StatementDesc::Block(block) => max_ident_stamp_in_block(block),
        StatementDesc::Variable(VariableDeclaration { ident, value, .. }) => value
            .as_ref()
            .map(max_ident_stamp_in_expression)
            .unwrap_or(0)
            .max(ident.stamp()),
        StatementDesc::Exp(expr) | StatementDesc::Return(expr) | StatementDesc::Throw(expr) => {
            max_ident_stamp_in_expression(expr)
        }
        StatementDesc::If(cond, then_block, else_block) => max_ident_stamp_in_expression(cond)
            .max(max_ident_stamp_in_block(then_block))
            .max(max_ident_stamp_in_block(else_block)),
        StatementDesc::While(cond, body) => {
            max_ident_stamp_in_expression(cond).max(max_ident_stamp_in_block(body))
        }
        StatementDesc::ForRange(start, finish, ident, _, body) => start
            .as_ref()
            .map(max_ident_stamp_in_expression)
            .unwrap_or(0)
            .max(max_ident_stamp_in_expression(finish))
            .max(ident.stamp())
            .max(max_ident_stamp_in_block(body)),
        StatementDesc::IntSwitch(test, clauses, default) => {
            let mut max_stamp = max_ident_stamp_in_expression(test);
            for (_, clause) in clauses {
                max_stamp = max_stamp.max(max_ident_stamp_in_block(&clause.body));
            }
            if let Some(default) = default {
                max_stamp = max_stamp.max(max_ident_stamp_in_block(default));
            }
            max_stamp
        }
        StatementDesc::StringSwitch(test, clauses, default) => {
            let mut max_stamp = max_ident_stamp_in_expression(test);
            for clause in clauses {
                max_stamp = max_stamp.max(max_ident_stamp_in_block(&clause.clause.body));
            }
            if let Some(default) = default {
                max_stamp = max_stamp.max(max_ident_stamp_in_block(default));
            }
            max_stamp
        }
        StatementDesc::Try(body, catch, finally) => {
            let mut max_stamp = max_ident_stamp_in_block(body);
            if let Some((ident, catch_block)) = catch {
                max_stamp = max_stamp
                    .max(ident.stamp())
                    .max(max_ident_stamp_in_block(catch_block));
            }
            if let Some(finally) = finally {
                max_stamp = max_stamp.max(max_ident_stamp_in_block(finally));
            }
            max_stamp
        }
        StatementDesc::Debugger | StatementDesc::Break | StatementDesc::Continue => 0,
    }
}

fn max_ident_stamp_in_expression(expr: &Expression) -> i32 {
    match &expr.desc {
        ExpressionDesc::Var(VIdent::Id(ident)) => ident.stamp(),
        ExpressionDesc::Var(VIdent::Qualified(module, _)) => module.id.stamp(),
        ExpressionDesc::Length(inner, _)
        | ExpressionDesc::IsNullOrUndefined(inner)
        | ExpressionDesc::Typeof(inner)
        | ExpressionDesc::JsNot(inner)
        | ExpressionDesc::JsBnot(inner)
        | ExpressionDesc::CamlBlockTag(inner, _)
        | ExpressionDesc::OptionalBlock(inner, _)
        | ExpressionDesc::Await(inner)
        | ExpressionDesc::Spread(inner) => max_ident_stamp_in_expression(inner),
        ExpressionDesc::StringAppend(left, right)
        | ExpressionDesc::In(left, right)
        | ExpressionDesc::Seq(left, right)
        | ExpressionDesc::Bin(_, left, right)
        | ExpressionDesc::FlatCall(left, right)
        | ExpressionDesc::StringIndex(left, right)
        | ExpressionDesc::ArrayIndex(left, right) => {
            max_ident_stamp_in_expression(left).max(max_ident_stamp_in_expression(right))
        }
        ExpressionDesc::Cond(test, consequent, alternate) => max_ident_stamp_in_expression(test)
            .max(max_ident_stamp_in_expression(consequent))
            .max(max_ident_stamp_in_expression(alternate)),
        ExpressionDesc::Call(func, args, _) => args
            .iter()
            .fold(max_ident_stamp_in_expression(func), |max_stamp, arg| {
                max_stamp.max(max_ident_stamp_in_expression(arg))
            }),
        ExpressionDesc::TaggedTemplate(tag, strings, values) => {
            let mut max_stamp = max_ident_stamp_in_expression(tag);
            for string in strings {
                max_stamp = max_stamp.max(max_ident_stamp_in_expression(string));
            }
            for value in values {
                max_stamp = max_stamp.max(max_ident_stamp_in_expression(value));
            }
            max_stamp
        }
        ExpressionDesc::StaticIndex(target, _, _) => max_ident_stamp_in_expression(target),
        ExpressionDesc::New(target, args) => {
            let mut max_stamp = max_ident_stamp_in_expression(target);
            if let Some(args) = args {
                for arg in args {
                    max_stamp = max_stamp.max(max_ident_stamp_in_expression(arg));
                }
            }
            max_stamp
        }
        ExpressionDesc::Fun { params, body, .. } => params
            .iter()
            .fold(max_ident_stamp_in_block(body), |max_stamp, param| {
                max_stamp.max(param.stamp())
            }),
        ExpressionDesc::Array(items, _) => items.iter().fold(0, |max_stamp, item| {
            max_stamp.max(max_ident_stamp_in_expression(item))
        }),
        ExpressionDesc::CamlBlock(items, _, tag, _) => items
            .iter()
            .fold(max_ident_stamp_in_expression(tag), |max_stamp, item| {
                max_stamp.max(max_ident_stamp_in_expression(item))
            }),
        ExpressionDesc::Object(dup, props) => {
            let mut max_stamp = dup
                .as_ref()
                .map(|dup| max_ident_stamp_in_expression(dup))
                .unwrap_or(0);
            for (_, value) in props {
                max_stamp = max_stamp.max(max_ident_stamp_in_expression(value));
            }
            max_stamp
        }
        ExpressionDesc::Bool(_)
        | ExpressionDesc::Str { .. }
        | ExpressionDesc::RawJsCode(_)
        | ExpressionDesc::Number(_)
        | ExpressionDesc::Undefined { .. }
        | ExpressionDesc::Null => 0,
    }
}

fn resolve_export_alias(
    export: &Ident,
    aliases: &HashMap<Ident, Ident>,
    declared: &HashSet<Ident>,
) -> Ident {
    if declared.contains(export) {
        return export.clone();
    }

    let mut current = export.clone();
    let mut seen = HashSet::new();

    while let Some(target) = aliases.get(&current) {
        if target.name() != export.name()
            || !declared.contains(target)
            || !seen.insert(current.clone())
        {
            break;
        }
        current = target.clone();
    }

    current
}

#[derive(Debug)]
struct ExtractedExports {
    exports: Vec<Ident>,
    values: Vec<Expression>,
}

fn extract_toplevel_exports(expr: Expression, block: &mut Block) -> Option<ExtractedExports> {
    let Expression { desc, comment } = expr;
    match desc {
        ExpressionDesc::CamlBlock(values, _, _, TagInfo::ModuleExport(exports)) => {
            debug_assert_eq!(
                exports.len(),
                values.len(),
                "module export idents and payloads must stay aligned"
            );
            Some(ExtractedExports { exports, values })
        }
        ExpressionDesc::Undefined { .. } => None,
        ExpressionDesc::Seq(left, right) => {
            let mut right_block = Vec::new();
            if let Some(exports) = extract_toplevel_exports((*right).clone(), &mut right_block) {
                push_effect_expression(block, *left);
                block.extend(right_block);
                Some(exports)
            } else {
                push_effect_expression(
                    block,
                    Expression {
                        desc: ExpressionDesc::Seq(left, right),
                        comment,
                    },
                );
                None
            }
        }
        other => {
            push_effect_expression(
                block,
                Expression {
                    desc: other,
                    comment,
                },
            );
            None
        }
    }
}

fn can_reuse_existing_undefined_export_binding(block: &Block, export: &Ident) -> bool {
    let flattened = flatten_toplevel_block(block);
    let Some(export_index) = flattened.iter().position(|stmt| {
        matches!(
            &stmt.desc,
            StatementDesc::Variable(VariableDeclaration { ident, .. }) if ident.same(export)
        )
    }) else {
        return false;
    };

    flattened[export_index + 1..]
        .iter()
        .all(statement_allows_undefined_export_reuse)
}

fn push_effect_expression(block: &mut Block, expr: Expression) {
    match expr.desc {
        ExpressionDesc::Seq(left, right) => {
            push_effect_expression(block, *left);
            push_effect_expression(block, *right);
        }
        _ if js_expr_no_side_effects(&expr) => {}
        _ => block.push(Statement::exp(expr)),
    }
}

fn statement_allows_undefined_export_reuse(stmt: &Statement) -> bool {
    match &stmt.desc {
        StatementDesc::Variable(VariableDeclaration { value, .. }) => {
            value.as_ref().is_none_or(|expr| {
                !matches!(expr.desc, ExpressionDesc::Fun { .. }) && js_expr_no_side_effects(expr)
            })
        }
        _ => false,
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

fn block_terminates(block: &Block) -> bool {
    block.last().is_some_and(statement_terminates)
}

fn block_finishes_output(block: &Block) -> bool {
    block.last().is_some_and(statement_finishes_output)
}

fn statement_terminates(stmt: &Statement) -> bool {
    match &stmt.desc {
        StatementDesc::Block(block) => block_terminates(block),
        StatementDesc::Return(_)
        | StatementDesc::Throw(_)
        | StatementDesc::Break
        | StatementDesc::Continue => true,
        StatementDesc::If(_, then_block, else_block) => {
            !then_block.is_empty()
                && !else_block.is_empty()
                && block_terminates(then_block)
                && block_terminates(else_block)
        }
        StatementDesc::IntSwitch(_, cases, default) => {
            default.as_ref().is_some_and(block_terminates)
                && !cases.is_empty()
                && cases
                    .iter()
                    .all(|(_, clause)| block_terminates(&clause.body))
        }
        StatementDesc::StringSwitch(_, cases, default) => {
            default.as_ref().is_some_and(block_terminates)
                && !cases.is_empty()
                && cases
                    .iter()
                    .all(|clause| block_terminates(&clause.clause.body))
        }
        _ => false,
    }
}

fn statement_finishes_output(stmt: &Statement) -> bool {
    match &stmt.desc {
        StatementDesc::Block(block) => block_finishes_output(block),
        StatementDesc::Return(_) | StatementDesc::Throw(_) => true,
        StatementDesc::If(_, then_block, else_block) => {
            !then_block.is_empty()
                && !else_block.is_empty()
                && block_finishes_output(then_block)
                && block_finishes_output(else_block)
        }
        StatementDesc::IntSwitch(_, cases, default) => {
            default.as_ref().is_some_and(block_finishes_output)
                && !cases.is_empty()
                && cases
                    .iter()
                    .all(|(_, clause)| block_finishes_output(&clause.body))
        }
        StatementDesc::StringSwitch(_, cases, default) => {
            default.as_ref().is_some_and(block_finishes_output)
                && !cases.is_empty()
                && cases
                    .iter()
                    .all(|clause| block_finishes_output(&clause.clause.body))
        }
        _ => false,
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
                || switch.sw_consts.iter().any(|(_, body)| lambda_has_exit(body))
                || switch.sw_blocks.iter().any(|(_, body)| lambda_has_exit(body))
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
                || cases.iter().any(|(_, body)| lambda_contains_staticcatch(body))
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
                add_count(count, lambda_static_raise_count_to_label(value, label, arity))
            },
        ),
        Lambda::Lprim(info) => info.args.iter().fold(0, |count, arg| {
            add_count(count, lambda_static_raise_count_to_label(arg, label, arity))
        }),
        Lambda::Lswitch(scrut, switch) => {
            let mut count = lambda_static_raise_count_to_label(scrut, label, arity);
            for (_, body) in &switch.sw_consts {
                count = add_count(count, lambda_static_raise_count_to_label(body, label, arity));
            }
            for (_, body) in &switch.sw_blocks {
                count = add_count(count, lambda_static_raise_count_to_label(body, label, arity));
            }
            if let Some(body) = switch.sw_failaction.as_deref() {
                count = add_count(count, lambda_static_raise_count_to_label(body, label, arity));
            }
            count
        }
        Lambda::LstringSwitch(scrut, cases, default) => {
            let mut count = lambda_static_raise_count_to_label(scrut, label, arity);
            for (_, body) in cases {
                count = add_count(count, lambda_static_raise_count_to_label(body, label, arity));
            }
            if let Some(body) = default.as_deref() {
                count = add_count(count, lambda_static_raise_count_to_label(body, label, arity));
            }
            count
        }
        Lambda::LstaticRaise(raise_label, args) => {
            let self_count = usize::from(*raise_label == label && args.len() == arity);
            args.iter().fold(self_count, |count, arg| {
                add_count(count, lambda_static_raise_count_to_label(arg, label, arity))
            })
        }
        Lambda::LstaticCatch(body, (_, _), handler) | Lambda::LtryWith(body, _, handler) => add_count(
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
            add_count(count, lambda_static_raise_count_to_label(body, label, arity))
        }
        Lambda::Lassign(_, value) => lambda_static_raise_count_to_label(value, label, arity),
        Lambda::LifThenElse(cond, then_, else_) => {
            let count = add_count(
                lambda_static_raise_count_to_label(cond, label, arity),
                lambda_static_raise_count_to_label(then_, label, arity),
            );
            add_count(count, lambda_static_raise_count_to_label(else_, label, arity))
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

fn comparison_to_binop(cmp: Comparison) -> BinOp {
    match cmp {
        Comparison::Eq => BinOp::EqEqEq,
        Comparison::Neq => BinOp::NotEqEq,
        Comparison::Lt => BinOp::Lt,
        Comparison::Le => BinOp::Le,
        Comparison::Gt => BinOp::Gt,
        Comparison::Ge => BinOp::Ge,
    }
}

fn comparison_to_runtime_member(cmp: Comparison) -> &'static str {
    match cmp {
        Comparison::Eq => "equal",
        Comparison::Neq => "notequal",
        Comparison::Lt => "lessthan",
        Comparison::Le => "lessequal",
        Comparison::Gt => "greaterthan",
        Comparison::Ge => "greaterequal",
    }
}

fn runtime_member_for_eta_wrapped_primitive(
    primitive: &Primitive,
) -> Option<(&'static str, &'static str)> {
    match primitive {
        Primitive::Pobjcomp(cmp) => Some(("Primitive_object", comparison_to_runtime_member(*cmp))),
        Primitive::Pobjorder => Some(("Primitive_object", "compare")),
        Primitive::Pobjmin => Some(("Primitive_object", "min")),
        Primitive::Pobjmax => Some(("Primitive_object", "max")),
        Primitive::Pboolorder => Some(("Primitive_bool", "compare")),
        Primitive::Pboolmin => Some(("Primitive_bool", "min")),
        Primitive::Pboolmax => Some(("Primitive_bool", "max")),
        Primitive::Phash => Some(("Primitive_hash", "hash")),
        Primitive::PhashMixint => Some(("Primitive_hash", "hash_mix_int")),
        Primitive::PhashMixstring => Some(("Primitive_hash", "hash_mix_string")),
        Primitive::PhashFinalmix => Some(("Primitive_hash", "hash_final_mix")),
        Primitive::Pintorder => Some(("Primitive_int", "compare")),
        Primitive::Pintmin => Some(("Primitive_int", "min")),
        Primitive::Pintmax => Some(("Primitive_int", "max")),
        Primitive::Pfloatorder => Some(("Primitive_float", "compare")),
        Primitive::Pfloatmin => Some(("Primitive_float", "min")),
        Primitive::Pfloatmax => Some(("Primitive_float", "max")),
        Primitive::Pbigintorder => Some(("Primitive_bigint", "compare")),
        Primitive::Pbigintmin => Some(("Primitive_bigint", "min")),
        Primitive::Pbigintmax => Some(("Primitive_bigint", "max")),
        Primitive::Pstringorder => Some(("Primitive_string", "compare")),
        Primitive::Pstringmin => Some(("Primitive_string", "min")),
        Primitive::Pstringmax => Some(("Primitive_string", "max")),
        _ => None,
    }
}

fn eta_wrapped_args_match_params(params: &[Ident], args: &[Lambda]) -> bool {
    params.len() == args.len()
        && params.iter().zip(args).all(|(param, arg)| match arg {
            Lambda::Lvar(id) => id.same(param),
            Lambda::Lprim(crate::lambda::PrimInfo {
                primitive: Primitive::PjsFnMake(_) | Primitive::PjsFnMakeUnit,
                args: inner_args,
                ..
            }) => matches!(inner_args.as_slice(), [Lambda::Lvar(id)] if id.same(param)),
            _ => false,
        })
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum NullishLiteral {
    Null,
    Undefined,
}

fn is_nullish_literal(expr: &Expression) -> Option<NullishLiteral> {
    match expr.desc {
        ExpressionDesc::Null => Some(NullishLiteral::Null),
        ExpressionDesc::Undefined { .. } => Some(NullishLiteral::Undefined),
        _ => None,
    }
}

fn is_nullish_eq_impossible_non_null_expr(expr: &Expression) -> bool {
    matches!(
        expr.desc,
        ExpressionDesc::Bool(_)
            | ExpressionDesc::Number(_)
            | ExpressionDesc::Typeof(_)
            | ExpressionDesc::Fun { .. }
            | ExpressionDesc::Array(_, _)
            | ExpressionDesc::CamlBlock(_, _, _, _)
    ) && js_expr_no_side_effects(expr)
}

fn compile_nullish_strict_comparison(
    cmp: Comparison,
    left: Expression,
    right: Expression,
) -> Expression {
    match (is_nullish_literal(&left), is_nullish_literal(&right)) {
        (Some(NullishLiteral::Null), Some(NullishLiteral::Null))
        | (Some(NullishLiteral::Undefined), Some(NullishLiteral::Undefined)) => {
            return Expression::bool(matches!(cmp, Comparison::Eq));
        }
        (Some(NullishLiteral::Null), Some(NullishLiteral::Undefined))
        | (Some(NullishLiteral::Undefined), Some(NullishLiteral::Null)) => {
            return Expression::bool(matches!(cmp, Comparison::Neq));
        }
        _ => {}
    }

    if is_nullish_literal(&left).is_some() && is_nullish_eq_impossible_non_null_expr(&right) {
        return Expression::bool(matches!(cmp, Comparison::Neq));
    }

    if is_nullish_literal(&right).is_some() && is_nullish_eq_impossible_non_null_expr(&left) {
        return Expression::bool(matches!(cmp, Comparison::Neq));
    }

    Expression::bin(comparison_to_binop(cmp), left, right)
}

fn compile_raw_comparison(cmp: Comparison, left: Expression, right: Expression) -> Expression {
    Expression::bin(comparison_to_binop(cmp), left, right)
}

fn compare_bool_literals(cmp: Comparison, left: bool, right: bool) -> bool {
    match cmp {
        Comparison::Eq => left == right,
        Comparison::Neq => left != right,
        Comparison::Lt => left < right,
        Comparison::Le => left <= right,
        Comparison::Gt => left > right,
        Comparison::Ge => left >= right,
    }
}

fn compare_int_literals(cmp: Comparison, left: i32, right: i32) -> bool {
    match cmp {
        Comparison::Eq => left == right,
        Comparison::Neq => left != right,
        Comparison::Lt => left < right,
        Comparison::Le => left <= right,
        Comparison::Gt => left > right,
        Comparison::Ge => left >= right,
    }
}

fn compile_int_equality(left: Expression, right: Expression) -> Expression {
    match (&left.desc, &right.desc) {
        (
            ExpressionDesc::Number(Number::Float(left_float)),
            ExpressionDesc::Number(Number::Float(right_float)),
        ) if left_float.f == right_float.f => Expression::bool(true),
        _ => compile_raw_comparison(Comparison::Eq, left, right),
    }
}

fn runtime_compare_call_args(expr: &Expression) -> Option<(&Expression, &Expression)> {
    let ExpressionDesc::Call(func, args, _) = &expr.desc else {
        return None;
    };
    let ExpressionDesc::Var(VIdent::Qualified(module, Some(member))) = &func.desc else {
        return None;
    };
    if !matches!(module.kind, Kind::Runtime) || member != "compare" {
        return None;
    }

    match args.as_slice() {
        [left, right] => Some((left, right)),
        _ => None,
    }
}

fn compare_string_literals(left: &Expression, right: &Expression) -> Option<bool> {
    match (&left.desc, &right.desc) {
        (
            ExpressionDesc::Str {
                txt: left_txt,
                delim: left_delim,
            },
            ExpressionDesc::Str {
                txt: right_txt,
                delim: right_delim,
            },
        ) if left_delim == right_delim => {
            if left_txt == right_txt {
                Some(true)
            } else if is_simple_string_comparison(left_txt)
                && is_simple_string_comparison(right_txt)
            {
                Some(false)
            } else {
                None
            }
        }
        _ => None,
    }
}

fn is_simple_string_comparison(text: &str) -> bool {
    text.is_ascii() && !text.as_bytes().contains(&b'\\')
}

fn is_optional_block(expr: &Expression) -> bool {
    matches!(expr.desc, ExpressionDesc::OptionalBlock(_, _))
}

fn js_seq(left: Expression, right: Expression) -> Expression {
    match (&left.desc, &right.desc) {
        (ExpressionDesc::Seq(first, second), _)
            if matches!(
                second.as_ref().desc,
                ExpressionDesc::Number(_) | ExpressionDesc::Undefined { .. }
            ) =>
        {
            return js_seq(first.as_ref().clone(), right);
        }
        (ExpressionDesc::Seq(first, second), _)
            if matches!(
                first.as_ref().desc,
                ExpressionDesc::Number(_) | ExpressionDesc::Undefined { .. }
            ) =>
        {
            return js_seq(second.as_ref().clone(), right);
        }
        (_, ExpressionDesc::Seq(first, second))
            if matches!(
                first.as_ref().desc,
                ExpressionDesc::Number(_) | ExpressionDesc::Undefined { .. }
            ) =>
        {
            return js_seq(left, second.as_ref().clone());
        }
        (_, ExpressionDesc::Seq(first, second))
            if matches!(
                second.as_ref().desc,
                ExpressionDesc::Number(_) | ExpressionDesc::Undefined { .. }
            ) =>
        {
            return js_seq(
                js_seq(left, first.as_ref().clone()),
                second.as_ref().clone(),
            );
        }
        (
            ExpressionDesc::Number(_) | ExpressionDesc::Var(_) | ExpressionDesc::Undefined { .. },
            _,
        ) => return right,
        _ => (),
    }

    Expression::new(ExpressionDesc::Seq(Box::new(left), Box::new(right)))
}

fn bool_literal(expr: &Expression) -> Option<bool> {
    match expr.desc {
        ExpressionDesc::Bool(value) => Some(value),
        _ => None,
    }
}

fn both_bool_literals(left: &Expression, right: &Expression) -> bool {
    bool_literal(left).is_some() && bool_literal(right).is_some()
}

fn both_int_literals(left: &Expression, right: &Expression) -> bool {
    int_literal(left).is_some() && int_literal(right).is_some()
}

fn both_float_literals(left: &Expression, right: &Expression) -> bool {
    matches!(left.desc, ExpressionDesc::Number(Number::Float(_)))
        && matches!(right.desc, ExpressionDesc::Number(Number::Float(_)))
}

fn both_bigint_literals(left: &Expression, right: &Expression) -> bool {
    matches!(left.desc, ExpressionDesc::Number(Number::BigInt(_)))
        && matches!(right.desc, ExpressionDesc::Number(Number::BigInt(_)))
}

fn both_string_literals(left: &Expression, right: &Expression) -> bool {
    matches!(left.desc, ExpressionDesc::Str { .. })
        && matches!(right.desc, ExpressionDesc::Str { .. })
}

fn int_expr(value: i32) -> Expression {
    Expression::number(Number::int(value))
}

fn int_literal(expr: &Expression) -> Option<i32> {
    match &expr.desc {
        ExpressionDesc::Number(Number::Int { i, .. }) => Some(*i),
        _ => None,
    }
}

fn is_zero_int(expr: &Expression) -> bool {
    int_literal(expr) == Some(0)
}

fn positive_power_of_two_shift(value: i32) -> Option<u32> {
    if value <= 0 {
        return None;
    }

    let value = value as u32;
    if value.is_power_of_two() {
        Some(value.trailing_zeros())
    } else {
        None
    }
}

fn to_int32(expr: Expression) -> Expression {
    int32_bor(expr, int_expr(0))
}

fn int32_add(left: Expression, right: Expression) -> Expression {
    match (int_literal(&left), int_literal(&right)) {
        (Some(lhs), Some(rhs)) => int_expr(lhs.wrapping_add(rhs)),
        _ => to_int32(Expression::bin(BinOp::Plus, left, right)),
    }
}

fn int32_minus(left: Expression, right: Expression) -> Expression {
    match (int_literal(&left), int_literal(&right)) {
        (Some(lhs), Some(rhs)) => int_expr(lhs.wrapping_sub(rhs)),
        _ => to_int32(Expression::bin(BinOp::Minus, left, right)),
    }
}

fn int32_mul(left: Expression, right: Expression) -> Expression {
    match (int_literal(&left), int_literal(&right)) {
        (_, Some(0)) if expression_has_no_side_effects(&left) => int_expr(0),
        (Some(0), _) if expression_has_no_side_effects(&right) => int_expr(0),
        (Some(lhs), Some(rhs)) => int_expr(lhs.wrapping_mul(rhs)),
        (_, Some(rhs)) => match positive_power_of_two_shift(rhs) {
            Some(shift) => int32_lsl(left, int_expr(shift as i32)),
            None => to_int32(Expression::bin(BinOp::Mul, left, right)),
        },
        (Some(lhs), _) => match positive_power_of_two_shift(lhs) {
            Some(shift) => int32_lsl(right, int_expr(shift as i32)),
            None => to_int32(Expression::bin(BinOp::Mul, left, right)),
        },
        _ => to_int32(Expression::bin(BinOp::Mul, left, right)),
    }
}

fn ocaml_int32_pow(base: i32, exponent: i32) -> i32 {
    let result = (base as f64).powf(exponent as f64);
    if result > i32::MAX as f64 || result < i32::MIN as f64 {
        let wide = result.trunc() as i64;
        ((wide & 0xFFFF_FFFF) as u32) as i32
    } else {
        result.trunc() as i32
    }
}

fn int32_pow(left: Expression, right: Expression) -> Expression {
    match (int_literal(&left), int_literal(&right)) {
        (Some(lhs), Some(rhs)) => int_expr(ocaml_int32_pow(lhs, rhs)),
        _ => to_int32(Expression::bin(BinOp::Pow, left, right)),
    }
}

fn int32_div(left: Expression, right: Expression) -> Expression {
    to_int32(Expression::bin(BinOp::Div, left, right))
}

fn int32_mod(left: Expression, right: Expression) -> Expression {
    Expression::bin(BinOp::Mod, left, right)
}

fn int32_lsl(left: Expression, right: Expression) -> Expression {
    match (int_literal(&left), int_literal(&right)) {
        (Some(lhs), Some(rhs)) => int_expr(lhs.wrapping_shl(rhs as u32)),
        _ => Expression::bin(BinOp::Lsl, left, right),
    }
}

fn int32_bor(left: Expression, right: Expression) -> Expression {
    match (&left.desc, &right.desc) {
        (
            ExpressionDesc::Number(Number::Int { i: lhs, .. }),
            ExpressionDesc::Number(Number::Int { i: rhs, .. }),
        ) => int_expr(*lhs | *rhs),
        (_, ExpressionDesc::Bin(BinOp::Lsr, inner, shift)) if is_zero_int(shift.as_ref()) => {
            int32_bor(left, inner.as_ref().clone())
        }
        (ExpressionDesc::Bin(BinOp::Lsr, inner, shift), _) if is_zero_int(shift.as_ref()) => {
            int32_bor(inner.as_ref().clone(), right)
        }
        (ExpressionDesc::Bin(BinOp::Lsr, _, shift), _)
            if is_zero_int(&right)
                && int_literal(shift.as_ref()).is_some_and(|value| value > 0) =>
        {
            left
        }
        (ExpressionDesc::Bin(BinOp::Bor, inner, truncation), _)
            if is_zero_int(&right) && is_zero_int(truncation.as_ref()) =>
        {
            int32_bor(inner.as_ref().clone(), right)
        }
        _ => Expression::bin(BinOp::Bor, left, right),
    }
}

fn int32_lsr(left: Expression, right: Expression) -> Expression {
    match (&left.desc, &right.desc) {
        (
            ExpressionDesc::Number(Number::Int { i: lhs, .. }),
            ExpressionDesc::Number(Number::Int { i: rhs, .. }),
        ) => int_expr(((*lhs as u32) >> (*rhs as u32)) as i32),
        (ExpressionDesc::Bin(BinOp::Lsr, _, _), _) if is_zero_int(&right) => left,
        (ExpressionDesc::Bin(BinOp::Bor, inner, truncation), _)
            if is_zero_int(&right) && is_zero_int(truncation.as_ref()) =>
        {
            int32_lsr(inner.as_ref().clone(), right)
        }
        _ => to_int32(Expression::bin(BinOp::Lsr, left, right)),
    }
}

fn int32_bxor(left: Expression, right: Expression) -> Expression {
    match (&left.desc, &right.desc) {
        (
            ExpressionDesc::Number(Number::Int { i: lhs, .. }),
            ExpressionDesc::Number(Number::Int { i: rhs, .. }),
        ) => int_expr(*lhs ^ *rhs),
        (_, ExpressionDesc::Bin(BinOp::Lsr, inner, shift)) if is_zero_int(shift.as_ref()) => {
            int32_bxor(left, inner.as_ref().clone())
        }
        (ExpressionDesc::Bin(BinOp::Lsr, inner, shift), _) if is_zero_int(shift.as_ref()) => {
            int32_bxor(inner.as_ref().clone(), right)
        }
        _ => Expression::bin(BinOp::Bxor, left, right),
    }
}

fn int32_band(left: Expression, right: Expression) -> Expression {
    match &left.desc {
        ExpressionDesc::Bin(BinOp::Bor, inner, zero) if is_zero_int(zero.as_ref()) => {
            int32_band(inner.as_ref().clone(), right)
        }
        _ => Expression::bin(BinOp::Band, left, right),
    }
}

fn int32_offset(expr: Expression, offset: i32) -> Expression {
    if offset == 0 {
        expr
    } else {
        int32_add(expr, int_expr(offset))
    }
}

fn is_type_number_expr(expr: Expression) -> Expression {
    Expression::bin(
        BinOp::EqEqEq,
        Expression::new(ExpressionDesc::Typeof(Box::new(expr))),
        Expression::string("number"),
    )
}

fn poly_var_tag_access(target: &Expression) -> Expression {
    match &target.desc {
        ExpressionDesc::CamlBlock(items, _, _, _) if js_expr_no_side_effects(target) => items
            .first()
            .cloned()
            .expect("polyvariant tag access expects a tag element"),
        _ => Expression::new(ExpressionDesc::StaticIndex(
            Box::new(target.clone()),
            "NAME".to_string(),
            Some(0),
        )),
    }
}

fn poly_var_value_access(target: &Expression) -> Expression {
    match &target.desc {
        ExpressionDesc::CamlBlock(items, _, _, _) if js_expr_no_side_effects(target) => items
            .get(1)
            .cloned()
            .expect("polyvariant value access expects a payload element"),
        _ => Expression::new(ExpressionDesc::StaticIndex(
            Box::new(target.clone()),
            "VAL".to_string(),
            Some(1),
        )),
    }
}

fn external_polyvar_string_dispatch(dispatches: &[(String, String)], txt: &str) -> String {
    dispatches
        .iter()
        .find(|(source, _)| source == txt)
        .map(|(_, target)| target.clone())
        .unwrap_or_else(|| panic!("missing polyvariant string dispatch for {txt}"))
}

fn external_polyvar_int_dispatch(dispatches: &[(String, i64)], txt: &str) -> i64 {
    dispatches
        .iter()
        .find(|(source, _)| source == txt)
        .map(|(_, target)| *target)
        .unwrap_or_else(|| panic!("missing polyvariant int dispatch for {txt}"))
}

fn string_switch_iife(scrutinee: Expression, cases: Vec<(String, Expression)>) -> Expression {
    let clauses = cases
        .into_iter()
        .map(|(tag, value)| StringClause {
            tag_type: SwitchCaseTag::String(tag),
            clause: CaseClause {
                body: vec![Statement::return_(value)],
                should_break: false,
                comment: None,
            },
        })
        .collect();
    Expression::call(
        Expression::new(ExpressionDesc::Fun {
            is_method: false,
            params: vec![],
            body: vec![Statement::new(StatementDesc::StringSwitch(
                scrutinee, clauses, None,
            ))],
            env: Default::default(),
            return_unit: false,
            async_: false,
            directive: None,
        }),
        vec![],
        CallInfo::default(),
    )
}

fn is_type_object_expr(expr: Expression) -> Expression {
    Expression::bin(
        BinOp::EqEqEq,
        Expression::new(ExpressionDesc::Typeof(Box::new(expr))),
        Expression::string("object"),
    )
}

fn strict_eq_int(expr: Expression, value: i32) -> Expression {
    Expression::bin(BinOp::EqEqEq, expr, int_expr(value))
}

fn range_exclusion_or(expr: Expression, upper: i32, lower: i32) -> Expression {
    Expression::bin(
        BinOp::Or,
        Expression::bin(BinOp::Gt, expr.clone(), int_expr(upper)),
        Expression::bin(BinOp::Lt, expr, int_expr(lower)),
    )
}

fn is_out_expr(expr: Expression, range: Expression) -> Expression {
    match (int_literal(&range), &expr.desc) {
        (Some(1), ExpressionDesc::Var(_)) => Expression::not(Expression::bin(
            BinOp::Or,
            strict_eq_int(expr.clone(), 0),
            strict_eq_int(expr.clone(), 1),
        )),
        (Some(1), ExpressionDesc::Bin(BinOp::Plus, left, right)) => match (&left.desc, &right.desc)
        {
            (ExpressionDesc::Number(Number::Int { i, .. }), ExpressionDesc::Var(_)) => {
                Expression::not(Expression::bin(
                    BinOp::Or,
                    strict_eq_int(right.as_ref().clone(), i.wrapping_neg()),
                    strict_eq_int(right.as_ref().clone(), 1i32.wrapping_sub(*i)),
                ))
            }
            (ExpressionDesc::Var(_), ExpressionDesc::Number(Number::Int { i, .. })) => {
                Expression::not(Expression::bin(
                    BinOp::Or,
                    strict_eq_int(left.as_ref().clone(), i.wrapping_neg()),
                    strict_eq_int(left.as_ref().clone(), 1i32.wrapping_sub(*i)),
                ))
            }
            _ => Expression::bin(BinOp::Gt, expr, range),
        },
        (Some(1), ExpressionDesc::Bin(BinOp::Minus, left, right)) => {
            match (&left.desc, &right.desc) {
                (ExpressionDesc::Var(_), ExpressionDesc::Number(Number::Int { i, .. })) => {
                    Expression::not(Expression::bin(
                        BinOp::Or,
                        strict_eq_int(left.as_ref().clone(), i.wrapping_add(1)),
                        strict_eq_int(left.as_ref().clone(), *i),
                    ))
                }
                _ => Expression::bin(BinOp::Gt, expr, range),
            }
        }
        (Some(k), ExpressionDesc::Bin(BinOp::Minus, left, right)) => {
            match (&left.desc, &right.desc) {
                (ExpressionDesc::Var(_), ExpressionDesc::Number(Number::Int { i, .. })) => {
                    range_exclusion_or(left.as_ref().clone(), i.wrapping_add(k), *i)
                }
                _ => Expression::bin(BinOp::Gt, expr, range),
            }
        }
        (Some(k), ExpressionDesc::Var(_)) => range_exclusion_or(expr, k, 0),
        (_, ExpressionDesc::Bin(BinOp::Bor, inner, zero))
            if is_zero_int(zero.as_ref())
                && matches!(
                    inner.as_ref().desc,
                    ExpressionDesc::Bin(BinOp::Plus | BinOp::Minus, _, _)
                ) =>
        {
            is_out_expr(inner.as_ref().clone(), range)
        }
        _ => Expression::bin(BinOp::Gt, expr, range),
    }
}

fn int_bnot(expr: Expression) -> Expression {
    match int_literal(&expr) {
        Some(value) => int_expr(!value),
        None => Expression::new(ExpressionDesc::JsBnot(Box::new(expr))),
    }
}

fn apply_js_flatten_pass(mut deps: DepsProgram) -> DepsProgram {
    deps.program = flatten_program(deps.program);
    deps
}

fn apply_js_flatten_and_mark_dead_pass(mut deps: DepsProgram, jsx_preserve: bool) -> DepsProgram {
    let id_gen = IdGenerator::with_start_stamp(max_ident_stamp_in_program(&deps.program));
    deps.program = flatten_and_mark_dead_program(deps.program, &id_gen, jsx_preserve);
    deps
}

fn flatten_and_mark_dead_program(
    mut program: Program,
    id_gen: &IdGenerator,
    jsx_preserve: bool,
) -> Program {
    let mut substitution = HashMap::new();
    program.block =
        flatten_and_mark_dead_block(program.block, id_gen, &mut substitution, jsx_preserve);
    program.block = collapse_sync_component_make_aliases(program.block, &program.export_set);
    mark_dead_code(&mut program);
    program
}

fn collapse_sync_component_make_aliases(block: Block, export_set: &HashSet<Ident>) -> Block {
    let mut rewritten = Vec::with_capacity(block.len());
    let mut index = 0;

    while index < block.len() {
        let Some(current) = block.get(index) else {
            break;
        };
        let Some(next) = block.get(index + 1) else {
            rewritten.push(current.clone());
            break;
        };

        let StatementDesc::Variable(function_decl) = &current.desc else {
            rewritten.push(current.clone());
            index += 1;
            continue;
        };
        let StatementDesc::Variable(alias_decl) = &next.desc else {
            rewritten.push(current.clone());
            index += 1;
            continue;
        };

        let Some(Expression {
            desc: ExpressionDesc::Fun {
                async_, directive, ..
            },
            ..
        }) = &function_decl.value
        else {
            rewritten.push(current.clone());
            index += 1;
            continue;
        };

        if *async_
            || directive.is_some()
            || !is_make_like_binding_name(function_decl.ident.name())
            || !is_descriptive_component_binding_name(alias_decl.ident.name())
            || export_set.contains(&function_decl.ident)
            || !matches!(
                alias_decl.value.as_ref(),
                Some(Expression {
                    desc: ExpressionDesc::Var(VIdent::Id(id)),
                    ..
                }) if id.same(&function_decl.ident)
            )
            || expression_mentions_ident(
                function_decl
                    .value
                    .as_ref()
                    .expect("function value checked above"),
                &function_decl.ident,
            )
            || statements_mention_ident(&block[(index + 2)..], &function_decl.ident)
            || !export_set.contains(&alias_decl.ident)
                && !statements_mention_ident(&block[(index + 2)..], &alias_decl.ident)
        {
            rewritten.push(current.clone());
            index += 1;
            continue;
        }

        rewritten.push(Statement {
            desc: StatementDesc::Variable(VariableDeclaration {
                ident: alias_decl.ident.clone(),
                value: function_decl.value.clone(),
                property: function_decl.property,
                ident_info: function_decl.ident_info.clone(),
            }),
            comment: current.comment.clone().or_else(|| next.comment.clone()),
        });
        index += 2;
    }

    rewritten
}

fn is_make_like_binding_name(name: &str) -> bool {
    name == "make"
        || name
            .strip_prefix("make$")
            .is_some_and(|suffix| !suffix.is_empty() && suffix.chars().all(|c| c.is_ascii_digit()))
}

fn is_descriptive_component_binding_name(name: &str) -> bool {
    !is_make_like_binding_name(name)
        && name
            .chars()
            .next()
            .is_some_and(|first| first.is_ascii_uppercase())
}

fn statements_mention_ident(stmts: &[Statement], target: &Ident) -> bool {
    stmts
        .iter()
        .any(|stmt| statement_mentions_ident(stmt, target))
}

fn statement_mentions_ident(stmt: &Statement, target: &Ident) -> bool {
    match &stmt.desc {
        StatementDesc::Block(block) => statements_mention_ident(block, target),
        StatementDesc::Variable(VariableDeclaration { ident, value, .. }) => {
            ident.same(target)
                || value
                    .as_ref()
                    .is_some_and(|value| expression_mentions_ident(value, target))
        }
        StatementDesc::Exp(expr) | StatementDesc::Return(expr) | StatementDesc::Throw(expr) => {
            expression_mentions_ident(expr, target)
        }
        StatementDesc::If(cond, then_block, else_block) => {
            expression_mentions_ident(cond, target)
                || statements_mention_ident(then_block, target)
                || statements_mention_ident(else_block, target)
        }
        StatementDesc::While(cond, body) => {
            expression_mentions_ident(cond, target) || statements_mention_ident(body, target)
        }
        StatementDesc::ForRange(start, finish, loop_ident, _, body) => {
            loop_ident.same(target)
                || start
                    .as_ref()
                    .is_some_and(|start| expression_mentions_ident(start, target))
                || expression_mentions_ident(finish, target)
                || statements_mention_ident(body, target)
        }
        StatementDesc::IntSwitch(test, clauses, default) => {
            expression_mentions_ident(test, target)
                || clauses
                    .iter()
                    .any(|(_, clause)| statements_mention_ident(&clause.body, target))
                || default
                    .as_ref()
                    .is_some_and(|block| statements_mention_ident(block, target))
        }
        StatementDesc::StringSwitch(test, clauses, default) => {
            expression_mentions_ident(test, target)
                || clauses
                    .iter()
                    .any(|clause| statements_mention_ident(&clause.clause.body, target))
                || default
                    .as_ref()
                    .is_some_and(|block| statements_mention_ident(block, target))
        }
        StatementDesc::Try(body, catch, finally) => {
            statements_mention_ident(body, target)
                || catch.as_ref().is_some_and(|(catch_ident, catch_block)| {
                    catch_ident.same(target) || statements_mention_ident(catch_block, target)
                })
                || finally
                    .as_ref()
                    .is_some_and(|block| statements_mention_ident(block, target))
        }
        StatementDesc::Debugger | StatementDesc::Break | StatementDesc::Continue => false,
    }
}

fn expression_mentions_ident(expr: &Expression, target: &Ident) -> bool {
    match &expr.desc {
        ExpressionDesc::Var(VIdent::Id(ident)) => ident.same(target),
        ExpressionDesc::Var(VIdent::Qualified(_, _))
        | ExpressionDesc::Bool(_)
        | ExpressionDesc::Str { .. }
        | ExpressionDesc::Number(_)
        | ExpressionDesc::Undefined { .. }
        | ExpressionDesc::Null
        | ExpressionDesc::RawJsCode(_) => false,
        ExpressionDesc::Length(inner, _)
        | ExpressionDesc::IsNullOrUndefined(inner)
        | ExpressionDesc::Typeof(inner)
        | ExpressionDesc::JsNot(inner)
        | ExpressionDesc::JsBnot(inner)
        | ExpressionDesc::Spread(inner)
        | ExpressionDesc::Await(inner)
        | ExpressionDesc::OptionalBlock(inner, _)
        | ExpressionDesc::StaticIndex(inner, _, _)
        | ExpressionDesc::New(inner, None) => expression_mentions_ident(inner, target),
        ExpressionDesc::In(left, right)
        | ExpressionDesc::StringAppend(left, right)
        | ExpressionDesc::Seq(left, right)
        | ExpressionDesc::Bin(_, left, right)
        | ExpressionDesc::FlatCall(left, right)
        | ExpressionDesc::StringIndex(left, right)
        | ExpressionDesc::ArrayIndex(left, right) => {
            expression_mentions_ident(left, target) || expression_mentions_ident(right, target)
        }
        ExpressionDesc::Cond(test, consequent, alternate) => {
            expression_mentions_ident(test, target)
                || expression_mentions_ident(consequent, target)
                || expression_mentions_ident(alternate, target)
        }
        ExpressionDesc::Call(func, args, _)
        | ExpressionDesc::New(func, Some(args))
        | ExpressionDesc::TaggedTemplate(func, _, args) => {
            expression_mentions_ident(func, target)
                || args
                    .iter()
                    .any(|arg| expression_mentions_ident(arg, target))
        }
        ExpressionDesc::Fun { params, body, .. } => {
            params.iter().any(|param| param.same(target)) || statements_mention_ident(body, target)
        }
        ExpressionDesc::Array(items, _) => items
            .iter()
            .any(|item| expression_mentions_ident(item, target)),
        ExpressionDesc::CamlBlock(items, _, tag, _) => {
            expression_mentions_ident(tag, target)
                || items
                    .iter()
                    .any(|item| expression_mentions_ident(item, target))
        }
        ExpressionDesc::Object(dup, props) => {
            dup.as_deref()
                .is_some_and(|dup| expression_mentions_ident(dup, target))
                || props
                    .iter()
                    .any(|(_, value)| expression_mentions_ident(value, target))
        }
        ExpressionDesc::CamlBlockTag(inner, _) => expression_mentions_ident(inner, target),
    }
}

fn flatten_and_mark_dead_block(
    block: Block,
    id_gen: &IdGenerator,
    substitution: &mut HashMap<Ident, Expression>,
    jsx_preserve: bool,
) -> Block {
    block
        .into_iter()
        .map(|stmt| flatten_and_mark_dead_statement(stmt, id_gen, substitution, jsx_preserve))
        .collect()
}

fn flatten_and_mark_dead_statement(
    stmt: Statement,
    id_gen: &IdGenerator,
    substitution: &mut HashMap<Ident, Expression>,
    jsx_preserve: bool,
) -> Statement {
    let Statement { desc, comment } = stmt;
    match desc {
        StatementDesc::Variable(decl) => {
            if matches!(decl.ident_info.used_stats, UsedStats::DeadPure) {
                return Statement {
                    desc: StatementDesc::Block(vec![]),
                    comment,
                };
            }

            if matches!(decl.ident_info.used_stats, UsedStats::DeadNonPure) {
                return match decl.value {
                    None => Statement {
                        desc: StatementDesc::Block(vec![]),
                        comment,
                    },
                    Some(value) => Statement {
                        desc: StatementDesc::Exp(value),
                        comment,
                    },
                };
            }

            if matches!(
                decl.property,
                LetKind::Strict | LetKind::StrictOpt | LetKind::Alias
            ) {
                if let Some(Expression {
                    desc: ExpressionDesc::CamlBlock(items, MutableFlag::Immutable, tag, tag_info),
                    comment: value_comment,
                }) = decl.value
                {
                    if items.len() >= 2 {
                        let mut rewritten_items = Vec::with_capacity(items.len());
                        let mut bindings = Vec::new();

                        for (index, item) in items.into_iter().enumerate() {
                            if is_simple_block_binding_item(&item) {
                                rewritten_items.push(item);
                            } else {
                                let rewritten = flatten_and_mark_dead_expression(
                                    item,
                                    id_gen,
                                    substitution,
                                    jsx_preserve,
                                );
                                let temp = id_gen.create(&block_substitution_name(
                                    &decl.ident,
                                    &tag_info,
                                    index,
                                ));
                                rewritten_items.push(Expression::var(temp.clone()));
                                bindings.push(Statement::variable(VariableDeclaration {
                                    ident: temp,
                                    value: Some(rewritten),
                                    property: LetKind::Strict,
                                    ident_info: IdentInfo::default(),
                                }));
                            }
                        }

                        let rewritten_value = Expression {
                            desc: ExpressionDesc::CamlBlock(
                                rewritten_items,
                                MutableFlag::Immutable,
                                tag,
                                tag_info,
                            ),
                            comment: value_comment,
                        };
                        substitution.insert(decl.ident.clone(), rewritten_value.clone());

                        let original = Statement {
                            desc: StatementDesc::Variable(VariableDeclaration {
                                ident: decl.ident,
                                value: Some(rewritten_value),
                                property: decl.property,
                                ident_info: decl.ident_info,
                            }),
                            comment,
                        };

                        if bindings.is_empty() {
                            return original;
                        }

                        bindings.push(original);
                        return Statement {
                            desc: StatementDesc::Block(bindings),
                            comment: None,
                        };
                    }

                    return Statement {
                        desc: {
                            let rewritten_value = Expression {
                                desc: ExpressionDesc::CamlBlock(
                                    items,
                                    MutableFlag::Immutable,
                                    tag,
                                    tag_info,
                                ),
                                comment: value_comment,
                            };
                            substitution.insert(decl.ident.clone(), rewritten_value.clone());
                            StatementDesc::Variable(VariableDeclaration {
                                ident: decl.ident,
                                value: Some(rewritten_value),
                                property: decl.property,
                                ident_info: decl.ident_info,
                            })
                        },
                        comment,
                    };
                }
            }

            Statement {
                desc: StatementDesc::Variable(VariableDeclaration {
                    ident: decl.ident,
                    value: decl.value.map(|value| {
                        flatten_and_mark_dead_expression(value, id_gen, substitution, jsx_preserve)
                    }),
                    property: decl.property,
                    ident_info: decl.ident_info,
                }),
                comment,
            }
        }
        StatementDesc::Block(block) => Statement {
            desc: StatementDesc::Block(flatten_and_mark_dead_block(
                block,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            comment,
        },
        StatementDesc::Exp(expr) => Statement {
            desc: StatementDesc::Exp(flatten_and_mark_dead_expression(
                expr,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            comment,
        },
        StatementDesc::Return(expr) => Statement {
            desc: StatementDesc::Return(flatten_and_mark_dead_expression(
                expr,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            comment,
        },
        StatementDesc::If(cond, then_block, else_block) => Statement {
            desc: StatementDesc::If(
                flatten_and_mark_dead_expression(cond, id_gen, substitution, jsx_preserve),
                flatten_and_mark_dead_block(then_block, id_gen, substitution, jsx_preserve),
                flatten_and_mark_dead_block(else_block, id_gen, substitution, jsx_preserve),
            ),
            comment,
        },
        StatementDesc::While(cond, body) => Statement {
            desc: StatementDesc::While(
                flatten_and_mark_dead_expression(cond, id_gen, substitution, jsx_preserve),
                flatten_and_mark_dead_block(body, id_gen, substitution, jsx_preserve),
            ),
            comment,
        },
        StatementDesc::ForRange(start, finish, ident, direction, body) => Statement {
            desc: StatementDesc::ForRange(
                start.map(|expr| {
                    flatten_and_mark_dead_expression(expr, id_gen, substitution, jsx_preserve)
                }),
                flatten_and_mark_dead_expression(finish, id_gen, substitution, jsx_preserve),
                ident,
                direction,
                flatten_and_mark_dead_block(body, id_gen, substitution, jsx_preserve),
            ),
            comment,
        },
        StatementDesc::IntSwitch(test, clauses, default) => Statement {
            desc: StatementDesc::IntSwitch(
                flatten_and_mark_dead_expression(test, id_gen, substitution, jsx_preserve),
                clauses
                    .into_iter()
                    .map(|(tag, clause)| {
                        (
                            tag,
                            CaseClause {
                                body: flatten_and_mark_dead_block(
                                    clause.body,
                                    id_gen,
                                    substitution,
                                    jsx_preserve,
                                ),
                                should_break: clause.should_break,
                                comment: clause.comment,
                            },
                        )
                    })
                    .collect(),
                default.map(|block| {
                    flatten_and_mark_dead_block(block, id_gen, substitution, jsx_preserve)
                }),
            ),
            comment,
        },
        StatementDesc::StringSwitch(test, clauses, default) => Statement {
            desc: StatementDesc::StringSwitch(
                flatten_and_mark_dead_expression(test, id_gen, substitution, jsx_preserve),
                clauses
                    .into_iter()
                    .map(|clause| crate::js_ir::StringClause {
                        tag_type: clause.tag_type,
                        clause: CaseClause {
                            body: flatten_and_mark_dead_block(
                                clause.clause.body,
                                id_gen,
                                substitution,
                                jsx_preserve,
                            ),
                            should_break: clause.clause.should_break,
                            comment: clause.clause.comment,
                        },
                    })
                    .collect(),
                default.map(|block| {
                    flatten_and_mark_dead_block(block, id_gen, substitution, jsx_preserve)
                }),
            ),
            comment,
        },
        StatementDesc::Throw(expr) => Statement {
            desc: StatementDesc::Throw(flatten_and_mark_dead_expression(
                expr,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            comment,
        },
        StatementDesc::Try(body, catch, finally) => Statement {
            desc: StatementDesc::Try(
                flatten_and_mark_dead_block(body, id_gen, substitution, jsx_preserve),
                catch.map(|(ident, block)| {
                    (
                        ident,
                        flatten_and_mark_dead_block(block, id_gen, substitution, jsx_preserve),
                    )
                }),
                finally.map(|block| {
                    flatten_and_mark_dead_block(block, id_gen, substitution, jsx_preserve)
                }),
            ),
            comment,
        },
        StatementDesc::Debugger => Statement {
            desc: StatementDesc::Debugger,
            comment,
        },
        StatementDesc::Break => Statement {
            desc: StatementDesc::Break,
            comment,
        },
        StatementDesc::Continue => Statement {
            desc: StatementDesc::Continue,
            comment,
        },
    }
}

fn flatten_and_mark_dead_expression(
    expr: Expression,
    id_gen: &IdGenerator,
    substitution: &mut HashMap<Ident, Expression>,
    jsx_preserve: bool,
) -> Expression {
    if let Some(rewritten) = try_substitute_caml_block_projection(&expr, substitution) {
        return rewritten;
    }

    let Expression { desc, comment } = expr;
    let desc = match desc {
        ExpressionDesc::Length(inner, object) => ExpressionDesc::Length(
            Box::new(flatten_and_mark_dead_expression(
                *inner,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            object,
        ),
        ExpressionDesc::IsNullOrUndefined(inner) => ExpressionDesc::IsNullOrUndefined(Box::new(
            flatten_and_mark_dead_expression(*inner, id_gen, substitution, jsx_preserve),
        )),
        ExpressionDesc::StringAppend(left, right) => ExpressionDesc::StringAppend(
            Box::new(flatten_and_mark_dead_expression(
                *left,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            Box::new(flatten_and_mark_dead_expression(
                *right,
                id_gen,
                substitution,
                jsx_preserve,
            )),
        ),
        ExpressionDesc::Bool(value) => ExpressionDesc::Bool(value),
        ExpressionDesc::Typeof(inner) => ExpressionDesc::Typeof(Box::new(
            flatten_and_mark_dead_expression(*inner, id_gen, substitution, jsx_preserve),
        )),
        ExpressionDesc::In(left, right) => ExpressionDesc::In(
            Box::new(flatten_and_mark_dead_expression(
                *left,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            Box::new(flatten_and_mark_dead_expression(
                *right,
                id_gen,
                substitution,
                jsx_preserve,
            )),
        ),
        ExpressionDesc::JsNot(inner) => ExpressionDesc::JsNot(Box::new(
            flatten_and_mark_dead_expression(*inner, id_gen, substitution, jsx_preserve),
        )),
        ExpressionDesc::JsBnot(inner) => ExpressionDesc::JsBnot(Box::new(
            flatten_and_mark_dead_expression(*inner, id_gen, substitution, jsx_preserve),
        )),
        ExpressionDesc::Seq(left, right) => ExpressionDesc::Seq(
            Box::new(flatten_and_mark_dead_expression(
                *left,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            Box::new(flatten_and_mark_dead_expression(
                *right,
                id_gen,
                substitution,
                jsx_preserve,
            )),
        ),
        ExpressionDesc::Cond(test, consequent, alternate) => ExpressionDesc::Cond(
            Box::new(flatten_and_mark_dead_expression(
                *test,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            Box::new(flatten_and_mark_dead_expression(
                *consequent,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            Box::new(flatten_and_mark_dead_expression(
                *alternate,
                id_gen,
                substitution,
                jsx_preserve,
            )),
        ),
        ExpressionDesc::Bin(op, left, right) => ExpressionDesc::Bin(
            op,
            Box::new(flatten_and_mark_dead_expression(
                *left,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            Box::new(flatten_and_mark_dead_expression(
                *right,
                id_gen,
                substitution,
                jsx_preserve,
            )),
        ),
        ExpressionDesc::FlatCall(func, args) => ExpressionDesc::FlatCall(
            Box::new(flatten_and_mark_dead_expression(
                *func,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            Box::new(flatten_and_mark_dead_expression(
                *args,
                id_gen,
                substitution,
                jsx_preserve,
            )),
        ),
        ExpressionDesc::Call(func, args, info) => ExpressionDesc::Call(
            Box::new(flatten_and_mark_dead_expression(
                *func,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            args.into_iter()
                .enumerate()
                .map(|(index, arg)| {
                    if jsx_preserve && info.call_transformed_jsx && index == 0 {
                        flatten_and_mark_dead_transformed_jsx_tag_expression(
                            arg,
                            id_gen,
                            substitution,
                            jsx_preserve,
                        )
                    } else {
                        flatten_and_mark_dead_expression(arg, id_gen, substitution, jsx_preserve)
                    }
                })
                .collect(),
            info,
        ),
        ExpressionDesc::StringIndex(left, right) => ExpressionDesc::StringIndex(
            Box::new(flatten_and_mark_dead_expression(
                *left,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            Box::new(flatten_and_mark_dead_expression(
                *right,
                id_gen,
                substitution,
                jsx_preserve,
            )),
        ),
        ExpressionDesc::ArrayIndex(left, right) => ExpressionDesc::ArrayIndex(
            Box::new(flatten_and_mark_dead_expression(
                *left,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            Box::new(flatten_and_mark_dead_expression(
                *right,
                id_gen,
                substitution,
                jsx_preserve,
            )),
        ),
        ExpressionDesc::TaggedTemplate(tag, strings, values) => ExpressionDesc::TaggedTemplate(
            Box::new(flatten_and_mark_dead_expression(
                *tag,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            strings
                .into_iter()
                .map(|value| {
                    flatten_and_mark_dead_expression(value, id_gen, substitution, jsx_preserve)
                })
                .collect(),
            values
                .into_iter()
                .map(|value| {
                    flatten_and_mark_dead_expression(value, id_gen, substitution, jsx_preserve)
                })
                .collect(),
        ),
        ExpressionDesc::StaticIndex(target, field, pos) => ExpressionDesc::StaticIndex(
            Box::new(flatten_and_mark_dead_expression(
                *target,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            field,
            pos,
        ),
        ExpressionDesc::New(target, args) => ExpressionDesc::New(
            Box::new(flatten_and_mark_dead_expression(
                *target,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            args.map(|items| {
                items
                    .into_iter()
                    .map(|arg| {
                        flatten_and_mark_dead_expression(arg, id_gen, substitution, jsx_preserve)
                    })
                    .collect()
            }),
        ),
        ExpressionDesc::Var(var) => ExpressionDesc::Var(var),
        ExpressionDesc::Fun {
            is_method,
            params,
            body,
            env,
            return_unit,
            async_,
            directive,
        } => ExpressionDesc::Fun {
            is_method,
            params,
            body: flatten_and_mark_dead_block(body, id_gen, substitution, jsx_preserve),
            env,
            return_unit,
            async_,
            directive,
        },
        ExpressionDesc::Str { delim, txt } => ExpressionDesc::Str { delim, txt },
        ExpressionDesc::RawJsCode(info) => ExpressionDesc::RawJsCode(info),
        ExpressionDesc::Array(items, mutable_flag) => ExpressionDesc::Array(
            items
                .into_iter()
                .map(|item| {
                    flatten_and_mark_dead_expression(item, id_gen, substitution, jsx_preserve)
                })
                .collect(),
            mutable_flag,
        ),
        ExpressionDesc::OptionalBlock(inner, flag) => ExpressionDesc::OptionalBlock(
            Box::new(flatten_and_mark_dead_expression(
                *inner,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            flag,
        ),
        ExpressionDesc::CamlBlock(items, mutable_flag, tag, tag_info) => ExpressionDesc::CamlBlock(
            items
                .into_iter()
                .map(|item| {
                    flatten_and_mark_dead_expression(item, id_gen, substitution, jsx_preserve)
                })
                .collect(),
            mutable_flag,
            Box::new(flatten_and_mark_dead_expression(
                *tag,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            tag_info,
        ),
        ExpressionDesc::CamlBlockTag(inner, tag) => ExpressionDesc::CamlBlockTag(
            Box::new(flatten_and_mark_dead_expression(
                *inner,
                id_gen,
                substitution,
                jsx_preserve,
            )),
            tag,
        ),
        ExpressionDesc::Number(number) => ExpressionDesc::Number(number),
        ExpressionDesc::Object(dup, props) => ExpressionDesc::Object(
            dup.map(|expr| {
                Box::new(flatten_and_mark_dead_expression(
                    *expr,
                    id_gen,
                    substitution,
                    jsx_preserve,
                ))
            }),
            props
                .into_iter()
                .map(|(name, value)| {
                    (
                        name,
                        flatten_and_mark_dead_expression(value, id_gen, substitution, jsx_preserve),
                    )
                })
                .collect(),
        ),
        ExpressionDesc::Undefined { is_unit } => ExpressionDesc::Undefined { is_unit },
        ExpressionDesc::Null => ExpressionDesc::Null,
        ExpressionDesc::Await(inner) => ExpressionDesc::Await(Box::new(
            flatten_and_mark_dead_expression(*inner, id_gen, substitution, jsx_preserve),
        )),
        ExpressionDesc::Spread(inner) => ExpressionDesc::Spread(Box::new(
            flatten_and_mark_dead_expression(*inner, id_gen, substitution, jsx_preserve),
        )),
    };

    Expression { desc, comment }
}

fn flatten_and_mark_dead_transformed_jsx_tag_expression(
    expr: Expression,
    id_gen: &IdGenerator,
    substitution: &mut HashMap<Ident, Expression>,
    jsx_preserve: bool,
) -> Expression {
    let Expression { desc, comment } = expr;
    match desc {
        // OCaml's js_pass_flatten_and_mark_dead preserves component `.make`
        // projections in JSX-preserve mode so the dumper can print `<Foo.make />`.
        ExpressionDesc::StaticIndex(target, field, Some(index)) if field == "make" => Expression {
            desc: ExpressionDesc::StaticIndex(
                Box::new(flatten_and_mark_dead_expression(
                    *target,
                    id_gen,
                    substitution,
                    jsx_preserve,
                )),
                field,
                Some(index),
            ),
            comment,
        },
        other => flatten_and_mark_dead_expression(
            Expression {
                desc: other,
                comment,
            },
            id_gen,
            substitution,
            jsx_preserve,
        ),
    }
}

fn try_substitute_caml_block_projection(
    expr: &Expression,
    substitution: &HashMap<Ident, Expression>,
) -> Option<Expression> {
    match &expr.desc {
        ExpressionDesc::ArrayIndex(left, right) => {
            let ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)) = &left.desc else {
                return None;
            };
            let ExpressionDesc::Number(Number::Int { i, .. }) = right.desc else {
                return None;
            };
            substituted_caml_block_item(substitution, id, i)
        }
        ExpressionDesc::StaticIndex(target, _, Some(index)) => {
            let ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)) = &target.desc else {
                return None;
            };
            substituted_caml_block_item(substitution, id, *index)
        }
        _ => None,
    }
}

fn substituted_caml_block_item(
    substitution: &HashMap<Ident, Expression>,
    id: &Ident,
    index: i32,
) -> Option<Expression> {
    let expression = substitution.get(id)?;
    let ExpressionDesc::CamlBlock(items, MutableFlag::Immutable, _, _) = &expression.desc else {
        return None;
    };
    let item = items.get(usize::try_from(index).ok()?)?;
    is_simple_substituted_index_value(item).then(|| item.clone())
}

fn is_simple_block_binding_item(expr: &Expression) -> bool {
    match &expr.desc {
        ExpressionDesc::Var(_)
        | ExpressionDesc::Number(_)
        | ExpressionDesc::Str { .. }
        | ExpressionDesc::Bool(_)
        | ExpressionDesc::Undefined { .. } => true,
        ExpressionDesc::OptionalBlock(inner, true) => is_simple_block_binding_item(inner),
        ExpressionDesc::CamlBlock(
            items,
            MutableFlag::Immutable,
            _,
            TagInfo::Constructor { .. },
        ) => {
            items.iter().all(is_simple_block_binding_item)
        }
        _ => false,
    }
}

fn is_simple_substituted_index_value(expr: &Expression) -> bool {
    match &expr.desc {
        ExpressionDesc::Var(_)
        | ExpressionDesc::Number(_)
        | ExpressionDesc::Str { .. }
        | ExpressionDesc::Undefined { .. } => true,
        ExpressionDesc::OptionalBlock(inner, true) => is_simple_substituted_index_value(inner),
        ExpressionDesc::CamlBlock(
            items,
            MutableFlag::Immutable,
            _,
            TagInfo::Constructor { .. },
        ) => {
            items.iter().all(is_simple_substituted_index_value)
        }
        _ => false,
    }
}

fn block_substitution_name(ident: &Ident, tag_info: &TagInfo, index: usize) -> String {
    let suffix = match tag_info {
        TagInfo::Module(fields) => fields
            .get(index)
            .cloned()
            .unwrap_or_else(|| index.to_string()),
        TagInfo::Record { fields, .. } => fields
            .get(index)
            .map(|(field, _)| field.clone())
            .unwrap_or_else(|| index.to_string()),
        _ => index.to_string(),
    };
    format!("{}_{}", ident.name(), suffix)
}

fn max_ident_stamp_in_program(program: &Program) -> i32 {
    program.exports.iter().fold(
        max_ident_stamp_in_block(&program.block),
        |max_stamp, export| max_stamp.max(export.stamp()),
    )
}

#[derive(Debug, Clone, Copy)]
enum MarkDeadInfo {
    Recursive,
    Info {
        pure: bool,
        used: bool,
        exported: bool,
    },
}

fn mark_dead_code(program: &mut Program) {
    let mut states = HashMap::new();
    collect_mark_dead_states_block(&program.block, &program.export_set, &mut states);
    apply_mark_dead_states_block(&mut program.block, &states);
}

fn collect_mark_dead_states_block(
    block: &Block,
    export_set: &HashSet<Ident>,
    states: &mut HashMap<Ident, MarkDeadInfo>,
) {
    for stmt in block {
        collect_mark_dead_states_statement(stmt, export_set, states);
    }
}

fn collect_mark_dead_states_statement(
    stmt: &Statement,
    export_set: &HashSet<Ident>,
    states: &mut HashMap<Ident, MarkDeadInfo>,
) {
    match &stmt.desc {
        StatementDesc::Block(block) => collect_mark_dead_states_block(block, export_set, states),
        StatementDesc::Variable(decl) => {
            collect_mark_dead_states_variable(decl, export_set, states)
        }
        StatementDesc::Exp(expr) | StatementDesc::Return(expr) | StatementDesc::Throw(expr) => {
            collect_mark_dead_states_expression(expr, states);
        }
        StatementDesc::If(cond, then_block, else_block) => {
            collect_mark_dead_states_expression(cond, states);
            collect_mark_dead_states_block(then_block, export_set, states);
            collect_mark_dead_states_block(else_block, export_set, states);
        }
        StatementDesc::While(cond, body) => {
            collect_mark_dead_states_expression(cond, states);
            collect_mark_dead_states_block(body, export_set, states);
        }
        StatementDesc::ForRange(start, finish, _, _, body) => {
            if let Some(start) = start {
                collect_mark_dead_states_expression(start, states);
            }
            collect_mark_dead_states_expression(finish, states);
            collect_mark_dead_states_block(body, export_set, states);
        }
        StatementDesc::IntSwitch(test, clauses, default) => {
            collect_mark_dead_states_expression(test, states);
            for (_, clause) in clauses {
                collect_mark_dead_states_block(&clause.body, export_set, states);
            }
            if let Some(default) = default {
                collect_mark_dead_states_block(default, export_set, states);
            }
        }
        StatementDesc::StringSwitch(test, clauses, default) => {
            collect_mark_dead_states_expression(test, states);
            for clause in clauses {
                collect_mark_dead_states_block(&clause.clause.body, export_set, states);
            }
            if let Some(default) = default {
                collect_mark_dead_states_block(default, export_set, states);
            }
        }
        StatementDesc::Try(body, catch, finally) => {
            collect_mark_dead_states_block(body, export_set, states);
            if let Some((_, block)) = catch {
                collect_mark_dead_states_block(block, export_set, states);
            }
            if let Some(block) = finally {
                collect_mark_dead_states_block(block, export_set, states);
            }
        }
        StatementDesc::Debugger | StatementDesc::Break | StatementDesc::Continue => {}
    }
}

fn collect_mark_dead_states_variable(
    decl: &VariableDeclaration,
    export_set: &HashSet<Ident>,
    states: &mut HashMap<Ident, MarkDeadInfo>,
) {
    match decl.ident_info.used_stats {
        UsedStats::DeadPure => return,
        UsedStats::DeadNonPure => {
            if let Some(value) = &decl.value {
                collect_mark_dead_states_expression(value, states);
            }
            return;
        }
        _ => {}
    }

    let pure = match &decl.value {
        None => true,
        Some(value) => {
            collect_mark_dead_states_expression(value, states);
            js_expr_no_side_effects(value)
        }
    };
    let exported = export_set.contains(&decl.ident);
    match states.get(&decl.ident).copied() {
        Some(MarkDeadInfo::Recursive) => {
            states.insert(
                decl.ident.clone(),
                MarkDeadInfo::Info {
                    pure,
                    used: true,
                    exported,
                },
            );
        }
        Some(MarkDeadInfo::Info { .. }) => {}
        None => {
            states.insert(
                decl.ident.clone(),
                MarkDeadInfo::Info {
                    pure,
                    used: false,
                    exported,
                },
            );
        }
    }
}

fn collect_mark_dead_states_expression(
    expr: &Expression,
    states: &mut HashMap<Ident, MarkDeadInfo>,
) {
    match &expr.desc {
        ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)) => mark_dead_ident_use(id, states),
        ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(_, _))
        | ExpressionDesc::Undefined { .. }
        | ExpressionDesc::Null
        | ExpressionDesc::Bool(_)
        | ExpressionDesc::Str { .. }
        | ExpressionDesc::RawJsCode(_)
        | ExpressionDesc::Number(_) => {}
        ExpressionDesc::Length(inner, _)
        | ExpressionDesc::IsNullOrUndefined(inner)
        | ExpressionDesc::Typeof(inner)
        | ExpressionDesc::JsNot(inner)
        | ExpressionDesc::JsBnot(inner)
        | ExpressionDesc::CamlBlockTag(inner, _)
        | ExpressionDesc::OptionalBlock(inner, _)
        | ExpressionDesc::Await(inner)
        | ExpressionDesc::Spread(inner) => collect_mark_dead_states_expression(inner, states),
        ExpressionDesc::StringAppend(left, right)
        | ExpressionDesc::In(left, right)
        | ExpressionDesc::Seq(left, right)
        | ExpressionDesc::Bin(_, left, right)
        | ExpressionDesc::FlatCall(left, right)
        | ExpressionDesc::StringIndex(left, right)
        | ExpressionDesc::ArrayIndex(left, right) => {
            collect_mark_dead_states_expression(left, states);
            collect_mark_dead_states_expression(right, states);
        }
        ExpressionDesc::Cond(test, consequent, alternate) => {
            collect_mark_dead_states_expression(test, states);
            collect_mark_dead_states_expression(consequent, states);
            collect_mark_dead_states_expression(alternate, states);
        }
        ExpressionDesc::Call(func, args, _) => {
            collect_mark_dead_states_expression(func, states);
            for arg in args {
                collect_mark_dead_states_expression(arg, states);
            }
        }
        ExpressionDesc::TaggedTemplate(tag, strings, values) => {
            collect_mark_dead_states_expression(tag, states);
            for string in strings {
                collect_mark_dead_states_expression(string, states);
            }
            for value in values {
                collect_mark_dead_states_expression(value, states);
            }
        }
        ExpressionDesc::StaticIndex(target, _, _) => {
            collect_mark_dead_states_expression(target, states)
        }
        ExpressionDesc::New(target, args) => {
            collect_mark_dead_states_expression(target, states);
            if let Some(args) = args {
                for arg in args {
                    collect_mark_dead_states_expression(arg, states);
                }
            }
        }
        ExpressionDesc::Fun { body, .. } => {
            for stmt in body {
                collect_mark_dead_states_statement(stmt, &HashSet::new(), states);
            }
        }
        ExpressionDesc::Array(items, _) => {
            for item in items {
                collect_mark_dead_states_expression(item, states);
            }
        }
        ExpressionDesc::CamlBlock(items, _, tag, _) => {
            for item in items {
                collect_mark_dead_states_expression(item, states);
            }
            collect_mark_dead_states_expression(tag, states);
        }
        ExpressionDesc::Object(dup, props) => {
            if let Some(dup) = dup {
                collect_mark_dead_states_expression(dup, states);
            }
            for (_, value) in props {
                collect_mark_dead_states_expression(value, states);
            }
        }
    }
}

fn mark_dead_ident_use(id: &Ident, states: &mut HashMap<Ident, MarkDeadInfo>) {
    match states.get_mut(id) {
        None => {
            states.insert(id.clone(), MarkDeadInfo::Recursive);
        }
        Some(MarkDeadInfo::Recursive) => {}
        Some(MarkDeadInfo::Info { used, .. }) => {
            *used = true;
        }
    }
}

fn apply_mark_dead_states_block(block: &mut Block, states: &HashMap<Ident, MarkDeadInfo>) {
    for stmt in block {
        apply_mark_dead_states_statement(stmt, states);
    }
}

fn apply_mark_dead_states_statement(stmt: &mut Statement, states: &HashMap<Ident, MarkDeadInfo>) {
    match &mut stmt.desc {
        StatementDesc::Block(block) => apply_mark_dead_states_block(block, states),
        StatementDesc::Variable(decl) => {
            apply_mark_dead_states_variable(decl, states);
            if let Some(value) = &mut decl.value {
                apply_mark_dead_states_expression(value, states);
            }
        }
        StatementDesc::Exp(expr) | StatementDesc::Return(expr) | StatementDesc::Throw(expr) => {
            apply_mark_dead_states_expression(expr, states);
        }
        StatementDesc::If(_, then_block, else_block) => {
            apply_mark_dead_states_block(then_block, states);
            apply_mark_dead_states_block(else_block, states);
        }
        StatementDesc::While(_, body) => apply_mark_dead_states_block(body, states),
        StatementDesc::ForRange(_, _, _, _, body) => apply_mark_dead_states_block(body, states),
        StatementDesc::IntSwitch(_, clauses, default) => {
            for (_, clause) in clauses {
                apply_mark_dead_states_block(&mut clause.body, states);
            }
            if let Some(default) = default {
                apply_mark_dead_states_block(default, states);
            }
        }
        StatementDesc::StringSwitch(_, clauses, default) => {
            for clause in clauses {
                apply_mark_dead_states_block(&mut clause.clause.body, states);
            }
            if let Some(default) = default {
                apply_mark_dead_states_block(default, states);
            }
        }
        StatementDesc::Try(body, catch, finally) => {
            apply_mark_dead_states_block(body, states);
            if let Some((_, block)) = catch {
                apply_mark_dead_states_block(block, states);
            }
            if let Some(block) = finally {
                apply_mark_dead_states_block(block, states);
            }
        }
        StatementDesc::Debugger | StatementDesc::Break | StatementDesc::Continue => {}
    }
}

fn apply_mark_dead_states_variable(
    decl: &mut VariableDeclaration,
    states: &HashMap<Ident, MarkDeadInfo>,
) {
    let Some(MarkDeadInfo::Info {
        pure,
        used,
        exported,
    }) = states.get(&decl.ident).copied()
    else {
        return;
    };

    let status = if exported {
        UsedStats::Exported
    } else if used {
        UsedStats::Used
    } else if pure {
        UsedStats::DeadPure
    } else {
        UsedStats::DeadNonPure
    };
    update_used_stats(&mut decl.ident_info, status);
}

fn apply_mark_dead_states_expression(expr: &mut Expression, states: &HashMap<Ident, MarkDeadInfo>) {
    match &mut expr.desc {
        ExpressionDesc::Length(inner, _)
        | ExpressionDesc::IsNullOrUndefined(inner)
        | ExpressionDesc::Typeof(inner)
        | ExpressionDesc::JsNot(inner)
        | ExpressionDesc::JsBnot(inner)
        | ExpressionDesc::CamlBlockTag(inner, _)
        | ExpressionDesc::OptionalBlock(inner, _)
        | ExpressionDesc::Await(inner)
        | ExpressionDesc::Spread(inner) => apply_mark_dead_states_expression(inner, states),
        ExpressionDesc::StringAppend(left, right)
        | ExpressionDesc::In(left, right)
        | ExpressionDesc::Seq(left, right)
        | ExpressionDesc::Bin(_, left, right)
        | ExpressionDesc::FlatCall(left, right)
        | ExpressionDesc::StringIndex(left, right)
        | ExpressionDesc::ArrayIndex(left, right) => {
            apply_mark_dead_states_expression(left, states);
            apply_mark_dead_states_expression(right, states);
        }
        ExpressionDesc::Cond(test, consequent, alternate) => {
            apply_mark_dead_states_expression(test, states);
            apply_mark_dead_states_expression(consequent, states);
            apply_mark_dead_states_expression(alternate, states);
        }
        ExpressionDesc::Call(func, args, _) => {
            apply_mark_dead_states_expression(func, states);
            for arg in args {
                apply_mark_dead_states_expression(arg, states);
            }
        }
        ExpressionDesc::TaggedTemplate(tag, strings, values) => {
            apply_mark_dead_states_expression(tag, states);
            for string in strings {
                apply_mark_dead_states_expression(string, states);
            }
            for value in values {
                apply_mark_dead_states_expression(value, states);
            }
        }
        ExpressionDesc::StaticIndex(target, _, _) => {
            apply_mark_dead_states_expression(target, states)
        }
        ExpressionDesc::New(target, args) => {
            apply_mark_dead_states_expression(target, states);
            if let Some(args) = args {
                for arg in args {
                    apply_mark_dead_states_expression(arg, states);
                }
            }
        }
        ExpressionDesc::Fun { body, .. } => apply_mark_dead_states_block(body, states),
        ExpressionDesc::Array(items, _) => {
            for item in items {
                apply_mark_dead_states_expression(item, states);
            }
        }
        ExpressionDesc::CamlBlock(items, _, tag, _) => {
            for item in items {
                apply_mark_dead_states_expression(item, states);
            }
            apply_mark_dead_states_expression(tag, states);
        }
        ExpressionDesc::Object(dup, props) => {
            if let Some(dup) = dup {
                apply_mark_dead_states_expression(dup, states);
            }
            for (_, value) in props {
                apply_mark_dead_states_expression(value, states);
            }
        }
        ExpressionDesc::Var(_)
        | ExpressionDesc::Undefined { .. }
        | ExpressionDesc::Null
        | ExpressionDesc::Bool(_)
        | ExpressionDesc::Str { .. }
        | ExpressionDesc::RawJsCode(_)
        | ExpressionDesc::Number(_) => {}
    }
}

fn update_used_stats(info: &mut IdentInfo, status: UsedStats) {
    if matches!(
        info.used_stats,
        UsedStats::DeadPure | UsedStats::DeadNonPure | UsedStats::Exported
    ) {
        return;
    }
    info.used_stats = status;
}

fn flatten_program(mut program: Program) -> Program {
    program.block = flatten_block(program.block);
    program
}

fn flatten_block(block: Block) -> Block {
    let mut flattened = Vec::new();

    for stmt in block {
        match flatten_statement(stmt) {
            Statement {
                desc: StatementDesc::Block(inner),
                ..
            } => flattened.extend(inner),
            other => flattened.push(other),
        }
    }

    flattened
}

fn flatten_statement(stmt: Statement) -> Statement {
    let Statement { desc, comment } = stmt;

    match desc {
        StatementDesc::Exp(expr) => {
            let Expression {
                desc,
                comment: expr_comment,
            } = expr;

            match desc {
                ExpressionDesc::Seq(_, _) => {
                    let block = flatten_sequence_statements(Expression {
                        desc,
                        comment: expr_comment,
                    });
                    Statement::new(StatementDesc::Block(block))
                }
                ExpressionDesc::CamlBlock(args, _, _, _) => {
                    let block = args
                        .into_iter()
                        .map(|arg| flatten_statement(Statement::exp(arg)))
                        .collect();
                    Statement::new(StatementDesc::Block(block))
                }
                ExpressionDesc::Cond(test, consequent, alternate) => Statement {
                    desc: StatementDesc::If(
                        flatten_expression(*test),
                        vec![flatten_statement(Statement::exp(*consequent))],
                        vec![flatten_statement(Statement::exp(*alternate))],
                    ),
                    comment,
                },
                ExpressionDesc::Bin(BinOp::Eq, target, value) => {
                    if matches!(value.desc, ExpressionDesc::Seq(_, _)) {
                        let mut exprs = Vec::new();
                        flatten_sequence_expressions(*value, &mut exprs);
                        let last = exprs
                            .pop()
                            .expect("sequence flattening must produce at least one expression");
                        let mut block: Block = exprs
                            .into_iter()
                            .map(|expr| flatten_statement(Statement::exp(expr)))
                            .collect();
                        block.push(flatten_statement(Statement::exp(Expression::bin(
                            BinOp::Eq,
                            *target,
                            last,
                        ))));
                        Statement::new(StatementDesc::Block(block))
                    } else {
                        Statement {
                            desc: StatementDesc::Exp(flatten_expression(Expression {
                                desc: ExpressionDesc::Bin(BinOp::Eq, target, value),
                                comment: expr_comment,
                            })),
                            comment,
                        }
                    }
                }
                desc => Statement {
                    desc: StatementDesc::Exp(flatten_expression(Expression {
                        desc,
                        comment: expr_comment,
                    })),
                    comment,
                },
            }
        }
        StatementDesc::Return(expr) => {
            let Expression {
                desc,
                comment: expr_comment,
            } = expr;

            match desc {
                ExpressionDesc::Cond(test, consequent, alternate) => Statement {
                    desc: StatementDesc::If(
                        flatten_expression(*test),
                        vec![flatten_statement(Statement::return_(*consequent))],
                        vec![flatten_statement(Statement::return_(*alternate))],
                    ),
                    comment,
                },
                ExpressionDesc::Seq(_, _) => {
                    let mut exprs = Vec::new();
                    flatten_sequence_expressions(
                        Expression {
                            desc,
                            comment: expr_comment,
                        },
                        &mut exprs,
                    );
                    let last = exprs
                        .pop()
                        .expect("return sequence flattening must produce at least one expression");
                    let mut block: Block = exprs
                        .into_iter()
                        .map(|expr| flatten_statement(Statement::exp(expr)))
                        .collect();
                    block.push(flatten_statement(Statement::return_(last)));
                    Statement::new(StatementDesc::Block(block))
                }
                desc => Statement {
                    desc: StatementDesc::Return(flatten_expression(Expression {
                        desc,
                        comment: expr_comment,
                    })),
                    comment,
                },
            }
        }
        StatementDesc::Block(block) => {
            if block.len() == 1 {
                flatten_statement(block.into_iter().next().expect("single-item block"))
            } else {
                Statement {
                    desc: StatementDesc::Block(flatten_block(block)),
                    comment,
                }
            }
        }
        StatementDesc::Variable(decl) => Statement {
            desc: StatementDesc::Variable(VariableDeclaration {
                ident: decl.ident,
                value: decl.value.map(flatten_expression),
                property: decl.property,
                ident_info: decl.ident_info,
            }),
            comment,
        },
        StatementDesc::If(cond, then_block, else_block) => Statement {
            desc: StatementDesc::If(
                flatten_expression(cond),
                flatten_block(then_block),
                flatten_block(else_block),
            ),
            comment,
        },
        StatementDesc::While(cond, body) => Statement {
            desc: StatementDesc::While(flatten_expression(cond), flatten_block(body)),
            comment,
        },
        StatementDesc::ForRange(start, finish, ident, direction, body) => Statement {
            desc: StatementDesc::ForRange(
                start.map(flatten_expression),
                flatten_expression(finish),
                ident,
                direction,
                flatten_block(body),
            ),
            comment,
        },
        StatementDesc::IntSwitch(test, clauses, default) => Statement {
            desc: StatementDesc::IntSwitch(
                flatten_expression(test),
                clauses
                    .into_iter()
                    .map(|(tag, clause)| (tag, flatten_case_clause(clause)))
                    .collect(),
                default.map(flatten_block),
            ),
            comment,
        },
        StatementDesc::StringSwitch(test, clauses, default) => Statement {
            desc: StatementDesc::StringSwitch(
                flatten_expression(test),
                clauses
                    .into_iter()
                    .map(|clause| StringClause {
                        tag_type: clause.tag_type,
                        clause: flatten_case_clause(clause.clause),
                    })
                    .collect(),
                default.map(flatten_block),
            ),
            comment,
        },
        StatementDesc::Throw(expr) => Statement {
            desc: StatementDesc::Throw(flatten_expression(expr)),
            comment,
        },
        StatementDesc::Try(body, catch, finally) => Statement {
            desc: StatementDesc::Try(
                flatten_block(body),
                catch.map(|(id, block)| (id, flatten_block(block))),
                finally.map(flatten_block),
            ),
            comment,
        },
        StatementDesc::Debugger => Statement {
            desc: StatementDesc::Debugger,
            comment,
        },
        StatementDesc::Break => Statement {
            desc: StatementDesc::Break,
            comment,
        },
        StatementDesc::Continue => Statement {
            desc: StatementDesc::Continue,
            comment,
        },
    }
}

fn flatten_case_clause(clause: CaseClause) -> CaseClause {
    CaseClause {
        body: flatten_block(clause.body),
        should_break: clause.should_break,
        comment: clause.comment,
    }
}

fn flatten_expression(expr: Expression) -> Expression {
    let comment = expr.comment;
    let desc = match expr.desc {
        ExpressionDesc::Length(inner, object) => {
            ExpressionDesc::Length(Box::new(flatten_expression(*inner)), object)
        }
        ExpressionDesc::IsNullOrUndefined(inner) => {
            ExpressionDesc::IsNullOrUndefined(Box::new(flatten_expression(*inner)))
        }
        ExpressionDesc::StringAppend(left, right) => ExpressionDesc::StringAppend(
            Box::new(flatten_expression(*left)),
            Box::new(flatten_expression(*right)),
        ),
        ExpressionDesc::Bool(value) => ExpressionDesc::Bool(value),
        ExpressionDesc::Typeof(inner) => {
            ExpressionDesc::Typeof(Box::new(flatten_expression(*inner)))
        }
        ExpressionDesc::In(left, right) => ExpressionDesc::In(
            Box::new(flatten_expression(*left)),
            Box::new(flatten_expression(*right)),
        ),
        ExpressionDesc::JsNot(inner) => ExpressionDesc::JsNot(Box::new(flatten_expression(*inner))),
        ExpressionDesc::JsBnot(inner) => {
            ExpressionDesc::JsBnot(Box::new(flatten_expression(*inner)))
        }
        ExpressionDesc::Seq(left, right) => ExpressionDesc::Seq(
            Box::new(flatten_expression(*left)),
            Box::new(flatten_expression(*right)),
        ),
        ExpressionDesc::Cond(test, consequent, alternate) => ExpressionDesc::Cond(
            Box::new(flatten_expression(*test)),
            Box::new(flatten_expression(*consequent)),
            Box::new(flatten_expression(*alternate)),
        ),
        ExpressionDesc::Bin(op, left, right) => ExpressionDesc::Bin(
            op,
            Box::new(flatten_expression(*left)),
            Box::new(flatten_expression(*right)),
        ),
        ExpressionDesc::FlatCall(func, args) => ExpressionDesc::FlatCall(
            Box::new(flatten_expression(*func)),
            Box::new(flatten_expression(*args)),
        ),
        ExpressionDesc::Call(func, args, info) => ExpressionDesc::Call(
            Box::new(flatten_expression(*func)),
            args.into_iter().map(flatten_expression).collect(),
            info,
        ),
        ExpressionDesc::StringIndex(left, right) => ExpressionDesc::StringIndex(
            Box::new(flatten_expression(*left)),
            Box::new(flatten_expression(*right)),
        ),
        ExpressionDesc::ArrayIndex(left, right) => ExpressionDesc::ArrayIndex(
            Box::new(flatten_expression(*left)),
            Box::new(flatten_expression(*right)),
        ),
        ExpressionDesc::TaggedTemplate(tag, strings, values) => ExpressionDesc::TaggedTemplate(
            Box::new(flatten_expression(*tag)),
            strings.into_iter().map(flatten_expression).collect(),
            values.into_iter().map(flatten_expression).collect(),
        ),
        ExpressionDesc::StaticIndex(target, field, pos) => {
            ExpressionDesc::StaticIndex(Box::new(flatten_expression(*target)), field, pos)
        }
        ExpressionDesc::New(target, args) => ExpressionDesc::New(
            Box::new(flatten_expression(*target)),
            args.map(|args| args.into_iter().map(flatten_expression).collect()),
        ),
        ExpressionDesc::Var(var) => ExpressionDesc::Var(var),
        ExpressionDesc::Fun {
            is_method,
            params,
            body,
            env,
            return_unit,
            async_,
            directive,
        } => ExpressionDesc::Fun {
            is_method,
            params,
            body: flatten_block(body),
            env,
            return_unit,
            async_,
            directive,
        },
        ExpressionDesc::Str { delim, txt } => ExpressionDesc::Str { delim, txt },
        ExpressionDesc::RawJsCode(info) => ExpressionDesc::RawJsCode(info),
        ExpressionDesc::Array(items, mutable_flag) => ExpressionDesc::Array(
            items.into_iter().map(flatten_expression).collect(),
            mutable_flag,
        ),
        ExpressionDesc::OptionalBlock(inner, flag) => {
            ExpressionDesc::OptionalBlock(Box::new(flatten_expression(*inner)), flag)
        }
        ExpressionDesc::CamlBlock(items, mutable_flag, tag, tag_info) => ExpressionDesc::CamlBlock(
            items.into_iter().map(flatten_expression).collect(),
            mutable_flag,
            Box::new(flatten_expression(*tag)),
            tag_info,
        ),
        ExpressionDesc::CamlBlockTag(inner, tag) => {
            ExpressionDesc::CamlBlockTag(Box::new(flatten_expression(*inner)), tag)
        }
        ExpressionDesc::Number(number) => ExpressionDesc::Number(number),
        ExpressionDesc::Object(dup, props) => ExpressionDesc::Object(
            dup.map(|dup| Box::new(flatten_expression(*dup))),
            props
                .into_iter()
                .map(|(name, value)| (name, flatten_expression(value)))
                .collect(),
        ),
        ExpressionDesc::Undefined { is_unit } => ExpressionDesc::Undefined { is_unit },
        ExpressionDesc::Null => ExpressionDesc::Null,
        ExpressionDesc::Await(inner) => ExpressionDesc::Await(Box::new(flatten_expression(*inner))),
        ExpressionDesc::Spread(inner) => {
            ExpressionDesc::Spread(Box::new(flatten_expression(*inner)))
        }
    };

    Expression { desc, comment }
}

fn flatten_sequence_statements(expr: Expression) -> Block {
    let mut exprs = Vec::new();
    flatten_sequence_expressions(expr, &mut exprs);
    exprs
        .into_iter()
        .map(|expr| flatten_statement(Statement::exp(expr)))
        .collect()
}

fn flatten_sequence_expressions(expr: Expression, out: &mut Vec<Expression>) {
    match expr.desc {
        ExpressionDesc::Seq(left, right) => {
            flatten_sequence_expressions(*left, out);
            flatten_sequence_expressions(*right, out);
        }
        desc => out.push(Expression {
            desc,
            comment: expr.comment,
        }),
    }
}

fn apply_external_shadow_pass(mut deps: DepsProgram) -> DepsProgram {
    let shadowed_globals = deps
        .program
        .block
        .iter()
        .filter_map(|stmt| match &stmt.desc {
            StatementDesc::Variable(VariableDeclaration {
                ident, property, ..
            }) if is_lexical_binding_kind(*property) && should_rewrite_binding(ident) => {
                Some(ident.name().to_string())
            }
            _ => None,
        })
        .collect::<HashSet<_>>();

    if shadowed_globals.is_empty() {
        return deps;
    }

    deps.program.block = rewrite_block(&deps.program.block, &shadowed_globals);
    deps
}

fn apply_js_tailcall_inline_pass(mut deps: DepsProgram) -> DepsProgram {
    deps.program = tailcall_inline_program(deps.program);
    deps
}

fn tailcall_inline_program(program: Program) -> Program {
    let mut inliner = TailcallInlineState::new(&program);
    let mut program = Program {
        block: inliner.transform_block(program.block),
        exports: program.exports,
        export_set: program.export_set,
    };
    apply_tailcall_used_stats_block(&mut program.block, &inliner.statuses);
    program
}

#[derive(Debug, Clone)]
struct TailcallInlineState {
    decls: HashMap<Ident, VariableDeclaration>,
    statuses: HashMap<Ident, UsedStats>,
}

impl TailcallInlineState {
    fn new(program: &Program) -> Self {
        let mut decls = HashMap::new();
        let mut counts = HashMap::new();
        collect_tailcall_use_counts_block(&program.block, &mut decls, &mut counts);

        let mut statuses = HashMap::with_capacity(decls.len());
        for (ident, decl) in &decls {
            let count = counts.get(ident).copied().unwrap_or(0);
            let exported = program.export_set.contains(ident);
            let pure = decl.value.as_ref().is_some_and(js_expr_no_side_effects);
            let status = if exported {
                UsedStats::Exported
            } else if count == 0 {
                if pure {
                    UsedStats::DeadPure
                } else {
                    UsedStats::DeadNonPure
                }
            } else if count == 1 && pure {
                UsedStats::OncePure
            } else {
                UsedStats::Used
            };
            statuses.insert(ident.clone(), status);
        }

        Self { decls, statuses }
    }

    fn transform_block(&mut self, block: Block) -> Block {
        if block.len() == 1 {
            if let Some(inlined) = self.try_inline_single_return_block(&block[0]) {
                return inlined;
            }
        }

        let mut iter = block.into_iter();
        let Some(first) = iter.next() else {
            return Vec::new();
        };
        let rest: Block = iter.collect();

        let mut transformed = self.transform_statement(first);
        transformed.extend(self.transform_block(rest));
        transformed
    }

    fn transform_statement(&mut self, stmt: Statement) -> Vec<Statement> {
        let Statement { desc, comment } = stmt;
        match desc {
            StatementDesc::Block(block) => vec![Statement {
                desc: StatementDesc::Block(self.transform_block(block)),
                comment,
            }],
            StatementDesc::Variable(mut decl) => {
                if let Some(value) = decl.value.take() {
                    decl.value = Some(self.transform_expression(value));
                }

                let status = self
                    .statuses
                    .get(&decl.ident)
                    .copied()
                    .unwrap_or(UsedStats::Used);
                decl.ident_info.used_stats = status;
                self.decls.insert(decl.ident.clone(), decl.clone());

                match status {
                    UsedStats::DeadPure => vec![],
                    UsedStats::DeadNonPure => decl
                        .value
                        .map(|value| {
                            vec![Statement {
                                desc: StatementDesc::Exp(value),
                                comment,
                            }]
                        })
                        .unwrap_or_default(),
                    _ => vec![Statement {
                        desc: StatementDesc::Variable(decl),
                        comment,
                    }],
                }
            }
            StatementDesc::Exp(expr) => vec![Statement {
                desc: StatementDesc::Exp(self.transform_expression(expr)),
                comment,
            }],
            StatementDesc::If(cond, then_block, else_block) => vec![Statement {
                desc: StatementDesc::If(
                    self.transform_expression(cond),
                    self.transform_block(then_block),
                    self.transform_block(else_block),
                ),
                comment,
            }],
            StatementDesc::While(cond, body) => vec![Statement {
                desc: StatementDesc::While(
                    self.transform_expression(cond),
                    self.transform_block(body),
                ),
                comment,
            }],
            StatementDesc::ForRange(start, finish, ident, direction, body) => vec![Statement {
                desc: StatementDesc::ForRange(
                    start.map(|expr| self.transform_expression(expr)),
                    self.transform_expression(finish),
                    ident,
                    direction,
                    self.transform_block(body),
                ),
                comment,
            }],
            StatementDesc::Continue => vec![Statement {
                desc: StatementDesc::Continue,
                comment,
            }],
            StatementDesc::Break => vec![Statement {
                desc: StatementDesc::Break,
                comment,
            }],
            StatementDesc::Return(expr) => vec![Statement {
                desc: StatementDesc::Return(self.transform_expression(expr)),
                comment,
            }],
            StatementDesc::IntSwitch(test, clauses, default) => vec![Statement {
                desc: StatementDesc::IntSwitch(
                    self.transform_expression(test),
                    clauses
                        .into_iter()
                        .map(|(value, clause)| {
                            (
                                value,
                                CaseClause {
                                    body: self.transform_block(clause.body),
                                    should_break: clause.should_break,
                                    comment: clause.comment,
                                },
                            )
                        })
                        .collect(),
                    default.map(|block| self.transform_block(block)),
                ),
                comment,
            }],
            StatementDesc::StringSwitch(test, clauses, default) => vec![Statement {
                desc: StatementDesc::StringSwitch(
                    self.transform_expression(test),
                    clauses
                        .into_iter()
                        .map(|clause| StringClause {
                            tag_type: clause.tag_type,
                            clause: CaseClause {
                                body: self.transform_block(clause.clause.body),
                                should_break: clause.clause.should_break,
                                comment: clause.clause.comment,
                            },
                        })
                        .collect(),
                    default.map(|block| self.transform_block(block)),
                ),
                comment,
            }],
            StatementDesc::Throw(expr) => vec![Statement {
                desc: StatementDesc::Throw(self.transform_expression(expr)),
                comment,
            }],
            StatementDesc::Try(body, catch, finally) => vec![Statement {
                desc: StatementDesc::Try(
                    self.transform_block(body),
                    catch.map(|(ident, block)| (ident, self.transform_block(block))),
                    finally.map(|block| self.transform_block(block)),
                ),
                comment,
            }],
            StatementDesc::Debugger => vec![Statement {
                desc: StatementDesc::Debugger,
                comment,
            }],
        }
    }

    fn transform_expression(&mut self, expr: Expression) -> Expression {
        let Expression { desc, comment } = expr;
        let desc = match desc {
            ExpressionDesc::Length(inner, obj) => {
                ExpressionDesc::Length(Box::new(self.transform_expression(*inner)), obj)
            }
            ExpressionDesc::IsNullOrUndefined(inner) => {
                ExpressionDesc::IsNullOrUndefined(Box::new(self.transform_expression(*inner)))
            }
            ExpressionDesc::StringAppend(left, right) => ExpressionDesc::StringAppend(
                Box::new(self.transform_expression(*left)),
                Box::new(self.transform_expression(*right)),
            ),
            ExpressionDesc::Bool(value) => ExpressionDesc::Bool(value),
            ExpressionDesc::Typeof(inner) => {
                ExpressionDesc::Typeof(Box::new(self.transform_expression(*inner)))
            }
            ExpressionDesc::In(left, right) => ExpressionDesc::In(
                Box::new(self.transform_expression(*left)),
                Box::new(self.transform_expression(*right)),
            ),
            ExpressionDesc::JsNot(inner) => {
                ExpressionDesc::JsNot(Box::new(self.transform_expression(*inner)))
            }
            ExpressionDesc::JsBnot(inner) => {
                ExpressionDesc::JsBnot(Box::new(self.transform_expression(*inner)))
            }
            ExpressionDesc::Seq(left, right) => ExpressionDesc::Seq(
                Box::new(self.transform_expression(*left)),
                Box::new(self.transform_expression(*right)),
            ),
            ExpressionDesc::Cond(test, consequent, alternate) => ExpressionDesc::Cond(
                Box::new(self.transform_expression(*test)),
                Box::new(self.transform_expression(*consequent)),
                Box::new(self.transform_expression(*alternate)),
            ),
            ExpressionDesc::Bin(op, left, right) => ExpressionDesc::Bin(
                op,
                Box::new(self.transform_expression(*left)),
                Box::new(self.transform_expression(*right)),
            ),
            ExpressionDesc::FlatCall(func, args) => ExpressionDesc::FlatCall(
                Box::new(self.transform_expression(*func)),
                Box::new(self.transform_expression(*args)),
            ),
            ExpressionDesc::Call(func, args, info) => ExpressionDesc::Call(
                Box::new(self.transform_expression(*func)),
                args.into_iter()
                    .map(|arg| self.transform_expression(arg))
                    .collect(),
                info,
            ),
            ExpressionDesc::StringIndex(left, right) => ExpressionDesc::StringIndex(
                Box::new(self.transform_expression(*left)),
                Box::new(self.transform_expression(*right)),
            ),
            ExpressionDesc::ArrayIndex(left, right) => ExpressionDesc::ArrayIndex(
                Box::new(self.transform_expression(*left)),
                Box::new(self.transform_expression(*right)),
            ),
            ExpressionDesc::TaggedTemplate(tag, strings, values) => ExpressionDesc::TaggedTemplate(
                Box::new(self.transform_expression(*tag)),
                strings
                    .into_iter()
                    .map(|expr| self.transform_expression(expr))
                    .collect(),
                values
                    .into_iter()
                    .map(|expr| self.transform_expression(expr))
                    .collect(),
            ),
            ExpressionDesc::StaticIndex(target, field, position) => ExpressionDesc::StaticIndex(
                Box::new(self.transform_expression(*target)),
                field,
                position,
            ),
            ExpressionDesc::New(target, args) => ExpressionDesc::New(
                Box::new(self.transform_expression(*target)),
                args.map(|args| {
                    args.into_iter()
                        .map(|arg| self.transform_expression(arg))
                        .collect()
                }),
            ),
            ExpressionDesc::Var(ident) => ExpressionDesc::Var(ident),
            ExpressionDesc::Fun {
                is_method,
                params,
                body,
                env,
                return_unit,
                async_,
                directive,
            } => ExpressionDesc::Fun {
                is_method,
                params,
                body: self.transform_block(body),
                env,
                return_unit,
                async_,
                directive,
            },
            ExpressionDesc::Str { delim, txt } => ExpressionDesc::Str { delim, txt },
            ExpressionDesc::RawJsCode(info) => ExpressionDesc::RawJsCode(info),
            ExpressionDesc::Array(items, mutable_flag) => ExpressionDesc::Array(
                items
                    .into_iter()
                    .map(|item| self.transform_expression(item))
                    .collect(),
                mutable_flag,
            ),
            ExpressionDesc::OptionalBlock(inner, flag) => {
                ExpressionDesc::OptionalBlock(Box::new(self.transform_expression(*inner)), flag)
            }
            ExpressionDesc::CamlBlock(items, mutable_flag, tag, info) => ExpressionDesc::CamlBlock(
                items
                    .into_iter()
                    .map(|item| self.transform_expression(item))
                    .collect(),
                mutable_flag,
                Box::new(self.transform_expression(*tag)),
                info,
            ),
            ExpressionDesc::CamlBlockTag(inner, field) => {
                ExpressionDesc::CamlBlockTag(Box::new(self.transform_expression(*inner)), field)
            }
            ExpressionDesc::Number(number) => ExpressionDesc::Number(number),
            ExpressionDesc::Object(dup, props) => ExpressionDesc::Object(
                dup.map(|expr| Box::new(self.transform_expression(*expr))),
                props
                    .into_iter()
                    .map(|(name, value)| (name, self.transform_expression(value)))
                    .collect(),
            ),
            ExpressionDesc::Undefined { is_unit } => ExpressionDesc::Undefined { is_unit },
            ExpressionDesc::Null => ExpressionDesc::Null,
            ExpressionDesc::Await(inner) => {
                ExpressionDesc::Await(Box::new(self.transform_expression(*inner)))
            }
            ExpressionDesc::Spread(inner) => {
                ExpressionDesc::Spread(Box::new(self.transform_expression(*inner)))
            }
        };

        Expression { desc, comment }
    }

    fn try_inline_single_return_block(&mut self, stmt: &Statement) -> Option<Block> {
        let StatementDesc::Return(expr) = &stmt.desc else {
            return None;
        };
        let ExpressionDesc::Call(func, args, _) = &expr.desc else {
            return None;
        };

        match &func.desc {
            ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)) => self.inline_named_call(id, args),
            ExpressionDesc::Fun {
                is_method: false,
                params,
                body,
                async_: false,
                directive: None,
                ..
            } if params.len() == args.len() => Some(self.inline_function_call(params, body, args)),
            _ => None,
        }
    }

    fn inline_named_call(&mut self, ident: &Ident, args: &[Expression]) -> Option<Block> {
        if self.statuses.get(ident).copied() != Some(UsedStats::OncePure) {
            return None;
        }

        let decl = self.decls.get(ident)?.clone();
        if !is_lexical_binding_kind(decl.property) {
            return None;
        }

        let Some(Expression {
            desc:
                ExpressionDesc::Fun {
                    is_method: false,
                    params,
                    body,
                    async_: false,
                    directive: None,
                    ..
                },
            ..
        }) = decl.value
        else {
            return None;
        };

        if params.len() != args.len() {
            return None;
        }

        self.statuses.insert(ident.clone(), UsedStats::DeadPure);
        Some(self.inline_function_call(&params, &body, args))
    }

    fn inline_function_call(
        &mut self,
        params: &[Ident],
        body: &Block,
        args: &[Expression],
    ) -> Block {
        let processed_body = self.transform_block(body.clone());
        let immutable_mask = immutable_param_mask(params, &processed_body);
        let args = args
            .iter()
            .cloned()
            .map(|arg| self.transform_expression(arg))
            .collect();
        inline_tailcall_call(&immutable_mask, params, args, processed_body)
    }
}

fn collect_tailcall_use_counts_block(
    block: &Block,
    decls: &mut HashMap<Ident, VariableDeclaration>,
    counts: &mut HashMap<Ident, usize>,
) {
    for stmt in block {
        collect_tailcall_use_counts_statement(stmt, decls, counts);
    }
}

fn collect_tailcall_use_counts_statement(
    stmt: &Statement,
    decls: &mut HashMap<Ident, VariableDeclaration>,
    counts: &mut HashMap<Ident, usize>,
) {
    match &stmt.desc {
        StatementDesc::Block(block) => collect_tailcall_use_counts_block(block, decls, counts),
        StatementDesc::Variable(decl) => {
            decls.insert(decl.ident.clone(), decl.clone());
            if let Some(value) = &decl.value {
                collect_tailcall_use_counts_expression(value, decls, counts);
            }
        }
        StatementDesc::Exp(expr) | StatementDesc::Return(expr) | StatementDesc::Throw(expr) => {
            collect_tailcall_use_counts_expression(expr, decls, counts);
        }
        StatementDesc::If(cond, then_block, else_block) => {
            collect_tailcall_use_counts_expression(cond, decls, counts);
            collect_tailcall_use_counts_block(then_block, decls, counts);
            collect_tailcall_use_counts_block(else_block, decls, counts);
        }
        StatementDesc::While(cond, body) => {
            collect_tailcall_use_counts_expression(cond, decls, counts);
            collect_tailcall_use_counts_block(body, decls, counts);
        }
        StatementDesc::ForRange(start, finish, _, _, body) => {
            if let Some(start) = start {
                collect_tailcall_use_counts_expression(start, decls, counts);
            }
            collect_tailcall_use_counts_expression(finish, decls, counts);
            collect_tailcall_use_counts_block(body, decls, counts);
        }
        StatementDesc::IntSwitch(test, clauses, default) => {
            collect_tailcall_use_counts_expression(test, decls, counts);
            for (_, clause) in clauses {
                collect_tailcall_use_counts_block(&clause.body, decls, counts);
            }
            if let Some(default) = default {
                collect_tailcall_use_counts_block(default, decls, counts);
            }
        }
        StatementDesc::StringSwitch(test, clauses, default) => {
            collect_tailcall_use_counts_expression(test, decls, counts);
            for clause in clauses {
                collect_tailcall_use_counts_block(&clause.clause.body, decls, counts);
            }
            if let Some(default) = default {
                collect_tailcall_use_counts_block(default, decls, counts);
            }
        }
        StatementDesc::Try(body, catch, finally) => {
            collect_tailcall_use_counts_block(body, decls, counts);
            if let Some((_, block)) = catch {
                collect_tailcall_use_counts_block(block, decls, counts);
            }
            if let Some(block) = finally {
                collect_tailcall_use_counts_block(block, decls, counts);
            }
        }
        StatementDesc::Debugger | StatementDesc::Break | StatementDesc::Continue => {}
    }
}

fn collect_tailcall_use_counts_expression(
    expr: &Expression,
    decls: &mut HashMap<Ident, VariableDeclaration>,
    counts: &mut HashMap<Ident, usize>,
) {
    match &expr.desc {
        ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)) => {
            *counts.entry(id.clone()).or_insert(0) += 1;
        }
        ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(_, _))
        | ExpressionDesc::Undefined { .. }
        | ExpressionDesc::Null
        | ExpressionDesc::Bool(_)
        | ExpressionDesc::Str { .. }
        | ExpressionDesc::RawJsCode(_)
        | ExpressionDesc::Number(_) => {}
        ExpressionDesc::Length(inner, _)
        | ExpressionDesc::IsNullOrUndefined(inner)
        | ExpressionDesc::Typeof(inner)
        | ExpressionDesc::JsNot(inner)
        | ExpressionDesc::JsBnot(inner)
        | ExpressionDesc::CamlBlockTag(inner, _)
        | ExpressionDesc::OptionalBlock(inner, _)
        | ExpressionDesc::Await(inner)
        | ExpressionDesc::Spread(inner) => {
            collect_tailcall_use_counts_expression(inner, decls, counts)
        }
        ExpressionDesc::StringAppend(left, right)
        | ExpressionDesc::In(left, right)
        | ExpressionDesc::Seq(left, right)
        | ExpressionDesc::Bin(_, left, right)
        | ExpressionDesc::FlatCall(left, right)
        | ExpressionDesc::StringIndex(left, right)
        | ExpressionDesc::ArrayIndex(left, right) => {
            collect_tailcall_use_counts_expression(left, decls, counts);
            collect_tailcall_use_counts_expression(right, decls, counts);
        }
        ExpressionDesc::Cond(test, consequent, alternate) => {
            collect_tailcall_use_counts_expression(test, decls, counts);
            collect_tailcall_use_counts_expression(consequent, decls, counts);
            collect_tailcall_use_counts_expression(alternate, decls, counts);
        }
        ExpressionDesc::Call(func, args, _) => {
            collect_tailcall_use_counts_expression(func, decls, counts);
            for arg in args {
                collect_tailcall_use_counts_expression(arg, decls, counts);
            }
        }
        ExpressionDesc::TaggedTemplate(tag, strings, values) => {
            collect_tailcall_use_counts_expression(tag, decls, counts);
            for string in strings {
                collect_tailcall_use_counts_expression(string, decls, counts);
            }
            for value in values {
                collect_tailcall_use_counts_expression(value, decls, counts);
            }
        }
        ExpressionDesc::StaticIndex(target, _, _) => {
            collect_tailcall_use_counts_expression(target, decls, counts)
        }
        ExpressionDesc::New(target, args) => {
            collect_tailcall_use_counts_expression(target, decls, counts);
            if let Some(args) = args {
                for arg in args {
                    collect_tailcall_use_counts_expression(arg, decls, counts);
                }
            }
        }
        ExpressionDesc::Fun { body, .. } => collect_tailcall_use_counts_block(body, decls, counts),
        ExpressionDesc::Array(items, _) => {
            for item in items {
                collect_tailcall_use_counts_expression(item, decls, counts);
            }
        }
        ExpressionDesc::CamlBlock(items, _, tag, _) => {
            for item in items {
                collect_tailcall_use_counts_expression(item, decls, counts);
            }
            collect_tailcall_use_counts_expression(tag, decls, counts);
        }
        ExpressionDesc::Object(dup, props) => {
            if let Some(dup) = dup {
                collect_tailcall_use_counts_expression(dup, decls, counts);
            }
            for (_, value) in props {
                collect_tailcall_use_counts_expression(value, decls, counts);
            }
        }
    }
}

fn immutable_param_mask(params: &[Ident], body: &Block) -> Vec<bool> {
    params
        .iter()
        .map(|param| !block_assigns_ident(body, param))
        .collect()
}

fn block_assigns_ident(block: &Block, ident: &Ident) -> bool {
    block
        .iter()
        .any(|stmt| statement_assigns_ident(stmt, ident))
}

fn statement_assigns_ident(stmt: &Statement, ident: &Ident) -> bool {
    match &stmt.desc {
        StatementDesc::Block(block) => block_assigns_ident(block, ident),
        StatementDesc::Variable(decl) => decl
            .value
            .as_ref()
            .is_some_and(|value| expression_assigns_ident(value, ident)),
        StatementDesc::Exp(expr) | StatementDesc::Return(expr) | StatementDesc::Throw(expr) => {
            expression_assigns_ident(expr, ident)
        }
        StatementDesc::If(cond, then_block, else_block) => {
            expression_assigns_ident(cond, ident)
                || block_assigns_ident(then_block, ident)
                || block_assigns_ident(else_block, ident)
        }
        StatementDesc::While(cond, body) => {
            expression_assigns_ident(cond, ident) || block_assigns_ident(body, ident)
        }
        StatementDesc::ForRange(start, finish, _, _, body) => {
            start
                .as_ref()
                .is_some_and(|expr| expression_assigns_ident(expr, ident))
                || expression_assigns_ident(finish, ident)
                || block_assigns_ident(body, ident)
        }
        StatementDesc::IntSwitch(test, clauses, default) => {
            expression_assigns_ident(test, ident)
                || clauses
                    .iter()
                    .any(|(_, clause)| block_assigns_ident(&clause.body, ident))
                || default
                    .as_ref()
                    .is_some_and(|block| block_assigns_ident(block, ident))
        }
        StatementDesc::StringSwitch(test, clauses, default) => {
            expression_assigns_ident(test, ident)
                || clauses
                    .iter()
                    .any(|clause| block_assigns_ident(&clause.clause.body, ident))
                || default
                    .as_ref()
                    .is_some_and(|block| block_assigns_ident(block, ident))
        }
        StatementDesc::Try(body, catch, finally) => {
            block_assigns_ident(body, ident)
                || catch
                    .as_ref()
                    .is_some_and(|(_, block)| block_assigns_ident(block, ident))
                || finally
                    .as_ref()
                    .is_some_and(|block| block_assigns_ident(block, ident))
        }
        StatementDesc::Debugger | StatementDesc::Break | StatementDesc::Continue => false,
    }
}

fn expression_assigns_ident(expr: &Expression, ident: &Ident) -> bool {
    match &expr.desc {
        ExpressionDesc::Bin(BinOp::Eq, left, right) => {
            matches!(
                left.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(lhs)),
                    ..
                } if lhs.same(ident)
            ) || expression_assigns_ident(left, ident)
                || expression_assigns_ident(right, ident)
        }
        ExpressionDesc::Length(inner, _)
        | ExpressionDesc::IsNullOrUndefined(inner)
        | ExpressionDesc::Typeof(inner)
        | ExpressionDesc::JsNot(inner)
        | ExpressionDesc::JsBnot(inner)
        | ExpressionDesc::CamlBlockTag(inner, _)
        | ExpressionDesc::OptionalBlock(inner, _)
        | ExpressionDesc::Await(inner)
        | ExpressionDesc::Spread(inner) => expression_assigns_ident(inner, ident),
        ExpressionDesc::StringAppend(left, right)
        | ExpressionDesc::In(left, right)
        | ExpressionDesc::Seq(left, right)
        | ExpressionDesc::Bin(_, left, right)
        | ExpressionDesc::FlatCall(left, right)
        | ExpressionDesc::StringIndex(left, right)
        | ExpressionDesc::ArrayIndex(left, right) => {
            expression_assigns_ident(left, ident) || expression_assigns_ident(right, ident)
        }
        ExpressionDesc::Cond(test, consequent, alternate) => {
            expression_assigns_ident(test, ident)
                || expression_assigns_ident(consequent, ident)
                || expression_assigns_ident(alternate, ident)
        }
        ExpressionDesc::Call(func, args, _) => {
            expression_assigns_ident(func, ident)
                || args.iter().any(|arg| expression_assigns_ident(arg, ident))
        }
        ExpressionDesc::TaggedTemplate(tag, strings, values) => {
            expression_assigns_ident(tag, ident)
                || strings
                    .iter()
                    .any(|expr| expression_assigns_ident(expr, ident))
                || values
                    .iter()
                    .any(|expr| expression_assigns_ident(expr, ident))
        }
        ExpressionDesc::StaticIndex(target, _, _) => expression_assigns_ident(target, ident),
        ExpressionDesc::New(target, args) => {
            expression_assigns_ident(target, ident)
                || args
                    .as_ref()
                    .is_some_and(|args| args.iter().any(|arg| expression_assigns_ident(arg, ident)))
        }
        ExpressionDesc::Fun { body, .. } => block_assigns_ident(body, ident),
        ExpressionDesc::Array(items, _) => items
            .iter()
            .any(|item| expression_assigns_ident(item, ident)),
        ExpressionDesc::CamlBlock(items, _, tag, _) => {
            items
                .iter()
                .any(|item| expression_assigns_ident(item, ident))
                || expression_assigns_ident(tag, ident)
        }
        ExpressionDesc::Object(dup, props) => {
            dup.as_ref()
                .is_some_and(|expr| expression_assigns_ident(expr, ident))
                || props
                    .iter()
                    .any(|(_, value)| expression_assigns_ident(value, ident))
        }
        ExpressionDesc::Var(_)
        | ExpressionDesc::Undefined { .. }
        | ExpressionDesc::Null
        | ExpressionDesc::Bool(_)
        | ExpressionDesc::Str { .. }
        | ExpressionDesc::RawJsCode(_)
        | ExpressionDesc::Number(_) => false,
    }
}

fn inline_tailcall_call(
    immutable_mask: &[bool],
    params: &[Ident],
    args: Vec<Expression>,
    body: Block,
) -> Block {
    let mut bindings = Vec::new();
    let mut substitution = HashMap::new();

    for ((param, arg), immutable) in params
        .iter()
        .cloned()
        .zip(args.into_iter())
        .zip(immutable_mask.iter().copied())
    {
        if immutable {
            if let ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)) = &arg.desc {
                substitution.insert(param, id.clone());
                continue;
            }
        }

        bindings.push(Statement::variable(VariableDeclaration {
            ident: param,
            value: Some(arg),
            property: LetKind::Variable,
            ident_info: IdentInfo::default(),
        }));
    }

    let body = if substitution.is_empty() {
        body
    } else {
        substitute_inline_block(body, &substitution)
    };

    bindings.into_iter().chain(body).collect()
}

fn substitute_inline_block(block: Block, substitution: &HashMap<Ident, Ident>) -> Block {
    let mut current_substitution = substitution.clone();
    let mut rewritten = Vec::with_capacity(block.len());

    for stmt in block {
        let stmt = substitute_inline_statement(stmt, &current_substitution);
        shadow_inline_statement_bindings(&stmt, &mut current_substitution);
        rewritten.push(stmt);
    }

    rewritten
}

fn substitute_inline_statement(stmt: Statement, substitution: &HashMap<Ident, Ident>) -> Statement {
    let Statement { desc, comment } = stmt;
    let desc = match desc {
        StatementDesc::Block(block) => {
            StatementDesc::Block(substitute_inline_block(block, substitution))
        }
        StatementDesc::Variable(mut decl) => {
            decl.value = decl
                .value
                .map(|value| substitute_inline_expression(value, substitution));
            StatementDesc::Variable(decl)
        }
        StatementDesc::Exp(expr) => {
            StatementDesc::Exp(substitute_inline_expression(expr, substitution))
        }
        StatementDesc::If(cond, then_block, else_block) => StatementDesc::If(
            substitute_inline_expression(cond, substitution),
            substitute_inline_block(then_block, substitution),
            substitute_inline_block(else_block, substitution),
        ),
        StatementDesc::While(cond, body) => StatementDesc::While(
            substitute_inline_expression(cond, substitution),
            substitute_inline_block(body, substitution),
        ),
        StatementDesc::ForRange(start, finish, ident, direction, body) => {
            let body_substitution = prune_inline_substitution(substitution, [&ident]);
            StatementDesc::ForRange(
                start.map(|expr| substitute_inline_expression(expr, substitution)),
                substitute_inline_expression(finish, substitution),
                ident,
                direction,
                substitute_inline_block(body, &body_substitution),
            )
        }
        StatementDesc::Continue => StatementDesc::Continue,
        StatementDesc::Break => StatementDesc::Break,
        StatementDesc::Return(expr) => {
            StatementDesc::Return(substitute_inline_expression(expr, substitution))
        }
        StatementDesc::IntSwitch(test, clauses, default) => StatementDesc::IntSwitch(
            substitute_inline_expression(test, substitution),
            clauses
                .into_iter()
                .map(|(value, clause)| {
                    (
                        value,
                        CaseClause {
                            body: substitute_inline_block(clause.body, substitution),
                            should_break: clause.should_break,
                            comment: clause.comment,
                        },
                    )
                })
                .collect(),
            default.map(|block| substitute_inline_block(block, substitution)),
        ),
        StatementDesc::StringSwitch(test, clauses, default) => StatementDesc::StringSwitch(
            substitute_inline_expression(test, substitution),
            clauses
                .into_iter()
                .map(|clause| StringClause {
                    tag_type: clause.tag_type,
                    clause: CaseClause {
                        body: substitute_inline_block(clause.clause.body, substitution),
                        should_break: clause.clause.should_break,
                        comment: clause.clause.comment,
                    },
                })
                .collect(),
            default.map(|block| substitute_inline_block(block, substitution)),
        ),
        StatementDesc::Throw(expr) => {
            StatementDesc::Throw(substitute_inline_expression(expr, substitution))
        }
        StatementDesc::Try(body, catch, finally) => StatementDesc::Try(
            substitute_inline_block(body, substitution),
            catch.map(|(ident, block)| {
                let catch_substitution = prune_inline_substitution(substitution, [&ident]);
                (ident, substitute_inline_block(block, &catch_substitution))
            }),
            finally.map(|block| substitute_inline_block(block, substitution)),
        ),
        StatementDesc::Debugger => StatementDesc::Debugger,
    };

    Statement { desc, comment }
}

fn substitute_inline_expression(
    expr: Expression,
    substitution: &HashMap<Ident, Ident>,
) -> Expression {
    let Expression { desc, comment } = expr;
    let desc = match desc {
        ExpressionDesc::Length(inner, obj) => ExpressionDesc::Length(
            Box::new(substitute_inline_expression(*inner, substitution)),
            obj,
        ),
        ExpressionDesc::IsNullOrUndefined(inner) => ExpressionDesc::IsNullOrUndefined(Box::new(
            substitute_inline_expression(*inner, substitution),
        )),
        ExpressionDesc::StringAppend(left, right) => ExpressionDesc::StringAppend(
            Box::new(substitute_inline_expression(*left, substitution)),
            Box::new(substitute_inline_expression(*right, substitution)),
        ),
        ExpressionDesc::Bool(value) => ExpressionDesc::Bool(value),
        ExpressionDesc::Typeof(inner) => {
            ExpressionDesc::Typeof(Box::new(substitute_inline_expression(*inner, substitution)))
        }
        ExpressionDesc::In(left, right) => ExpressionDesc::In(
            Box::new(substitute_inline_expression(*left, substitution)),
            Box::new(substitute_inline_expression(*right, substitution)),
        ),
        ExpressionDesc::JsNot(inner) => {
            ExpressionDesc::JsNot(Box::new(substitute_inline_expression(*inner, substitution)))
        }
        ExpressionDesc::JsBnot(inner) => {
            ExpressionDesc::JsBnot(Box::new(substitute_inline_expression(*inner, substitution)))
        }
        ExpressionDesc::Seq(left, right) => ExpressionDesc::Seq(
            Box::new(substitute_inline_expression(*left, substitution)),
            Box::new(substitute_inline_expression(*right, substitution)),
        ),
        ExpressionDesc::Cond(test, consequent, alternate) => ExpressionDesc::Cond(
            Box::new(substitute_inline_expression(*test, substitution)),
            Box::new(substitute_inline_expression(*consequent, substitution)),
            Box::new(substitute_inline_expression(*alternate, substitution)),
        ),
        ExpressionDesc::Bin(op, left, right) => ExpressionDesc::Bin(
            op,
            Box::new(substitute_inline_expression(*left, substitution)),
            Box::new(substitute_inline_expression(*right, substitution)),
        ),
        ExpressionDesc::FlatCall(func, args) => ExpressionDesc::FlatCall(
            Box::new(substitute_inline_expression(*func, substitution)),
            Box::new(substitute_inline_expression(*args, substitution)),
        ),
        ExpressionDesc::Call(func, args, info) => ExpressionDesc::Call(
            Box::new(substitute_inline_expression(*func, substitution)),
            args.into_iter()
                .map(|arg| substitute_inline_expression(arg, substitution))
                .collect(),
            info,
        ),
        ExpressionDesc::StringIndex(left, right) => ExpressionDesc::StringIndex(
            Box::new(substitute_inline_expression(*left, substitution)),
            Box::new(substitute_inline_expression(*right, substitution)),
        ),
        ExpressionDesc::ArrayIndex(left, right) => ExpressionDesc::ArrayIndex(
            Box::new(substitute_inline_expression(*left, substitution)),
            Box::new(substitute_inline_expression(*right, substitution)),
        ),
        ExpressionDesc::TaggedTemplate(tag, strings, values) => ExpressionDesc::TaggedTemplate(
            Box::new(substitute_inline_expression(*tag, substitution)),
            strings
                .into_iter()
                .map(|expr| substitute_inline_expression(expr, substitution))
                .collect(),
            values
                .into_iter()
                .map(|expr| substitute_inline_expression(expr, substitution))
                .collect(),
        ),
        ExpressionDesc::StaticIndex(target, field, position) => ExpressionDesc::StaticIndex(
            Box::new(substitute_inline_expression(*target, substitution)),
            field,
            position,
        ),
        ExpressionDesc::New(target, args) => ExpressionDesc::New(
            Box::new(substitute_inline_expression(*target, substitution)),
            args.map(|args| {
                args.into_iter()
                    .map(|arg| substitute_inline_expression(arg, substitution))
                    .collect()
            }),
        ),
        ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)) => {
            let id = substitution.get(&id).cloned().unwrap_or(id);
            ExpressionDesc::Var(crate::js_ir::VIdent::Id(id))
        }
        ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(module, member)) => {
            ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(module, member))
        }
        ExpressionDesc::Fun {
            is_method,
            params,
            body,
            env,
            return_unit,
            async_,
            directive,
        } => ExpressionDesc::Fun {
            is_method,
            body: {
                let body_substitution = prune_inline_substitution(substitution, params.iter());
                substitute_inline_block(body, &body_substitution)
            },
            params,
            env,
            return_unit,
            async_,
            directive,
        },
        ExpressionDesc::Str { delim, txt } => ExpressionDesc::Str { delim, txt },
        ExpressionDesc::RawJsCode(info) => ExpressionDesc::RawJsCode(info),
        ExpressionDesc::Array(items, mutable_flag) => ExpressionDesc::Array(
            items
                .into_iter()
                .map(|item| substitute_inline_expression(item, substitution))
                .collect(),
            mutable_flag,
        ),
        ExpressionDesc::OptionalBlock(inner, flag) => ExpressionDesc::OptionalBlock(
            Box::new(substitute_inline_expression(*inner, substitution)),
            flag,
        ),
        ExpressionDesc::CamlBlock(items, mutable_flag, tag, info) => ExpressionDesc::CamlBlock(
            items
                .into_iter()
                .map(|item| substitute_inline_expression(item, substitution))
                .collect(),
            mutable_flag,
            Box::new(substitute_inline_expression(*tag, substitution)),
            info,
        ),
        ExpressionDesc::CamlBlockTag(inner, field) => ExpressionDesc::CamlBlockTag(
            Box::new(substitute_inline_expression(*inner, substitution)),
            field,
        ),
        ExpressionDesc::Number(number) => ExpressionDesc::Number(number),
        ExpressionDesc::Object(dup, props) => ExpressionDesc::Object(
            dup.map(|expr| Box::new(substitute_inline_expression(*expr, substitution))),
            props
                .into_iter()
                .map(|(name, value)| (name, substitute_inline_expression(value, substitution)))
                .collect(),
        ),
        ExpressionDesc::Undefined { is_unit } => ExpressionDesc::Undefined { is_unit },
        ExpressionDesc::Null => ExpressionDesc::Null,
        ExpressionDesc::Await(inner) => {
            ExpressionDesc::Await(Box::new(substitute_inline_expression(*inner, substitution)))
        }
        ExpressionDesc::Spread(inner) => {
            ExpressionDesc::Spread(Box::new(substitute_inline_expression(*inner, substitution)))
        }
    };

    Expression { desc, comment }
}

fn prune_inline_substitution<'a>(
    substitution: &HashMap<Ident, Ident>,
    shadowed: impl IntoIterator<Item = &'a Ident>,
) -> HashMap<Ident, Ident> {
    let mut pruned = substitution.clone();
    for ident in shadowed {
        pruned.remove(ident);
    }
    pruned
}

fn shadow_inline_statement_bindings(
    stmt: &Statement,
    substitution: &mut HashMap<Ident, Ident>,
) {
    if let StatementDesc::Variable(VariableDeclaration { ident, .. }) = &stmt.desc {
        substitution.remove(ident);
    }
}

fn apply_tailcall_used_stats_block(block: &mut Block, statuses: &HashMap<Ident, UsedStats>) {
    for stmt in block {
        apply_tailcall_used_stats_statement(stmt, statuses);
    }
}

fn apply_tailcall_used_stats_statement(stmt: &mut Statement, statuses: &HashMap<Ident, UsedStats>) {
    match &mut stmt.desc {
        StatementDesc::Block(block) => apply_tailcall_used_stats_block(block, statuses),
        StatementDesc::Variable(decl) => {
            if let Some(status) = statuses.get(&decl.ident).copied() {
                decl.ident_info.used_stats = status;
            }
            if let Some(value) = &mut decl.value {
                apply_tailcall_used_stats_expression(value, statuses);
            }
        }
        StatementDesc::Exp(expr) | StatementDesc::Return(expr) | StatementDesc::Throw(expr) => {
            apply_tailcall_used_stats_expression(expr, statuses);
        }
        StatementDesc::If(_, then_block, else_block) => {
            apply_tailcall_used_stats_block(then_block, statuses);
            apply_tailcall_used_stats_block(else_block, statuses);
        }
        StatementDesc::While(_, body) => apply_tailcall_used_stats_block(body, statuses),
        StatementDesc::ForRange(_, _, _, _, body) => {
            apply_tailcall_used_stats_block(body, statuses)
        }
        StatementDesc::IntSwitch(_, clauses, default) => {
            for (_, clause) in clauses {
                apply_tailcall_used_stats_block(&mut clause.body, statuses);
            }
            if let Some(default) = default {
                apply_tailcall_used_stats_block(default, statuses);
            }
        }
        StatementDesc::StringSwitch(_, clauses, default) => {
            for clause in clauses {
                apply_tailcall_used_stats_block(&mut clause.clause.body, statuses);
            }
            if let Some(default) = default {
                apply_tailcall_used_stats_block(default, statuses);
            }
        }
        StatementDesc::Try(body, catch, finally) => {
            apply_tailcall_used_stats_block(body, statuses);
            if let Some((_, block)) = catch {
                apply_tailcall_used_stats_block(block, statuses);
            }
            if let Some(block) = finally {
                apply_tailcall_used_stats_block(block, statuses);
            }
        }
        StatementDesc::Debugger | StatementDesc::Break | StatementDesc::Continue => {}
    }
}

fn apply_tailcall_used_stats_expression(
    expr: &mut Expression,
    statuses: &HashMap<Ident, UsedStats>,
) {
    match &mut expr.desc {
        ExpressionDesc::Length(inner, _)
        | ExpressionDesc::IsNullOrUndefined(inner)
        | ExpressionDesc::Typeof(inner)
        | ExpressionDesc::JsNot(inner)
        | ExpressionDesc::JsBnot(inner)
        | ExpressionDesc::CamlBlockTag(inner, _)
        | ExpressionDesc::OptionalBlock(inner, _)
        | ExpressionDesc::Await(inner)
        | ExpressionDesc::Spread(inner) => apply_tailcall_used_stats_expression(inner, statuses),
        ExpressionDesc::StringAppend(left, right)
        | ExpressionDesc::In(left, right)
        | ExpressionDesc::Seq(left, right)
        | ExpressionDesc::Bin(_, left, right)
        | ExpressionDesc::FlatCall(left, right)
        | ExpressionDesc::StringIndex(left, right)
        | ExpressionDesc::ArrayIndex(left, right) => {
            apply_tailcall_used_stats_expression(left, statuses);
            apply_tailcall_used_stats_expression(right, statuses);
        }
        ExpressionDesc::Cond(test, consequent, alternate) => {
            apply_tailcall_used_stats_expression(test, statuses);
            apply_tailcall_used_stats_expression(consequent, statuses);
            apply_tailcall_used_stats_expression(alternate, statuses);
        }
        ExpressionDesc::Call(func, args, _) => {
            apply_tailcall_used_stats_expression(func, statuses);
            for arg in args {
                apply_tailcall_used_stats_expression(arg, statuses);
            }
        }
        ExpressionDesc::TaggedTemplate(tag, strings, values) => {
            apply_tailcall_used_stats_expression(tag, statuses);
            for string in strings {
                apply_tailcall_used_stats_expression(string, statuses);
            }
            for value in values {
                apply_tailcall_used_stats_expression(value, statuses);
            }
        }
        ExpressionDesc::StaticIndex(target, _, _) => {
            apply_tailcall_used_stats_expression(target, statuses)
        }
        ExpressionDesc::New(target, args) => {
            apply_tailcall_used_stats_expression(target, statuses);
            if let Some(args) = args {
                for arg in args {
                    apply_tailcall_used_stats_expression(arg, statuses);
                }
            }
        }
        ExpressionDesc::Fun { body, .. } => apply_tailcall_used_stats_block(body, statuses),
        ExpressionDesc::Array(items, _) => {
            for item in items {
                apply_tailcall_used_stats_expression(item, statuses);
            }
        }
        ExpressionDesc::CamlBlock(items, _, tag, _) => {
            for item in items {
                apply_tailcall_used_stats_expression(item, statuses);
            }
            apply_tailcall_used_stats_expression(tag, statuses);
        }
        ExpressionDesc::Object(dup, props) => {
            if let Some(dup) = dup {
                apply_tailcall_used_stats_expression(dup, statuses);
            }
            for (_, value) in props {
                apply_tailcall_used_stats_expression(value, statuses);
            }
        }
        ExpressionDesc::Var(_)
        | ExpressionDesc::Undefined { .. }
        | ExpressionDesc::Null
        | ExpressionDesc::Bool(_)
        | ExpressionDesc::Str { .. }
        | ExpressionDesc::RawJsCode(_)
        | ExpressionDesc::Number(_) => {}
    }
}

fn apply_js_shake_pass(mut deps: DepsProgram) -> DepsProgram {
    deps.program = shake_program(deps.program);
    deps
}

fn shake_program(mut program: Program) -> Program {
    program.block = shake_block(&program.block, &program.export_set);
    program
}

fn shake_block(block: &Block, export_set: &HashSet<Ident>) -> Block {
    let block = flatten_toplevel_block(block);
    let required = fixed_point_required_idents(&block, export_set);

    block
        .into_iter()
        .filter(|stmt| match &stmt.desc {
            StatementDesc::Variable(VariableDeclaration { ident, value, .. }) => {
                if required.contains(ident) {
                    true
                } else {
                    value
                        .as_ref()
                        .is_some_and(|expr| !js_expr_no_side_effects(expr))
                }
            }
            _ => !js_statement_no_side_effects(stmt),
        })
        .collect()
}

fn flatten_toplevel_block(block: &Block) -> Block {
    let mut flattened = Vec::new();
    flatten_toplevel_block_into(block, &mut flattened);
    flattened
}

fn flatten_toplevel_block_into(block: &Block, flattened: &mut Block) {
    for stmt in block {
        match &stmt.desc {
            StatementDesc::Variable(VariableDeclaration {
                ident_info:
                    IdentInfo {
                        used_stats: UsedStats::DeadPure,
                    },
                ..
            })
            | StatementDesc::Variable(VariableDeclaration {
                ident_info:
                    IdentInfo {
                        used_stats: UsedStats::DeadNonPure,
                    },
                value: None,
                ..
            }) => {}
            StatementDesc::Block(inner) => flatten_toplevel_block_into(inner, flattened),
            _ => flattened.push(stmt.clone()),
        }
    }
}

fn fixed_point_required_idents(block: &Block, export_set: &HashSet<Ident>) -> HashSet<Ident> {
    let mut required = required_idents(block, export_set, true);
    loop {
        let next = required_idents(block, &required, false);
        if next.len() == required.len() && next.is_subset(&required) {
            return required;
        }
        required = next;
    }
}

fn required_idents(
    block: &Block,
    initial: &HashSet<Ident>,
    count_effect_statements: bool,
) -> HashSet<Ident> {
    let mut required = initial.clone();

    for stmt in block {
        match &stmt.desc {
            StatementDesc::Variable(VariableDeclaration { ident, value, .. }) => {
                if required.contains(ident) {
                    if let Some(value) = value {
                        required.extend(free_variables_of_expression(value));
                    }
                } else if let Some(value) = value {
                    if !js_expr_no_side_effects(value) {
                        required.insert(ident.clone());
                        required.extend(free_variables_of_expression(value));
                    }
                }
            }
            _ => {
                if count_effect_statements && !js_statement_no_side_effects(stmt) {
                    required.extend(free_variables_of_statement(stmt));
                }
            }
        }
    }

    required
}

#[derive(Default)]
struct JsIdentStats {
    used_idents: HashSet<Ident>,
    defined_idents: HashSet<Ident>,
}

impl JsIdentStats {
    fn with_defined<I>(idents: I) -> Self
    where
        I: IntoIterator<Item = Ident>,
    {
        Self {
            used_idents: HashSet::new(),
            defined_idents: idents.into_iter().collect(),
        }
    }

    fn add_used_ident(&mut self, ident: &Ident) {
        if !self.defined_idents.contains(ident) {
            self.used_idents.insert(ident.clone());
        }
    }

    fn add_defined_ident(&mut self, ident: &Ident) {
        self.defined_idents.insert(ident.clone());
    }

    fn extend_free_idents(&mut self, other: HashSet<Ident>) {
        self.used_idents.extend(other);
    }

    fn free_variables(mut self) -> HashSet<Ident> {
        self.used_idents
            .retain(|ident| !self.defined_idents.contains(ident));
        self.used_idents
    }
}

fn free_variables_of_statement(stmt: &Statement) -> HashSet<Ident> {
    let mut stats = JsIdentStats::default();
    collect_statement_idents(stmt, &mut stats);
    stats.free_variables()
}

fn free_variables_of_expression(expr: &Expression) -> HashSet<Ident> {
    let mut stats = JsIdentStats::default();
    collect_expression_idents(expr, &mut stats);
    stats.free_variables()
}

fn free_variables_of_block_with_defined(
    block: &Block,
    defined: impl IntoIterator<Item = Ident>,
) -> HashSet<Ident> {
    let mut stats = JsIdentStats::with_defined(defined);
    collect_block_idents(block, &mut stats);
    stats.free_variables()
}

fn collect_block_idents(block: &Block, stats: &mut JsIdentStats) {
    for stmt in block {
        collect_statement_idents(stmt, stats);
    }
}

fn collect_statement_idents(stmt: &Statement, stats: &mut JsIdentStats) {
    match &stmt.desc {
        StatementDesc::Block(block) => collect_block_idents(block, stats),
        StatementDesc::Variable(VariableDeclaration { ident, value, .. }) => {
            stats.add_defined_ident(ident);
            if let Some(value) = value {
                collect_expression_idents(value, stats);
            }
        }
        StatementDesc::Exp(expr) | StatementDesc::Return(expr) | StatementDesc::Throw(expr) => {
            collect_expression_idents(expr, stats);
        }
        StatementDesc::If(cond, then_block, else_block) => {
            collect_expression_idents(cond, stats);
            collect_block_idents(then_block, stats);
            collect_block_idents(else_block, stats);
        }
        StatementDesc::While(cond, body) => {
            collect_expression_idents(cond, stats);
            collect_block_idents(body, stats);
        }
        StatementDesc::ForRange(start, finish, loop_ident, _, body) => {
            if let Some(start) = start {
                collect_expression_idents(start, stats);
            }
            collect_expression_idents(finish, stats);
            stats.extend_free_idents(free_variables_of_block_with_defined(
                body,
                std::iter::once(loop_ident.clone()),
            ));
        }
        StatementDesc::IntSwitch(test, clauses, default) => {
            collect_expression_idents(test, stats);
            for (_, clause) in clauses {
                collect_block_idents(&clause.body, stats);
            }
            if let Some(default) = default {
                collect_block_idents(default, stats);
            }
        }
        StatementDesc::StringSwitch(test, clauses, default) => {
            collect_expression_idents(test, stats);
            for clause in clauses {
                collect_block_idents(&clause.clause.body, stats);
            }
            if let Some(default) = default {
                collect_block_idents(default, stats);
            }
        }
        StatementDesc::Try(body, catch, finally) => {
            collect_block_idents(body, stats);
            if let Some((catch_ident, catch_block)) = catch {
                stats.extend_free_idents(free_variables_of_block_with_defined(
                    catch_block,
                    std::iter::once(catch_ident.clone()),
                ));
            }
            if let Some(finally) = finally {
                collect_block_idents(finally, stats);
            }
        }
        StatementDesc::Debugger | StatementDesc::Break | StatementDesc::Continue => {}
    }
}

fn collect_expression_idents(expr: &Expression, stats: &mut JsIdentStats) {
    match &expr.desc {
        ExpressionDesc::Var(crate::js_ir::VIdent::Id(ident)) => stats.add_used_ident(ident),
        ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(_, _))
        | ExpressionDesc::Undefined { .. }
        | ExpressionDesc::Null
        | ExpressionDesc::Bool(_)
        | ExpressionDesc::Str { .. }
        | ExpressionDesc::RawJsCode(_)
        | ExpressionDesc::Number(_) => {}
        ExpressionDesc::Length(inner, _)
        | ExpressionDesc::IsNullOrUndefined(inner)
        | ExpressionDesc::Typeof(inner)
        | ExpressionDesc::JsNot(inner)
        | ExpressionDesc::JsBnot(inner)
        | ExpressionDesc::CamlBlockTag(inner, _)
        | ExpressionDesc::OptionalBlock(inner, _)
        | ExpressionDesc::Await(inner)
        | ExpressionDesc::Spread(inner) => collect_expression_idents(inner, stats),
        ExpressionDesc::StringAppend(left, right)
        | ExpressionDesc::In(left, right)
        | ExpressionDesc::Seq(left, right)
        | ExpressionDesc::Bin(_, left, right)
        | ExpressionDesc::FlatCall(left, right)
        | ExpressionDesc::StringIndex(left, right)
        | ExpressionDesc::ArrayIndex(left, right) => {
            collect_expression_idents(left, stats);
            collect_expression_idents(right, stats);
        }
        ExpressionDesc::Cond(test, consequent, alternate) => {
            collect_expression_idents(test, stats);
            collect_expression_idents(consequent, stats);
            collect_expression_idents(alternate, stats);
        }
        ExpressionDesc::Call(func, args, _) => {
            collect_expression_idents(func, stats);
            for arg in args {
                collect_expression_idents(arg, stats);
            }
        }
        ExpressionDesc::TaggedTemplate(tag, strings, values) => {
            collect_expression_idents(tag, stats);
            for string in strings {
                collect_expression_idents(string, stats);
            }
            for value in values {
                collect_expression_idents(value, stats);
            }
        }
        ExpressionDesc::StaticIndex(target, _, _) => collect_expression_idents(target, stats),
        ExpressionDesc::New(target, args) => {
            collect_expression_idents(target, stats);
            if let Some(args) = args {
                for arg in args {
                    collect_expression_idents(arg, stats);
                }
            }
        }
        ExpressionDesc::Fun { params, body, .. } => {
            stats.extend_free_idents(free_variables_of_block_with_defined(
                body,
                params.iter().cloned(),
            ));
        }
        ExpressionDesc::Array(items, _) => {
            for item in items {
                collect_expression_idents(item, stats);
            }
        }
        ExpressionDesc::CamlBlock(items, _, tag, _) => {
            for item in items {
                collect_expression_idents(item, stats);
            }
            collect_expression_idents(tag, stats);
        }
        ExpressionDesc::Object(dup, props) => {
            if let Some(dup) = dup {
                collect_expression_idents(dup, stats);
            }
            for (_, value) in props {
                collect_expression_idents(value, stats);
            }
        }
    }
}

fn js_block_no_side_effects(block: &Block) -> bool {
    block.iter().all(js_statement_no_side_effects)
}

fn js_statement_no_side_effects(stmt: &Statement) -> bool {
    match &stmt.desc {
        StatementDesc::Throw(_)
        | StatementDesc::Debugger
        | StatementDesc::Break
        | StatementDesc::Variable(_)
        | StatementDesc::Continue => false,
        StatementDesc::Exp(expr) | StatementDesc::Return(expr) => js_expr_no_side_effects(expr),
        StatementDesc::Block(block) => js_block_no_side_effects(block),
        StatementDesc::If(cond, then_block, else_block) => {
            js_expr_no_side_effects(cond)
                && js_block_no_side_effects(then_block)
                && js_block_no_side_effects(else_block)
        }
        StatementDesc::While(cond, body) => {
            js_expr_no_side_effects(cond) && js_block_no_side_effects(body)
        }
        StatementDesc::ForRange(start, finish, _, _, body) => {
            start.as_ref().is_none_or(js_expr_no_side_effects)
                && js_expr_no_side_effects(finish)
                && js_block_no_side_effects(body)
        }
        StatementDesc::IntSwitch(test, clauses, default) => {
            js_expr_no_side_effects(test)
                && clauses
                    .iter()
                    .all(|(_, clause)| js_block_no_side_effects(&clause.body))
                && default.as_ref().is_none_or(js_block_no_side_effects)
        }
        StatementDesc::StringSwitch(test, clauses, default) => {
            js_expr_no_side_effects(test)
                && clauses
                    .iter()
                    .all(|clause| js_block_no_side_effects(&clause.clause.body))
                && default.as_ref().is_none_or(js_block_no_side_effects)
        }
        StatementDesc::Try(body, catch, finally) => {
            js_block_no_side_effects(body)
                && catch
                    .as_ref()
                    .is_none_or(|(_, block)| js_block_no_side_effects(block))
                && finally.as_ref().is_none_or(js_block_no_side_effects)
        }
    }
}

fn is_lexical_binding_kind(property: LetKind) -> bool {
    matches!(
        property,
        LetKind::Strict | LetKind::StrictOpt | LetKind::Alias
    )
}

fn should_rewrite_binding(ident: &Ident) -> bool {
    !ident.is_global() && !is_js_keyword_or_global(ident.name())
}

fn rewrite_block(block: &Block, shadowed_globals: &HashSet<String>) -> Block {
    block
        .iter()
        .map(|stmt| rewrite_statement(stmt, shadowed_globals))
        .collect()
}

fn rewrite_statement(stmt: &Statement, shadowed_globals: &HashSet<String>) -> Statement {
    let desc = match &stmt.desc {
        StatementDesc::Block(block) => StatementDesc::Block(rewrite_block(block, shadowed_globals)),
        StatementDesc::Variable(decl) => {
            let value = decl.value.as_ref().map(|value| {
                let value = if is_lexical_binding_kind(decl.property)
                    && should_rewrite_binding(&decl.ident)
                {
                    rewrite_shadowed_global_in_expr(value, decl.ident.name())
                } else {
                    value.clone()
                };
                rewrite_global_static_index_expr(&value, shadowed_globals)
            });
            StatementDesc::Variable(VariableDeclaration {
                ident: decl.ident.clone(),
                value,
                property: decl.property,
                ident_info: decl.ident_info.clone(),
            })
        }
        StatementDesc::Exp(expr) => {
            StatementDesc::Exp(rewrite_global_static_index_expr(expr, shadowed_globals))
        }
        StatementDesc::If(cond, then_block, else_block) => StatementDesc::If(
            rewrite_global_static_index_expr(cond, shadowed_globals),
            rewrite_block(then_block, shadowed_globals),
            rewrite_block(else_block, shadowed_globals),
        ),
        StatementDesc::While(cond, body) => StatementDesc::While(
            rewrite_global_static_index_expr(cond, shadowed_globals),
            rewrite_block(body, shadowed_globals),
        ),
        StatementDesc::ForRange(init, end, id, direction, body) => StatementDesc::ForRange(
            init.as_ref()
                .map(|expr| rewrite_global_static_index_expr(expr, shadowed_globals)),
            rewrite_global_static_index_expr(end, shadowed_globals),
            id.clone(),
            *direction,
            rewrite_block(body, shadowed_globals),
        ),
        StatementDesc::Continue => StatementDesc::Continue,
        StatementDesc::Break => StatementDesc::Break,
        StatementDesc::Return(expr) => {
            StatementDesc::Return(rewrite_global_static_index_expr(expr, shadowed_globals))
        }
        StatementDesc::IntSwitch(expr, clauses, default) => StatementDesc::IntSwitch(
            rewrite_global_static_index_expr(expr, shadowed_globals),
            clauses
                .iter()
                .map(|(value, clause)| (*value, rewrite_case_clause(clause, shadowed_globals)))
                .collect(),
            default
                .as_ref()
                .map(|block| rewrite_block(block, shadowed_globals)),
        ),
        StatementDesc::StringSwitch(expr, clauses, default) => StatementDesc::StringSwitch(
            rewrite_global_static_index_expr(expr, shadowed_globals),
            clauses
                .iter()
                .map(|clause| crate::js_ir::StringClause {
                    tag_type: clause.tag_type.clone(),
                    clause: rewrite_case_clause(&clause.clause, shadowed_globals),
                })
                .collect(),
            default
                .as_ref()
                .map(|block| rewrite_block(block, shadowed_globals)),
        ),
        StatementDesc::Throw(expr) => {
            StatementDesc::Throw(rewrite_global_static_index_expr(expr, shadowed_globals))
        }
        StatementDesc::Try(body, catch, finally) => StatementDesc::Try(
            rewrite_block(body, shadowed_globals),
            catch
                .as_ref()
                .map(|(ident, block)| (ident.clone(), rewrite_block(block, shadowed_globals))),
            finally
                .as_ref()
                .map(|block| rewrite_block(block, shadowed_globals)),
        ),
        StatementDesc::Debugger => StatementDesc::Debugger,
    };

    Statement {
        desc,
        comment: stmt.comment.clone(),
    }
}

fn rewrite_case_clause(
    clause: &crate::js_ir::CaseClause,
    shadowed_globals: &HashSet<String>,
) -> crate::js_ir::CaseClause {
    crate::js_ir::CaseClause {
        body: rewrite_block(&clause.body, shadowed_globals),
        should_break: clause.should_break,
        comment: clause.comment.clone(),
    }
}

fn rewrite_shadowed_global_in_expr(expr: &Expression, name: &str) -> Expression {
    let expr = rewrite_expr_children(expr, &|child| rewrite_shadowed_global_in_expr(child, name));
    match &expr.desc {
        ExpressionDesc::Var(crate::js_ir::VIdent::Id(id))
            if id.is_global() && id.name() == name =>
        {
            global_this_field(name)
        }
        _ => expr,
    }
}

fn rewrite_global_static_index_expr(
    expr: &Expression,
    shadowed_globals: &HashSet<String>,
) -> Expression {
    let expr = rewrite_expr_children(expr, &|child| {
        rewrite_global_static_index_expr(child, shadowed_globals)
    });
    match &expr.desc {
        ExpressionDesc::StaticIndex(obj, field, pos) => match &obj.desc {
            ExpressionDesc::Var(crate::js_ir::VIdent::Id(id))
                if id.is_global() && shadowed_globals.contains(id.name()) =>
            {
                Expression::new(ExpressionDesc::StaticIndex(
                    Box::new(global_this_field(id.name())),
                    field.clone(),
                    *pos,
                ))
            }
            _ => expr,
        },
        _ => expr,
    }
}

fn rewrite_expr_children(
    expr: &Expression,
    rewrite: &impl Fn(&Expression) -> Expression,
) -> Expression {
    let desc = match &expr.desc {
        ExpressionDesc::Length(inner, kind) => {
            ExpressionDesc::Length(Box::new(rewrite(inner)), kind.clone())
        }
        ExpressionDesc::IsNullOrUndefined(inner) => {
            ExpressionDesc::IsNullOrUndefined(Box::new(rewrite(inner)))
        }
        ExpressionDesc::StringAppend(left, right) => {
            ExpressionDesc::StringAppend(Box::new(rewrite(left)), Box::new(rewrite(right)))
        }
        ExpressionDesc::Bool(value) => ExpressionDesc::Bool(*value),
        ExpressionDesc::Typeof(inner) => ExpressionDesc::Typeof(Box::new(rewrite(inner))),
        ExpressionDesc::In(left, right) => {
            ExpressionDesc::In(Box::new(rewrite(left)), Box::new(rewrite(right)))
        }
        ExpressionDesc::JsNot(inner) => ExpressionDesc::JsNot(Box::new(rewrite(inner))),
        ExpressionDesc::JsBnot(inner) => ExpressionDesc::JsBnot(Box::new(rewrite(inner))),
        ExpressionDesc::Seq(first, second) => {
            ExpressionDesc::Seq(Box::new(rewrite(first)), Box::new(rewrite(second)))
        }
        ExpressionDesc::Cond(cond, then_, else_) => ExpressionDesc::Cond(
            Box::new(rewrite(cond)),
            Box::new(rewrite(then_)),
            Box::new(rewrite(else_)),
        ),
        ExpressionDesc::Bin(op, left, right) => {
            ExpressionDesc::Bin(*op, Box::new(rewrite(left)), Box::new(rewrite(right)))
        }
        ExpressionDesc::FlatCall(func, args) => {
            ExpressionDesc::FlatCall(Box::new(rewrite(func)), Box::new(rewrite(args)))
        }
        ExpressionDesc::Call(func, args, info) => ExpressionDesc::Call(
            Box::new(rewrite(func)),
            args.iter().map(rewrite).collect(),
            info.clone(),
        ),
        ExpressionDesc::StringIndex(value, index) => {
            ExpressionDesc::StringIndex(Box::new(rewrite(value)), Box::new(rewrite(index)))
        }
        ExpressionDesc::ArrayIndex(value, index) => {
            ExpressionDesc::ArrayIndex(Box::new(rewrite(value)), Box::new(rewrite(index)))
        }
        ExpressionDesc::TaggedTemplate(func, strings, values) => ExpressionDesc::TaggedTemplate(
            Box::new(rewrite(func)),
            strings.iter().map(rewrite).collect(),
            values.iter().map(rewrite).collect(),
        ),
        ExpressionDesc::StaticIndex(obj, field, pos) => {
            ExpressionDesc::StaticIndex(Box::new(rewrite(obj)), field.clone(), *pos)
        }
        ExpressionDesc::New(ctor, args) => ExpressionDesc::New(
            Box::new(rewrite(ctor)),
            args.as_ref()
                .map(|items| items.iter().map(rewrite).collect()),
        ),
        ExpressionDesc::Var(vident) => ExpressionDesc::Var(vident.clone()),
        ExpressionDesc::Fun {
            is_method,
            params,
            body,
            env,
            return_unit,
            async_,
            directive,
        } => ExpressionDesc::Fun {
            is_method: *is_method,
            params: params.clone(),
            body: rewrite_block(body, &HashSet::new()),
            env: env.clone(),
            return_unit: *return_unit,
            async_: *async_,
            directive: directive.clone(),
        },
        ExpressionDesc::Str { delim, txt } => ExpressionDesc::Str {
            delim: *delim,
            txt: txt.clone(),
        },
        ExpressionDesc::RawJsCode(info) => ExpressionDesc::RawJsCode(info.clone()),
        ExpressionDesc::Array(items, mutable_flag) => {
            ExpressionDesc::Array(items.iter().map(rewrite).collect(), *mutable_flag)
        }
        ExpressionDesc::OptionalBlock(value, flag) => {
            ExpressionDesc::OptionalBlock(Box::new(rewrite(value)), *flag)
        }
        ExpressionDesc::CamlBlock(values, mutable_flag, tag, tag_info) => {
            ExpressionDesc::CamlBlock(
                values.iter().map(rewrite).collect(),
                *mutable_flag,
                Box::new(rewrite(tag)),
                tag_info.clone(),
            )
        }
        ExpressionDesc::CamlBlockTag(value, tag) => {
            ExpressionDesc::CamlBlockTag(Box::new(rewrite(value)), tag.clone())
        }
        ExpressionDesc::Number(number) => ExpressionDesc::Number(number.clone()),
        ExpressionDesc::Object(proto, props) => ExpressionDesc::Object(
            proto.as_ref().map(|expr| Box::new(rewrite(expr))),
            props
                .iter()
                .map(|(name, value)| (name.clone(), rewrite(value)))
                .collect(),
        ),
        ExpressionDesc::Undefined { is_unit } => ExpressionDesc::Undefined { is_unit: *is_unit },
        ExpressionDesc::Null => ExpressionDesc::Null,
        ExpressionDesc::Await(inner) => ExpressionDesc::Await(Box::new(rewrite(inner))),
        ExpressionDesc::Spread(inner) => ExpressionDesc::Spread(Box::new(rewrite(inner))),
    };

    Expression {
        desc,
        comment: expr.comment.clone(),
    }
}

fn global_this_field(name: &str) -> Expression {
    Expression::new(ExpressionDesc::StaticIndex(
        Box::new(Expression::var(Ident::create_persistent("globalThis"))),
        name.to_string(),
        None,
    ))
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
        StatementDesc::Variable(decl) => {
            if let Some(value) = &decl.value {
                collect_modules_from_expression(value, modules);
            }
        }
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
mod tests {
    use super::*;
    use crate::cmi::persistent_env::PersistentEnv;
    use crate::js_ir::printer::print_deps_program_with_directives;
    use crate::js_ir::{ModulePathResolver, print_block, print_deps_program, print_expression};
    use crate::lambda::constant::{Constant, ConstructorRuntimeTag, ConstructorTag, PointerInfo};
    use crate::lambda::primitive::{
        ExternalArgAttr, ExternalArgConst, ExternalArgDelim, ExternalArgLabel, ExternalArgSpec,
        ExternalFfiKind, ExternalFfiSpec, ExternalModuleBindName, ExternalModuleName,
        ExternalObjLabel, ExternalObjSpec, ExternalReturnWrapper, ExternalSpec, JsRawInfo,
        Primitive,
    };
    use crate::lambda::{
        ApInfo, Apply, ApplyStatus, FunctionAttribute, InlineAttribute, Lambda, SwitchNames,
    };
    use crate::location::Location;
    use std::fs;
    use std::path::PathBuf;
    use tempfile::tempdir;

    fn write_ast_source_stub(ast_path: &std::path::Path, source_path: &std::path::Path) {
        let mut bytes = Vec::new();
        bytes.extend_from_slice(&0u32.to_be_bytes());
        bytes.extend_from_slice(source_path.to_string_lossy().as_bytes());
        bytes.push(b'\n');
        fs::write(ast_path, bytes).expect("failed to write ast source stub");
    }

    fn external_module(bundle: &str) -> ExternalModuleName {
        ExternalModuleName {
            bundle: bundle.to_string(),
            module_bind_name: ExternalModuleBindName::Nothing,
            import_attributes: None,
        }
    }

    fn resolver_with_checked_in_cmj() -> ModulePathResolver {
        let mut persistent_env = PersistentEnv::new();
        persistent_env.add_load_path(
            PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .parent()
                .expect("repo root")
                .join("tests")
                .join("tests")
                .join("lib")
                .join("ocaml"),
        );
        persistent_env.add_load_path(
            PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .parent()
                .expect("repo root")
                .join("packages")
                .join("@rescript")
                .join("runtime")
                .join("lib")
                .join("ocaml"),
        );
        ModulePathResolver::from_compile_options(
            None,
            Some(std::path::Path::new("/tmp/Effect.mjs")),
            None,
            Some(persistent_env),
        )
    }

    #[test]
    fn test_compile_constant_int() {
        let mut compiler = LambdaCompiler::new();
        let lam = Lambda::const_(Constant::int(7));
        let program = compiler.compile_program(&lam);
        assert!(!program.block.is_empty());
    }

    #[test]
    fn lowers_upto_subint_one_finish_to_ocaml_exclusive_for_range() {
        let mut compiler = LambdaCompiler::new();
        let i = Ident::create_local("i");
        let xs = Ident::create_local("xs");
        let lam = Lambda::for_(
            i,
            Lambda::const_(Constant::int(0)),
            Lambda::prim(
                Primitive::Psubint,
                vec![Lambda::var(xs), Lambda::const_(Constant::int(1))],
                Location::none(),
            ),
            crate::lambda::DirectionFlag::Upto,
            Lambda::unit(),
        );

        let compiled = compiler.compile_expr(&lam);
        let rendered = print_block(&compiled.prelude);

        assert_eq!(rendered.trim(), "for (let i = 0; i < xs; ++i) {}");
    }

    #[test]
    fn lowers_upto_predint_finish_to_ocaml_exclusive_for_range() {
        let mut compiler = LambdaCompiler::new();
        let i = Ident::create_local("i");
        let xs = Ident::create_local("xs");
        let lam = Lambda::for_(
            i,
            Lambda::const_(Constant::int(0)),
            Lambda::prim(
                Primitive::Poffsetint(-1),
                vec![Lambda::var(xs)],
                Location::none(),
            ),
            crate::lambda::DirectionFlag::Upto,
            Lambda::unit(),
        );

        let compiled = compiler.compile_expr(&lam);
        let rendered = print_block(&compiled.prelude);

        assert_eq!(rendered.trim(), "for (let i = 0; i < xs; ++i) {}");
    }

    #[test]
    fn compile_raw_js_trims_outer_whitespace_before_js_ir_printing() {
        let mut compiler = LambdaCompiler::new();
        let lam = Lambda::prim(
            Primitive::PrawJsCode(JsRawInfo {
                code: "\nif (import.meta.hot){\n  console.log('es6')\n}\n".to_string(),
                is_stmt: true,
            }),
            vec![],
            Location::none(),
        );

        let program = compiler.compile_program(&lam);
        let raw_code = program
            .block
            .iter()
            .find_map(|stmt| match &stmt.desc {
                StatementDesc::Exp(Expression {
                    desc: ExpressionDesc::RawJsCode(info),
                    ..
                }) => Some(info.code.as_str()),
                _ => None,
            })
            .expect("compiled raw js statement");

        assert_eq!(raw_code, "if (import.meta.hot){\n  console.log('es6')\n}");
    }

    #[test]
    fn compile_constant_named_constructor_uses_string_runtime_name() {
        let compiled = LambdaCompiler::compile_constant(&Constant::Int {
            i: 0,
            comment: Some(PointerInfo::Constructor(ConstructorTag {
                name: "NoParam".to_string(),
                const_: 1,
                non_const: 2,
                runtime_tag: None,
            })),
        });

        assert!(matches!(
            compiled,
            Expression {
                desc: ExpressionDesc::Str { ref txt, .. },
                ..
            } if txt == "NoParam"
        ));
    }

    #[test]
    fn compile_constant_constructor_runtime_tag_uses_runtime_literal() {
        let compiled = LambdaCompiler::compile_constant(&Constant::Int {
            i: 0,
            comment: Some(PointerInfo::Constructor(ConstructorTag {
                name: "Three".to_string(),
                const_: 1,
                non_const: 0,
                runtime_tag: Some(ConstructorRuntimeTag::String("three".to_string())),
            })),
        });

        assert!(matches!(
            compiled,
            Expression {
                desc: ExpressionDesc::Str { ref txt, .. },
                ..
            } if txt == "three"
        ));
    }

    #[test]
    fn compile_constant_empty_list_keeps_numeric_zero_with_pointer_comment() {
        let compiled = LambdaCompiler::compile_constant(&Constant::Int {
            i: 0,
            comment: Some(PointerInfo::Constructor(ConstructorTag {
                name: "[]".to_string(),
                const_: 1,
                non_const: 1,
                runtime_tag: None,
            })),
        });

        assert!(matches!(
            compiled,
            Expression {
                desc: ExpressionDesc::Number(Number::Int { i: 0, .. }),
                comment: Some(ref comment),
            }
            if comment == "[]"
        ));
        assert_eq!(print_expression(&compiled), "/* [] */0");
    }

    #[test]
    fn compile_constant_some_unit_boxes_undefined_none_encoding() {
        let compiled =
            LambdaCompiler::compile_constant(&Constant::Some(Box::new(Constant::JsUndefined {
                is_unit: true,
            })));

        assert!(matches!(
            compiled,
            Expression {
                desc: ExpressionDesc::OptionalBlock(ref inner, false),
                ..
            } if matches!(
                inner.as_ref(),
                Expression {
                    desc: ExpressionDesc::Undefined { is_unit: false },
                    ..
                }
            )
        ));
        assert_eq!(
            print_expression(&compiled),
            "Primitive_option.some(undefined)"
        );
    }

    #[test]
    fn compile_constant_preserves_marshaled_starj_strings() {
        let compiled = LambdaCompiler::compile_constant(&Constant::String {
            s: "\\\"".to_string(),
            delim: Some(StringDelim::StarJ),
        });

        assert!(matches!(
            compiled,
            Expression {
                desc: ExpressionDesc::Str {
                    delim: Delim::StarJ,
                    ref txt,
                },
                ..
            } if txt == "\\\""
        ));
        assert_eq!(print_expression(&compiled), "\"\\\"\"");
    }

    #[test]
    fn compile_constant_quotes_noquote_delim_strings_like_ocaml() {
        let compiled = LambdaCompiler::compile_constant(&Constant::String {
            s: "{foo:true}".to_string(),
            delim: Some(StringDelim::NoQuotes),
        });

        assert!(matches!(
            compiled,
            Expression {
                desc: ExpressionDesc::Str {
                    delim: Delim::None,
                    ref txt,
                },
                ..
            } if txt == "{foo:true}"
        ));
        assert_eq!(print_expression(&compiled), "\"{foo:true}\"");
    }

    #[test]
    fn switch_case_expr_preserves_marshaled_string_tags() {
        let compiled = LambdaCompiler::switch_case_expr(&SwitchCaseTag::String("\\\"".to_string()));

        assert!(matches!(
            compiled,
            Expression {
                desc: ExpressionDesc::Str {
                    delim: Delim::StarJ,
                    ref txt,
                },
                ..
            } if txt == "\\\""
        ));
        assert_eq!(print_expression(&compiled), "\"\\\"\"");
    }

    #[test]
    fn compile_constant_nested_some_none_preserves_nested_optional_boxes() {
        let compiled = LambdaCompiler::compile_constant(&Constant::Some(Box::new(Constant::Some(
            Box::new(Constant::JsUndefined { is_unit: false }),
        ))));

        assert_eq!(
            print_expression(&compiled),
            "Primitive_option.some(Primitive_option.some(undefined))"
        );
    }

    #[test]
    fn compile_float_pow_uses_js_exponentiation_operator() {
        let mut compiler = LambdaCompiler::new();
        let compiled = compiler.compile_expr(&Lambda::prim(
            Primitive::Ppowfloat,
            vec![
                Lambda::const_(Constant::float("2.")),
                Lambda::const_(Constant::float("3.")),
            ],
            Location::none(),
        ));

        assert!(compiled.prelude.is_empty());
        assert!(matches!(
            &compiled.expr,
            Expression {
                desc: ExpressionDesc::Bin(BinOp::Pow, left, right),
                ..
            } if matches!(
                left.as_ref(),
                Expression {
                    desc: ExpressionDesc::Number(Number::Float(_)),
                    ..
                }
            ) && matches!(
                right.as_ref(),
                Expression {
                    desc: ExpressionDesc::Number(Number::Float(_)),
                    ..
                }
            )
        ));
        let printed = print_expression(&compiled.expr);
        assert!(
            printed.contains("**"),
            "expected exponentiation operator, got {printed}"
        );
        assert!(
            !printed.contains("Math.pow"),
            "expected float pow lowering to avoid Math.pow, got {printed}"
        );
    }

    #[test]
    fn compile_int_pow_folds_small_int_literals_like_ocaml_ext_int() {
        let mut compiler = LambdaCompiler::new();
        let compiled = compiler.compile_expr(&Lambda::prim(
            Primitive::Ppowint,
            vec![
                Lambda::const_(Constant::int(2)),
                Lambda::const_(Constant::int(2)),
            ],
            Location::none(),
        ));

        assert!(compiled.prelude.is_empty());
        assert_int_expr(&compiled.expr, 4);
    }

    #[test]
    fn compile_int_pow_folds_overflowing_int_literals_like_ocaml_ext_int() {
        let mut compiler = LambdaCompiler::new();
        let compiled = compiler.compile_expr(&Lambda::prim(
            Primitive::Ppowint,
            vec![
                Lambda::const_(Constant::int(2_147_483_647)),
                Lambda::const_(Constant::int(2)),
            ],
            Location::none(),
        ));

        assert!(compiled.prelude.is_empty());
        assert_int_expr(&compiled.expr, 0);
    }

    #[test]
    fn compile_create_extension_uses_primitive_exceptions_create() {
        let mut compiler = LambdaCompiler::new();
        let compiled = compiler.compile_expr(&Lambda::prim(
            Primitive::PcreateExtension("Local_exception_test.A".to_string()),
            vec![],
            Location::none(),
        ));

        assert!(compiled.prelude.is_empty());
        let ExpressionDesc::Call(func, args, _) = &compiled.expr.desc else {
            panic!("expected extension constructors to lower to a runtime call");
        };
        assert!(matches!(
            func.as_ref(),
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(module, Some(member))),
                ..
            } if module.id.name() == "Primitive_exceptions" && member == "create"
        ));
        assert!(matches!(
            args.as_slice(),
            [Expression {
                desc: ExpressionDesc::Str { txt, .. },
                ..
            }] if txt == "Local_exception_test.A"
        ));
        assert_eq!(compiled.expr.comment.as_deref(), Some("@__PURE__"));
        assert_eq!(
            print_expression(&compiled.expr),
            "/* @__PURE__ */Primitive_exceptions.create(\"Local_exception_test.A\")"
        );
    }

    #[test]
    fn compile_wrap_exn_uses_primitive_exceptions_internal_to_exception() {
        let mut compiler = LambdaCompiler::new();
        let exn = Ident::create_local("exn");
        let compiled = compiler.compile_expr(&Lambda::prim(
            Primitive::PwrapExn,
            vec![Lambda::var(exn.clone())],
            Location::none(),
        ));

        assert!(compiled.prelude.is_empty());
        let ExpressionDesc::Call(func, args, _) = &compiled.expr.desc else {
            panic!("expected exception wrapping to lower to a runtime call");
        };
        assert!(matches!(
            func.as_ref(),
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(module, Some(member))),
                ..
            } if module.id.name() == "Primitive_exceptions" && member == "internalToException"
        ));
        assert!(matches!(
            args.as_slice(),
            [Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            }] if id.same(&exn)
        ));
    }

    #[test]
    fn compile_int_order_uses_primitive_int_compare() {
        let mut compiler = LambdaCompiler::new();
        let left = Ident::create_local("left");
        let right = Ident::create_local("right");
        let compiled = compiler.compile_expr(&Lambda::prim(
            Primitive::Pintorder,
            vec![Lambda::var(left), Lambda::var(right)],
            Location::none(),
        ));

        assert!(compiled.prelude.is_empty());
        assert_eq!(
            print_expression(&compiled.expr),
            "Primitive_int.compare(left, right)"
        );
    }

    #[test]
    fn compile_string_order_uses_primitive_string_compare() {
        let mut compiler = LambdaCompiler::new();
        let left = Ident::create_local("left");
        let right = Ident::create_local("right");
        let compiled = compiler.compile_expr(&Lambda::prim(
            Primitive::Pstringorder,
            vec![Lambda::var(left), Lambda::var(right)],
            Location::none(),
        ));

        assert!(compiled.prelude.is_empty());
        assert_eq!(
            print_expression(&compiled.expr),
            "Primitive_string.compare(left, right)"
        );
    }

    #[test]
    fn compile_arrayrefu_uses_direct_array_index() {
        let mut compiler = LambdaCompiler::new();
        let array = Ident::create_local("arr");
        let index = Ident::create_local("i");
        let compiled = compiler.compile_expr(&Lambda::prim(
            Primitive::Parrayrefu,
            vec![Lambda::var(array), Lambda::var(index)],
            Location::none(),
        ));

        assert!(compiled.prelude.is_empty());
        assert_eq!(print_expression(&compiled.expr), "arr[i]");
    }

    #[test]
    fn compile_arrayrefs_uses_primitive_array_get() {
        let mut compiler = LambdaCompiler::new();
        let array = Ident::create_local("arr");
        let index = Ident::create_local("i");
        let compiled = compiler.compile_expr(&Lambda::prim(
            Primitive::Parrayrefs,
            vec![Lambda::var(array), Lambda::var(index)],
            Location::none(),
        ));

        assert!(compiled.prelude.is_empty());
        assert_eq!(
            print_expression(&compiled.expr),
            "Primitive_array.get(arr, i)"
        );
    }

    #[test]
    fn compile_arraysetu_sequences_assignment_to_unit() {
        let mut compiler = LambdaCompiler::new();
        let array = Ident::create_local("arr");
        let index = Ident::create_local("i");
        let value = Ident::create_local("value");
        let compiled = compiler.compile_expr(&Lambda::prim(
            Primitive::Parraysetu,
            vec![
                Lambda::var(array.clone()),
                Lambda::var(index.clone()),
                Lambda::var(value.clone()),
            ],
            Location::none(),
        ));

        assert!(compiled.prelude.is_empty());
        let ExpressionDesc::Seq(assign, tail) = &compiled.expr.desc else {
            panic!("expected array set to lower to a seq");
        };
        let ExpressionDesc::Bin(BinOp::Eq, lhs, rhs) = &assign.desc else {
            panic!("expected array set seq head to be an assignment");
        };
        let ExpressionDesc::ArrayIndex(target, position) = &lhs.desc else {
            panic!("expected array set assignment lhs to be an array index");
        };
        assert!(matches!(
            target.as_ref(),
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&array)
        ));
        assert!(matches!(
            position.as_ref(),
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&index)
        ));
        assert!(matches!(
            rhs.as_ref(),
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&value)
        ));
        assert!(matches!(
            tail.as_ref(),
            Expression {
                desc: ExpressionDesc::Undefined { is_unit: false },
                ..
            }
        ));
    }

    #[test]
    fn compile_arraysets_uses_primitive_array_set() {
        let mut compiler = LambdaCompiler::new();
        let array = Ident::create_local("arr");
        let index = Ident::create_local("i");
        let value = Ident::create_local("value");
        let compiled = compiler.compile_expr(&Lambda::prim(
            Primitive::Parraysets,
            vec![Lambda::var(array), Lambda::var(index), Lambda::var(value)],
            Location::none(),
        ));

        assert!(compiled.prelude.is_empty());
        assert_eq!(
            print_expression(&compiled.expr),
            "Primitive_array.set(arr, i, value)"
        );
    }

    #[test]
    fn compile_string_refs_use_primitive_string_get_char() {
        let mut compiler = LambdaCompiler::new();
        let string = Ident::create_local("str");
        let index = Ident::create_local("i");
        let compiled = compiler.compile_expr(&Lambda::prim(
            Primitive::Pstringrefs,
            vec![Lambda::var(string), Lambda::var(index)],
            Location::none(),
        ));

        assert!(compiled.prelude.is_empty());
        assert_eq!(
            print_expression(&compiled.expr),
            "Primitive_string.getChar(str, i)"
        );
    }

    #[test]
    fn compile_obj_compare_against_null_uses_strict_equality() {
        let mut compiler = LambdaCompiler::new();
        let value = Ident::create_local("value");
        let compiled = compiler.compile_expr(&Lambda::prim(
            Primitive::Pobjcomp(Comparison::Eq),
            vec![Lambda::const_(Constant::JsNull), Lambda::var(value)],
            Location::none(),
        ));

        assert!(compiled.prelude.is_empty());
        assert_eq!(print_expression(&compiled.expr), "null === value");
    }

    #[test]
    fn compile_obj_compare_null_against_number_literal_folds_false() {
        let mut compiler = LambdaCompiler::new();
        let compiled = compiler.compile_expr(&Lambda::prim(
            Primitive::Pobjcomp(Comparison::Eq),
            vec![
                Lambda::const_(Constant::JsNull),
                Lambda::const_(Constant::int(5)),
            ],
            Location::none(),
        ));

        assert!(compiled.prelude.is_empty());
        assert_eq!(print_expression(&compiled.expr), "false");
    }

    #[test]
    fn compile_obj_notequal_undefined_against_number_literal_folds_true() {
        let mut compiler = LambdaCompiler::new();
        let compiled = compiler.compile_expr(&Lambda::prim(
            Primitive::Pobjcomp(Comparison::Neq),
            vec![
                Lambda::const_(Constant::JsUndefined { is_unit: false }),
                Lambda::const_(Constant::int(5)),
            ],
            Location::none(),
        ));

        assert!(compiled.prelude.is_empty());
        assert_eq!(print_expression(&compiled.expr), "true");
    }

    #[test]
    fn compile_obj_order_uses_primitive_object_compare() {
        let mut compiler = LambdaCompiler::new();
        let left = Ident::create_local("left");
        let right = Ident::create_local("right");
        let compiled = compiler.compile_expr(&Lambda::prim(
            Primitive::Pobjorder,
            vec![Lambda::var(left), Lambda::var(right)],
            Location::none(),
        ));

        assert!(compiled.prelude.is_empty());
        assert_eq!(
            print_expression(&compiled.expr),
            "Primitive_object.compare(left, right)"
        );
    }

    #[test]
    fn compile_eta_wrapped_object_compare_function_aliases_runtime_member() {
        let mut compiler = LambdaCompiler::new();
        let left = Ident::create_local("left");
        let right = Ident::create_local("right");
        let compiled = compiler.compile_expr(&Lambda::function_(
            2,
            vec![left.clone(), right.clone()],
            Lambda::prim(
                Primitive::Pobjorder,
                vec![Lambda::var(left), Lambda::var(right)],
                Location::none(),
            ),
            Default::default(),
        ));

        assert!(compiled.prelude.is_empty());
        assert_eq!(print_expression(&compiled.expr), "Primitive_object.compare");
    }

    #[test]
    fn compile_eta_wrapped_float_compare_function_aliases_runtime_member() {
        let mut compiler = LambdaCompiler::new();
        let left = Ident::create_local("x");
        let right = Ident::create_local("y");
        let compiled = compiler.compile_expr(&Lambda::function_(
            2,
            vec![left.clone(), right.clone()],
            Lambda::prim(
                Primitive::Pfloatorder,
                vec![Lambda::var(left), Lambda::var(right)],
                Location::none(),
            ),
            Default::default(),
        ));

        assert!(compiled.prelude.is_empty());
        assert_eq!(print_expression(&compiled.expr), "Primitive_float.compare");
    }

    #[test]
    fn compile_expr_keeps_forwarded_module_call_params_like_ocaml() {
        let mut compiler = LambdaCompiler::new();
        let none = Ident::create_local("none");
        let icmp = Ident::create_persistent("Icmp");
        let belt_map = Ident::create_persistent("Belt_Map");

        let compiled = compiler.compile_expr(&Lambda::function_(
            1,
            vec![none.clone()],
            Lambda::Lapply(Apply {
                ap_func: Box::new(Lambda::prim(
                    Primitive::Pfield(
                        23,
                        FieldDbgInfo::Module {
                            name: "fromArray".to_string(),
                        },
                    ),
                    vec![Lambda::LglobalModule(belt_map, false)],
                    Location::none(),
                )),
                ap_args: vec![Lambda::var(none.clone()), Lambda::var(icmp.clone())],
                ap_info: ApInfo {
                    loc: Location::none(),
                    inlined: InlineAttribute::Default,
                    status: ApplyStatus::Uncurry,
                },
                ap_transformed_jsx: false,
            }),
            Default::default(),
        ));

        let rendered = print_expression(&compiled.expr);
        assert!(
            compiled.prelude.is_empty(),
            "expected the forwarding wrapper to compile as a pure expression, got prelude:\n{}",
            print_block(&compiled.prelude)
        );
        assert!(
            rendered.contains("fromArray(none, Icmp)"),
            "expected forwarded wrapper parameter to survive in the lowered call, got:\n{rendered}"
        );
        assert!(
            !rendered.contains("fromArray(undefined, Icmp)"),
            "unexpected forwarded parameter loss in lowered call:\n{rendered}"
        );
    }

    #[test]
    fn compile_expr_keeps_forwarded_nested_wrapper_params_like_ocaml() {
        let mut compiler = LambdaCompiler::new();
        let a = Ident::create_local("a");
        let b = Ident::create_local("b");
        let extra = Ident::create_local("extra");
        let belt_map = Ident::create_persistent("Belt_Map");

        let compiled = compiler.compile_expr(&Lambda::function_(
            2,
            vec![a.clone(), b.clone()],
            Lambda::function_(
                1,
                vec![extra.clone()],
                Lambda::Lapply(Apply {
                    ap_func: Box::new(Lambda::prim(
                        Primitive::Pfield(
                            9,
                            FieldDbgInfo::Module {
                                name: "eq".to_string(),
                            },
                        ),
                        vec![Lambda::LglobalModule(belt_map, false)],
                        Location::none(),
                    )),
                    ap_args: vec![
                        Lambda::var(a.clone()),
                        Lambda::var(b.clone()),
                        Lambda::var(extra.clone()),
                    ],
                    ap_info: ApInfo {
                        loc: Location::none(),
                        inlined: InlineAttribute::Default,
                        status: ApplyStatus::Uncurry,
                    },
                    ap_transformed_jsx: false,
                }),
                Default::default(),
            ),
            Default::default(),
        ));

        let rendered = print_expression(&compiled.expr);
        assert!(
            compiled.prelude.is_empty(),
            "expected the nested forwarding wrapper to compile as a pure expression, got prelude:\n{}",
            print_block(&compiled.prelude)
        );
        assert!(
            rendered.contains("eq(a, b, extra)"),
            "expected nested wrapper parameter to survive in the lowered call, got:\n{rendered}"
        );
        assert!(
            !rendered.contains("eq(a, b, undefined)"),
            "unexpected nested wrapper parameter loss in lowered call:\n{rendered}"
        );
    }

    #[test]
    fn compile_effectful_underscore_binding_from_nested_js_function_calls_survives_shake() {
        let mut compiler = LambdaCompiler::new();
        let outer_fn_param = Ident::create_local("x");
        let inner_true_param = Ident::create_local("f");
        let inner_zero_param = Ident::create_local("f");
        let unused = Ident::create_local("_s");
        let always_true = Ident::create_local("h");
        let also_true = Ident::create_local("j");
        let loc = Location::none();
        let starj_empty = Lambda::const_(Constant::String {
            s: "".to_string(),
            delim: Some(StringDelim::StarJ),
        });

        let outer_value = Lambda::let_(
            LetKind::Strict,
            always_true,
            Lambda::true_(),
            Lambda::prim(
                Primitive::PjsFnMake(1),
                vec![Lambda::function_(
                    1,
                    vec![outer_fn_param.clone()],
                    Lambda::let_(
                        LetKind::Strict,
                        also_true,
                        Lambda::prim(
                            Primitive::PjsFnMake(1),
                            vec![Lambda::function_(
                                1,
                                vec![inner_true_param],
                                Lambda::true_(),
                                FunctionAttribute::default(),
                            )],
                            loc.clone(),
                        ),
                        Lambda::prim(
                            Primitive::PjsFnMake(1),
                            vec![Lambda::function_(
                                1,
                                vec![inner_zero_param],
                                Lambda::const_(Constant::int(0)),
                                FunctionAttribute::default(),
                            )],
                            loc.clone(),
                        ),
                    ),
                    FunctionAttribute::default(),
                )],
                loc.clone(),
            ),
        );
        let nested_call = Lambda::Lapply(Apply {
            ap_func: Box::new(Lambda::Lapply(Apply {
                ap_func: Box::new(outer_value),
                ap_args: vec![starj_empty.clone()],
                ap_info: ApInfo {
                    loc: loc.clone(),
                    inlined: InlineAttribute::Default,
                    status: ApplyStatus::Uncurry,
                },
                ap_transformed_jsx: false,
            })),
            ap_args: vec![starj_empty],
            ap_info: ApInfo {
                loc: loc.clone(),
                inlined: InlineAttribute::Default,
                status: ApplyStatus::Uncurry,
            },
            ap_transformed_jsx: false,
        });
        let program = compiler.compile_program(&Lambda::let_(
            LetKind::Strict,
            unused,
            nested_call,
            Lambda::unit(),
        ));

        let rendered = print_block(&program.block);
        assert!(
            rendered.contains("(f => 0)(\"\")"),
            "expected the top-level call to survive, got:\n{rendered}"
        );
    }

    #[test]
    fn compile_hash_primitives_lower_to_primitive_hash_runtime_calls_like_ocaml() {
        let mut compiler = LambdaCompiler::new();
        let x = Ident::create_local("x");
        let seed = Ident::create_local("seed");
        let value = Ident::create_local("value");

        let hash = compiler.compile_expr(&Lambda::prim(
            Primitive::Phash,
            vec![
                Lambda::const_(Constant::int(10)),
                Lambda::const_(Constant::int(100)),
                Lambda::const_(Constant::int(0)),
                Lambda::var(x.clone()),
            ],
            Location::none(),
        ));
        assert!(hash.prelude.is_empty());
        assert_eq!(
            print_expression(&hash.expr),
            "Primitive_hash.hash(10, 100, 0, x)"
        );

        let hash_mix_int = compiler.compile_expr(&Lambda::prim(
            Primitive::PhashMixint,
            vec![Lambda::var(seed.clone()), Lambda::var(value.clone())],
            Location::none(),
        ));
        assert!(hash_mix_int.prelude.is_empty());
        assert_eq!(
            print_expression(&hash_mix_int.expr),
            "Primitive_hash.hash_mix_int(seed, value)"
        );

        let hash_mix_string = compiler.compile_expr(&Lambda::prim(
            Primitive::PhashMixstring,
            vec![Lambda::var(seed.clone()), Lambda::var(value.clone())],
            Location::none(),
        ));
        assert!(hash_mix_string.prelude.is_empty());
        assert_eq!(
            print_expression(&hash_mix_string.expr),
            "Primitive_hash.hash_mix_string(seed, value)"
        );

        let hash_final_mix = compiler.compile_expr(&Lambda::prim(
            Primitive::PhashFinalmix,
            vec![Lambda::var(seed)],
            Location::none(),
        ));
        assert!(hash_final_mix.prelude.is_empty());
        assert_eq!(
            print_expression(&hash_final_mix.expr),
            "Primitive_hash.hash_final_mix(seed)"
        );
    }

    #[test]
    fn compile_eta_wrapped_hash_function_aliases_runtime_member() {
        let mut compiler = LambdaCompiler::new();
        let hash_limit = Ident::create_local("hash_limit");
        let hash_count = Ident::create_local("hash_count");
        let hash_acc = Ident::create_local("hash_acc");
        let value = Ident::create_local("value");
        let compiled = compiler.compile_expr(&Lambda::function_(
            4,
            vec![
                hash_limit.clone(),
                hash_count.clone(),
                hash_acc.clone(),
                value.clone(),
            ],
            Lambda::prim(
                Primitive::Phash,
                vec![
                    Lambda::var(hash_limit),
                    Lambda::var(hash_count),
                    Lambda::var(hash_acc),
                    Lambda::var(value),
                ],
                Location::none(),
            ),
            Default::default(),
        ));

        assert!(compiled.prelude.is_empty());
        assert_eq!(print_expression(&compiled.expr), "Primitive_hash.hash");
    }

    #[test]
    fn compile_compare_against_zero_elides_runtime_compare_call_like_ocaml() {
        let mut compiler = LambdaCompiler::new();
        let left = Ident::create_local("x");
        let right = Ident::create_local("y");
        let compiled = compiler.compile_expr(&Lambda::prim(
            Primitive::Pintcomp(Comparison::Gt),
            vec![
                Lambda::prim(
                    Primitive::Pfloatorder,
                    vec![Lambda::var(left.clone()), Lambda::var(right.clone())],
                    Location::none(),
                ),
                Lambda::const_(Constant::int(0)),
            ],
            Location::none(),
        ));

        assert!(compiled.prelude.is_empty());
        assert_eq!(print_expression(&compiled.expr), "x > y");
    }

    #[test]
    fn compile_bigint_compare_against_zero_elides_runtime_compare_call_like_ocaml() {
        let mut compiler = LambdaCompiler::new();
        let compiled = compiler.compile_expr(&Lambda::prim(
            Primitive::Pintcomp(Comparison::Lt),
            vec![
                Lambda::prim(
                    Primitive::Pfloatorder,
                    vec![
                        Lambda::const_(Constant::BigInt {
                            negative: false,
                            value: "123".to_string(),
                        }),
                        Lambda::const_(Constant::BigInt {
                            negative: false,
                            value: "555555".to_string(),
                        }),
                    ],
                    Location::none(),
                ),
                Lambda::const_(Constant::int(0)),
            ],
            Location::none(),
        ));

        assert!(compiled.prelude.is_empty());
        assert_eq!(print_expression(&compiled.expr), "123n < 555555n");
    }

    #[test]
    fn compile_eta_wrapped_float_equality_stays_as_function() {
        let mut compiler = LambdaCompiler::new();
        let left = Ident::create_local("x");
        let right = Ident::create_local("y");
        let compiled = compiler.compile_expr(&Lambda::function_(
            2,
            vec![left.clone(), right.clone()],
            Lambda::prim(
                Primitive::Pfloatcomp(Comparison::Eq),
                vec![Lambda::var(left), Lambda::var(right)],
                Location::none(),
            ),
            Default::default(),
        ));

        assert!(compiled.prelude.is_empty());
        assert!(matches!(compiled.expr.desc, ExpressionDesc::Fun { .. }));
    }

    #[test]
    fn compile_bigint_min_literals_use_conditional_fast_path() {
        let mut compiler = LambdaCompiler::new();
        let compiled = compiler.compile_expr(&Lambda::prim(
            Primitive::Pbigintmin,
            vec![
                Lambda::const_(Constant::BigInt {
                    negative: false,
                    value: "9".to_string(),
                }),
                Lambda::const_(Constant::BigInt {
                    negative: false,
                    value: "1".to_string(),
                }),
            ],
            Location::none(),
        ));

        assert!(compiled.prelude.is_empty());
        assert_eq!(print_expression(&compiled.expr), "9n < 1n ? 9n : 1n");
    }

    #[test]
    fn compile_bigint_arithmetic_primitives_use_raw_js_bigint_ops_like_ocaml() {
        let mut compiler = LambdaCompiler::new();
        let lhs = Lambda::const_(Constant::BigInt {
            negative: false,
            value: "9".to_string(),
        });
        let rhs = Lambda::const_(Constant::BigInt {
            negative: false,
            value: "1".to_string(),
        });

        let add = compiler.compile_expr(&Lambda::prim(
            Primitive::Paddbigint,
            vec![lhs.clone(), rhs.clone()],
            Location::none(),
        ));
        assert!(add.prelude.is_empty());
        assert_eq!(print_expression(&add.expr), "9n + 1n");

        let pow = compiler.compile_expr(&Lambda::prim(
            Primitive::Ppowbigint,
            vec![lhs.clone(), rhs.clone()],
            Location::none(),
        ));
        assert!(pow.prelude.is_empty());
        assert_eq!(print_expression(&pow.expr), "9n ** 1n");

        let neg = compiler.compile_expr(&Lambda::prim(
            Primitive::Pnegbigint,
            vec![lhs],
            Location::none(),
        ));
        assert!(neg.prelude.is_empty());
        assert_eq!(print_expression(&neg.expr), "0n - 9n");
    }

    #[test]
    fn compile_bigint_bitwise_primitives_use_raw_js_bigint_ops_like_ocaml() {
        let mut compiler = LambdaCompiler::new();
        let lhs = Lambda::const_(Constant::BigInt {
            negative: false,
            value: "9".to_string(),
        });
        let rhs = Lambda::const_(Constant::BigInt {
            negative: false,
            value: "1".to_string(),
        });

        let land = compiler.compile_expr(&Lambda::prim(
            Primitive::Pandbigint,
            vec![lhs.clone(), rhs.clone()],
            Location::none(),
        ));
        assert!(land.prelude.is_empty());
        assert_eq!(print_expression(&land.expr), "9n & 1n");

        let lsl = compiler.compile_expr(&Lambda::prim(
            Primitive::Plslbigint,
            vec![lhs.clone(), rhs.clone()],
            Location::none(),
        ));
        assert!(lsl.prelude.is_empty());
        assert_eq!(print_expression(&lsl.expr), "(9n << 1n)");

        let lnot = compiler.compile_expr(&Lambda::prim(
            Primitive::Pnotbigint,
            vec![lhs],
            Location::none(),
        ));
        assert!(lnot.prelude.is_empty());
        assert_eq!(print_expression(&lnot.expr), "~9n");
    }

    #[test]
    fn compile_duprecord_lowers_to_object_spread_like_ocaml() {
        let mut compiler = LambdaCompiler::new();
        let source = Ident::create_local("source");
        let compiled = compiler.compile_expr(&Lambda::prim(
            Primitive::Pduprecord,
            vec![Lambda::var(source)],
            Location::none(),
        ));

        assert!(compiled.prelude.is_empty());
        assert_eq!(print_expression(&compiled.expr), "{...source}");
    }

    #[test]
    fn compile_deps_program_reuses_same_name_export_targets() {
        let mut compiler = LambdaCompiler::new();
        let source = Ident::create_local("value");
        let rebound_export = Ident::create_local("value");
        let param = Ident::create_local("arg");
        let lam = Lambda::let_(
            LetKind::Strict,
            source.clone(),
            Lambda::function_(
                1,
                vec![param.clone()],
                Lambda::var(param),
                crate::lambda::FunctionAttribute::default(),
            ),
            Lambda::let_(
                LetKind::Alias,
                rebound_export.clone(),
                Lambda::var(source.clone()),
                Lambda::prim(
                    Primitive::Pmakeblock(
                        0,
                        TagInfo::ModuleExport(vec![rebound_export]),
                        Mutable::Immutable,
                    ),
                    vec![Lambda::var(source.clone())],
                    Location::none(),
                ),
            ),
        );

        let deps = compiler.compile_deps_program(&lam);

        let [exported] = deps.program.exports.as_slice() else {
            panic!("expected a single export");
        };
        assert!(
            exported.same(&source),
            "expected export {:?}, got {:?}",
            source,
            exported
        );

        let [stmt] = deps.program.block.as_slice() else {
            panic!("expected the rebound export alias to be shaken away");
        };
        match &stmt.desc {
            StatementDesc::Variable(VariableDeclaration { ident, .. }) => {
                assert!(ident.same(&source))
            }
            other => panic!("expected only the original exported binding to remain, got {other:?}"),
        }
    }

    #[test]
    fn coerce_toplevel_exports_reuses_existing_undefined_binding() {
        let mut compiler = LambdaCompiler::new();
        let alias = Ident::create_local("VS");
        let other = Ident::create_local("y");
        let mut block = vec![
            Statement::variable(VariableDeclaration {
                ident: alias.clone(),
                value: Some(Expression::undefined(false)),
                property: LetKind::Strict,
                ident_info: IdentInfo::default(),
            }),
            Statement::variable(VariableDeclaration {
                ident: other.clone(),
                value: Some(Expression::number(Number::int(13))),
                property: LetKind::Strict,
                ident_info: IdentInfo::default(),
            }),
        ];

        let exports = compiler.coerce_toplevel_exports(
            &mut block,
            ExtractedExports {
                exports: vec![alias.clone(), other.clone()],
                values: vec![Expression::undefined(false), Expression::var(other.clone())],
            },
        );

        assert_eq!(exports, vec![alias.clone(), other.clone()]);
        let [first, second] = block.as_slice() else {
            panic!("expected the existing bindings to be reused without rebound placeholders");
        };
        match &first.desc {
            StatementDesc::Variable(VariableDeclaration { ident, .. }) => {
                assert!(ident.same(&alias))
            }
            other => panic!("expected the original alias binding first, got {other:?}"),
        }
        match &second.desc {
            StatementDesc::Variable(VariableDeclaration { ident, .. }) => {
                assert!(ident.same(&other))
            }
            other => panic!("expected the later binding second, got {other:?}"),
        }
    }

    #[test]
    fn coerce_toplevel_exports_keeps_undefined_rebound_after_later_effects() {
        let mut compiler = LambdaCompiler::new();
        let alias = Ident::create_local("MyURL");
        let callback = Ident::create_persistent("callback");
        let mut block = vec![
            Statement::variable(VariableDeclaration {
                ident: alias.clone(),
                value: Some(Expression::undefined(false)),
                property: LetKind::Strict,
                ident_info: IdentInfo::default(),
            }),
            Statement::exp(Expression::call(
                Expression::var(callback),
                vec![],
                CallInfo::default(),
            )),
        ];

        let exports = compiler.coerce_toplevel_exports(
            &mut block,
            ExtractedExports {
                exports: vec![alias.clone()],
                values: vec![Expression::undefined(false)],
            },
        );

        let [decl, effect, rebound] = block.as_slice() else {
            panic!("expected the later effect to force a trailing rebound placeholder");
        };
        match &decl.desc {
            StatementDesc::Variable(VariableDeclaration { ident, .. }) => {
                assert!(ident.same(&alias))
            }
            other => panic!("expected the original alias binding first, got {other:?}"),
        }
        assert!(matches!(effect.desc, StatementDesc::Exp(_)));
        match &rebound.desc {
            StatementDesc::Variable(VariableDeclaration { ident, .. }) => {
                assert!(
                    !ident.same(&alias),
                    "expected a rebound export placeholder at the tail"
                );
                assert_eq!(ident.name(), alias.name());
                assert_eq!(exports, vec![ident.clone()]);
            }
            other => panic!("expected the trailing rebound export placeholder, got {other:?}"),
        }
    }

    #[test]
    fn coerce_toplevel_exports_skips_unreachable_undefined_placeholder_after_throw() {
        let mut compiler = LambdaCompiler::new();
        let exported = Ident::create_local("u");
        let mut block = vec![Statement::throw(Expression::string("boom".to_string()))];

        let exports = compiler.coerce_toplevel_exports(
            &mut block,
            ExtractedExports {
                exports: vec![exported.clone()],
                values: vec![Expression::undefined(false)],
            },
        );

        assert_eq!(exports, vec![exported.clone()]);
        let [stmt] = block.as_slice() else {
            panic!("expected the terminating effect to stay alone in the block");
        };
        assert!(matches!(
            stmt.desc,
            StatementDesc::Throw(Expression {
                desc: ExpressionDesc::Str { .. },
                ..
            })
        ));
    }

    #[test]
    fn compile_deps_program_preserves_toplevel_binding_order_during_shake() {
        let mut compiler = LambdaCompiler::new();
        let first = Ident::create_local("first");
        let second = Ident::create_local("second");
        let lam = Lambda::let_(
            LetKind::Strict,
            first.clone(),
            Lambda::const_(Constant::int(3)),
            Lambda::let_(
                LetKind::Strict,
                second.clone(),
                Lambda::const_(Constant::int(4)),
                Lambda::prim(
                    Primitive::Pmakeblock(
                        0,
                        TagInfo::ModuleExport(vec![first.clone(), second.clone()]),
                        Mutable::Immutable,
                    ),
                    vec![Lambda::var(first.clone()), Lambda::var(second.clone())],
                    Location::none(),
                ),
            ),
        );

        let deps = compiler.compile_deps_program(&lam);

        let [first_export, second_export] = deps.program.exports.as_slice() else {
            panic!("expected two exports");
        };
        assert!(first_export.same(&first));
        assert!(second_export.same(&second));

        let [first_stmt, second_stmt] = deps.program.block.as_slice() else {
            panic!("expected the retained bindings to stay in the OCaml shake order");
        };

        match &first_stmt.desc {
            StatementDesc::Variable(VariableDeclaration {
                ident,
                value:
                    Some(Expression {
                        desc: ExpressionDesc::Number(Number::Int { i: 3, .. }),
                        ..
                    }),
                ..
            }) => assert!(ident.same(&first)),
            other => panic!("expected the earlier retained binding first, got {other:?}"),
        }

        match &second_stmt.desc {
            StatementDesc::Variable(VariableDeclaration {
                ident,
                value:
                    Some(Expression {
                        desc: ExpressionDesc::Number(Number::Int { i: 4, .. }),
                        ..
                    }),
                ..
            }) => assert!(ident.same(&second)),
            other => panic!("expected the later retained binding second, got {other:?}"),
        }
    }

    #[test]
    fn compile_deps_program_keeps_exported_call_result_before_rebound_constant_block_export() {
        let mut compiler = LambdaCompiler::new();
        let f = Ident::create_local("f");
        let v = Ident::create_local("v");
        let res = Ident::create_local("res");
        let param = Ident::create_local("v");
        let export_block = Lambda::prim(
            Primitive::Pmakeblock(
                0,
                TagInfo::ModuleExport(vec![v.clone(), res.clone()]),
                Mutable::Immutable,
            ),
            vec![Lambda::var(v.clone()), Lambda::var(res.clone())],
            Location::none(),
        );
        let lam = Lambda::let_(
            LetKind::Strict,
            f.clone(),
            Lambda::prim(
                Primitive::PjsFnMake(1),
                vec![Lambda::function_(
                    1,
                    vec![param.clone()],
                    Lambda::prim(
                        Primitive::Pfield(
                            0,
                            crate::lambda::compat::FieldDbgInfo::Record {
                                name: "x".to_string(),
                                mutable_flag: crate::parser::ast::MutableFlag::Immutable,
                            },
                        ),
                        vec![Lambda::var(param)],
                        Location::none(),
                    ),
                    FunctionAttribute::default(),
                )],
                Location::none(),
            ),
            Lambda::let_(
                LetKind::Strict,
                v.clone(),
                Lambda::const_(Constant::Block {
                    tag: 0,
                    tag_info: TagInfo::record(
                        vec![
                            ("x".to_string(), false),
                            ("y".to_string(), false),
                            ("z".to_string(), false),
                        ],
                        crate::parser::ast::MutableFlag::Immutable,
                    ),
                    elements: vec![
                        Constant::int(3),
                        Constant::int(4),
                        Constant::JsUndefined { is_unit: false },
                    ],
                }),
                Lambda::let_(
                    LetKind::Strict,
                    res.clone(),
                    Lambda::Lapply(Apply {
                        ap_func: Box::new(Lambda::var(f)),
                        ap_args: vec![Lambda::var(v.clone())],
                        ap_info: ApInfo {
                            loc: Location::none(),
                            inlined: InlineAttribute::Default,
                            status: ApplyStatus::Uncurry,
                        },
                        ap_transformed_jsx: false,
                    }),
                    export_block,
                ),
            ),
        );

        let deps = compiler.compile_deps_program(&lam);
        let rendered = print_deps_program(&deps, None);
        let res_idx = rendered
            .find("let res = 3;")
            .expect("expected the reduced exported call result binding");
        let v_idx = rendered
            .find("let v = {\n  x: 3,")
            .expect("expected the rebound constant-block export binding");
        assert!(
            res_idx < v_idx,
            "expected the preserved exported call result before the rebound block export:\n{rendered}"
        );
    }

    #[test]
    fn compile_deps_program_rebinds_different_name_exports_after_effects() {
        let mut compiler = LambdaCompiler::new();
        let original_export = Ident::create_local("MyURL");
        let export_block = Lambda::prim(
            Primitive::Pmakeblock(
                0,
                TagInfo::ModuleExport(vec![original_export.clone()]),
                Mutable::Immutable,
            ),
            vec![Lambda::unit()],
            Location::none(),
        );
        let lam = Lambda::let_(
            LetKind::Alias,
            original_export.clone(),
            Lambda::unit(),
            Lambda::seq(
                Lambda::prim(Primitive::Pdebugger, vec![], Location::none()),
                export_block,
            ),
        );

        let deps = compiler.compile_deps_program(&lam);

        let [exported] = deps.program.exports.as_slice() else {
            panic!("expected a single export");
        };
        assert_eq!(exported.name(), "MyURL");
        assert!(
            !exported.same(&original_export),
            "expected export coercion to rename the trailing export binding"
        );

        let [debugger, rebound] = deps.program.block.as_slice() else {
            panic!(
                "expected the original placeholder to shake away and the rebound export to remain"
            );
        };
        assert!(matches!(debugger.desc, StatementDesc::Debugger));
        match &rebound.desc {
            StatementDesc::Variable(VariableDeclaration {
                ident,
                value:
                    Some(Expression {
                        desc: ExpressionDesc::Undefined { is_unit: true },
                        ..
                    }),
                ..
            }) => assert!(ident.same(exported)),
            other => panic!("expected trailing undefined export placeholder, got {other:?}"),
        }
    }

    #[test]
    fn compile_deps_program_rebinds_exported_constants_after_surviving_function_bindings() {
        let mut compiler = LambdaCompiler::new();
        let x = Ident::create_local("x");
        let xx = Ident::create_local("xx");
        let foo = Ident::create_local("foo");
        let param = Ident::create_local("x");
        let export_block = Lambda::prim(
            Primitive::Pmakeblock(
                0,
                TagInfo::ModuleExport(vec![x.clone(), xx.clone(), foo.clone()]),
                Mutable::Immutable,
            ),
            vec![
                Lambda::var(x.clone()),
                Lambda::var(xx.clone()),
                Lambda::var(foo.clone()),
            ],
            Location::none(),
        );
        let lam = Lambda::let_(
            LetKind::Strict,
            x.clone(),
            Lambda::const_(Constant::int(1)),
            Lambda::let_(
                LetKind::Strict,
                xx.clone(),
                Lambda::var(x),
                Lambda::let_(
                    LetKind::Strict,
                    foo.clone(),
                    Lambda::prim(
                        Primitive::PjsFnMake(1),
                        vec![Lambda::function_(
                            1,
                            vec![param.clone()],
                            Lambda::var(param),
                            FunctionAttribute::default(),
                        )],
                        Location::none(),
                    ),
                    export_block,
                ),
            ),
        );

        let deps = compiler.compile_deps_program(&lam);

        assert_eq!(
            deps.program
                .exports
                .iter()
                .map(|ident| ident.name())
                .collect::<Vec<_>>(),
            vec!["x", "xx", "foo"]
        );

        let [first, second, third] = deps.program.block.as_slice() else {
            panic!("expected function binding followed by two rebound constant exports");
        };
        match &first.desc {
            StatementDesc::Variable(VariableDeclaration {
                ident,
                value:
                    Some(Expression {
                        desc: ExpressionDesc::Fun { .. },
                        ..
                    }),
                ..
            }) => assert!(ident.same(&foo)),
            other => panic!("expected the surviving function binding first, got {other:?}"),
        }
        match &second.desc {
            StatementDesc::Variable(VariableDeclaration { ident, .. }) => {
                assert_eq!(ident.name(), "x");
            }
            other => panic!("expected the rebound x export second, got {other:?}"),
        }
        match &third.desc {
            StatementDesc::Variable(VariableDeclaration { ident, .. }) => {
                assert_eq!(ident.name(), "xx");
            }
            other => panic!("expected the rebound xx export third, got {other:?}"),
        }

        let rendered = print_deps_program(&deps, None);
        let foo_idx = rendered.find("function foo").unwrap();
        let x_idx = rendered.find("let x = 1;").unwrap();
        let xx_idx = rendered.find("let xx = 1;").unwrap();
        assert!(foo_idx < x_idx);
        assert!(x_idx < xx_idx);
    }

    #[test]
    fn compile_deps_program_rebinds_marshaled_string_exports_after_surviving_function_bindings() {
        let mut compiler = LambdaCompiler::new();
        let foo = Ident::create_local("foo");
        let s = Ident::create_local("s");
        let bar = Ident::create_local("bar");
        let foo_param = Ident::create_local("x");
        let bar_param = Ident::create_local("x");
        let export_block = Lambda::prim(
            Primitive::Pmakeblock(
                0,
                TagInfo::ModuleExport(vec![foo.clone(), s.clone(), bar.clone()]),
                Mutable::Immutable,
            ),
            vec![
                Lambda::var(foo.clone()),
                Lambda::var(s.clone()),
                Lambda::var(bar.clone()),
            ],
            Location::none(),
        );
        let lam = Lambda::let_(
            LetKind::Strict,
            foo.clone(),
            Lambda::prim(
                Primitive::PjsFnMake(1),
                vec![Lambda::function_(
                    1,
                    vec![foo_param.clone()],
                    Lambda::var(foo_param),
                    FunctionAttribute::default(),
                )],
                Location::none(),
            ),
            Lambda::let_(
                LetKind::Strict,
                s.clone(),
                Lambda::const_(Constant::String {
                    s: "😀".to_string(),
                    delim: Some(StringDelim::StarJ),
                }),
                Lambda::let_(
                    LetKind::Strict,
                    bar.clone(),
                    Lambda::prim(
                        Primitive::PjsFnMake(1),
                        vec![Lambda::function_(
                            1,
                            vec![bar_param.clone()],
                            Lambda::var(bar_param),
                            FunctionAttribute::default(),
                        )],
                        Location::none(),
                    ),
                    export_block,
                ),
            ),
        );

        let deps = compiler.compile_deps_program(&lam);

        assert_eq!(
            deps.program
                .exports
                .iter()
                .map(|ident| ident.name())
                .collect::<Vec<_>>(),
            vec!["foo", "s", "bar"]
        );

        let rendered = print_deps_program(&deps, None);
        let foo_idx = rendered.find("function foo").unwrap();
        let bar_idx = rendered.find("function bar").unwrap();
        let s_idx = rendered.find("let s = \"😀\";").unwrap();
        assert!(foo_idx < bar_idx);
        assert!(bar_idx < s_idx);
    }

    #[test]
    fn compile_deps_program_keeps_same_name_export_aliases_for_unbound_globals() {
        let mut compiler = LambdaCompiler::new();
        let global = Ident::create_persistent("parseInt");
        let rebound_export = Ident::create_local("parseInt");
        let lam = Lambda::let_(
            LetKind::Alias,
            rebound_export.clone(),
            Lambda::var(global.clone()),
            Lambda::prim(
                Primitive::Pmakeblock(
                    0,
                    TagInfo::ModuleExport(vec![rebound_export.clone()]),
                    Mutable::Immutable,
                ),
                vec![Lambda::var(rebound_export.clone())],
                Location::none(),
            ),
        );

        let deps = compiler.compile_deps_program(&lam);

        let [exported] = deps.program.exports.as_slice() else {
            panic!("expected a single export");
        };
        assert_eq!(exported.name(), rebound_export.name());

        let [stmt] = deps.program.block.as_slice() else {
            panic!("expected the rebound alias to stay as a real binding");
        };
        match &stmt.desc {
            StatementDesc::Variable(VariableDeclaration {
                ident,
                value:
                    Some(Expression {
                        desc: ExpressionDesc::Var(VIdent::Id(target)),
                        ..
                    }),
                ..
            }) => {
                assert_eq!(ident.name(), rebound_export.name());
                assert!(target.same(&global));
            }
            other => panic!("expected the rebound export binding to remain, got {other:?}"),
        }
    }

    #[test]
    fn coerce_and_resolve_keep_declared_same_name_export_aliases() {
        let mut compiler = LambdaCompiler::new();
        let target = Ident::create_local("broken");
        let exported = Ident::create_local("broken");
        let mut block = vec![
            Statement::variable(VariableDeclaration {
                ident: target.clone(),
                value: Some(Expression::number(Number::int(1))),
                property: LetKind::Strict,
                ident_info: IdentInfo::default(),
            }),
            Statement::variable(VariableDeclaration {
                ident: exported.clone(),
                value: Some(Expression::var(target.clone())),
                property: LetKind::Alias,
                ident_info: IdentInfo::default(),
            }),
        ];

        let exports = compiler.coerce_toplevel_exports(
            &mut block,
            ExtractedExports {
                exports: vec![exported.clone()],
                values: vec![Expression::var(target.clone())],
            },
        );
        let exports = resolve_export_aliases(&block, exports);

        assert_eq!(exports, vec![exported.clone()]);

        let [first, second] = block.as_slice() else {
            panic!("expected the original target and alias bindings to remain");
        };
        match &first.desc {
            StatementDesc::Variable(VariableDeclaration { ident, .. }) => {
                assert!(ident.same(&target));
            }
            other => panic!("expected the original target binding first, got {other:?}"),
        }
        match &second.desc {
            StatementDesc::Variable(VariableDeclaration { ident, .. }) => {
                assert!(ident.same(&exported));
            }
            other => panic!("expected the exported alias binding second, got {other:?}"),
        }
    }

    #[test]
    fn compile_deps_program_keeps_exports_after_trailing_effect_sequence() {
        let mut compiler = LambdaCompiler::new();
        let exported = Ident::create_local("foo");
        let export_block = Lambda::prim(
            Primitive::Pmakeblock(
                0,
                TagInfo::ModuleExport(vec![exported.clone()]),
                Mutable::Immutable,
            ),
            vec![Lambda::var(exported.clone())],
            Location::none(),
        );
        let lam = Lambda::let_(
            LetKind::Strict,
            exported.clone(),
            Lambda::const_(Constant::int(1)),
            Lambda::seq(
                Lambda::assign(exported.clone(), Lambda::const_(Constant::int(2))),
                export_block,
            ),
        );

        let deps = compiler.compile_deps_program(&lam);

        let [exported_ident] = deps.program.exports.as_slice() else {
            panic!("expected a single export after the trailing effect");
        };
        assert!(exported_ident.same(&exported));

        assert!(
            deps.program.block.iter().any(|stmt| matches!(
                &stmt.desc,
                StatementDesc::Exp(Expression {
                    desc: ExpressionDesc::Bin(
                        BinOp::Eq,
                        left,
                        right,
                    ),
                    ..
                }) if matches!(
                    left.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(VIdent::Id(id)),
                        ..
                    } if id.same(&exported)
                ) && matches!(
                    right.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Number(Number::Int { i: 2, .. }),
                        ..
                    }
                )
            )),
            "expected the trailing assignment effect to remain in the program block"
        );
    }

    #[test]
    fn compile_deps_program_skips_unreachable_throwing_export_binding_declaration() {
        let mut compiler = LambdaCompiler::new();
        let exported = Ident::create_local("u");
        let export_block = Lambda::prim(
            Primitive::Pmakeblock(
                0,
                TagInfo::ModuleExport(vec![exported.clone()]),
                Mutable::Immutable,
            ),
            vec![Lambda::var(exported.clone())],
            Location::none(),
        );
        let lam = Lambda::let_(
            LetKind::Strict,
            exported.clone(),
            Lambda::prim(
                Primitive::Praise,
                vec![Lambda::const_(Constant::string("boom"))],
                Location::none(),
            ),
            export_block,
        );

        let deps = compiler.compile_deps_program(&lam);

        assert_eq!(deps.program.exports, vec![exported.clone()]);
        let [stmt] = deps.program.block.as_slice() else {
            panic!(
                "expected the terminating throw to stay as the only statement, got {:?}",
                deps.program.block
            );
        };
        assert!(matches!(
            stmt,
            Statement {
                desc: StatementDesc::Throw(Expression {
                    desc: ExpressionDesc::Str { txt, .. },
                    ..
                }),
                ..
            } if txt == "boom"
        ));
    }

    #[test]
    fn compile_deps_program_skips_unreachable_nested_throwing_export_binding_declaration() {
        let mut compiler = LambdaCompiler::new();
        let exported = Ident::create_local("A");
        let nested = Ident::create_local("u");
        let export_block = Lambda::prim(
            Primitive::Pmakeblock(
                0,
                TagInfo::ModuleExport(vec![exported.clone()]),
                Mutable::Immutable,
            ),
            vec![Lambda::var(exported.clone())],
            Location::none(),
        );
        let lam = Lambda::let_(
            LetKind::Strict,
            exported.clone(),
            Lambda::let_(
                LetKind::Strict,
                nested.clone(),
                Lambda::prim(
                    Primitive::Praise,
                    vec![Lambda::const_(Constant::string("boom"))],
                    Location::none(),
                ),
                Lambda::prim(
                    Primitive::Pmakeblock(
                        0,
                        TagInfo::record(
                            vec![(nested.name().to_string(), false)],
                            crate::parser::ast::MutableFlag::Immutable,
                        ),
                        Mutable::Immutable,
                    ),
                    vec![Lambda::var(nested)],
                    Location::none(),
                ),
            ),
            export_block,
        );

        let deps = compiler.compile_deps_program(&lam);

        assert_eq!(deps.program.exports, vec![exported.clone()]);
        let [stmt] = deps.program.block.as_slice() else {
            panic!(
                "expected the terminating throw to stay as the only statement, got {:?}",
                deps.program.block
            );
        };
        assert!(
            matches!(
                stmt,
                Statement {
                    desc: StatementDesc::Throw(Expression {
                        desc: ExpressionDesc::Str { txt, .. },
                        ..
                    }),
                    ..
                } if txt == "boom"
            ),
            "expected a terminating throw, got {:?}",
            stmt
        );
    }

    #[test]
    fn compile_return_block_skips_unreachable_sequence_after_throw() {
        let mut compiler = LambdaCompiler::new();
        let block = compiler.compile_return_block(&Lambda::seq(
            Lambda::prim(
                Primitive::Praise,
                vec![Lambda::const_(Constant::string("boom"))],
                Location::none(),
            ),
            Lambda::const_(Constant::int(12)),
        ));

        let [stmt] = block.as_slice() else {
            panic!("expected only the terminating throw, got {:?}", block);
        };
        assert!(matches!(
            stmt,
            Statement {
                desc: StatementDesc::Throw(Expression {
                    desc: ExpressionDesc::Str { txt, .. },
                    ..
                }),
                ..
            } if txt == "boom"
        ));
    }

    #[test]
    fn compile_return_block_lowers_trywith_in_return_position() {
        let mut compiler = LambdaCompiler::new();
        let callee = Ident::create_local("g");
        let exn = Ident::create_local("exn");
        let block = compiler.compile_return_block(&Lambda::LtryWith(
            Box::new(Lambda::Lapply(Apply {
                ap_func: Box::new(Lambda::var(callee)),
                ap_args: vec![],
                ap_info: ApInfo {
                    loc: Location::none(),
                    inlined: InlineAttribute::Default,
                    status: ApplyStatus::Na,
                },
                ap_transformed_jsx: false,
            })),
            exn.clone(),
            Box::new(Lambda::const_(Constant::int(0))),
        ));

        let [stmt] = block.as_slice() else {
            panic!("expected a single try statement, got {:?}", block);
        };
        let StatementDesc::Try(body, Some((caught, handler)), None) = &stmt.desc else {
            panic!("expected a try statement, got {:?}", stmt);
        };

        assert!(caught.same(&exn));
        assert!(matches!(
            body.as_slice(),
            [Statement {
                desc: StatementDesc::Return(_),
                ..
            }]
        ));
        assert!(matches!(
            handler.as_slice(),
            [Statement {
                desc: StatementDesc::Return(Expression {
                    desc: ExpressionDesc::Number(Number::Int { i: 0, .. }),
                    ..
                }),
                ..
            }]
        ));
    }

    #[test]
    fn trywith_expression_result_temp_uses_tmp_name_like_ocaml() {
        let mut compiler = LambdaCompiler::new();
        let exn = Ident::create_local("exn");
        let compiled = compiler.compile_expr(&Lambda::LtryWith(
            Box::new(Lambda::const_(Constant::int(1))),
            exn.clone(),
            Box::new(Lambda::const_(Constant::int(2))),
        ));

        let [declare, try_stmt] = compiled.prelude.as_slice() else {
            panic!("expected a declaration followed by a try statement");
        };
        let StatementDesc::Variable(VariableDeclaration { ident: result, .. }) = &declare.desc
        else {
            panic!("expected the trywith result temp declaration");
        };
        assert_eq!(result.name(), "tmp");
        let StatementDesc::Try(body, Some((caught, handler)), None) = &try_stmt.desc else {
            panic!("expected a try statement");
        };
        assert!(caught.same(&exn));
        assert!(matches!(
            body.as_slice(),
            [Statement {
                desc: StatementDesc::Exp(Expression {
                    desc: ExpressionDesc::Bin(BinOp::Eq, lhs, rhs),
                    ..
                }),
                ..
            }] if matches!(
                (&lhs.desc, &rhs.desc),
                (
                    ExpressionDesc::Var(crate::js_ir::VIdent::Id(lhs_id)),
                    ExpressionDesc::Number(Number::Int { i: 1, .. })
                ) if lhs_id.same(result)
            )
        ));
        assert!(matches!(
            handler.as_slice(),
            [Statement {
                desc: StatementDesc::Exp(Expression {
                    desc: ExpressionDesc::Bin(BinOp::Eq, lhs, rhs),
                    ..
                }),
                ..
            }] if matches!(
                (&lhs.desc, &rhs.desc),
                (
                    ExpressionDesc::Var(crate::js_ir::VIdent::Id(lhs_id)),
                    ExpressionDesc::Number(Number::Int { i: 2, .. })
                ) if lhs_id.same(result)
            )
        ));
        assert!(matches!(
            compiled.expr,
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(result)
        ));
    }

    #[test]
    fn nested_static_raises_in_return_position_keep_the_return_continuation() {
        let mut compiler = LambdaCompiler::new();
        let cond_a = Ident::create_local("condA");
        let cond_b = Ident::create_local("condB");
        let block = compiler.compile_return_block(&Lambda::LstaticCatch(
            Box::new(Lambda::LstaticCatch(
                Box::new(Lambda::if_(
                    Lambda::var(cond_a),
                    Lambda::const_(Constant::int(1)),
                    Lambda::static_raise(2, Vec::new()),
                )),
                (2, vec![]),
                Box::new(Lambda::if_(
                    Lambda::var(cond_b),
                    Lambda::const_(Constant::int(2)),
                    Lambda::static_raise(1, Vec::new()),
                )),
            )),
            (1, vec![]),
            Box::new(Lambda::prim(
                Primitive::Praise,
                vec![Lambda::const_(Constant::string("boom"))],
                Location::none(),
            )),
        ));

        let rendered = print_block(&block);
        assert!(
            !rendered.contains("let ifres"),
            "nested static raises lost the return continuation and reintroduced ifres temps:\n{rendered}"
        );
        assert!(
            rendered.contains("if (condA)") && rendered.contains("return 1;"),
            "expected the first static-raise branch to stay in return position:\n{rendered}"
        );
        assert!(
            rendered.contains("if (condB)") && rendered.contains("return 2;"),
            "expected the nested handler to stay in return position:\n{rendered}"
        );
        assert!(
            rendered.contains("throw \"boom\";"),
            "expected the final handler to stay as the fallthrough throw:\n{rendered}"
        );
    }

    #[test]
    fn block_finishes_output_ignores_switch_case_breaks() {
        let block = vec![Statement::new(StatementDesc::StringSwitch(
            Expression::bool(true),
            vec![StringClause {
                tag_type: crate::lambda::SwitchCaseTag::String("a".to_string()),
                clause: CaseClause {
                    body: vec![
                        Statement::exp(Expression::string("a".to_string())),
                        Statement::break_(),
                    ],
                    should_break: false,
                    comment: None,
                },
            }],
            Some(vec![Statement::throw(Expression::string(
                "boom".to_string(),
            ))]),
        ))];

        assert!(block_terminates(&block));
        assert!(!block_finishes_output(&block));
    }

    #[test]
    fn lowers_expression_sequences_to_js_comma_expressions() {
        let mut compiler = LambdaCompiler::new();
        let callback = Ident::create_local("callback");
        let sequence = Lambda::Lsequence(
            Box::new(Lambda::Lapply(Apply {
                ap_func: Box::new(Lambda::var(callback.clone())),
                ap_args: vec![],
                ap_info: ApInfo {
                    loc: Location::none(),
                    inlined: InlineAttribute::Default,
                    status: ApplyStatus::Na,
                },
                ap_transformed_jsx: false,
            })),
            Box::new(Lambda::const_(Constant::none())),
        );
        let program = compiler.compile_program(&Lambda::prim(
            Primitive::Pmakearray,
            vec![sequence],
            Location::none(),
        ));

        let [stmt] = program.block.as_slice() else {
            panic!("expected a single expression statement");
        };
        match &stmt.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Array(items, _),
                ..
            }) => {
                let [item] = items.as_slice() else {
                    panic!("expected a single array element");
                };
                match &item.desc {
                    ExpressionDesc::Seq(first, second) => {
                        assert!(matches!(
                            first.as_ref(),
                            Expression {
                                desc: ExpressionDesc::Call(func, args, _),
                                ..
                            } if args.is_empty() && matches!(
                                func.as_ref(),
                                Expression {
                                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                                    ..
                                } if id.same(&callback)
                            )
                        ));
                        assert!(matches!(
                            second.as_ref(),
                            Expression {
                                desc: ExpressionDesc::Undefined { is_unit: false },
                                ..
                            }
                        ));
                    }
                    other => panic!("expected comma expression inside array, got {other:?}"),
                }
            }
            other => panic!("expected array literal output, got {other:?}"),
        }
    }

    #[test]
    fn nested_effect_sequences_drop_intermediate_pignore_suffixes_when_appended_to_values() {
        let mut compiler = LambdaCompiler::new();
        let callback = Ident::create_local("callback");
        let value = Ident::create_local("value");
        let call = Lambda::Lapply(Apply {
            ap_func: Box::new(Lambda::var(callback.clone())),
            ap_args: vec![],
            ap_info: ApInfo {
                loc: Location::none(),
                inlined: InlineAttribute::Default,
                status: ApplyStatus::Na,
            },
            ap_transformed_jsx: false,
        });
        let sequence = Lambda::Lsequence(
            Box::new(Lambda::Lsequence(
                Box::new(call),
                Box::new(Lambda::prim(
                    Primitive::Pignore,
                    vec![Lambda::const_(Constant::int(3))],
                    Location::none(),
                )),
            )),
            Box::new(Lambda::var(value.clone())),
        );

        let compiled = compiler.compile_expr(&sequence);

        assert!(
            compiled.prelude.is_empty(),
            "nested effect/value sequence unexpectedly produced prelude statements"
        );
        match &compiled.expr.desc {
            ExpressionDesc::Seq(first, second) => {
                assert!(matches!(
                    first.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Call(func, args, _),
                        ..
                    } if args.is_empty() && matches!(
                        func.as_ref(),
                        Expression {
                            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                            ..
                        } if id.same(&callback)
                    )
                ));
                assert!(matches!(
                    second.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&value)
                ));
            }
            other => panic!("expected cleaned sequence expression, got {other:?}"),
        }
    }

    #[test]
    fn int_switch_expressions_assign_branch_values_into_the_result_temp() {
        let mut compiler = LambdaCompiler::new();
        let scrutinee = Ident::create_local("scrutinee");
        let compiled = compiler.compile_expr(&Lambda::Lswitch(
            Box::new(Lambda::var(scrutinee.clone())),
            LambdaSwitch {
                sw_consts_full: true,
                sw_consts: vec![
                    (0, Lambda::const_(Constant::int(1))),
                    (1, Lambda::const_(Constant::int(2))),
                ],
                sw_blocks_full: false,
                sw_blocks: vec![],
                sw_failaction: Some(Box::new(Lambda::const_(Constant::int(3)))),
                sw_names: None,
            },
        ));

        let [declare, switch_stmt] = compiled.prelude.as_slice() else {
            panic!("expected a declaration and switch statement");
        };
        let StatementDesc::Variable(VariableDeclaration { ident: result, .. }) = &declare.desc
        else {
            panic!("expected the switch temporary declaration");
        };
        assert_eq!(result.name(), "tmp");
        let StatementDesc::IntSwitch(test, clauses, Some(default_block)) = &switch_stmt.desc else {
            panic!("expected an integer switch with a default block");
        };
        assert!(matches!(
            test,
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&scrutinee)
        ));
        assert!(matches!(
            compiled.expr,
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(result)
        ));

        let expected_cases = [(0, 1_i32), (1, 2_i32)];
        for ((tag, clause), (expected_tag, expected_value)) in clauses.iter().zip(expected_cases) {
            assert_eq!(*tag, expected_tag);
            assert_switch_case_assigns_int_result(&clause.body, result, expected_value);
        }
        assert_switch_case_assigns_int_result(default_block, result, 3);
    }

    #[test]
    fn string_switch_expressions_assign_branch_values_into_the_result_temp() {
        let mut compiler = LambdaCompiler::new();
        let scrutinee = Ident::create_local("scrutinee");
        let compiled = compiler.compile_expr(&Lambda::LstringSwitch(
            Box::new(Lambda::var(scrutinee.clone())),
            vec![
                ("linux".to_string(), Lambda::const_(Constant::int(1))),
                ("darwin".to_string(), Lambda::const_(Constant::int(2))),
            ],
            Some(Box::new(Lambda::const_(Constant::int(3)))),
        ));

        let [declare, switch_stmt] = compiled.prelude.as_slice() else {
            panic!("expected a declaration and string switch statement");
        };
        let StatementDesc::Variable(VariableDeclaration { ident: result, .. }) = &declare.desc
        else {
            panic!("expected the string switch temporary declaration");
        };
        assert_eq!(result.name(), "tmp");
        let StatementDesc::StringSwitch(test, clauses, Some(default_block)) = &switch_stmt.desc
        else {
            panic!("expected a string switch with a default block");
        };
        assert!(matches!(
            test,
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&scrutinee)
        ));
        assert!(matches!(
            compiled.expr,
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(result)
        ));

        let expected_cases = [("linux", 1_i32), ("darwin", 2_i32)];
        for (clause, (expected_tag, expected_value)) in clauses.iter().zip(expected_cases) {
            assert_eq!(
                clause.tag_type,
                SwitchCaseTag::String(expected_tag.to_string())
            );
            assert_switch_case_assigns_int_result(&clause.clause.body, result, expected_value);
        }
        assert_switch_case_assigns_int_result(default_block, result, 3);
    }

    #[test]
    fn int_switch_expressions_group_adjacent_equal_cases_and_drop_default_duplicates() {
        let mut compiler = LambdaCompiler::new();
        let scrutinee = Ident::create_local("scrutinee");
        let compiled = compiler.compile_expr(&Lambda::Lswitch(
            Box::new(Lambda::var(scrutinee.clone())),
            LambdaSwitch {
                sw_consts_full: false,
                sw_consts: vec![
                    (0, Lambda::const_(Constant::int(1))),
                    (1, Lambda::const_(Constant::int(1))),
                    (2, Lambda::const_(Constant::int(2))),
                ],
                sw_blocks_full: false,
                sw_blocks: vec![],
                sw_failaction: Some(Box::new(Lambda::const_(Constant::int(2)))),
                sw_names: None,
            },
        ));

        let [declare, switch_stmt] = compiled.prelude.as_slice() else {
            panic!("expected a declaration and switch statement");
        };
        let StatementDesc::Variable(VariableDeclaration { ident: result, .. }) = &declare.desc
        else {
            panic!("expected the switch temporary declaration");
        };
        let StatementDesc::IntSwitch(test, clauses, Some(default_block)) = &switch_stmt.desc else {
            panic!("expected an integer switch with a default block");
        };
        assert!(matches!(
            test,
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&scrutinee)
        ));
        assert_eq!(
            clauses.len(),
            2,
            "expected the default-duplicate case to be filtered"
        );
        assert_eq!(clauses[0].0, 0);
        assert!(
            clauses[0].1.body.is_empty(),
            "expected the first grouped case to fall through"
        );
        assert!(!clauses[0].1.should_break);
        assert_eq!(clauses[1].0, 1);
        assert_switch_case_assigns_int_result(&clauses[1].1.body, result, 1);
        assert_switch_case_assigns_int_result(default_block, result, 2);
    }

    #[test]
    fn int_switch_expressions_group_non_adjacent_equal_cases_like_ocaml_stable_group() {
        let mut compiler = LambdaCompiler::new();
        let scrutinee = Ident::create_local("scrutinee");
        let compiled = compiler.compile_expr(&Lambda::Lswitch(
            Box::new(Lambda::var(scrutinee.clone())),
            LambdaSwitch {
                sw_consts_full: true,
                sw_consts: vec![
                    (0, Lambda::const_(Constant::int(2))),
                    (1, Lambda::const_(Constant::int(1))),
                    (2, Lambda::const_(Constant::int(2))),
                ],
                sw_blocks_full: false,
                sw_blocks: vec![],
                sw_failaction: None,
                sw_names: None,
            },
        ));

        let [declare, switch_stmt] = compiled.prelude.as_slice() else {
            panic!("expected a declaration and switch statement");
        };
        let StatementDesc::Variable(VariableDeclaration { ident: result, .. }) = &declare.desc
        else {
            panic!("expected the switch temporary declaration");
        };
        let StatementDesc::IntSwitch(_, clauses, None) = &switch_stmt.desc else {
            panic!("expected an exhaustive integer switch");
        };

        assert_eq!(
            clauses.len(),
            3,
            "expected OCaml-style stable grouping to keep all tags while reordering groups"
        );
        assert_eq!(clauses[0].0, 1);
        assert_switch_case_assigns_int_result(&clauses[0].1.body, result, 1);
        assert_eq!(clauses[1].0, 0);
        assert!(
            clauses[1].1.body.is_empty(),
            "expected the first equal-body case to fall through after stable grouping"
        );
        assert!(!clauses[1].1.should_break);
        assert_eq!(clauses[2].0, 2);
        assert_switch_case_assigns_int_result(&clauses[2].1.body, result, 2);
    }

    #[test]
    fn string_switch_effects_group_adjacent_equal_cases_and_drop_default_duplicates() {
        let mut compiler = LambdaCompiler::new();
        let scrutinee = Ident::create_local("scrutinee");
        let captured = Ident::create_local("captured");
        let block = compiler.compile_effect_block(&Lambda::LstringSwitch(
            Box::new(Lambda::var(scrutinee.clone())),
            vec![
                (
                    "A".to_string(),
                    Lambda::Lassign(captured.clone(), Box::new(Lambda::const_(Constant::int(1)))),
                ),
                (
                    "B".to_string(),
                    Lambda::Lassign(captured.clone(), Box::new(Lambda::const_(Constant::int(1)))),
                ),
                (
                    "C".to_string(),
                    Lambda::Lassign(captured.clone(), Box::new(Lambda::const_(Constant::int(2)))),
                ),
            ],
            Some(Box::new(Lambda::Lassign(
                captured.clone(),
                Box::new(Lambda::const_(Constant::int(2))),
            ))),
        ));

        let [switch_stmt] = block.as_slice() else {
            panic!("expected a single string switch");
        };
        let StatementDesc::StringSwitch(test, clauses, Some(default_block)) = &switch_stmt.desc
        else {
            panic!("expected a string switch with a default block");
        };
        assert!(matches!(
            test,
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&scrutinee)
        ));
        assert_eq!(
            clauses.len(),
            2,
            "expected the default-duplicate case to be filtered"
        );
        assert_eq!(clauses[0].tag_type, SwitchCaseTag::String("A".to_string()));
        assert!(
            clauses[0].clause.body.is_empty(),
            "expected the first grouped case to fall through"
        );
        assert!(!clauses[0].clause.should_break);
        assert_eq!(clauses[1].tag_type, SwitchCaseTag::String("B".to_string()));
        assert!(clauses[1].clause.should_break);
        assert_effect_assignment_writes_int(&clauses[1].clause.body, &captured, 1);
        assert_effect_assignment_writes_int(default_block, &captured, 2);
    }

    #[test]
    fn string_switch_effects_group_non_adjacent_equal_cases_like_ocaml_stable_group() {
        let mut compiler = LambdaCompiler::new();
        let scrutinee = Ident::create_local("scrutinee");
        let captured = Ident::create_local("captured");
        let block = compiler.compile_effect_block(&Lambda::LstringSwitch(
            Box::new(Lambda::var(scrutinee.clone())),
            vec![
                (
                    "A".to_string(),
                    Lambda::Lassign(captured.clone(), Box::new(Lambda::const_(Constant::int(2)))),
                ),
                (
                    "B".to_string(),
                    Lambda::Lassign(captured.clone(), Box::new(Lambda::const_(Constant::int(1)))),
                ),
                (
                    "C".to_string(),
                    Lambda::Lassign(captured.clone(), Box::new(Lambda::const_(Constant::int(2)))),
                ),
            ],
            None,
        ));

        let [switch_stmt] = block.as_slice() else {
            panic!("expected a single string switch");
        };
        let StatementDesc::StringSwitch(_, clauses, None) = &switch_stmt.desc else {
            panic!("expected an exhaustive string switch");
        };

        assert_eq!(clauses.len(), 3);
        assert_eq!(clauses[0].tag_type, SwitchCaseTag::String("B".to_string()));
        assert_effect_assignment_writes_int(&clauses[0].clause.body, &captured, 1);
        assert_eq!(clauses[1].tag_type, SwitchCaseTag::String("A".to_string()));
        assert!(
            clauses[1].clause.body.is_empty(),
            "expected the first equal-body case to fall through after stable grouping"
        );
        assert!(!clauses[1].clause.should_break);
        assert_eq!(clauses[2].tag_type, SwitchCaseTag::String("C".to_string()));
        assert_effect_assignment_writes_int(&clauses[2].clause.body, &captured, 2);
    }

    #[test]
    fn fallthrough_handlers_do_not_reorder_grouped_named_string_return_cases() {
        let mut compiler = LambdaCompiler::new();
        let scrutinee = Ident::create_local("scrutinee");
        let case_a = Lambda::const_(Constant::int(2));
        let case_b = Lambda::const_(Constant::int(1));
        let case_c = Lambda::const_(Constant::int(2));
        let cases = vec![
            (SwitchCaseTag::String("A".to_string()), &case_a),
            (SwitchCaseTag::String("B".to_string()), &case_b),
            (SwitchCaseTag::String("C".to_string()), &case_c),
        ];

        let block = compiler.with_fallthrough_return_handler(1, &[], |this| {
            this.compile_named_string_switch_return(Expression::var(scrutinee.clone()), &cases, None, true)
        });

        let [switch_stmt] = block.as_slice() else {
            panic!("expected a single string switch");
        };
        let StatementDesc::StringSwitch(test, clauses, None) = &switch_stmt.desc else {
            panic!("expected an exhaustive string switch");
        };
        assert!(matches!(
            test,
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&scrutinee)
        ));

        assert_eq!(clauses.len(), 3);
        assert_eq!(clauses[0].tag_type, SwitchCaseTag::String("B".to_string()));
        assert_switch_case_returns_int_result(&clauses[0].clause.body, 1);
        assert_eq!(clauses[1].tag_type, SwitchCaseTag::String("A".to_string()));
        assert!(clauses[1].clause.body.is_empty());
        assert_eq!(clauses[2].tag_type, SwitchCaseTag::String("C".to_string()));
        assert_switch_case_returns_int_result(&clauses[2].clause.body, 2);
    }

    #[test]
    fn fallthrough_handlers_do_not_reorder_grouped_string_switch_return_blocks() {
        let mut compiler = LambdaCompiler::new();
        let scrutinee = Ident::create_local("scrutinee");
        let block = compiler.with_fallthrough_return_handler(1, &[], |this| {
            this.compile_string_switch_return_block(
                &Lambda::var(scrutinee.clone()),
                &[
                    ("A".to_string(), Lambda::const_(Constant::int(2))),
                    ("B".to_string(), Lambda::const_(Constant::int(1))),
                    ("C".to_string(), Lambda::const_(Constant::int(2))),
                ],
                None,
            )
        });

        let [switch_stmt] = block.as_slice() else {
            panic!("expected a single string switch");
        };
        let StatementDesc::StringSwitch(test, clauses, None) = &switch_stmt.desc else {
            panic!("expected an exhaustive string switch");
        };
        assert!(matches!(
            test,
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&scrutinee)
        ));

        assert_eq!(clauses.len(), 3);
        assert_eq!(clauses[0].tag_type, SwitchCaseTag::String("B".to_string()));
        assert_switch_case_returns_int_result(&clauses[0].clause.body, 1);
        assert_eq!(clauses[1].tag_type, SwitchCaseTag::String("A".to_string()));
        assert!(clauses[1].clause.body.is_empty());
        assert_eq!(clauses[2].tag_type, SwitchCaseTag::String("C".to_string()));
        assert_switch_case_returns_int_result(&clauses[2].clause.body, 2);
    }

    #[test]
    fn let_bindings_lower_string_switches_directly_into_the_declared_binding() {
        let mut compiler = LambdaCompiler::new();
        let version = Ident::create_local("version");
        let scrutinee = Ident::create_local("platform");
        let program = compiler.compile_program(&Lambda::Llet(
            LetKind::Strict,
            version.clone(),
            Box::new(Lambda::LstringSwitch(
                Box::new(Lambda::var(scrutinee.clone())),
                vec![
                    ("linux".to_string(), Lambda::const_(Constant::int(1))),
                    ("darwin".to_string(), Lambda::const_(Constant::int(2))),
                ],
                Some(Box::new(Lambda::const_(Constant::int(3)))),
            )),
            Box::new(Lambda::var(version.clone())),
        ));

        let [declare, switch_stmt] = program.block.as_slice() else {
            panic!("expected a declaration followed by a string switch");
        };
        let StatementDesc::Variable(VariableDeclaration {
            ident, value: None, ..
        }) = &declare.desc
        else {
            panic!("expected an uninitialized binding declaration");
        };
        assert!(ident.same(&version));

        let StatementDesc::StringSwitch(test, clauses, Some(default_block)) = &switch_stmt.desc
        else {
            panic!("expected a direct string switch statement");
        };
        assert!(matches!(
            test,
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&scrutinee)
        ));

        let expected_cases = [("linux", 1_i32), ("darwin", 2_i32)];
        for (clause, (expected_tag, expected_value)) in clauses.iter().zip(expected_cases) {
            assert_eq!(
                clause.tag_type,
                SwitchCaseTag::String(expected_tag.to_string())
            );
            assert_switch_case_assigns_int_result(&clause.clause.body, &version, expected_value);
        }
        assert_switch_default_assigns_int_result(default_block, &version, 3);
    }

    #[test]
    fn single_case_string_switches_with_default_lower_to_if_else() {
        let mut compiler = LambdaCompiler::new();
        let scrutinee = Ident::create_local("platform");
        let compiled = compiler.compile_expr(&Lambda::LstringSwitch(
            Box::new(Lambda::var(scrutinee.clone())),
            vec![("linux".to_string(), Lambda::const_(Constant::int(1)))],
            Some(Box::new(Lambda::const_(Constant::int(2)))),
        ));

        let [declare, if_stmt] = compiled.prelude.as_slice() else {
            panic!("expected a declaration followed by an if statement");
        };
        let StatementDesc::Variable(VariableDeclaration { ident: result, .. }) = &declare.desc
        else {
            panic!("expected the string switch temporary declaration");
        };
        let StatementDesc::If(cond, then_block, else_block) = &if_stmt.desc else {
            panic!("expected single-case string switches to lower to if/else");
        };
        assert_string_equality_check(cond, Some(&scrutinee), None, "linux");
        assert_switch_default_assigns_int_result(then_block, result, 1);
        assert_switch_default_assigns_int_result(else_block, result, 2);
    }

    #[test]
    fn staticcatch_wrapped_string_switches_use_the_handler_as_the_default_value() {
        let mut compiler = LambdaCompiler::new();
        let version = Ident::create_local("version");
        let scrutinee = Ident::create_local("platform");
        let program = compiler.compile_program(&Lambda::Llet(
            LetKind::Strict,
            version.clone(),
            Box::new(Lambda::LstaticCatch(
                Box::new(Lambda::LstringSwitch(
                    Box::new(Lambda::var(scrutinee.clone())),
                    vec![
                        ("linux".to_string(), Lambda::const_(Constant::int(1))),
                        ("darwin".to_string(), Lambda::const_(Constant::int(2))),
                    ],
                    Some(Box::new(Lambda::static_raise(1, Vec::new()))),
                )),
                (1, vec![]),
                Box::new(Lambda::const_(Constant::int(3))),
            )),
            Box::new(Lambda::var(version.clone())),
        ));

        let [declare, switch_stmt] = program.block.as_slice() else {
            panic!("expected a declaration followed by a string switch");
        };
        let StatementDesc::Variable(VariableDeclaration {
            ident, value: None, ..
        }) = &declare.desc
        else {
            panic!("expected an uninitialized binding declaration");
        };
        assert!(ident.same(&version));

        let StatementDesc::StringSwitch(_, clauses, Some(default_block)) = &switch_stmt.desc else {
            panic!("expected a direct string switch statement");
        };
        let expected_cases = [("linux", 1_i32), ("darwin", 2_i32)];
        for (clause, (expected_tag, expected_value)) in clauses.iter().zip(expected_cases) {
            assert_eq!(
                clause.tag_type,
                SwitchCaseTag::String(expected_tag.to_string())
            );
            assert_switch_case_assigns_int_result(&clause.clause.body, &version, expected_value);
        }
        assert_switch_default_assigns_int_result(default_block, &version, 3);
    }

    #[test]
    fn staticcatch_wrapped_int_return_switches_omit_empty_default_arms() {
        let mut compiler = LambdaCompiler::new();
        let action = Ident::create_local("action");
        let block = compiler.compile_return_block(&Lambda::LstaticCatch(
            Box::new(Lambda::LstaticCatch(
                Box::new(Lambda::Lswitch(
                    Box::new(Lambda::var(action.clone())),
                    LambdaSwitch {
                        sw_consts_full: false,
                        sw_consts: vec![
                            (1, Lambda::const_(Constant::int(10))),
                            (2, Lambda::const_(Constant::int(20))),
                        ],
                        sw_blocks_full: true,
                        sw_blocks: vec![],
                        sw_failaction: Some(Box::new(Lambda::static_raise(2, Vec::new()))),
                        sw_names: None,
                    },
                )),
                (2, vec![]),
                Box::new(Lambda::static_raise(1, Vec::new())),
            )),
            (1, vec![]),
            Box::new(Lambda::const_(Constant::int(30))),
        ));

        let [switch_stmt, handler_return] = block.as_slice() else {
            panic!("expected a switch followed by the outer handler return");
        };
        let StatementDesc::IntSwitch(test, clauses, None) = &switch_stmt.desc else {
            panic!("expected the fallthrough default to stay outside the switch");
        };
        assert!(matches!(
            test,
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&action)
        ));

        let expected_cases = [(1, 10_i32), (2, 20_i32)];
        for ((tag, clause), (expected_tag, expected_value)) in clauses.iter().zip(expected_cases) {
            assert_eq!(*tag, expected_tag);
            assert_switch_case_returns_int_result(&clause.body, expected_value);
        }
        match &handler_return.desc {
            StatementDesc::Return(expr) => assert_int_expr(expr, 30),
            other => panic!("expected the outer handler return, got {other:?}"),
        }
    }

    #[test]
    fn staticcatch_wrapped_multi_case_string_return_switches_omit_empty_default_arms() {
        let mut compiler = LambdaCompiler::new();
        let platform = Ident::create_local("platform");
        let block = compiler.compile_return_block(&Lambda::LstaticCatch(
            Box::new(Lambda::LstaticCatch(
                Box::new(Lambda::LstringSwitch(
                    Box::new(Lambda::var(platform.clone())),
                    vec![
                        ("linux".to_string(), Lambda::const_(Constant::int(1))),
                        ("darwin".to_string(), Lambda::const_(Constant::int(2))),
                    ],
                    Some(Box::new(Lambda::static_raise(2, Vec::new()))),
                )),
                (2, vec![]),
                Box::new(Lambda::static_raise(1, Vec::new())),
            )),
            (1, vec![]),
            Box::new(Lambda::const_(Constant::int(3))),
        ));

        let [switch_stmt, handler_return] = block.as_slice() else {
            panic!("expected a switch followed by the outer handler return");
        };
        let StatementDesc::StringSwitch(test, clauses, None) = &switch_stmt.desc else {
            panic!("expected the fallthrough default to stay outside the string switch");
        };
        assert!(matches!(
            test,
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&platform)
        ));

        let expected_cases = [("linux", 1_i32), ("darwin", 2_i32)];
        for (clause, (expected_tag, expected_value)) in clauses.iter().zip(expected_cases) {
            assert_eq!(
                clause.tag_type,
                SwitchCaseTag::String(expected_tag.to_string())
            );
            assert_switch_case_returns_int_result(&clause.clause.body, expected_value);
        }
        match &handler_return.desc {
            StatementDesc::Return(expr) => assert_int_expr(expr, 3),
            other => panic!("expected the outer handler return, got {other:?}"),
        }
    }

    #[test]
    fn staticcatch_wrapped_int_return_switches_keep_single_handlers_as_default_arms() {
        let mut compiler = LambdaCompiler::new();
        let action = Ident::create_local("action");
        let block = compiler.compile_return_block(&Lambda::LstaticCatch(
            Box::new(Lambda::Lswitch(
                Box::new(Lambda::var(action.clone())),
                LambdaSwitch {
                    sw_consts_full: false,
                    sw_consts: vec![
                        (1, Lambda::const_(Constant::int(10))),
                        (2, Lambda::const_(Constant::int(20))),
                    ],
                    sw_blocks_full: true,
                    sw_blocks: vec![],
                    sw_failaction: Some(Box::new(Lambda::static_raise(2, Vec::new()))),
                    sw_names: None,
                },
            )),
            (2, vec![]),
            Box::new(Lambda::const_(Constant::int(30))),
        ));

        let [switch_stmt] = block.as_slice() else {
            panic!("expected a single switch statement");
        };
        let StatementDesc::IntSwitch(test, clauses, Some(default_block)) = &switch_stmt.desc else {
            panic!("expected the single handler to stay as the default arm");
        };
        assert!(matches!(
            test,
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&action)
        ));

        let expected_cases = [(1, 10_i32), (2, 20_i32)];
        for ((tag, clause), (expected_tag, expected_value)) in clauses.iter().zip(expected_cases) {
            assert_eq!(*tag, expected_tag);
            assert_switch_case_returns_int_result(&clause.body, expected_value);
        }
        let [default_return] = default_block.as_slice() else {
            panic!("expected one default return statement");
        };
        match &default_return.desc {
            StatementDesc::Return(expr) => assert_int_expr(expr, 30),
            other => panic!("expected the default return, got {other:?}"),
        }
    }

    #[test]
    fn staticcatch_wrapped_string_return_switches_keep_single_handlers_as_default_arms() {
        let mut compiler = LambdaCompiler::new();
        let platform = Ident::create_local("platform");
        let block = compiler.compile_return_block(&Lambda::LstaticCatch(
            Box::new(Lambda::LstringSwitch(
                Box::new(Lambda::var(platform.clone())),
                vec![
                    ("linux".to_string(), Lambda::const_(Constant::int(1))),
                    ("darwin".to_string(), Lambda::const_(Constant::int(2))),
                ],
                Some(Box::new(Lambda::static_raise(2, Vec::new()))),
            )),
            (2, vec![]),
            Box::new(Lambda::const_(Constant::int(3))),
        ));

        let [switch_stmt] = block.as_slice() else {
            panic!("expected a single string switch statement");
        };
        let StatementDesc::StringSwitch(test, clauses, Some(default_block)) = &switch_stmt.desc else {
            panic!("expected the single handler to stay as the string-switch default arm");
        };
        assert!(matches!(
            test,
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&platform)
        ));

        let expected_cases = [("linux", 1_i32), ("darwin", 2_i32)];
        for (clause, (expected_tag, expected_value)) in clauses.iter().zip(expected_cases) {
            assert_eq!(
                clause.tag_type,
                SwitchCaseTag::String(expected_tag.to_string())
            );
            assert_switch_case_returns_int_result(&clause.clause.body, expected_value);
        }
        let [default_return] = default_block.as_slice() else {
            panic!("expected one default return statement");
        };
        match &default_return.desc {
            StatementDesc::Return(expr) => assert_int_expr(expr, 3),
            other => panic!("expected the default return, got {other:?}"),
        }
    }

    #[test]
    fn untagged_object_return_switches_keep_outer_plain_handler_inside_the_switch() {
        let mut compiler = LambdaCompiler::new();
        let value = Ident::create_local("value");
        let body_id = Ident::create_local("body");
        let block = compiler.compile_return_block(&Lambda::LstaticCatch(
            Box::new(Lambda::Lswitch(
                Box::new(Lambda::var(value.clone())),
                LambdaSwitch {
                    sw_consts_full: false,
                    sw_consts: vec![],
                    sw_blocks_full: false,
                    sw_blocks: vec![(
                        0,
                        Lambda::LstaticCatch(
                            Box::new(Lambda::static_raise(2, Vec::new())),
                            (2, vec![]),
                            Box::new(Lambda::let_(
                                LetKind::Strict,
                                body_id.clone(),
                                Lambda::const_(Constant::int(1)),
                                Lambda::var(body_id.clone()),
                            )),
                        ),
                    )],
                    sw_failaction: Some(Box::new(Lambda::static_raise(1, Vec::new()))),
                    sw_names: Some(SwitchNames {
                        consts: vec![
                            crate::lambda::SwitchTag {
                                name: "Null".to_string(),
                                tag_type: Some(crate::lambda::SwitchCaseTag::Null),
                            },
                            crate::lambda::SwitchTag {
                                name: "String".to_string(),
                                tag_type: Some(crate::lambda::SwitchCaseTag::String(
                                    "string".to_string(),
                                )),
                            },
                        ],
                        blocks: vec![
                            crate::lambda::SwitchBlock {
                                tag: crate::lambda::SwitchTag::named("Object"),
                                tag_name: None,
                                block_type: Some(crate::lambda::SwitchBlockType::Object),
                            },
                            crate::lambda::SwitchBlock {
                                tag: crate::lambda::SwitchTag::named("Array"),
                                tag_name: None,
                                block_type: Some(crate::lambda::SwitchBlockType::Instance(
                                    "Array".to_string(),
                                )),
                            },
                        ],
                    }),
                },
            )),
            (1, vec![]),
            Box::new(Lambda::const_(Constant::int(0))),
        ));

        let rendered = print_block(&block);
        assert!(
            rendered.contains(
                "if (typeof value !== \"object\" || value === null || Array.isArray(value))"
            ),
            "expected the outer handler to stay as the literal-side guard:\n{rendered}"
        );
        assert!(
            !rendered.ends_with("return 0;"),
            "expected the outer handler not to be peeled out as a trailing fallthrough:\n{rendered}"
        );
        assert!(
            rendered.contains("let body = 1;") && rendered.contains("return body;"),
            "expected the object branch to stay inline after the guard:\n{rendered}"
        );
    }

    #[test]
    fn nested_staticcatch_binding_handlers_that_raise_outward_avoid_exit_temps() {
        let mut compiler = LambdaCompiler::new();
        let cond = Ident::create_local("cond");
        let carried = Ident::create_local("carried");
        let block = compiler.compile_return_block(&Lambda::LstaticCatch(
            Box::new(Lambda::LstaticCatch(
                Box::new(Lambda::if_(
                    Lambda::var(cond.clone()),
                    Lambda::const_(Constant::int(0)),
                    Lambda::static_raise(2, Vec::new()),
                )),
                (2, vec![]),
                Box::new(Lambda::static_raise(
                    1,
                    vec![Lambda::const_(Constant::int(1))],
                )),
            )),
            (1, vec![carried.clone()]),
            Box::new(Lambda::var(carried.clone())),
        ));

        let rendered = print_block(&block);
        assert!(
            !rendered.contains("let exit ="),
            "nested binding handlers reintroduced an explicit staticcatch jump temp:\n{rendered}"
        );
        assert!(
            !rendered.contains("if (exit ==="),
            "nested binding handlers still guard the handler behind an exit sentinel:\n{rendered}"
        );
        assert!(
            rendered.contains("return cond ? 0 : 1;")
                || (rendered.contains("if (cond)")
                    && rendered.contains("return 0;")
                    && rendered.contains("return 1;")),
            "expected the outward handler raise to lower directly instead of through an exit temp:\n{rendered}"
        );
    }

    #[test]
    fn return_staticcatchs_share_nontrivial_handlers_across_multiple_exit_sites() {
        let mut compiler = LambdaCompiler::new();
        let cond = Ident::create_local("cond");
        let kind = Ident::create_local("kind");
        let block = compiler.compile_return_block(&Lambda::LstaticCatch(
            Box::new(Lambda::LstaticCatch(
                Box::new(Lambda::if_(
                    Lambda::var(cond.clone()),
                    Lambda::static_raise(2, Vec::new()),
                    Lambda::LstringSwitch(
                        Box::new(Lambda::var(kind.clone())),
                        vec![("e".to_string(), Lambda::const_(Constant::int(4)))],
                        Some(Box::new(Lambda::static_raise(2, Vec::new()))),
                    ),
                )),
                (2, vec![]),
                Box::new(Lambda::LstringSwitch(
                    Box::new(Lambda::var(kind.clone())),
                    vec![("f".to_string(), Lambda::const_(Constant::int(5)))],
                    Some(Box::new(Lambda::static_raise(1, Vec::new()))),
                )),
            )),
            (1, vec![]),
            Box::new(Lambda::const_(Constant::int(6))),
        ));

        let rendered = print_block(&block);
        assert!(
            rendered.contains("let exit = 0;"),
            "expected repeated exits to share the handler behind an exit temp:\n{rendered}"
        );
        assert!(
            rendered.contains("if (exit ==="),
            "expected the shared handler to stay after an explicit exit test:\n{rendered}"
        );
        assert_eq!(
            rendered.matches("=== \"f\"").count(),
            1,
            "expected the nontrivial handler to be emitted once:\n{rendered}"
        );
    }

    #[test]
    fn return_staticcatchs_keep_plain_handlers_inline_across_multiple_exit_sites() {
        let mut compiler = LambdaCompiler::new();
        let kind = Ident::create_local("kind");
        let do_with_b = Ident::create_local("doWithB");
        let block = compiler.compile_return_block(&Lambda::LstaticCatch(
            Box::new(Lambda::LstringSwitch(
                Box::new(Lambda::var(kind.clone())),
                vec![
                    ("four".to_string(), Lambda::static_raise(2, Vec::new())),
                    ("five".to_string(), Lambda::static_raise(2, Vec::new())),
                    ("six".to_string(), Lambda::const_(Constant::int(6))),
                ],
                Some(Box::new(Lambda::const_(Constant::int(7)))),
            )),
            (2, vec![]),
            Box::new(Lambda::apply(
                Lambda::var(do_with_b.clone()),
                vec![Lambda::var(kind.clone())],
                ApInfo {
                    loc: Location::none(),
                    inlined: InlineAttribute::Default,
                    status: ApplyStatus::Na,
                },
                false,
            )),
        ));

        let rendered = print_block(&block);
        assert!(
            !rendered.contains("let exit ="),
            "plain multi-exit handlers should stay inline without an exit temp:\n{rendered}"
        );
        assert!(
            rendered.contains("case \"four\" :") && rendered.contains("case \"five\" :"),
            "expected grouped inline cases for the shared handler:\n{rendered}"
        );
        assert_eq!(
            rendered.matches("return doWithB(kind);").count(),
            1,
            "expected the shared plain handler to stay inline in the switch:\n{rendered}"
        );
    }

    #[test]
    fn single_case_staticcatch_wrapped_named_variant_return_switch_falls_through_to_handler() {
        let mut compiler = LambdaCompiler::new();
        let action = Ident::create_local("action");
        let block = compiler.with_return_unit_context(true, |compiler| {
            compiler.compile_return_block(&Lambda::LstaticCatch(
                Box::new(Lambda::Lswitch(
                    Box::new(Lambda::var(action.clone())),
                    LambdaSwitch {
                        sw_consts_full: false,
                        sw_consts: vec![(0, Lambda::const_(Constant::int(1)))],
                        sw_blocks_full: true,
                        sw_blocks: vec![],
                        sw_failaction: Some(Box::new(Lambda::static_raise(7, Vec::new()))),
                        sw_names: Some(SwitchNames {
                            consts: vec![crate::lambda::SwitchTag::named("One")],
                            blocks: vec![],
                        }),
                    },
                )),
                (7, vec![]),
                Box::new(Lambda::const_(Constant::int(2))),
            ))
        });

        let [if_stmt, handler_return] = block.as_slice() else {
            panic!("expected an if statement followed by the handler return");
        };
        let (cond, then_block, else_block) = match &if_stmt.desc {
            StatementDesc::If(cond, then_block, else_block) => (cond, then_block, else_block),
            StatementDesc::Block(inner) => {
                let [inner_if] = inner.as_slice() else {
                    panic!("expected the staticcatch wrapper block to contain a single if");
                };
                let StatementDesc::If(cond, then_block, else_block) = &inner_if.desc else {
                    panic!(
                        "expected the single-case staticcatch switch to lower to if/fallthrough"
                    );
                };
                (cond, then_block, else_block)
            }
            other => panic!(
                "expected the single-case staticcatch switch to lower to if/fallthrough, got {other:?}"
            ),
        };
        assert_string_equality_check(cond, Some(&action), None, "One");
        assert!(
            else_block.is_empty(),
            "unexpected else block: {else_block:?}"
        );
        assert_switch_case_returns_int_result(then_block, 1);
        match &handler_return.desc {
            StatementDesc::Return(expr) => assert_int_expr(expr, 2),
            other => panic!("expected the fallthrough handler return, got {other:?}"),
        }
    }

    #[test]
    fn multi_case_staticcatch_wrapped_named_variant_return_switch_moves_fallthrough_cases_last() {
        let mut compiler = LambdaCompiler::new();
        let action = Ident::create_local("action");
        let block = compiler.compile_return_block(&Lambda::LstaticCatch(
            Box::new(Lambda::LstaticCatch(
                Box::new(Lambda::LstaticCatch(
                    Box::new(Lambda::Lswitch(
                        Box::new(Lambda::var(action.clone())),
                        LambdaSwitch {
                            sw_consts_full: true,
                            sw_consts: vec![
                                (0, Lambda::static_raise(4, Vec::new())),
                                (1, Lambda::static_raise(1, Vec::new())),
                                (2, Lambda::static_raise(4, Vec::new())),
                            ],
                            sw_blocks_full: true,
                            sw_blocks: vec![],
                            sw_failaction: None,
                            sw_names: Some(SwitchNames {
                                consts: vec![
                                    crate::lambda::SwitchTag::named("A"),
                                    crate::lambda::SwitchTag::named("B"),
                                    crate::lambda::SwitchTag::named("C"),
                                ],
                                blocks: vec![],
                            }),
                        },
                    )),
                    (4, vec![]),
                    Box::new(Lambda::static_raise(2, Vec::new())),
                )),
                (2, vec![]),
                Box::new(Lambda::const_(Constant::JsFalse)),
            )),
            (1, vec![]),
            Box::new(Lambda::const_(Constant::JsTrue)),
        ));

        let [switch_stmt, handler_return] = block.as_slice() else {
            panic!("expected a switch followed by the fallthrough handler return");
        };
        let StatementDesc::StringSwitch(test, clauses, None) = &switch_stmt.desc else {
            panic!("expected a named-constructor string switch");
        };
        assert!(matches!(
            test,
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&action)
        ));

        let expected_tags = ["B", "A", "C"];
        assert_eq!(clauses.len(), expected_tags.len());
        for (clause, expected_tag) in clauses.iter().zip(expected_tags) {
            assert_eq!(
                clause.tag_type,
                SwitchCaseTag::String(expected_tag.to_string())
            );
        }
        assert_switch_case_returns_bool_result(&clauses[0].clause.body, true);
        assert!(clauses[1].clause.body.is_empty());
        assert!(clauses[2].clause.body.is_empty());
        match &handler_return.desc {
            StatementDesc::Return(Expression {
                desc: ExpressionDesc::Bool(value),
                ..
            }) => assert!(!value),
            other => panic!("expected the fallthrough handler return, got {other:?}"),
        }
    }

    #[test]
    fn nested_named_variant_return_switches_keep_plain_inner_handlers_as_default_arms() {
        let mut compiler = LambdaCompiler::new();
        let action = Ident::create_local("action");
        let block = compiler.compile_return_block(&Lambda::LstaticCatch(
            Box::new(Lambda::LstaticCatch(
                Box::new(Lambda::LstaticCatch(
                    Box::new(Lambda::Lswitch(
                        Box::new(Lambda::var(action.clone())),
                        LambdaSwitch {
                            sw_consts_full: false,
                            sw_consts: vec![
                                (0, Lambda::static_raise(4, Vec::new())),
                                (1, Lambda::static_raise(4, Vec::new())),
                                (2, Lambda::static_raise(5, Vec::new())),
                                (3, Lambda::static_raise(5, Vec::new())),
                            ],
                            sw_blocks_full: true,
                            sw_blocks: vec![],
                            sw_failaction: Some(Box::new(Lambda::static_raise(3, Vec::new()))),
                            sw_names: Some(SwitchNames {
                                consts: vec![
                                    crate::lambda::SwitchTag::named("Four"),
                                    crate::lambda::SwitchTag::named("Five"),
                                    crate::lambda::SwitchTag::named("Six"),
                                    crate::lambda::SwitchTag::named("Seven"),
                                ],
                                blocks: vec![],
                            }),
                        },
                    )),
                    (3, vec![]),
                    Box::new(Lambda::const_(Constant::int(10))),
                )),
                (4, vec![]),
                Box::new(Lambda::const_(Constant::int(20))),
            )),
            (5, vec![]),
            Box::new(Lambda::const_(Constant::int(30))),
        ));
        let rendered = print_block(&block);

        let [switch_stmt] = block.as_slice() else {
            panic!("expected a single switch with the plain handler kept as the default arm:\n{rendered}");
        };
        let StatementDesc::StringSwitch(test, clauses, Some(default_block)) = &switch_stmt.desc else {
            panic!("expected the innermost plain handler to stay in the switch default:\n{rendered}");
        };
        assert!(matches!(
            test,
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&action)
        ));

        let expected_tags = ["Four", "Five", "Six", "Seven"];
        assert_eq!(clauses.len(), expected_tags.len());
        for (clause, expected_tag) in clauses.iter().zip(expected_tags) {
            assert_eq!(
                clause.tag_type,
                SwitchCaseTag::String(expected_tag.to_string())
            );
        }
        assert!(clauses[0].clause.body.is_empty());
        assert_switch_case_returns_int_result(&clauses[1].clause.body, 20);
        assert!(clauses[2].clause.body.is_empty());
        assert_switch_case_returns_int_result(&clauses[3].clause.body, 30);
        assert_switch_default_returns_int_result(default_block, 10);
    }

    fn gpr_1438_switch_cases(b: &Ident, c: &Ident, d: &Ident, e: &Ident) -> Vec<(i32, Lambda)> {
        vec![
            (98, Lambda::var(c.clone())),
            (99, Lambda::static_raise(1, Vec::new())),
            (100, Lambda::static_raise(2, Vec::new())),
            (101, Lambda::static_raise(2, Vec::new())),
            (102, Lambda::static_raise(2, Vec::new())),
            (103, Lambda::static_raise(2, Vec::new())),
            (104, Lambda::static_raise(2, Vec::new())),
            (105, Lambda::static_raise(2, Vec::new())),
            (106, Lambda::var(d.clone())),
            (107, Lambda::var(e.clone())),
            (108, Lambda::static_raise(2, Vec::new())),
            (109, Lambda::static_raise(2, Vec::new())),
            (110, Lambda::static_raise(2, Vec::new())),
            (111, Lambda::static_raise(2, Vec::new())),
            (112, Lambda::static_raise(2, Vec::new())),
            (113, Lambda::static_raise(2, Vec::new())),
            (114, Lambda::static_raise(2, Vec::new())),
            (115, Lambda::static_raise(2, Vec::new())),
            (116, Lambda::var(b.clone())),
            (117, Lambda::static_raise(2, Vec::new())),
            (118, Lambda::static_raise(1, Vec::new())),
        ]
    }

    fn gpr_1438_fallthrough_handler() -> Lambda {
        let param = Ident::create_local("param");
        Lambda::prim(
            Primitive::PjsFnMake(1),
            vec![Lambda::function_(
                1,
                vec![param],
                Lambda::const_(Constant::JsUndefined { is_unit: true }),
                FunctionAttribute {
                    return_unit: true,
                    ..FunctionAttribute::default()
                },
            )],
            Location::none(),
        )
    }

    #[test]
    fn nested_plain_int_return_switches_can_fall_through_like_gpr_1438() {
        let mut compiler = LambdaCompiler::new();
        let key = Ident::create_local("key");
        let a = Ident::create_local("a");
        let b = Ident::create_local("b");
        let c = Ident::create_local("c");
        let d = Ident::create_local("d");
        let e = Ident::create_local("e");
        let block = compiler.compile_return_block(&Lambda::LstaticCatch(
            Box::new(Lambda::LstaticCatch(
                Box::new(Lambda::Lswitch(
                    Box::new(Lambda::var(key.clone())),
                    LambdaSwitch {
                        sw_consts_full: false,
                        sw_consts: gpr_1438_switch_cases(&b, &c, &d, &e),
                        sw_blocks_full: true,
                        sw_blocks: vec![],
                        sw_failaction: Some(Box::new(Lambda::static_raise(2, Vec::new()))),
                        sw_names: None,
                    },
                )),
                (2, vec![]),
                Box::new(gpr_1438_fallthrough_handler()),
            )),
            (1, vec![]),
            Box::new(Lambda::var(a.clone())),
        ));

        let [switch_stmt, handler_return] = block.as_slice() else {
            panic!("expected a switch followed by the outer fallthrough handler");
        };
        let StatementDesc::IntSwitch(test, clauses, None) = &switch_stmt.desc else {
            panic!("expected the inner plain handler to stay outside the switch");
        };
        assert!(matches!(
            test,
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&key)
        ));
        assert_eq!(clauses.len(), 6);

        let rendered = print_block(&block);
        assert_eq!(
            rendered,
            "switch (key) {\n  case 98 :\n    return c;\n  case 106 :\n    return d;\n  case 107 :\n    return e;\n  case 116 :\n    return b;\n  case 99 :\n  case 118 :\n    return a;\n}\n\nreturn param => {};"
        );

        match &handler_return.desc {
            StatementDesc::Return(_) => {}
            other => panic!("expected the outer handler return, got {other:?}"),
        }
    }

    #[test]
    fn compile_deps_program_keeps_gpr_1438_fallthrough_return_outside_switch() {
        let mut compiler = LambdaCompiler::new();
        let action_key = Ident::create_local("actionKey");
        let key = Ident::create_local("key");
        let a = Ident::create_local("a");
        let b = Ident::create_local("b");
        let c = Ident::create_local("c");
        let d = Ident::create_local("d");
        let e = Ident::create_local("e");
        let function = Lambda::function_(
            6,
            vec![
                key.clone(),
                a.clone(),
                b.clone(),
                c.clone(),
                d.clone(),
                e.clone(),
            ],
            Lambda::LstaticCatch(
                Box::new(Lambda::LstaticCatch(
                    Box::new(Lambda::Lswitch(
                        Box::new(Lambda::var(key.clone())),
                        LambdaSwitch {
                            sw_consts_full: false,
                            sw_consts: gpr_1438_switch_cases(&b, &c, &d, &e),
                            sw_blocks_full: true,
                            sw_blocks: vec![],
                            sw_failaction: Some(Box::new(Lambda::static_raise(2, Vec::new()))),
                            sw_names: None,
                        },
                    )),
                    (2, vec![]),
                    Box::new(gpr_1438_fallthrough_handler()),
                )),
                (1, vec![]),
                Box::new(Lambda::var(a.clone())),
            ),
            FunctionAttribute::default(),
        );
        let lam = Lambda::let_(
            LetKind::Strict,
            action_key.clone(),
            Lambda::prim(Primitive::PjsFnMake(6), vec![function], Location::none()),
            Lambda::prim(
                Primitive::Pmakeblock(
                    0,
                    TagInfo::ModuleExport(vec![action_key.clone()]),
                    Mutable::Immutable,
                ),
                vec![Lambda::var(action_key.clone())],
                Location::none(),
            ),
        );

        let deps = compiler.compile_deps_program(&lam);
        let rendered = print_deps_program(&deps, None);
        assert_eq!(
            rendered,
            "// Generated by ReScript, PLEASE EDIT WITH CARE\n\n\nfunction actionKey(key, a, b, c, d, e) {\n  switch (key) {\n    case 98 :\n      return c;\n    case 106 :\n      return d;\n    case 107 :\n      return e;\n    case 116 :\n      return b;\n    case 99 :\n    case 118 :\n      return a;\n  }\n  return param => {};\n}\n\nexport {\n  actionKey,\n}\n/* No side effect */\n"
        );
    }

    #[test]
    fn nested_let_values_preserve_declaration_context_for_wrapped_string_switches() {
        let mut compiler = LambdaCompiler::new();
        let version = Ident::create_local("version");
        let match_id = Ident::create_local("match");
        let scrutinee = Ident::create_local("platform");
        let program = compiler.compile_program(&Lambda::Llet(
            LetKind::Strict,
            version.clone(),
            Box::new(Lambda::let_(
                LetKind::Strict,
                match_id.clone(),
                Lambda::var(scrutinee.clone()),
                Lambda::LstaticCatch(
                    Box::new(Lambda::LstringSwitch(
                        Box::new(Lambda::var(match_id.clone())),
                        vec![
                            ("linux".to_string(), Lambda::const_(Constant::int(1))),
                            ("darwin".to_string(), Lambda::const_(Constant::int(2))),
                        ],
                        Some(Box::new(Lambda::static_raise(1, Vec::new()))),
                    )),
                    (1, vec![]),
                    Box::new(Lambda::const_(Constant::int(3))),
                ),
            )),
            Box::new(Lambda::var(version.clone())),
        ));

        let [version_decl, switch_stmt] = program.block.as_slice() else {
            panic!(
                "expected simplification to inline the nested binding into a declaration and switch"
            );
        };

        let StatementDesc::Variable(VariableDeclaration {
            ident, value: None, ..
        }) = &version_decl.desc
        else {
            panic!("expected an uninitialized declaration for the outer binding");
        };
        assert!(ident.same(&version));

        let StatementDesc::StringSwitch(test, clauses, Some(default_block)) = &switch_stmt.desc
        else {
            panic!("expected the outer declaration context to reach the string switch");
        };
        assert!(matches!(
            test,
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&scrutinee)
        ));

        let expected_cases = [("linux", 1_i32), ("darwin", 2_i32)];
        for (clause, (expected_tag, expected_value)) in clauses.iter().zip(expected_cases) {
            assert_eq!(
                clause.tag_type,
                SwitchCaseTag::String(expected_tag.to_string())
            );
            assert_switch_case_assigns_int_result(&clause.clause.body, &version, expected_value);
        }
        assert_switch_default_assigns_int_result(default_block, &version, 3);
    }

    #[test]
    fn function_return_blocks_lower_switches_without_a_result_temp() {
        let mut compiler = LambdaCompiler::new();
        let scrutinee = Ident::create_local("scrutinee");
        let compiled = compiler.compile_expr(&Lambda::Lfunction(crate::lambda::LFunction {
            arity: 1,
            params: vec![scrutinee.clone()],
            body: Box::new(Lambda::Lswitch(
                Box::new(Lambda::var(scrutinee.clone())),
                LambdaSwitch {
                    sw_consts_full: true,
                    sw_consts: vec![
                        (0, Lambda::const_(Constant::int(1))),
                        (1, Lambda::const_(Constant::int(2))),
                    ],
                    sw_blocks_full: false,
                    sw_blocks: vec![],
                    sw_failaction: Some(Box::new(Lambda::const_(Constant::int(3)))),
                    sw_names: None,
                },
            )),
            attr: crate::lambda::FunctionAttribute::default(),
        }));

        let Expression {
            desc: ExpressionDesc::Fun { body, .. },
            ..
        } = compiled.expr
        else {
            panic!("expected a function expression");
        };

        let [switch_stmt] = body.as_slice() else {
            panic!("expected a single switch statement in the function body");
        };
        let StatementDesc::IntSwitch(test, clauses, Some(default_block)) = &switch_stmt.desc else {
            panic!("expected a direct integer switch in the function body");
        };
        assert!(matches!(
            test,
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&scrutinee)
        ));

        let expected_cases = [(0, 1_i32), (1, 2_i32)];
        for ((tag, clause), (expected_tag, expected_value)) in clauses.iter().zip(expected_cases) {
            assert_eq!(*tag, expected_tag);
            assert_switch_case_returns_int_result(&clause.body, expected_value);
        }
        assert_switch_default_returns_int_result(default_block, 3);
    }

    #[test]
    fn function_return_blocks_lower_ifs_without_a_result_temp() {
        let mut compiler = LambdaCompiler::new();
        let cond = Ident::create_local("cond");
        let branch = Ident::create_local("branch");
        let compiled = compiler.compile_expr(&Lambda::Lfunction(crate::lambda::LFunction {
            arity: 1,
            params: vec![cond.clone()],
            body: Box::new(Lambda::LifThenElse(
                Box::new(Lambda::var(cond.clone())),
                Box::new(Lambda::let_(
                    LetKind::Strict,
                    branch.clone(),
                    Lambda::const_(Constant::int(1)),
                    Lambda::var(branch.clone()),
                )),
                Box::new(Lambda::const_(Constant::int(0))),
            )),
            attr: crate::lambda::FunctionAttribute::default(),
        }));

        let Expression {
            desc: ExpressionDesc::Fun { body, .. },
            ..
        } = compiled.expr
        else {
            panic!("expected a function expression");
        };

        match body.as_slice() {
            [if_stmt] => {
                let (test, then_block, else_block) = match &if_stmt.desc {
                    StatementDesc::If(test, then_block, else_block) => {
                        (test, then_block, else_block)
                    }
                    StatementDesc::Block(inner) => {
                        match inner.as_slice() {
                            [inner_if] => {
                                let StatementDesc::If(test, then_block, else_block) =
                                    &inner_if.desc
                                else {
                                    panic!("expected the wrapper block to contain an if");
                                };
                                (test, then_block, else_block)
                            }
                            [guard_stmt, branch_decl, branch_return] => {
                                let (test, then_block, else_block) = match &guard_stmt.desc {
                                    StatementDesc::If(test, then_block, else_block) => {
                                        (test, then_block, else_block)
                                    }
                                    other => panic!("expected a guard if, got {other:?}"),
                                };
                                assert!(matches!(
                                    test,
                                    Expression {
                                        desc: ExpressionDesc::JsNot(inner),
                                        ..
                                    } if matches!(
                                        &inner.desc,
                                        ExpressionDesc::Var(crate::js_ir::VIdent::Id(id))
                                            if id.same(&cond)
                                    )
                                ));
                                assert!(else_block.is_empty());
                                assert_switch_case_returns_int_result(then_block, 0);

                                let StatementDesc::Variable(VariableDeclaration {
                                    ident,
                                    value:
                                        Some(Expression {
                                            desc: ExpressionDesc::Number(Number::Int { i: 1, .. }),
                                            ..
                                        }),
                                    ..
                                }) = &branch_decl.desc
                                else {
                                    panic!("expected the then-branch declaration");
                                };
                                assert!(ident.same(&branch));
                                assert!(matches!(
                                    branch_return,
                                    Statement {
                                        desc: StatementDesc::Return(Expression {
                                            desc: ExpressionDesc::Var(
                                                crate::js_ir::VIdent::Id(id)
                                            ),
                                            ..
                                        }),
                                        ..
                                    } if id.same(&branch)
                                ));
                                return;
                            }
                            _ => panic!("expected a single wrapped if statement"),
                        }
                    }
                    other => panic!("expected direct return-position if lowering, got {other:?}"),
                };
                assert!(matches!(
                    test,
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&cond)
                ));

                let [branch_decl, branch_return] = then_block.as_slice() else {
                    panic!("expected the let-binding branch to stay inline in the then block");
                };
                let StatementDesc::Variable(VariableDeclaration {
                    ident,
                    value:
                        Some(Expression {
                            desc: ExpressionDesc::Number(Number::Int { i: 1, .. }),
                            ..
                        }),
                    ..
                }) = &branch_decl.desc
                else {
                    panic!("expected the then branch local declaration");
                };
                assert!(ident.same(&branch));
                assert!(matches!(
                    branch_return,
                    Statement {
                        desc: StatementDesc::Return(Expression {
                            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                            ..
                        }),
                        ..
                    } if id.same(&branch)
                ));

                let [else_return] = else_block.as_slice() else {
                    panic!("expected a single return in the else branch");
                };
                assert!(matches!(
                    else_return,
                    Statement {
                        desc: StatementDesc::Return(Expression {
                            desc: ExpressionDesc::Number(Number::Int { i: 0, .. }),
                            ..
                        }),
                        ..
                    }
                ));
            }
            [guard_stmt, branch_decl, branch_return] => {
                let (test, then_block, else_block) = match &guard_stmt.desc {
                    StatementDesc::If(test, then_block, else_block) => {
                        (test, then_block, else_block)
                    }
                    StatementDesc::Block(inner) => {
                        let [inner_if] = inner.as_slice() else {
                            panic!("expected a single guard if inside the wrapper block");
                        };
                        let StatementDesc::If(test, then_block, else_block) = &inner_if.desc
                        else {
                            panic!("expected the wrapper block to contain an if");
                        };
                        (test, then_block, else_block)
                    }
                    other => panic!("expected a guard if, got {other:?}"),
                };
                assert!(matches!(
                    test,
                    Expression {
                        desc: ExpressionDesc::JsNot(inner),
                        ..
                    } if matches!(
                        &inner.desc,
                        ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)) if id.same(&cond)
                    )
                ));
                assert!(else_block.is_empty());
                assert_switch_case_returns_int_result(then_block, 0);

                let StatementDesc::Variable(VariableDeclaration {
                    ident,
                    value:
                        Some(Expression {
                            desc: ExpressionDesc::Number(Number::Int { i: 1, .. }),
                            ..
                        }),
                    ..
                }) = &branch_decl.desc
                else {
                    panic!("expected the then-branch declaration");
                };
                assert!(ident.same(&branch));
                assert!(matches!(
                    branch_return,
                    Statement {
                        desc: StatementDesc::Return(Expression {
                            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                            ..
                        }),
                        ..
                    } if id.same(&branch)
                ));
            }
            _ => panic!("expected either a direct if or a guard-fallthrough lowering"),
        }
    }

    #[test]
    fn function_return_blocks_lower_effectful_sequands_without_a_result_temp() {
        let mut compiler = LambdaCompiler::new();
        let cond = Ident::create_local("cond");
        let branch = Ident::create_local("branch");
        let compiled = compiler.compile_expr(&Lambda::Lfunction(crate::lambda::LFunction {
            arity: 1,
            params: vec![cond.clone()],
            body: Box::new(Lambda::prim(
                Primitive::Psequand,
                vec![
                    Lambda::var(cond.clone()),
                    Lambda::let_(
                        LetKind::Strict,
                        branch.clone(),
                        Lambda::const_(Constant::int(1)),
                        Lambda::var(branch.clone()),
                    ),
                ],
                Location::none(),
            )),
            attr: crate::lambda::FunctionAttribute::default(),
        }));

        let Expression {
            desc: ExpressionDesc::Fun { body, .. },
            ..
        } = compiled.expr
        else {
            panic!("expected a function expression");
        };

        let [stmt] = body.as_slice() else {
            panic!("expected a single short-circuit lowering statement");
        };
        match &stmt.desc {
            StatementDesc::If(test, then_block, else_block) => {
                assert!(matches!(
                    test,
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&cond)
                ));

                let [branch_decl, branch_return] = then_block.as_slice() else {
                    panic!("expected the right-hand branch declaration and return");
                };
                let StatementDesc::Variable(VariableDeclaration {
                    ident,
                    value:
                        Some(Expression {
                            desc: ExpressionDesc::Number(Number::Int { i: 1, .. }),
                            ..
                        }),
                    ..
                }) = &branch_decl.desc
                else {
                    panic!("expected the right-hand branch local declaration");
                };
                assert!(ident.same(&branch));
                assert!(matches!(
                    branch_return,
                    Statement {
                        desc: StatementDesc::Return(Expression {
                            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                            ..
                        }),
                        ..
                    } if id.same(&branch)
                ));

                let [else_return] = else_block.as_slice() else {
                    panic!("expected a single false return in the else branch");
                };
                assert!(matches!(
                    else_return,
                    Statement {
                        desc: StatementDesc::Return(Expression {
                            desc: ExpressionDesc::Bool(false),
                            ..
                        }),
                        ..
                    }
                ));
            }
            StatementDesc::Block(block) => {
                let [guard_if, branch_decl, branch_return] = block.as_slice() else {
                    panic!("expected a guarded false-return plus the right-hand branch");
                };
                let StatementDesc::If(test, then_block, else_block) = &guard_if.desc else {
                    panic!("expected the short-circuit false-return guard");
                };
                assert!(matches!(
                    test,
                    Expression {
                        desc: ExpressionDesc::JsNot(inner),
                        ..
                    } if matches!(
                        &inner.desc,
                        ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)) if id.same(&cond)
                    )
                ));
                assert!(else_block.is_empty());
                let [guard_return] = then_block.as_slice() else {
                    panic!("expected the false-return guard body");
                };
                assert!(matches!(
                    guard_return,
                    Statement {
                        desc: StatementDesc::Return(Expression {
                            desc: ExpressionDesc::Bool(false),
                            ..
                        }),
                        ..
                    }
                ));

                let StatementDesc::Variable(VariableDeclaration {
                    ident,
                    value:
                        Some(Expression {
                            desc: ExpressionDesc::Number(Number::Int { i: 1, .. }),
                            ..
                        }),
                    ..
                }) = &branch_decl.desc
                else {
                    panic!("expected the right-hand branch local declaration");
                };
                assert!(ident.same(&branch));
                assert!(matches!(
                    branch_return,
                    Statement {
                        desc: StatementDesc::Return(Expression {
                            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                            ..
                        }),
                        ..
                    } if id.same(&branch)
                ));
            }
            _ => panic!("expected direct return-position short-circuit lowering"),
        }
    }

    #[test]
    fn let_bindings_lower_ifs_without_a_result_temp() {
        let mut compiler = LambdaCompiler::new();
        let cond = Ident::create_local("cond");
        let result = Ident::create_local("result");
        let branch = Ident::create_local("branch");
        let compiled = compiler.compile_expr(&Lambda::Llet(
            LetKind::Strict,
            result.clone(),
            Box::new(Lambda::LifThenElse(
                Box::new(Lambda::var(cond.clone())),
                Box::new(Lambda::let_(
                    LetKind::Strict,
                    branch.clone(),
                    Lambda::const_(Constant::int(1)),
                    Lambda::var(branch.clone()),
                )),
                Box::new(Lambda::const_(Constant::int(0))),
            )),
            Box::new(Lambda::var(result.clone())),
        ));

        let [result_decl, if_stmt] = compiled.prelude.as_slice() else {
            panic!("expected a declaration followed by direct if assignment");
        };
        let StatementDesc::Variable(VariableDeclaration {
            ident, value: None, ..
        }) = &result_decl.desc
        else {
            panic!("expected an uninitialized declaration for the let-bound result");
        };
        assert!(ident.same(&result));

        let StatementDesc::If(test, then_block, else_block) = &if_stmt.desc else {
            panic!("expected the let-bound if to lower directly into branch assignments");
        };
        assert!(matches!(
            test,
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&cond)
        ));

        let [branch_decl, branch_assign] = then_block.as_slice() else {
            panic!("expected the then branch declaration and assignment");
        };
        let StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Number(Number::Int { i: 1, .. }),
                    ..
                }),
            ..
        }) = &branch_decl.desc
        else {
            panic!("expected the then branch local declaration");
        };
        assert!(ident.same(&branch));
        assert!(matches!(
            branch_assign,
            Statement {
                desc: StatementDesc::Exp(Expression {
                    desc: ExpressionDesc::Bin(
                        BinOp::Eq,
                        lhs,
                        rhs
                    ),
                    ..
                }),
                ..
            } if matches!(
                (&lhs.desc, &rhs.desc),
                (
                    ExpressionDesc::Var(crate::js_ir::VIdent::Id(lhs_id)),
                    ExpressionDesc::Var(crate::js_ir::VIdent::Id(rhs_id))
                ) if lhs_id.same(&result) && rhs_id.same(&branch)
            )
        ));

        let [else_assign] = else_block.as_slice() else {
            panic!("expected a single assignment in the else branch");
        };
        assert!(matches!(
            else_assign,
            Statement {
                desc: StatementDesc::Exp(Expression {
                    desc: ExpressionDesc::Bin(
                        BinOp::Eq,
                        lhs,
                        rhs
                    ),
                    ..
                }),
                ..
            } if matches!(
                (&lhs.desc, &rhs.desc),
                (
                    ExpressionDesc::Var(crate::js_ir::VIdent::Id(lhs_id)),
                    ExpressionDesc::Number(Number::Int { i: 0, .. })
                ) if lhs_id.same(&result)
            )
        ));
    }

    #[test]
    fn let_bindings_merge_direct_if_assignments_into_initialized_declarations() {
        let mut compiler = LambdaCompiler::new();
        let cond = Ident::create_local("cond");
        let result = Ident::create_local("result");
        let compiled = compiler.compile_expr(&Lambda::Llet(
            LetKind::Strict,
            result.clone(),
            Box::new(Lambda::LifThenElse(
                Box::new(Lambda::var(cond.clone())),
                Box::new(Lambda::const_(Constant::int(1))),
                Box::new(Lambda::const_(Constant::int(0))),
            )),
            Box::new(Lambda::var(result.clone())),
        ));

        let [result_decl] = compiled.prelude.as_slice() else {
            panic!("expected the let-bound if to collapse into one initialized declaration");
        };
        let StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Cond(test, then_expr, else_expr),
                    ..
                }),
            ..
        }) = &result_decl.desc
        else {
            panic!("expected a single initialized declaration for the let-bound result");
        };
        assert!(ident.same(&result));
        assert!(matches!(
            test.as_ref(),
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&cond)
        ));
        assert!(matches!(
            then_expr.as_ref(),
            Expression {
                desc: ExpressionDesc::Number(Number::Int { i: 1, .. }),
                ..
            }
        ));
        assert!(matches!(
            else_expr.as_ref(),
            Expression {
                desc: ExpressionDesc::Number(Number::Int { i: 0, .. }),
                ..
            }
        ));
    }

    #[test]
    fn effect_blocks_lower_ifs_without_a_result_temp() {
        let mut compiler = LambdaCompiler::new();
        let cond = Ident::create_local("cond");
        let slot = Ident::create_local("slot");
        let block = compiler.compile_effect_block(&Lambda::LifThenElse(
            Box::new(Lambda::var(cond.clone())),
            Box::new(Lambda::Lsequence(
                Box::new(Lambda::Lassign(
                    slot.clone(),
                    Box::new(Lambda::const_(Constant::int(1))),
                )),
                Box::new(Lambda::const_(Constant::int(42))),
            )),
            Box::new(Lambda::const_(Constant::int(0))),
        ));

        let [if_stmt] = block.as_slice() else {
            panic!("expected a single direct if statement in effect context");
        };
        let StatementDesc::If(test, then_block, else_block) = &if_stmt.desc else {
            panic!("expected effect-position if lowering");
        };
        assert!(matches!(
            test,
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&cond)
        ));
        assert!(else_block.is_empty());

        let [assign_stmt] = then_block.as_slice() else {
            panic!("expected the pure branch value to be dropped");
        };
        assert!(matches!(
            assign_stmt,
            Statement {
                desc: StatementDesc::Exp(Expression {
                    desc: ExpressionDesc::Bin(
                        BinOp::Eq,
                        lhs,
                        rhs
                    ),
                    ..
                }),
                ..
            } if matches!(
                (&lhs.desc, &rhs.desc),
                (
                    ExpressionDesc::Var(crate::js_ir::VIdent::Id(lhs_id)),
                    ExpressionDesc::Number(Number::Int { i: 1, .. })
                ) if lhs_id.same(&slot)
            )
        ));
    }

    #[test]
    fn effect_blocks_keep_conditional_expressions_when_both_branches_are_effectful() {
        let mut compiler = LambdaCompiler::new();
        let cond = Ident::create_local("cond");
        let lhs = Ident::create_local("lhs");
        let rhs = Ident::create_local("rhs");
        let block = compiler.compile_effect_block(&Lambda::LifThenElse(
            Box::new(Lambda::var(cond.clone())),
            Box::new(Lambda::Lassign(
                lhs.clone(),
                Box::new(Lambda::const_(Constant::int(1))),
            )),
            Box::new(Lambda::Lassign(
                rhs.clone(),
                Box::new(Lambda::const_(Constant::int(2))),
            )),
        ));

        let [stmt] = block.as_slice() else {
            panic!("expected a single expression statement");
        };
        let StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Cond(test, then_expr, else_expr),
            ..
        }) = &stmt.desc
        else {
            panic!("expected an effectful conditional expression");
        };
        assert!(matches!(
            test.as_ref(),
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&cond)
        ));
        assert!(matches!(
            (&then_expr.desc, &else_expr.desc),
            (
                ExpressionDesc::Bin(
                    BinOp::Eq,
                    then_lhs,
                    then_rhs
                ),
                ExpressionDesc::Bin(
                    BinOp::Eq,
                    else_lhs,
                    else_rhs
                )
            ) if matches!(
                (&then_lhs.desc, &then_rhs.desc),
                (
                    ExpressionDesc::Var(crate::js_ir::VIdent::Id(lhs_id)),
                    ExpressionDesc::Number(Number::Int { i: 1, .. })
                ) if lhs_id.same(&lhs)
            ) && matches!(
                (&else_lhs.desc, &else_rhs.desc),
                (
                    ExpressionDesc::Var(crate::js_ir::VIdent::Id(rhs_id)),
                    ExpressionDesc::Number(Number::Int { i: 2, .. })
                ) if rhs_id.same(&rhs)
            )
        ));
    }

    #[test]
    fn sequence_prefix_ifs_use_effect_lowering_without_result_temps() {
        let mut compiler = LambdaCompiler::new();
        let cond = Ident::create_local("cond");
        let value = Ident::create_local("value");
        let compiled = compiler.compile_expr(&Lambda::Lsequence(
            Box::new(Lambda::LifThenElse(
                Box::new(Lambda::var(cond.clone())),
                Box::new(Lambda::const_(Constant::int(0))),
                Box::new(Lambda::LstaticRaise(
                    1,
                    vec![Lambda::const_(Constant::string("boom"))],
                )),
            )),
            Box::new(Lambda::var(value.clone())),
        ));

        assert!(
            compiled
                .prelude
                .iter()
                .all(|stmt| !matches!(stmt.desc, StatementDesc::Variable(_))),
            "effect-lowered sequence prefixes should not allocate result temps"
        );

        let [if_stmt] = compiled.prelude.as_slice() else {
            panic!("expected a single effect-position if prelude");
        };
        let StatementDesc::If(_, then_block, else_block) = &if_stmt.desc else {
            panic!("expected an effect-lowered if statement");
        };
        assert!(
            matches!(
                then_block.as_slice(),
                [Statement {
                    desc: StatementDesc::Throw(_),
                    ..
                }]
            ) || matches!(
                else_block.as_slice(),
                [Statement {
                    desc: StatementDesc::Throw(_),
                    ..
                }]
            ),
            "expected the lowered branch to throw directly"
        );
        assert!(matches!(
            compiled.expr,
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&value)
        ));
    }

    #[test]
    fn if_value_branches_keep_assignment_continuation_through_let_bindings() {
        let mut compiler = LambdaCompiler::new();
        let outer_cond = Ident::create_local("outerCond");
        let inner_cond = Ident::create_local("innerCond");
        let alias = Ident::create_local("alias");
        let compiled = compiler.compile_expr(&Lambda::LifThenElse(
            Box::new(Lambda::var(outer_cond.clone())),
            Box::new(Lambda::Llet(
                LetKind::Strict,
                alias.clone(),
                Box::new(Lambda::const_(Constant::int(1))),
                Box::new(Lambda::LifThenElse(
                    Box::new(Lambda::var(inner_cond.clone())),
                    Box::new(Lambda::const_(Constant::int(2))),
                    Box::new(Lambda::const_(Constant::int(3))),
                )),
            )),
            Box::new(Lambda::const_(Constant::int(4))),
        ));

        let [result_decl, if_stmt] = compiled.prelude.as_slice() else {
            panic!("expected a temp declaration and one if statement");
        };

        let result = match &result_decl.desc {
            StatementDesc::Variable(VariableDeclaration { ident, .. }) => ident.clone(),
            _ => panic!("expected a result temp declaration"),
        };
        assert_eq!(result.name(), "tmp");
        let StatementDesc::If(_, then_block, else_block) = &if_stmt.desc else {
            panic!("expected an if statement");
        };

        let [alias_decl, then_assign] = then_block.as_slice() else {
            panic!("expected the then branch to bind the alias then assign");
        };
        assert!(matches!(
            alias_decl,
            Statement {
                desc: StatementDesc::Variable(VariableDeclaration { ident, .. }),
                ..
            } if ident.same(&alias)
        ));
        assert!(matches!(
            then_assign,
            Statement {
                desc: StatementDesc::Exp(Expression {
                    desc: ExpressionDesc::Bin(
                        BinOp::Eq,
                        lhs,
                        rhs
                    ),
                    ..
                }),
                ..
            } if matches!(
                (&lhs.desc, &rhs.desc),
                (
                    ExpressionDesc::Var(crate::js_ir::VIdent::Id(lhs_id)),
                    ExpressionDesc::Cond(test, consequent, alternate)
                ) if lhs_id.same(&result)
                    && matches!(
                        test.as_ref(),
                        Expression {
                            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(test_id)),
                            ..
                        } if test_id.same(&inner_cond)
                    )
                    && matches!(consequent.desc, ExpressionDesc::Number(Number::Int { i: 2, .. }))
                    && matches!(alternate.desc, ExpressionDesc::Number(Number::Int { i: 3, .. }))
            )
        ));
        assert!(matches!(
            else_block.as_slice(),
            [Statement {
                desc: StatementDesc::Exp(Expression {
                    desc: ExpressionDesc::Bin(
                        BinOp::Eq,
                        lhs,
                        rhs
                    ),
                    ..
                }),
                ..
            }] if matches!(
                (&lhs.desc, &rhs.desc),
                (
                    ExpressionDesc::Var(crate::js_ir::VIdent::Id(lhs_id)),
                    ExpressionDesc::Number(Number::Int { i: 4, .. })
                ) if lhs_id.same(&result)
            )
        ));
        assert!(matches!(
            compiled.expr,
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&result)
        ));
    }

    #[test]
    fn named_variant_switch_expressions_split_const_and_block_dispatch() {
        let mut compiler = LambdaCompiler::new();
        let scrutinee = Ident::create_local("scrutinee");
        let compiled = compiler.compile_expr(&Lambda::Lswitch(
            Box::new(Lambda::var(scrutinee.clone())),
            LambdaSwitch {
                sw_consts_full: false,
                sw_consts: vec![(0, Lambda::const_(Constant::int(1)))],
                sw_blocks_full: false,
                sw_blocks: vec![(0, Lambda::const_(Constant::int(2)))],
                sw_failaction: Some(Box::new(Lambda::const_(Constant::int(3)))),
                sw_names: Some(SwitchNames {
                    consts: vec![crate::lambda::SwitchTag::named("A")],
                    blocks: vec![crate::lambda::SwitchBlock::named("B")],
                }),
            },
        ));

        let [declare, dispatch] = compiled.prelude.as_slice() else {
            panic!("expected a declaration followed by a named-variant dispatch");
        };
        let StatementDesc::Variable(VariableDeclaration { ident: result, .. }) = &declare.desc
        else {
            panic!("expected the named-variant result declaration");
        };
        let StatementDesc::If(cond, then_block, else_block) = &dispatch.desc else {
            panic!("expected an object split before the named switch");
        };

        assert_typeof_object_check(cond, &scrutinee, false);

        let [const_switch] = then_block.as_slice() else {
            panic!("expected a const-variant switch in the non-object branch");
        };
        let StatementDesc::StringSwitch(test, const_clauses, Some(const_default)) =
            &const_switch.desc
        else {
            panic!("expected a string switch for const constructors");
        };
        assert!(matches!(
            test,
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&scrutinee)
        ));
        assert_eq!(const_clauses.len(), 1);
        assert_eq!(
            const_clauses[0].tag_type,
            SwitchCaseTag::String("A".to_string())
        );
        assert_switch_case_assigns_int_result(&const_clauses[0].clause.body, result, 1);
        assert_switch_default_assigns_int_result(const_default, result, 3);

        let [block_switch] = else_block.as_slice() else {
            panic!("expected a payload-variant switch in the object branch");
        };
        let StatementDesc::StringSwitch(test, block_clauses, Some(block_default)) =
            &block_switch.desc
        else {
            panic!("expected a string switch for payload constructors");
        };
        assert_tag_field_access(test, &scrutinee);
        assert_eq!(block_clauses.len(), 1);
        assert_eq!(
            block_clauses[0].tag_type,
            SwitchCaseTag::String("B".to_string())
        );
        assert_switch_case_assigns_int_result(&block_clauses[0].clause.body, result, 2);
        assert_switch_default_assigns_int_result(block_default, result, 3);
    }

    #[test]
    fn named_variant_constant_return_switch_skips_redundant_match_temp() {
        let mut compiler = LambdaCompiler::new();
        let block = compiler.compile_return_block(&Lambda::Lswitch(
            Box::new(Lambda::const_(Constant::int(2))),
            LambdaSwitch {
                sw_consts_full: true,
                sw_consts: vec![
                    (0, Lambda::const_(Constant::string("a"))),
                    (1, Lambda::const_(Constant::string("b"))),
                ],
                sw_blocks_full: true,
                sw_blocks: vec![],
                sw_failaction: None,
                sw_names: Some(SwitchNames {
                    consts: vec![
                        crate::lambda::SwitchTag {
                            name: "A".to_string(),
                            tag_type: Some(SwitchCaseTag::Int(0)),
                        },
                        crate::lambda::SwitchTag {
                            name: "B".to_string(),
                            tag_type: Some(SwitchCaseTag::Int(2)),
                        },
                    ],
                    blocks: vec![],
                }),
            },
        ));

        let [stmt] = block.as_slice() else {
            panic!("expected a single simplified return statement");
        };
        match &stmt.desc {
            StatementDesc::Return(Expression {
                desc: ExpressionDesc::Str { txt, .. },
                ..
            }) => assert_eq!(txt, "b"),
            StatementDesc::Block(inner) => {
                let [inner_stmt] = inner.as_slice() else {
                    panic!("expected the simplified block to contain one return");
                };
                assert!(matches!(
                    &inner_stmt.desc,
                    StatementDesc::Return(Expression {
                        desc: ExpressionDesc::Str { txt, .. },
                        ..
                    }) if txt == "b"
                ));
            }
            other => panic!("expected the switch to collapse to the taken branch, got {other:?}"),
        }
    }

    #[test]
    fn named_variant_effect_switches_keep_payload_cases() {
        let mut compiler = LambdaCompiler::new();
        let action = Ident::create_local("action");
        let captured = Ident::create_local("captured");
        let block = compiler.compile_effect_block(&Lambda::Lswitch(
            Box::new(Lambda::var(action.clone())),
            LambdaSwitch {
                sw_consts_full: false,
                sw_consts: vec![(0, Lambda::unit())],
                sw_blocks_full: false,
                sw_blocks: vec![(
                    0,
                    Lambda::Lassign(captured.clone(), Box::new(Lambda::const_(Constant::int(1)))),
                )],
                sw_failaction: Some(Box::new(Lambda::unit())),
                sw_names: Some(SwitchNames {
                    consts: vec![crate::lambda::SwitchTag::named("WithoutPayload")],
                    blocks: vec![crate::lambda::SwitchBlock::named("WithPayload")],
                }),
            },
        ));

        let rendered = print_block(&block);
        assert!(
            rendered.contains("if (typeof action === \"object\" && action.TAG === \"WithPayload\") {"),
            "expected the payload-effect switch to stay guarded by the object/tag check:\n{rendered}"
        );
        assert!(
            rendered.contains("captured = 1;"),
            "expected the payload-effect branch to keep the assignment:\n{rendered}"
        );
    }

    #[test]
    fn named_variant_return_switches_with_only_payload_cases_skip_object_split() {
        let mut compiler = LambdaCompiler::new();
        let action = Ident::create_local("action");
        let block = compiler.compile_return_block(&Lambda::Lswitch(
            Box::new(Lambda::var(action.clone())),
            LambdaSwitch {
                sw_consts_full: true,
                sw_consts: vec![],
                sw_blocks_full: true,
                sw_blocks: vec![
                    (0, Lambda::const_(Constant::int(1))),
                    (1, Lambda::const_(Constant::int(2))),
                ],
                sw_failaction: None,
                sw_names: Some(SwitchNames {
                    consts: vec![],
                    blocks: vec![
                        crate::lambda::SwitchBlock::named("Ok"),
                        crate::lambda::SwitchBlock::named("Error"),
                    ],
                }),
            },
        ));

        let rendered = print_block(&block);
        assert!(
            rendered.contains("return action.TAG === \"Ok\" ? 1 : 2;"),
            "expected the all-payload switch to lower directly over TAG without an object split:\n{rendered}"
        );
    }

    #[test]
    fn named_variant_incomplete_payload_only_return_switches_keep_default_as_negated_guard() {
        let mut compiler = LambdaCompiler::new();
        let action = Ident::create_local("action");
        let block = compiler.compile_return_block(&Lambda::Lswitch(
            Box::new(Lambda::var(action.clone())),
            LambdaSwitch {
                sw_consts_full: false,
                sw_consts: vec![],
                sw_blocks_full: false,
                sw_blocks: vec![(1, Lambda::const_(Constant::int(7)))],
                sw_failaction: Some(Box::new(Lambda::const_(Constant::int(42)))),
                sw_names: Some(SwitchNames {
                    consts: vec![
                        crate::lambda::SwitchTag::named("A1"),
                        crate::lambda::SwitchTag::named("A2"),
                    ],
                    blocks: vec![
                        crate::lambda::SwitchBlock::named("B"),
                        crate::lambda::SwitchBlock::named("C"),
                        crate::lambda::SwitchBlock::named("D"),
                    ],
                }),
            },
        ));

        let rendered = print_block(&block);
        assert!(
            rendered.contains("return typeof action !== \"object\" || action.TAG !== \"C\" ? 42 : 7;"),
            "expected the incomplete payload-only dispatch to keep OCaml's negated default guard:\n{rendered}"
        );
    }

    #[test]
    fn named_variant_incomplete_const_only_return_switches_keep_literal_guard() {
        let mut compiler = LambdaCompiler::new();
        let action = Ident::create_local("action");
        let block = compiler.compile_return_block(&Lambda::Lswitch(
            Box::new(Lambda::var(action.clone())),
            LambdaSwitch {
                sw_consts_full: false,
                sw_consts: vec![(0, Lambda::const_(Constant::int(1)))],
                sw_blocks_full: false,
                sw_blocks: vec![],
                sw_failaction: Some(Box::new(Lambda::const_(Constant::int(42)))),
                sw_names: Some(SwitchNames {
                    consts: vec![
                        crate::lambda::SwitchTag::named("A1"),
                        crate::lambda::SwitchTag::named("A2"),
                    ],
                    blocks: vec![crate::lambda::SwitchBlock::named("C")],
                }),
            },
        ));

        let rendered = print_block(&block);
        assert!(
            rendered.contains("return typeof action !== \"object\" && action === \"A1\" ? 1 : 42;"),
            "expected the incomplete const-only dispatch to keep the literal-side guard:\n{rendered}"
        );
    }

    #[test]
    fn named_variant_return_switches_keep_shared_final_groups_inside_the_switch_without_exits() {
        let mut compiler = LambdaCompiler::new();
        let action = Ident::create_local("action");
        let block = compiler.compile_return_block(&Lambda::Lswitch(
            Box::new(Lambda::var(action.clone())),
            LambdaSwitch {
                sw_consts_full: true,
                sw_consts: vec![],
                sw_blocks_full: true,
                sw_blocks: vec![
                    (0, Lambda::const_(Constant::int(1))),
                    (1, Lambda::const_(Constant::int(2))),
                    (2, Lambda::const_(Constant::int(2))),
                ],
                sw_failaction: None,
                sw_names: Some(SwitchNames {
                    consts: vec![],
                    blocks: vec![
                        crate::lambda::SwitchBlock::named("A"),
                        crate::lambda::SwitchBlock::named("B"),
                        crate::lambda::SwitchBlock::named("C"),
                    ],
                }),
            },
        ));

        let [switch_stmt] = block.as_slice() else {
            panic!("expected a single payload tag switch");
        };
        let StatementDesc::StringSwitch(test, clauses, None) = &switch_stmt.desc else {
            panic!("expected a direct payload tag switch without a default arm");
        };
        assert_tag_field_access(test, &action);
        assert_eq!(clauses.len(), 3);
        assert_eq!(clauses[0].tag_type, SwitchCaseTag::String("A".to_string()));
        assert_switch_case_returns_int_result(&clauses[0].clause.body, 1);
        assert_eq!(clauses[1].tag_type, SwitchCaseTag::String("B".to_string()));
        assert!(
            clauses[1].clause.body.is_empty(),
            "expected the first shared case to keep falling through"
        );
        assert!(!clauses[1].clause.should_break);
        assert_eq!(clauses[2].tag_type, SwitchCaseTag::String("C".to_string()));
        assert_switch_case_returns_int_result(&clauses[2].clause.body, 2);
        assert!(
            !clauses[2].clause.should_break,
            "plain shared return groups should stay in the switch without an exit-driven break"
        );
    }

    #[test]
    fn named_variant_return_switches_inline_resolved_static_handler_values_inside_the_switch() {
        let mut compiler = LambdaCompiler::new();
        let action = Ident::create_local("action");
        let block = compiler.compile_return_block(&Lambda::LstaticCatch(
            Box::new(Lambda::Lswitch(
                Box::new(Lambda::var(action.clone())),
                LambdaSwitch {
                    sw_consts_full: true,
                    sw_consts: vec![
                        (0, Lambda::const_(Constant::int(1))),
                        (1, Lambda::static_raise(7, Vec::new())),
                        (2, Lambda::static_raise(7, Vec::new())),
                    ],
                    sw_blocks_full: true,
                    sw_blocks: vec![],
                    sw_failaction: None,
                    sw_names: Some(SwitchNames {
                        consts: vec![
                            crate::lambda::SwitchTag::named("A"),
                            crate::lambda::SwitchTag::named("B"),
                            crate::lambda::SwitchTag::named("C"),
                        ],
                        blocks: vec![],
                    }),
                },
            )),
            (7, vec![]),
            Box::new(Lambda::const_(Constant::int(2))),
        ));

        let [switch_stmt] = block.as_slice() else {
            panic!("expected a single switch with the resolved handler inlined");
        };
        let StatementDesc::StringSwitch(test, clauses, None) = &switch_stmt.desc else {
            panic!("expected a named-constructor string switch without a trailing handler block");
        };
        assert!(matches!(
            test,
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&action)
        ));
        assert_eq!(clauses.len(), 3);
        assert_eq!(clauses[0].tag_type, SwitchCaseTag::String("A".to_string()));
        assert_switch_case_returns_int_result(&clauses[0].clause.body, 1);
        assert_eq!(clauses[1].tag_type, SwitchCaseTag::String("B".to_string()));
        assert!(clauses[1].clause.body.is_empty());
        assert!(!clauses[1].clause.should_break);
        assert_eq!(clauses[2].tag_type, SwitchCaseTag::String("C".to_string()));
        assert_switch_case_returns_int_result(&clauses[2].clause.body, 2);
        assert!(!clauses[2].clause.should_break);
    }

    #[test]
    fn nested_named_variant_return_switches_keep_complete_payload_handlers_inline() {
        let mut compiler = LambdaCompiler::new();
        let action = Ident::create_local("action");
        let block = compiler.compile_return_block(&Lambda::LstaticCatch(
            Box::new(Lambda::LstaticCatch(
                Box::new(Lambda::Lswitch(
                    Box::new(Lambda::var(action.clone())),
                    LambdaSwitch {
                        sw_consts_full: true,
                        sw_consts: vec![
                            (0, Lambda::const_(Constant::int(1))),
                            (1, Lambda::const_(Constant::int(3))),
                            (2, Lambda::const_(Constant::int(4))),
                        ],
                        sw_blocks_full: true,
                        sw_blocks: vec![
                            (0, Lambda::static_raise(18, Vec::new())),
                            (1, Lambda::static_raise(18, Vec::new())),
                            (2, Lambda::static_raise(19, Vec::new())),
                        ],
                        sw_failaction: None,
                        sw_names: Some(SwitchNames {
                            consts: vec![
                                crate::lambda::SwitchTag::named("A"),
                                crate::lambda::SwitchTag::named("B"),
                                crate::lambda::SwitchTag::named("F"),
                            ],
                            blocks: vec![
                                crate::lambda::SwitchBlock::named("C"),
                                crate::lambda::SwitchBlock::named("D"),
                                crate::lambda::SwitchBlock::named("E"),
                            ],
                        }),
                    },
                )),
                (19, vec![]),
                Box::new(Lambda::const_(Constant::int(2))),
            )),
            (18, vec![]),
            Box::new(Lambda::const_(Constant::int(1))),
        ));

        let [if_stmt] = block.as_slice() else {
            panic!("expected a single const/payload dispatch statement");
        };
        let StatementDesc::If(_, _, else_block) = &if_stmt.desc else {
            panic!("expected the named variant lowering to stay as an if dispatch");
        };
        let [switch_stmt] = else_block.as_slice() else {
            panic!("expected the payload branch to stay inside one switch");
        };
        let StatementDesc::StringSwitch(test, clauses, None) = &switch_stmt.desc else {
            panic!("expected the complete payload branch to compile without a default arm");
        };
        assert_tag_field_access(test, &action);
        assert_eq!(clauses.len(), 3);
        assert_eq!(clauses[0].tag_type, SwitchCaseTag::String("C".to_string()));
        assert!(clauses[0].clause.body.is_empty());
        assert_eq!(clauses[1].tag_type, SwitchCaseTag::String("D".to_string()));
        assert_switch_case_returns_int_result(&clauses[1].clause.body, 1);
        assert_eq!(clauses[2].tag_type, SwitchCaseTag::String("E".to_string()));
        assert_switch_case_returns_int_result(&clauses[2].clause.body, 2);
    }

    #[test]
    fn named_variant_return_switches_preserve_binding_temps_in_hoisted_shared_tails() {
        let mut compiler = LambdaCompiler::new();
        let action = Ident::create_local("action");
        let inner = Ident::create_local("inner");
        let carried = Ident::create_local("carried");
        let block = compiler.compile_return_block(&Lambda::LstaticCatch(
            Box::new(Lambda::LstaticCatch(
                Box::new(Lambda::Lswitch(
                    Box::new(Lambda::var(action.clone())),
                    LambdaSwitch {
                        sw_consts_full: true,
                        sw_consts: vec![
                            (0, Lambda::const_(Constant::int(1))),
                            (1, Lambda::static_raise(3, Vec::new())),
                            (2, Lambda::static_raise(3, Vec::new())),
                        ],
                        sw_blocks_full: true,
                        sw_blocks: vec![],
                        sw_failaction: None,
                        sw_names: Some(SwitchNames {
                            consts: vec![
                                crate::lambda::SwitchTag::named("A"),
                                crate::lambda::SwitchTag::named("B"),
                                crate::lambda::SwitchTag::named("C"),
                            ],
                            blocks: vec![],
                        }),
                    },
                )),
                (3, vec![]),
                Box::new(Lambda::let_(
                    LetKind::Strict,
                    inner.clone(),
                    Lambda::const_(Constant::int(5)),
                    Lambda::static_raise(2, vec![Lambda::var(inner.clone())]),
                )),
            )),
            (2, vec![carried.clone()]),
            Box::new(Lambda::prim(
                Primitive::Pmulint,
                vec![Lambda::var(carried.clone()), Lambda::var(carried.clone())],
                Location::none(),
            )),
        ));

        let rendered = print_block(&block);
        assert!(
            rendered.contains("case \"B\" :\n  case \"C\" :\n    break;"),
            "expected the grouped shared tail to stay after the switch:\n{rendered}"
        );
        assert!(
            rendered.contains("let carried = inner;"),
            "expected the outer staticcatch binding to stay materialized as a temp:\n{rendered}"
        );
        assert!(
            rendered.contains("return carried * carried | 0;"),
            "expected the hoisted tail to return through the bound temp:\n{rendered}"
        );
    }

    #[test]
    fn builtin_untagged_block_switch_expressions_dispatch_on_object_runtime_shape() {
        let mut compiler = LambdaCompiler::new();
        let value = Ident::create_local("value");
        let body_id = Ident::create_local("body");
        let compiled = compiler.compile_expr(&Lambda::Lswitch(
            Box::new(Lambda::var(value.clone())),
            LambdaSwitch {
                sw_consts_full: false,
                sw_consts: vec![],
                sw_blocks_full: false,
                sw_blocks: vec![(
                    0,
                    Lambda::let_(
                        LetKind::Strict,
                        body_id.clone(),
                        Lambda::const_(Constant::int(1)),
                        Lambda::var(body_id.clone()),
                    ),
                )],
                sw_failaction: Some(Box::new(Lambda::const_(Constant::int(0)))),
                sw_names: Some(SwitchNames {
                    consts: vec![],
                    blocks: vec![crate::lambda::SwitchBlock {
                        tag: crate::lambda::SwitchTag::named("Object"),
                        tag_name: None,
                        block_type: Some(crate::lambda::SwitchBlockType::Object),
                    }],
                }),
            },
        ));

        let [declare, dispatch] = compiled.prelude.as_slice() else {
            panic!("expected a result declaration followed by object dispatch");
        };
        let StatementDesc::Variable(VariableDeclaration { ident: result, .. }) = &declare.desc
        else {
            panic!("expected the switch result declaration");
        };
        let StatementDesc::If(cond, then_block, else_block) = &dispatch.desc else {
            panic!("expected an object runtime check around the block case");
        };

        assert_typeof_object_check(cond, &value, true);
        assert!(matches!(
            then_block.as_slice(),
            [
                Statement {
                    desc: StatementDesc::Variable(VariableDeclaration {
                        ident,
                        value: Some(Expression {
                            desc: ExpressionDesc::Number(Number::Int { i, .. }),
                            ..
                        }),
                        ..
                    }),
                    ..
                },
                Statement {
                    desc: StatementDesc::Exp(Expression {
                        desc: ExpressionDesc::Bin(BinOp::Eq, left, right),
                        ..
                    }),
                    ..
                }
            ] if ident.same(&body_id)
                && *i == 1
                && matches!(
                    left.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(result)
                )
                && matches!(
                    right.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&body_id)
                )
        ));
        assert_switch_default_assigns_int_result(else_block, result, 0);
    }

    #[test]
    fn builtin_untagged_object_switches_use_plain_object_check_after_array_split() {
        let mut compiler = LambdaCompiler::new();
        let value = Ident::create_local("value");
        let array_seen = Ident::create_local("array_seen");
        let object_seen = Ident::create_local("object_seen");
        let block = compiler.compile_effect_block(&Lambda::Lswitch(
            Box::new(Lambda::var(value.clone())),
            LambdaSwitch {
                sw_consts_full: false,
                sw_consts: vec![],
                sw_blocks_full: false,
                sw_blocks: vec![
                    (
                        0,
                        Lambda::Lassign(
                            array_seen.clone(),
                            Box::new(Lambda::const_(Constant::int(1))),
                        ),
                    ),
                    (
                        1,
                        Lambda::Lassign(
                            object_seen.clone(),
                            Box::new(Lambda::const_(Constant::int(2))),
                        ),
                    ),
                ],
                sw_failaction: Some(Box::new(Lambda::unit())),
                sw_names: Some(SwitchNames {
                    consts: vec![],
                    blocks: vec![
                        crate::lambda::SwitchBlock {
                            tag: crate::lambda::SwitchTag::named("Array"),
                            tag_name: None,
                            block_type: Some(crate::lambda::SwitchBlockType::Instance(
                                "Array".to_string(),
                            )),
                        },
                        crate::lambda::SwitchBlock {
                            tag: crate::lambda::SwitchTag::named("Object"),
                            tag_name: None,
                            block_type: Some(crate::lambda::SwitchBlockType::Object),
                        },
                    ],
                }),
            },
        ));

        let [dispatch] = block.as_slice() else {
            panic!("expected an array/object dispatch chain");
        };
        let StatementDesc::If(array_cond, _, else_block) = &dispatch.desc else {
            panic!("expected the array case to lower to a runtime if-check");
        };
        assert_array_is_array_call(array_cond, &value);

        let [object_dispatch] = else_block.as_slice() else {
            panic!("expected an object fallback after the array case");
        };
        let StatementDesc::If(object_cond, _, _) = &object_dispatch.desc else {
            panic!("expected the object fallback to be another runtime if-check");
        };
        assert_typeof_object_check(object_cond, &value, true);
    }

    #[test]
    fn object_and_array_untagged_return_switches_keep_object_inside_typeof_switch_like_ocaml() {
        let mut compiler = LambdaCompiler::new();
        let value = Ident::create_local("value");
        let block = compiler.compile_untagged_variant_switch_return_statements(
            Expression::var(value.clone()),
            &LambdaSwitch {
                sw_consts_full: true,
                sw_consts: vec![],
                sw_blocks_full: true,
                sw_blocks: vec![
                    (0, Lambda::const_(Constant::int(1))),
                    (1, Lambda::const_(Constant::int(2))),
                    (2, Lambda::const_(Constant::int(3))),
                    (3, Lambda::const_(Constant::int(4))),
                ],
                sw_failaction: None,
                sw_names: Some(SwitchNames {
                    consts: vec![],
                    blocks: vec![
                        crate::lambda::SwitchBlock {
                            tag: crate::lambda::SwitchTag::named("String"),
                            tag_name: None,
                            block_type: Some(crate::lambda::SwitchBlockType::String),
                        },
                        crate::lambda::SwitchBlock {
                            tag: crate::lambda::SwitchTag::named("Number"),
                            tag_name: None,
                            block_type: Some(crate::lambda::SwitchBlockType::Int),
                        },
                        crate::lambda::SwitchBlock {
                            tag: crate::lambda::SwitchTag::named("Object"),
                            tag_name: None,
                            block_type: Some(crate::lambda::SwitchBlockType::Object),
                        },
                        crate::lambda::SwitchBlock {
                            tag: crate::lambda::SwitchTag::named("Array"),
                            tag_name: None,
                            block_type: Some(crate::lambda::SwitchBlockType::Instance(
                                "Array".to_string(),
                            )),
                        },
                    ],
                }),
            },
        );
        let statements = match block.as_slice() {
            [Statement {
                desc: StatementDesc::Block(inner),
                ..
            }] => inner.as_slice(),
            other => other,
        };

        let [dispatch, typeof_switch] = statements else {
            panic!("expected an Array runtime split followed by a typeof switch");
        };
        let StatementDesc::If(array_cond, then_block, else_block) = &dispatch.desc else {
            panic!("expected the Array case to lower to a runtime if-check");
        };
        assert_array_is_array_call(array_cond, &value);
        assert_switch_case_returns_int_result(then_block, 4);
        assert!(else_block.is_empty());

        let StatementDesc::StringSwitch(test, clauses, None) = &typeof_switch.desc else {
            panic!("expected the remaining block cases to stay inside a typeof switch");
        };
        assert!(matches!(
            test,
            Expression {
                desc: ExpressionDesc::Typeof(inner),
                ..
            } if matches!(
                inner.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.same(&value)
            )
        ));
        assert_eq!(
            clauses
                .iter()
                .map(|clause| clause.tag_type.clone())
                .collect::<Vec<_>>(),
            vec![
                SwitchCaseTag::String("string".to_string()),
                SwitchCaseTag::String("number".to_string()),
                SwitchCaseTag::String("object".to_string()),
            ]
        );
        assert_switch_case_returns_int_result(&clauses[2].clause.body, 3);
    }

    #[test]
    fn small_untagged_object_value_switches_keep_ocaml_runtime_guards() {
        let mut compiler = LambdaCompiler::new();
        let value = Ident::create_local("value");
        let compiled = compiler.compile_expr(&Lambda::Lswitch(
            Box::new(Lambda::var(value.clone())),
            LambdaSwitch {
                sw_consts_full: false,
                sw_consts: vec![],
                sw_blocks_full: false,
                sw_blocks: vec![(0, Lambda::const_(Constant::int(1)))],
                sw_failaction: Some(Box::new(Lambda::const_(Constant::int(0)))),
                sw_names: Some(SwitchNames {
                    consts: vec![crate::lambda::SwitchTag {
                        name: "Null".to_string(),
                        tag_type: Some(crate::lambda::SwitchCaseTag::Null),
                    }],
                    blocks: vec![
                        crate::lambda::SwitchBlock {
                            tag: crate::lambda::SwitchTag::named("Object"),
                            tag_name: None,
                            block_type: Some(crate::lambda::SwitchBlockType::Object),
                        },
                        crate::lambda::SwitchBlock {
                            tag: crate::lambda::SwitchTag::named("Array"),
                            tag_name: None,
                            block_type: Some(crate::lambda::SwitchBlockType::Instance(
                                "Array".to_string(),
                            )),
                        },
                    ],
                }),
            },
        ));

        let rendered = print_block(&compiled.prelude);
        assert!(
            rendered.contains("typeof value === \"object\" && value !== null && !Array.isArray(value)"),
            "expected the small object switch to keep OCaml's object/null/array runtime guard:\n{rendered}"
        );
    }

    #[test]
    fn complete_object_then_array_untagged_return_switches_preserve_case_order() {
        let mut compiler = LambdaCompiler::new();
        let value = Ident::create_local("value");
        let block = compiler.compile_untagged_variant_switch_return_statements(
            Expression::var(value.clone()),
            &LambdaSwitch {
                sw_consts_full: true,
                sw_consts: vec![],
                sw_blocks_full: true,
                sw_blocks: vec![
                    (0, Lambda::const_(Constant::int(1))),
                    (1, Lambda::const_(Constant::int(2))),
                ],
                sw_failaction: None,
                sw_names: Some(SwitchNames {
                    consts: vec![],
                    blocks: vec![
                        crate::lambda::SwitchBlock {
                            tag: crate::lambda::SwitchTag::named("Object"),
                            tag_name: None,
                            block_type: Some(crate::lambda::SwitchBlockType::Object),
                        },
                        crate::lambda::SwitchBlock {
                            tag: crate::lambda::SwitchTag::named("Array"),
                            tag_name: None,
                            block_type: Some(crate::lambda::SwitchBlockType::Instance(
                                "Array".to_string(),
                            )),
                        },
                    ],
                }),
            },
        );

        let rendered = print_block(&block);
        assert!(
            rendered.contains("typeof value === \"object\" && !Array.isArray(value)"),
            "expected the object-first two-case switch to keep the first case test:\n{rendered}"
        );
        assert!(
            !rendered.contains("if (Array.isArray(value))"),
            "expected the object-first two-case switch not to flip to an Array-first split:\n{rendered}"
        );
    }

    fn single_complete_array_block_switch(
        array_body: Lambda,
        undefined_body: Lambda,
    ) -> LambdaSwitch {
        LambdaSwitch {
            sw_consts_full: true,
            sw_consts: vec![(0, undefined_body)],
            sw_blocks_full: true,
            sw_blocks: vec![(0, array_body)],
            sw_failaction: None,
            sw_names: Some(SwitchNames {
                consts: vec![crate::lambda::SwitchTag {
                    name: "Empty".to_string(),
                    tag_type: Some(crate::lambda::SwitchCaseTag::Undefined),
                }],
                blocks: vec![crate::lambda::SwitchBlock {
                    tag: crate::lambda::SwitchTag::named("Cons"),
                    tag_name: None,
                    block_type: Some(crate::lambda::SwitchBlockType::Instance(
                        "Array".to_string(),
                    )),
                }],
            }),
        }
    }

    fn default_only_untagged_boolean_switch(
        boolean_body: Lambda,
        default_body: Lambda,
    ) -> LambdaSwitch {
        LambdaSwitch {
            sw_consts_full: false,
            sw_consts: vec![],
            sw_blocks_full: false,
            sw_blocks: vec![(0, boolean_body)],
            sw_failaction: Some(Box::new(default_body)),
            sw_names: Some(SwitchNames {
                consts: vec![
                    crate::lambda::SwitchTag {
                        name: "Null".to_string(),
                        tag_type: Some(crate::lambda::SwitchCaseTag::Null),
                    },
                    crate::lambda::SwitchTag {
                        name: "Undefined".to_string(),
                        tag_type: Some(crate::lambda::SwitchCaseTag::Undefined),
                    },
                ],
                blocks: vec![
                    crate::lambda::SwitchBlock {
                        tag: crate::lambda::SwitchTag::named("B"),
                        tag_name: None,
                        block_type: Some(crate::lambda::SwitchBlockType::Boolean),
                    },
                    crate::lambda::SwitchBlock {
                        tag: crate::lambda::SwitchTag::named("S"),
                        tag_name: None,
                        block_type: Some(crate::lambda::SwitchBlockType::String),
                    },
                    crate::lambda::SwitchBlock {
                        tag: crate::lambda::SwitchTag::named("I"),
                        tag_name: None,
                        block_type: Some(crate::lambda::SwitchBlockType::Int),
                    },
                ],
            }),
        }
    }

    #[test]
    fn complete_single_untagged_array_value_branch_skips_redundant_instance_guard() {
        let mut compiler = LambdaCompiler::new();
        let value = Ident::create_local("value");
        let result = Ident::create_local("result");
        let block = compiler.compile_untagged_variant_switch_assignment_statements(
            &result,
            Expression::var(value.clone()),
            &single_complete_array_block_switch(
                Lambda::const_(Constant::int(1)),
                Lambda::const_(Constant::int(0)),
            ),
        );

        let [dispatch] = block.as_slice() else {
            panic!("expected a single literal-vs-block dispatch");
        };
        let StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Bin(BinOp::Eq, left, right),
            ..
        }) = &dispatch.desc
        else {
            panic!("expected the direct switch assignment");
        };
        assert!(matches!(
            left.as_ref(),
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&result)
        ));
        let ExpressionDesc::Cond(cond, then_expr, else_expr) = &right.as_ref().desc else {
            panic!("expected a conditional expression on the assignment RHS");
        };
        assert_is_undefined_equality_check(cond, &value);
        assert_int_expr(then_expr, 0);
        assert_int_expr(else_expr, 1);
    }

    #[test]
    fn complete_single_untagged_array_return_branch_skips_redundant_instance_guard() {
        let mut compiler = LambdaCompiler::new();
        let value = Ident::create_local("value");
        let block = compiler.compile_untagged_variant_switch_return_statements(
            Expression::var(value.clone()),
            &single_complete_array_block_switch(
                Lambda::const_(Constant::int(1)),
                Lambda::const_(Constant::int(0)),
            ),
        );

        let [dispatch] = block.as_slice() else {
            panic!("expected a single literal dispatch");
        };
        let StatementDesc::Return(Expression {
            desc: ExpressionDesc::Cond(cond, then_expr, else_expr),
            ..
        }) = &dispatch.desc
        else {
            panic!("expected the direct switch return");
        };
        assert_is_undefined_equality_check(cond, &value);
        assert_int_expr(then_expr, 0);
        assert_int_expr(else_expr, 1);
    }

    #[test]
    fn complete_single_untagged_array_effect_branch_skips_redundant_instance_guard() {
        let mut compiler = LambdaCompiler::new();
        let value = Ident::create_local("value");
        let empty_seen = Ident::create_local("empty_seen");
        let cons_seen = Ident::create_local("cons_seen");
        let block = compiler.compile_untagged_variant_switch_effect_statements(
            Expression::var(value.clone()),
            &single_complete_array_block_switch(
                Lambda::Lassign(
                    cons_seen.clone(),
                    Box::new(Lambda::const_(Constant::int(1))),
                ),
                Lambda::Lassign(
                    empty_seen.clone(),
                    Box::new(Lambda::const_(Constant::int(0))),
                ),
            ),
        );

        let [dispatch] = block.as_slice() else {
            panic!("expected a single literal dispatch");
        };
        let StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Cond(cond, then_expr, else_expr),
            ..
        }) = &dispatch.desc
        else {
            panic!("expected the direct switch effect expression");
        };
        assert_is_undefined_equality_check(cond, &value);
        assert_assignment_to_int(then_expr, &empty_seen, 0);
        assert_assignment_to_int(else_expr, &cons_seen, 1);
    }

    #[test]
    fn default_only_untagged_boolean_assignment_skips_literal_dispatch_when_defaults_match() {
        let mut compiler = LambdaCompiler::new();
        let value = Ident::create_local("value");
        let result = Ident::create_local("result");
        let block = compiler.compile_untagged_variant_switch_assignment_statements(
            &result,
            Expression::var(value.clone()),
            &default_only_untagged_boolean_switch(
                Lambda::const_(Constant::int(1)),
                Lambda::const_(Constant::int(0)),
            ),
        );

        let [assign] = block.as_slice() else {
            panic!("expected a single direct switch assignment");
        };
        let StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Bin(BinOp::Eq, left, right),
            ..
        }) = &assign.desc
        else {
            panic!("expected the switch assignment");
        };
        assert!(matches!(
            left.as_ref(),
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&result)
        ));
        let ExpressionDesc::Cond(cond, then_expr, else_expr) = &right.as_ref().desc else {
            panic!("expected the assignment RHS to be a conditional expression");
        };
        assert_typeof_check(cond, &value, "boolean", BinOp::EqEqEq);
        assert_int_expr(then_expr, 1);
        assert_int_expr(else_expr, 0);
    }

    #[test]
    fn default_only_untagged_boolean_return_skips_literal_dispatch_when_defaults_match() {
        let mut compiler = LambdaCompiler::new();
        let value = Ident::create_local("value");
        let block = compiler.compile_untagged_variant_switch_return_statements(
            Expression::var(value.clone()),
            &default_only_untagged_boolean_switch(
                Lambda::const_(Constant::int(1)),
                Lambda::const_(Constant::int(0)),
            ),
        );

        let [dispatch] = block.as_slice() else {
            panic!("expected a single direct switch return");
        };
        let StatementDesc::Return(Expression {
            desc: ExpressionDesc::Cond(cond, then_expr, else_expr),
            ..
        }) = &dispatch.desc
        else {
            panic!("expected the switch return to be a conditional expression");
        };
        assert_typeof_check(cond, &value, "boolean", BinOp::EqEqEq);
        assert_int_expr(then_expr, 1);
        assert_int_expr(else_expr, 0);
    }

    #[test]
    fn default_only_untagged_object_return_keeps_literal_default_branch_outside_object_chain() {
        let mut compiler = LambdaCompiler::new();
        let value = Ident::create_local("value");
        let body_id = Ident::create_local("body");
        let block = compiler.compile_untagged_variant_switch_return_statements(
            Expression::var(value.clone()),
            &LambdaSwitch {
                sw_consts_full: false,
                sw_consts: vec![],
                sw_blocks_full: false,
                sw_blocks: vec![(
                    0,
                    Lambda::let_(
                        LetKind::Strict,
                        body_id.clone(),
                        Lambda::const_(Constant::int(1)),
                        Lambda::var(body_id.clone()),
                    ),
                )],
                sw_failaction: Some(Box::new(Lambda::const_(Constant::int(0)))),
                sw_names: Some(SwitchNames {
                    consts: vec![
                        crate::lambda::SwitchTag {
                            name: "Null".to_string(),
                            tag_type: Some(crate::lambda::SwitchCaseTag::Null),
                        },
                        crate::lambda::SwitchTag {
                            name: "String".to_string(),
                            tag_type: Some(crate::lambda::SwitchCaseTag::String(
                                "string".to_string(),
                            )),
                        },
                    ],
                    blocks: vec![
                        crate::lambda::SwitchBlock {
                            tag: crate::lambda::SwitchTag::named("Object"),
                            tag_name: None,
                            block_type: Some(crate::lambda::SwitchBlockType::Object),
                        },
                        crate::lambda::SwitchBlock {
                            tag: crate::lambda::SwitchTag::named("Array"),
                            tag_name: None,
                            block_type: Some(crate::lambda::SwitchBlockType::Instance(
                                "Array".to_string(),
                            )),
                        },
                    ],
                }),
            },
        );

        let rendered = print_block(&block);
        assert!(
            rendered.contains(
                "if (typeof value !== \"object\" || value === null || Array.isArray(value))"
            ),
            "expected the literal/default side to stay outside the object chain:\n{rendered}"
        );
        assert!(
            rendered.contains("return 0;"),
            "expected the literal/default branch to return the fallback:\n{rendered}"
        );
        assert!(
            rendered.contains("let body = 1;") && rendered.contains("return body;"),
            "expected the object branch to stay inside the guarded path:\n{rendered}"
        );
    }

    fn assert_switch_case_assigns_int_result(block: &Block, result: &Ident, expected: i32) {
        let [assign, break_stmt] = block.as_slice() else {
            panic!("expected an assignment followed by break");
        };
        match &assign.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Bin(BinOp::Eq, left, right),
                ..
            }) => {
                assert!(matches!(
                    left.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(result)
                ));
                assert!(matches!(
                    right.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Number(Number::Int { i, .. }),
                        ..
                    } if *i == expected
                ));
            }
            other => panic!("expected a result assignment, got {other:?}"),
        }
        assert!(matches!(break_stmt.desc, StatementDesc::Break));
    }

    fn assert_switch_default_assigns_int_result(block: &Block, result: &Ident, expected: i32) {
        let assign = match block.as_slice() {
            [assign] => assign,
            [assign, break_stmt] if matches!(break_stmt.desc, StatementDesc::Break) => assign,
            _ => panic!("expected a default assignment with an optional break"),
        };
        match &assign.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Bin(BinOp::Eq, left, right),
                ..
            }) => {
                assert!(matches!(
                    left.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(result)
                ));
                assert!(matches!(
                    right.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Number(Number::Int { i, .. }),
                        ..
                    } if *i == expected
                ));
            }
            other => panic!("expected a default assignment, got {other:?}"),
        }
    }

    fn assert_is_undefined_equality_check(expr: &Expression, ident: &Ident) {
        match &expr.desc {
            ExpressionDesc::Bin(BinOp::EqEqEq, left, right) => {
                assert!(matches!(
                    left.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(ident)
                ));
                assert!(matches!(
                    right.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Undefined { .. },
                        ..
                    }
                ));
            }
            other => panic!("expected an undefined equality dispatch, got {other:?}"),
        }
    }

    fn assert_int_expr(expr: &Expression, expected: i32) {
        assert!(matches!(
            expr,
            Expression {
                desc: ExpressionDesc::Number(Number::Int { i, .. }),
                ..
            } if *i == expected
        ));
    }

    fn assert_assignment_to_int(expr: &Expression, ident: &Ident, expected: i32) {
        match &expr.desc {
            ExpressionDesc::Bin(BinOp::Eq, left, right) => {
                assert!(matches!(
                    left.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(ident)
                ));
                assert_int_expr(right, expected);
            }
            other => panic!("expected an assignment expression, got {other:?}"),
        }
    }

    fn assert_effect_assignment_writes_int(block: &Block, ident: &Ident, expected: i32) {
        let [assign] = block.as_slice() else {
            panic!("expected a single effect assignment");
        };
        match &assign.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Bin(BinOp::Eq, left, right),
                ..
            }) => {
                assert!(matches!(
                    left.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(ident)
                ));
                assert!(matches!(
                    right.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Number(Number::Int { i, .. }),
                        ..
                    } if *i == expected
                ));
            }
            other => panic!("expected an effect assignment, got {other:?}"),
        }
    }

    fn assert_switch_case_returns_int_result(block: &Block, expected: i32) {
        let [ret] = block.as_slice() else {
            panic!("expected a single return statement");
        };
        match &ret.desc {
            StatementDesc::Return(Expression {
                desc: ExpressionDesc::Number(Number::Int { i, .. }),
                ..
            }) if *i == expected => {}
            other => panic!("expected a return of {expected}, got {other:?}"),
        }
    }

    fn assert_switch_default_returns_int_result(block: &Block, expected: i32) {
        assert_switch_case_returns_int_result(block, expected);
    }

    fn assert_switch_case_returns_bool_result(block: &Block, expected: bool) {
        let [ret] = block.as_slice() else {
            panic!("expected a single return statement");
        };
        match &ret.desc {
            StatementDesc::Return(Expression {
                desc: ExpressionDesc::Bool(value),
                ..
            }) if *value == expected => {}
            other => panic!("expected a return of {expected}, got {other:?}"),
        }
    }

    fn assert_typeof_check(
        expr: &Expression,
        ident: &Ident,
        expected_type: &str,
        expected_op: BinOp,
    ) {
        match &expr.desc {
            ExpressionDesc::Bin(op, left, right) if *op == expected_op => {
                assert!(matches!(
                    left.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Typeof(inner),
                        ..
                    } if matches!(
                        inner.as_ref(),
                        Expression {
                            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                            ..
                        } if id.same(ident)
                    )
                ));
                assert!(matches!(
                    right.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Str { txt, .. },
                        ..
                    } if txt == expected_type
                ));
            }
            other => panic!("expected a typeof check, got {other:?}"),
        }
    }

    fn assert_typeof_object_check(expr: &Expression, ident: &Ident, expect_object: bool) {
        let expected_op = if expect_object {
            BinOp::EqEqEq
        } else {
            BinOp::NotEqEq
        };
        assert_typeof_check(expr, ident, "object", expected_op);
    }

    fn assert_array_is_array_call(expr: &Expression, ident: &Ident) {
        match &expr.desc {
            ExpressionDesc::Call(func, args, _) => {
                assert!(matches!(
                    func.as_ref(),
                    Expression {
                        desc: ExpressionDesc::StaticIndex(target, field, _),
                        ..
                    } if field == "isArray"
                        && matches!(
                            target.as_ref(),
                            Expression {
                                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(array_ident)),
                                ..
                            } if array_ident.name() == "Array"
                        )
                ));
                assert!(matches!(
                    args.as_slice(),
                    [Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    }] if id.same(ident)
                ));
            }
            other => panic!("expected Array.isArray call, got {other:?}"),
        }
    }

    fn assert_string_equality_check(
        expr: &Expression,
        ident: Option<&Ident>,
        tag_ident: Option<&Ident>,
        expected_tag: &str,
    ) {
        match &expr.desc {
            ExpressionDesc::Bin(BinOp::EqEqEq, left, right) => {
                match (ident, tag_ident) {
                    (Some(ident), None) => {
                        assert!(matches!(
                            left.as_ref(),
                            Expression {
                                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                                ..
                            } if id.same(ident)
                        ));
                    }
                    (None, Some(tag_ident)) => assert_tag_field_access(left, tag_ident),
                    _ => panic!("expected exactly one string-equality input shape"),
                }
                assert!(matches!(
                    right.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Str { txt, .. },
                        ..
                    } if txt == expected_tag
                ));
            }
            other => panic!("expected a string equality check, got {other:?}"),
        }
    }

    fn assert_tag_field_access(expr: &Expression, ident: &Ident) {
        match &expr.desc {
            ExpressionDesc::StaticIndex(target, field, _) if field == "TAG" => {
                assert!(matches!(
                    target.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(ident)
                ));
            }
            other => panic!("expected a TAG field access, got {other:?}"),
        }
    }

    #[test]
    fn drops_pure_sequence_prefixes_in_effect_contexts() {
        let mut compiler = LambdaCompiler::new();
        let value = Ident::create_local("value");
        let lam = Lambda::Lsequence(
            Box::new(Lambda::const_(Constant::int(1))),
            Box::new(Lambda::var(value.clone())),
        );
        let program = compiler.compile_program(&lam);

        let [stmt] = program.block.as_slice() else {
            panic!("expected a single expression statement");
        };
        match &stmt.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            }) => assert!(id.same(&value)),
            other => panic!("expected pure sequence prefix to be removed, got {other:?}"),
        }
    }

    #[test]
    fn flattens_value_sequences_back_to_effect_statements_at_toplevel() {
        let mut compiler = LambdaCompiler::new();
        let callback = Ident::create_local("callback");
        let lam = Lambda::Lsequence(
            Box::new(Lambda::Lapply(Apply {
                ap_func: Box::new(Lambda::var(callback.clone())),
                ap_args: vec![],
                ap_info: ApInfo {
                    loc: Location::none(),
                    inlined: InlineAttribute::Default,
                    status: ApplyStatus::Na,
                },
                ap_transformed_jsx: false,
            })),
            Box::new(Lambda::const_(Constant::none())),
        );
        let program = compiler.compile_program(&lam);

        let [stmt] = program.block.as_slice() else {
            panic!("expected a single expression statement");
        };
        match &stmt.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Call(func, args, _),
                ..
            }) => {
                assert!(args.is_empty());
                assert!(matches!(
                    func.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&callback)
                ));
            }
            other => {
                panic!("expected top-level sequence to flatten to a call statement, got {other:?}")
            }
        }
    }

    #[test]
    fn effect_context_calls_with_arg_preludes_skip_intermediate_call_temps() {
        let mut compiler = LambdaCompiler::new();
        let before = Ident::create_local("before");
        let after = Ident::create_local("after");
        let then_fn = Ident::create_local("thenFn");
        let else_fn = Ident::create_local("elseFn");
        let lam = Lambda::Lapply(Apply {
            ap_func: Box::new(Lambda::LifThenElse(
                Box::new(Lambda::const_(Constant::JsTrue)),
                Box::new(Lambda::Lsequence(
                    Box::new(Lambda::Lapply(Apply {
                        ap_func: Box::new(Lambda::var(before.clone())),
                        ap_args: vec![],
                        ap_info: ApInfo {
                            loc: Location::none(),
                            inlined: InlineAttribute::Default,
                            status: ApplyStatus::Na,
                        },
                        ap_transformed_jsx: false,
                    })),
                    Box::new(Lambda::var(then_fn.clone())),
                )),
                Box::new(Lambda::Lsequence(
                    Box::new(Lambda::Lapply(Apply {
                        ap_func: Box::new(Lambda::var(after.clone())),
                        ap_args: vec![],
                        ap_info: ApInfo {
                            loc: Location::none(),
                            inlined: InlineAttribute::Default,
                            status: ApplyStatus::Na,
                        },
                        ap_transformed_jsx: false,
                    })),
                    Box::new(Lambda::var(else_fn.clone())),
                )),
            )),
            ap_args: vec![Lambda::const_(Constant::int(1))],
            ap_info: ApInfo {
                loc: Location::none(),
                inlined: InlineAttribute::Default,
                status: ApplyStatus::Na,
            },
            ap_transformed_jsx: false,
        });

        let program = compiler.compile_program(&lam);
        let rendered = print_block(&program.block);
        assert!(
            !rendered.contains("let call ="),
            "effect-context apply reintroduced a call temp:\n{rendered}"
        );
        assert!(
            rendered.contains("(1);"),
            "effect-context apply lost the direct call:\n{rendered}"
        );
    }

    #[test]
    fn value_context_direct_calls_stay_as_call_expressions() {
        let mut compiler = LambdaCompiler::new();
        let callback = Ident::create_local("callback");
        let compiled = compiler.compile_expr(&Lambda::Lapply(Apply {
            ap_func: Box::new(Lambda::var(callback.clone())),
            ap_args: vec![Lambda::const_(Constant::int(1))],
            ap_info: ApInfo {
                loc: Location::none(),
                inlined: InlineAttribute::Default,
                status: ApplyStatus::Na,
            },
            ap_transformed_jsx: false,
        }));

        assert!(
            compiled.prelude.is_empty(),
            "value-context call unexpectedly emitted a prelude: {:?}",
            compiled.prelude
        );
        assert!(matches!(
            compiled.expr,
            Expression {
                desc: ExpressionDesc::Call(func, args, _),
                ..
            } if matches!(
                func.as_ref(),
                Expression {
                    desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                    ..
                } if id.same(&callback)
            ) && matches!(
                args.as_slice(),
                [Expression {
                    desc: ExpressionDesc::Number(Number::Int { i: 1, .. }),
                    ..
                }]
            )
        ));
    }

    #[test]
    fn nested_app_na_calls_reassociate_through_lam_apply_for_ari_regress_shape() {
        let mut compiler = LambdaCompiler::new();
        let gg = Ident::create_local("gg");
        let x = Ident::create_local("x");
        let y = Ident::create_local("y");
        let u = Ident::create_local("u");
        let z = Ident::create_local("z");
        let result = Ident::create_local("result");
        let loc = Location::none();

        let lam = Lambda::let_(
            LetKind::Alias,
            gg.clone(),
            Lambda::prim(
                Primitive::PjsFnMake(2),
                vec![Lambda::function_(
                    2,
                    vec![x.clone(), y.clone()],
                    Lambda::let_(
                        LetKind::Strict,
                        u.clone(),
                        Lambda::prim(
                            Primitive::Paddint,
                            vec![Lambda::var(x), Lambda::var(y)],
                            loc.clone(),
                        ),
                        Lambda::prim(
                            Primitive::PjsFnMake(1),
                            vec![Lambda::function_(
                                1,
                                vec![z.clone()],
                                Lambda::prim(
                                    Primitive::Paddint,
                                    vec![Lambda::var(u.clone()), Lambda::var(z)],
                                    loc.clone(),
                                ),
                                crate::lambda::FunctionAttribute::default(),
                            )],
                            loc.clone(),
                        ),
                    ),
                    crate::lambda::FunctionAttribute::default(),
                )],
                loc.clone(),
            ),
            Lambda::let_(
                LetKind::Strict,
                result.clone(),
                Lambda::Lapply(Apply {
                    ap_func: Box::new(Lambda::Lapply(Apply {
                        ap_func: Box::new(Lambda::var(gg)),
                        ap_args: vec![
                            Lambda::const_(Constant::int(3)),
                            Lambda::const_(Constant::int(5)),
                        ],
                        ap_info: ApInfo {
                            loc: loc.clone(),
                            inlined: InlineAttribute::Default,
                            status: ApplyStatus::Na,
                        },
                        ap_transformed_jsx: false,
                    })),
                    ap_args: vec![Lambda::const_(Constant::int(6))],
                    ap_info: ApInfo {
                        loc: loc.clone(),
                        inlined: InlineAttribute::Default,
                        status: ApplyStatus::Na,
                    },
                    ap_transformed_jsx: false,
                }),
                Lambda::var(result.clone()),
            ),
        );

        let simplified = crate::lambda::simplify::simplify_for_js_backend(&lam);
        let compiled = compiler.compile_expr(&simplified);
        let rendered = format!(
            "{}\n{}",
            print_block(&compiled.prelude),
            print_expression(&compiled.expr)
        );
        assert!(
            rendered.contains("u + 6 | 0"),
            "expected Ari_regress-style nested apply to collapse to a direct add, got:\n{rendered}"
        );
        assert!(
            !rendered.contains("(z => u + z | 0)(6)"),
            "expected Ari_regress-style nested apply to avoid an emitted IIFE, got:\n{rendered}"
        );
    }

    #[test]
    fn nested_app_na_calls_reassociate_multi_arg_returned_functions_for_test_demo_shape() {
        let mut compiler = LambdaCompiler::new();
        let g1 = Ident::create_local("g1");
        let x = Ident::create_local("x");
        let y = Ident::create_local("y");
        let u = Ident::create_local("u");
        let xx = Ident::create_local("xx");
        let yy = Ident::create_local("yy");
        let extra = Ident::create_local("extra");
        let result = Ident::create_local("result");
        let loc = Location::none();

        let lam = Lambda::let_(
            LetKind::Alias,
            g1.clone(),
            Lambda::prim(
                Primitive::PjsFnMake(2),
                vec![Lambda::function_(
                    2,
                    vec![x.clone(), y.clone()],
                    Lambda::let_(
                        LetKind::Strict,
                        u.clone(),
                        Lambda::prim(
                            Primitive::Paddint,
                            vec![Lambda::var(x), Lambda::var(y)],
                            loc.clone(),
                        ),
                        Lambda::prim(
                            Primitive::PjsFnMake(2),
                            vec![Lambda::function_(
                                2,
                                vec![xx.clone(), yy.clone()],
                                Lambda::prim(
                                    Primitive::Paddint,
                                    vec![
                                        Lambda::prim(
                                            Primitive::Paddint,
                                            vec![Lambda::var(xx), Lambda::var(yy)],
                                            loc.clone(),
                                        ),
                                        Lambda::var(u.clone()),
                                    ],
                                    loc.clone(),
                                ),
                                crate::lambda::FunctionAttribute::default(),
                            )],
                            loc.clone(),
                        ),
                    ),
                    crate::lambda::FunctionAttribute::default(),
                )],
                loc.clone(),
            ),
            Lambda::let_(
                LetKind::Strict,
                result.clone(),
                Lambda::function_(
                    1,
                    vec![extra.clone()],
                    Lambda::Lapply(Apply {
                        ap_func: Box::new(Lambda::Lapply(Apply {
                            ap_func: Box::new(Lambda::var(g1)),
                            ap_args: vec![
                                Lambda::const_(Constant::int(3)),
                                Lambda::const_(Constant::int(4)),
                            ],
                            ap_info: ApInfo {
                                loc: loc.clone(),
                                inlined: InlineAttribute::Default,
                                status: ApplyStatus::Na,
                            },
                            ap_transformed_jsx: false,
                        })),
                        ap_args: vec![Lambda::const_(Constant::int(6)), Lambda::var(extra.clone())],
                        ap_info: ApInfo {
                            loc: loc.clone(),
                            inlined: InlineAttribute::Default,
                            status: ApplyStatus::Na,
                        },
                        ap_transformed_jsx: false,
                    }),
                    crate::lambda::FunctionAttribute::default(),
                ),
                Lambda::var(result),
            ),
        );

        let simplified = crate::lambda::simplify::simplify_for_js_backend(&lam);
        let compiled = compiler.compile_expr(&simplified);
        let rendered = print_expression(&compiled.expr);
        assert!(
            rendered.contains("(6 + extra | 0) + u | 0"),
            "expected test_demo-style nested apply to collapse to a direct returned add, got:\n{rendered}"
        );
        assert!(
            !rendered.contains("((xx, yy) => (xx + yy | 0) + u | 0)(6, extra)"),
            "expected test_demo-style nested apply to avoid an emitted multi-arg IIFE, got:\n{rendered}"
        );
    }

    #[test]
    fn let_bound_direct_calls_skip_intermediate_call_aliases() {
        let mut compiler = LambdaCompiler::new();
        let callback = Ident::create_local("callback");
        let x = Ident::create_local("x");
        let compiled = compiler.compile_expr(&Lambda::Llet(
            LetKind::Strict,
            x.clone(),
            Box::new(Lambda::Lapply(Apply {
                ap_func: Box::new(Lambda::var(callback)),
                ap_args: vec![Lambda::const_(Constant::int(1))],
                ap_info: ApInfo {
                    loc: Location::none(),
                    inlined: InlineAttribute::Default,
                    status: ApplyStatus::Na,
                },
                ap_transformed_jsx: false,
            })),
            Box::new(Lambda::var(x.clone())),
        ));

        let [decl] = compiled.prelude.as_slice() else {
            panic!("expected one initialized declaration for the let-bound call");
        };
        assert!(matches!(
            decl,
            Statement {
                desc: StatementDesc::Variable(VariableDeclaration {
                    ident,
                    value:
                        Some(Expression {
                            desc: ExpressionDesc::Call(func, args, _),
                            ..
                        }),
                    ..
                }),
                ..
            } if ident.same(&x)
                && matches!(
                    func.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.name() == "callback"
                )
                && matches!(
                    args.as_slice(),
                    [Expression {
                        desc: ExpressionDesc::Number(Number::Int { i: 1, .. }),
                        ..
                    }]
                )
        ));
        assert!(matches!(
            compiled.expr,
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&x)
        ));
    }

    #[test]
    fn return_context_calls_with_arg_preludes_skip_intermediate_call_temps() {
        let mut compiler = LambdaCompiler::new();
        let before = Ident::create_local("before");
        let after = Ident::create_local("after");
        let then_fn = Ident::create_local("thenFn");
        let else_fn = Ident::create_local("elseFn");
        let lam = Lambda::Lapply(Apply {
            ap_func: Box::new(Lambda::LifThenElse(
                Box::new(Lambda::const_(Constant::JsTrue)),
                Box::new(Lambda::Lsequence(
                    Box::new(Lambda::Lapply(Apply {
                        ap_func: Box::new(Lambda::var(before.clone())),
                        ap_args: vec![],
                        ap_info: ApInfo {
                            loc: Location::none(),
                            inlined: InlineAttribute::Default,
                            status: ApplyStatus::Na,
                        },
                        ap_transformed_jsx: false,
                    })),
                    Box::new(Lambda::var(then_fn.clone())),
                )),
                Box::new(Lambda::Lsequence(
                    Box::new(Lambda::Lapply(Apply {
                        ap_func: Box::new(Lambda::var(after.clone())),
                        ap_args: vec![],
                        ap_info: ApInfo {
                            loc: Location::none(),
                            inlined: InlineAttribute::Default,
                            status: ApplyStatus::Na,
                        },
                        ap_transformed_jsx: false,
                    })),
                    Box::new(Lambda::var(else_fn.clone())),
                )),
            )),
            ap_args: vec![Lambda::const_(Constant::int(1))],
            ap_info: ApInfo {
                loc: Location::none(),
                inlined: InlineAttribute::Default,
                status: ApplyStatus::Na,
            },
            ap_transformed_jsx: false,
        });

        let block = compiler.compile_return_block(&lam);
        let rendered = print_block(&block);
        assert!(
            !rendered.contains("let call ="),
            "return-context apply reintroduced a call temp:\n{rendered}"
        );
        assert!(
            !rendered.contains("return call;"),
            "return-context apply still returns the call temp:\n{rendered}"
        );
        assert!(
            rendered.contains("return ") && rendered.contains("(1);"),
            "return-context apply lost the direct return call:\n{rendered}"
        );
    }

    #[test]
    fn assignment_context_calls_with_arg_preludes_skip_intermediate_call_temps() {
        let mut compiler = LambdaCompiler::new();
        let before = Ident::create_local("before");
        let after = Ident::create_local("after");
        let then_fn = Ident::create_local("thenFn");
        let else_fn = Ident::create_local("elseFn");
        let result = Ident::create_local("result");
        let lam = Lambda::Lapply(Apply {
            ap_func: Box::new(Lambda::LifThenElse(
                Box::new(Lambda::const_(Constant::JsTrue)),
                Box::new(Lambda::Lsequence(
                    Box::new(Lambda::Lapply(Apply {
                        ap_func: Box::new(Lambda::var(before.clone())),
                        ap_args: vec![],
                        ap_info: ApInfo {
                            loc: Location::none(),
                            inlined: InlineAttribute::Default,
                            status: ApplyStatus::Na,
                        },
                        ap_transformed_jsx: false,
                    })),
                    Box::new(Lambda::var(then_fn.clone())),
                )),
                Box::new(Lambda::Lsequence(
                    Box::new(Lambda::Lapply(Apply {
                        ap_func: Box::new(Lambda::var(after.clone())),
                        ap_args: vec![],
                        ap_info: ApInfo {
                            loc: Location::none(),
                            inlined: InlineAttribute::Default,
                            status: ApplyStatus::Na,
                        },
                        ap_transformed_jsx: false,
                    })),
                    Box::new(Lambda::var(else_fn.clone())),
                )),
            )),
            ap_args: vec![Lambda::const_(Constant::int(1))],
            ap_info: ApInfo {
                loc: Location::none(),
                inlined: InlineAttribute::Default,
                status: ApplyStatus::Na,
            },
            ap_transformed_jsx: false,
        });

        let block = compiler.compile_assign_to_target_block(&result, &lam);
        let rendered = print_block(&block);
        assert!(
            !rendered.contains("let call ="),
            "assignment-context apply reintroduced a call temp:\n{rendered}"
        );
        assert!(
            !rendered.contains("= call;"),
            "assignment-context apply still assigns from the call temp:\n{rendered}"
        );
        assert!(
            rendered.contains("result = ") && rendered.contains("(1);"),
            "assignment-context apply lost the direct assignment call:\n{rendered}"
        );
    }

    #[test]
    fn function_bodies_drop_pure_undefined_sequence_suffixes() {
        let mut compiler = LambdaCompiler::new();
        let callback = Ident::create_local("callback");
        let value = Ident::create_local("value");
        let call = || {
            Lambda::Lapply(Apply {
                ap_func: Box::new(Lambda::var(callback.clone())),
                ap_args: vec![],
                ap_info: ApInfo {
                    loc: Location::none(),
                    inlined: InlineAttribute::Default,
                    status: ApplyStatus::Na,
                },
                ap_transformed_jsx: false,
            })
        };
        let body = Lambda::Lsequence(
            Box::new(Lambda::Lsequence(
                Box::new(call()),
                Box::new(Lambda::const_(Constant::none())),
            )),
            Box::new(Lambda::Lsequence(
                Box::new(Lambda::Lsequence(
                    Box::new(call()),
                    Box::new(Lambda::const_(Constant::none())),
                )),
                Box::new(Lambda::var(value.clone())),
            )),
        );
        let compiled = compiler.compile_expr(&Lambda::Lfunction(crate::lambda::LFunction {
            arity: 1,
            params: vec![value.clone()],
            body: Box::new(body),
            attr: crate::lambda::FunctionAttribute::default(),
        }));

        let Expression {
            desc: ExpressionDesc::Fun { body, .. },
            ..
        } = compiled.expr
        else {
            panic!("expected a function expression");
        };

        let [first, second, third] = body.as_slice() else {
            panic!("expected two effect statements followed by a return");
        };

        for stmt in [first, second] {
            match &stmt.desc {
                StatementDesc::Exp(Expression {
                    desc: ExpressionDesc::Call(func, args, _),
                    ..
                }) => {
                    assert!(args.is_empty());
                    assert!(matches!(
                        func.as_ref(),
                        Expression {
                            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                            ..
                        } if id.same(&callback)
                    ));
                }
                other => panic!("expected a callback call statement, got {other:?}"),
            }
        }

        match &third.desc {
            StatementDesc::Return(Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            }) => assert!(id.same(&value)),
            other => panic!("expected a return of the original value, got {other:?}"),
        }
    }

    #[test]
    fn top_level_if_effects_drop_trailing_pure_undefined_branch_suffixes() {
        let mut compiler = LambdaCompiler::new();
        let cond = Ident::create_local("cond");
        let then_callback = Ident::create_local("thenCallback");
        let else_callback = Ident::create_local("elseCallback");
        let call = |id: &Ident| {
            Lambda::Lapply(Apply {
                ap_func: Box::new(Lambda::var(id.clone())),
                ap_args: vec![],
                ap_info: ApInfo {
                    loc: Location::none(),
                    inlined: InlineAttribute::Default,
                    status: ApplyStatus::Na,
                },
                ap_transformed_jsx: false,
            })
        };
        let lam = Lambda::LifThenElse(
            Box::new(Lambda::var(cond)),
            Box::new(Lambda::Lsequence(
                Box::new(call(&then_callback)),
                Box::new(Lambda::const_(Constant::none())),
            )),
            Box::new(Lambda::Lsequence(
                Box::new(call(&else_callback)),
                Box::new(Lambda::const_(Constant::none())),
            )),
        );

        let program = compiler.compile_program(&lam);
        let rendered = print_block(&program.block);
        assert!(
            !rendered.contains("undefined;"),
            "top-level if effect branch kept a pure undefined suffix:\n{rendered}"
        );
    }

    #[test]
    fn js_flatten_pass_splits_function_return_sequences_into_statements() {
        let function_ident = Ident::create_local("run");
        let callback = Ident::create_local("callback");
        let deps = apply_js_flatten_pass(DepsProgram {
            program: Program::new(
                vec![Statement::variable(VariableDeclaration {
                    ident: function_ident,
                    value: Some(Expression::new(ExpressionDesc::Fun {
                        is_method: false,
                        params: vec![],
                        body: vec![Statement::return_(Expression::new(ExpressionDesc::Seq(
                            Box::new(Expression::call(
                                Expression::var(callback.clone()),
                                vec![],
                                CallInfo::default(),
                            )),
                            Box::new(Expression::undefined(false)),
                        )))],
                        env: Default::default(),
                        return_unit: false,
                        async_: false,
                        directive: None,
                    })),
                    property: LetKind::Strict,
                    ident_info: IdentInfo::default(),
                })],
                vec![],
            ),
            modules: vec![],
            side_effect: None,
        });

        let [stmt] = deps.program.block.as_slice() else {
            panic!("expected one top-level statement");
        };
        let StatementDesc::Variable(VariableDeclaration {
            value:
                Some(Expression {
                    desc: ExpressionDesc::Fun { body, .. },
                    ..
                }),
            ..
        }) = &stmt.desc
        else {
            panic!("expected a function-valued variable declaration");
        };

        let [first, second] = body.as_slice() else {
            panic!("expected flattened function body");
        };
        match &first.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Call(func, args, _),
                ..
            }) => {
                assert!(args.is_empty());
                assert!(matches!(
                    func.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&callback)
                ));
            }
            other => panic!("expected callback expression statement, got {other:?}"),
        }
        match &second.desc {
            StatementDesc::Return(Expression {
                desc: ExpressionDesc::Undefined { is_unit: false },
                ..
            }) => {}
            other => panic!("expected return undefined after flattening, got {other:?}"),
        }
    }

    #[test]
    fn js_flatten_pass_turns_conditional_effects_into_if_statements() {
        let then_callback = Ident::create_local("thenCallback");
        let else_callback = Ident::create_local("elseCallback");
        let deps = apply_js_flatten_pass(DepsProgram {
            program: Program::new(
                vec![Statement::exp(Expression::cond(
                    Expression::bool(true),
                    Expression::call(
                        Expression::var(then_callback.clone()),
                        vec![],
                        CallInfo::default(),
                    ),
                    Expression::call(
                        Expression::var(else_callback.clone()),
                        vec![],
                        CallInfo::default(),
                    ),
                ))],
                vec![],
            ),
            modules: vec![],
            side_effect: None,
        });

        let [stmt] = deps.program.block.as_slice() else {
            panic!("expected one top-level statement");
        };
        let StatementDesc::If(test, then_block, else_block) = &stmt.desc else {
            panic!("expected conditional effect to lower to an if statement");
        };
        assert!(matches!(test.desc, ExpressionDesc::Bool(true)));

        let [then_stmt] = then_block.as_slice() else {
            panic!("expected one statement in then branch");
        };
        let [else_stmt] = else_block.as_slice() else {
            panic!("expected one statement in else branch");
        };

        match &then_stmt.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Call(func, args, _),
                ..
            }) => {
                assert!(args.is_empty());
                assert!(matches!(
                    func.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&then_callback)
                ));
            }
            other => panic!("expected then branch effect call, got {other:?}"),
        }
        match &else_stmt.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Call(func, args, _),
                ..
            }) => {
                assert!(args.is_empty());
                assert!(matches!(
                    func.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&else_callback)
                ));
            }
            other => panic!("expected else branch effect call, got {other:?}"),
        }
    }

    #[test]
    fn js_tailcall_inline_inlines_once_pure_named_calls() {
        let helper = Ident::create_local("helper");
        let arg = Ident::create_local("arg");
        let run = Ident::create_local("run");
        let value = Ident::create_local("value");
        let deps = apply_js_tailcall_inline_pass(DepsProgram {
            program: Program::new(
                vec![
                    Statement::variable(VariableDeclaration {
                        ident: helper.clone(),
                        value: Some(Expression::new(ExpressionDesc::Fun {
                            is_method: false,
                            params: vec![arg.clone()],
                            body: vec![Statement::return_(Expression::var(arg.clone()))],
                            env: Default::default(),
                            return_unit: false,
                            async_: false,
                            directive: None,
                        })),
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    }),
                    Statement::variable(VariableDeclaration {
                        ident: run.clone(),
                        value: Some(Expression::new(ExpressionDesc::Fun {
                            is_method: false,
                            params: vec![value.clone()],
                            body: vec![Statement::return_(Expression::call(
                                Expression::var(helper.clone()),
                                vec![Expression::var(value.clone())],
                                CallInfo::default(),
                            ))],
                            env: Default::default(),
                            return_unit: false,
                            async_: false,
                            directive: None,
                        })),
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    }),
                ],
                vec![run.clone()],
            ),
            modules: vec![],
            side_effect: None,
        });

        let [helper_stmt, run_stmt] = deps.program.block.as_slice() else {
            panic!("expected helper and run bindings");
        };

        match &helper_stmt.desc {
            StatementDesc::Variable(VariableDeclaration { ident_info, .. }) => {
                assert_eq!(ident_info.used_stats, UsedStats::DeadPure);
            }
            other => {
                panic!("expected helper to remain marked dead for the next pass, got {other:?}")
            }
        }

        let StatementDesc::Variable(VariableDeclaration {
            ident,
            ident_info,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Fun { body, .. },
                    ..
                }),
            ..
        }) = &run_stmt.desc
        else {
            panic!("expected run to remain a function binding");
        };
        assert!(ident.same(&run));
        assert_eq!(ident_info.used_stats, UsedStats::Exported);

        let [stmt] = body.as_slice() else {
            panic!("expected the inlined body to contain a single return");
        };
        match &stmt.desc {
            StatementDesc::Return(Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            }) => assert!(id.same(&value)),
            other => panic!("expected the named call to inline to `return value`, got {other:?}"),
        }
    }

    #[test]
    fn js_tailcall_inline_inlines_suffix_named_calls_after_prefix_statements() {
        let helper = Ident::create_local("helper");
        let arg = Ident::create_local("arg");
        let run = Ident::create_local("run");
        let value = Ident::create_local("value");
        let guard = Ident::create_local("guard");
        let deps = apply_js_tailcall_inline_pass(DepsProgram {
            program: Program::new(
                vec![
                    Statement::variable(VariableDeclaration {
                        ident: helper.clone(),
                        value: Some(Expression::new(ExpressionDesc::Fun {
                            is_method: false,
                            params: vec![arg.clone()],
                            body: vec![Statement::return_(Expression::var(arg.clone()))],
                            env: Default::default(),
                            return_unit: false,
                            async_: false,
                            directive: None,
                        })),
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    }),
                    Statement::variable(VariableDeclaration {
                        ident: run.clone(),
                        value: Some(Expression::new(ExpressionDesc::Fun {
                            is_method: false,
                            params: vec![guard.clone(), value.clone()],
                            body: vec![
                                Statement::if_(
                                    Expression::var(guard.clone()),
                                    vec![Statement::return_(Expression::number(Number::int(0)))],
                                    vec![],
                                ),
                                Statement::return_(Expression::call(
                                    Expression::var(helper.clone()),
                                    vec![Expression::var(value.clone())],
                                    CallInfo::default(),
                                )),
                            ],
                            env: Default::default(),
                            return_unit: false,
                            async_: false,
                            directive: None,
                        })),
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    }),
                ],
                vec![run.clone()],
            ),
            modules: vec![],
            side_effect: None,
        });

        let [helper_stmt, run_stmt] = deps.program.block.as_slice() else {
            panic!("expected helper and run bindings");
        };

        match &helper_stmt.desc {
            StatementDesc::Variable(VariableDeclaration { ident_info, .. }) => {
                assert_eq!(ident_info.used_stats, UsedStats::DeadPure);
            }
            other => {
                panic!("expected helper to remain marked dead for the next pass, got {other:?}")
            }
        }

        let StatementDesc::Variable(VariableDeclaration {
            value:
                Some(Expression {
                    desc: ExpressionDesc::Fun { body, .. },
                    ..
                }),
            ..
        }) = &run_stmt.desc
        else {
            panic!("expected run to remain a function binding");
        };

        let [prefix, suffix] = body.as_slice() else {
            panic!("expected the guard to remain ahead of the inlined suffix call");
        };
        assert!(match &prefix.desc {
            StatementDesc::If(_, _, _) => true,
            StatementDesc::Block(block) => matches!(
                block.as_slice(),
                [Statement {
                    desc: StatementDesc::If(_, _, _),
                    ..
                }]
            ),
            _ => false,
        });
        match &suffix.desc {
            StatementDesc::Return(Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            }) => assert!(id.same(&value)),
            other => {
                panic!("expected the suffix named call to inline to `return value`, got {other:?}")
            }
        }
    }

    #[test]
    fn js_tailcall_inline_inlines_direct_return_iifes() {
        let run = Ident::create_local("run");
        let value = Ident::create_local("value");
        let param = Ident::create_local("param");
        let deps = apply_js_tailcall_inline_pass(DepsProgram {
            program: Program::new(
                vec![Statement::variable(VariableDeclaration {
                    ident: run.clone(),
                    value: Some(Expression::new(ExpressionDesc::Fun {
                        is_method: false,
                        params: vec![value.clone()],
                        body: vec![Statement::return_(Expression::call(
                            Expression::new(ExpressionDesc::Fun {
                                is_method: false,
                                params: vec![param.clone()],
                                body: vec![Statement::return_(Expression::var(param.clone()))],
                                env: Default::default(),
                                return_unit: false,
                                async_: false,
                                directive: None,
                            }),
                            vec![Expression::var(value.clone())],
                            CallInfo::default(),
                        ))],
                        env: Default::default(),
                        return_unit: false,
                        async_: false,
                        directive: None,
                    })),
                    property: LetKind::Strict,
                    ident_info: IdentInfo::default(),
                })],
                vec![run.clone()],
            ),
            modules: vec![],
            side_effect: None,
        });

        let [stmt] = deps.program.block.as_slice() else {
            panic!("expected one top-level binding");
        };
        let StatementDesc::Variable(VariableDeclaration {
            value:
                Some(Expression {
                    desc: ExpressionDesc::Fun { body, .. },
                    ..
                }),
            ..
        }) = &stmt.desc
        else {
            panic!("expected run to remain a function binding");
        };

        let [stmt] = body.as_slice() else {
            panic!("expected the direct IIFE to inline to one return statement");
        };
        match &stmt.desc {
            StatementDesc::Return(Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            }) => assert!(id.same(&value)),
            other => panic!("expected the direct IIFE to inline to `return value`, got {other:?}"),
        }
    }

    #[test]
    fn js_tailcall_inline_preserves_shadowed_returned_function_params() {
        let run = Ident::create_local("run");
        let outer_param = Ident::create_local("extra");
        let inner_param = Ident::create_local("extra");
        let deps = apply_js_tailcall_inline_pass(DepsProgram {
            program: Program::new(
                vec![Statement::variable(VariableDeclaration {
                    ident: run.clone(),
                    value: Some(Expression::new(ExpressionDesc::Fun {
                        is_method: false,
                        params: vec![],
                        body: vec![Statement::return_(Expression::call(
                            Expression::new(ExpressionDesc::Fun {
                                is_method: false,
                                params: vec![outer_param.clone()],
                                body: vec![Statement::return_(Expression::new(
                                    ExpressionDesc::Fun {
                                        is_method: false,
                                        params: vec![inner_param.clone()],
                                        body: vec![Statement::return_(Expression::var(
                                            inner_param.clone(),
                                        ))],
                                        env: Default::default(),
                                        return_unit: false,
                                        async_: false,
                                        directive: None,
                                    },
                                ))],
                                env: Default::default(),
                                return_unit: false,
                                async_: false,
                                directive: None,
                            }),
                            vec![Expression::undefined(false)],
                            CallInfo::default(),
                        ))],
                        env: Default::default(),
                        return_unit: false,
                        async_: false,
                        directive: None,
                    })),
                    property: LetKind::Strict,
                    ident_info: IdentInfo::default(),
                })],
                vec![run.clone()],
            ),
            modules: vec![],
            side_effect: None,
        });
        let rendered = print_block(&deps.program.block);
        assert!(
            rendered.contains("return extra => extra;"),
            "expected the returned function parameter to survive tailcall inlining, got:\n{rendered}"
        );
        assert!(
            !rendered.contains("return extra => undefined;"),
            "unexpected shadowed-parameter rewrite during tailcall inlining:\n{rendered}"
        );
    }

    #[test]
    fn js_tailcall_inline_preserves_shadowed_block_bindings() {
        let run = Ident::create_local("run");
        let outer_param = Ident::create_local("value");
        let inner_binding = Ident::create_local("value");
        let deps = apply_js_tailcall_inline_pass(DepsProgram {
            program: Program::new(
                vec![Statement::variable(VariableDeclaration {
                    ident: run.clone(),
                    value: Some(Expression::new(ExpressionDesc::Fun {
                        is_method: false,
                        params: vec![],
                        body: vec![Statement::return_(Expression::call(
                            Expression::new(ExpressionDesc::Fun {
                                is_method: false,
                                params: vec![outer_param.clone()],
                                body: vec![
                                    Statement::variable(VariableDeclaration {
                                        ident: inner_binding.clone(),
                                        value: Some(Expression::number(Number::int(1))),
                                        property: LetKind::Strict,
                                        ident_info: IdentInfo::default(),
                                    }),
                                    Statement::return_(Expression::var(inner_binding.clone())),
                                ],
                                env: Default::default(),
                                return_unit: false,
                                async_: false,
                                directive: None,
                            }),
                            vec![Expression::undefined(false)],
                            CallInfo::default(),
                        ))],
                        env: Default::default(),
                        return_unit: false,
                        async_: false,
                        directive: None,
                    })),
                    property: LetKind::Strict,
                    ident_info: IdentInfo::default(),
                })],
                vec![run.clone()],
            ),
            modules: vec![],
            side_effect: None,
        });
        let rendered = print_block(&deps.program.block);
        assert!(
            rendered.contains("let value$1 = 1;"),
            "expected the shadowing binding to stay intact after inlining, got:\n{rendered}"
        );
        assert!(
            rendered.contains("return value$1;"),
            "expected the shadowing binding to stay visible after inlining, got:\n{rendered}"
        );
        assert!(
            !rendered.contains("return undefined;"),
            "unexpected shadowed-block rewrite during tailcall inlining:\n{rendered}"
        );
    }

    #[test]
    fn function_return_blocks_collapse_identity_module_wrapper_to_parameter() {
        let mut compiler = LambdaCompiler::new();
        let module_param = Ident::create_local("U");
        let field_alias = Ident::create_local("x");
        let loc = crate::location::Location::none();

        let compiled = compiler.compile_expr(&Lambda::Lfunction(crate::lambda::LFunction {
            arity: 1,
            params: vec![module_param.clone()],
            body: Box::new(Lambda::let_(
                LetKind::Alias,
                field_alias.clone(),
                Lambda::prim(
                    Primitive::Pfield(
                        0,
                        FieldDbgInfo::Module {
                            name: "x".to_string(),
                        },
                    ),
                    vec![Lambda::var(module_param.clone())],
                    loc.clone(),
                ),
                Lambda::prim(
                    Primitive::Pmakeblock(
                        0,
                        TagInfo::Module(vec!["x".to_string()]),
                        Mutable::Immutable,
                    ),
                    vec![Lambda::var(field_alias)],
                    loc,
                ),
            )),
            attr: crate::lambda::FunctionAttribute::default(),
        }));

        let Expression {
            desc: ExpressionDesc::Fun { body, .. },
            ..
        } = compiled.expr
        else {
            panic!("expected a function expression");
        };

        let [stmt] = body.as_slice() else {
            panic!("expected the identity module wrapper to collapse to one return statement");
        };
        match &stmt.desc {
            StatementDesc::Return(Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            }) if id.same(&module_param) => {}
            other => panic!("expected `return U`, got {other:?}"),
        }
    }

    #[test]
    fn function_return_blocks_collapse_inlined_identity_module_wrapper_to_parameter() {
        let mut compiler = LambdaCompiler::new();
        let module_param = Ident::create_local("U");
        let loc = crate::location::Location::none();

        let compiled = compiler.compile_expr(&Lambda::Lfunction(crate::lambda::LFunction {
            arity: 1,
            params: vec![module_param.clone()],
            body: Box::new(Lambda::prim(
                Primitive::Pmakeblock(
                    0,
                    TagInfo::Module(vec!["x".to_string()]),
                    Mutable::Immutable,
                ),
                vec![Lambda::prim(
                    Primitive::Pfield(
                        0,
                        FieldDbgInfo::Module {
                            name: "x".to_string(),
                        },
                    ),
                    vec![Lambda::var(module_param.clone())],
                    loc,
                )],
                crate::location::Location::none(),
            )),
            attr: crate::lambda::FunctionAttribute::default(),
        }));

        let Expression {
            desc: ExpressionDesc::Fun { body, .. },
            ..
        } = compiled.expr
        else {
            panic!("expected a function expression");
        };

        let [stmt] = body.as_slice() else {
            panic!("expected the inlined identity module wrapper to collapse to one return");
        };
        match &stmt.desc {
            StatementDesc::Return(Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            }) if id.same(&module_param) => {}
            other => panic!("expected `return U`, got {other:?}"),
        }
    }

    #[test]
    fn function_return_blocks_keep_non_identity_module_wrapper() {
        let mut compiler = LambdaCompiler::new();
        let left = Ident::create_local("Left");
        let right = Ident::create_local("Right");
        let left_alias = Ident::create_local("x");
        let right_alias = Ident::create_local("y");
        let loc = crate::location::Location::none();

        let compiled = compiler.compile_expr(&Lambda::Lfunction(crate::lambda::LFunction {
            arity: 2,
            params: vec![left.clone(), right.clone()],
            body: Box::new(Lambda::let_(
                LetKind::Alias,
                left_alias.clone(),
                Lambda::prim(
                    Primitive::Pfield(
                        0,
                        FieldDbgInfo::Module {
                            name: "x".to_string(),
                        },
                    ),
                    vec![Lambda::var(left.clone())],
                    loc.clone(),
                ),
                Lambda::let_(
                    LetKind::Alias,
                    right_alias.clone(),
                    Lambda::prim(
                        Primitive::Pfield(
                            1,
                            FieldDbgInfo::Module {
                                name: "y".to_string(),
                            },
                        ),
                        vec![Lambda::var(right.clone())],
                        loc.clone(),
                    ),
                    Lambda::prim(
                        Primitive::Pmakeblock(
                            0,
                            TagInfo::Module(vec!["x".to_string(), "y".to_string()]),
                            Mutable::Immutable,
                        ),
                        vec![Lambda::var(left_alias), Lambda::var(right_alias)],
                        loc,
                    ),
                ),
            )),
            attr: crate::lambda::FunctionAttribute::default(),
        }));

        let Expression {
            desc: ExpressionDesc::Fun { body, .. },
            ..
        } = compiled.expr
        else {
            panic!("expected a function expression");
        };

        assert_eq!(
            body.len(),
            3,
            "expected the mixed-target module wrapper to keep its alias bindings"
        );
    }

    #[test]
    fn js_flatten_and_mark_dead_rewrites_pre_marked_dead_bindings() {
        let dead_pure = Ident::create_local("deadPure");
        let dead_non_pure = Ident::create_local("deadNonPure");
        let callback = Ident::create_local("callback");
        let deps = apply_js_flatten_and_mark_dead_pass(
            DepsProgram {
                program: Program::new(
                    vec![
                        Statement::variable(VariableDeclaration {
                            ident: dead_pure,
                            value: Some(Expression::number(Number::int(1))),
                            property: LetKind::Strict,
                            ident_info: IdentInfo {
                                used_stats: UsedStats::DeadPure,
                            },
                        }),
                        Statement::variable(VariableDeclaration {
                            ident: dead_non_pure,
                            value: Some(Expression::call(
                                Expression::var(callback.clone()),
                                vec![],
                                CallInfo::default(),
                            )),
                            property: LetKind::Strict,
                            ident_info: IdentInfo {
                                used_stats: UsedStats::DeadNonPure,
                            },
                        }),
                    ],
                    vec![],
                ),
                modules: vec![],
                side_effect: None,
            },
            false,
        );

        let [first, second] = deps.program.block.as_slice() else {
            panic!("expected two rewritten statements");
        };
        match &first.desc {
            StatementDesc::Block(block) => assert!(block.is_empty()),
            other => {
                panic!("expected the dead pure binding to become an empty block, got {other:?}")
            }
        }
        match &second.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Call(func, args, _),
                ..
            }) => {
                assert!(args.is_empty());
                assert!(matches!(
                    func.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&callback)
                ));
            }
            other => panic!(
                "expected the dead impure binding to become an effect statement, got {other:?}"
            ),
        }
    }

    #[test]
    fn js_flatten_and_mark_dead_substitutes_immutable_caml_block_index_reads() {
        let tuple = Ident::create_local("tuple");
        let field = Ident::create_local("field");
        let callback = Ident::create_local("callback");
        let deps = apply_js_flatten_and_mark_dead_pass(
            DepsProgram {
                program: Program::new(
                    vec![
                        Statement::variable(VariableDeclaration {
                            ident: tuple.clone(),
                            value: Some(Expression::new(ExpressionDesc::CamlBlock(
                                vec![
                                    Expression::call(
                                        Expression::var(callback.clone()),
                                        vec![],
                                        CallInfo::default(),
                                    ),
                                    Expression::number(Number::int(2)),
                                ],
                                MutableFlag::Immutable,
                                Box::new(Expression::number(Number::int(0))),
                                TagInfo::tuple(),
                            ))),
                            property: LetKind::Strict,
                            ident_info: IdentInfo::default(),
                        }),
                        Statement::variable(VariableDeclaration {
                            ident: field,
                            value: Some(Expression::new(ExpressionDesc::ArrayIndex(
                                Box::new(Expression::var(tuple.clone())),
                                Box::new(Expression::number(Number::int(1))),
                            ))),
                            property: LetKind::Strict,
                            ident_info: IdentInfo::default(),
                        }),
                    ],
                    vec![],
                ),
                modules: vec![],
                side_effect: None,
            },
            false,
        );

        let [tuple_stmt, field_stmt] = deps.program.block.as_slice() else {
            panic!("expected the tuple binding and the rewritten projection");
        };

        let StatementDesc::Block(bindings) = &tuple_stmt.desc else {
            panic!("expected the tuple binding to expand into helper bindings");
        };
        let [helper_stmt, original_stmt] = bindings.as_slice() else {
            panic!("expected one helper binding plus the original tuple binding");
        };

        match &helper_stmt.desc {
            StatementDesc::Variable(VariableDeclaration {
                value:
                    Some(Expression {
                        desc: ExpressionDesc::Call(func, args, _),
                        ..
                    }),
                ..
            }) => {
                assert!(args.is_empty());
                assert!(matches!(
                    func.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&callback)
                ));
            }
            other => {
                panic!("expected the complex tuple field to become a helper binding, got {other:?}")
            }
        }
        match &original_stmt.desc {
            StatementDesc::Variable(VariableDeclaration {
                ident,
                value:
                    Some(Expression {
                        desc: ExpressionDesc::CamlBlock(items, MutableFlag::Immutable, _, _),
                        ..
                    }),
                ..
            }) => {
                assert!(ident.same(&tuple));
                assert!(matches!(
                    items.as_slice(),
                    [
                        Expression {
                            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(_)),
                            ..
                        },
                        Expression {
                            desc: ExpressionDesc::Number(Number::Int { i: 2, .. }),
                            ..
                        }
                    ]
                ));
            }
            other => panic!(
                "expected the original tuple binding to remain as a rewritten Caml block, got {other:?}"
            ),
        }
        match &field_stmt.desc {
            StatementDesc::Variable(VariableDeclaration {
                value:
                    Some(Expression {
                        desc: ExpressionDesc::Number(Number::Int { i: 2, .. }),
                        ..
                    }),
                ..
            }) => {}
            other => panic!(
                "expected the tuple projection to inline to the selected field, got {other:?}"
            ),
        }
    }

    #[test]
    fn js_flatten_and_mark_dead_keeps_pure_nested_immutable_caml_blocks_inline() {
        let list = Ident::create_local("list");
        let deps = apply_js_flatten_and_mark_dead_pass(
            DepsProgram {
                program: Program::new(
                    vec![Statement::variable(VariableDeclaration {
                        ident: list.clone(),
                        value: Some(Expression::new(ExpressionDesc::CamlBlock(
                            vec![
                                Expression::number(Number::int(2)),
                                Expression::new(ExpressionDesc::CamlBlock(
                                    vec![
                                        Expression::number(Number::int(3)),
                                        Expression::number(Number::int(0)),
                                    ],
                                    MutableFlag::Immutable,
                                    Box::new(Expression::number(Number::int(0))),
                                    TagInfo::Constructor {
                                        name: "::".to_string(),
                                        num_nonconst: 1,
                                        tag: 0,
                                        attrs: vec![],
                                    },
                                )),
                            ],
                            MutableFlag::Immutable,
                            Box::new(Expression::number(Number::int(0))),
                            TagInfo::Constructor {
                                name: "::".to_string(),
                                num_nonconst: 1,
                                tag: 0,
                                attrs: vec![],
                            },
                        ))),
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    })],
                    vec![],
                ),
                modules: vec![],
                side_effect: None,
            },
            false,
        );

        let [stmt] = deps.program.block.as_slice() else {
            panic!("expected the list binding to remain");
        };

        let StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::CamlBlock(items, MutableFlag::Immutable, _, _),
                    ..
                }),
            ..
        }) = &stmt.desc
        else {
            panic!("expected the pure nested list binding to stay inline");
        };
        assert!(ident.same(&list));
        assert!(matches!(
            items.as_slice(),
            [
                Expression {
                    desc: ExpressionDesc::Number(Number::Int { i: 2, .. }),
                    ..
                },
                Expression {
                    desc: ExpressionDesc::CamlBlock(inner, MutableFlag::Immutable, _, _),
                    ..
                }
            ] if matches!(
                inner.as_slice(),
                [
                    Expression {
                        desc: ExpressionDesc::Number(Number::Int { i: 3, .. }),
                        ..
                    },
                    Expression {
                        desc: ExpressionDesc::Number(Number::Int { i: 0, .. }),
                        ..
                    }
                ]
            )
        ));
    }

    #[test]
    fn js_flatten_and_mark_dead_substitutes_single_field_module_reads() {
        let module = Ident::create_local("M");
        let eq = Ident::create_local("Eq");
        let projected = Ident::create_local("EQ");
        let deps = apply_js_flatten_and_mark_dead_pass(
            DepsProgram {
                program: Program::new(
                    vec![
                        Statement::variable(VariableDeclaration {
                            ident: module.clone(),
                            value: Some(Expression::new(ExpressionDesc::CamlBlock(
                                vec![Expression::var(eq.clone())],
                                MutableFlag::Immutable,
                                Box::new(Expression::number(Number::int(0))),
                                TagInfo::Module(vec!["Eq".to_string()]),
                            ))),
                            property: LetKind::Strict,
                            ident_info: IdentInfo::default(),
                        }),
                        Statement::variable(VariableDeclaration {
                            ident: projected,
                            value: Some(Expression::new(ExpressionDesc::StaticIndex(
                                Box::new(Expression::var(module.clone())),
                                "Eq".to_string(),
                                Some(0),
                            ))),
                            property: LetKind::Strict,
                            ident_info: IdentInfo::default(),
                        }),
                    ],
                    vec![],
                ),
                modules: vec![],
                side_effect: None,
            },
            false,
        );

        let [module_stmt, projected_stmt] = deps.program.block.as_slice() else {
            panic!("expected the module binding and the rewritten projection");
        };
        match &module_stmt.desc {
            StatementDesc::Variable(VariableDeclaration {
                ident,
                value:
                    Some(Expression {
                        desc: ExpressionDesc::CamlBlock(items, MutableFlag::Immutable, _, _),
                        ..
                    }),
                ..
            }) => {
                assert!(ident.same(&module));
                assert!(matches!(
                    items.as_slice(),
                    [Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    }] if id.same(&eq)
                ));
            }
            other => {
                panic!("expected the single-field module binding to remain intact, got {other:?}")
            }
        }
        match &projected_stmt.desc {
            StatementDesc::Variable(VariableDeclaration {
                value:
                    Some(Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    }),
                ..
            }) if id.same(&eq) => {}
            other => panic!(
                "expected the single-field module projection to inline to the field value, got {other:?}"
            ),
        }
    }

    #[test]
    fn js_flatten_and_mark_dead_preserves_transformed_jsx_component_make_reads() {
        let module = Ident::create_local("Foo");
        let component = Ident::create_local("Async_jsx$Foo");
        let rendered = print_deps_program_with_directives(
            &apply_js_flatten_and_mark_dead_pass(
                DepsProgram {
                    program: Program::new(
                        vec![
                            Statement::variable(VariableDeclaration {
                                ident: module.clone(),
                                value: Some(Expression::new(ExpressionDesc::CamlBlock(
                                    vec![Expression::var(component.clone())],
                                    MutableFlag::Immutable,
                                    Box::new(Expression::number(Number::int(0))),
                                    TagInfo::Module(vec!["make".to_string()]),
                                ))),
                                property: LetKind::Strict,
                                ident_info: IdentInfo::default(),
                            }),
                            Statement::exp(Expression::call(
                                Expression::qualified(
                                    ModuleId {
                                        id: Ident::create_persistent("JsxRuntime"),
                                        kind: Kind::External {
                                            name: "react/jsx-runtime".to_string(),
                                            default: false,
                                            import_attributes: None,
                                        },
                                        dynamic_import: false,
                                    },
                                    Some("jsx".to_string()),
                                ),
                                vec![
                                    Expression::new(ExpressionDesc::StaticIndex(
                                        Box::new(Expression::var(module.clone())),
                                        "make".to_string(),
                                        Some(0),
                                    )),
                                    Expression::new(ExpressionDesc::CamlBlock(
                                        vec![],
                                        MutableFlag::Immutable,
                                        Box::new(Expression::number(Number::int(0))),
                                        TagInfo::record(
                                            vec![],
                                            crate::parser::ast::MutableFlag::Immutable,
                                        ),
                                    )),
                                ],
                                CallInfo {
                                    call_transformed_jsx: true,
                                    ..CallInfo::default()
                                },
                            )),
                        ],
                        vec![],
                    ),
                    modules: vec![],
                    side_effect: None,
                },
                true,
            ),
            None,
            &[],
            false,
            true,
        );

        assert!(
            rendered.contains("<Foo.make />"),
            "expected transformed JSX preserve mode to keep Foo.make visible:\n{rendered}"
        );
        assert!(
            !rendered.contains("<Async_jsx$Foo />"),
            "transformed JSX tag regressed to the component function value:\n{rendered}"
        );
    }

    #[test]
    fn js_flatten_and_mark_dead_does_not_preserve_component_make_reads_without_jsx_preserve() {
        let module = Ident::create_local("Foo");
        let component = Ident::create_local("Async_jsx$Foo");
        let rendered = print_deps_program(
            &apply_js_flatten_and_mark_dead_pass(
                DepsProgram {
                    program: Program::new(
                        vec![
                            Statement::variable(VariableDeclaration {
                                ident: module.clone(),
                                value: Some(Expression::new(ExpressionDesc::CamlBlock(
                                    vec![Expression::var(component.clone())],
                                    MutableFlag::Immutable,
                                    Box::new(Expression::number(Number::int(0))),
                                    TagInfo::Module(vec!["make".to_string()]),
                                ))),
                                property: LetKind::Strict,
                                ident_info: IdentInfo::default(),
                            }),
                            Statement::exp(Expression::call(
                                Expression::qualified(
                                    ModuleId {
                                        id: Ident::create_persistent("JsxRuntime"),
                                        kind: Kind::External {
                                            name: "react/jsx-runtime".to_string(),
                                            default: false,
                                            import_attributes: None,
                                        },
                                        dynamic_import: false,
                                    },
                                    Some("jsx".to_string()),
                                ),
                                vec![
                                    Expression::new(ExpressionDesc::StaticIndex(
                                        Box::new(Expression::var(module.clone())),
                                        "make".to_string(),
                                        Some(0),
                                    )),
                                    Expression::new(ExpressionDesc::CamlBlock(
                                        vec![],
                                        MutableFlag::Immutable,
                                        Box::new(Expression::number(Number::int(0))),
                                        TagInfo::record(
                                            vec![],
                                            crate::parser::ast::MutableFlag::Immutable,
                                        ),
                                    )),
                                ],
                                CallInfo {
                                    call_transformed_jsx: true,
                                    ..CallInfo::default()
                                },
                            )),
                        ],
                        vec![],
                    ),
                    modules: vec![],
                    side_effect: None,
                },
                false,
            ),
            None,
        );

        assert!(
            rendered.contains("JsxRuntime.jsx(Async_jsx$Foo, {})"),
            "without jsx preserve the single-field module projection should inline:\n{rendered}"
        );
        assert!(
            !rendered.contains("Foo.make"),
            "component .make read should not survive when jsx preserve is disabled:\n{rendered}"
        );
    }

    #[test]
    fn js_flatten_and_mark_dead_rebinds_sync_component_make_aliases_to_descriptive_names() {
        let make = Ident::create_local("make");
        let component = Ident::create_local("Jsx_preserve_test$B");
        let module = Ident::create_local("B");
        let props = Ident::create_local("props");
        let rendered = print_deps_program(
            &apply_js_flatten_and_mark_dead_pass(
                DepsProgram {
                    program: Program::new(
                        vec![
                            Statement::variable(VariableDeclaration {
                                ident: make.clone(),
                                value: Some(Expression::new(ExpressionDesc::Fun {
                                    is_method: false,
                                    params: vec![props],
                                    body: vec![Statement::return_(Expression::null())],
                                    env: Default::default(),
                                    return_unit: false,
                                    async_: false,
                                    directive: None,
                                })),
                                property: LetKind::Strict,
                                ident_info: IdentInfo::default(),
                            }),
                            Statement::variable(VariableDeclaration {
                                ident: component.clone(),
                                value: Some(Expression::var(make.clone())),
                                property: LetKind::Alias,
                                ident_info: IdentInfo::default(),
                            }),
                            Statement::variable(VariableDeclaration {
                                ident: module.clone(),
                                value: Some(Expression::new(ExpressionDesc::CamlBlock(
                                    vec![Expression::var(component.clone())],
                                    MutableFlag::Immutable,
                                    Box::new(Expression::number(Number::int(0))),
                                    TagInfo::Module(vec!["make".to_string()]),
                                ))),
                                property: LetKind::Strict,
                                ident_info: IdentInfo::default(),
                            }),
                        ],
                        vec![],
                    ),
                    modules: vec![],
                    side_effect: None,
                },
                true,
            ),
            None,
        );

        assert!(
            rendered.contains("function Jsx_preserve_test$B(props)"),
            "expected the descriptive component binding to own the function:\n{rendered}"
        );
        assert!(
            !rendered.contains("let Jsx_preserve_test$B = make;"),
            "component alias should collapse into the function declaration:\n{rendered}"
        );
        assert!(
            !rendered.contains("function make(props)"),
            "generic make binding should not survive for sync component aliases:\n{rendered}"
        );
    }

    #[test]
    fn js_flatten_and_mark_dead_keeps_async_component_make_aliases_materialized() {
        let make = Ident::create_local("make");
        let component = Ident::create_local("Async_jsx$Foo");
        let module = Ident::create_local("Foo");
        let param = Ident::create_local("param");
        let rendered = print_deps_program(
            &apply_js_flatten_and_mark_dead_pass(
                DepsProgram {
                    program: Program::new(
                        vec![
                            Statement::variable(VariableDeclaration {
                                ident: make.clone(),
                                value: Some(Expression::new(ExpressionDesc::Fun {
                                    is_method: false,
                                    params: vec![param],
                                    body: vec![Statement::return_(Expression::null())],
                                    env: Default::default(),
                                    return_unit: false,
                                    async_: true,
                                    directive: None,
                                })),
                                property: LetKind::Strict,
                                ident_info: IdentInfo::default(),
                            }),
                            Statement::variable(VariableDeclaration {
                                ident: component.clone(),
                                value: Some(Expression::var(make.clone())),
                                property: LetKind::Alias,
                                ident_info: IdentInfo::default(),
                            }),
                            Statement::variable(VariableDeclaration {
                                ident: module,
                                value: Some(Expression::new(ExpressionDesc::CamlBlock(
                                    vec![Expression::var(component.clone())],
                                    MutableFlag::Immutable,
                                    Box::new(Expression::number(Number::int(0))),
                                    TagInfo::Module(vec!["make".to_string()]),
                                ))),
                                property: LetKind::Strict,
                                ident_info: IdentInfo::default(),
                            }),
                        ],
                        vec![],
                    ),
                    modules: vec![],
                    side_effect: None,
                },
                true,
            ),
            None,
        );

        assert!(
            rendered.contains("async function make(param)"),
            "async component binding should keep the original make function:\n{rendered}"
        );
        assert!(
            rendered.contains("let Async_jsx$Foo = make;"),
            "async component alias should remain materialized:\n{rendered}"
        );
        assert!(
            !rendered.contains("async function Async_jsx$Foo(param)"),
            "async component function should not be rebound to the descriptive alias:\n{rendered}"
        );
    }

    #[test]
    fn js_flatten_and_mark_dead_keeps_identity_optional_record_fields_inline() {
        let record = Ident::create_local("x");
        let deps = apply_js_flatten_and_mark_dead_pass(
            DepsProgram {
                program: Program::new(
                    vec![Statement::variable(VariableDeclaration {
                        ident: record.clone(),
                        value: Some(Expression::new(ExpressionDesc::CamlBlock(
                            vec![
                                Expression::undefined(false),
                                Expression::new(ExpressionDesc::OptionalBlock(
                                    Box::new(Expression::string("test".to_string())),
                                    true,
                                )),
                                Expression::undefined(false),
                                Expression::undefined(false),
                                Expression::new(ExpressionDesc::OptionalBlock(
                                    Box::new(Expression::string("test".to_string())),
                                    true,
                                )),
                                Expression::undefined(false),
                            ],
                            MutableFlag::Immutable,
                            Box::new(Expression::number(Number::int(0))),
                            TagInfo::Record {
                                fields: vec![
                                    ("id".to_string(), true),
                                    ("name".to_string(), true),
                                    ("title".to_string(), true),
                                    ("className".to_string(), true),
                                    ("x".to_string(), true),
                                    ("y".to_string(), true),
                                ],
                                mutable_flag: crate::parser::ast::MutableFlag::Immutable,
                            },
                        ))),
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    })],
                    vec![],
                ),
                modules: vec![],
                side_effect: None,
            },
            false,
        );

        let [record_stmt] = deps.program.block.as_slice() else {
            panic!("expected the record binding to stay as a single declaration");
        };
        match &record_stmt.desc {
            StatementDesc::Variable(VariableDeclaration {
                ident,
                value:
                    Some(Expression {
                        desc: ExpressionDesc::CamlBlock(items, MutableFlag::Immutable, _, _),
                        ..
                    }),
                ..
            }) => {
                assert!(ident.same(&record));
                assert!(matches!(
                    items.as_slice(),
                    [
                        Expression {
                            desc: ExpressionDesc::Undefined { .. },
                            ..
                        },
                        Expression {
                            desc: ExpressionDesc::OptionalBlock(_, true),
                            ..
                        },
                        Expression {
                            desc: ExpressionDesc::Undefined { .. },
                            ..
                        },
                        Expression {
                            desc: ExpressionDesc::Undefined { .. },
                            ..
                        },
                        Expression {
                            desc: ExpressionDesc::OptionalBlock(_, true),
                            ..
                        },
                        Expression {
                            desc: ExpressionDesc::Undefined { .. },
                            ..
                        }
                    ]
                ));
            }
            other => panic!("expected the optional record binding to remain inline, got {other:?}"),
        }
    }

    #[test]
    fn js_flatten_and_mark_dead_marks_unused_nested_pure_bindings() {
        let run = Ident::create_local("run");
        let unused = Ident::create_local("unused");
        let used = Ident::create_local("used");
        let deps = apply_js_flatten_and_mark_dead_pass(
            DepsProgram {
                program: Program::new(
                    vec![Statement::variable(VariableDeclaration {
                        ident: run,
                        value: Some(Expression::new(ExpressionDesc::Fun {
                            is_method: false,
                            params: vec![],
                            body: vec![
                                Statement::variable(VariableDeclaration {
                                    ident: unused.clone(),
                                    value: Some(Expression::number(Number::int(1))),
                                    property: LetKind::Strict,
                                    ident_info: IdentInfo::default(),
                                }),
                                Statement::variable(VariableDeclaration {
                                    ident: used.clone(),
                                    value: Some(Expression::number(Number::int(2))),
                                    property: LetKind::Strict,
                                    ident_info: IdentInfo::default(),
                                }),
                                Statement::return_(Expression::var(used.clone())),
                            ],
                            env: Default::default(),
                            return_unit: false,
                            async_: false,
                            directive: None,
                        })),
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    })],
                    vec![],
                ),
                modules: vec![],
                side_effect: None,
            },
            false,
        );

        let [stmt] = deps.program.block.as_slice() else {
            panic!("expected one top-level function binding");
        };
        let StatementDesc::Variable(VariableDeclaration {
            value:
                Some(Expression {
                    desc: ExpressionDesc::Fun { body, .. },
                    ..
                }),
            ..
        }) = &stmt.desc
        else {
            panic!("expected a function-valued binding");
        };
        let [unused_stmt, used_stmt, _] = body.as_slice() else {
            panic!("expected two nested bindings followed by a return");
        };
        match &unused_stmt.desc {
            StatementDesc::Variable(VariableDeclaration { ident_info, .. }) => {
                assert_eq!(ident_info.used_stats, UsedStats::DeadPure);
            }
            other => panic!(
                "expected the first nested binding to remain a variable declaration, got {other:?}"
            ),
        }
        match &used_stmt.desc {
            StatementDesc::Variable(VariableDeclaration { ident_info, .. }) => {
                assert_eq!(ident_info.used_stats, UsedStats::Used);
            }
            other => panic!(
                "expected the used nested binding to remain a variable declaration, got {other:?}"
            ),
        }
    }

    #[test]
    fn lowers_js_var_without_args_to_a_value() {
        let mut compiler = LambdaCompiler::new();
        let lam = Lambda::prim(
            Primitive::PjsCall {
                prim_name: "process".to_string(),
                arg_types: vec![],
                ffi: ExternalFfiSpec {
                    kind: ExternalFfiKind::Default,
                    spec: Some(ExternalSpec::JsVar {
                        name: "process".to_string(),
                        external_module_name: None,
                        scopes: vec![],
                    }),
                    obj_params: None,
                    return_wrapper: ExternalReturnWrapper::Identity,
                    inline_constant: None,
                },
                dynamic_import: false,
                transformed_jsx: false,
            },
            vec![],
            Location::none(),
        );

        let compiled = compiler.compile_expr(&lam);
        assert!(compiled.prelude.is_empty());
        assert!(matches!(
            compiled.expr,
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(ref id)),
                ..
            } if id.name() == "process"
        ));
    }

    #[test]
    fn lowers_js_var_calls_with_runtime_args_even_without_external_arg_metadata() {
        let mut compiler = LambdaCompiler::new();
        let lam = Lambda::prim(
            Primitive::PjsCall {
                prim_name: "foo1".to_string(),
                arg_types: vec![],
                ffi: ExternalFfiSpec {
                    kind: ExternalFfiKind::Default,
                    spec: Some(ExternalSpec::JsVar {
                        name: "foo1".to_string(),
                        external_module_name: None,
                        scopes: vec![],
                    }),
                    obj_params: None,
                    return_wrapper: ExternalReturnWrapper::Identity,
                    inline_constant: None,
                },
                dynamic_import: false,
                transformed_jsx: false,
            },
            vec![Lambda::Lconst(Constant::Int {
                i: 10,
                comment: None,
            })],
            Location::none(),
        );

        let program = compiler.compile_program(&lam);
        let [stmt] = program.block.as_slice() else {
            panic!("expected a single expression statement");
        };
        match &stmt.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Call(func, args, _),
                ..
            }) => {
                assert_eq!(args.len(), 1);
                assert!(matches!(
                    func.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.name() == "foo1"
                ));
                assert!(matches!(
                    args[0],
                    Expression {
                        desc: ExpressionDesc::Number(Number::Int { i: 10, .. }),
                        ..
                    }
                ));
            }
            other => panic!("expected a direct js-var call, got {other:?}"),
        }
    }

    #[test]
    fn lowers_module_external_calls_to_namespace_imports() {
        let mut compiler = LambdaCompiler::new();
        let lam = Lambda::prim(
            Primitive::PjsCall {
                prim_name: "describe".to_string(),
                arg_types: vec![],
                ffi: ExternalFfiSpec {
                    kind: ExternalFfiKind::Default,
                    spec: Some(ExternalSpec::JsCall {
                        name: "describe".to_string(),
                        external_module_name: Some(external_module("mocha")),
                        splice: false,
                        scopes: vec![],
                        tagged_template: false,
                    }),
                    obj_params: None,
                    return_wrapper: ExternalReturnWrapper::Identity,
                    inline_constant: None,
                },
                dynamic_import: false,
                transformed_jsx: false,
            },
            vec![],
            Location::none(),
        );

        let deps = compiler.compile_deps_program(&lam);
        assert!(matches!(
            deps.modules.as_slice(),
            [ModuleId {
                kind: Kind::External { name, default, .. },
                ..
            }] if name == "mocha" && !default
        ));

        let [stmt] = deps.program.block.as_slice() else {
            panic!("expected a single expression statement");
        };
        match &stmt.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Call(func, args, _),
                ..
            }) => {
                assert!(args.is_empty());
                assert!(matches!(
                    func.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(
                            ModuleId {
                                kind: Kind::External { name, default, .. },
                                ..
                            },
                            Some(field),
                        )),
                        ..
                    } if field == "describe" && name == "mocha" && !default
                ));
            }
            other => panic!("expected external module call, got {other:?}"),
        }
    }

    #[test]
    fn translates_external_module_values_to_qualified_members_like_ocaml() {
        let mut compiler = LambdaCompiler::new();
        let expr = compiler.translate_scoped_module_value(
            Some(&external_module("react/jsx-runtime")),
            "jsx",
            &[],
            false,
        );

        assert!(matches!(
            expr,
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(
                    ModuleId {
                        kind: Kind::External {
                            name: ref name,
                            default,
                            ..
                        },
                        ..
                    },
                    Some(ref member),
                )),
                ..
            } if name == "react/jsx-runtime" && !default && member == "jsx"
        ));
        assert_eq!(print_expression(&expr), "JsxRuntime.jsx");
    }

    #[test]
    fn lowers_pjs_unsafe_downgrade_getters_to_method_calls() {
        let mut compiler = LambdaCompiler::new();
        let john = Ident::create_persistent("john");
        let lam = Lambda::Lapply(Apply {
            ap_func: Box::new(Lambda::prim(
                Primitive::PjsUnsafeDowngrade {
                    name: "say".to_string(),
                    setter: false,
                },
                vec![Lambda::var(john.clone())],
                Location::none(),
            )),
            ap_args: vec![
                Lambda::const_(Constant::String {
                    s: "hey".to_string(),
                    delim: None,
                }),
                Lambda::const_(Constant::String {
                    s: "jude".to_string(),
                    delim: None,
                }),
            ],
            ap_info: ApInfo {
                loc: Location::none(),
                inlined: InlineAttribute::Default,
                status: ApplyStatus::Uncurry,
            },
            ap_transformed_jsx: false,
        });

        let program = compiler.compile_program(&lam);
        let rendered = print_block(&program.block);
        assert_eq!(rendered, "john.say(\"hey\", \"jude\");");
    }

    #[test]
    fn lowers_pjs_unsafe_downgrade_setters_to_property_assignments() {
        let mut compiler = LambdaCompiler::new();
        let student = Ident::create_persistent("student1");
        let lam = Lambda::prim(
            Primitive::PjsUnsafeDowngrade {
                name: "name".to_string(),
                setter: true,
            },
            vec![
                Lambda::var(student),
                Lambda::const_(Constant::String {
                    s: "Mary".to_string(),
                    delim: None,
                }),
            ],
            Location::none(),
        );

        let program = compiler.compile_program(&lam);
        let rendered = print_block(&program.block);
        assert_eq!(rendered, "student1.name = \"Mary\";");
    }

    #[test]
    fn top_level_record_field_assignments_on_pure_fresh_literals_collapse_to_rhs_effects() {
        let mut compiler = LambdaCompiler::new();
        let lam = Lambda::seq(
            Lambda::prim(
                Primitive::Psetfield(0, SetFieldDbgInfo::RecordSet("x".to_string())),
                vec![
                    Lambda::prim(
                        Primitive::Pmakeblock(
                            0,
                            TagInfo::Record {
                                fields: vec![("x".to_string(), false)],
                                mutable_flag: crate::parser::ast::MutableFlag::Mutable,
                            },
                            Mutable::Immutable,
                        ),
                        vec![Lambda::const_(Constant::int(3))],
                        Location::none(),
                    ),
                    Lambda::Lsequence(
                        Box::new(Lambda::prim(
                            Primitive::PrawJsCode(crate::lambda::primitive::JsRawInfo {
                                code: "console.log(\"hi\")".to_string(),
                                is_stmt: true,
                            }),
                            vec![],
                            Location::none(),
                        )),
                        Box::new(Lambda::const_(Constant::int(2))),
                    ),
                ],
                Location::none(),
            ),
            Lambda::unit(),
        );

        let rendered = print_block(&compiler.compile_program(&lam).block);
        assert!(
            rendered.contains("console.log(\"hi\")"),
            "expected the sequenced logging effect to remain, got:\n{rendered}"
        );
        assert!(
            !rendered.contains(".x = 2;"),
            "did not expect a dead assignment to a pure fresh record literal, got:\n{rendered}"
        );
    }

    #[test]
    fn source_record_field_assignments_on_pure_fresh_literals_collapse_to_rhs_effects() {
        let source = r#"
@val external log: string => unit = "console.log"
type u = {mutable x: int}

{x: 3}.x = {
  log("hi")
  2
}
"#;

        let output = crate::driver::compile_source_to_js(source, "fresh_record_set.res").unwrap();
        assert!(
            output.contains("console.log(\"hi\");"),
            "expected the RHS effect to survive source compilation, got:\n{output}"
        );
        assert!(
            !output.contains("}).x = 2;"),
            "did not expect a dead assignment to a pure fresh record literal, got:\n{output}"
        );
    }

    #[test]
    fn source_record_field_assignments_on_impure_fresh_literals_keep_the_assignment() {
        let source = r#"
@val external log: string => unit = "console.log"
type u = {mutable x: int}

let f = x =>
  {
    x: {
      log("hi")
      x
    },
  }.x = x + 1
"#;

        let output =
            crate::driver::compile_source_to_js(source, "fresh_record_set_impure.res").unwrap();
        assert!(
            output.contains("console.log(\"hi\")"),
            "expected the impure target initializer to stay visible, got:\n{output}"
        );
        assert!(
            output.contains("}).x = x + 1 | 0;"),
            "expected impure fresh-record assignments to stay materialized, got:\n{output}"
        );
    }

    #[test]
    fn lowers_spliced_js_calls_by_flattening_literal_variadic_arrays() {
        let mut compiler = LambdaCompiler::new();
        let lam = Lambda::prim(
            Primitive::PjsCall {
                prim_name: "join".to_string(),
                arg_types: vec![ExternalArgSpec::dummy()],
                ffi: ExternalFfiSpec {
                    kind: ExternalFfiKind::Default,
                    spec: Some(ExternalSpec::JsCall {
                        name: "join".to_string(),
                        external_module_name: Some(external_module("path")),
                        splice: true,
                        scopes: vec![],
                        tagged_template: false,
                    }),
                    obj_params: None,
                    return_wrapper: ExternalReturnWrapper::Identity,
                    inline_constant: None,
                },
                dynamic_import: false,
                transformed_jsx: false,
            },
            vec![Lambda::prim(
                Primitive::Pmakearray,
                vec![
                    Lambda::const_(Constant::String {
                        s: ".".to_string(),
                        delim: None,
                    }),
                    Lambda::const_(Constant::String {
                        s: "Node_path_test".to_string(),
                        delim: None,
                    }),
                ],
                Location::none(),
            )],
            Location::none(),
        );

        let program = compiler.compile_program(&lam);
        let rendered = print_block(&program.block);
        assert_eq!(rendered, "Path.join(\".\", \"Node_path_test\");");
    }

    #[test]
    fn lowers_default_module_values_in_dynamic_imports() {
        let mut compiler = LambdaCompiler::new();
        let external_value = Lambda::prim(
            Primitive::PjsCall {
                prim_name: "default".to_string(),
                arg_types: vec![],
                ffi: ExternalFfiSpec {
                    kind: ExternalFfiKind::Default,
                    spec: Some(ExternalSpec::JsVar {
                        name: "default".to_string(),
                        external_module_name: Some(external_module("a")),
                        scopes: vec![],
                    }),
                    obj_params: None,
                    return_wrapper: ExternalReturnWrapper::Identity,
                    inline_constant: None,
                },
                dynamic_import: false,
                transformed_jsx: false,
            },
            vec![],
            Location::none(),
        );
        let program = compiler.compile_program(&Lambda::prim(
            Primitive::Pimport,
            vec![external_value],
            Location::none(),
        ));
        let rendered = print_block(&program.block);
        assert_eq!(rendered, "import(\"a\").then(m => m.default);");
    }

    #[test]
    fn lowers_unit_returning_default_module_functions_in_dynamic_imports() {
        let mut compiler = LambdaCompiler::new();
        let param = Ident::create_local("prim");
        let eta_expanded_default = Lambda::Lfunction(crate::lambda::LFunction {
            arity: 1,
            params: vec![param.clone()],
            body: Box::new(Lambda::seq(
                Lambda::prim(
                    Primitive::PjsCall {
                        prim_name: "default".to_string(),
                        arg_types: vec![ExternalArgSpec::dummy()],
                        ffi: ExternalFfiSpec {
                            kind: ExternalFfiKind::Default,
                            spec: Some(ExternalSpec::JsVar {
                                name: "default".to_string(),
                                external_module_name: Some(external_module("b")),
                                scopes: vec![],
                            }),
                            obj_params: None,
                            return_wrapper: ExternalReturnWrapper::Identity,
                            inline_constant: None,
                        },
                        dynamic_import: false,
                        transformed_jsx: false,
                    },
                    vec![Lambda::var(param)],
                    Location::none(),
                ),
                Lambda::const_(Constant::JsUndefined { is_unit: true }),
            )),
            attr: crate::lambda::FunctionAttribute::default(),
        });
        let program = compiler.compile_program(&Lambda::prim(
            Primitive::Pimport,
            vec![eta_expanded_default],
            Location::none(),
        ));

        let rendered = print_block(&program.block);
        assert_eq!(rendered, "import(\"b\").then(m => m.default);");
    }

    #[test]
    fn lowers_js_new_to_new_expression() {
        let mut compiler = LambdaCompiler::new();
        let arg = Ident::create_local("prim");
        let lam = Lambda::prim(
            Primitive::PjsCall {
                prim_name: "URL".to_string(),
                arg_types: vec![],
                ffi: ExternalFfiSpec {
                    kind: ExternalFfiKind::Default,
                    spec: Some(ExternalSpec::JsNew {
                        name: "URL".to_string(),
                        external_module_name: None,
                        splice: false,
                        scopes: vec![],
                    }),
                    obj_params: None,
                    return_wrapper: ExternalReturnWrapper::Identity,
                    inline_constant: None,
                },
                dynamic_import: false,
                transformed_jsx: false,
            },
            vec![Lambda::var(arg.clone())],
            Location::none(),
        );

        let program = compiler.compile_program(&lam);
        let [stmt] = program.block.as_slice() else {
            panic!("expected a single expression statement");
        };
        match &stmt.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::New(ctor, Some(args)),
                ..
            }) => {
                assert!(matches!(
                    ctor.desc,
                    ExpressionDesc::Var(crate::js_ir::VIdent::Id(ref id)) if id.name() == "URL"
                ));
                assert!(matches!(
                    args.as_slice(),
                    [Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    }] if id.same(&arg)
                ));
            }
            other => panic!("expected a new expression, got {other:?}"),
        }
    }

    #[test]
    fn lowers_js_call_omits_trailing_optional_undefined_args_like_ocaml() {
        let mut compiler = LambdaCompiler::new();
        let date = Ident::create_local("date");
        let lam = Lambda::prim(
            Primitive::PjsCall {
                prim_name: "formatDate".to_string(),
                arg_types: vec![
                    ExternalArgSpec {
                        arg_type: ExternalArgAttr::Nothing,
                        arg_label: ExternalArgLabel::Empty,
                    },
                    ExternalArgSpec {
                        arg_type: ExternalArgAttr::Nothing,
                        arg_label: ExternalArgLabel::Optional,
                    },
                    ExternalArgSpec {
                        arg_type: ExternalArgAttr::Nothing,
                        arg_label: ExternalArgLabel::Optional,
                    },
                ],
                ffi: ExternalFfiSpec {
                    kind: ExternalFfiKind::Default,
                    spec: Some(ExternalSpec::JsCall {
                        name: "formatDate".to_string(),
                        external_module_name: Some(external_module("SomeModule")),
                        splice: false,
                        scopes: vec![],
                        tagged_template: false,
                    }),
                    obj_params: None,
                    return_wrapper: ExternalReturnWrapper::Identity,
                    inline_constant: None,
                },
                dynamic_import: false,
                transformed_jsx: false,
            },
            vec![
                Lambda::var(date.clone()),
                Lambda::const_(Constant::JsUndefined { is_unit: false }),
                Lambda::const_(Constant::JsUndefined { is_unit: false }),
            ],
            Location::none(),
        );

        let simplified = crate::lambda::simplify::simplify_for_js_backend(&lam);
        let compiled = compiler.compile_expr(&simplified);
        let rendered = if compiled.prelude.is_empty() {
            print_expression(&compiled.expr)
        } else {
            print_block(&compiled.prelude)
        };
        assert_eq!(rendered, "SomeModule.formatDate(date);");
    }

    #[test]
    fn lowers_js_send_omits_trailing_optional_undefined_args_like_ocaml() {
        let mut compiler = LambdaCompiler::new();
        let lam = Lambda::prim(
            Primitive::PjsCall {
                prim_name: "toString".to_string(),
                arg_types: vec![
                    ExternalArgSpec {
                        arg_type: ExternalArgAttr::Nothing,
                        arg_label: ExternalArgLabel::Empty,
                    },
                    ExternalArgSpec {
                        arg_type: ExternalArgAttr::Nothing,
                        arg_label: ExternalArgLabel::Optional,
                    },
                ],
                ffi: ExternalFfiSpec {
                    kind: ExternalFfiKind::Default,
                    spec: Some(ExternalSpec::JsSend {
                        name: "toString".to_string(),
                        splice: false,
                        js_send_scopes: vec![],
                    }),
                    obj_params: None,
                    return_wrapper: ExternalReturnWrapper::Identity,
                    inline_constant: None,
                },
                dynamic_import: false,
                transformed_jsx: false,
            },
            vec![
                Lambda::const_(Constant::Float("42.".to_string())),
                Lambda::const_(Constant::JsUndefined { is_unit: false }),
            ],
            Location::none(),
        );

        let rendered = print_block(&compiler.compile_program(&lam).block);
        assert_eq!(rendered, "(42).toString();");
    }

    #[test]
    fn lowers_js_new_omits_trailing_optional_undefined_args_like_ocaml() {
        let mut compiler = LambdaCompiler::new();
        let lam = Lambda::prim(
            Primitive::PjsCall {
                prim_name: "RegExp".to_string(),
                arg_types: vec![
                    ExternalArgSpec {
                        arg_type: ExternalArgAttr::Nothing,
                        arg_label: ExternalArgLabel::Empty,
                    },
                    ExternalArgSpec {
                        arg_type: ExternalArgAttr::Nothing,
                        arg_label: ExternalArgLabel::Optional,
                    },
                ],
                ffi: ExternalFfiSpec {
                    kind: ExternalFfiKind::Default,
                    spec: Some(ExternalSpec::JsNew {
                        name: "RegExp".to_string(),
                        external_module_name: None,
                        splice: false,
                        scopes: vec![],
                    }),
                    obj_params: None,
                    return_wrapper: ExternalReturnWrapper::Identity,
                    inline_constant: None,
                },
                dynamic_import: false,
                transformed_jsx: false,
            },
            vec![
                Lambda::const_(Constant::String {
                    s: "ab+c".to_string(),
                    delim: None,
                }),
                Lambda::const_(Constant::JsUndefined { is_unit: false }),
            ],
            Location::none(),
        );

        let rendered = print_block(&compiler.compile_program(&lam).block);
        assert_eq!(rendered, "new RegExp(\"ab+c\");");
    }

    #[test]
    fn lowers_external_polyvar_string_and_int_args_like_ocaml() {
        let mut compiler = LambdaCompiler::new();
        let lam = Lambda::prim(
            Primitive::PjsCall {
                prim_name: "consume".to_string(),
                arg_types: vec![
                    ExternalArgSpec {
                        arg_type: ExternalArgAttr::PolyVarString {
                            descr: vec![
                                ("on_closed".to_string(), "on_closed".to_string()),
                                ("on_open".to_string(), "on_open".to_string()),
                                ("in_".to_string(), "in".to_string()),
                            ],
                        },
                        arg_label: ExternalArgLabel::Empty,
                    },
                    ExternalArgSpec {
                        arg_type: ExternalArgAttr::Int(vec![
                            ("on_closed".to_string(), 0),
                            ("on_open".to_string(), 3),
                            ("in_".to_string(), 4),
                        ]),
                        arg_label: ExternalArgLabel::Empty,
                    },
                ],
                ffi: ExternalFfiSpec {
                    kind: ExternalFfiKind::Default,
                    spec: Some(ExternalSpec::JsCall {
                        name: "consume".to_string(),
                        external_module_name: None,
                        splice: false,
                        scopes: vec![],
                        tagged_template: false,
                    }),
                    obj_params: None,
                    return_wrapper: ExternalReturnWrapper::Identity,
                    inline_constant: None,
                },
                dynamic_import: false,
                transformed_jsx: false,
            },
            vec![
                Lambda::const_(Constant::Pointer("in_".to_string())),
                Lambda::const_(Constant::Pointer("on_open".to_string())),
            ],
            Location::none(),
        );

        let rendered = print_block(&compiler.compile_program(&lam).block);
        assert_eq!(rendered, "consume(\"in\", 3);");
    }

    #[test]
    fn lowers_external_polyvar_payload_args_to_two_js_args_like_ocaml() {
        let mut compiler = LambdaCompiler::new();
        let lam = Lambda::prim(
            Primitive::PjsCall {
                prim_name: "handle".to_string(),
                arg_types: vec![ExternalArgSpec {
                    arg_type: ExternalArgAttr::PolyVar {
                        descr: Some(vec![("b".to_string(), "renamed".to_string())]),
                    },
                    arg_label: ExternalArgLabel::Empty,
                }],
                ffi: ExternalFfiSpec {
                    kind: ExternalFfiKind::Default,
                    spec: Some(ExternalSpec::JsCall {
                        name: "handle".to_string(),
                        external_module_name: None,
                        splice: false,
                        scopes: vec![],
                        tagged_template: false,
                    }),
                    obj_params: None,
                    return_wrapper: ExternalReturnWrapper::Identity,
                    inline_constant: None,
                },
                dynamic_import: false,
                transformed_jsx: false,
            },
            vec![Lambda::const_(Constant::Block {
                tag: 0,
                tag_info: TagInfo::PolyVar("b".to_string()),
                elements: vec![Constant::Pointer("b".to_string()), Constant::int(2)],
            })],
            Location::none(),
        );

        let rendered = print_block(&compiler.compile_program(&lam).block);
        assert_eq!(rendered, "handle(\"renamed\", 2);");
    }

    #[test]
    fn source_json_template_falls_back_to_regular_string_interpolation_like_ocaml() {
        let source = r#"
let x = json`some random ${"string"}`
"#;

        let output = crate::driver::compile_source_to_js(source, "json_template_test.res").unwrap();

        assert!(
            output.contains("let x = \"some random \" + \"string\";"),
            "expected ordinary string interpolation fallback, got:\n{output}"
        );
    }

    #[test]
    fn source_ref_aliases_survive_later_mutation_like_ocaml() {
        let source = r#"
let fib3 = n => {
  let a = ref(1)
  let b = ref(1)
  for i in 1 to n {
    let tmp = a.contents
    a := b.contents
    b := b.contents + tmp
  }
  a.contents
}
"#;

        let output = crate::driver::compile_source_to_js(source, "fib_ref_alias_test.res").unwrap();

        assert!(
            output.contains("let tmp = a;"),
            "expected the loop alias to remain materialized, got:\n{output}"
        );
        assert!(
            output.contains("b = b + tmp | 0;"),
            "expected the carried temp to feed the second assignment, got:\n{output}"
        );
        assert!(
            !output.contains("b = b + a | 0;"),
            "did not expect the carried temp to collapse to the reassigned binding:\n{output}"
        );
    }


    #[test]
    fn lowers_marshaled_constant_args_in_js_call() {
        let mut compiler = LambdaCompiler::new();
        let lam = Lambda::prim(
            Primitive::PjsCall {
                prim_name: "somefn".to_string(),
                arg_types: vec![ExternalArgSpec {
                    arg_type: ExternalArgAttr::ArgCst(ExternalArgConst::StringLit(
                        "{foo:true}".to_string(),
                        ExternalArgDelim::NoQuotes,
                    )),
                    arg_label: ExternalArgLabel::Empty,
                }],
                ffi: ExternalFfiSpec {
                    kind: ExternalFfiKind::Default,
                    spec: Some(ExternalSpec::JsCall {
                        name: "somefn".to_string(),
                        external_module_name: None,
                        splice: false,
                        scopes: vec!["somescope".to_string()],
                        tagged_template: false,
                    }),
                    obj_params: None,
                    return_wrapper: ExternalReturnWrapper::Identity,
                    inline_constant: None,
                },
                dynamic_import: false,
                transformed_jsx: false,
            },
            vec![],
            Location::none(),
        );

        let program = compiler.compile_program(&lam);
        let [stmt] = program.block.as_slice() else {
            panic!("expected a single expression statement");
        };
        match &stmt.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Call(func, args, _),
                ..
            }) => {
                assert!(matches!(
                    func.desc,
                    ExpressionDesc::StaticIndex(_, ref field, _)
                    if field == "somefn"
                ));
                assert!(matches!(
                    args.as_slice(),
                    [Expression {
                        desc: ExpressionDesc::Str {
                            delim: Delim::NoQuotes,
                            txt,
                        },
                        ..
                    }] if txt == "{foo:true}"
                ));
            }
            other => panic!("expected a JS call, got {other:?}"),
        }
    }

    #[test]
    fn lowers_js_object_create_with_marshaled_fields() {
        let mut compiler = LambdaCompiler::new();
        let name_ident = Ident::create_local("name");
        let compiled = compiler.compile_expr(&Lambda::prim(
            Primitive::PjsObjectCreate(vec![
                ExternalObjSpec {
                    obj_arg_type: ExternalArgAttr::ArgCst(ExternalArgConst::StringLit(
                        "false".to_string(),
                        ExternalArgDelim::NoQuotes,
                    )),
                    obj_arg_label: ExternalObjLabel::Label {
                        name: "objectMode".to_string(),
                    },
                },
                ExternalObjSpec {
                    obj_arg_type: ExternalArgAttr::Nothing,
                    obj_arg_label: ExternalObjLabel::Label {
                        name: "name".to_string(),
                    },
                },
                ExternalObjSpec {
                    obj_arg_type: ExternalArgAttr::ArgCst(ExternalArgConst::StringLit(
                        "true".to_string(),
                        ExternalArgDelim::NoQuotes,
                    )),
                    obj_arg_label: ExternalObjLabel::Label {
                        name: "someOther".to_string(),
                    },
                },
                ExternalObjSpec {
                    obj_arg_type: ExternalArgAttr::ExternUnit,
                    obj_arg_label: ExternalObjLabel::Empty,
                },
            ]),
            vec![
                Lambda::var(name_ident.clone()),
                Lambda::const_(Constant::JsUndefined { is_unit: true }),
            ],
            Location::none(),
        ));

        assert!(compiled.prelude.is_empty());
        match &compiled.expr.desc {
            ExpressionDesc::Object(_, props) => {
                assert_eq!(props.len(), 3);
                assert!(matches!(
                    &props[0],
                    (
                        PropertyName::Lit(name),
                        Expression {
                            desc: ExpressionDesc::Str {
                                delim: Delim::NoQuotes,
                                txt,
                            },
                            ..
                        },
                    ) if name == "objectMode" && txt == "false"
                ));
                assert!(matches!(
                    &props[1],
                    (
                        PropertyName::Lit(name),
                        Expression {
                            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                            ..
                        },
                    ) if name == "name" && id.same(&name_ident)
                ));
                assert!(matches!(
                    &props[2],
                    (
                        PropertyName::Lit(name),
                        Expression {
                            desc: ExpressionDesc::Str {
                                delim: Delim::NoQuotes,
                                txt,
                            },
                            ..
                        },
                    ) if name == "someOther" && txt == "true"
                ));
            }
            other => panic!("expected an object literal expression, got {other:?}"),
        }
    }

    #[test]
    fn lowers_js_object_create_with_polyvar_string_field_like_ocaml() {
        let mut compiler = LambdaCompiler::new();
        let compiled = compiler.compile_expr(&Lambda::prim(
            Primitive::PjsObjectCreate(vec![ExternalObjSpec {
                obj_arg_type: ExternalArgAttr::PolyVarString {
                    descr: vec![
                        ("lookup".to_string(), "lookup".to_string()),
                        ("best_fit".to_string(), "best fit".to_string()),
                    ],
                },
                obj_arg_label: ExternalObjLabel::Label {
                    name: "localeMatcher".to_string(),
                },
            }]),
            vec![Lambda::const_(Constant::Pointer("best_fit".to_string()))],
            Location::none(),
        ));

        assert!(compiled.prelude.is_empty());
        match &compiled.expr.desc {
            ExpressionDesc::Object(_, props) => {
                assert_eq!(props.len(), 1);
                assert!(matches!(
                    &props[0],
                    (
                        PropertyName::Lit(name),
                        Expression {
                            desc: ExpressionDesc::Str { txt, .. },
                            ..
                        },
                    ) if name == "localeMatcher" && txt == "best fit"
                ));
            }
            other => panic!("expected an object literal expression, got {other:?}"),
        }
    }

    #[test]
    fn lowers_js_object_create_with_optional_polyvar_string_field_inline_like_ocaml() {
        let mut compiler = LambdaCompiler::new();
        let compiled = compiler.compile_expr(&Lambda::prim(
            Primitive::PjsObjectCreate(vec![ExternalObjSpec {
                obj_arg_type: ExternalArgAttr::PolyVarString {
                    descr: vec![
                        ("numeric".to_string(), "numeric".to_string()),
                        ("two_digit".to_string(), "2-digit".to_string()),
                    ],
                },
                obj_arg_label: ExternalObjLabel::Optional {
                    name: "day".to_string(),
                    for_sure_no_nested_option: false,
                },
            }]),
            vec![Lambda::prim(
                Primitive::Psome,
                vec![Lambda::const_(Constant::Pointer("two_digit".to_string()))],
                Location::none(),
            )],
            Location::none(),
        ));

        assert!(compiled.prelude.is_empty());
        match &compiled.expr.desc {
            ExpressionDesc::Object(_, props) => {
                assert_eq!(props.len(), 1);
                assert!(matches!(
                    &props[0],
                    (
                        PropertyName::Lit(name),
                        Expression {
                            desc: ExpressionDesc::Str { txt, .. },
                            ..
                        },
                    ) if name == "day" && txt == "2-digit"
                ));
            }
            other => panic!("expected an object literal expression, got {other:?}"),
        }
    }

    #[test]
    fn bind_switch_scrutinee_once_uses_tmp_name_like_ocaml() {
        let mut compiler = LambdaCompiler::new();
        let (prelude, expr) = compiler.bind_switch_scrutinee_once(
            vec![],
            Expression::call(
                Expression::var(Ident::create_local("compute")),
                vec![Expression::number(Number::int(1))],
                CallInfo::default(),
            ),
        );

        let ExpressionDesc::Var(crate::js_ir::VIdent::Id(tmp_ident)) = &expr.desc else {
            panic!("expected the bound scrutinee expression to become a temp variable");
        };
        assert_eq!(tmp_ident.name(), "tmp");

        let [stmt] = prelude.as_slice() else {
            panic!("expected a single temp binding statement");
        };
        match &stmt.desc {
            StatementDesc::Variable(VariableDeclaration { ident, value, .. }) => {
                assert!(ident.same(tmp_ident));
                assert!(matches!(
                    value,
                    Some(Expression {
                        desc: ExpressionDesc::Call(_, args, _),
                        ..
                    }) if args.len() == 1
                ));
            }
            other => panic!("expected a temp binding variable statement, got {other:?}"),
        }
    }

    #[test]
    fn lowers_js_object_create_with_statically_present_optional_field_inline_like_ocaml() {
        let mut compiler = LambdaCompiler::new();
        let compiled = compiler.compile_expr(&Lambda::prim(
            Primitive::PjsObjectCreate(vec![ExternalObjSpec {
                obj_arg_type: ExternalArgAttr::Nothing,
                obj_arg_label: ExternalObjLabel::Optional {
                    name: "alt".to_string(),
                    for_sure_no_nested_option: false,
                },
            }]),
            vec![Lambda::prim(
                Primitive::Psome,
                vec![Lambda::const_(Constant::string("pic"))],
                Location::none(),
            )],
            Location::none(),
        ));

        assert!(compiled.prelude.is_empty());
        match &compiled.expr.desc {
            ExpressionDesc::Object(_, props) => {
                assert_eq!(props.len(), 1);
                assert!(matches!(
                    &props[0],
                    (
                        PropertyName::Lit(name),
                        Expression {
                            desc: ExpressionDesc::Str { txt, .. },
                            ..
                        },
                    ) if name == "alt" && txt == "pic"
                ));
            }
            other => panic!("expected an inline object literal expression, got {other:?}"),
        }
    }

    #[test]
    fn lowers_js_object_create_with_unknown_optional_field_to_conditional_assignment_like_ocaml() {
        let mut compiler = LambdaCompiler::new();
        let opt = Ident::create_local("opt");
        let compiled = compiler.compile_expr(&Lambda::prim(
            Primitive::PjsObjectCreate(vec![ExternalObjSpec {
                obj_arg_type: ExternalArgAttr::Nothing,
                obj_arg_label: ExternalObjLabel::Optional {
                    name: "alt".to_string(),
                    for_sure_no_nested_option: false,
                },
            }]),
            vec![Lambda::var(opt.clone())],
            Location::none(),
        ));

        let ExpressionDesc::Var(crate::js_ir::VIdent::Id(obj)) = &compiled.expr.desc else {
            panic!("expected the conditional path to return the temp object");
        };

        let [init_stmt, if_stmt] = compiled.prelude.as_slice() else {
            panic!("expected object init plus one conditional assignment");
        };

        match &init_stmt.desc {
            StatementDesc::Variable(VariableDeclaration {
                ident,
                value:
                    Some(Expression {
                        desc: ExpressionDesc::Object(_, props),
                        ..
                    }),
                ..
            }) => {
                assert!(ident.same(obj));
                assert!(props.is_empty());
            }
            other => panic!("expected an empty object temp, got {other:?}"),
        }

        match &if_stmt.desc {
            StatementDesc::If(cond, then_block, else_block) => {
                assert!(else_block.is_empty());
                assert!(matches!(
                    &cond.desc,
                    ExpressionDesc::Bin(
                        BinOp::NotEqEq,
                        left,
                        right,
                    ) if matches!(
                        left.as_ref(),
                        Expression {
                            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                            ..
                        } if id.same(&opt)
                    ) && matches!(
                        right.as_ref(),
                        Expression {
                            desc: ExpressionDesc::Undefined { is_unit: false },
                            ..
                        }
                    )
                ));

                let [assign_stmt] = then_block.as_slice() else {
                    panic!("expected one conditional assignment");
                };
                match &assign_stmt.desc {
                    StatementDesc::Exp(Expression {
                        desc: ExpressionDesc::Bin(BinOp::Eq, target, value),
                        ..
                    }) => {
                        assert!(matches!(
                            target.as_ref(),
                            Expression {
                                desc: ExpressionDesc::StaticIndex(target_obj, field, _),
                                ..
                            } if field == "alt"
                                && matches!(
                                    target_obj.as_ref(),
                                    Expression {
                                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                                        ..
                                    } if id.same(obj)
                                )
                        ));
                        assert_eq!(
                            print_expression(value),
                            "Primitive_option.valFromOption(opt)"
                        );
                    }
                    other => panic!("expected an object-field assignment, got {other:?}"),
                }
            }
            other => panic!("expected a conditional optional assignment, got {other:?}"),
        }
    }

    #[test]
    fn lowers_ignored_js_call_args_to_ocaml_sequence_effects() {
        let mut compiler = LambdaCompiler::new();
        let lam = Lambda::prim(
            Primitive::PjsCall {
                prim_name: "somefn".to_string(),
                arg_types: vec![
                    ExternalArgSpec {
                        arg_type: ExternalArgAttr::Ignore,
                        arg_label: ExternalArgLabel::Empty,
                    },
                    ExternalArgSpec {
                        arg_type: ExternalArgAttr::Nothing,
                        arg_label: ExternalArgLabel::Empty,
                    },
                ],
                ffi: ExternalFfiSpec {
                    kind: ExternalFfiKind::Default,
                    spec: Some(ExternalSpec::JsCall {
                        name: "somefn".to_string(),
                        external_module_name: None,
                        splice: false,
                        scopes: vec![],
                        tagged_template: false,
                    }),
                    obj_params: None,
                    return_wrapper: ExternalReturnWrapper::Identity,
                    inline_constant: None,
                },
                dynamic_import: false,
                transformed_jsx: false,
            },
            vec![
                Lambda::Lsequence(
                    Box::new(Lambda::prim(
                        Primitive::PrawJsCode(JsRawInfo {
                            code: "sideEffect()".to_string(),
                            is_stmt: false,
                        }),
                        vec![],
                        Location::none(),
                    )),
                    Box::new(Lambda::const_(Constant::string("Float"))),
                ),
                Lambda::const_(Constant::int(3)),
            ],
            Location::none(),
        );

        let compiled = compiler.compile_expr(&lam);
        assert!(
            compiled.prelude.is_empty(),
            "expected ignored-call effects to stay in the expression, got {:?}",
            compiled.prelude
        );
        let ExpressionDesc::Seq(left, call) = &compiled.expr.desc else {
            panic!("expected outer effect sequence, got {:?}", compiled.expr);
        };
        let ExpressionDesc::Seq(effect, kind) = &left.as_ref().desc else {
            panic!("expected nested ignored-arg sequence, got {:?}", left);
        };
        assert!(matches!(
            effect.as_ref(),
            Expression {
                desc: ExpressionDesc::RawJsCode(crate::js_ir::JsRawInfo {
                    code,
                    is_stmt: false,
                }),
                ..
            } if code == "sideEffect()"
        ));
        assert!(matches!(
            kind.as_ref(),
            Expression {
                desc: ExpressionDesc::Str { txt, .. },
                ..
            } if txt == "Float"
        ));
        match &call.as_ref().desc {
            ExpressionDesc::Call(func, args, _) => {
                assert!(matches!(func.as_ref().desc, ExpressionDesc::Var(_)));
                assert!(matches!(
                    args.as_slice(),
                    [Expression {
                        desc: ExpressionDesc::Number(Number::Int { i: 3, .. }),
                        ..
                    }]
                ));
            }
            other => panic!("expected a call expression, got {other:?}"),
        };
    }

    #[test]
    fn lowers_ignored_js_object_fields_to_ocaml_sequence_effects() {
        let mut compiler = LambdaCompiler::new();
        let lam = Lambda::prim(
            Primitive::PjsObjectCreate(vec![
                ExternalObjSpec {
                    obj_arg_type: ExternalArgAttr::Ignore,
                    obj_arg_label: ExternalObjLabel::Label {
                        name: "kind".to_string(),
                    },
                },
                ExternalObjSpec {
                    obj_arg_type: ExternalArgAttr::Nothing,
                    obj_arg_label: ExternalObjLabel::Label {
                        name: "hi".to_string(),
                    },
                },
            ]),
            vec![
                Lambda::Lsequence(
                    Box::new(Lambda::prim(
                        Primitive::PrawJsCode(JsRawInfo {
                            code: "sideEffect()".to_string(),
                            is_stmt: false,
                        }),
                        vec![],
                        Location::none(),
                    )),
                    Box::new(Lambda::const_(Constant::string("Float"))),
                ),
                Lambda::const_(Constant::int(3)),
            ],
            Location::none(),
        );

        let compiled = compiler.compile_expr(&lam);
        assert!(
            compiled.prelude.is_empty(),
            "expected ignored-object effects to stay in the expression, got {:?}",
            compiled.prelude
        );
        let ExpressionDesc::Seq(left, object) = &compiled.expr.desc else {
            panic!("expected outer effect sequence, got {:?}", compiled.expr);
        };
        assert!(matches!(
            left.as_ref(),
            Expression {
                desc: ExpressionDesc::Seq(effect, kind),
                ..
            } if matches!(
                effect.as_ref(),
                Expression {
                    desc: ExpressionDesc::RawJsCode(crate::js_ir::JsRawInfo {
                        code,
                        is_stmt: false,
                    }),
                    ..
                } if code == "sideEffect()"
            ) && matches!(
                kind.as_ref(),
                Expression {
                    desc: ExpressionDesc::Str { txt, .. },
                    ..
                } if txt == "Float"
            )
        ));
        match &object.as_ref().desc {
            ExpressionDesc::Object(_, props) => {
                assert_eq!(props.len(), 1);
                assert!(matches!(
                    &props[0],
                    (
                        PropertyName::Lit(name),
                        Expression {
                            desc: ExpressionDesc::Number(Number::Int { i: 3, .. }),
                            ..
                        },
                    ) if name == "hi"
                ));
            }
            other => panic!("expected an object literal expression, got {other:?}"),
        };
    }

    #[test]
    fn compile_deps_program_keeps_exported_dict_initializer_object_literals() {
        let mut compiler = LambdaCompiler::new();
        let dict_ident = Ident::create_local("stringDict");
        let dict_value = Lambda::prim(
            Primitive::Pmakedict,
            vec![Lambda::prim(
                Primitive::Pmakearray,
                vec![Lambda::prim(
                    Primitive::Pmakeblock(0, TagInfo::Tuple, Mutable::Immutable),
                    vec![
                        Lambda::const_(Constant::string("first")),
                        Lambda::const_(Constant::string("hello")),
                    ],
                    Location::none(),
                )],
                Location::none(),
            )],
            Location::none(),
        );
        let lam = Lambda::let_(
            LetKind::Strict,
            dict_ident.clone(),
            dict_value,
            Lambda::prim(
                Primitive::Pmakeblock(
                    0,
                    TagInfo::ModuleExport(vec![dict_ident.clone()]),
                    Mutable::Immutable,
                ),
                vec![Lambda::var(dict_ident.clone())],
                Location::none(),
            ),
        );

        let deps = compiler.compile_deps_program(&lam);

        let [stmt] = deps.program.block.as_slice() else {
            panic!("expected one exported dict binding");
        };
        match &stmt.desc {
            StatementDesc::Variable(VariableDeclaration {
                ident,
                value:
                    Some(Expression {
                        desc: ExpressionDesc::Object(_, props),
                        ..
                    }),
                ..
            }) => {
                assert!(ident.same(&dict_ident));
                assert_eq!(props.len(), 1);
                assert!(matches!(
                    &props[0],
                    (
                        PropertyName::Lit(name),
                        Expression {
                            desc: ExpressionDesc::Str { txt, .. },
                            ..
                        },
                    ) if name == "first" && txt == "hello"
                ));
            }
            other => panic!("expected exported dict object literal, got {other:?}"),
        }
    }

    #[test]
    fn collects_static_module_dependencies() {
        let mut compiler = LambdaCompiler::new();
        let deps = compiler.compile_deps_program(&Lambda::global_module(
            Ident::create_persistent("Belt_List"),
            false,
        ));

        assert_eq!(deps.modules.len(), 1);
        assert_eq!(deps.modules[0].id.name(), "Belt_List");
        assert!(!deps.modules[0].dynamic_import);
    }

    #[test]
    fn external_module_import_attributes_preserve_all_fields() {
        let module = ExternalModuleName {
            bundle: "./myJson.json".to_string(),
            module_bind_name: ExternalModuleBindName::Nothing,
            import_attributes: Some(vec![
                ("type".to_string(), "json".to_string()),
                ("some-identifier".to_string(), "yep".to_string()),
            ]),
        };

        let attrs = external_module_import_attributes(&module).expect("expected import attributes");

        assert_eq!(
            attrs.entries,
            vec![
                ("type".to_string(), "json".to_string()),
                ("some-identifier".to_string(), "yep".to_string()),
            ]
        );
    }

    #[test]
    fn skips_dynamic_import_only_possible_required_modules() {
        let mut compiler = LambdaCompiler::new();
        let extras = std::collections::HashSet::from([ModuleId {
            id: Ident::create_persistent("Side_effect"),
            kind: Kind::Ml,
            dynamic_import: true,
        }]);
        let deps =
            compiler.compile_deps_program_with_possible_required_modules(&Lambda::unit(), &extras);

        assert!(deps.modules.is_empty());
    }

    #[test]
    fn sorts_external_module_dependencies_by_module_name() {
        let compiler = LambdaCompiler::new();
        let block = vec![
            Statement::exp(Expression::qualified(
                ModuleId {
                    id: Ident::create_persistent("JsxRuntime"),
                    kind: Kind::External {
                        name: "react/jsx-runtime".to_string(),
                        default: false,
                        import_attributes: None,
                    },
                    dynamic_import: false,
                },
                None,
            )),
            Statement::exp(Expression::qualified(
                ModuleId {
                    id: Ident::create_persistent("ReactIntl"),
                    kind: Kind::External {
                        name: "react-intl".to_string(),
                        default: false,
                        import_attributes: None,
                    },
                    dynamic_import: false,
                },
                None,
            )),
        ];

        let modules = compiler.collect_required_modules(&block);

        assert_eq!(modules.len(), 2);
        assert_eq!(module_sort_name(&modules[0]), "react-intl");
        assert_eq!(module_sort_name(&modules[1]), "react/jsx-runtime");
    }

    #[test]
    fn sorts_required_modules_by_length_before_bytes() {
        let compiler = LambdaCompiler::new();
        let block = vec![
            Statement::exp(Expression::qualified(
                ModuleId {
                    id: Ident::create_persistent("Test_utils"),
                    kind: Kind::Ml,
                    dynamic_import: false,
                },
                None,
            )),
            Statement::exp(Expression::qualified(
                ModuleId {
                    id: Ident::create_persistent("Mocha"),
                    kind: Kind::External {
                        name: "mocha".to_string(),
                        default: false,
                        import_attributes: None,
                    },
                    dynamic_import: false,
                },
                None,
            )),
        ];

        let modules = compiler.collect_required_modules(&block);

        assert_eq!(modules.len(), 2);
        assert_eq!(module_sort_name(&modules[0]), "mocha");
        assert_eq!(module_sort_name(&modules[1]), "Test_utils");
    }

    #[test]
    fn required_modules_match_ocaml_sort_across_same_name_import_pairs() {
        let compiler = LambdaCompiler::new();
        let some_default = ModuleId {
            id: Ident::create_local("SomeEs6Module"),
            kind: Kind::External {
                name: "some-es6-module".to_string(),
                default: true,
                import_attributes: None,
            },
            dynamic_import: false,
        };
        let some_namespace = ModuleId {
            id: Ident::create_local("SomeEs6Module"),
            kind: Kind::External {
                name: "some-es6-module".to_string(),
                default: false,
                import_attributes: None,
            },
            dynamic_import: false,
        };
        let ome_default = ModuleId {
            id: Ident::create_local("OmeEs6Module"),
            kind: Kind::External {
                name: "./ome-es6-module".to_string(),
                default: true,
                import_attributes: None,
            },
            dynamic_import: false,
        };
        let ome_namespace = ModuleId {
            id: Ident::create_local("OmeEs6Module"),
            kind: Kind::External {
                name: "./ome-es6-module".to_string(),
                default: false,
                import_attributes: None,
            },
            dynamic_import: false,
        };
        let vscode = ModuleId {
            id: Ident::create_local("Vscode"),
            kind: Kind::External {
                name: "vscode".to_string(),
                default: false,
                import_attributes: None,
            },
            dynamic_import: false,
        };
        let block = vec![
            Statement::exp(Expression::qualified(some_default.clone(), None)),
            Statement::exp(Expression::qualified(
                some_namespace.clone(),
                Some("default2".to_string()),
            )),
            Statement::exp(Expression::qualified(ome_default.clone(), None)),
            Statement::exp(Expression::qualified(
                ome_namespace.clone(),
                Some("default2".to_string()),
            )),
            Statement::exp(Expression::qualified(
                vscode.clone(),
                Some("window".to_string()),
            )),
        ];

        let modules = compiler.collect_required_modules(&block);

        assert_eq!(
            modules,
            vec![
                vscode,
                some_namespace,
                some_default,
                ome_default,
                ome_namespace,
            ]
        );
    }

    #[test]
    fn required_module_effect_reason_uses_external_module_name() {
        let reason = required_module_side_effect_reason(
            None,
            &[ModuleId {
                id: Ident::create_persistent("GentTypeReTestGen"),
                kind: Kind::External {
                    name: "./gentTypeReTest.gen".to_string(),
                    default: false,
                    import_attributes: None,
                },
                dynamic_import: false,
            }],
        );

        assert_eq!(reason.as_deref(), Some("./gentTypeReTest.gen"));
    }

    #[test]
    fn pure_ml_dependencies_do_not_mark_module_impure() {
        let resolver = resolver_with_checked_in_cmj();
        let reason = required_module_side_effect_reason(
            Some(&resolver),
            &[ModuleId {
                id: Ident::create_persistent("Side_effect_free"),
                kind: Kind::Ml,
                dynamic_import: false,
            }],
        );

        assert_eq!(reason, None);
    }

    #[test]
    fn preserves_impure_side_effect_only_ml_dependencies_from_lambda() {
        let resolver = resolver_with_checked_in_cmj();
        let side_effect = Ident::create_persistent("Side_effect");
        let include_binding = Ident::create_local("include");
        let mut compiler = LambdaCompiler::with_module_path_resolver(Some(resolver));
        let deps = compiler.compile_deps_program(&Lambda::let_(
            LetKind::Alias,
            include_binding,
            Lambda::global_module(side_effect.clone(), false),
            Lambda::unit(),
        ));

        assert!(deps.program.block.is_empty());
        assert!(deps.program.exports.is_empty());
        assert_eq!(deps.modules.len(), 1);
        assert_eq!(deps.modules[0].id.name(), side_effect.name());
        assert_eq!(deps.modules[0].kind, Kind::Ml);
        assert_eq!(deps.side_effect.as_deref(), Some("Side_effect"));
    }

    #[test]
    fn impure_ml_dependencies_use_module_name_as_effect_reason() {
        let resolver = resolver_with_checked_in_cmj();
        let reason = required_module_side_effect_reason(
            Some(&resolver),
            &[ModuleId {
                id: Ident::create_persistent("Test_utils"),
                kind: Kind::Ml,
                dynamic_import: false,
            }],
        );

        assert_eq!(reason.as_deref(), Some("Test_utils"));
    }

    #[test]
    fn module_side_effect_reason_uses_first_impure_group_in_final_order_like_ocaml() {
        let first = Ident::create_local("first");
        let second = Ident::create_local("second");
        let lam = Lambda::let_(
            LetKind::Strict,
            first,
            Lambda::prim(Primitive::Pdebugger, vec![], Location::none()),
            Lambda::let_(
                LetKind::Strict,
                second.clone(),
                Lambda::prim(Primitive::Pdebugger, vec![], Location::none()),
                Lambda::unit(),
            ),
        );

        assert_eq!(module_side_effect_reason(&lam).as_deref(), Some("first"));
    }

    #[test]
    fn module_side_effect_reason_uses_binding_name_for_impure_group_bodies() {
        let match_id = Ident::create_local("match");
        let lam = Lambda::seq(
            Lambda::let_(
                LetKind::Strict,
                match_id.clone(),
                Lambda::prim(Primitive::Pdebugger, vec![], Location::none()),
                Lambda::unit(),
            ),
            Lambda::unit(),
        );

        assert_eq!(module_side_effect_reason(&lam).as_deref(), Some("match"));
    }

    #[test]
    fn module_side_effect_reason_keeps_empty_reason_for_impure_nops() {
        let lam = Lambda::seq(
            Lambda::prim(Primitive::Pdebugger, vec![], Location::none()),
            Lambda::unit(),
        );

        assert_eq!(module_side_effect_reason(&lam).as_deref(), Some(""));
    }

    #[test]
    fn resolves_runtime_dynamic_import_to_string_path() {
        let runtime = tempdir().expect("failed to create runtime tempdir");
        let runtime_ocaml = runtime.path().join("lib").join("ocaml");
        fs::create_dir_all(&runtime_ocaml).expect("failed to create runtime ocaml dir");
        fs::write(runtime_ocaml.join("Belt_List.cmi"), []).expect("failed to stub runtime cmi");

        let project = tempdir().expect("failed to create project tempdir");
        let source = project.path().join("src").join("Import.res");
        let output = project.path().join("src").join("Import.mjs");

        let resolver = ModulePathResolver::from_compile_options(
            Some(source.to_str().expect("utf8 source path")),
            Some(output.as_path()),
            Some(runtime.path()),
            None,
        );
        let mut compiler = LambdaCompiler::with_module_path_resolver(Some(resolver));
        let program = compiler.compile_program(&Lambda::prim(
            Primitive::Pimport,
            vec![Lambda::global_module(
                Ident::create_persistent("Belt_List"),
                true,
            )],
            Location::none(),
        ));

        let [stmt] = program.block.as_slice() else {
            panic!("expected a single import expression statement");
        };
        match &stmt.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Call(func, args, _),
                ..
            }) => {
                assert!(matches!(
                    func.desc,
                    ExpressionDesc::Var(crate::js_ir::VIdent::Id(ref id)) if id.name() == "import"
                ));
                assert!(matches!(
                    args.as_slice(),
                    [Expression {
                        desc: ExpressionDesc::Str { txt, .. },
                        ..
                    }] if txt == "@rescript/runtime/lib/es6/Belt_List.js"
                ));
            }
            other => panic!("expected import(\"...\") call, got {other:?}"),
        }
    }

    #[test]
    fn resolves_local_module_paths_from_ast_metadata() {
        let project = tempdir().expect("failed to create project tempdir");
        let source_dir = project.path().join("src");
        let build_dir = project.path().join("lib").join("bs").join("src");
        fs::create_dir_all(&source_dir).expect("failed to create source dir");
        fs::create_dir_all(&build_dir).expect("failed to create build dir");

        let current_source = source_dir.join("Current.res");
        let target_source = source_dir.join("ModuleWithAlias.res");
        fs::write(&current_source, "").expect("failed to stub current source");
        fs::write(&target_source, "").expect("failed to stub target source");
        write_ast_source_stub(&build_dir.join("ModuleWithAlias.ast"), &target_source);

        let mut pers = PersistentEnv::new();
        pers.set_load_path(vec![build_dir]);

        let resolver = ModulePathResolver::from_compile_options(
            Some(current_source.to_str().expect("utf8 current source path")),
            Some(source_dir.join("Current.mjs").as_path()),
            None,
            Some(pers),
        );
        let module = ModuleId {
            id: Ident::create_persistent("ModuleWithAlias"),
            kind: Kind::Ml,
            dynamic_import: true,
        };

        assert_eq!(
            resolver.resolve_module_path(&module).as_deref(),
            Some("./ModuleWithAlias.mjs")
        );
    }

    #[test]
    fn lowers_paddint_with_int32_coercion() {
        let mut compiler = LambdaCompiler::new();
        let lhs = Ident::create_local("lhs");
        let rhs = Ident::create_local("rhs");
        let program = compiler.compile_program(&Lambda::prim(
            Primitive::Paddint,
            vec![Lambda::var(lhs.clone()), Lambda::var(rhs.clone())],
            Location::none(),
        ));

        let [stmt] = program.block.as_slice() else {
            panic!("expected a single expression statement");
        };
        match &stmt.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Bin(BinOp::Bor, left, right),
                ..
            }) => {
                assert!(matches!(
                    right.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Number(Number::Int { i: 0, .. }),
                        ..
                    }
                ));
                assert!(matches!(
                    left.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Bin(BinOp::Plus, lhs_expr, rhs_expr),
                        ..
                    }
                    if matches!(
                        lhs_expr.as_ref(),
                        Expression {
                            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                            ..
                        } if id.same(&lhs)
                    ) && matches!(
                        rhs_expr.as_ref(),
                        Expression {
                            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                            ..
                        } if id.same(&rhs)
                    )
                ));
            }
            other => panic!("expected `lhs + rhs | 0`, got {other:?}"),
        }
    }

    #[test]
    fn lowers_poffsetref_to_ref_contents_update() {
        let mut compiler = LambdaCompiler::new();
        let cell = Ident::create_local("cell");
        let program = compiler.compile_program(&Lambda::prim(
            Primitive::Poffsetref(1),
            vec![Lambda::var(cell.clone())],
            Location::none(),
        ));

        let [stmt] = program.block.as_slice() else {
            panic!("expected a single effect statement");
        };
        match &stmt.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Bin(BinOp::Eq, left, right),
                ..
            }) => {
                assert!(matches!(
                    left.as_ref(),
                    Expression {
                        desc: ExpressionDesc::StaticIndex(target, field, None),
                        ..
                    } if field == "contents"
                        && matches!(
                            target.as_ref(),
                            Expression {
                                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                                ..
                            } if id.same(&cell)
                        )
                ));
                assert!(matches!(
                    right.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Bin(BinOp::Bor, offset_inner, truncation),
                        ..
                    }
                    if matches!(
                        truncation.as_ref(),
                        Expression {
                            desc: ExpressionDesc::Number(Number::Int { i: 0, .. }),
                            ..
                        }
                    ) && matches!(
                        offset_inner.as_ref(),
                        Expression {
                            desc: ExpressionDesc::Bin(BinOp::Plus, read_back, delta),
                            ..
                        }
                        if matches!(
                            read_back.as_ref(),
                            Expression {
                                desc: ExpressionDesc::StaticIndex(target, field, None),
                                ..
                            } if field == "contents"
                                && matches!(
                                    target.as_ref(),
                                    Expression {
                                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                                        ..
                                    } if id.same(&cell)
                                )
                        ) && matches!(
                            delta.as_ref(),
                            Expression {
                                desc: ExpressionDesc::Number(Number::Int { i: 1, .. }),
                                ..
                            }
                        )
                    )
                ));
            }
            other => panic!("expected `cell.contents = cell.contents + 1 | 0`, got {other:?}"),
        }
    }

    #[test]
    fn lassign_expression_lowers_to_statement_prelude_and_unit_value() {
        let mut compiler = LambdaCompiler::new();
        let cell = Ident::create_local("cell");
        let compiled = compiler.compile_expr(&Lambda::Lassign(
            cell.clone(),
            Box::new(Lambda::prim(
                Primitive::Poffsetint(1),
                vec![Lambda::var(cell.clone())],
                Location::none(),
            )),
        ));

        assert_eq!(print_block(&compiled.prelude), "cell = cell + 1 | 0;");
        assert!(matches!(
            compiled.expr,
            Expression {
                desc: ExpressionDesc::Undefined { is_unit: false },
                ..
            }
        ));
    }

    #[test]
    fn let_bindings_of_unit_lassigns_emit_effects_before_undefined_declarations() {
        let mut compiler = LambdaCompiler::new();
        let u = Ident::create_local("u");
        let v = Ident::create_local("v");
        let block = compiler.compile_let_binding(
            LetKind::Strict,
            &v,
            &Lambda::Lassign(
                u.clone(),
                Box::new(Lambda::prim(
                    Primitive::Poffsetint(1),
                    vec![Lambda::var(u.clone())],
                    Location::none(),
                )),
            ),
        );
        assert_eq!(print_block(&block), "u = u + 1 | 0;\n\nlet v;");
    }

    #[test]
    fn lowers_pis_poly_var_block_to_typeof_object_check() {
        let mut compiler = LambdaCompiler::new();
        let value = Ident::create_local("value");
        let compiled = compiler.compile_expr(&Lambda::prim(
            Primitive::PisPolyVarBlock,
            vec![Lambda::var(value)],
            Location::none(),
        ));

        assert!(
            compiled.prelude.is_empty(),
            "unexpected prelude:\n{}",
            print_block(&compiled.prelude)
        );
        assert!(
            print_expression(&compiled.expr) == "typeof value === \"object\"",
            "rendered expression was:\n{}",
            print_expression(&compiled.expr)
        );
    }

    #[test]
    fn lowers_pisint_to_typeof_number_check() {
        let mut compiler = LambdaCompiler::new();
        let value = Ident::create_local("value");
        let compiled = compiler.compile_expr(&Lambda::prim(
            Primitive::Pisint,
            vec![Lambda::var(value)],
            Location::none(),
        ));

        assert!(
            compiled.prelude.is_empty(),
            "unexpected prelude:\n{}",
            print_block(&compiled.prelude)
        );
        assert!(
            print_expression(&compiled.expr) == "typeof value === \"number\"",
            "rendered expression was:\n{}",
            print_expression(&compiled.expr)
        );
    }

    #[test]
    fn lowers_pisout_to_ocaml_range_check_shapes() {
        let mut compiler = LambdaCompiler::new();
        let value = Ident::create_local("value");
        let zero_offset = compiler.compile_expr(&Lambda::prim(
            Primitive::Pisout(0),
            vec![Lambda::const_(Constant::int(1)), Lambda::var(value.clone())],
            Location::none(),
        ));
        let one_offset = compiler.compile_expr(&Lambda::prim(
            Primitive::Pisout(1),
            vec![Lambda::const_(Constant::int(1)), Lambda::var(value)],
            Location::none(),
        ));

        assert!(
            zero_offset.prelude.is_empty(),
            "unexpected prelude:\n{}",
            print_block(&zero_offset.prelude)
        );
        assert!(
            one_offset.prelude.is_empty(),
            "unexpected prelude:\n{}",
            print_block(&one_offset.prelude)
        );
        assert!(
            print_expression(&zero_offset.expr) == "value !== 0 && value !== 1",
            "rendered expression was:\n{}",
            print_expression(&zero_offset.expr)
        );
        assert!(
            print_expression(&one_offset.expr) == "value !== -1 && value !== 0",
            "rendered expression was:\n{}",
            print_expression(&one_offset.expr)
        );
    }

    #[test]
    fn lowers_plsrint_with_int32_coercion() {
        let mut compiler = LambdaCompiler::new();
        let value = Ident::create_local("value");
        let shift = Ident::create_local("shift");
        let program = compiler.compile_program(&Lambda::prim(
            Primitive::Plsrint,
            vec![Lambda::var(value.clone()), Lambda::var(shift.clone())],
            Location::none(),
        ));

        let [stmt] = program.block.as_slice() else {
            panic!("expected a single expression statement");
        };
        match &stmt.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Bin(BinOp::Bor, left, right),
                ..
            }) => {
                assert!(matches!(
                    right.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Number(Number::Int { i: 0, .. }),
                        ..
                    }
                ));
                assert!(matches!(
                    left.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Bin(BinOp::Lsr, value_expr, shift_expr),
                        ..
                    }
                    if matches!(
                        value_expr.as_ref(),
                        Expression {
                            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                            ..
                        } if id.same(&value)
                    ) && matches!(
                        shift_expr.as_ref(),
                        Expression {
                            desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                            ..
                        } if id.same(&shift)
                    )
                ));
            }
            other => panic!("expected `value >>> shift | 0`, got {other:?}"),
        }
    }

    #[test]
    fn lowers_pmulint_by_positive_power_of_two_to_shift() {
        let value = Ident::create_local("value");
        let expr = int32_mul(Expression::var(value.clone()), int_expr(2));

        match expr.desc {
            ExpressionDesc::Bin(BinOp::Lsl, left, right) => {
                assert!(matches!(
                    left.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&value)
                ));
                assert!(matches!(
                    right.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Number(Number::Int { i: 1, .. }),
                        ..
                    }
                ));
            }
            other => panic!("expected `value << 1`, got {other:?}"),
        }
    }

    #[test]
    fn lowers_pxorint_literal_operands_to_folded_constant() {
        let expr = int32_bxor(int_expr(2), int_expr(-3));

        match expr.desc {
            ExpressionDesc::Number(Number::Int { i: -1, .. }) => {}
            other => panic!("expected folded `-1`, got {other:?}"),
        }
    }

    #[test]
    fn to_int32_drops_redundant_bor_after_logical_shift() {
        let value = Ident::create_local("value");
        let expr = to_int32(Expression::bin(
            BinOp::Lsr,
            Expression::var(value.clone()),
            int_expr(3),
        ));

        match expr.desc {
            ExpressionDesc::Bin(BinOp::Lsr, left, right) => {
                assert!(matches!(
                    left.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&value)
                ));
                assert!(matches!(
                    right.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Number(Number::Int { i: 3, .. }),
                        ..
                    }
                ));
            }
            other => panic!("expected bare logical shift, got {other:?}"),
        }
    }

    #[test]
    fn int32_band_drops_redundant_bor_on_left_operand() {
        let value = Ident::create_local("value");
        let expr = int32_band(
            to_int32(Expression::bin(
                BinOp::Plus,
                Expression::var(value),
                int_expr(1),
            )),
            int_expr(0x7fff_ffff),
        );

        assert_eq!(print_expression(&expr), "value + 1 & 2147483647");
    }

    #[test]
    fn lowers_psome_not_nest_to_identity_optional_block() {
        let mut compiler = LambdaCompiler::new();
        let value = Ident::create_local("value");
        let compiled = compiler.compile_expr(&Lambda::prim(
            Primitive::PsomeNotNest,
            vec![Lambda::var(value.clone())],
            Location::none(),
        ));

        assert!(compiled.prelude.is_empty());
        match &compiled.expr.desc {
            ExpressionDesc::OptionalBlock(inner, true) => {
                assert!(matches!(
                    inner.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&value)
                ));
            }
            other => panic!("expected identity optional block, got {other:?}"),
        }
    }

    #[test]
    fn lowers_psome_immediates_to_identity_optional_block_like_ocaml() {
        let mut compiler = LambdaCompiler::new();
        let compiled = compiler.compile_expr(&Lambda::prim(
            Primitive::Psome,
            vec![Lambda::const_(Constant::int(3))],
            Location::none(),
        ));

        assert!(compiled.prelude.is_empty());
        match &compiled.expr.desc {
            ExpressionDesc::OptionalBlock(inner, true) => {
                assert!(matches!(
                    inner.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Number(Number::Int { i: 3, .. }),
                        ..
                    }
                ));
            }
            other => panic!("expected identity optional block for an immediate, got {other:?}"),
        }
    }

    fn lowers_pval_from_option_optional_block_to_inner_value() {
        let mut compiler = LambdaCompiler::new();
        let value = Ident::create_local("value");
        let program = compiler.compile_program(&Lambda::prim(
            Primitive::PvalFromOption,
            vec![Lambda::prim(
                Primitive::PsomeNotNest,
                vec![Lambda::var(value.clone())],
                Location::none(),
            )],
            Location::none(),
        ));

        let [stmt] = program.block.as_slice() else {
            panic!("expected a single expression statement");
        };
        match &stmt.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            }) => assert!(id.same(&value)),
            other => panic!("expected optional unwrap to lower to the inner value, got {other:?}"),
        }
    }

    #[test]
    fn lowers_pval_from_option_to_primitive_option_runtime_call() {
        let mut compiler = LambdaCompiler::new();
        let value = Ident::create_local("value");
        let compiled = compiler.compile_expr(&Lambda::prim(
            Primitive::PvalFromOption,
            vec![Lambda::var(value.clone())],
            Location::none(),
        ));

        assert!(compiled.prelude.is_empty());
        let ExpressionDesc::Call(func, args, _) = &compiled.expr.desc else {
            panic!("expected option unwrap to lower to a runtime call");
        };
        assert!(matches!(
            func.as_ref(),
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(module, Some(member))),
                ..
            } if module.id.name() == "Primitive_option" && member == "valFromOption"
        ));
        assert!(matches!(
            args.as_slice(),
            [Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            }] if id.same(&value)
        ));
        assert_eq!(
            print_expression(&compiled.expr),
            "Primitive_option.valFromOption(value)"
        );
    }

    #[test]
    fn lowers_pnull_to_opt_non_inline_operand_to_primitive_option_from_null() {
        let mut compiler = LambdaCompiler::new();
        let compiled = compiler.compile_expr(&Lambda::prim(
            Primitive::PnullToOpt,
            vec![Lambda::const_(Constant::string("value"))],
            Location::none(),
        ));

        assert!(compiled.prelude.is_empty());
        let ExpressionDesc::Call(func, args, _) = &compiled.expr.desc else {
            panic!("expected null-to-option lowering to use the runtime helper");
        };
        assert!(matches!(
            func.as_ref(),
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(module, Some(member))),
                ..
            } if module.id.name() == "Primitive_option" && member == "fromNull"
        ));
        assert!(matches!(
            args.as_slice(),
            [Expression {
                desc: ExpressionDesc::Str { txt, .. },
                ..
            }] if txt == "value"
        ));
        assert_eq!(
            print_expression(&compiled.expr),
            "Primitive_option.fromNull(\"value\")"
        );
    }

    #[test]
    fn lowers_pnull_undefined_to_opt_non_inline_operand_to_primitive_option_from_nullable() {
        let mut compiler = LambdaCompiler::new();
        let compiled = compiler.compile_expr(&Lambda::prim(
            Primitive::PnullUndefinedToOpt,
            vec![Lambda::const_(Constant::string("value"))],
            Location::none(),
        ));

        assert!(compiled.prelude.is_empty());
        let ExpressionDesc::Call(func, args, _) = &compiled.expr.desc else {
            panic!("expected nullable-to-option lowering to use the runtime helper");
        };
        assert!(matches!(
            func.as_ref(),
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(module, Some(member))),
                ..
            } if module.id.name() == "Primitive_option" && member == "fromNullable"
        ));
        assert!(matches!(
            args.as_slice(),
            [Expression {
                desc: ExpressionDesc::Str { txt, .. },
                ..
            }] if txt == "value"
        ));
        assert_eq!(
            print_expression(&compiled.expr),
            "Primitive_option.fromNullable(\"value\")"
        );
    }

    #[test]
    fn compile_deps_program_imports_primitive_option_for_non_identity_optional_block() {
        let mut compiler = LambdaCompiler::new();
        let global = Ident::create_persistent("value");
        let exported = Ident::create_local("wrapped");
        let lam = Lambda::let_(
            LetKind::Strict,
            exported.clone(),
            Lambda::prim(
                Primitive::Psome,
                vec![Lambda::var(global.clone())],
                Location::none(),
            ),
            Lambda::prim(
                Primitive::Pmakeblock(
                    0,
                    TagInfo::ModuleExport(vec![exported.clone()]),
                    Mutable::Immutable,
                ),
                vec![Lambda::var(exported.clone())],
                Location::none(),
            ),
        );

        let deps = compiler.compile_deps_program(&lam);
        assert!(deps.modules.iter().any(|module| {
            module.kind == Kind::Runtime && module.id.name() == "Primitive_option"
        }));

        let resolver = ModulePathResolver::from_compile_options(
            None,
            Some(std::path::Path::new("/tmp/wrapped.mjs")),
            None,
            None,
        );
        let rendered = print_deps_program(&deps, Some(&resolver));
        assert!(rendered.contains(
            "import * as Primitive_option from \"@rescript/runtime/lib/es6/Primitive_option.js\";"
        ));
        assert!(rendered.contains("let wrapped = Primitive_option.some(value);"));
    }

    #[test]
    fn external_module_ids_reuse_first_binding_for_same_bundle_and_default() {
        let mut compiler = LambdaCompiler::new();
        let plain = ExternalModuleName {
            bundle: "x".to_string(),
            module_bind_name: ExternalModuleBindName::Nothing,
            import_attributes: None,
        };
        let hinted = ExternalModuleName {
            bundle: "x".to_string(),
            module_bind_name: ExternalModuleBindName::HintName("U".to_string()),
            import_attributes: None,
        };

        let plain_module = compiler.external_module_id(&plain, false, false);
        let hinted_module = compiler.external_module_id(&hinted, false, false);
        let default_module = compiler.external_module_id(&plain, true, false);
        let dynamic_plain_module = compiler.external_module_id(&plain, false, true);

        assert_eq!(plain_module, hinted_module);
        assert_eq!(plain_module.id.name(), "X");
        assert!(!plain_module.id.same(&default_module.id));
        assert!(plain_module.id.same(&dynamic_plain_module.id));
        assert!(!plain_module.dynamic_import);
        assert!(dynamic_plain_module.dynamic_import);
    }

    #[test]
    fn lowers_nullable_predicates_to_js_null_checks() {
        let mut compiler = LambdaCompiler::new();
        let value = Ident::create_local("value");

        let null_compiled = compiler.compile_expr(&Lambda::prim(
            Primitive::PisNull,
            vec![Lambda::var(value.clone())],
            Location::none(),
        ));
        let undefined_compiled = compiler.compile_expr(&Lambda::prim(
            Primitive::PisUndefined,
            vec![Lambda::var(value.clone())],
            Location::none(),
        ));
        let nullable_compiled = compiler.compile_expr(&Lambda::prim(
            Primitive::PisNullUndefined,
            vec![Lambda::var(value.clone())],
            Location::none(),
        ));

        assert!(null_compiled.prelude.is_empty());
        match &null_compiled.expr.desc {
            ExpressionDesc::Bin(BinOp::EqEqEq, left, right) => {
                assert!(matches!(
                    left.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&value)
                ));
                assert!(matches!(
                    right.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Null,
                        ..
                    }
                ));
            }
            other => panic!("expected `value === null`, got {other:?}"),
        }

        assert!(undefined_compiled.prelude.is_empty());
        match &undefined_compiled.expr.desc {
            ExpressionDesc::Bin(BinOp::EqEqEq, left, right) => {
                assert!(matches!(
                    left.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&value)
                ));
                assert!(matches!(
                    right.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Undefined { .. },
                        ..
                    }
                ));
            }
            other => panic!("expected `value === undefined`, got {other:?}"),
        }

        assert!(nullable_compiled.prelude.is_empty());
        match &nullable_compiled.expr.desc {
            ExpressionDesc::IsNullOrUndefined(inner) => {
                assert!(matches!(
                    inner.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&value)
                ));
            }
            other => panic!("expected `value == null`, got {other:?}"),
        }
    }

    #[test]
    fn lowers_pfield_cons_to_hd_tl_properties() {
        let mut compiler = LambdaCompiler::new();
        let list = Ident::create_local("list");
        let head_program = compiler.compile_program(&Lambda::prim(
            Primitive::Pfield(0, FieldDbgInfo::Cons),
            vec![Lambda::var(list.clone())],
            Location::none(),
        ));
        let tail_program = compiler.compile_program(&Lambda::prim(
            Primitive::Pfield(1, FieldDbgInfo::Cons),
            vec![Lambda::var(list.clone())],
            Location::none(),
        ));

        let [head_stmt] = head_program.block.as_slice() else {
            panic!("expected a single expression statement for head");
        };
        let [tail_stmt] = tail_program.block.as_slice() else {
            panic!("expected a single expression statement for tail");
        };

        match &head_stmt.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::StaticIndex(target, field, _),
                ..
            }) => {
                assert_eq!(field, "hd");
                assert!(matches!(
                    target.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&list)
                ));
            }
            other => panic!("expected head access to lower to `.hd`, got {other:?}"),
        }

        match &tail_stmt.desc {
            StatementDesc::Exp(Expression {
                desc: ExpressionDesc::StaticIndex(target, field, _),
                ..
            }) => {
                assert_eq!(field, "tl");
                assert!(matches!(
                    target.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&list)
                ));
            }
            other => panic!("expected tail access to lower to `.tl`, got {other:?}"),
        }
    }

    #[test]
    fn lowers_module_pfield_with_ocaml_identifier_conversion() {
        let mut compiler = LambdaCompiler::new();
        let module_value = Ident::create_local("Js_promise2");
        let expr = compiler.compile_field_access(
            3,
            &FieldDbgInfo::Module {
                name: "catch".to_string(),
            },
            &Expression::var(module_value.clone()),
        );

        match &expr.desc {
            ExpressionDesc::StaticIndex(target, field, Some(index)) => {
                assert_eq!(field, "$$catch");
                assert_eq!(*index, 3);
                assert!(matches!(
                    target.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&module_value)
                ));
            }
            other => panic!(
                "expected module field access to lower to converted static index, got {other:?}"
            ),
        }

        assert_eq!(print_expression(&expr), "Js_promise2.$$catch");
    }

    #[test]
    fn lowers_extension_pfield_to_named_payload_property_like_ocaml() {
        let mut compiler = LambdaCompiler::new();
        let exn = Ident::create_local("exn");
        let expr = compiler.compile_field_access(
            1,
            &FieldDbgInfo::Extension,
            &Expression::var(exn.clone()),
        );

        match &expr.desc {
            ExpressionDesc::StaticIndex(target, field, Some(index)) => {
                assert_eq!(field, "_1");
                assert_eq!(*index, 1);
                assert!(matches!(
                    target.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&exn)
                ));
            }
            other => panic!(
                "expected extension field access to lower to a named static index, got {other:?}"
            ),
        }

        assert_eq!(print_expression(&expr), "exn._1");
    }

    #[test]
    fn lowers_module_pfield_from_pure_caml_block_directly_like_ocaml() {
        let mut compiler = LambdaCompiler::new();
        let eq = Ident::create_local("Eq");
        let expr = compiler.compile_field_access(
            0,
            &FieldDbgInfo::Module {
                name: "Eq".to_string(),
            },
            &Expression::new(ExpressionDesc::CamlBlock(
                vec![Expression::var(eq.clone())],
                MutableFlag::Immutable,
                Box::new(Expression::number(Number::int(0))),
                TagInfo::Module(vec!["Eq".to_string()]),
            )),
        );

        assert!(matches!(
            &expr,
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&eq)
        ));
        assert_eq!(print_expression(&expr), "Eq");
    }

    #[test]
    fn lowers_polyvar_pfield_to_named_static_access_like_ocaml() {
        let mut compiler = LambdaCompiler::new();
        let variant = Ident::create_local("variant");
        let tag = compiler.compile_field_access(
            0,
            &FieldDbgInfo::PolyVarTag,
            &Expression::var(variant.clone()),
        );
        let value = compiler.compile_field_access(
            1,
            &FieldDbgInfo::PolyVarContent,
            &Expression::var(variant.clone()),
        );

        match &tag.desc {
            ExpressionDesc::StaticIndex(target, field, Some(index)) => {
                assert_eq!(field, "NAME");
                assert_eq!(*index, 0);
                assert!(matches!(
                    target.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&variant)
                ));
            }
            other => panic!("expected polyvariant tag access to lower to `.NAME`, got {other:?}"),
        }

        match &value.desc {
            ExpressionDesc::StaticIndex(target, field, Some(index)) => {
                assert_eq!(field, "VAL");
                assert_eq!(*index, 1);
                assert!(matches!(
                    target.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&variant)
                ));
            }
            other => {
                panic!("expected polyvariant payload access to lower to `.VAL`, got {other:?}")
            }
        }

        assert_eq!(print_expression(&tag), "variant.NAME");
        assert_eq!(print_expression(&value), "variant.VAL");
    }

    #[test]
    fn lowers_polyvar_pfield_from_pure_caml_block_directly_like_ocaml() {
        let mut compiler = LambdaCompiler::new();
        let payload = Ident::create_local("payload");
        let block = Expression::new(ExpressionDesc::CamlBlock(
            vec![Expression::string("Tag"), Expression::var(payload.clone())],
            MutableFlag::Immutable,
            Box::new(Expression::number(Number::int(0))),
            TagInfo::PolyVar("Tag".to_string()),
        ));
        let tag = compiler.compile_field_access(0, &FieldDbgInfo::PolyVarTag, &block);
        let value = compiler.compile_field_access(1, &FieldDbgInfo::PolyVarContent, &block);

        assert_eq!(print_expression(&tag), "\"Tag\"");
        assert!(matches!(
            &value,
            Expression {
                desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                ..
            } if id.same(&payload)
        ));
        assert_eq!(print_expression(&value), "payload");
    }

    #[test]
    fn lowers_qualified_ml_module_default_field_without_preconverting_the_member_name() {
        let mut compiler = LambdaCompiler::new();
        let expr = compiler.compile_field_access(
            0,
            &FieldDbgInfo::Module {
                name: "default".to_string(),
            },
            &Expression::qualified(
                ModuleId {
                    id: Ident::create_persistent("Es6_export"),
                    kind: Kind::Ml,
                    dynamic_import: false,
                },
                None,
            ),
        );

        match &expr.desc {
            ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(module, Some(member))) => {
                assert_eq!(module.id.name(), "Es6_export");
                assert!(matches!(module.kind, Kind::Ml));
                assert_eq!(member, "default");
            }
            other => {
                panic!("expected qualified ml-module access for default export, got {other:?}")
            }
        }

        assert_eq!(print_expression(&expr), "Es6_export.default");
    }

    #[test]
    fn lowers_qualified_ml_module_reserved_fields_through_vident_printing() {
        let mut compiler = LambdaCompiler::new();
        let expr = compiler.compile_field_access(
            3,
            &FieldDbgInfo::Module {
                name: "catch".to_string(),
            },
            &Expression::qualified(
                ModuleId {
                    id: Ident::create_persistent("Js_promise2"),
                    kind: Kind::Ml,
                    dynamic_import: false,
                },
                None,
            ),
        );

        match &expr.desc {
            ExpressionDesc::Var(crate::js_ir::VIdent::Qualified(module, Some(member))) => {
                assert_eq!(module.id.name(), "Js_promise2");
                assert!(matches!(module.kind, Kind::Ml));
                assert_eq!(member, "catch");
            }
            other => {
                panic!("expected qualified ml-module access for reserved field, got {other:?}")
            }
        }

        assert_eq!(print_expression(&expr), "Js_promise2.$$catch");
    }

    #[test]
    fn lowers_qualified_ml_module_closed_undefined_constant_from_cmj() {
        let resolver = resolver_with_checked_in_cmj();
        let mut compiler = LambdaCompiler::with_module_path_resolver(Some(resolver));
        let expr = compiler.compile_field_access(
            0,
            &FieldDbgInfo::Module {
                name: "empty".to_string(),
            },
            &Expression::qualified(
                ModuleId {
                    id: Ident::create_persistent("Belt_MapString"),
                    kind: Kind::Ml,
                    dynamic_import: false,
                },
                None,
            ),
        );

        assert!(matches!(
            expr.desc,
            ExpressionDesc::Undefined { is_unit: false }
        ));
        assert_eq!(print_expression(&expr), "undefined");
    }

    #[test]
    fn external_shadow_pass_rewrites_only_shadowed_initializer_reads() {
        let process = Ident::create_local("process");
        let proc = Ident::create_local("proc");
        let global_process = Ident::create_persistent("process");
        let deps = DepsProgram {
            program: Program::new(
                vec![
                    Statement::variable(VariableDeclaration {
                        ident: process.clone(),
                        value: Some(Expression::var(global_process.clone())),
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    }),
                    Statement::variable(VariableDeclaration {
                        ident: proc,
                        value: Some(Expression::var(global_process.clone())),
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    }),
                ],
                vec![],
            ),
            modules: vec![],
            side_effect: None,
        };

        let rewritten = apply_external_shadow_pass(deps);
        let [first, second] = rewritten.program.block.as_slice() else {
            panic!("expected two variable declarations");
        };

        match &first.desc {
            StatementDesc::Variable(VariableDeclaration {
                value:
                    Some(Expression {
                        desc: ExpressionDesc::StaticIndex(target, field, _),
                        ..
                    }),
                ..
            }) => {
                assert_eq!(field, "process");
                assert!(matches!(
                    target.desc,
                    ExpressionDesc::Var(crate::js_ir::VIdent::Id(ref id)) if id.name() == "globalThis"
                ));
            }
            other => panic!("expected first initializer to read globalThis.process, got {other:?}"),
        }

        match &second.desc {
            StatementDesc::Variable(VariableDeclaration {
                value:
                    Some(Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    }),
                ..
            }) => assert_eq!(id.name(), "process"),
            other => {
                panic!("expected second initializer to remain a plain process read, got {other:?}")
            }
        }
    }

    #[test]
    fn js_shake_pass_removes_unused_pure_toplevel_bindings_and_statements() {
        let exported = Ident::create_local("exported");
        let unused = Ident::create_local("unused");
        let deps = apply_js_shake_pass(DepsProgram {
            program: Program::new(
                vec![
                    Statement::exp(Expression::undefined(false)),
                    Statement::variable(VariableDeclaration {
                        ident: unused,
                        value: Some(Expression::number(Number::int(1))),
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    }),
                    Statement::variable(VariableDeclaration {
                        ident: exported.clone(),
                        value: Some(Expression::number(Number::int(2))),
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    }),
                ],
                vec![exported.clone()],
            ),
            modules: vec![],
            side_effect: None,
        });

        let [stmt] = deps.program.block.as_slice() else {
            panic!("expected only the exported binding to remain");
        };

        match &stmt.desc {
            StatementDesc::Variable(VariableDeclaration {
                ident,
                value:
                    Some(Expression {
                        desc: ExpressionDesc::Number(Number::Int { i: 2, .. }),
                        ..
                    }),
                ..
            }) => assert!(ident.same(&exported)),
            other => panic!("expected exported number binding, got {other:?}"),
        }
    }

    #[test]
    fn js_shake_pass_keeps_export_dependencies_and_impure_bindings() {
        let dep = Ident::create_local("dep");
        let exported = Ident::create_local("exported");
        let callback = Ident::create_local("callback");
        let side = Ident::create_local("side");
        let deps = apply_js_shake_pass(DepsProgram {
            program: Program::new(
                vec![
                    Statement::variable(VariableDeclaration {
                        ident: dep.clone(),
                        value: Some(Expression::number(Number::int(1))),
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    }),
                    Statement::variable(VariableDeclaration {
                        ident: exported.clone(),
                        value: Some(Expression::var(dep.clone())),
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    }),
                    Statement::variable(VariableDeclaration {
                        ident: side.clone(),
                        value: Some(Expression::call(
                            Expression::var(callback.clone()),
                            vec![],
                            CallInfo::default(),
                        )),
                        property: LetKind::Strict,
                        ident_info: IdentInfo::default(),
                    }),
                ],
                vec![exported.clone()],
            ),
            modules: vec![],
            side_effect: None,
        });

        let [side_stmt, exported_stmt, dep_stmt] = deps.program.block.as_slice() else {
            panic!("expected the dependency chain and impure binding to remain");
        };

        match &side_stmt.desc {
            StatementDesc::Variable(VariableDeclaration {
                ident,
                value:
                    Some(Expression {
                        desc: ExpressionDesc::Call(func, args, _),
                        ..
                    }),
                ..
            }) => {
                assert!(ident.same(&side));
                assert!(args.is_empty());
                assert!(matches!(
                    func.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(crate::js_ir::VIdent::Id(id)),
                        ..
                    } if id.same(&callback)
                ));
            }
            other => panic!("expected the impure binding to remain first, got {other:?}"),
        }
        match &exported_stmt.desc {
            StatementDesc::Variable(VariableDeclaration { ident, .. }) => {
                assert!(ident.same(&exported));
            }
            other => panic!("expected the exported binding to remain in the middle, got {other:?}"),
        }
        match &dep_stmt.desc {
            StatementDesc::Variable(VariableDeclaration { ident, .. }) => {
                assert!(ident.same(&dep));
            }
            other => panic!("expected the dependency binding to remain last, got {other:?}"),
        }
    }

    #[test]
    fn one_unit_arg_functions_lower_to_zero_arg_js_functions() {
        let mut compiler = LambdaCompiler::new();
        let compiled = compiler.compile_expr(&Lambda::function_(
            1,
            vec![Ident::create_local("param")],
            Lambda::unit(),
            FunctionAttribute {
                one_unit_arg: true,
                ..FunctionAttribute::default()
            },
        ));

        assert!(compiled.prelude.is_empty());
        match compiled.expr.desc {
            ExpressionDesc::Fun { params, .. } => assert!(params.is_empty()),
            other => panic!("expected lowered JS function, got {other:?}"),
        }
    }

    #[test]
    fn recursive_function_bindings_lower_directly_without_placeholder_assignments() {
        let mut compiler = LambdaCompiler::new();
        let func = Ident::create_local("u");
        let param = Ident::create_local("param");
        let lam = Lambda::letrec(
            vec![(
                func.clone(),
                Lambda::function_(
                    1,
                    vec![param],
                    Lambda::var(func.clone()),
                    FunctionAttribute::default(),
                ),
            )],
            Lambda::unit(),
        );

        let compiled = compiler.compile_expr(&lam);
        let rendered = print_block(&compiled.prelude);

        assert!(
            rendered.contains("function u(param)"),
            "expected a direct recursive function declaration:\n{rendered}"
        );
        assert!(
            !rendered.contains("let u;"),
            "unexpected recursive placeholder declaration:\n{rendered}"
        );
        assert!(
            !rendered.contains("u ="),
            "unexpected recursive assignment fallback:\n{rendered}"
        );
    }

    #[test]
    fn mutually_recursive_function_bindings_lower_without_placeholder_assignments() {
        let mut compiler = LambdaCompiler::new();
        let even = Ident::create_local("even");
        let odd = Ident::create_local("odd");
        let n = Ident::create_local("n");
        let lam = Lambda::letrec(
            vec![
                (
                    even.clone(),
                    Lambda::function_(
                        1,
                        vec![n.clone()],
                        Lambda::var(odd.clone()),
                        FunctionAttribute::default(),
                    ),
                ),
                (
                    odd.clone(),
                    Lambda::function_(
                        1,
                        vec![n],
                        Lambda::var(even.clone()),
                        FunctionAttribute::default(),
                    ),
                ),
            ],
            Lambda::unit(),
        );

        let compiled = compiler.compile_expr(&lam);
        let rendered = print_block(&compiled.prelude);

        assert!(
            rendered.contains("function even(n)"),
            "expected the first recursive function to lower directly:\n{rendered}"
        );
        assert!(
            rendered.contains("function odd(n)"),
            "expected the second recursive function to lower directly:\n{rendered}"
        );
        assert!(
            !rendered.contains("let even;") && !rendered.contains("let odd;"),
            "unexpected recursive placeholders remained:\n{rendered}"
        );
    }

    #[test]
    fn recursive_self_referential_record_bindings_lower_to_dummy_object_updates_like_ocaml() {
        let mut compiler = LambdaCompiler::new();
        let xx = Ident::create_local("xx");
        let lam = Lambda::letrec(
            vec![(
                xx.clone(),
                Lambda::prim(
                    Primitive::Pmakeblock(
                        0,
                        TagInfo::record(
                            vec![("xx".to_string(), false)],
                            crate::parser::ast::MutableFlag::Immutable,
                        ),
                        Mutable::Immutable,
                    ),
                    vec![Lambda::var(xx.clone())],
                    Location::none(),
                ),
            )],
            Lambda::unit(),
        );

        let compiled = compiler.compile_expr(&lam);
        let [declare, assign] = compiled.prelude.as_slice() else {
            panic!("expected a dummy-object declaration followed by a field update");
        };

        let StatementDesc::Variable(VariableDeclaration {
            ident,
            value:
                Some(Expression {
                    desc: ExpressionDesc::Object(None, props),
                    ..
                }),
            property: LetKind::Variable,
            ..
        }) = &declare.desc
        else {
            panic!("expected an initialized dummy-object declaration");
        };
        assert!(ident.same(&xx));
        assert!(props.is_empty(), "expected an empty dummy object");

        let StatementDesc::Exp(Expression {
            desc: ExpressionDesc::Bin(BinOp::Eq, left, right),
            ..
        }) = &assign.desc
        else {
            panic!("expected the recursive record field assignment");
        };
        assert!(matches!(
            left.as_ref(),
            Expression {
                desc: ExpressionDesc::StaticIndex(target, field, None),
                ..
            } if field == "xx"
                && matches!(
                    target.as_ref(),
                    Expression {
                        desc: ExpressionDesc::Var(VIdent::Id(id)),
                        ..
                    } if id.same(&xx)
                )
        ));
        assert!(matches!(
            right.as_ref(),
            Expression {
                desc: ExpressionDesc::Var(VIdent::Id(id)),
                ..
            } if id.same(&xx)
        ));
    }

    #[test]
    fn acyclic_letrec_singletons_lower_like_lam_scc_plain_lets() {
        let mut compiler = LambdaCompiler::new();
        let a = Ident::create_local("a");
        let b = Ident::create_local("b");
        let lam = Lambda::letrec(
            vec![
                (
                    a.clone(),
                    Lambda::prim(
                        Primitive::Pmakeblock(
                            0,
                            TagInfo::record(
                                vec![("inner".to_string(), false)],
                                crate::parser::ast::MutableFlag::Immutable,
                            ),
                            Mutable::Immutable,
                        ),
                        vec![Lambda::prim(
                            Primitive::Pmakeblock(
                                0,
                                TagInfo::record(
                                    vec![("value".to_string(), false)],
                                    crate::parser::ast::MutableFlag::Immutable,
                                ),
                                Mutable::Immutable,
                            ),
                            vec![Lambda::const_(Constant::int(1))],
                            Location::none(),
                        )],
                        Location::none(),
                    ),
                ),
                (
                    b.clone(),
                    Lambda::prim(
                        Primitive::Pmakeblock(
                            0,
                            TagInfo::record(
                                vec![("next".to_string(), false)],
                                crate::parser::ast::MutableFlag::Immutable,
                            ),
                            Mutable::Immutable,
                        ),
                        vec![Lambda::var(a.clone())],
                        Location::none(),
                    ),
                ),
            ],
            Lambda::unit(),
        );

        let rendered = print_block(&compiler.compile_expr(&lam).prelude);

        assert!(
            rendered.contains("let a = {"),
            "expected the non-recursive singleton to lower as a plain let:\n{rendered}"
        );
        assert!(
            rendered.contains("let b = {"),
            "expected the dependent singleton to lower as a plain let:\n{rendered}"
        );
        assert!(
            !rendered.contains("let a;") && !rendered.contains("let b;"),
            "unexpected recursive placeholder declaration remained:\n{rendered}"
        );
        assert!(
            !rendered.contains("Primitive_object.updateDummy"),
            "acyclic singletons should not go through dummy-object updates:\n{rendered}"
        );
    }

    #[test]
    fn mutually_recursive_record_bindings_lower_to_runtime_update_dummy_calls() {
        let mut compiler = LambdaCompiler::new();
        let a = Ident::create_local("a");
        let b = Ident::create_local("b");
        let lam = Lambda::letrec(
            vec![
                (
                    a.clone(),
                    Lambda::prim(
                        Primitive::Pmakeblock(
                            0,
                            TagInfo::record(
                                vec![("b".to_string(), false)],
                                crate::parser::ast::MutableFlag::Immutable,
                            ),
                            Mutable::Immutable,
                        ),
                        vec![Lambda::var(b.clone())],
                        Location::none(),
                    ),
                ),
                (
                    b.clone(),
                    Lambda::prim(
                        Primitive::Pmakeblock(
                            0,
                            TagInfo::record(
                                vec![("a".to_string(), false)],
                                crate::parser::ast::MutableFlag::Immutable,
                            ),
                            Mutable::Immutable,
                        ),
                        vec![Lambda::var(a.clone())],
                        Location::none(),
                    ),
                ),
            ],
            Lambda::unit(),
        );

        let rendered = print_block(&compiler.compile_expr(&lam).prelude);

        assert!(
            rendered.contains("let a = {};") && rendered.contains("let b = {};"),
            "expected dummy-object declarations for mutually recursive records:\n{rendered}"
        );
        assert!(
            rendered.contains("Primitive_object.updateDummy(a, {")
                && rendered.contains("Primitive_object.updateDummy(b, {"),
            "expected runtime dummy-object updates for mutually recursive records:\n{rendered}"
        );
        assert!(
            !rendered.contains("let a;") && !rendered.contains("let b;"),
            "unexpected placeholder assignments remained:\n{rendered}"
        );
    }

    #[test]
    fn recursive_self_tailcalls_lower_to_looping_while_bodies() {
        let mut compiler = LambdaCompiler::new();
        let loop_ = Ident::create_local("loop");
        let flag = Ident::create_local("flag");
        let acc = Ident::create_local("acc");
        let next = Ident::create_local("next");
        let tailcall = Lambda::Lapply(Apply {
            ap_func: Box::new(Lambda::var(loop_.clone())),
            ap_args: vec![
                Lambda::const_(Constant::JsFalse),
                Lambda::var(next.clone()),
                Lambda::var(next.clone()),
            ],
            ap_info: ApInfo {
                loc: Location::none(),
                inlined: InlineAttribute::Default,
                status: ApplyStatus::Na,
            },
            ap_transformed_jsx: false,
        });
        let lam = Lambda::letrec(
            vec![(
                loop_.clone(),
                Lambda::function_(
                    3,
                    vec![flag.clone(), acc.clone(), next],
                    Lambda::if_(Lambda::var(flag), tailcall, Lambda::var(acc)),
                    FunctionAttribute::default(),
                ),
            )],
            Lambda::unit(),
        );

        let compiled = compiler.compile_expr(&lam);
        let rendered = print_block(&compiled.prelude);

        assert!(
            rendered.contains("while (true)"),
            "expected recursive self-tailcall lowering to emit a loop:\n{rendered}"
        );
        assert!(
            rendered.contains("continue;"),
            "expected recursive self-tailcall lowering to continue the loop:\n{rendered}"
        );
        assert!(
            !rendered.contains("return loop("),
            "unexpected recursive return call remained:\n{rendered}"
        );
    }

    #[test]
    fn recursive_self_tailcalls_lower_sequands_to_looping_while_bodies() {
        let mut compiler = LambdaCompiler::new();
        let loop_ = Ident::create_local("loop");
        let flag = Ident::create_local("flag");
        let tailcall = Lambda::Lapply(Apply {
            ap_func: Box::new(Lambda::var(loop_.clone())),
            ap_args: vec![Lambda::const_(Constant::JsFalse)],
            ap_info: ApInfo {
                loc: Location::none(),
                inlined: InlineAttribute::Default,
                status: ApplyStatus::Na,
            },
            ap_transformed_jsx: false,
        });
        let lam = Lambda::letrec(
            vec![(
                loop_.clone(),
                Lambda::function_(
                    1,
                    vec![flag.clone()],
                    Lambda::prim(
                        Primitive::Psequand,
                        vec![Lambda::var(flag), tailcall],
                        Location::none(),
                    ),
                    FunctionAttribute::default(),
                ),
            )],
            Lambda::unit(),
        );

        let compiled = compiler.compile_expr(&lam);
        let rendered = print_block(&compiled.prelude);

        assert!(
            rendered.contains("while (true)"),
            "expected recursive sequand lowering to emit a loop:\n{rendered}"
        );
        assert!(
            rendered.contains("continue;"),
            "expected recursive sequand lowering to continue the loop:\n{rendered}"
        );
        assert!(
            !rendered.contains("return loop("),
            "unexpected recursive return call remained:\n{rendered}"
        );
    }

    #[test]
    fn recursive_self_tailcalls_lower_sequors_to_looping_while_bodies() {
        let mut compiler = LambdaCompiler::new();
        let loop_ = Ident::create_local("loop");
        let flag = Ident::create_local("flag");
        let tailcall = Lambda::Lapply(Apply {
            ap_func: Box::new(Lambda::var(loop_.clone())),
            ap_args: vec![Lambda::const_(Constant::JsFalse)],
            ap_info: ApInfo {
                loc: Location::none(),
                inlined: InlineAttribute::Default,
                status: ApplyStatus::Na,
            },
            ap_transformed_jsx: false,
        });
        let lam = Lambda::letrec(
            vec![(
                loop_.clone(),
                Lambda::function_(
                    1,
                    vec![flag.clone()],
                    Lambda::prim(
                        Primitive::Psequor,
                        vec![Lambda::var(flag), tailcall],
                        Location::none(),
                    ),
                    FunctionAttribute::default(),
                ),
            )],
            Lambda::unit(),
        );

        let compiled = compiler.compile_expr(&lam);
        let rendered = print_block(&compiled.prelude);

        assert!(
            rendered.contains("while (true)"),
            "expected recursive sequor lowering to emit a loop:\n{rendered}"
        );
        assert!(
            rendered.contains("continue;"),
            "expected recursive sequor lowering to continue the loop:\n{rendered}"
        );
        assert!(
            !rendered.contains("return loop("),
            "unexpected recursive return call remained:\n{rendered}"
        );
    }

    #[test]
    fn recursive_self_tailcalls_rename_params_before_loop_assignments() {
        let mut compiler = LambdaCompiler::new();
        let loop_ = Ident::create_local("loop");
        let a = Ident::create_local("a");
        let b = Ident::create_local("b");
        let flag = Ident::create_local("flag");
        let tailcall = Lambda::Lapply(Apply {
            ap_func: Box::new(Lambda::var(loop_.clone())),
            ap_args: vec![
                Lambda::var(b.clone()),
                Lambda::var(a.clone()),
                Lambda::const_(Constant::JsFalse),
            ],
            ap_info: ApInfo {
                loc: Location::none(),
                inlined: InlineAttribute::Default,
                status: ApplyStatus::Na,
            },
            ap_transformed_jsx: false,
        });
        let lam = Lambda::letrec(
            vec![(
                loop_.clone(),
                Lambda::function_(
                    3,
                    vec![a.clone(), b.clone(), flag.clone()],
                    Lambda::if_(Lambda::var(flag), tailcall, Lambda::var(a)),
                    FunctionAttribute::default(),
                ),
            )],
            Lambda::unit(),
        );

        let compiled = compiler.compile_expr(&lam);
        let rendered = print_block(&compiled.prelude);

        assert!(
            rendered.contains("function loop(_a, _b, _flag)"),
            "expected loop parameters to be renamed before tailcall assignments:\n{rendered}"
        );
        assert!(
            rendered.contains("let a = _a;")
                && rendered.contains("let b = _b;")
                && rendered.contains("let flag = _flag;"),
            "expected original parameter aliases inside the loop body:\n{rendered}"
        );
        assert!(
            rendered.contains("_a = b;")
                && rendered.contains("_b = a;")
                && rendered.contains("_flag = false;"),
            "expected assignments to target renamed loop params:\n{rendered}"
        );
    }

    #[test]
    fn recursive_self_tailcalls_preserve_ocaml_loop_ordering() {
        let mut compiler = LambdaCompiler::new();
        let f = Ident::create_local("f");
        let n = Ident::create_local("n");
        let acc = Ident::create_local("acc");
        let body = Lambda::if_(
            Lambda::var(n.clone()),
            Lambda::Lapply(Apply {
                ap_func: Box::new(Lambda::var(f.clone())),
                ap_args: vec![
                    Lambda::prim(
                        Primitive::Psubint,
                        vec![Lambda::var(n.clone()), Lambda::const_(Constant::int(1))],
                        Location::none(),
                    ),
                    Lambda::function_(
                        1,
                        vec![Ident::create_local("param")],
                        Lambda::var(acc.clone()),
                        FunctionAttribute::default(),
                    ),
                ],
                ap_info: ApInfo {
                    loc: Location::none(),
                    inlined: InlineAttribute::Default,
                    status: ApplyStatus::Na,
                },
                ap_transformed_jsx: false,
            }),
            Lambda::var(acc.clone()),
        );
        let lam = Lambda::letrec(
            vec![(
                f.clone(),
                Lambda::function_(
                    2,
                    vec![n.clone(), acc.clone()],
                    body,
                    FunctionAttribute::default(),
                ),
            )],
            Lambda::unit(),
        );

        let compiled = compiler.compile_expr(&lam);
        let rendered = print_block(&compiled.prelude);
        let alias_start = rendered
            .find("let acc = _acc;")
            .expect("expected acc alias in loop body");
        let alias_next = rendered
            .find("let n = _n;")
            .expect("expected n alias in loop body");
        let assign_start = rendered
            .find("_acc =")
            .expect("expected acc reassignment in loop body");
        let assign_next = rendered
            .find("_n =")
            .expect("expected n reassignment in loop body");

        assert!(
            alias_start < alias_next,
            "expected acc alias before n alias:\n{rendered}"
        );
        assert!(
            assign_start < assign_next,
            "expected acc reassignment before n reassignment:\n{rendered}"
        );
    }

    #[test]
    fn recursive_wrapped_js_fn_make_bindings_lower_to_looping_while_bodies() {
        let mut compiler = LambdaCompiler::new();
        let loop_ = Ident::create_local("loop");
        let flag = Ident::create_local("flag");
        let acc = Ident::create_local("acc");
        let next = Ident::create_local("next");
        let tailcall = Lambda::Lapply(Apply {
            ap_func: Box::new(Lambda::var(loop_.clone())),
            ap_args: vec![
                Lambda::const_(Constant::JsFalse),
                Lambda::var(next.clone()),
                Lambda::var(next.clone()),
            ],
            ap_info: ApInfo {
                loc: Location::none(),
                inlined: InlineAttribute::Default,
                status: ApplyStatus::Na,
            },
            ap_transformed_jsx: false,
        });
        let lam = Lambda::letrec(
            vec![(
                loop_.clone(),
                Lambda::prim(
                    Primitive::PjsFnMake(3),
                    vec![Lambda::function_(
                        3,
                        vec![flag.clone(), acc.clone(), next],
                        Lambda::if_(Lambda::var(flag), tailcall, Lambda::var(acc)),
                        FunctionAttribute::default(),
                    )],
                    Location::none(),
                ),
            )],
            Lambda::var(loop_.clone()),
        );

        let simplified = crate::lambda::simplify::simplify_for_js_backend(&lam);
        let compiled = compiler.compile_expr(&simplified);
        let rendered = if compiled.prelude.is_empty() {
            print_expression(&compiled.expr)
        } else {
            print_block(&compiled.prelude)
        };

        assert!(
            rendered.contains("while (true)"),
            "expected wrapped recursive self-tailcall lowering to emit a loop:\n{rendered}"
        );
        assert!(
            rendered.contains("continue;"),
            "expected wrapped recursive self-tailcall lowering to continue the loop:\n{rendered}"
        );
        assert!(
            !rendered.contains("return loop("),
            "unexpected wrapped recursive return call remained:\n{rendered}"
        );
    }

    #[test]
    fn recursive_function_aliases_reenter_the_same_tail_loop_like_a_scope_bug() {
        let mut compiler = LambdaCompiler::new();
        let odd = Ident::create_local("odd");
        let even = Ident::create_local("even");
        let z = Ident::create_local("z");
        let y = Ident::create_local("y");
        let lam = Lambda::letrec(
            vec![
                (
                    odd.clone(),
                    Lambda::prim(
                        Primitive::PjsFnMake(1),
                        vec![Lambda::function_(
                            1,
                            vec![z],
                            Lambda::Lapply(Apply {
                                ap_func: Box::new(Lambda::var(even.clone())),
                                ap_args: vec![Lambda::const_(Constant::int(32))],
                                ap_info: ApInfo {
                                    loc: Location::none(),
                                    inlined: InlineAttribute::Default,
                                    status: ApplyStatus::Na,
                                },
                                ap_transformed_jsx: false,
                            }),
                            FunctionAttribute::default(),
                        )],
                        Location::none(),
                    ),
                ),
                (
                    even.clone(),
                    Lambda::prim(
                        Primitive::PjsFnMake(1),
                        vec![Lambda::function_(
                            1,
                            vec![y.clone()],
                            Lambda::Lapply(Apply {
                                ap_func: Box::new(Lambda::var(odd.clone())),
                                ap_args: vec![Lambda::var(y)],
                                ap_info: ApInfo {
                                    loc: Location::none(),
                                    inlined: InlineAttribute::Default,
                                    status: ApplyStatus::Na,
                                },
                                ap_transformed_jsx: false,
                            }),
                            FunctionAttribute::default(),
                        )],
                        Location::none(),
                    ),
                ),
            ],
            Lambda::var(odd.clone()),
        );

        let simplified = crate::lambda::simplify::simplify_for_js_backend(&lam);
        let Lambda::Lletrec(bindings, _) = &simplified else {
            panic!("expected simplified alias test to stay a letrec, got {simplified:?}");
        };
        let tail_targets = direct_recursive_function_tail_targets(bindings);
        let odd_targets = tail_targets
            .get(&odd)
            .cloned()
            .unwrap_or_else(|| panic!("expected tail targets for odd, got {tail_targets:?}"));
        assert!(
            odd_targets.iter().any(|target| target.same(&odd))
                && odd_targets.iter().any(|target| target.same(&even)),
            "expected odd tail targets to include the same-group alias, got {odd_targets:?}\nsimplified:\n{}",
            crate::lambda::print::lambda_to_string(&simplified)
        );
        let compiled = compiler.compile_expr(&simplified);
        let rendered = if compiled.prelude.is_empty() {
            print_expression(&compiled.expr)
        } else {
            print_block(&compiled.prelude)
        };

        assert!(
            rendered.contains("while (true)"),
            "expected same-group function aliases to lower through the tail loop:\n{rendered}"
        );
        assert!(
            rendered.contains("let even = odd;"),
            "expected the recursive alias binding to collapse to a direct alias:\n{rendered}"
        );
        assert!(
            !rendered.contains("return even("),
            "unexpected recursive alias call remained in the emitted JS:\n{rendered}"
        );
    }
}
