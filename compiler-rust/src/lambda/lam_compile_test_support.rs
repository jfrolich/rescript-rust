//! Tree-input wrappers over the arena JS lowering, for unit tests that build
//! recursive Lambda terms. Each call imports its input into a fresh arena.

use super::*;
use crate::lambda::LambdaSwitch;
use crate::lambda::lam_compile_variant::LamSwitch;

fn import_switch(a: &mut LamArena, switch: &LambdaSwitch) -> Sw {
    let lam = a.import(&Lambda::Lswitch(
        Box::new(Lambda::const_(Constant::JsNull)),
        Box::new(switch.clone()),
    ));
    let Node::Switch { actions, info, .. } = a.node(lam) else {
        unreachable!("an imported switch is a switch node")
    };
    Sw { actions, info }
}

fn import_cases<K: Clone>(a: &mut LamArena, cases: &[(K, &Lambda)]) -> Vec<(K, Lam)> {
    cases
        .iter()
        .map(|(key, body)| (key.clone(), a.import(body)))
        .collect()
}

impl LambdaCompiler {
    pub(crate) fn compile_expr_tree(&mut self, lam: &Lambda) -> Compiled {
        let mut a = LamArena::new();
        let lam = a.import(lam);
        self.compile_expr(&mut a, lam)
    }

    pub(crate) fn compile_return_block_tree(&mut self, lam: &Lambda) -> Block {
        let mut a = LamArena::new();
        let lam = a.import(lam);
        self.compile_return_block(&mut a, lam)
    }

    pub(crate) fn compile_effect_block_tree(&mut self, lam: &Lambda) -> Block {
        let mut a = LamArena::new();
        let lam = a.import(lam);
        self.compile_effect_block(&mut a, lam)
    }

    pub(crate) fn compile_assign_to_target_block_tree(
        &mut self,
        result: &Ident,
        lam: &Lambda,
    ) -> Block {
        let mut a = LamArena::new();
        let lam = a.import(lam);
        self.compile_assign_to_target_block(&mut a, result, lam)
    }

    pub(crate) fn compile_string_switch_return_block_tree(
        &mut self,
        scrut: &Lambda,
        cases: &[(String, Lambda)],
        default: Option<&Lambda>,
    ) -> Block {
        let mut a = LamArena::new();
        let lam = a.import(&Lambda::LstringSwitch(
            Box::new(scrut.clone()),
            cases.to_vec(),
            default.map(|d| Box::new(d.clone())),
        ));
        let Node::StringSwitch {
            scrut,
            actions,
            info,
        } = a.node(lam)
        else {
            unreachable!("an imported string switch is a string switch node")
        };
        self.compile_string_switch_return_block(&mut a, scrut, StrSw { actions, info })
    }

    fn decoded_tree_switch(a: &mut LamArena, switch: &LambdaSwitch) -> LamSwitch {
        let sw = import_switch(a, switch);
        sw.decode(a)
    }

    pub(crate) fn compile_untagged_variant_switch_return_statements_tree(
        &mut self,
        scrut: Expression,
        switch: &LambdaSwitch,
    ) -> Block {
        let mut a = LamArena::new();
        let switch = Self::decoded_tree_switch(&mut a, switch);
        self.compile_untagged_variant_switch_return_statements(&mut a, scrut, &switch)
    }

    pub(crate) fn compile_untagged_variant_switch_assignment_statements_tree(
        &mut self,
        result: &Ident,
        scrut: Expression,
        switch: &LambdaSwitch,
    ) -> Block {
        let mut a = LamArena::new();
        let switch = Self::decoded_tree_switch(&mut a, switch);
        self.compile_untagged_variant_switch_assignment_statements(&mut a, result, scrut, &switch)
    }

    pub(crate) fn compile_untagged_variant_switch_effect_statements_tree(
        &mut self,
        scrut: Expression,
        switch: &LambdaSwitch,
    ) -> Block {
        let mut a = LamArena::new();
        let switch = Self::decoded_tree_switch(&mut a, switch);
        self.compile_untagged_variant_switch_effect_statements(&mut a, scrut, &switch)
    }

    pub(crate) fn compile_let_binding_tree(
        &mut self,
        kind: LetKind,
        id: &Ident,
        value: &Lambda,
    ) -> Block {
        let mut a = LamArena::new();
        let value = a.import(value);
        self.compile_let_binding(&mut a, kind, id, value)
    }

    pub(crate) fn compile_named_variant_switch_return_statements_tree(
        &mut self,
        scrut: Expression,
        switch: &LambdaSwitch,
    ) -> Block {
        let mut a = LamArena::new();
        let switch = Self::decoded_tree_switch(&mut a, switch);
        self.compile_named_variant_switch_return_statements(&mut a, scrut, &switch)
    }

    pub(crate) fn compile_named_string_switch_return_tree(
        &mut self,
        test: Expression,
        cases: &[(SwitchCaseTag, &Lambda)],
        default: Option<&Lambda>,
        complete: bool,
    ) -> Block {
        let mut a = LamArena::new();
        let cases = import_cases(&mut a, cases);
        let default = default.map(|d| a.import(d));
        self.compile_named_string_switch_return(&mut a, test, &cases, default, complete)
    }
}

pub(crate) fn module_side_effect_reason_tree(lam: &Lambda) -> Option<String> {
    let mut a = LamArena::new();
    let lam = a.import(lam);
    module_side_effect_reason(&a, lam)
}

/// `(dependencies, groups)` of recursive bindings given as trees.
pub(crate) fn recursive_binding_groups_tree(bindings: &[(Ident, Lambda)]) -> Vec<Vec<usize>> {
    let mut a = LamArena::new();
    let bindings: Vec<_> = bindings
        .iter()
        .map(|(id, value)| (*id, a.import(value)))
        .collect();
    let dependencies = recursive_binding_dependencies(&a, &bindings);
    recursive_binding_groups(&a, &bindings, &dependencies)
}

/// The JS-backend simplification of a tree program, exported back to a tree.
pub(crate) fn simplify_tree_for_js_backend(lam: &Lambda) -> Lambda {
    let mut no_external_inline = |_: &Ident, _: &str| None;
    let mut no_external_arity = |_: &Ident, _: &str| None;
    let s = crate::lambda::lam_compile_main::simplify_for_js_backend(
        lam,
        false,
        &mut no_external_inline,
        &mut no_external_arity,
    );
    s.arena.export(s.lam)
}

/// Tree form of [`ExtractedExports`].
#[derive(Debug)]
pub(crate) struct TreeExtractedExports {
    pub(crate) exports: Vec<Ident>,
    pub(crate) values: Vec<Expression>,
}

/// `resolve_export_aliases` over a tree block.
pub(crate) fn resolve_export_aliases_tree(block: &Block, exports: Vec<Ident>) -> Vec<Ident> {
    let mut j = JsArena::new();
    let block = import_block_vec(&mut j, block);
    crate::lambda::lam_coercion::resolve_export_aliases(&mut j, &block, exports)
}

impl LambdaCompiler {
    pub(crate) fn compile_program_tree(&mut self, lam: &Lambda) -> crate::js_ir::Program {
        self.compile_program(lam).to_tree()
    }

    pub(crate) fn compile_deps_program_tree(&mut self, lam: &Lambda) -> crate::js_ir::DepsProgram {
        self.compile_deps_program(lam).to_tree()
    }

    pub(crate) fn compile_deps_program_with_possible_required_modules_tree(
        &mut self,
        lam: &Lambda,
        extra: &AHashSet<ModuleId>,
    ) -> crate::js_ir::DepsProgram {
        self.compile_deps_program_with_possible_required_modules(lam, extra)
            .to_tree()
    }

    /// Export coercion over a tree block.
    pub(crate) fn coerce_toplevel_exports(
        &mut self,
        block: &mut Block,
        extracted: TreeExtractedExports,
    ) -> Vec<Ident> {
        let mut j = JsArena::new();
        let mut arena_block = import_block_vec(&mut j, block);
        let values = extracted
            .values
            .iter()
            .map(|value| import_expr(&mut j, value))
            .collect();
        let (exports, _) = self.coerce_toplevel_exports_with_name_reservations(
            &mut j,
            &mut arena_block,
            ExtractedExports {
                exports: extracted.exports,
                values,
            },
        );
        *block = arena_block
            .iter()
            .map(|stmt| crate::js_ir::arena_tree::export_stmt(&j, *stmt))
            .collect();
        exports
    }
}

/// Tree-program wrappers over the arena JS passes.
pub(crate) mod tree_passes {
    use crate::js_ir::arena::JsDepsProgram;
    use crate::js_ir::{Block, DepsProgram, Expression};

    fn via_arena(
        deps: DepsProgram,
        pass: impl FnOnce(JsDepsProgram) -> JsDepsProgram,
    ) -> DepsProgram {
        pass(JsDepsProgram::from_tree(&deps)).to_tree()
    }

    pub(crate) fn apply_js_flatten_pass(deps: DepsProgram) -> DepsProgram {
        via_arena(
            deps,
            crate::lambda::js_pass_flatten_and_mark_dead::apply_js_flatten_pass,
        )
    }

    pub(crate) fn apply_external_shadow_pass(deps: DepsProgram) -> DepsProgram {
        via_arena(
            deps,
            crate::lambda::js_pass_external_shadow::apply_external_shadow_pass,
        )
    }

    pub(crate) fn apply_js_tailcall_inline_pass(deps: DepsProgram) -> DepsProgram {
        via_arena(
            deps,
            crate::lambda::js_pass_tailcall_inline::apply_js_tailcall_inline_pass,
        )
    }

    pub(crate) fn apply_js_flatten_and_mark_dead_pass(
        deps: DepsProgram,
        jsx_preserve: bool,
    ) -> DepsProgram {
        via_arena(deps, |d| {
            crate::lambda::js_pass_flatten_and_mark_dead::apply_js_flatten_and_mark_dead_pass(
                d,
                jsx_preserve,
            )
        })
    }

    pub(crate) fn apply_js_shake_pass(deps: DepsProgram) -> DepsProgram {
        via_arena(deps, crate::lambda::js_shake::apply_js_shake_pass)
    }

    /// `extract_toplevel_exports` over tree values.
    pub(crate) fn extract_toplevel_exports(
        expr: Expression,
        block: &mut Block,
    ) -> Option<super::TreeExtractedExports> {
        use crate::js_ir::arena_tree::{export_expr, export_stmt, import_block_vec, import_expr};
        let mut j = crate::js_ir::arena::JsArena::new();
        let mut arena_block = import_block_vec(&mut j, block);
        let expr = import_expr(&mut j, &expr);
        let extracted =
            crate::lambda::lam_coercion::extract_toplevel_exports(&mut j, expr, &mut arena_block);
        *block = arena_block.iter().map(|s| export_stmt(&j, *s)).collect();
        extracted.map(|e| super::TreeExtractedExports {
            exports: e.exports,
            values: e.values.iter().map(|v| export_expr(&j, *v)).collect(),
        })
    }
}
