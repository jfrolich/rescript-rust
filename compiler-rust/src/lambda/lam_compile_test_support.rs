//! Lambda-tree-input wrappers over the JS lowering, for unit tests that
//! build recursive Lambda terms. Each call imports its input into a fresh
//! Lambda arena; the JS output lives in the compiler's `j` arena.

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
    fn decoded_switch(a: &mut LamArena, switch: &LambdaSwitch) -> LamSwitch {
        let sw = import_switch(a, switch);
        sw.decode(a)
    }

    pub(crate) fn compile_expr_lam(&mut self, lam: &Lambda) -> Compiled {
        let mut a = LamArena::new();
        let lam = a.import(lam);
        self.compile_expr(&mut a, lam)
    }

    pub(crate) fn compile_return_block_lam(&mut self, lam: &Lambda) -> Vec<Stmt> {
        let mut a = LamArena::new();
        let lam = a.import(lam);
        self.compile_return_block(&mut a, lam)
    }

    pub(crate) fn compile_effect_block_lam(&mut self, lam: &Lambda) -> Vec<Stmt> {
        let mut a = LamArena::new();
        let lam = a.import(lam);
        self.compile_effect_block(&mut a, lam)
    }

    pub(crate) fn compile_assign_to_target_block_lam(
        &mut self,
        result: &Ident,
        lam: &Lambda,
    ) -> Vec<Stmt> {
        let mut a = LamArena::new();
        let lam = a.import(lam);
        self.compile_assign_to_target_block(&mut a, result, lam)
    }

    pub(crate) fn compile_string_switch_return_block_lam(
        &mut self,
        scrut: &Lambda,
        cases: &[(String, Lambda)],
        default: Option<&Lambda>,
    ) -> Vec<Stmt> {
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

    pub(crate) fn compile_untagged_variant_switch_return_statements_lam(
        &mut self,
        scrut: Expr,
        switch: &LambdaSwitch,
    ) -> Vec<Stmt> {
        let mut a = LamArena::new();
        let sw = import_switch(&mut a, switch);
        let plan = sw.untagged_plan(&a).expect("untagged switch plan");
        let fallback = sw.fail(&a);
        self.compile_untagged_plan(
            &mut a,
            crate::lambda::lam_compile_variant::UntaggedMode::Return,
            &mut None,
            scrut,
            fallback,
            &plan,
        )
    }

    pub(crate) fn compile_untagged_variant_switch_assignment_statements_lam(
        &mut self,
        result: &Ident,
        scrut: Expr,
        switch: &LambdaSwitch,
    ) -> Vec<Stmt> {
        let mut a = LamArena::new();
        let sw = import_switch(&mut a, switch);
        let plan = sw.untagged_plan(&a).expect("untagged switch plan");
        let fallback = sw.fail(&a);
        self.compile_untagged_plan(
            &mut a,
            crate::lambda::lam_compile_variant::UntaggedMode::Assign(result),
            &mut None,
            scrut,
            fallback,
            &plan,
        )
    }

    pub(crate) fn compile_untagged_variant_switch_effect_statements_lam(
        &mut self,
        scrut: Expr,
        switch: &LambdaSwitch,
    ) -> Vec<Stmt> {
        let mut a = LamArena::new();
        let sw = import_switch(&mut a, switch);
        let plan = sw.untagged_plan(&a).expect("untagged switch plan");
        let fallback = sw.fail(&a);
        self.compile_untagged_plan(
            &mut a,
            crate::lambda::lam_compile_variant::UntaggedMode::Effect,
            &mut None,
            scrut,
            fallback,
            &plan,
        )
    }

    pub(crate) fn compile_let_binding_lam(
        &mut self,
        kind: LetKind,
        id: &Ident,
        value: &Lambda,
    ) -> Vec<Stmt> {
        let mut a = LamArena::new();
        let value = a.import(value);
        self.compile_let_binding(&mut a, kind, id, value)
    }

    pub(crate) fn compile_named_variant_switch_return_statements_lam(
        &mut self,
        scrut: Expr,
        switch: &LambdaSwitch,
    ) -> Vec<Stmt> {
        let mut a = LamArena::new();
        let switch = Self::decoded_switch(&mut a, switch);
        self.compile_named_variant_switch_return_statements(&mut a, scrut, &switch)
    }

    pub(crate) fn compile_named_string_switch_return_lam(
        &mut self,
        test: Expr,
        cases: &[(SwitchCaseTag, &Lambda)],
        default: Option<&Lambda>,
        complete: bool,
    ) -> Vec<Stmt> {
        let mut a = LamArena::new();
        let cases = import_cases(&mut a, cases);
        let default = default.map(|d| a.import(d));
        self.compile_named_string_switch_return(&mut a, test, &cases, default, complete)
    }

    pub(crate) fn coerce_toplevel_exports_lam(
        &mut self,
        block: &mut Vec<Stmt>,
        extracted: ExtractedExports,
        finished: OutputFinished,
    ) -> Vec<Ident> {
        let mut j = std::mem::take(&mut self.j);
        let (exports, _) =
            self.coerce_toplevel_exports_with_name_reservations(&mut j, block, extracted, finished);
        self.j = j;
        exports
    }
}

pub(crate) fn module_side_effect_reason_tree(lam: &Lambda) -> Option<String> {
    let mut a = LamArena::new();
    let lam = a.import(lam);
    module_side_effect_reason(&a, lam)
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

impl LambdaCompiler {
    pub(crate) fn compile_assign_to_target_output_tree(
        &mut self,
        result: &Ident,
        lam: &Lambda,
    ) -> BlockOutput {
        let mut a = LamArena::new();
        let lam = a.import(lam);
        self.compile_assign_to_target_output(&mut a, result, lam)
    }
    pub(crate) fn compile_effect_block_output_tree(&mut self, lam: &Lambda) -> BlockOutput {
        let mut a = LamArena::new();
        let lam = a.import(lam);
        self.compile_effect_block_output(&mut a, lam)
    }
    pub(crate) fn compile_return_output_tree(&mut self, lam: &Lambda) -> BlockOutput {
        let mut a = LamArena::new();
        let lam = a.import(lam);
        self.compile_return_output(&mut a, lam)
    }
    pub(crate) fn compile_let_binding_output_tree(
        &mut self,
        kind: LetKind,
        id: &Ident,
        lam: &Lambda,
    ) -> BlockOutput {
        let mut a = LamArena::new();
        let lam = a.import(lam);
        self.compile_let_binding_output(&mut a, kind, id, lam)
    }
}
