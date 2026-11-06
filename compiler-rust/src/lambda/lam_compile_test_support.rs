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
