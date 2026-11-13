//! T4a (THREE_TREES 11.4, "T4a as built"): the unit's exports, read from the
//! last value of the top level where the lowering completes it.
use super::*;
use crate::bir::JsPayload;
use crate::lambda::TagInfo;

impl State {
    /// O:209 extract_toplevel_exports and the finished case of
    /// lam_compile_main.ml:390-395. Reads the unit's last value: an export
    /// block gives the export identifiers and leaves one plain `SExp` per
    /// value on the statement stack, in export order; the heads of a comma
    /// that ends in an export block become effect statements before them;
    /// any other value is one effect and the unit has no export block
    /// (`None`). Cost: one step per comma on the right spine of the value,
    /// one per comma operand of a head, one per export. No allocation: the
    /// identifiers are moved out of the block's payload.
    pub(super) fn extract_exports(
        &mut self,
        value: Option<NodeId>,
        finished: Finished,
    ) -> Option<Vec<Ident>> {
        let mut value = value?;
        if matches!(self.arena.view(value), View::JUndefined) {
            self.arena.release(value);
            return None;
        }
        let mut end = value;
        while let View::JSeq { second, .. } = self.arena.view(end) {
            end = second;
        }
        let block = match self.arena.view(end) {
            View::JBlockLit { info, .. } => matches!(
                self.arena.javascript(info),
                JsPayload::Block(TagInfo::ModuleExport(_))
            )
            .then_some(info),
            _ => None,
        };
        let Some(info) = block else {
            self.push_effect(value);
            return None;
        };
        while let View::JSeq { first, second } = self.arena.view(value) {
            self.arena.detach(first);
            self.arena.detach(second);
            self.arena.release(value);
            self.push_effect(first);
            value = second;
        }
        let mut values = std::mem::take(&mut self.scratch);
        debug_assert!(values.is_empty());
        let View::JBlockLit { values: fields, .. } = self.arena.view(value) else {
            unreachable!("the right spine ends in the export block")
        };
        values.extend_from_slice(fields);
        for &field in &values {
            self.arena.detach(field);
        }
        self.arena.release(value);
        let JsPayload::Block(TagInfo::ModuleExport(exports)) =
            &mut self.arena.pools.js[info.index()]
        else {
            unreachable!("checked above")
        };
        let exports = std::mem::take(exports);
        debug_assert_eq!(
            exports.len(),
            values.len(),
            "module export idents and payloads must stay aligned"
        );
        for &field in &values {
            let field = if finished == Finished::True {
                self.arena.release(field);
                self.pure_expression(View::JUndefined, 0)
            } else {
                field
            };
            let carrier = self.arena.new_node(View::SExp { value: field }, 0);
            self.statements.push(carrier);
        }
        values.clear();
        self.scratch = values;
        Some(exports)
    }

    /// O:339 push_effect_expression onto the top-level run. One step per
    /// comma operand of `value`; the scratch vector is reused.
    fn push_effect(&mut self, value: NodeId) {
        let mut effects = std::mem::take(&mut self.scratch);
        debug_assert!(effects.is_empty());
        crate::bir::j::norm::jm14_push_effect_expression(&mut self.arena, value, &mut effects);
        for statement in effects.drain(..) {
            self.statements.push(statement);
        }
        self.scratch = effects;
    }
}

#[cfg(test)]
mod tests {
    use crate::ident::{Ident, IdentFlags};
    use crate::lambda::arena::{Lam, LamArena};
    use crate::lambda::lam_compat::LetKind;
    use crate::lambda::lam_compile::LambdaCompiler;
    use crate::lambda::lam_constant::Constant as C;
    use crate::lambda::lam_primitive::{Mutable, Primitive as P};
    use crate::lambda::{ApInfo, ApplyStatus, LamLoc, TagInfo};

    fn id(name: &str, stamp: i32) -> Ident {
        Ident::new(name, stamp, IdentFlags::NONE)
    }
    fn exports(a: &mut LamArena, ids: &[Ident], values: &[Lam]) -> Lam {
        a.prim_raw(
            P::Pmakeblock(TagInfo::ModuleExport(ids.to_vec()), Mutable::Immutable),
            values,
            LamLoc::NONE,
        )
    }
    fn call(a: &mut LamArena, name: &str, stamp: i32) -> Lam {
        let callee = a.var(id(name, stamp));
        let unit = a.const_(C::JsUndefined { is_unit: true });
        a.apply_raw(
            callee,
            &[unit],
            ApInfo {
                status: ApplyStatus::InferFull,
                loc: LamLoc::NONE,
            },
        )
    }
    /// The oracle form: the same Lambda through the legacy pipeline and
    /// through the new lowering, both printed texts compared by the gate.
    /// Returns the legacy text after the passes.
    fn gate(a: LamArena, root: Lam) -> String {
        let mut compiler = LambdaCompiler::new();
        let (deps, check) =
            compiler.compile_deps_program_with_lower_check::<true>(a, root, Default::default());
        let check = check.unwrap();
        assert!(matches!(
            check,
            crate::bir::shadow::LowerCheck::Supported(_)
        ));
        crate::bir::shadow::check_lower(check, "Export.res", false).unwrap();
        crate::js_ir::print_deps_program_with_directives_and_options(
            &deps,
            None,
            &[],
            false,
            false,
            false,
        )
    }

    #[test]
    fn a_plain_export_is_extracted() {
        let mut a = LamArena::new();
        let x = id("x", 10);
        let value = call(&mut a, "ext", 1);
        let read = a.var(x);
        let block = exports(&mut a, &[x], &[read]);
        let root = a.let_(LetKind::Strict, x, value, block);
        let text = gate(a, root);
        assert!(text.contains("let x = ext();"), "{text}");
        assert!(text.contains("x,"), "{text}");
    }

    #[test]
    fn an_export_of_a_value_that_is_not_a_variable_is_extracted() {
        let mut a = LamArena::new();
        let value = a.const_(C::Int { i: 42, comment: None });
        let root = exports(&mut a, &[id("answer", 10)], &[value]);
        let text = gate(a, root);
        assert!(text.contains("let answer = 42;"), "{text}");
    }

    #[test]
    fn a_unit_without_exports_has_no_export_block() {
        let mut a = LamArena::new();
        let root = exports(&mut a, &[], &[]);
        gate(a, root);
        let mut a = LamArena::new();
        let root = a.const_(C::JsUndefined { is_unit: true });
        gate(a, root);
    }

    #[test]
    fn a_unit_whose_only_statement_is_an_effect() {
        let mut a = LamArena::new();
        let root = call(&mut a, "ext", 1);
        let text = gate(a, root);
        assert!(text.contains("ext();"), "{text}");
    }

    #[test]
    fn the_heads_of_a_comma_before_the_export_block_are_effects() {
        let mut a = LamArena::new();
        let first = call(&mut a, "first", 1);
        let second = call(&mut a, "second", 2);
        let value = a.const_(C::JsTrue);
        let block = exports(&mut a, &[id("flag", 10)], &[value]);
        let tail = a.seq_raw(second, block);
        let root = a.seq_raw(first, tail);
        let text = gate(a, root);
        let (first, second) = (text.find("first();").unwrap(), text.find("second();").unwrap());
        assert!(first < second, "{text}");
        assert!(text.contains("let flag = true;"), "{text}");
    }

    #[test]
    fn a_finished_unit_exports_undefined_values() {
        let mut a = LamArena::new();
        let x = id("x", 10);
        let payload = a.const_(C::JsNull);
        let raised = a.prim_raw(P::Praise, &[payload], LamLoc::NONE);
        let read = a.var(x);
        let block = exports(&mut a, &[x], &[read]);
        let root = a.let_(LetKind::Strict, x, raised, block);
        let text = gate(a, root);
        assert!(text.contains("throw null;"), "{text}");
        assert!(text.contains("let x;"), "{text}");
    }
}
