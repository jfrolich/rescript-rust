//! Reachable J normalization rows for Var/Global/Const/Fun/Let/Seq.
use crate::bir::{Bir, NodeFlags, NodeId};

/// J-M14, O:339 push_effect_expression: discard a strictly pure effect value.
/// All expression producers supported by S3.3a are strictly pure. Their
/// structural preludes remain on the statement stack; only the value is dropped.
/// Later slices add comma splitting and effectful values when they can occur.
pub(crate) fn discard_pure_effect(bir: &mut Bir, value: NodeId) {
    assert!(bir.node(value).flags().contains(NodeFlags::STRICT));
    bir.release(value);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bir::{View, bridge_j};
    use crate::js_ir::arena::{JsArena, JsDepsProgram, JsProgram, StmtKind};
    use crate::js_ir::build::exp;
    use crate::lambda::lam_coercion::push_effect_expression;

    #[test]
    fn jm14_pure_effects_match_legacy_printed_text() {
        for input in 0..5 {
            let mut legacy = JsArena::new();
            let value = match input {
                0 => exp::undefined(true, &mut legacy),
                1 => exp::null(&mut legacy),
                2 => exp::bool(true, &mut legacy),
                3 => exp::string("discarded", &mut legacy),
                4 => exp::var(
                    crate::ident::Ident::new("value", 1, crate::ident::IdentFlags::NONE),
                    &mut legacy,
                ),
                _ => unreachable!(),
            };
            let statement = legacy.stmt(StmtKind::Exp(value));
            let source = JsDepsProgram {
                program: JsProgram::new_in(vec![statement], vec![], legacy),
                modules: vec![],
                side_effect: None,
            };
            let mut imported = bridge_j::import_js(&source).unwrap();
            let View::SBlock { statements } = imported.arena.view(imported.root) else {
                panic!("block")
            };
            let View::SExp { value: actual } = imported.arena.view(statements[0]) else {
                panic!("expression")
            };
            // The row consumes the cached predicate. The source lowering's
            // independent flag tests establish it for these same producers.
            let mut flags = imported.arena.node(actual).flags();
            flags.0 |= NodeFlags::STRICT;
            imported.arena.nodes[actual.index()].set_flags(flags);
            imported.arena.detach(actual);
            imported.arena.release(imported.root);
            discard_pure_effect(&mut imported.arena, actual);
            imported.root = imported.arena.new_node(View::SBlock { statements: &[] }, 0);
            let actual = bridge_j::export_js(&imported).unwrap();
            let mut expected = source;
            let mut block = Vec::new();
            push_effect_expression(&mut expected.program.arena, &mut block, value);
            expected.program.block = block;
            let print = |p: &JsDepsProgram| {
                crate::js_ir::print_deps_program_with_directives_and_options(
                    p,
                    None,
                    &[],
                    false,
                    false,
                    false,
                )
            };
            assert_eq!(print(&actual), print(&expected));
            imported.arena.validate(Some(imported.root), false).unwrap();
        }
    }
}
