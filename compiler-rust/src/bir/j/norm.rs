//! Reachable J normalization rows for Var/Global/Const/Fun/Let/Seq.
use crate::bir::{Bir, NodeFlags, NodeId};

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
            assert!(jm14_effect(&mut imported.arena, actual).is_empty());
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

/// J-M14: O:339 push_effect_expression. Split commas iteratively and read the
/// strict-purity flag. No J-S1 trigger remains on an emitted leaf.
pub(crate) fn jm14_effect(bir: &mut Bir, root: NodeId) -> Vec<NodeId> {
    let mut work = vec![root];
    let mut statements = Vec::new();
    while let Some(value) = work.pop() {
        if let crate::bir::View::JSeq { first, second } = bir.view(value) {
            bir.detach(first);
            bir.detach(second);
            bir.release(value);
            work.extend([second, first]);
        } else if bir.node(value).flags().contains(NodeFlags::STRICT) {
            bir.release(value);
        } else {
            statements.push(bir.new_node(crate::bir::View::SExp { value }, 0));
        }
    }
    statements
}

/// J-M1: E:399 js_seq. Every recursive constructor request becomes a work item.
pub(crate) fn jm1_seq(bir: &mut Bir, left: NodeId, right: NodeId) -> NodeId {
    use crate::bir::{Op, View};
    enum Work { Pair(NodeId, NodeId), Suffix(NodeId) }
    let mut work = vec![Work::Pair(left, right)];
    let mut result = None;
    let trivial = |bir: &Bir, node| matches!(bir.node(node).op(), Op::JNumber | Op::JUndefined);
    while let Some(task) = work.pop() {
        let (left, right) = match task {
            Work::Pair(left, right) => (left, right),
            Work::Suffix(right) => (result.take().expect("comma prefix"), right),
        };
        if let View::JSeq { first, second } = bir.view(left) {
            if trivial(bir, second) || trivial(bir, first) {
                let (keep, drop) = if trivial(bir, second) { (first, second) } else { (second, first) };
                bir.detach(keep);
                bir.detach(drop);
                bir.release(left);
                bir.release(drop);
                work.push(Work::Pair(keep, right));
                continue;
            }
        }
        if let View::JSeq { first, second } = bir.view(right) {
            if trivial(bir, first) || trivial(bir, second) {
                bir.detach(first);
                bir.detach(second);
                bir.release(right);
                if trivial(bir, first) {
                    bir.release(first);
                    work.push(Work::Pair(left, second));
                } else {
                    work.push(Work::Suffix(second));
                    work.push(Work::Pair(left, first));
                }
                continue;
            }
        }
        result = Some(if matches!(bir.node(left).op(), Op::JNumber | Op::JUndefined | Op::Var | Op::JQualified) {
            bir.release(left);
            right
        } else {
            let strict = bir.node(left).flags().contains(NodeFlags::STRICT) && bir.node(right).flags().contains(NodeFlags::STRICT);
            let value = bir.new_node(View::JSeq { first: left, second: right }, 0);
            if strict { let mut flags = bir.node(value).flags(); flags.0 |= NodeFlags::STRICT; bir.nodes[value.index()].set_flags(flags); }
            value
        });
    }
    result.expect("comma result")
}

#[cfg(test)]
mod application_tests {
    use super::*;
    use crate::bir::{bridge_j, View};
    use crate::js_ir::{arena::{JsArena, JsDepsProgram, JsProgram, StmtKind}, build::exp};

    #[test]
    fn jm1_commas_match_legacy_constructor() {
        for shape in 0..7 {
            let mut old = JsArena::new();
            let id = crate::ident::Ident::new("f", 1, crate::ident::IdentFlags::NONE);
            let f = exp::var(id, &mut old);
            let effect = exp::call(f, &[], Default::default(), &mut old);
            let unit = exp::undefined(false, &mut old);
            let number = exp::int(1, &mut old);
            let (left, right) = match shape {
                0 => (effect, unit),
                1 => (number, effect),
                2 => (exp::var(id, &mut old), effect),
                3 => (exp::seq(effect, number, &mut old), unit),
                4 => (unit, exp::seq(number, effect, &mut old)),
                5 => (exp::null(&mut old), exp::seq(effect, unit, &mut old)),
                6 => (exp::seq(number, effect, &mut old), unit),
                _ => unreachable!(),
            };
            let a = old.stmt(StmtKind::Exp(left));
            let b = old.stmt(StmtKind::Exp(right));
            let mut expected = JsDepsProgram { program: JsProgram::new_in(vec![a, b], vec![], old), modules: vec![], side_effect: None };
            let mut candidate = bridge_j::import_js(&expected).unwrap();
            let View::SBlock { statements } = candidate.arena.view(candidate.root) else { panic!("block") };
            let [a, b] = *statements else { panic!("two statements") };
            let View::SExp { value: a } = candidate.arena.view(a) else { panic!("left") };
            let View::SExp { value: b } = candidate.arena.view(b) else { panic!("right") };
            candidate.arena.detach(a);
            candidate.arena.detach(b);
            candidate.arena.release(candidate.root);
            let value = jm1_seq(&mut candidate.arena, a, b);
            let statement = candidate.arena.new_node(View::SExp { value }, 0);
            candidate.root = candidate.arena.new_node(View::SBlock { statements: &[statement] }, 0);
            candidate.arena.validate(Some(candidate.root), false).unwrap();
            let actual = bridge_j::export_js(&candidate).unwrap();
            let value = crate::lambda::js_exp_make::js_seq(left, right, &mut expected.program.arena);
            let statement = expected.program.arena.stmt(StmtKind::Exp(value));
            expected.program.block = vec![statement];
            let print = |p: &JsDepsProgram| crate::js_ir::print_deps_program_with_directives_and_options(p, None, &[], false, false, false);
            assert_eq!(print(&actual), print(&expected), "shape {shape}");
        }
    }
}
