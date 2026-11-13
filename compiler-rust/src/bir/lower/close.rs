//! Step A of THREE_TREES 11.4, the decisions only ("T4c design"): where a
//! run is copied, the status the legacy tail-call pass would give each of
//! its declarations, read from `built`, and the tail-call sites of the
//! `return`s of the run. Nothing is rewritten: the legacy pass still runs on
//! the new side of the gate, and check mode compares its decisions with
//! these (`bir::shadow::compare_decisions`).
use super::scope::{Decision, VarFacts};
use crate::bir::j::facts::strictly_pure;
use crate::bir::{Bir, FuncHeader, ListId, NodeId, View};
use crate::js_ir::op::UsedStats;
use crate::lambda::lam_compat::LetKind;

/// The close of the copied run `list`, last statement first: the sites of
/// each `return`, then the decision of each declaration, so that a site in
/// the run is known to the declarations before it. Sites in lists nested in
/// the run were recorded when those were copied.
///
/// Cost: one step per statement of `list` and one per operand of a returned
/// conditional or sequence on the path to a site (`scope::return_sites`); no statement
/// body is read, and nothing is allocated once the spine and the decision
/// rows have their capacity. The test at 10,000 declarations asserts 3
/// steps per declaration of a function whose body is one `return` of a call
/// (`ten_thousand_declarations_close_in_three_steps_each`): one for the
/// declaration, two for the body's list.
///
/// A list is copied, and decided, each time the lowering moves its
/// statements (a held run, a branch `simplify_if_head` moves after its
/// guard), so a declaration is decided once per copy of its statement, not
/// once: the bound is `StatementStack::copied`, which no constant per
/// declaration bounds (7 decisions of one variable in the runtime's
/// `Primitive_object`, one decision in five replaced on a 3,735-module
/// application). The last decision is the one that stands
/// (`a_declaration_is_decided_once_per_copy_of_its_statement`). That is
/// acceptable while nothing is rewritten: a decision is a pure function of
/// the counts and costs the step the copy already takes. A splice needs a
/// close that happens once (THREE_TREES 11.4, "T4c design").
pub(super) fn decide(bir: &mut Bir, list: ListId) {
    let count = bir.lists.get(list).len();
    let mut steps = 0;
    for at in (0..count).rev() {
        steps += 1;
        let statement = bir.lists.get(list)[at];
        match bir.view(statement) {
            View::SReturn { value } => super::scope::return_sites(bir, value, at + 1 == count),
            View::SDecl { var, value } => {
                let kind = bir.node(statement).aux() & 3;
                let scope = bir.js_scope.as_ref().expect("lowering scope");
                let built = scope.uses[var.index()].built;
                let origin = bir.vars.j_origin[var.index()];
                let exported = scope.facts[origin.index()].state & VarFacts::EXPORTED != 0;
                let site = scope.facts[var.index()].site != VarFacts::NO_SITE;
                let pure = value.is_some_and(|value| strictly_pure(bir, value));
                let status = if exported {
                    UsedStats::Exported
                } else if built == 0 {
                    if pure { UsedStats::DeadPure } else { UsedStats::DeadNonPure }
                } else if built == 1 && pure {
                    UsedStats::OncePure
                } else {
                    UsedStats::Used
                };
                let inline = status == UsedStats::OncePure
                    && site
                    && (kind == LetKind::Strict as u16 || kind == LetKind::StrictOpt as u16 || kind == LetKind::Alias as u16)
                    && value.is_some_and(|value| inlinable_function(bir, value));
                let scope = bir.js_scope.as_mut().expect("lowering scope");
                scope.decisions.push(Decision::new(var, status, inline, built));
            }
            _ => {}
        }
    }
    bir.js_scope.as_mut().expect("lowering scope").close_steps += steps;
}

/// `inline_function_decl_from_variable` of the legacy pass: a function
/// literal that is not a method, not `async` and has no directive. Constant.
fn inlinable_function(bir: &Bir, value: NodeId) -> bool {
    let View::JFun { header, .. } = bir.view(value) else { return false };
    let attributes = bir.function_attributes(header);
    bir.function(header).flags & FuncHeader::METHOD == 0 && !attributes.async_ && attributes.directive.is_none()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bir::lower::scope::Scope;
    use crate::name::Name;

    /// A list of `count` declarations `let v = w` and one `return c ? w : w`.
    fn run(b: &mut Bir, count: u32) -> ListId {
        let other = b.new_var_id(Name::new("w"), 0);
        let mut statements = Vec::with_capacity(count as usize + 1);
        for order in 0..count {
            let var = b.new_var_id(Name::new("v"), order + 1);
            let value = b.new_node(View::Var { var: other }, 0);
            statements.push(b.new_node(View::SDecl { var, value: Some(value) }, LetKind::Strict as u16));
        }
        let operands = [(); 3].map(|()| b.new_node(View::Var { var: other }, 0));
        let value = b.new_node(View::JCond { condition: operands[0], then_: operands[1], else_: operands[2] }, 0);
        statements.push(b.new_node(View::SReturn { value }, 0));
        b.lists.push(&statements)
    }

    #[test]
    fn ten_thousand_declarations_are_decided_without_allocating_once_the_tables_are_warm() {
        let mut b = Bir::default();
        b.begin_bulk();
        b.js_scope = Some(Scope::new(0));
        let list = run(&mut b, 10_000);
        // Warm: the spine has its capacity, the rows have room.
        decide(&mut b, list);
        let scope = b.js_scope.as_mut().unwrap();
        assert_eq!(scope.decisions.len(), 10_000);
        // 10,001 statements; the returned conditional and its two branches.
        assert_eq!(scope.close_steps, 10_001 + 3);
        scope.decisions.reserve(10_000);
        let allocations = allocation_counter::measure(|| decide(&mut b, list));
        assert_eq!(allocations.count_total, 0, "{allocations:?}");
        assert_eq!(b.js_scope.as_ref().unwrap().decisions.len(), 20_000);
    }
}
