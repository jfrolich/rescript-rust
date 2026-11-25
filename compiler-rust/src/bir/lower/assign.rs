//! Assignment statements (BACKEND_LOWERING §3.11).
use super::*;

impl State {
    /// C:2078 compile_expr, Assign arm. O(1) excluding realization of the
    /// already visited operand. Assignment facts are final on entry.
    pub(super) fn finish_assignment(&mut self, cx: Cx, var: VarId, child: Probed) -> Probed {
        let mut out = self.realize(
            Cx {
                cont: Cont::Value(Tail::No),
                ..cx
            },
            child,
        );
        let value = out
            .value
            .take()
            .unwrap_or_else(|| self.pure_expression(View::JUndefined, 0));
        let statement = super::super::j::assign(&mut self.arena, var, value);
        self.statements.push(statement);
        let unit = self.pure_expression(View::JUndefined, 0);
        let tail = self.leaf(cx, unit);
        out.stmts = self.statements.since(Span {
            start: out.stmts.start,
            len: 0,
        });
        out.value = tail.value;
        out.finished = tail.finished;
        Probed::Out(out)
    }
}

#[cfg(test)]
mod tests {
    use super::super::oracle_tests::compare;
    use crate::ident::{Ident, IdentFlags};
    use crate::lambda::arena::LamArena;
    use crate::lambda::lam_constant::Constant;

    #[test]
    fn assignment_captured_and_uncaptured() {
        use crate::lambda::{FunctionAttribute, LamLoc};
        for captured in [false, true] {
            let mut a = LamArena::new();
            let id = Ident::new("mutable", 10, IdentFlags::NONE);
            let value = a.const_(Constant::Int {
                i: 42,
                comment: None,
            });
            let assignment = a.assign(id, value);
            let mut tail = a.var(id);
            if captured {
                tail = a.function_(0, &[], tail, FunctionAttribute::default(), LamLoc::NONE);
            }
            let root = a.seq_raw(assignment, tail);
            compare(a, root);
        }
    }

    #[test]
    fn assignment_raising_operand() {
        let mut a = LamArena::new();
        let value = a.const_(Constant::Int {
            i: 42,
            comment: None,
        });
        let value = a.prim_raw(
            crate::lambda::lam_primitive::Primitive::Praise,
            &[value],
            crate::lambda::LamLoc::NONE,
        );
        let root = a.assign(Ident::new("mutable", 10, IdentFlags::NONE), value);
        compare(a, root);
    }

    #[test]
    fn ten_thousand_assignments_are_linear() {
        use super::super::*;
        const N: usize = 10_000;
        let mut a = LamArena::new();
        let leaf = a.const_(Constant::Int {
            i: 42,
            comment: None,
        });
        let assignment = a.assign(Ident::new("mutable", 10, IdentFlags::NONE), leaf);
        let mut root = leaf;
        for _ in 0..N {
            root = a.seq_raw(assignment, root);
        }
        let input = crate::bir::bridge::import_lambda(&a, root).unwrap();
        let root = input.root;
        let mut state = State::new(input);
        let output = state.probe(Cx::returning(), root).unwrap();
        state.realize(Cx::returning(), output);
        assert_eq!(state.source_steps, 3 * N + 1);
        assert_eq!(state.statements.pushed, N + 1);
        eprintln!(
            "assignments: visits={}, statements={}",
            state.source_steps, state.statements.pushed
        );
    }

    #[test]
    fn assignment_all_continuations() {
        let mut a = LamArena::new();
        let value = a.const_(Constant::Int {
            i: 42,
            comment: None,
        });
        let root = a.assign(Ident::new("mutable", 10, IdentFlags::NONE), value);
        compare(a, root);
    }
}
