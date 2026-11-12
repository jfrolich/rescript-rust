//! Assignment statements (BACKEND_LOWERING §3.11).
use super::*;

impl State {
    /// C:2078 compile_expr, Assign arm. O(1) excluding realization of the
    /// already visited operand. Assignment facts are final on entry.
    pub(super) fn finish_assignment(&mut self, cx: Cx, var: VarId, child: Probed) -> Probed {
        let mut out = self.realize(Cx { cont: Cont::Value(Tail::No), ..cx }, child);
        let value = out.value.take().unwrap_or_else(|| self.pure_expression(View::JUndefined, 0));
        let statement = super::super::j::assign(&mut self.arena, var, value);
        self.statements.push(statement);
        let unit = self.pure_expression(View::JUndefined, 0);
        let tail = self.leaf(cx, unit);
        out.stmts = self.statements.since(Span { start: out.stmts.start, len: 0 });
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
    fn assignment_all_continuations() {
        let mut a = LamArena::new();
        let value = a.const_(Constant::Int { i: 42, comment: None });
        let root = a.assign(Ident::new("mutable", 10, IdentFlags::NONE), value);
        compare(a, root);
    }
}
