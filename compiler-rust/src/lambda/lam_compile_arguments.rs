//! Left-to-right evaluation of compiled call and literal arguments.
//!
//! Port of `delay_safe`, `evaluate_now`, `evaluate_all_now`,
//! `sequence_arguments` and `compile_arguments` from
//! `compiler/core/lam_compile.ml`.

use super::js_exp_make::js_expr_no_side_effects;
use super::js_pass_external_shadow::is_js_global;
use super::lam_compile::LambdaCompiler;
use crate::ident::Ident;
use crate::js_ir::BinOp;
use crate::js_ir::arena::{Block, Expr, ExprKind, JsArena, PropName, Stmt, StmtKind};
use crate::js_ir::build::{exp as JE, stmt as JS};
use crate::lambda::arena::{Lam, LamArena};
use crate::lambda::lam_compat::LetKind;
use ahash::AHashSet;

/// Compiled arguments of a call, primitive or literal, each with the
/// statements it needs first. Most have at most a few, so they stay off the
/// heap.
pub(crate) type HeldArgs = smallvec::SmallVec<[(Block, Expr); 4]>;

/// The values of compiled arguments.
pub(crate) type ArgValues = smallvec::SmallVec<[Expr; 4]>;

/// `delay_safe`: local immutable values and pure operations on them may be
/// evaluated after later arguments; heap reads and JS globals may not.
pub(crate) fn delay_safe(j: &JsArena, assignable: &AHashSet<Ident>, e: Expr) -> bool {
    let safe = |e| delay_safe(j, assignable, e);
    match j.ek(e) {
        ExprKind::Undefined { .. }
        | ExprKind::Null
        | ExprKind::Bool(_)
        | ExprKind::Number(_)
        | ExprKind::Str(_)
        | ExprKind::TemplateLiteral(_)
        | ExprKind::JsonLiteral(_)
        | ExprKind::Fun(_)
        | ExprKind::Qualified(_) => true,
        ExprKind::Var(id) => {
            let id = j.ident(id);
            !is_js_global(&id) && !assignable.contains(&id)
        }
        ExprKind::Bin(BinOp::Eq, _, _) => false,
        ExprKind::Bin(_, a, b) => js_expr_no_side_effects(j, e) && safe(a) && safe(b),
        ExprKind::StringAppend(a, b) => safe(a) && safe(b),
        ExprKind::JsNot(a)
        | ExprKind::JsBnot(a)
        | ExprKind::Typeof(a)
        | ExprKind::IsNullOrUndefined(a)
        | ExprKind::OptionalBlock(a, _) => safe(a),
        ExprKind::Cond(a, b, c) => safe(a) && safe(b) && safe(c),
        ExprKind::InterpolatedTemplate(_, values)
        | ExprKind::Array(values, _)
        | ExprKind::CamlBlock(values, _, _) => j.exprs(values).iter().all(|v| safe(*v)),
        ExprKind::Object(entries) => j.props(entries).iter().all(|(name, value)| match name {
            PropName::Lit(_) | PropName::Symbol => safe(*value),
            PropName::Spread | PropName::RecordSpread => false,
        }),
        _ => false,
    }
}

/// js_analyzer.ml `is_okay_to_duplicate`.
pub(crate) fn is_okay_to_duplicate(j: &JsArena, e: Expr) -> bool {
    match j.ek(e) {
        ExprKind::Var(_)
        | ExprKind::Qualified(_)
        | ExprKind::Bool(_)
        | ExprKind::Str(_)
        | ExprKind::TemplateLiteral(_)
        | ExprKind::Number(_) => true,
        ExprKind::StaticIndex(e, _, _) => is_okay_to_duplicate(j, e),
        _ => false,
    }
}

/// `define_variable ~kind:Strict`: undefined becomes a bare declaration.
pub(crate) fn define_strict_variable(ident: Ident, value: Expr, j: &mut JsArena) -> Stmt {
    let value = if matches!(j.ek(value), ExprKind::Undefined { .. }) {
        None
    } else {
        Some(value)
    };
    JS::define(ident, value, LetKind::Strict, j)
}

impl LambdaCompiler {
    /// Preserve literal shape while evaluating its elements now. A sequence's
    /// leading effects become statements; other unsafe values get temporaries.
    fn evaluate_now(&mut self, e: Expr) -> (Block, Expr) {
        if delay_safe(&self.j, &self.assignable, e) {
            return (Vec::new(), e);
        }
        let cold = self.j.expr_cold(e);
        match self.j.ek(e) {
            ExprKind::Seq(a, b) => {
                let (mut rest, b) = self.evaluate_now(b);
                if !js_expr_no_side_effects(&self.j, a) {
                    rest.insert(0, self.j.stmt(StmtKind::Exp(a)));
                }
                (rest, b)
            }
            ExprKind::Array(xs, mutable) => {
                let xs = self.j.expr_vec(xs);
                let (held, xs) = self.evaluate_all_now(xs);
                let xs = self.j.expr_list(&xs);
                (held, self.j.expr_with(ExprKind::Array(xs, mutable), cold))
            }
            ExprKind::CamlBlock(xs, mutable, tag) => {
                let xs = self.j.expr_vec(xs);
                let (held, xs) = self.evaluate_all_now(xs);
                let xs = self.j.expr_list(&xs);
                (
                    held,
                    self.j
                        .expr_with(ExprKind::CamlBlock(xs, mutable, tag), cold),
                )
            }
            ExprKind::Object(entries)
                if self
                    .j
                    .props(entries)
                    .iter()
                    .all(|(name, _)| matches!(name, PropName::Lit(_) | PropName::Symbol)) =>
            {
                let (keys, values): (Vec<_>, Vec<_>) =
                    self.j.props(entries).iter().copied().unzip();
                let (held, values) = self.evaluate_all_now(values);
                let entries: Vec<_> = keys.into_iter().zip(values).collect();
                let entries = self.j.prop_list(&entries);
                (held, self.j.expr_with(ExprKind::Object(entries), cold))
            }
            _ => {
                let tmp = self.fresh_tmp_ident();
                let statement = define_strict_variable(tmp, e, &mut self.j);
                (vec![statement], JE::var(tmp, &mut self.j))
            }
        }
    }

    /// `evaluate_all_now`: evaluate literal elements left to right.
    fn evaluate_all_now(&mut self, xs: Vec<Expr>) -> (Block, Vec<Expr>) {
        let mut held = Vec::new();
        let mut values = Vec::with_capacity(xs.len());
        for x in xs {
            let (block, x) = self.evaluate_now(x);
            held.extend(block);
            values.push(x);
        }
        (held, values)
    }

    /// `sequence_arguments`: allocate temporaries right to left, then emit
    /// argument effects left to right. A method callee retains its receiver.
    pub(crate) fn sequence_arguments(
        &mut self,
        method_callee: bool,
        args: HeldArgs,
    ) -> (Block, ArgValues) {
        if !args.iter().skip(1).any(|(block, _)| !block.is_empty()) {
            let mut code = Vec::new();
            let mut values = ArgValues::with_capacity(args.len());
            for (block, value) in args {
                code.extend(block);
                values.push(value);
            }
            return (code, values);
        }
        let mut chunks: Vec<Block> = Vec::with_capacity(args.len() * 2);
        let mut has_code = false;
        let mut values = ArgValues::with_capacity(args.len());
        for (i, (block, value)) in args.into_iter().enumerate().rev() {
            let (held, value) = if !has_code {
                (Vec::new(), value)
            } else {
                match self.j.ek(value) {
                    ExprKind::StaticIndex(obj, name, pos) if method_callee && i == 0 => {
                        let cold = self.j.expr_cold(value);
                        let (held, obj) = self.evaluate_now(obj);
                        (
                            held,
                            self.j
                                .expr_with(ExprKind::StaticIndex(obj, name, pos), cold),
                        )
                    }
                    _ => self.evaluate_now(value),
                }
            };
            has_code |= !block.is_empty() || !held.is_empty();
            chunks.push(held);
            chunks.push(block);
            values.push(value);
        }
        let mut code = Vec::with_capacity(chunks.iter().map(Vec::len).sum());
        for chunk in chunks.into_iter().rev() {
            code.extend(chunk);
        }
        values.reverse();
        (code, values)
    }

    /// lam_compile.ml `compile_arguments`: compiles the arguments of a call
    /// or literal, then orders them with `sequence_arguments`.
    pub(crate) fn compile_arguments(
        &mut self,
        a: &mut LamArena,
        method_callee: bool,
        args: impl IntoIterator<Item = Lam>,
    ) -> (Block, ArgValues) {
        let compiled = self.compile_each_argument(a, args);
        self.sequence_arguments(method_callee, compiled)
    }

    /// The first half of `compile_arguments`: each argument compiled left to
    /// right in `NeedValue Not_tail` (`Ext_list.map`). `compile_arguments
    /// ?hold` adds statements to the result, such as the bindings of
    /// `hold_external_args`, before it is sequenced.
    pub(crate) fn compile_each_argument(
        &mut self,
        a: &mut LamArena,
        args: impl IntoIterator<Item = Lam>,
    ) -> HeldArgs {
        args.into_iter()
            .map(|arg| {
                let compiled = self.compile_expr(a, arg);
                (compiled.prelude, compiled.expr)
            })
            .collect()
    }

    /// Extends `assignable` with the variables `lam` assigns that are not
    /// already in it, and returns them so the caller can drop them again.
    /// lam_compile.ml scopes the union to the inlined body
    /// (`compile_lambda {lambda_cxt with meta} inlined`).
    pub(crate) fn extend_assignable(&mut self, a: &LamArena, lam: Lam) -> Vec<Ident> {
        let mut added = Vec::new();
        for id in crate::lambda::lambda_traverse::arena_assigned_variables(a, lam) {
            if self.assignable.insert(id) {
                added.push(id);
            }
        }
        added
    }

    pub(crate) fn restore_assignable(&mut self, added: Vec<Ident>) {
        for id in added {
            self.assignable.remove(&id);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::js_ir::CallInfo;
    use crate::lambda::Lambda;

    fn call(j: &mut JsArena, name: &str) -> Expr {
        let callee = JE::var(Ident::create_persistent(name), j);
        JE::call(callee, &[], CallInfo::default(), j)
    }

    fn is_array(j: &mut JsArena, arg: Expr) -> Expr {
        let array = JE::var(Ident::create_persistent("Array"), j);
        let callee = JE::static_index(array, "isArray", None, j);
        JE::call(callee, &[arg], CallInfo::default(), j)
    }

    fn exp_statement(j: &JsArena, s: Stmt) -> Expr {
        match j.sk(s) {
            StmtKind::Exp(e) => e,
            other => panic!("expected an expression statement, got {other:?}"),
        }
    }

    fn later_statement(j: &mut JsArena) -> Block {
        let effect = call(j, "effect");
        vec![JS::exp(effect, j)]
    }

    #[test]
    fn evaluate_now_drops_pure_array_is_array_in_sequence() {
        let mut compiler = LambdaCompiler::new();
        let x = compiler.fresh_ident("x");
        let x = JE::var(x, &mut compiler.j);
        let pure = is_array(&mut compiler.j, x);
        let effect = call(&mut compiler.j, "effect");
        let seq = compiler.j.expr(ExprKind::Seq(pure, effect));
        let (held, value) = compiler.evaluate_now(seq);
        assert_eq!(held.len(), 1, "only the tail gets a temporary: {held:?}");
        assert!(matches!(compiler.j.sk(held[0]), StmtKind::Variable(_)));
        assert!(matches!(compiler.j.ek(value), ExprKind::Var(_)));
    }

    #[test]
    fn evaluate_now_keeps_array_is_array_with_effectful_argument() {
        let mut compiler = LambdaCompiler::new();
        let effect = call(&mut compiler.j, "effect");
        let check = is_array(&mut compiler.j, effect);
        let seq = compiler.j.expr(ExprKind::Seq(check, effect));
        let (held, _) = compiler.evaluate_now(seq);
        assert_eq!(held.len(), 2);
        assert!(matches!(
            compiler.j.ek(exp_statement(&compiler.j, held[0])),
            ExprKind::Call(..)
        ));
    }

    #[test]
    fn evaluate_now_splits_nested_sequences_left_to_right() {
        let mut compiler = LambdaCompiler::new();
        let first = call(&mut compiler.j, "first");
        let second = call(&mut compiler.j, "second");
        let effect = call(&mut compiler.j, "effect");
        let rest = compiler.j.expr(ExprKind::Seq(second, effect));
        let seq = compiler.j.expr(ExprKind::Seq(first, rest));
        let (held, value) = compiler.evaluate_now(seq);
        assert_eq!(held.len(), 3);
        for (statement, name) in held[..2].iter().zip(["first", "second"]) {
            let ExprKind::Call(callee, _, _) =
                compiler.j.ek(exp_statement(&compiler.j, *statement))
            else {
                panic!("expected a call");
            };
            assert!(
                matches!(compiler.j.ek(callee), ExprKind::Var(id) if compiler.j.ident(id).name() == name)
            );
        }
        assert!(matches!(compiler.j.ek(value), ExprKind::Var(_)));
    }

    #[test]
    fn sequence_arguments_holds_method_object_not_property_read() {
        let mut compiler = LambdaCompiler::new();
        let obj = compiler.fresh_ident("obj");
        compiler.assignable.insert(obj);
        let receiver = JE::var(obj, &mut compiler.j);
        let callee = JE::static_index(receiver, "m", None, &mut compiler.j);
        let later = later_statement(&mut compiler.j);
        let value = JE::string("v", &mut compiler.j);
        let (code, values) = compiler.sequence_arguments(
            true,
            HeldArgs::from_vec(vec![(vec![], callee), (later, value)]),
        );
        assert_eq!(code.len(), 2, "held object, then the argument's statement");
        let StmtKind::Variable(decl) = compiler.j.sk(code[0]) else {
            panic!("expected held object");
        };
        let decl = compiler.j.var(decl);
        assert!(
            matches!(decl.value.map(|v| compiler.j.ek(v)), Some(ExprKind::Var(id)) if compiler.j.ident(id) == obj)
        );
        let ExprKind::StaticIndex(target, name, _) = compiler.j.ek(values[0]) else {
            panic!("property read stays in call");
        };
        assert_eq!(compiler.j.text(name), "m");
        assert!(
            matches!(compiler.j.ek(target), ExprKind::Var(id) if compiler.j.ident(id) == decl.ident)
        );
    }

    #[test]
    fn sequence_arguments_allocates_temporaries_right_to_left() {
        let mut compiler = LambdaCompiler::new();
        let obj = JE::var(Ident::create_persistent("o"), &mut compiler.j);
        let a = JE::static_index(obj, "a", None, &mut compiler.j);
        let b = JE::static_index(obj, "b", None, &mut compiler.j);
        let later = later_statement(&mut compiler.j);
        let value = JE::string("v", &mut compiler.j);
        let (code, values) = compiler.sequence_arguments(
            false,
            HeldArgs::from_vec(vec![(vec![], a), (vec![], b), (later, value)]),
        );
        assert_eq!(code.len(), 3);
        let held: Vec<Ident> = code[..2]
            .iter()
            .map(|s| match compiler.j.sk(*s) {
                StmtKind::Variable(decl) => compiler.j.var(decl).ident,
                other => panic!("expected temporary, got {other:?}"),
            })
            .collect();
        assert!(held[1].stamp() < held[0].stamp(), "{held:?}");
        assert!(matches!(compiler.j.sk(code[2]), StmtKind::Exp(_)));
        assert!(
            matches!(compiler.j.ek(values[0]), ExprKind::Var(id) if compiler.j.ident(id) == held[0])
        );
    }

    fn unit_assign(id: Ident) -> Lambda {
        Lambda::assign(id, Lambda::unit())
    }

    fn function_body(body: Lambda) -> Lambda {
        Lambda::function_(
            0,
            vec![],
            body,
            crate::lambda::FunctionAttribute::default(),
            crate::lambda::LamLoc::NONE,
        )
    }

    fn assignable_names(compiler: &LambdaCompiler) -> Vec<Ident> {
        let mut ids: Vec<Ident> = compiler.assignable.iter().copied().collect();
        ids.sort_by_key(|id| id.stamp());
        ids
    }

    /// lambda_traverse.ml `assigned_variables`: every `Lassign` target,
    /// including those inside function bodies, once each; two idents with
    /// the same name but different stamps stay distinct.
    #[test]
    fn assigned_variables_collects_targets_by_identity() {
        let compiler = LambdaCompiler::new();
        let x = compiler.fresh_ident("x");
        let x_other = compiler.fresh_ident("x");
        let y = compiler.fresh_ident("y");
        let lam = Lambda::seq(
            unit_assign(x),
            Lambda::seq(
                function_body(Lambda::seq(unit_assign(y), unit_assign(x))),
                Lambda::var(x_other),
            ),
        );
        let assigned = crate::lambda::lambda_traverse::assigned_variables(&lam);
        assert_eq!(assigned.len(), 2);
        assert!(assigned.contains(&x) && assigned.contains(&y));
        assert!(!assigned.contains(&x_other));
    }

    /// The variables an inlined body assigns change the hold decision while
    /// that body compiles: a read of one is no longer `delay_safe`, so
    /// `evaluate_now` binds it to a temporary. After `restore_assignable`
    /// the read is safe to delay again.
    #[test]
    fn extended_assignable_changes_hold_decision_until_restored() {
        let mut compiler = LambdaCompiler::new();
        let r = compiler.fresh_ident("r");
        let r_expr = JE::var(r, &mut compiler.j);
        assert!(delay_safe(&compiler.j, &compiler.assignable, r_expr));
        let mut arena = LamArena::new();
        let lam = arena.import(&Lambda::seq(unit_assign(r), Lambda::var(r)));
        let added = compiler.extend_assignable(&arena, lam);
        assert_eq!(added, vec![r]);
        assert!(!delay_safe(&compiler.j, &compiler.assignable, r_expr));
        let (held, value) = compiler.evaluate_now(r_expr);
        let [statement] = held.as_slice() else {
            panic!("expected one temporary: {held:?}");
        };
        let StmtKind::Variable(decl) = compiler.j.sk(*statement) else {
            panic!("expected a temporary");
        };
        let decl = compiler.j.var(decl);
        assert!(
            matches!(decl.value.map(|v| compiler.j.ek(v)), Some(ExprKind::Var(id)) if compiler.j.ident(id) == r)
        );
        assert!(
            matches!(compiler.j.ek(value), ExprKind::Var(id) if compiler.j.ident(id) == decl.ident)
        );
        compiler.restore_assignable(added);
        assert!(compiler.assignable.is_empty());
        assert!(delay_safe(&compiler.j, &compiler.assignable, r_expr));
    }

    /// Nested inlined bodies: each extension adds only the ids not already
    /// assignable, so restoring the inner body keeps the outer body's and
    /// the module's ids, and restoring the outer body gives back exactly
    /// the module's set.
    #[test]
    fn nested_assignable_extensions_restore_exactly() {
        let mut compiler = LambdaCompiler::new();
        let module_var = compiler.fresh_ident("m");
        let a = compiler.fresh_ident("a");
        let b = compiler.fresh_ident("b");
        let a_same_name = compiler.fresh_ident("a");
        let a_expr = JE::var(a, &mut compiler.j);
        let module_expr = JE::var(module_var, &mut compiler.j);
        let same_name_expr = JE::var(a_same_name, &mut compiler.j);
        compiler.assignable.insert(module_var);
        let original = assignable_names(&compiler);

        let mut arena = LamArena::new();
        let outer_body = arena.import(&Lambda::seq(unit_assign(module_var), unit_assign(a)));
        let outer = compiler.extend_assignable(&arena, outer_body);
        assert_eq!(outer, vec![a]);
        let after_outer = assignable_names(&compiler);

        let inner_body = Lambda::seq(
            unit_assign(a),
            Lambda::seq(
                unit_assign(module_var),
                function_body(Lambda::seq(unit_assign(b), unit_assign(b))),
            ),
        );
        let inner_body = arena.import(&inner_body);
        let mut inner = compiler.extend_assignable(&arena, inner_body);
        assert_eq!(inner, vec![b]);
        assert!(delay_safe(
            &compiler.j,
            &compiler.assignable,
            same_name_expr
        ));

        let same_name_body = arena.import(&unit_assign(a_same_name));
        let inner_same_name = compiler.extend_assignable(&arena, same_name_body);
        assert_eq!(inner_same_name, vec![a_same_name]);
        assert!(!delay_safe(
            &compiler.j,
            &compiler.assignable,
            same_name_expr
        ));
        compiler.restore_assignable(inner_same_name);
        assert!(delay_safe(
            &compiler.j,
            &compiler.assignable,
            same_name_expr
        ));

        compiler.restore_assignable(std::mem::take(&mut inner));
        assert_eq!(assignable_names(&compiler), after_outer);
        assert!(!delay_safe(&compiler.j, &compiler.assignable, a_expr));
        assert!(!delay_safe(&compiler.j, &compiler.assignable, module_expr));

        compiler.restore_assignable(outer);
        assert_eq!(assignable_names(&compiler), original);
        assert!(delay_safe(&compiler.j, &compiler.assignable, a_expr));
        assert!(!delay_safe(&compiler.j, &compiler.assignable, module_expr));
    }

    /// `sequence_arguments` stays linear in the number of arguments.
    #[test]
    fn sequence_arguments_handles_long_argument_lists() {
        let mut compiler = LambdaCompiler::new();
        let value = JE::string("v", &mut compiler.j);
        let args: HeldArgs = (0..20_000)
            .map(|_| (later_statement(&mut compiler.j), value))
            .collect();
        let (code, values) = compiler.sequence_arguments(false, args);
        assert_eq!(values.len(), 20_000);
        assert_eq!(code.len(), 20_000);
    }
}
