//! Left-to-right evaluation of compiled call and literal arguments.
//!
//! Port of `delay_safe`, `evaluate_now`, `evaluate_all_now`,
//! `sequence_arguments` and `compile_arguments` from
//! `compiler/core/lam_compile.ml`.

use super::js_exp_make::js_expr_no_side_effects;
use super::js_pass_external_shadow::is_js_global;
use super::lam_compile::LambdaCompiler;
use crate::ident::Ident;
use crate::js_ir::op::IdentInfo;
use crate::js_ir::{
    BinOp, Block, Expression, ExpressionDesc, ObjectEntry, Statement, StatementDesc, VIdent,
    VariableDeclaration,
};
use crate::lambda::Lambda;
use crate::lambda::lam_compat::LetKind;
use ahash::AHashSet;

/// lam_compile.ml `delay_safe`: whether evaluating `e` later, after other
/// code, gives the same value and the same effects as evaluating it now:
/// constants, functions, immutable local variables and pure operations on
/// them. `assignable` are the local variables some `Lassign` assigns; the
/// other code, or a closure it calls, may assign them. JS globals (`@val`)
/// and reads of the heap (fields, array elements, lengths) may change too.
pub(crate) fn delay_safe(assignable: &AHashSet<Ident>, e: &Expression) -> bool {
    match &e.desc {
        ExpressionDesc::Undefined { .. }
        | ExpressionDesc::Null
        | ExpressionDesc::Bool(_)
        | ExpressionDesc::Number(_)
        | ExpressionDesc::Str(_)
        | ExpressionDesc::TemplateLiteral(_)
        | ExpressionDesc::JsonLiteral(_)
        | ExpressionDesc::Fun { .. }
        | ExpressionDesc::Var(VIdent::Qualified(..)) => true,
        // `not (Ext_ident.is_js id)`: Rust creates JS globals as persistent
        // idents, which `is_js_global` recognizes.
        ExpressionDesc::Var(VIdent::Id(id)) => !is_js_global(id) && !assignable.contains(id),
        ExpressionDesc::Bin(BinOp::Eq, _, _) => false,
        ExpressionDesc::Bin(_, a, b) => {
            js_expr_no_side_effects(e) && delay_safe(assignable, a) && delay_safe(assignable, b)
        }
        ExpressionDesc::StringAppend(a, b) => {
            delay_safe(assignable, a) && delay_safe(assignable, b)
        }
        ExpressionDesc::JsNot(a)
        | ExpressionDesc::JsBnot(a)
        | ExpressionDesc::Typeof(a)
        | ExpressionDesc::IsNullOrUndefined(a)
        | ExpressionDesc::OptionalBlock(a, _) => delay_safe(assignable, a),
        ExpressionDesc::Cond(a, b, c) => {
            delay_safe(assignable, a) && delay_safe(assignable, b) && delay_safe(assignable, c)
        }
        ExpressionDesc::InterpolatedTemplate { values, .. } => {
            values.iter().all(|v| delay_safe(assignable, v))
        }
        ExpressionDesc::Array(xs, _) | ExpressionDesc::CamlBlock(xs, _, _) => {
            xs.iter().all(|x| delay_safe(assignable, x))
        }
        ExpressionDesc::Object(entries) => entries.iter().all(|entry| match entry {
            ObjectEntry::Property(_, v) => delay_safe(assignable, v),
            ObjectEntry::RecordSpread(_) | ObjectEntry::Spread(_) => false,
        }),
        _ => false,
    }
}

/// js_analyzer.ml `is_okay_to_duplicate`.
pub(crate) fn is_okay_to_duplicate(e: &Expression) -> bool {
    match &e.desc {
        ExpressionDesc::Var(_)
        | ExpressionDesc::Bool(_)
        | ExpressionDesc::Str(_)
        | ExpressionDesc::TemplateLiteral(_)
        | ExpressionDesc::Number(_) => true,
        ExpressionDesc::StaticIndex(e, _, _) => is_okay_to_duplicate(e),
        _ => false,
    }
}

/// js_stmt_make.ml `define_variable ~kind:Strict v e`: an `Undefined` value
/// becomes a bare declaration (`declare_variable`).
pub(crate) fn define_strict_variable(ident: Ident, value: Expression) -> Statement {
    let value = match value.desc {
        ExpressionDesc::Undefined { .. } => None,
        _ => Some(value),
    };
    Statement::variable(VariableDeclaration {
        ident,
        value,
        property: LetKind::Strict,
        ident_info: IdentInfo::default(),
    })
}

impl LambdaCompiler {
    /// lam_compile.ml `evaluate_now`: statements that evaluate `e` now, and
    /// the expression that stands for its value afterwards. A sequence's
    /// leading expressions become statements of their own, and the last one
    /// gets a temporary unless it is `delay_safe`. A literal stays in place
    /// and its elements are evaluated now instead, which keeps it visible to
    /// translations that look into their arguments (dict rows, `@variadic`).
    fn evaluate_now(&self, e: Expression) -> (Block, Expression) {
        if delay_safe(&self.assignable, &e) {
            return (Vec::new(), e);
        }
        let Expression {
            desc,
            comment,
            source_loc,
        } = e;
        let rebuild = |desc| Expression {
            desc,
            comment,
            source_loc,
        };
        match desc {
            ExpressionDesc::Seq(a, b) => {
                let (mut rest, b) = self.evaluate_now(*b);
                if !js_expr_no_side_effects(&a) {
                    // `{J.statement_desc = Exp a; comment = None;
                    // source_loc = None}`: built directly, not through `S.exp`.
                    rest.insert(
                        0,
                        Statement {
                            desc: StatementDesc::Exp(*a),
                            comment: None,
                            source_loc: None,
                        },
                    );
                }
                (rest, b)
            }
            ExpressionDesc::Array(xs, mutable_flag) => {
                let (held, xs) = self.evaluate_all_now(xs);
                (held, rebuild(ExpressionDesc::Array(xs, mutable_flag)))
            }
            ExpressionDesc::CamlBlock(xs, mutable_flag, tag) => {
                let (held, xs) = self.evaluate_all_now(xs);
                (
                    held,
                    rebuild(ExpressionDesc::CamlBlock(xs, mutable_flag, tag)),
                )
            }
            ExpressionDesc::Object(entries)
                if entries
                    .iter()
                    .all(|entry| matches!(entry, ObjectEntry::Property(..))) =>
            {
                let (keys, values): (Vec<_>, Vec<_>) = entries
                    .into_iter()
                    .map(|entry| match entry {
                        ObjectEntry::Property(k, v) => (k, v),
                        ObjectEntry::RecordSpread(_) | ObjectEntry::Spread(_) => unreachable!(),
                    })
                    .unzip();
                let (held, values) = self.evaluate_all_now(values);
                let entries = keys
                    .into_iter()
                    .zip(values)
                    .map(|(k, v)| ObjectEntry::Property(k, v))
                    .collect();
                (held, rebuild(ExpressionDesc::Object(entries)))
            }
            desc => {
                // `Ext_ident.create_tmp ()` and
                // `S.define_variable ~kind:Strict tmp e`.
                let tmp = self.fresh_tmp_ident();
                let statement = define_strict_variable(tmp, rebuild(desc));
                (vec![statement], Expression::var(tmp))
            }
        }
    }

    /// lam_compile.ml `evaluate_all_now`: `evaluate_now` on each of `xs`,
    /// left to right (`Ext_list.split_map`).
    fn evaluate_all_now(&self, xs: Vec<Expression>) -> (Block, Vec<Expression>) {
        let mut held = Vec::new();
        let mut values = Vec::with_capacity(xs.len());
        for x in xs {
            let (block, x) = self.evaluate_now(x);
            held.extend(block);
            values.push(x);
        }
        (held, values)
    }

    /// lam_compile.ml `sequence_arguments`: assembles compiled arguments of a
    /// call or literal evaluated left to right. When an argument has
    /// statements, every argument to its left is evaluated before them with
    /// `evaluate_now`. With `method_callee`, the first argument is a JS
    /// method read `obj.m` being called: the object is held and the property
    /// read stays in the call, so `obj` is still `this`.
    pub(crate) fn sequence_arguments(
        &self,
        method_callee: bool,
        args: Vec<(Block, Expression)>,
    ) -> (Block, Vec<Expression>) {
        let later_statements = args.iter().skip(1).any(|(block, _)| !block.is_empty());
        if !later_statements {
            let mut code = Vec::new();
            let mut values = Vec::with_capacity(args.len());
            for (block, value) in args {
                code.extend(block);
                values.push(value);
            }
            return (code, values);
        }
        // `Ext_list.fold_right`: the last argument is processed first, so
        // temporaries are allocated right to left as in OCaml. Each step
        // prepends `block @ held` to the code after it; the chunks are kept
        // and joined once at the end instead of copying that code each time.
        let mut chunks: Vec<Block> = Vec::with_capacity(args.len() * 2);
        let mut has_code = false;
        let mut values = Vec::with_capacity(args.len());
        for (i, (block, value)) in args.into_iter().enumerate().rev() {
            let (held, value) = if !has_code {
                (Vec::new(), value)
            } else {
                match value {
                    Expression {
                        desc: ExpressionDesc::StaticIndex(obj, name, pos),
                        comment,
                        source_loc,
                    } if method_callee && i == 0 => {
                        let (held, obj) = self.evaluate_now(*obj);
                        (
                            held,
                            Expression {
                                desc: ExpressionDesc::StaticIndex(Box::new(obj), name, pos),
                                comment,
                                source_loc,
                            },
                        )
                    }
                    value => self.evaluate_now(value),
                }
            };
            has_code |= !block.is_empty() || !held.is_empty();
            // `Ext_list.append block (Ext_list.append held code)`, in reverse.
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
    /// or literal (`Ext_list.map`, left to right, in `NeedValue Not_tail`),
    /// then orders them with `sequence_arguments`.
    pub(crate) fn compile_arguments<'a>(
        &mut self,
        method_callee: bool,
        args: impl IntoIterator<Item = &'a Lambda>,
    ) -> (Block, Vec<Expression>) {
        let compiled = args
            .into_iter()
            .map(|arg| {
                let compiled = self.compile_expr(arg);
                (compiled.prelude, compiled.expr)
            })
            .collect();
        self.sequence_arguments(method_callee, compiled)
    }

    /// Extends `assignable` with the variables `lam` assigns that are not
    /// already in it, and returns them so the caller can drop them again.
    /// lam_compile.ml scopes the union to the inlined body
    /// (`compile_lambda {lambda_cxt with meta} inlined`).
    pub(crate) fn extend_assignable(&mut self, lam: &Lambda) -> Vec<Ident> {
        let mut added = Vec::new();
        for id in crate::lambda::lambda_traverse::assigned_variables(lam) {
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

    fn var(id: Ident) -> Expression {
        Expression::var(id)
    }

    fn seq(a: Expression, b: Expression) -> Expression {
        Expression::new(ExpressionDesc::Seq(Box::new(a), Box::new(b)))
    }

    fn is_array(arg: Expression) -> Expression {
        let callee = Expression::new(ExpressionDesc::StaticIndex(
            Box::new(var(Ident::create_persistent("Array"))),
            "isArray".to_string(),
            None,
        ));
        Expression::call(callee, vec![arg], CallInfo::default())
    }

    fn effect() -> Expression {
        Expression::call(
            var(Ident::create_persistent("effect")),
            vec![],
            CallInfo::default(),
        )
    }

    fn exp_statement(s: &Statement) -> &Expression {
        match &s.desc {
            StatementDesc::Exp(e) => e,
            other => panic!("expected an expression statement, got {other:?}"),
        }
    }

    fn later_statement() -> Block {
        vec![Statement::exp(effect())]
    }

    /// js_analyzer.ml: `Array.isArray(x)` has no side effect when `x` has
    /// none, so the leading expression of a sequence is dropped.
    #[test]
    fn evaluate_now_drops_pure_array_is_array_in_sequence() {
        let compiler = LambdaCompiler::new();
        let x = compiler.fresh_ident("x");
        let (held, value) = compiler.evaluate_now(seq(is_array(var(x)), effect()));
        assert_eq!(held.len(), 1, "only the tail gets a temporary: {held:?}");
        assert!(matches!(held[0].desc, StatementDesc::Variable(_)));
        assert!(matches!(value.desc, ExpressionDesc::Var(VIdent::Id(_))));
    }

    /// The argument of `Array.isArray` is evaluated for its effects: an
    /// impure argument keeps the leading expression as a statement.
    #[test]
    fn evaluate_now_keeps_array_is_array_with_effectful_argument() {
        let compiler = LambdaCompiler::new();
        let (held, _) = compiler.evaluate_now(seq(is_array(effect()), effect()));
        assert_eq!(held.len(), 2);
        assert!(matches!(
            exp_statement(&held[0]).desc,
            ExpressionDesc::Call(..)
        ));
    }

    /// `Seq (a, Seq (b, c))`: each impure leading expression becomes its own
    /// statement, left to right, and the last value gets a temporary.
    #[test]
    fn evaluate_now_splits_nested_sequences_left_to_right() {
        let compiler = LambdaCompiler::new();
        let first = Ident::create_persistent("first");
        let second = Ident::create_persistent("second");
        let call = |id| Expression::call(var(id), vec![], CallInfo::default());
        let (held, value) = compiler.evaluate_now(seq(call(first), seq(call(second), effect())));
        assert_eq!(held.len(), 3);
        for (statement, name) in held[..2].iter().zip(["first", "second"]) {
            let ExpressionDesc::Call(callee, _, _) = &exp_statement(statement).desc else {
                panic!("expected a call");
            };
            assert!(
                matches!(&callee.desc, ExpressionDesc::Var(VIdent::Id(id)) if id.name() == name)
            );
        }
        assert!(matches!(value.desc, ExpressionDesc::Var(VIdent::Id(_))));
    }

    /// A JS method callee keeps its property read so the object stays
    /// `this`; only the object is held.
    #[test]
    fn sequence_arguments_holds_method_object_not_property_read() {
        let mut compiler = LambdaCompiler::new();
        let obj = compiler.fresh_ident("obj");
        compiler.assignable.insert(obj);
        let callee = Expression::new(ExpressionDesc::StaticIndex(
            Box::new(var(obj)),
            "m".to_string(),
            None,
        ));
        let (code, values) = compiler.sequence_arguments(
            true,
            vec![
                (vec![], callee),
                (later_statement(), Expression::string("v")),
            ],
        );
        assert_eq!(code.len(), 2, "held object, then the argument's statement");
        let StatementDesc::Variable(decl) = &code[0].desc else {
            panic!("expected the object to be held");
        };
        assert!(matches!(
            decl.value.as_ref().map(|v| &v.desc),
            Some(ExpressionDesc::Var(VIdent::Id(id))) if *id == obj
        ));
        let ExpressionDesc::StaticIndex(target, name, _) = &values[0].desc else {
            panic!("the property read stays in the call");
        };
        assert_eq!(name, "m");
        assert!(matches!(&target.desc, ExpressionDesc::Var(VIdent::Id(id)) if *id == decl.ident));
    }

    /// Temporaries are allocated right to left, as OCaml's
    /// `Ext_list.fold_right`, and the statements keep left-to-right order.
    #[test]
    fn sequence_arguments_allocates_temporaries_right_to_left() {
        let compiler = LambdaCompiler::new();
        let read = |name: &str| {
            Expression::new(ExpressionDesc::StaticIndex(
                Box::new(var(Ident::create_persistent("o"))),
                name.to_string(),
                None,
            ))
        };
        let (code, values) = compiler.sequence_arguments(
            false,
            vec![
                (vec![], read("a")),
                (vec![], read("b")),
                (later_statement(), Expression::string("v")),
            ],
        );
        assert_eq!(code.len(), 3);
        let held: Vec<Ident> = code[..2]
            .iter()
            .map(|s| match &s.desc {
                StatementDesc::Variable(decl) => decl.ident,
                other => panic!("expected a temporary, got {other:?}"),
            })
            .collect();
        assert!(held[1].stamp() < held[0].stamp(), "{held:?}");
        assert!(matches!(code[2].desc, StatementDesc::Exp(_)));
        assert!(matches!(&values[0].desc, ExpressionDesc::Var(VIdent::Id(id)) if *id == held[0]));
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
        assert!(delay_safe(&compiler.assignable, &var(r)));
        let added = compiler.extend_assignable(&Lambda::seq(unit_assign(r), Lambda::var(r)));
        assert_eq!(added, vec![r]);
        assert!(!delay_safe(&compiler.assignable, &var(r)));
        let (held, value) = compiler.evaluate_now(var(r));
        let [statement] = held.as_slice() else {
            panic!("expected one temporary: {held:?}");
        };
        let StatementDesc::Variable(decl) = &statement.desc else {
            panic!("expected a temporary");
        };
        assert!(matches!(
            decl.value.as_ref().map(|v| &v.desc),
            Some(ExpressionDesc::Var(VIdent::Id(id))) if *id == r
        ));
        assert!(matches!(&value.desc, ExpressionDesc::Var(VIdent::Id(id)) if *id == decl.ident));
        compiler.restore_assignable(added);
        assert!(compiler.assignable.is_empty());
        assert!(delay_safe(&compiler.assignable, &var(r)));
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
        compiler.assignable.insert(module_var);
        let original = assignable_names(&compiler);

        let outer =
            compiler.extend_assignable(&Lambda::seq(unit_assign(module_var), unit_assign(a)));
        assert_eq!(outer, vec![a]);
        let after_outer = assignable_names(&compiler);

        let inner_body = Lambda::seq(
            unit_assign(a),
            Lambda::seq(
                unit_assign(module_var),
                function_body(Lambda::seq(unit_assign(b), unit_assign(b))),
            ),
        );
        let mut inner = compiler.extend_assignable(&inner_body);
        assert_eq!(inner, vec![b]);
        assert!(delay_safe(&compiler.assignable, &var(a_same_name)));

        let inner_same_name = compiler.extend_assignable(&unit_assign(a_same_name));
        assert_eq!(inner_same_name, vec![a_same_name]);
        assert!(!delay_safe(&compiler.assignable, &var(a_same_name)));
        compiler.restore_assignable(inner_same_name);
        assert!(delay_safe(&compiler.assignable, &var(a_same_name)));

        compiler.restore_assignable(std::mem::take(&mut inner));
        assert_eq!(assignable_names(&compiler), after_outer);
        assert!(!delay_safe(&compiler.assignable, &var(a)));
        assert!(!delay_safe(&compiler.assignable, &var(module_var)));

        compiler.restore_assignable(outer);
        assert_eq!(assignable_names(&compiler), original);
        assert!(delay_safe(&compiler.assignable, &var(a)));
        assert!(!delay_safe(&compiler.assignable, &var(module_var)));
    }

    /// `sequence_arguments` stays linear in the number of arguments.
    #[test]
    fn sequence_arguments_handles_long_argument_lists() {
        let compiler = LambdaCompiler::new();
        let args: Vec<(Block, Expression)> = (0..20_000)
            .map(|_| (later_statement(), Expression::string("v")))
            .collect();
        let (code, values) = compiler.sequence_arguments(false, args);
        assert_eq!(values.len(), 20_000);
        assert_eq!(code.len(), 20_000);
    }
}
