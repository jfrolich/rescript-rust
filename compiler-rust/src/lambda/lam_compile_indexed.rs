//! Mutable JS-lowering owner. Closed lowering operations take child continuations
//! explicitly while the remaining consumer modes are moved here. A continuation
//! receives the same owner and a NodeId, never a borrowed store or a Lambda tree.

use super::*;
use crate::lambda::indexed::NodeView;
use crate::lambda::lam_compile_input::LambdaInputs;
use crate::lambda::lam_indexed_helpers::append_rebuilt;

pub(crate) struct IndexedJsConsumer<'a> {
    pub(super) compiler: &'a mut LambdaCompiler,
    pub(super) context: &'a mut IndexedLambdaContext,
}

impl<'a> IndexedJsConsumer<'a> {
    pub(super) fn new(
        compiler: &'a mut LambdaCompiler,
        context: &'a mut IndexedLambdaContext,
    ) -> Self {
        Self { compiler, context }
    }

    /// NeedValue application lowering. `lower` is also the continuation for
    /// beta results and flattened applications, not just original children.
    pub(super) fn application(
        &mut self,
        application: NodeId,
        lower: &mut impl FnMut(&mut Self, NodeId) -> Compiled,
    ) -> Compiled {
        let loc = match self.context.store().view(application) {
            NodeView::Apply(_, _, info, _) => info.loc,
            _ => panic!("application lowering requires an application node"),
        };
        let mut compiled = self.application_inner(application, lower);
        if compiled.expr.source_loc.is_none() {
            compiled.expr.source_loc = self.compiler.source_loc(&loc);
        }
        compiled
    }

    fn application_inner(
        &mut self,
        application: NodeId,
        lower: &mut impl FnMut(&mut Self, NodeId) -> Compiled,
    ) -> Compiled {
        let (function, count, info, jsx) = match self.context.store().view(application) {
            NodeView::Apply(function, args, info, jsx) => (function, args.len(), info.clone(), jsx),
            _ => unreachable!("checked by application"),
        };
        // compiler/core/lam_compile.ml:1609-1623. Only the real flattening
        // operation collects an owned list of handles. Apply's smart constructor
        // can change the root, so immediately dispatch that returned ID.
        if info.status == ApplyStatus::Na {
            let flattened = match self.context.store().view(function) {
                NodeView::Apply(inner, inner_args, inner_info, _)
                    if inner_info.status == ApplyStatus::Na =>
                {
                    let mut merged_info = info.clone();
                    merged_info.inlined = inner_info.inlined;
                    let mut args = inner_args.to_vec();
                    let NodeView::Apply(_, outer_args, _, _) =
                        self.context.store().view(application)
                    else {
                        unreachable!()
                    };
                    args.extend_from_slice(outer_args);
                    Some((inner, args, merged_info))
                }
                _ => None,
            };
            if let Some((function, args, info)) = flattened {
                let merged = append_rebuilt(
                    self.context.store_mut(),
                    NodeSnapshot::Apply(function, args, info, jsx),
                );
                return lower(self, merged);
            }
        }

        // compiler/core/lam_compile.ml:342-357: the query/header test precedes
        // import and beta; compile the returned root in this SAME owner.
        if let Some(prepared) = self
            .compiler
            .prepare_indexed_external_field_apply(self.context, application)
        {
            return match prepared {
                PreparedIndexedExternalApply::Reduced(root) => lower(self, root),
                PreparedIndexedExternalApply::Call {
                    module,
                    field_name,
                    args,
                    info,
                    transformed_jsx,
                    known_arity,
                } => {
                    let (prelude, args) = self.call_arguments(args.len(), |_, i| args[i], lower);
                    let function = Expression::qualified(module, Some(field_name));
                    let expr = match info.status {
                        ApplyStatus::InferFull | ApplyStatus::Uncurry => Expression::call(
                            function,
                            args,
                            call_info_of_apply_status(transformed_jsx, info.status),
                        ),
                        ApplyStatus::Na => match known_arity {
                            Some(arity) if !arity.is_na() => {
                                self.compiler.apply_with_arity(function, arity, args)
                            }
                            _ => Expression::call(function, args, CallInfo::default()),
                        },
                    };
                    Compiled { prelude, expr }
                }
            };
        }

        // fold_right (function :: args), compiler/core/lam_compile.ml:1647-1656.
        // Compiler visits are RTL; the emitted prelude and operands remain in
        // source order. In particular, compile the function AFTER its arguments.
        let (args_prelude, args) = self.call_arguments(
            count,
            |owner, i| {
                let NodeView::Apply(_, args, _, _) = owner.context.store().view(application) else {
                    unreachable!()
                };
                args[i]
            },
            lower,
        );
        let compiled_function = lower(self, function);
        let mut prelude = compiled_function.prelude;
        prelude.extend(args_prelude);
        Compiled {
            prelude,
            expr: Expression::call(
                compiled_function.expr,
                args,
                call_info_of_apply_status(jsx, info.status),
            ),
        }
    }

    fn call_arguments(
        &mut self,
        count: usize,
        node: impl Fn(&Self, usize) -> NodeId,
        lower: &mut impl FnMut(&mut Self, NodeId) -> Compiled,
    ) -> (Block, Vec<Expression>) {
        let mut compiled = Vec::with_capacity(count);
        for i in (0..count).rev() {
            let argument = node(self, i);
            compiled.push(lower(self, argument));
        }
        let mut prelude = Vec::new();
        let mut args = Vec::with_capacity(count);
        for compiled in compiled.into_iter().rev() {
            prelude.extend(compiled.prelude);
            args.push(compiled.expr);
        }
        (prelude, args)
    }

    pub(super) fn primitive(
        &mut self,
        node: NodeId,
        lower: &mut impl FnMut(&mut Self, NodeId) -> Compiled,
    ) -> Compiled {
        let (primitive, count, loc) = match self.context.store().view(node) {
            NodeView::Prim(primitive, args, loc) => (primitive.clone(), args.len(), *loc),
            _ => panic!("primitive lowering requires a primitive node"),
        };
        if matches!(primitive, Primitive::Pimport) {
            return self.import(node, count, loc, lower);
        }
        if count == 2 && matches!(primitive, Primitive::Psequand | Primitive::Psequor) {
            let (lhs, rhs) = match self.context.store().view(node) {
                NodeView::Prim(_, args, _) => (args[0], args[1]),
                _ => unreachable!(),
            };
            let lhs = lower(self, lhs);
            let rhs = lower(self, rhs);
            let op = if matches!(primitive, Primitive::Psequand) {
                ShortCircuitOp::And
            } else {
                ShortCircuitOp::Or
            };
            return self.compiler.compile_short_circuit_js(op, lhs, rhs);
        }
        {
            let NodeView::Prim(primitive, nodes, _) = self.context.store().view(node) else {
                unreachable!()
            };
            if let Some(compiled) = self.compiler.compile_hoisted_external_field(
                primitive,
                LambdaInputs::Indexed {
                    store: self.context.store(),
                    nodes,
                },
            ) {
                return compiled;
            }
        }
        // Ext_list.split_map is LTR (compiler/ext/ext_list.ml:643-670), unlike
        // call arguments. Do not reuse the fold_right helper here.
        let mut prelude = Vec::new();
        let mut args = Vec::with_capacity(count);
        for i in 0..count {
            let child = match self.context.store().view(node) {
                NodeView::Prim(_, args, _) => args[i],
                _ => unreachable!(),
            };
            let compiled = lower(self, child);
            prelude.extend(compiled.prelude);
            args.push(compiled.expr);
        }
        self.compiler
            .compile_primitive_js(&primitive, args, prelude, &loc)
    }

    /// NeedValue branch of compiler/core/lam_compile.ml:1384-1407. Assign
    /// remains an explicit continuation; nested bodies must not be flattened
    /// into expression/IIFE substitutes. Native OCaml evaluates the labelled
    /// handler argument of S.try_ before its positional body argument.
    pub(super) fn try_with(
        &mut self,
        node: NodeId,
        assign: &mut impl FnMut(&mut Self, &Ident, NodeId) -> Block,
    ) -> Compiled {
        let (body, exception, handler) = match self.context.store().view(node) {
            NodeView::TryWith(body, exception, handler) => (body, exception.clone(), handler),
            _ => panic!("try_with lowering requires a try node"),
        };
        let result = self.compiler.fresh_tmp_ident();
        let handler = assign(self, &result, handler);
        let body = assign(self, &result, body);
        Compiled {
            prelude: vec![
                Statement::variable(VariableDeclaration {
                    ident: result.clone(),
                    value: None,
                    property: LetKind::Variable,
                    ident_info: IdentInfo::default(),
                }),
                self.compiler.try_statement(body, &exception, handler),
            ],
            expr: Expression::var(result),
        }
    }

    fn import(
        &mut self,
        node: NodeId,
        count: usize,
        loc: Location,
        lower: &mut impl FnMut(&mut Self, NodeId) -> Compiled,
    ) -> Compiled {
        if count != 1 {
            self.compiler.report_diagnostic(&loc, "Missing argument: Dynamic import requires a module or module value that is a file as argument.");
            return Compiled {
                prelude: vec![],
                expr: Expression::undefined(false),
            };
        }
        let mut target = match self.context.store().view(node) {
            NodeView::Prim(_, args, _) => args[0],
            _ => unreachable!(),
        };
        let wrapped_call = match self.context.store().view(target) {
            NodeView::Function(_, _, body, _) => match self.context.store().view(body) {
                NodeView::Prim(Primitive::PjsCall { .. }, _, _) => Some(body),
                NodeView::Sequence(first, second)
                    if matches!(
                        self.context.store().view(second),
                        NodeView::Const(Constant::JsUndefined { .. })
                    ) && matches!(
                        self.context.store().view(first),
                        NodeView::Prim(Primitive::PjsCall { .. }, _, _)
                    ) =>
                {
                    Some(first)
                }
                _ => None,
            },
            _ => None,
        };
        if let Some(call) = wrapped_call {
            let NodeSnapshot::Prim(mut primitive, args, loc) = self.context.store().snapshot(call)
            else {
                unreachable!()
            };
            let Primitive::PjsCall { dynamic_import, .. } = &mut primitive else {
                unreachable!()
            };
            *dynamic_import = true;
            target = self
                .context
                .store_mut()
                .append(NodeSnapshot::Prim(primitive, args, loc));
        }
        if !matches!(
            self.context.store().view(target),
            NodeView::GlobalModule(..)
                | NodeView::Var(_)
                | NodeView::Prim(Primitive::Pfield(..) | Primitive::PjsCall { .. }, _, _)
        ) {
            self.compiler.report_diagnostic(&loc, "Invalid argument: unsupported argument to dynamic import. If you believe this should be supported, please open an issue.");
            return Compiled {
                prelude: vec![],
                expr: Expression::undefined(false),
            };
        }
        let compiled = lower(self, target);
        let expr = self.compiler.compile_import(&loc, vec![compiled.expr]);
        Compiled {
            prelude: compiled.prelude,
            expr,
        }
    }
}

#[cfg(test)]
#[path = "lam_compile_indexed_tests.rs"]
mod tests;
