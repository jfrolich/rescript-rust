//! Mutable JS-lowering owner. Closed lowering operations take child continuations
//! explicitly while the remaining consumer modes are moved here. A continuation
//! receives the same owner and a NodeId, never a borrowed store or a Lambda tree.

use super::*;
use self::context::{Continuation, TailType, MaybeTail, MapIdent};
use self::output::{Output, Finished};
use crate::lambda::indexed::NodeView;
use crate::lambda::lam_compile_input::LambdaInputs;
use crate::lambda::lam_indexed_helpers::append_rebuilt;

pub(crate) struct IndexedJsConsumer<'a> {
    pub(super) compiler: &'a mut LambdaCompiler,
    pub(super) context: &'a mut IndexedLambdaContext,
    return_labels: Vec<context::ReturnLabel>,
}

impl<'a> IndexedJsConsumer<'a> {
    pub(super) fn new(
        compiler: &'a mut LambdaCompiler,
        context: &'a mut IndexedLambdaContext,
    ) -> Self {
        Self { compiler, context, return_labels: Vec::new() }
    }

    /// Thin NeedValue wrapper for callers still using Compiled.
    pub(super) fn application(
        &mut self,
        application: NodeId,
        lower: &mut impl FnMut(&mut Self, NodeId) -> Compiled,
    ) -> Compiled {
        let output = self.application_output(application, &Continuation::NeedValue(TailType::NotTail), &mut |owner, child, _| {
            let compiled = lower(owner, child);
            Output { block: compiled.prelude, value: Some(compiled.expr), finished: Finished::False }
        });
        Compiled { prelude: output.block, expr: output.value.expect("NeedValue application") }
    }

    pub(super) fn application_output(
        &mut self,
        application: NodeId,
        continuation: &Continuation,
        lower: &mut impl FnMut(&mut Self, NodeId, &Continuation) -> Output,
    ) -> Output {
        let (function, count, info, jsx) = match self.context.store().view(application) {
            NodeView::Apply(function, args, info, jsx) => (function, args.len(), info.clone(), jsx),
            _ => panic!("application lowering requires an application node"),
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
                return lower(self, merged, continuation);
            }
        }

        // compiler/core/lam_compile.ml:342-357: the query/header test precedes
        // import and beta; compile the returned root in this SAME owner.
        if let Some(prepared) = self
            .compiler
            .prepare_indexed_external_field_apply(self.context, application)
        {
            return match prepared {
                PreparedIndexedExternalApply::Reduced(root) => lower(self, root, continuation),
                PreparedIndexedExternalApply::Call {
                    module,
                    field_name,
                    args,
                    info,
                    transformed_jsx,
                    known_arity,
                } => {
                    let (prelude, args) = self.call_arguments(args.len(), |_, i| args[i], &mut |owner, child| {
                        let output = lower(owner, child, &Continuation::NeedValue(TailType::NotTail));
                        Compiled { prelude: output.block, expr: output.value.expect("call argument") }
                    });
                    let function = Expression::qualified(module, Some(field_name));
                    let mut expr = match info.status {
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
                    if expr.source_loc.is_none() { expr.source_loc = (self.compiler.source_loc(&info.loc)).map(Box::new); }
                    Output::of_block_and_expression(continuation, prelude, expr)
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
            &mut |owner, child| {
                let output = lower(owner, child, &Continuation::NeedValue(TailType::NotTail));
                Compiled { prelude: output.block, expr: output.value.expect("call argument") }
            },
        );
        let compiled_function = lower(self, function, &Continuation::NeedValue(TailType::NotTail));
        let mut prelude = compiled_function.block;
        prelude.extend(args_prelude);
        // compiler/core/lam_compile.ml:1658-1702. Tail state belongs to this
        // owner; NeedValue tail probes and EffectCall share this exact label.
        let tail_label = match continuation {
            Continuation::NeedValue(TailType::MaybeTailIsReturn(MaybeTail::TailWithName { label, .. })) |
            Continuation::EffectCall(TailType::MaybeTailIsReturn(MaybeTail::TailWithName { label, .. })) => *label,
            _ => None,
        };
        if let Some(label) = tail_label {
            if matches!(self.context.store().view(function), NodeView::Var(id) if id.same(&self.return_labels[label.0].id)) {
                let ret = &mut self.return_labels[label.0];
                ret.triggered = true;
                let args = if ret.params.is_empty() { Vec::new() } else { args };
                assert_eq!(ret.params.len(), args.len(), "native tail parameter arity");
                let mut assigned = Vec::new();
                let mut new_params = std::collections::BTreeMap::new();
                for (i, (param, arg)) in ret.params.iter().zip(args).enumerate() {
                    if matches!(&arg.desc, ExpressionDesc::Var(VIdent::Id(id)) if id.same(param)) { continue; }
                    let key = MapIdent(param.clone());
                    let new_param = match ret.new_params.get(&key) {
                        Some(id) => id.clone(),
                        None => {
                            ret.immutable_mask[i] = false;
                            let id = self.compiler.fresh_ident(&format!("_{}", param.name()));
                            new_params.insert(key, id.clone());
                            id
                        },
                    };
                    assigned.push((new_param, arg));
                }
                for (key, value) in new_params {
                    assert!(ret.new_params.insert(key, value).is_none(), "disjoint tail parameter map");
                }
                for (param, arg) in assigned.into_iter().rev() {
                    prelude.push(Statement::exp(Expression::bin(BinOp::Eq, Expression::var(param), arg)));
                }
                prelude.push(Statement::continue_());
                return Output { block: prelude, value: None, finished: Finished::True };
            }
        }
        let mut expr = Expression::call(
            compiled_function.value.expect("call function"), args,
            call_info_of_apply_status(jsx, info.status),
        );
        expr.source_loc = (self.compiler.source_loc(&info.loc)).map(Box::new);
        Output::of_block_and_expression(continuation, prelude, expr)
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
            return self.short_circuit_value(node, lower);
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

#[path = "lam_compile_indexed_control.rs"]
mod control;

#[path = "lam_compile_indexed_output.rs"]
mod output;
#[path = "lam_compile_indexed_short_circuit.rs"]
mod short_circuit;

#[path = "lam_compile_indexed_context.rs"]
mod context;

#[path = "lam_compile_indexed_conditional.rs"]
mod conditional;

#[path = "lam_compile_indexed_bindings.rs"]
mod bindings;
