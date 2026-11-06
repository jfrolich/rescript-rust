//! Indexed `Lam_pass_remove_alias.simplify_alias`.

use crate::context::IdGenerator;
use crate::ident::Ident;
use crate::lambda::LamLoc;
use crate::lambda::indexed::{IndexedLambda, IndexedLambdaContext, NodeId, NodeSnapshot, NodeView};
use crate::lambda::lam_analysis_indexed::{hit_variable, is_closed_with_map, no_side_effects};
use crate::lambda::lam_beta_reduce_indexed::{
    BetaDiagnostics, propagate_beta_reduce, propagate_beta_reduce_with_map,
};
use crate::lambda::lam_compat::FieldDbgInfo;
use crate::lambda::lam_compile_context::BoxedNullable;
use crate::lambda::lam_indexed_helpers::append_rebuilt;
use crate::lambda::lam_pass_collect_indexed::indexed_size_upto;
use crate::lambda::lam_pass_collect_indexed::{IndexedElement, IndexedIdKind, IndexedLamStats};
use crate::lambda::lam_primitive::Primitive;
use crate::lambda::{InlineAttribute, Lambda, TagInfo};

pub type IndexedExternalInlineResolver<'a> = dyn FnMut(&Ident, &str) -> Option<Lambda> + 'a;

#[derive(Clone, Copy)]
enum Outcome {
    False,
    True,
    Unknown,
}

fn boolean_kind(store: &IndexedLambda, meta: &IndexedLamStats, id: &Ident) -> Outcome {
    match meta.ident_tbl.get(id) {
        Some(IndexedIdKind::NormalOptional(node))
            if matches!(
                store.view(*node),
                NodeView::Const(
                    crate::lambda::Constant::JsFalse
                        | crate::lambda::Constant::JsNull
                        | crate::lambda::Constant::JsUndefined { .. }
                )
            ) =>
        {
            Outcome::False
        }
        Some(IndexedIdKind::Constant(crate::lambda::Constant::JsTrue)) => Outcome::True,
        Some(IndexedIdKind::Constant(crate::lambda::Constant::Int { i, .. })) => {
            if *i == 0 {
                Outcome::False
            } else {
                Outcome::True
            }
        }
        Some(IndexedIdKind::Constant(
            crate::lambda::Constant::JsFalse
            | crate::lambda::Constant::JsNull
            | crate::lambda::Constant::JsUndefined { .. },
        )) => Outcome::False,
        _ => Outcome::Unknown,
    }
}

fn const_some(value: &crate::lambda::Constant) -> bool {
    matches!(value, crate::lambda::Constant::Some(_))
        || matches!(
            value,
            crate::lambda::Constant::Block { tag_info, .. }
                if matches!(**tag_info, TagInfo::Some | TagInfo::SomeNotNested)
        )
}

fn field_get(
    store: &mut IndexedLambda,
    meta: &IndexedLamStats,
    var: &Ident,
    index: i32,
    info: &FieldDbgInfo,
) -> Option<NodeId> {
    match meta.ident_tbl.get(var) {
        Some(IndexedIdKind::Module(module)) => {
            let base = store.append(NodeSnapshot::GlobalModule(*module));
            Some(append_rebuilt(
                store,
                NodeSnapshot::Prim(
                    Primitive::Pfield(index, info.clone()),
                    vec![base],
                    LamLoc::NONE,
                ),
            ))
        }
        Some(IndexedIdKind::ImmutableBlock(elements)) => {
            elements
                .get(index as usize)
                .and_then(|element| match element {
                    IndexedElement::SimpleForm(node) => Some(*node),
                    IndexedElement::Na => None,
                })
        }
        Some(IndexedIdKind::Constant(crate::lambda::Constant::Block { tag_info, elements })) => {
            let selected = match (info, &**tag_info) {
                (FieldDbgInfo::Record { name }, TagInfo::Record { fields, .. }) => fields
                    .iter()
                    .position(|(field, _)| field == name)
                    .and_then(|i| elements.get(i)),
                _ => elements.get(index as usize),
            };
            selected
                .filter(|value| !value.is_allocating())
                .map(|value| store.append(NodeSnapshot::Const(value.clone())))
        }
        _ => None,
    }
}

fn destruct_pattern(
    store: &mut IndexedLambda,
    body: NodeId,
    params: &[Ident],
    args: &[NodeId],
) -> bool {
    match store.snapshot(body) {
        NodeSnapshot::Switch {
            scrutinee,
            consts_full,
            consts,
            blocks_full,
            blocks,
            fail_action,
            dispatch,
        } => {
            let Some((_, arg)) = params.iter().zip(args).find(
                |(param, _)| matches!(store.view(scrutinee), NodeView::Var(id) if id.same(param)),
            ) else {
                return false;
            };
            if !matches!(store.view(*arg), NodeView::Const(_)) {
                false
            } else {
                let reduced = append_rebuilt(
                    store,
                    NodeSnapshot::Switch {
                        scrutinee: *arg,
                        consts_full,
                        consts,
                        blocks_full,
                        blocks,
                        fail_action,
                        dispatch,
                    },
                );
                indexed_size_upto(store, reduced, 5) < 5
            }
        }
        NodeSnapshot::IfThenElse(condition, then_, else_) => {
            let Some((_, arg)) = params.iter().zip(args).find(
                |(param, _)| matches!(store.view(condition), NodeView::Var(id) if id.same(param)),
            ) else {
                return false;
            };
            if !matches!(store.view(*arg), NodeView::Const(_)) {
                false
            } else {
                let reduced = append_rebuilt(store, NodeSnapshot::IfThenElse(*arg, then_, else_));
                indexed_size_upto(store, reduced, 5) < 5
            }
        }
        _ => false,
    }
}

fn inline_allowed(
    store: &mut IndexedLambda,
    body: NodeId,
    params: &[Ident],
    args: &[NodeId],
    inline: InlineAttribute,
) -> bool {
    match inline {
        InlineAttribute::Always => true,
        InlineAttribute::Never => false,
        InlineAttribute::Default => {
            let body_size = indexed_size_upto(store, body, 10);
            body_size < 5
                || destruct_pattern(store, body, params, args)
                || (args
                    .iter()
                    .all(|node| matches!(store.view(*node), NodeView::Const(_)))
                    && body_size < 10
                    && no_side_effects(store, body))
        }
    }
}

struct Simplifier<'a> {
    store: &'a mut IndexedLambda,
    meta: &'a mut IndexedLamStats,
    id_gen: &'a IdGenerator,
    beta_diagnostics: &'a mut BetaDiagnostics,
    external: &'a mut IndexedExternalInlineResolver<'a>,
    /// See [`super::lam_pass_remove_alias::MAX_INLINE_DEPTH`].
    inline_depth: usize,
}

impl Simplifier<'_> {
    fn simpl(&mut self, node: NodeId) -> NodeId {
        match self.store.snapshot(node) {
            NodeSnapshot::Var(_)
            | NodeSnapshot::GlobalModule(_)
            | NodeSnapshot::Const(_)
            | NodeSnapshot::Break
            | NodeSnapshot::Continue => node,
            // Keep a JSX tag like `M.make` as it is (#7432).
            NodeSnapshot::Prim(primitive @ Primitive::Pjsx(_), args, loc)
                if args.first().is_some_and(|node| {
                    matches!(
                        self.store.view(*node),
                        NodeView::Prim(Primitive::Pfield(_, _), _, _)
                    )
                }) =>
            {
                let mut iter = args.into_iter();
                let first = iter.next().unwrap();
                let mut mapped = vec![first];
                mapped.extend(iter.map(|n| self.simpl(n)));
                append_rebuilt(self.store, NodeSnapshot::Prim(primitive, mapped, loc))
            }
            NodeSnapshot::Prim(Primitive::Pfield(index, info), args, loc) if args.len() == 1 => {
                let arg = self.simpl(args[0]);
                if let NodeView::Var(id) = self.store.view(arg) {
                    let id = *id;
                    if let Some(selected) = field_get(self.store, self.meta, &id, index, &info) {
                        return selected;
                    }
                }
                append_rebuilt(
                    self.store,
                    NodeSnapshot::Prim(Primitive::Pfield(index, info), vec![arg], loc),
                )
            }
            NodeSnapshot::Prim(
                p @ (Primitive::PvalFromOption | Primitive::PvalFromOptionNotNest),
                args,
                loc,
            ) if args.len() == 1 && matches!(self.store.view(args[0]), NodeView::Var(_)) => {
                let id = match self.store.view(args[0]) {
                    NodeView::Var(id) => *id,
                    _ => unreachable!(),
                };
                match self.meta.ident_tbl.get(&id) {
                    Some(IndexedIdKind::OptionalBlock(value, _)) => *value,
                    // `v` bound to `Some(l)`: unwrapping gives back `l`,
                    // whether or not it was nested. Only substitute forms
                    // that are safe to repeat.
                    Some(IndexedIdKind::NormalOptional(value))
                        if match self.store.view(*value) {
                            NodeView::Var(_) => true,
                            NodeView::Const(c) => !c.is_allocating(),
                            _ => false,
                        } =>
                    {
                        *value
                    }
                    _ if matches!(p, Primitive::PvalFromOptionNotNest) => args[0],
                    _ => append_rebuilt(self.store, NodeSnapshot::Prim(p, args, loc)),
                }
            }
            NodeSnapshot::Prim(primitive, args, loc) => {
                let args = args.into_iter().map(|n| self.simpl(n)).collect();
                append_rebuilt(self.store, NodeSnapshot::Prim(primitive, args, loc))
            }
            NodeSnapshot::IfThenElse(condition, then_, else_) => {
                if let NodeView::Prim(Primitive::PisNotNone, [arg], loc) =
                    self.store.view(condition)
                    && let NodeView::Var(id) = self.store.view(*arg)
                {
                    let id = *id;
                    let loc = *loc;
                    match self.meta.ident_tbl.get(&id).cloned() {
                        Some(IndexedIdKind::Constant(c)) if const_some(&c) => {
                            return self.simpl(then_);
                        }
                        Some(
                            IndexedIdKind::ImmutableBlock(_)
                            | IndexedIdKind::MutableBlock(_)
                            | IndexedIdKind::NormalOptional(_),
                        ) => return self.simpl(then_),
                        Some(IndexedIdKind::OptionalBlock(value, boxed)) => {
                            let primitive = match boxed {
                                BoxedNullable::Null => Primitive::PisNull,
                                BoxedNullable::Undefined => Primitive::PisUndefined,
                                BoxedNullable::NullUndefined => Primitive::PisNullUndefined,
                            };
                            let pred = append_rebuilt(
                                self.store,
                                NodeSnapshot::Prim(primitive, vec![value], LamLoc::NONE),
                            );
                            let not = append_rebuilt(
                                self.store,
                                NodeSnapshot::Prim(Primitive::Pnot, vec![pred], LamLoc::NONE),
                            );
                            let a = self.simpl(then_);
                            let b = self.simpl(else_);
                            return append_rebuilt(self.store, NodeSnapshot::IfThenElse(not, a, b));
                        }
                        _ => {
                            let var = self.store.append(NodeSnapshot::Var(id));
                            let pred = append_rebuilt(
                                self.store,
                                NodeSnapshot::Prim(Primitive::PisNotNone, vec![var], loc),
                            );
                            let a = self.simpl(then_);
                            let b = self.simpl(else_);
                            return append_rebuilt(
                                self.store,
                                NodeSnapshot::IfThenElse(pred, a, b),
                            );
                        }
                    }
                }
                if let NodeView::Var(id) = self.store.view(condition) {
                    match boolean_kind(self.store, self.meta, id) {
                        Outcome::True => return self.simpl(then_),
                        Outcome::False => return self.simpl(else_),
                        Outcome::Unknown => {}
                    }
                }
                let c = self.simpl(condition);
                let a = self.simpl(then_);
                let b = self.simpl(else_);
                append_rebuilt(self.store, NodeSnapshot::IfThenElse(c, a, b))
            }
            NodeSnapshot::Apply(function, args, info) => self.simpl_apply(function, args, info),
            NodeSnapshot::StringSwitch(scrutinee, cases, default) => {
                let scrutinee = if let NodeView::Var(id) = self.store.view(scrutinee) {
                    match self.meta.ident_tbl.get(id) {
                        Some(IndexedIdKind::Constant(c)) => {
                            self.store.append(NodeSnapshot::Const(c.clone()))
                        }
                        _ => self.simpl(scrutinee),
                    }
                } else {
                    self.simpl(scrutinee)
                };
                let cases = cases.into_iter().map(|(k, n)| (k, self.simpl(n))).collect();
                let default = default.map(|n| self.simpl(n));
                append_rebuilt(
                    self.store,
                    NodeSnapshot::StringSwitch(scrutinee, cases, default),
                )
            }
            snapshot => self.simpl_children(snapshot),
        }
    }

    fn simpl_children(&mut self, snapshot: NodeSnapshot) -> NodeId {
        let mapped = match snapshot {
            NodeSnapshot::Function(a, p, b, attr, loc) => {
                NodeSnapshot::Function(a, p, self.simpl(b), attr, loc)
            }
            NodeSnapshot::Let(k, id, a, b) => {
                let a = self.simpl(a);
                let b = self.simpl(b);
                NodeSnapshot::Let(k, id, a, b)
            }
            NodeSnapshot::LetRec(bindings, body) => {
                let bindings = bindings
                    .into_iter()
                    .map(|(id, n)| (id, self.simpl(n)))
                    .collect();
                let body = self.simpl(body);
                NodeSnapshot::LetRec(bindings, body)
            }
            NodeSnapshot::Switch {
                scrutinee,
                consts_full,
                consts,
                blocks_full,
                blocks,
                fail_action,
                dispatch,
            } => {
                let scrutinee = self.simpl(scrutinee);
                let consts = consts
                    .into_iter()
                    .map(|(k, n)| (k, self.simpl(n)))
                    .collect();
                let blocks = blocks
                    .into_iter()
                    .map(|(k, n)| (k, self.simpl(n)))
                    .collect();
                let fail_action = fail_action.map(|n| self.simpl(n));
                NodeSnapshot::Switch {
                    scrutinee,
                    consts_full,
                    consts,
                    blocks_full,
                    blocks,
                    fail_action,
                    dispatch,
                }
            }
            NodeSnapshot::StaticRaise(i, args) => {
                NodeSnapshot::StaticRaise(i, args.into_iter().map(|n| self.simpl(n)).collect())
            }
            NodeSnapshot::StaticCatch(a, i, ids, b) => {
                let a = self.simpl(a);
                let b = self.simpl(b);
                NodeSnapshot::StaticCatch(a, i, ids, b)
            }
            NodeSnapshot::TryWith(a, id, b) => {
                let a = self.simpl(a);
                let b = self.simpl(b);
                NodeSnapshot::TryWith(a, id, b)
            }
            NodeSnapshot::TryFinally(a, b) => {
                let a = self.simpl(a);
                let b = self.simpl(b);
                NodeSnapshot::TryFinally(a, b)
            }
            NodeSnapshot::Sequence(a, b) => {
                let a = self.simpl(a);
                let b = self.simpl(b);
                NodeSnapshot::Sequence(a, b)
            }
            NodeSnapshot::While(a, b) => {
                let a = self.simpl(a);
                let b = self.simpl(b);
                NodeSnapshot::While(a, b)
            }
            NodeSnapshot::For(id, a, b, d, c) => {
                let a = self.simpl(a);
                let b = self.simpl(b);
                let c = self.simpl(c);
                NodeSnapshot::For(id, a, b, d, c)
            }
            NodeSnapshot::ForOf(id, a, b) => {
                let a = self.simpl(a);
                let b = self.simpl(b);
                NodeSnapshot::ForOf(id, a, b)
            }
            NodeSnapshot::ForAwaitOf(id, a, b) => {
                let a = self.simpl(a);
                let b = self.simpl(b);
                NodeSnapshot::ForAwaitOf(id, a, b)
            }
            NodeSnapshot::Assign(id, a) => NodeSnapshot::Assign(id, self.simpl(a)),
            other => other,
        };
        append_rebuilt(self.store, mapped)
    }

    fn simpl_apply(
        &mut self,
        function: NodeId,
        args: Vec<NodeId>,
        info: crate::lambda::ApInfo,
    ) -> NodeId {
        if let NodeView::Prim(Primitive::Pfield(_, FieldDbgInfo::Module { name }), [base], _) =
            self.store.view(function)
            && let NodeView::GlobalModule(module) = self.store.view(*base)
        {
            let (module, name) = (*module, name.clone());
            if let Some(lambda) = (self.external)(&module, &name) {
                let imported = self.store.append_compat_lambda(lambda);
                if let NodeSnapshot::Function(_,params,body,attr, _)=self.store.snapshot(imported) && params.len()==args.len() && !attr.async_ && attr.directive.is_none() && args.iter().all(|arg| !matches!(self.store.view(*arg),NodeView::Var(id) if matches!(self.meta.ident_tbl.get(id),Some(IndexedIdKind::Parameter)))) { let reduced=propagate_beta_reduce(self.store,self.meta,&params,body,&args,self.id_gen,self.beta_diagnostics); return self.simpl(reduced); }
            }
        }
        if let NodeView::Var(id) = self.store.view(function) {
            let id = *id;
            let args: Vec<_> = args.into_iter().map(|n| self.simpl(n)).collect();
            let candidate = match self.meta.ident_tbl.get(&id).cloned() {
                Some(IndexedIdKind::FunctionId {
                    lambda: Some((node, rec_flag)),
                    ..
                }) => match self.store.snapshot(node) {
                    NodeSnapshot::Function(_, params, body, attr, _)
                        if !attr.async_
                            && attr.directive.is_none()
                            && params.len() == args.len() =>
                    {
                        Some((params, body, attr, rec_flag))
                    }
                    _ => None,
                },
                _ => None,
            };
            if let Some((params, body, attr, rec_flag)) = candidate {
                if attr.is_a_functor {
                    let reduced = propagate_beta_reduce(
                        self.store,
                        self.meta,
                        &params,
                        body,
                        &args,
                        self.id_gen,
                        self.beta_diagnostics,
                    );
                    return self.simpl(reduced);
                }
                if inline_allowed(self.store, body, &params, &args, attr.inline) {
                    let (closed, map) =
                        is_closed_with_map(self.store, &self.meta.export_idents, &params, body);
                    if !self.meta.export_idents.contains(&id) || closed {
                        match rec_flag {
                            crate::lambda::lam_compile_context::RecFlag::Rec => {
                                return propagate_beta_reduce_with_map(
                                    self.store,
                                    self.meta,
                                    &map,
                                    &params,
                                    body,
                                    &args,
                                    self.id_gen,
                                    self.beta_diagnostics,
                                );
                            }
                            crate::lambda::lam_compile_context::RecFlag::SelfRec => {}
                            crate::lambda::lam_compile_context::RecFlag::NonRec
                                if !args.iter().any(|n| hit_variable(self.store, &id, *n))
                                    && (self.inline_depth
                                        < super::lam_pass_remove_alias::MAX_INLINE_DEPTH
                                        || attr.inline
                                            == crate::lambda::InlineAttribute::Always) =>
                            {
                                let reduced = propagate_beta_reduce_with_map(
                                    self.store,
                                    self.meta,
                                    &map,
                                    &params,
                                    body,
                                    &args,
                                    self.id_gen,
                                    self.beta_diagnostics,
                                );
                                self.inline_depth += 1;
                                let inlined = self.simpl(reduced);
                                self.inline_depth -= 1;
                                return inlined;
                            }
                            _ => {}
                        }
                    }
                }
            }
            let function = self.simpl(function);
            return append_rebuilt(self.store, NodeSnapshot::Apply(function, args, info));
        }
        if let NodeSnapshot::Function(_, params, body, attr, _) = self.store.snapshot(function)
            && params.len() == args.len()
            && !attr.async_
            && attr.directive.is_none()
        {
            let reduced = propagate_beta_reduce(
                self.store,
                self.meta,
                &params,
                body,
                &args,
                self.id_gen,
                self.beta_diagnostics,
            );
            return self.simpl(reduced);
        }
        let function = self.simpl(function);
        let args = args.into_iter().map(|n| self.simpl(n)).collect();
        append_rebuilt(self.store, NodeSnapshot::Apply(function, args, info))
    }
}

impl IndexedLambdaContext {
    pub fn simplify_alias(
        &mut self,
        id_gen: &IdGenerator,
        external: &mut IndexedExternalInlineResolver<'_>,
    ) {
        let root = self.current_root();
        let mut beta_diagnostics = BetaDiagnostics::default();
        let root = {
            let (store, meta) = self.parts_mut();
            Simplifier {
                store,
                meta,
                id_gen,
                beta_diagnostics: &mut beta_diagnostics,
                external,
                inline_depth: 0,
            }
            .simpl(root)
        };
        self.replace_root(root);
        #[cfg(test)]
        self.record_beta_substitution_peak(beta_diagnostics.substitution_peak_unique_nodes);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ident::IdentFlags;
    use crate::lambda::{
        ApInfo, Apply, ApplyStatus, Constant, FunctionAttribute, LFunction, LetKind,
    };

    fn id(name: &str, stamp: i32) -> Ident {
        Ident::new(name, stamp, IdentFlags::NONE)
    }
    fn int(value: i32) -> Lambda {
        Lambda::const_(Constant::int(value))
    }
    fn info() -> ApInfo {
        ApInfo {
            loc: LamLoc::NONE,
            status: ApplyStatus::Na,
        }
    }
    fn apply(function: Lambda, args: Vec<Lambda>) -> Lambda {
        Lambda::Lapply(Box::new(Apply {
            ap_func: Box::new(function),
            ap_args: args,
            ap_info: info(),
        }))
    }
    fn run(input: Lambda, start: i32) -> (Lambda, i32, usize) {
        let generator = IdGenerator::with_start_stamp(start);
        let mut context = IndexedLambdaContext::from_lambda(input, []);
        context.collect_info();
        let mut external = |_: &Ident, _: &str| None;
        context.simplify_alias(&generator, &mut external);
        (
            context.materialize(),
            generator.current_stamp(),
            context.beta_substitution_peak_unique_nodes(),
        )
    }

    fn assert_exact(actual: &Lambda, expected: &Lambda) {
        assert_eq!(format!("{actual:#?}"), format!("{expected:#?}"));
    }

    #[test]
    fn boolean_metadata_outcomes_choose_exact_reference_branch() {
        let cases = vec![
            (Constant::JsTrue, true),
            (Constant::int(0), false),
            (Constant::int(2), true),
            (Constant::JsFalse, false),
            (Constant::JsNull, false),
            (Constant::JsUndefined { is_unit: false }, false),
        ];
        for (constant, take_then) in cases {
            let value = id("value", 1);
            let binding = Lambda::const_(constant);
            let input = Lambda::let_(
                LetKind::Strict,
                value,
                binding.clone(),
                Lambda::if_(Lambda::var(value), int(1), int(2)),
            );
            let (actual, frontier, _) = run(input, 20);
            let expected = Lambda::let_(
                LetKind::Strict,
                value,
                binding,
                if take_then { int(1) } else { int(2) },
            );
            assert_exact(&actual, &expected);
            assert_eq!(frontier, 20);
        }

        let value = id("optional", 2);
        let binding = Lambda::prim(
            Primitive::Psome,
            vec![Lambda::const_(Constant::JsFalse)],
            LamLoc::NONE,
        );
        let input = Lambda::let_(
            LetKind::Strict,
            value,
            binding.clone(),
            Lambda::if_(Lambda::var(value), int(1), int(2)),
        );
        let (actual, _, _) = run(input, 20);
        assert_exact(
            &actual,
            &Lambda::let_(LetKind::Strict, value, binding, int(2)),
        );

        let unknown = id("unknown", 3);
        let input = Lambda::if_(Lambda::var(unknown), int(1), int(2));
        let (actual, _, _) = run(input.clone(), 20);
        assert_exact(&actual, &input);
    }

    #[test]
    fn optional_block_modes_build_exact_predicates_and_keep_metadata_payload() {
        for (mode, predicate) in [
            (BoxedNullable::Null, Primitive::PisNull),
            (BoxedNullable::Undefined, Primitive::PisUndefined),
            (BoxedNullable::NullUndefined, Primitive::PisNullUndefined),
        ] {
            let boxed = id("boxed", 1);
            let source = id("source", 2);
            let condition_loc = LamLoc::for_test(1);
            let input = Lambda::if_(
                Lambda::prim(
                    Primitive::PisNotNone,
                    vec![Lambda::var(boxed)],
                    condition_loc,
                ),
                int(1),
                int(2),
            );
            let mut context = IndexedLambdaContext::from_lambda(input, []);
            let source_node = context
                .store_mut()
                .append_compat_lambda(Lambda::var(source));
            context
                .metadata_mut()
                .ident_tbl
                .insert(boxed, IndexedIdKind::OptionalBlock(source_node, mode));
            match context.metadata().ident_tbl.get(&boxed) {
                Some(IndexedIdKind::OptionalBlock(node, actual_mode)) => {
                    assert_eq!(*actual_mode, mode);
                    assert_exact(
                        &context.store().materialize_node(*node),
                        &Lambda::var(source),
                    );
                }
                other => panic!("unexpected metadata: {other:?}"),
            }
            let generator = IdGenerator::with_start_stamp(20);
            let mut external = |_: &Ident, _: &str| None;
            context.simplify_alias(&generator, &mut external);
            let check = Lambda::prim(predicate, vec![Lambda::var(source)], LamLoc::NONE);
            let expected = Lambda::if_(
                Lambda::prim(Primitive::Pnot, vec![check], LamLoc::NONE),
                int(1),
                int(2),
            );
            assert_exact(&context.materialize(), &expected);
            assert_eq!(generator.current_stamp(), 20);
        }
    }

    #[test]
    fn pis_not_none_known_shapes_choose_then_exactly() {
        let shapes = vec![
            Lambda::const_(Constant::Some(Box::new(Constant::int(1)))),
            Lambda::const_(Constant::Block {
                tag_info: Box::new(TagInfo::Some),
                elements: vec![Constant::int(1)],
            }),
            Lambda::const_(Constant::Block {
                tag_info: Box::new(TagInfo::SomeNotNested),
                elements: vec![Constant::int(1)],
            }),
            Lambda::prim(
                Primitive::Pmakeblock(
                    TagInfo::Tuple,
                    crate::lambda::lam_primitive::Mutable::Immutable,
                ),
                vec![int(1)],
                LamLoc::NONE,
            ),
            Lambda::prim(Primitive::Psome, vec![int(1)], LamLoc::NONE),
        ];
        for (index, binding) in shapes.into_iter().enumerate() {
            let value = id("shape", index as i32 + 1);
            let input = Lambda::let_(
                LetKind::Strict,
                value,
                binding.clone(),
                Lambda::if_(
                    Lambda::prim(
                        Primitive::PisNotNone,
                        vec![Lambda::var(value)],
                        LamLoc::for_test(2),
                    ),
                    int(7),
                    int(8),
                ),
            );
            let (actual, _, _) = run(input, 30);
            assert_exact(
                &actual,
                &Lambda::let_(LetKind::Strict, value, binding, int(7)),
            );
        }

        let value = id("mutable", 20);
        let input = Lambda::if_(
            Lambda::prim(
                Primitive::PisNotNone,
                vec![Lambda::var(value)],
                LamLoc::NONE,
            ),
            int(7),
            int(8),
        );
        let mut context = IndexedLambdaContext::from_lambda(input, []);
        context
            .metadata_mut()
            .ident_tbl
            .insert(value, IndexedIdKind::MutableBlock(vec![]));
        let generator = IdGenerator::with_start_stamp(30);
        let mut external = |_: &Ident, _: &str| None;
        context.simplify_alias(&generator, &mut external);
        assert_exact(&context.materialize(), &int(7));
    }

    #[test]
    fn field_metadata_branches_return_exact_nodes_and_fallbacks() {
        fn simplify_field(
            kind: IndexedIdKind,
            info: FieldDbgInfo,
            index: i32,
            loc: LamLoc,
        ) -> Lambda {
            let value = id("value", 1);
            let input = Lambda::prim(
                Primitive::Pfield(index, info.clone()),
                vec![Lambda::var(value)],
                loc,
            );
            let mut context = IndexedLambdaContext::from_lambda(input, []);
            context.metadata_mut().ident_tbl.insert(value, kind);
            let generator = IdGenerator::with_start_stamp(20);
            let mut external = |_: &Ident, _: &str| None;
            context.simplify_alias(&generator, &mut external);
            context.materialize()
        }
        let module = id("Module", 9);
        let actual = simplify_field(
            IndexedIdKind::Module(module),
            FieldDbgInfo::Module {
                name: "field".into(),
            },
            0,
            LamLoc::for_test(3),
        );
        let expected = Lambda::prim(
            Primitive::Pfield(
                0,
                FieldDbgInfo::Module {
                    name: "field".into(),
                },
            ),
            vec![Lambda::global_module(module)],
            LamLoc::NONE,
        );
        assert_exact(&actual, &expected);

        let mut context = IndexedLambdaContext::from_lambda(int(0), []);
        let simple = context.store_mut().append_compat_lambda(int(7));
        let value = id("value", 1);
        let loc = LamLoc::for_test(4);
        let root = context.store_mut().append_compat_lambda(Lambda::prim(
            Primitive::Pfield(0, FieldDbgInfo::Tuple),
            vec![Lambda::var(value)],
            loc,
        ));
        context.replace_root(root);
        context.metadata_mut().ident_tbl.insert(
            value,
            IndexedIdKind::ImmutableBlock(vec![IndexedElement::SimpleForm(simple)]),
        );
        let generator = IdGenerator::with_start_stamp(20);
        let mut external = |_: &Ident, _: &str| None;
        context.simplify_alias(&generator, &mut external);
        assert_exact(&context.materialize(), &int(7));

        let fallback = Lambda::prim(
            Primitive::Pfield(1, FieldDbgInfo::Tuple),
            vec![Lambda::var(value)],
            loc,
        );
        let actual = simplify_field(
            IndexedIdKind::ImmutableBlock(vec![IndexedElement::Na]),
            FieldDbgInfo::Tuple,
            1,
            loc,
        );
        assert_exact(&actual, &fallback);

        let record = Constant::Block {
            tag_info: Box::new(TagInfo::record(
                vec![("a".into(), false), ("b".into(), false)],
                crate::parser::ast::MutableFlag::Immutable,
            )),
            elements: vec![Constant::int(7), Constant::int(8)],
        };
        let actual = simplify_field(
            IndexedIdKind::Constant(record),
            FieldDbgInfo::Record { name: "b".into() },
            0,
            LamLoc::NONE,
        );
        assert_exact(&actual, &int(8));
        let tuple = Constant::Block {
            tag_info: Box::new(TagInfo::Tuple),
            elements: vec![Constant::int(9)],
        };
        let actual = simplify_field(
            IndexedIdKind::Constant(tuple),
            FieldDbgInfo::Tuple,
            0,
            LamLoc::NONE,
        );
        assert_exact(&actual, &int(9));
    }

    #[test]
    fn string_switch_and_jsx_preserve_use_exact_metadata_and_child_policy() {
        let value = id("value", 1);
        let switch = Lambda::string_switch(
            Lambda::var(value),
            vec![("yes".into(), int(1))],
            Some(Box::new(int(2))),
        );
        let mut context = IndexedLambdaContext::from_lambda(switch, []);
        context
            .metadata_mut()
            .ident_tbl
            .insert(value, IndexedIdKind::Constant(Constant::string("yes")));
        let generator = IdGenerator::with_start_stamp(20);
        let mut external = |_: &Ident, _: &str| None;
        context.simplify_alias(&generator, &mut external);
        assert_exact(&context.materialize(), &int(1));

        // The tag of a JSX element stays a projection (#7432); the props
        // are simplified.
        let jsx = || {
            Primitive::Pjsx(Box::new(crate::lambda::lam_primitive::JsxElement {
                jsx_name: "jsx".into(),
                jsx_ffi: crate::lambda::lam_primitive::ExternalDecl::test_val("jsx", 2),
                jsx_multi: false,
                jsx_fragment: false,
                jsx_spread: false,
                jsx_props: vec![("x".into(), false)],
                jsx_children: None,
                jsx_key: false,
            }))
        };
        let base = id("base", 2);
        let first_loc = LamLoc::for_test(5);
        let call_loc = LamLoc::for_test(6);
        let first = Lambda::prim(
            Primitive::Pfield(0, FieldDbgInfo::Tuple),
            vec![Lambda::var(base)],
            first_loc,
        );
        let input = Lambda::prim(
            jsx(),
            vec![
                first.clone(),
                Lambda::if_(Lambda::const_(Constant::JsTrue), int(3), int(4)),
            ],
            call_loc,
        );
        let mut context = IndexedLambdaContext::from_lambda(input, []);
        let simple = context.store_mut().append_compat_lambda(int(99));
        context.metadata_mut().ident_tbl.insert(
            base,
            IndexedIdKind::ImmutableBlock(vec![IndexedElement::SimpleForm(simple)]),
        );
        let generator = IdGenerator::with_start_stamp(20);
        let mut external = |_: &Ident, _: &str| None;
        context.simplify_alias(&generator, &mut external);
        let expected = Lambda::prim(jsx(), vec![first, int(3)], call_loc);
        assert_exact(&context.materialize(), &expected);
    }

    #[test]
    fn inline_decision_runs_destruct_probe_before_constant_purity_fallback() {
        let param = id("param", 1);
        let then_ = Lambda::prim(
            Primitive::Paddint,
            vec![Lambda::var(id("left", 3)), Lambda::var(id("right", 4))],
            LamLoc::NONE,
        );
        let body = Lambda::if_(Lambda::var(param), then_.clone(), int(3));
        let mut store = IndexedLambda::from_lambda(body);
        let body = store.root();
        let unknown_truth = store.append_compat_lambda(Lambda::const_(Constant::Constructor(
            crate::types::VariantTag {
                name: "unknown".into(),
                literal: Some(crate::types::VariantLiteralTag::Float("nan".into())),
            },
        )));
        let before = store.node_count();
        assert!(inline_allowed(
            &mut store,
            body,
            std::slice::from_ref(&param),
            &[unknown_truth],
            InlineAttribute::Default
        ));
        assert_eq!(store.node_count(), before + 1);

        let impure_body = store.append_compat_lambda(Lambda::if_(
            Lambda::var(param),
            then_,
            Lambda::prim(Primitive::Pdebugger, vec![], LamLoc::NONE),
        ));
        let truth = store.append_compat_lambda(Lambda::const_(Constant::JsTrue));
        assert!(inline_allowed(
            &mut store,
            impure_body,
            std::slice::from_ref(&param),
            &[truth],
            InlineAttribute::Default
        ));
        let variable = store.append_compat_lambda(Lambda::var(id("argument", 2)));
        assert!(!inline_allowed(
            &mut store,
            body,
            std::slice::from_ref(&param),
            &[variable],
            InlineAttribute::Default
        ));
    }

    fn context_with_function(
        function_id: Ident,
        function: Lambda,
        argument: Lambda,
        rec_flag: crate::lambda::lam_compile_context::RecFlag,
        exported: bool,
    ) -> IndexedLambdaContext {
        let input = apply(Lambda::var(function_id), vec![argument]);
        let exports = if exported { vec![function_id] } else { vec![] };
        let mut context = IndexedLambdaContext::from_lambda(input, exports);
        let function_node = context.store_mut().append_compat_lambda(function.clone());
        context.metadata_mut().ident_tbl.insert(
            function_id,
            IndexedIdKind::FunctionId {
                arity: crate::lambda::lam_arity::Arity::info(vec![1], false),
                lambda: Some((function_node, rec_flag)),
            },
        );
        match context.metadata().ident_tbl.get(&function_id) {
            Some(IndexedIdKind::FunctionId {
                arity,
                lambda: Some((node, actual_flag)),
            }) => {
                assert_eq!(
                    arity,
                    &crate::lambda::lam_arity::Arity::info(vec![1], false)
                );
                assert_eq!(*actual_flag, rec_flag);
                assert_exact(&context.store().materialize_node(*node), &function);
            }
            other => panic!("unexpected function metadata: {other:?}"),
        }
        context
    }

    #[test]
    fn recursion_export_and_capture_guards_match_exact_application_shapes() {
        let f = id("f", 1);
        let p = id("p", 2);
        let function = Lambda::function_(
            1,
            vec![p],
            Lambda::prim(Primitive::Pidentity, vec![Lambda::var(p)], LamLoc::NONE),
            FunctionAttribute::default(),
            LamLoc::NONE,
        );
        for (flag, should_inline) in [
            (crate::lambda::lam_compile_context::RecFlag::Rec, true),
            (crate::lambda::lam_compile_context::RecFlag::SelfRec, false),
            (crate::lambda::lam_compile_context::RecFlag::NonRec, true),
        ] {
            let mut context = context_with_function(f, function.clone(), int(4), flag, false);
            let generator = IdGenerator::with_start_stamp(20);
            let mut external = |_: &Ident, _: &str| None;
            context.simplify_alias(&generator, &mut external);
            let expected = if should_inline {
                Lambda::prim(Primitive::Pidentity, vec![int(4)], LamLoc::NONE)
            } else {
                apply(Lambda::var(f), vec![int(4)])
            };
            assert_exact(&context.materialize(), &expected);
        }

        let mut context = context_with_function(
            f,
            function.clone(),
            Lambda::var(f),
            crate::lambda::lam_compile_context::RecFlag::NonRec,
            false,
        );
        let generator = IdGenerator::with_start_stamp(20);
        let mut external = |_: &Ident, _: &str| None;
        context.simplify_alias(&generator, &mut external);
        assert_exact(
            &context.materialize(),
            &apply(Lambda::var(f), vec![Lambda::var(f)]),
        );

        let mut closed = context_with_function(
            f,
            function,
            int(4),
            crate::lambda::lam_compile_context::RecFlag::NonRec,
            true,
        );
        let generator = IdGenerator::with_start_stamp(20);
        let mut external = |_: &Ident, _: &str| None;
        closed.simplify_alias(&generator, &mut external);
        assert_exact(
            &closed.materialize(),
            &Lambda::prim(Primitive::Pidentity, vec![int(4)], LamLoc::NONE),
        );

        let free = id("free", 3);
        let open_function = Lambda::function_(
            1,
            vec![p],
            Lambda::var(free),
            FunctionAttribute::default(),
            LamLoc::NONE,
        );
        let mut open = context_with_function(
            f,
            open_function.clone(),
            int(4),
            crate::lambda::lam_compile_context::RecFlag::NonRec,
            true,
        );
        let generator = IdGenerator::with_start_stamp(20);
        let mut external = |_: &Ident, _: &str| None;
        open.simplify_alias(&generator, &mut external);
        assert_exact(&open.materialize(), &apply(Lambda::var(f), vec![int(4)]));
    }

    #[test]
    fn direct_function_attribute_and_arity_guards_preserve_full_apply_info() {
        let x = id("x", 1);
        let app_info = ApInfo {
            loc: LamLoc::for_test(7),
            status: ApplyStatus::Uncurry,
        };
        let variants = vec![
            FunctionAttribute {
                async_: true,
                ..FunctionAttribute::default()
            },
            FunctionAttribute {
                directive: Some("use server".into()),
                ..FunctionAttribute::default()
            },
        ];
        for attr in variants {
            let function = Lambda::function_(1, vec![x], Lambda::var(x), attr, LamLoc::NONE);
            let input = Lambda::Lapply(Box::new(Apply {
                ap_func: Box::new(function),
                ap_args: vec![int(1)],
                ap_info: app_info.clone(),
            }));
            let (actual, frontier, _) = run(input.clone(), 20);
            assert_exact(&actual, &input);
            assert_eq!(frontier, 20);
        }
        let function = Lambda::function_(
            2,
            vec![x, id("y", 2)],
            Lambda::var(x),
            FunctionAttribute::default(),
            LamLoc::NONE,
        );
        let input = Lambda::Lapply(Box::new(Apply {
            ap_func: Box::new(function),
            ap_args: vec![int(1)],
            ap_info: app_info,
        }));
        let (actual, _, _) = run(input.clone(), 20);
        assert_exact(&actual, &input);
    }

    #[test]
    fn external_inline_success_and_parameter_gate_preserve_query_and_frontier() {
        let module = id("External", 1);
        let parameter = id("externalParam", 50);
        let target = Lambda::prim(
            Primitive::Pfield(0, FieldDbgInfo::Module { name: "run".into() }),
            vec![Lambda::global_module(module)],
            LamLoc::for_test(8),
        );
        let input = apply(target.clone(), vec![Lambda::const_(Constant::JsTrue)]);
        let mut context = IndexedLambdaContext::from_lambda(input, []);
        context.collect_info();
        let generator = IdGenerator::with_start_stamp(100);
        let mut calls = Vec::new();
        let external_function = Lambda::function_(
            1,
            vec![parameter],
            Lambda::if_(Lambda::var(parameter), int(7), int(8)),
            FunctionAttribute::default(),
            LamLoc::NONE,
        );
        let mut external = |id: &Ident, field: &str| {
            calls.push((id.name().to_string(), field.to_string()));
            Some(external_function.clone())
        };
        context.simplify_alias(&generator, &mut external);
        assert_exact(&context.materialize(), &int(7));
        assert_eq!(calls, vec![("External".into(), "run".into())]);
        assert_eq!(generator.current_stamp(), 100);

        let blocked = id("blocked", 60);
        let input = apply(target, vec![Lambda::var(blocked)]);
        let mut context = IndexedLambdaContext::from_lambda(input.clone(), []);
        context
            .metadata_mut()
            .ident_tbl
            .insert(blocked, IndexedIdKind::Parameter);
        let generator = IdGenerator::with_start_stamp(100);
        let mut external = |_: &Ident, _: &str| Some(external_function.clone());
        context.simplify_alias(&generator, &mut external);
        let Lambda::Lapply(expected_apply) = input else {
            unreachable!()
        };
        let expected = Lambda::Lapply(Box::new(Apply { ..*expected_apply }));
        assert_exact(&context.materialize(), &expected);
        assert_eq!(generator.current_stamp(), 100);
    }

    #[test]
    fn nullable_beta_arguments_bind_original_rhs_without_identity_compensation() {
        for primitive in [Primitive::PnullToOpt, Primitive::PnullUndefinedToOpt] {
            let x = id("x", 1);
            let predicate_loc = LamLoc::for_test(9);
            let unwrap_loc = LamLoc::for_test(10);
            let argument_loc = LamLoc::for_test(11);
            let effect_loc = LamLoc::for_test(12);
            let body = Lambda::if_(
                Lambda::prim(Primitive::PisNotNone, vec![Lambda::var(x)], predicate_loc),
                Lambda::prim(Primitive::PvalFromOption, vec![Lambda::var(x)], unwrap_loc),
                Lambda::const_(Constant::JsUndefined { is_unit: false }),
            );
            let effect = Lambda::prim(
                Primitive::PjsCall {
                    prim_name: "effect".into(),
                    arg_types: vec![],
                    ffi: Box::new(crate::lambda::lam_primitive::ExternalDecl::test_val("", 0)),
                },
                vec![],
                effect_loc,
            );
            let argument = Lambda::prim(primitive.clone(), vec![effect.clone()], argument_loc);
            let input = apply(
                Lambda::function_(1, vec![x], body, FunctionAttribute::default(), LamLoc::NONE),
                vec![argument.clone()],
            );
            let (actual, frontier, peak) = run(input, 200);
            let fresh = id("x", 201);
            let expected = Lambda::let_(
                LetKind::Strict,
                fresh,
                argument,
                Lambda::if_(
                    Lambda::prim(
                        Primitive::PisNotNone,
                        vec![Lambda::var(fresh)],
                        predicate_loc,
                    ),
                    Lambda::prim(
                        Primitive::PvalFromOption,
                        vec![Lambda::var(fresh)],
                        unwrap_loc,
                    ),
                    Lambda::const_(Constant::JsUndefined { is_unit: false }),
                ),
            );
            assert_exact(&actual, &expected);
            assert_eq!(frontier, 201);
            assert!(peak >= 1);
        }
    }

    #[test]
    fn directly_applied_function_uses_indexed_beta_and_resets_jsx() {
        let x = id("x", 1);
        let callee = id("callee", 2);
        let input = apply(
            Lambda::Lfunction(Box::new(LFunction {
                loc: LamLoc::NONE,
                arity: 1,
                params: vec![x],
                body: Box::new(apply(Lambda::var(callee), vec![Lambda::var(x)])),
                attr: FunctionAttribute::default(),
            })),
            vec![int(4)],
        );
        let (result, frontier, _) = run(input, 20);
        assert_exact(&result, &apply(Lambda::var(callee), vec![int(4)]));
        assert_eq!(frontier, 20);
    }

    #[test]
    fn complex_argument_freshens_binder_and_preserves_capture_avoidance() {
        let x = id("x", 1);
        let local = id("local", 2);
        let body = Lambda::let_(
            LetKind::Strict,
            local,
            int(1),
            Lambda::seq(Lambda::var(x), Lambda::var(local)),
        );
        let argument = Lambda::prim(
            Primitive::PjsCall {
                prim_name: "effect".into(),
                arg_types: vec![],
                ffi: Box::new(crate::lambda::lam_primitive::ExternalDecl::test_val("", 0)),
            },
            vec![],
            LamLoc::NONE,
        );
        let input = apply(
            Lambda::function_(1, vec![x], body, FunctionAttribute::default(), LamLoc::NONE),
            vec![argument.clone()],
        );
        let (result, frontier, substitution_peak) = run(input, 100);
        assert_eq!(frontier, 102);
        assert!(substitution_peak >= 2);
        let fresh_x = id("x", 101);
        let fresh_local = id("local", 102);
        let expected = Lambda::let_(
            LetKind::Strict,
            fresh_x,
            argument,
            Lambda::let_(
                LetKind::Strict,
                fresh_local,
                int(1),
                Lambda::seq(Lambda::var(fresh_x), Lambda::var(fresh_local)),
            ),
        );
        assert_exact(&result, &expected);
    }

    #[test]
    fn collected_block_field_and_optional_metadata_drive_alias_rewrites() {
        let block = id("block", 1);
        let optional = id("optional", 2);
        let source = id("source", 3);
        let input = Lambda::let_(
            LetKind::Strict,
            source,
            int(8),
            Lambda::let_(
                LetKind::Strict,
                block,
                Lambda::prim(
                    Primitive::Pmakeblock(
                        TagInfo::Tuple,
                        crate::lambda::lam_primitive::Mutable::Immutable,
                    ),
                    vec![int(7)],
                    LamLoc::NONE,
                ),
                Lambda::let_(
                    LetKind::Strict,
                    optional,
                    Lambda::prim(
                        Primitive::PnullToOpt,
                        vec![Lambda::var(source)],
                        LamLoc::NONE,
                    ),
                    Lambda::seq(
                        Lambda::prim(
                            Primitive::Pfield(0, FieldDbgInfo::Tuple),
                            vec![Lambda::var(block)],
                            LamLoc::NONE,
                        ),
                        Lambda::prim(
                            Primitive::PvalFromOption,
                            vec![Lambda::var(optional)],
                            LamLoc::NONE,
                        ),
                    ),
                ),
            ),
        );
        let expected = Lambda::let_(
            LetKind::Strict,
            source,
            int(8),
            Lambda::let_(
                LetKind::Strict,
                block,
                Lambda::prim(
                    Primitive::Pmakeblock(
                        TagInfo::Tuple,
                        crate::lambda::lam_primitive::Mutable::Immutable,
                    ),
                    vec![int(7)],
                    LamLoc::NONE,
                ),
                Lambda::let_(
                    LetKind::Strict,
                    optional,
                    Lambda::prim(
                        Primitive::PnullToOpt,
                        vec![Lambda::var(source)],
                        LamLoc::NONE,
                    ),
                    Lambda::seq(int(7), Lambda::var(source)),
                ),
            ),
        );
        let (result, frontier, _) = run(input, 20);
        assert_exact(&result, &expected);
        assert_eq!(frontier, 20);
    }

    #[test]
    fn external_query_order_and_failed_inline_reset_application_jsx() {
        let module = id("External", 1);
        let target = Lambda::prim(
            Primitive::Pfield(0, FieldDbgInfo::Module { name: "run".into() }),
            vec![Lambda::global_module(module)],
            LamLoc::NONE,
        );
        let input = apply(target.clone(), vec![int(1)]);
        let generator = IdGenerator::with_start_stamp(10);
        let mut context = IndexedLambdaContext::from_lambda(input, []);
        context.collect_info();
        let mut calls = Vec::new();
        let mut external = |id: &Ident, field: &str| {
            calls.push((id.name().to_string(), field.to_string()));
            None
        };
        context.simplify_alias(&generator, &mut external);
        assert_eq!(calls, vec![("External".into(), "run".into())]);
        assert_exact(&context.materialize(), &apply(target, vec![int(1)]));
        assert_eq!(generator.current_stamp(), 10);
    }

    #[test]
    fn one_store_sequence_collects_exits_collects_and_simplifies_alias() {
        let f = id("f", 1);
        let x = id("x", 2);
        let function = Lambda::function_(
            1,
            vec![x],
            Lambda::prim(Primitive::Pidentity, vec![Lambda::var(x)], LamLoc::NONE),
            FunctionAttribute::default(),
            LamLoc::NONE,
        );
        let raised = Lambda::static_raise(7, vec![int(9)]);
        let caught = Lambda::static_catch(
            raised,
            7,
            vec![x],
            apply(Lambda::var(f), vec![Lambda::var(x)]),
        );
        let expected_function = function.clone();
        let expected_f = f;
        let input = Lambda::let_(LetKind::Strict, f, function, caught);
        let generator = IdGenerator::with_start_stamp(20);
        let mut context = IndexedLambdaContext::from_lambda(input, []);
        context.collect_info();
        context.simplify_exits(&generator);
        context.collect_info();
        let mut external = |_: &Ident, _: &str| None;
        context.simplify_alias(&generator, &mut external);
        context.deep_flatten(&generator);
        let expected = Lambda::let_(
            LetKind::StrictOpt,
            expected_f,
            expected_function,
            Lambda::prim(Primitive::Pidentity, vec![int(9)], LamLoc::NONE),
        );
        assert_exact(&context.materialize(), &expected);
        let measurements = context.storage_measurements();
        assert_eq!(
            (
                measurements.node_allocations,
                measurements.current_root_unique_nodes,
                measurements.metadata_unique_nodes,
                measurements.live_unique_nodes,
                measurements.superseded_nodes,
                measurements.current_live_side_payload_shallow_bytes,
                measurements.metadata_retained_only_side_payload_shallow_bytes,
                measurements.superseded_unreachable_side_payload_shallow_bytes,
            ),
            (25, 6, 3, 8, 17, 392, 180, 812),
        );
    }
}
