//! Indexed `Lam_pass_remove_alias.simplify_alias`.

use crate::context::IdGenerator;
use crate::ident::Ident;
use crate::lambda::indexed::{IndexedLambda, IndexedLambdaContext, NodeId, NodeSnapshot, NodeView};
use crate::lambda::lam_analysis_indexed::{hit_variable, is_closed_with_map, no_side_effects};
use crate::lambda::lam_beta_reduce_indexed::{
    BetaDiagnostics, propagate_beta_reduce, propagate_beta_reduce_with_map,
};
use crate::lambda::lam_compat::FieldDbgInfo;
use crate::lambda::lam_compile_context::BoxedNullable;
use crate::lambda::lam_indexed_helpers::append_rebuilt;
use crate::lambda::lam_pass_collect_indexed::indexed_size;
use crate::lambda::lam_pass_collect_indexed::{IndexedElement, IndexedIdKind, IndexedLamStats};
use crate::lambda::lam_primitive::Primitive;
use crate::lambda::{InlineAttribute, Lambda, TagInfo};
use crate::location::Location;

pub type IndexedExternalInlineResolver<'a> = dyn FnMut(&Ident, bool, &str) -> Option<Lambda> + 'a;

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
    matches!(
        value,
        crate::lambda::Constant::Some(_)
            | crate::lambda::Constant::Block {
                tag_info: TagInfo::Some | TagInfo::SomeNotNested,
                ..
            }
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
            let base = store.append(NodeSnapshot::GlobalModule(module.clone(), false));
            Some(append_rebuilt(
                store,
                NodeSnapshot::Prim(
                    Primitive::Pfield(index, info.clone()),
                    vec![base],
                    Location::none(),
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
            let selected = match (info, tag_info) {
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
            let body_size = indexed_size(store, body);
            body_size < 5
                || (args
                    .iter()
                    .all(|node| matches!(store.view(*node), NodeView::Const(_)))
                    && body_size < 10
                    && no_side_effects(store, body))
                || match store.snapshot(body) {
                    NodeSnapshot::Switch {
                        scrutinee,
                        consts_full,
                        consts,
                        blocks_full,
                        blocks,
                        fail_action,
                        dispatch,
                    } => {
                        let Some((_, arg)) = params.iter().zip(args).find(|(param, _)| matches!(store.view(scrutinee), NodeView::Var(id) if id.same(param))) else { return false; };
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
                            indexed_size(store, reduced) < 5
                        }
                    }
                    NodeSnapshot::IfThenElse(condition, then_, else_) => {
                        let Some((_, arg)) = params.iter().zip(args).find(|(param, _)| matches!(store.view(condition), NodeView::Var(id) if id.same(param))) else { return false; };
                        if !matches!(store.view(*arg), NodeView::Const(_)) {
                            false
                        } else {
                            let reduced =
                                append_rebuilt(store, NodeSnapshot::IfThenElse(*arg, then_, else_));
                            indexed_size(store, reduced) < 5
                        }
                    }
                    _ => false,
                }
        }
    }
}

struct Simplifier<'a> {
    store: &'a mut IndexedLambda,
    meta: &'a mut IndexedLamStats,
    id_gen: &'a IdGenerator,
    beta_hash_bucket_count: &'a mut usize,
    beta_diagnostics: &'a mut BetaDiagnostics,
    jsx_preserve: bool,
    external: &'a mut IndexedExternalInlineResolver<'a>,
}

impl Simplifier<'_> {
    fn simpl(&mut self, node: NodeId) -> NodeId {
        match self.store.snapshot(node) {
            NodeSnapshot::Var(_)
            | NodeSnapshot::GlobalModule(_, _)
            | NodeSnapshot::Const(_)
            | NodeSnapshot::Break
            | NodeSnapshot::Continue => node,
            NodeSnapshot::Prim(primitive @ Primitive::PjsCall { .. }, args, loc)
                if self.jsx_preserve
                    && matches!(&primitive, Primitive::PjsCall { prim_name, .. } if prim_name == "jsx" || prim_name == "jsxs")
                    && args.first().is_some_and(|node| {
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
                    let id = id.clone();
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
                    NodeView::Var(id) => id.clone(),
                    _ => unreachable!(),
                };
                match self.meta.ident_tbl.get(&id) {
                    Some(IndexedIdKind::OptionalBlock(value, _)) => *value,
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
                    let id = id.clone();
                    let loc = loc.clone();
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
                                NodeSnapshot::Prim(primitive, vec![value], Location::none()),
                            );
                            let not = append_rebuilt(
                                self.store,
                                NodeSnapshot::Prim(Primitive::Pnot, vec![pred], Location::none()),
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
            NodeSnapshot::Apply(function, args, info, jsx) => {
                self.simpl_apply(function, args, info, jsx)
            }
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
            NodeSnapshot::Function(a, p, b, attr) => {
                NodeSnapshot::Function(a, p, self.simpl(b), attr)
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
        jsx: bool,
    ) -> NodeId {
        let mut fallback_jsx = jsx;
        if let NodeView::Prim(Primitive::Pfield(_, FieldDbgInfo::Module { name }), [base], _) =
            self.store.view(function)
            && let NodeView::GlobalModule(module, dynamic) = self.store.view(*base)
        {
            fallback_jsx = false;
            let (module, dynamic, name) = (module.clone(), dynamic, name.clone());
            if let Some(lambda) = (self.external)(&module, dynamic, &name) {
                let imported = self.store.append_compat_lambda(lambda);
                if let NodeSnapshot::Function(_,params,body,attr)=self.store.snapshot(imported) && params.len()==args.len() && !attr.async_ && attr.directive.is_none() && args.iter().all(|arg| !matches!(self.store.view(*arg),NodeView::Var(id) if matches!(self.meta.ident_tbl.get(id),Some(IndexedIdKind::Parameter)))) { let reduced=propagate_beta_reduce(self.store,self.meta,&params,body,&args,self.id_gen,self.beta_hash_bucket_count,self.beta_diagnostics); return self.simpl(reduced); }
            }
        }
        if let NodeView::Var(id) = self.store.view(function) {
            let id = id.clone();
            let args: Vec<_> = args.into_iter().map(|n| self.simpl(n)).collect();
            let candidate = match self.meta.ident_tbl.get(&id).cloned() {
                Some(IndexedIdKind::FunctionId {
                    lambda: Some((node, rec_flag)),
                    ..
                }) => match self.store.snapshot(node) {
                    NodeSnapshot::Function(_, params, body, attr)
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
                        self.beta_hash_bucket_count,
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
                                    self.beta_hash_bucket_count,
                                    self.beta_diagnostics,
                                );
                            }
                            crate::lambda::lam_compile_context::RecFlag::SelfRec => {}
                            crate::lambda::lam_compile_context::RecFlag::NonRec
                                if !args.iter().any(|n| hit_variable(self.store, &id, *n)) =>
                            {
                                let reduced = propagate_beta_reduce_with_map(
                                    self.store,
                                    self.meta,
                                    &map,
                                    &params,
                                    body,
                                    &args,
                                    self.id_gen,
                                    self.beta_hash_bucket_count,
                                    self.beta_diagnostics,
                                );
                                return self.simpl(reduced);
                            }
                            _ => {}
                        }
                    }
                }
            }
            let function = self.simpl(function);
            return append_rebuilt(self.store, NodeSnapshot::Apply(function, args, info, jsx));
        }
        if let NodeSnapshot::Function(_, params, body, attr) = self.store.snapshot(function)
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
                self.beta_hash_bucket_count,
                self.beta_diagnostics,
            );
            return self.simpl(reduced);
        }
        let function = self.simpl(function);
        let args = args.into_iter().map(|n| self.simpl(n)).collect();
        append_rebuilt(
            self.store,
            NodeSnapshot::Apply(function, args, info, fallback_jsx),
        )
    }
}

impl IndexedLambdaContext {
    pub fn simplify_alias(
        &mut self,
        id_gen: &IdGenerator,
        jsx_preserve: bool,
        external: &mut IndexedExternalInlineResolver<'_>,
    ) {
        let root = self.current_root();
        let mut beta_diagnostics = BetaDiagnostics::default();
        let root = {
            let (store, meta, beta_hash_bucket_count) = self.alias_parts_mut();
            Simplifier {
                store,
                meta,
                id_gen,
                beta_hash_bucket_count,
                beta_diagnostics: &mut beta_diagnostics,
                jsx_preserve,
                external,
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
            loc: Location::none(),
            inlined: InlineAttribute::Default,
            status: ApplyStatus::Na,
        }
    }
    fn apply(function: Lambda, args: Vec<Lambda>, jsx: bool) -> Lambda {
        Lambda::Lapply(Apply {
            ap_func: Box::new(function),
            ap_args: args,
            ap_info: info(),
            ap_transformed_jsx: jsx,
        })
    }
    fn run(input: Lambda, start: i32) -> (Lambda, i32, usize) {
        let generator = IdGenerator::with_start_stamp(start);
        let mut context = IndexedLambdaContext::from_lambda(input, []);
        context.collect_info();
        let mut external = |_: &Ident, _: bool, _: &str| None;
        context.simplify_alias(&generator, false, &mut external);
        (
            context.materialize(),
            generator.current_stamp(),
            context.beta_substitution_peak_unique_nodes(),
        )
    }

    #[test]
    fn directly_applied_function_uses_indexed_beta_and_resets_jsx() {
        let x = id("x", 1);
        let callee = id("callee", 2);
        let input = apply(
            Lambda::Lfunction(LFunction {
                arity: 1,
                params: vec![x.clone()],
                body: Box::new(apply(
                    Lambda::var(callee.clone()),
                    vec![Lambda::var(x)],
                    true,
                )),
                attr: FunctionAttribute::default(),
            }),
            vec![int(4)],
            true,
        );
        let (result, frontier, _) = run(input, 20);
        assert!(
            matches!(result, Lambda::Lapply(Apply { ap_transformed_jsx: false, ap_args, .. }) if matches!(ap_args.as_slice(), [Lambda::Lconst(Constant::Int { i: 4, .. })]))
        );
        assert_eq!(frontier, 20);
    }

    #[test]
    fn complex_argument_freshens_binder_and_preserves_capture_avoidance() {
        let x = id("x", 1);
        let local = id("local", 2);
        let body = Lambda::let_(
            LetKind::Strict,
            local.clone(),
            int(1),
            Lambda::seq(Lambda::var(x.clone()), Lambda::var(local)),
        );
        let argument = Lambda::prim(
            Primitive::PjsCall {
                prim_name: "effect".into(),
                arg_types: vec![],
                ffi: crate::lambda::lam_primitive::ExternalFfiSpec {
                    kind: crate::lambda::lam_primitive::ExternalFfiKind::Default,
                    spec: None,
                    obj_params: None,
                    return_wrapper: crate::lambda::lam_primitive::ExternalReturnWrapper::Identity,
                    inline_constant: None,
                },
                dynamic_import: false,
                transformed_jsx: false,
            },
            vec![],
            Location::none(),
        );
        let input = apply(
            Lambda::function_(1, vec![x], body, FunctionAttribute::default()),
            vec![argument],
            false,
        );
        let (result, frontier, substitution_peak) = run(input, 100);
        assert_eq!(frontier, 102);
        assert!(substitution_peak >= 2);
        let text = format!("{result:#?}");
        assert!(text.contains("x/101"));
        assert!(text.contains("local/102"));
        assert!(text.find("effect").unwrap() < text.find("local/102").unwrap());
    }

    #[test]
    fn collected_block_field_and_optional_metadata_drive_alias_rewrites() {
        let block = id("block", 1);
        let optional = id("optional", 2);
        let source = id("source", 3);
        let input = Lambda::let_(
            LetKind::Strict,
            source.clone(),
            int(8),
            Lambda::let_(
                LetKind::Strict,
                block.clone(),
                Lambda::prim(
                    Primitive::Pmakeblock(
                        TagInfo::Tuple,
                        crate::lambda::lam_primitive::Mutable::Immutable,
                    ),
                    vec![int(7)],
                    Location::none(),
                ),
                Lambda::let_(
                    LetKind::Strict,
                    optional.clone(),
                    Lambda::prim(
                        Primitive::PnullToOpt,
                        vec![Lambda::var(source)],
                        Location::none(),
                    ),
                    Lambda::seq(
                        Lambda::prim(
                            Primitive::Pfield(0, FieldDbgInfo::Tuple),
                            vec![Lambda::var(block)],
                            Location::none(),
                        ),
                        Lambda::prim(
                            Primitive::PvalFromOption,
                            vec![Lambda::var(optional)],
                            Location::none(),
                        ),
                    ),
                ),
            ),
        );
        let (result, frontier, _) = run(input, 20);
        let text = format!("{result:#?}");
        assert!(text.contains("i: 7"));
        assert!(text.contains("i: 8"));
        assert!(!text.contains("Pfield"));
        assert!(!text.contains("PvalFromOption"));
        assert_eq!(frontier, 20);
    }

    #[test]
    fn external_query_order_and_failed_inline_reset_application_jsx() {
        let module = id("External", 1);
        let target = Lambda::prim(
            Primitive::Pfield(0, FieldDbgInfo::Module { name: "run".into() }),
            vec![Lambda::global_module(module.clone(), true)],
            Location::none(),
        );
        let input = apply(target, vec![int(1)], true);
        let generator = IdGenerator::with_start_stamp(10);
        let mut context = IndexedLambdaContext::from_lambda(input, []);
        context.collect_info();
        let mut calls = Vec::new();
        let mut external = |id: &Ident, dynamic: bool, field: &str| {
            calls.push((id.name().to_string(), dynamic, field.to_string()));
            None
        };
        context.simplify_alias(&generator, false, &mut external);
        assert_eq!(calls, vec![("External".into(), true, "run".into())]);
        assert!(matches!(
            context.materialize(),
            Lambda::Lapply(Apply {
                ap_transformed_jsx: false,
                ..
            })
        ));
        assert_eq!(generator.current_stamp(), 10);
    }

    #[test]
    fn one_store_sequence_collects_exits_collects_and_simplifies_alias() {
        let f = id("f", 1);
        let x = id("x", 2);
        let function = Lambda::function_(
            1,
            vec![x.clone()],
            Lambda::prim(
                Primitive::Pidentity,
                vec![Lambda::var(x.clone())],
                Location::none(),
            ),
            FunctionAttribute::default(),
        );
        let raised = Lambda::static_raise(7, vec![int(9)]);
        let caught = Lambda::static_catch(
            raised,
            7,
            vec![x.clone()],
            apply(Lambda::var(f.clone()), vec![Lambda::var(x)], false),
        );
        let input = Lambda::let_(LetKind::Strict, f, function, caught);
        let generator = IdGenerator::with_start_stamp(20);
        let mut context = IndexedLambdaContext::from_lambda(input, []);
        context.collect_info();
        context.simplify_exits(&generator);
        context.collect_info();
        let mut external = |_: &Ident, _: bool, _: &str| None;
        context.simplify_alias(&generator, false, &mut external);
        context.deep_flatten(&generator);
        let result = format!("{:#?}", context.materialize());
        assert!(result.contains("i: 9"));
        assert!(!result.contains("LstaticCatch"));
        assert!(context.storage_measurements().superseded_nodes > 0);
    }
}
