//! Construction and inspection boundary for typed-tree translation and matching.
//!
//! This is a static-dispatch interface: it preserves the existing raw node,
//! payload and list handles. In particular it does not perform lowering or
//! change action sharing. Readers hold a borrow only while inspecting nodes;
//! drop the guard before calling a constructor.
//!
//! The observation schema is deliberately today's `Lam`/`Node`/`View`, not a
//! new IR. A later builder must provide equivalent raw observations while
//! lowering; notably string-switch views currently borrow `LamArena` storage.
//! That representation seam must be adapted with the new builder, rather than
//! silently changing the match compiler's key or equality semantics here.

use super::{RawArena, RawLambda, RawLambdaSwitch};
use crate::ident::Ident;
use crate::lambda::arena::{
    ApplyId, ApplyPayload, IdentId, Lam, LamArena, Node, PrimId, PrimPayload, View,
};
use crate::lambda::{
    ApInfo, Constant, DirectionFlag, FunctionAttribute, LamLoc, LetKind, Primitive,
};
use std::cell::Ref;
use std::ops::Deref;

/// The read-back operations used by conversion and match compilation.
/// Views describe raw semantics, including unlowered constants and primitives.
/// The next builder must preserve these observations, not its storage layout.
pub trait RawLambdaRead {
    /// The compact node and its payload handles.
    fn node(&self, lam: Lam) -> Node;
    /// The node with borrowed payloads and child slices resolved.
    fn view(&self, lam: Lam) -> View<'_>;
    /// Resolve an identifier payload handle.
    fn ident(&self, id: IdentId) -> Ident;
    /// The identifier of a variable node, if any.
    fn as_var(&self, lam: Lam) -> Option<Ident>;
    /// Borrow the constant payload, if any.
    fn as_const(&self, lam: Lam) -> Option<&Constant>;
    /// Borrow call attributes and arguments metadata.
    fn apply_payload(&self, id: ApplyId) -> &ApplyPayload;
    /// Borrow a primitive and its location.
    fn prim_payload(&self, id: PrimId) -> &PrimPayload;
    /// Existing conservative structural equivalence (not action-key equality).
    fn eq_approx(&self, lhs: Lam, rhs: Lam) -> bool;
    /// Visit immediate children in the existing arena order.
    fn iter_children(&self, lam: Lam, f: impl FnMut(Lam));
}

impl RawLambdaRead for LamArena {
    #[inline]
    fn node(&self, lam: Lam) -> Node {
        LamArena::node(self, lam)
    }
    #[inline]
    fn view(&self, lam: Lam) -> View<'_> {
        LamArena::view(self, lam)
    }
    #[inline]
    fn ident(&self, id: IdentId) -> Ident {
        LamArena::ident(self, id)
    }
    #[inline]
    fn as_var(&self, lam: Lam) -> Option<Ident> {
        LamArena::as_var(self, lam)
    }
    #[inline]
    fn as_const(&self, lam: Lam) -> Option<&Constant> {
        LamArena::as_const(self, lam)
    }
    #[inline]
    fn apply_payload(&self, id: ApplyId) -> &ApplyPayload {
        LamArena::apply_payload(self, id)
    }
    #[inline]
    fn prim_payload(&self, id: PrimId) -> &PrimPayload {
        LamArena::prim_payload(self, id)
    }
    #[inline]
    fn eq_approx(&self, lhs: Lam, rhs: Lam) -> bool {
        LamArena::eq_approx(self, lhs, rhs)
    }
    #[inline]
    fn iter_children(&self, lam: Lam, f: impl FnMut(Lam)) {
        LamArena::iter_children(self, lam, f)
    }
}

/// Owned string-switch read-back: scrutinee, ordered cases and default action.
pub type StringSwitchParts = (RawLambda, Vec<(String, RawLambda)>, Option<RawLambda>);

/// Builds raw nodes bottom-up without dynamic dispatch.
///
/// The two rewriting operations are explicit so implementations need not expose
/// mutable arena storage to the converter or integer-switch compiler.
pub trait RawLambdaBuilder {
    /// Storage-independent inspection interface.
    type Reader: RawLambdaRead;
    /// Borrow guard for a sequence of read-back operations.
    type Read<'a>: Deref<Target = Self::Reader>
    where
        Self: 'a;
    /// Borrow a reader. Release it before constructing or rewriting nodes.
    fn get(&self) -> Self::Read<'_>;
    /// The compact node and its payload handles.
    fn node(&self, lam: RawLambda) -> Node;
    /// The identifier of a variable node, if any.
    fn as_var(&self, lam: RawLambda) -> Option<Ident>;
    /// Whether `lam` is a constant node.
    fn is_const(&self, lam: RawLambda) -> bool;
    /// The constant of a `Lconst` node.
    fn const_of(&self, lam: RawLambda) -> Option<Constant>;
    /// Check if this is the unit value.
    fn is_unit(&self, lam: RawLambda) -> bool;
    /// Arity, parameters, body, attributes and location of a function node.
    fn function_parts(
        &self,
        lam: RawLambda,
    ) -> Option<(i32, Vec<Ident>, RawLambda, FunctionAttribute, LamLoc)>;
    /// The attributes of a function node.
    fn function_attr(&self, lam: RawLambda) -> Option<FunctionAttribute>;
    /// A function node with its attributes changed by `f`; `lam` must be a
    /// function.
    fn with_function_attr(
        &self,
        lam: RawLambda,
        f: impl FnOnce(&mut FunctionAttribute),
    ) -> RawLambda;
    /// The list `list` as an owned vector.
    fn list(&self, list: crate::lambda::arena::LamList) -> Vec<RawLambda>;
    /// The scrutinee and owned cases of a switch node.
    fn switch_parts(&self, lam: RawLambda) -> Option<(RawLambda, RawLambdaSwitch)>;
    /// The scrutinee, owned cases and default of a string switch node.
    fn string_switch_parts(
        &self,
        lam: RawLambda,
    ) -> Option<StringSwitchParts>;
    /// Push a node built from existing payload handles.
    fn push(&self, node: Node) -> RawLambda;
    /// Create a variable reference.
    fn var(&self, id: Ident) -> RawLambda;
    /// Create a global module reference. A predefined exception is its own
    /// name at runtime, so it becomes that string
    /// (`compiler/ml/transl_path.ml` `transl_normal_path`).
    fn global_module(&self, id: Ident) -> RawLambda;
    /// Create a constant.
    fn const_(&self, c: Constant) -> RawLambda;
    /// Unit constant.
    fn unit(&self) -> RawLambda;
    /// Create a function.
    fn function_(
        &self,
        arity: i32,
        params: &[Ident],
        body: RawLambda,
        attr: FunctionAttribute,
        loc: LamLoc,
    ) -> RawLambda;
    /// Create a let binding.
    fn let_(&self, kind: LetKind, id: Ident, value: RawLambda, body: RawLambda) -> RawLambda;
    /// Create recursive let bindings.
    fn letrec(&self, bindings: &[(Ident, RawLambda)], body: RawLambda) -> RawLambda;
    /// Create a primitive operation.
    fn prim(&self, primitive: Primitive, args: &[RawLambda], loc: LamLoc) -> RawLambda;
    /// `Lambda.mk_builtin` builds a builtin through the smart `Lambda.prim`
    /// (lambda.ml), whose folds evaluate a primitive over one or two
    /// constant arguments at construction. Those folds read constants only,
    /// so they are taken from [`crate::lambda::Lambda::prim`], applied to the constants in
    /// the form OCaml builds them (raw constants keep a few encodings, such
    /// as an int-named polymorphic variant, until they are lowered).
    fn prim_folded(&self, primitive: Primitive, args: &[RawLambda], loc: LamLoc) -> RawLambda;
    /// Translcore builds conditionals through the smart `Lambda.if_`
    /// (lambda.ml). Its constant-condition and `assert false` arms decide
    /// which branches the match compiler sees, so they apply here; the arms
    /// that rewrite the condition itself are applied by [`LamArena::if_`]
    /// when the term is lowered.
    fn if_(&self, cond: RawLambda, then_: RawLambda, else_: RawLambda) -> RawLambda;
    /// `Lifthenelse` without the smart constructor.
    fn if_raw(&self, cond: RawLambda, then_: RawLambda, else_: RawLambda) -> RawLambda;
    /// Create a sequence.
    fn seq(&self, first: RawLambda, second: RawLambda) -> RawLambda;
    /// Function application.
    fn apply(&self, func: RawLambda, args: &[RawLambda], info: ApInfo) -> RawLambda;
    /// Switch on integer/block tag.
    fn switch(&self, scrut: RawLambda, sw: RawLambdaSwitch) -> RawLambda;
    /// Switch on string value.
    fn string_switch(
        &self,
        scrut: RawLambda,
        cases: &[(String, RawLambda)],
        default: Option<RawLambda>,
    ) -> RawLambda;
    /// Raise a static exception.
    fn static_raise(&self, label: i32, args: &[RawLambda]) -> RawLambda;
    /// Catch a static exception.
    fn static_catch(
        &self,
        body: RawLambda,
        label: i32,
        params: &[Ident],
        handler: RawLambda,
    ) -> RawLambda;
    /// Evaluate the finally block on every exit from the body.
    fn try_finally(&self, body: RawLambda, finally: RawLambda) -> RawLambda;
    /// Try-with exception handling.
    fn try_with(&self, body: RawLambda, exn: Ident, handler: RawLambda) -> RawLambda;
    /// While loop.
    fn while_(&self, cond: RawLambda, body: RawLambda) -> RawLambda;
    /// For loop.
    fn for_(
        &self,
        var: Ident,
        start: RawLambda,
        finish: RawLambda,
        dir: DirectionFlag,
        body: RawLambda,
    ) -> RawLambda;
    /// For-of loop (upstream #7887).
    fn for_of(&self, var: Ident, iterable: RawLambda, body: RawLambda) -> RawLambda;
    /// For-await-of loop (upstream #7887).
    fn for_await_of(&self, var: Ident, iterable: RawLambda, body: RawLambda) -> RawLambda;
    /// Break out of the enclosing loop (port of OCaml `Lbreak`).
    fn break_(&self) -> RawLambda;
    /// Continue the enclosing loop (port of OCaml `Lcontinue`).
    fn continue_(&self) -> RawLambda;
    /// Assignment.
    fn assign(&self, id: Ident, value: RawLambda) -> RawLambda;
    /// Substitute identifier references using the existing plain shallow mapper.
    fn subst_idents(
        &self,
        subst: &crate::fast_hash::AHashMap<Ident, Ident>,
        lam: RawLambda,
    ) -> RawLambda;
    /// Add a default to a complete integer range switch on the same variable.
    /// Return `None` unless the existing switch covers exactly `lo..=hi`.
    fn switch_with_range_default(
        &self,
        arg: RawLambda,
        lo: i32,
        hi: i32,
        ifso: RawLambda,
        ifno: RawLambda,
    ) -> Option<RawLambda>;
}

impl RawLambdaBuilder for RawArena {
    type Reader = LamArena;
    type Read<'a> = Ref<'a, LamArena>;
    #[inline]
    fn get(&self) -> Self::Read<'_> {
        RawArena::get(self)
    }
    #[inline]
    fn node(&self, lam: RawLambda) -> Node {
        RawArena::node(self, lam)
    }
    #[inline]
    fn as_var(&self, lam: RawLambda) -> Option<Ident> {
        RawArena::as_var(self, lam)
    }
    #[inline]
    fn is_const(&self, lam: RawLambda) -> bool {
        RawArena::is_const(self, lam)
    }
    #[inline]
    fn const_of(&self, lam: RawLambda) -> Option<Constant> {
        RawArena::const_of(self, lam)
    }
    #[inline]
    fn is_unit(&self, lam: RawLambda) -> bool {
        RawArena::is_unit(self, lam)
    }
    #[inline]
    fn function_parts(
        &self,
        lam: RawLambda,
    ) -> Option<(i32, Vec<Ident>, RawLambda, FunctionAttribute, LamLoc)> {
        RawArena::function_parts(self, lam)
    }
    #[inline]
    fn function_attr(&self, lam: RawLambda) -> Option<FunctionAttribute> {
        RawArena::function_attr(self, lam)
    }
    #[inline]
    fn with_function_attr(
        &self,
        lam: RawLambda,
        f: impl FnOnce(&mut FunctionAttribute),
    ) -> RawLambda {
        RawArena::with_function_attr(self, lam, f)
    }
    #[inline]
    fn list(&self, list: crate::lambda::arena::LamList) -> Vec<RawLambda> {
        RawArena::list(self, list)
    }
    #[inline]
    fn switch_parts(&self, lam: RawLambda) -> Option<(RawLambda, RawLambdaSwitch)> {
        RawArena::switch_parts(self, lam)
    }
    #[inline]
    fn string_switch_parts(
        &self,
        lam: RawLambda,
    ) -> Option<StringSwitchParts> {
        RawArena::string_switch_parts(self, lam)
    }
    #[inline]
    fn push(&self, node: Node) -> RawLambda {
        RawArena::push(self, node)
    }
    #[inline]
    fn var(&self, id: Ident) -> RawLambda {
        RawArena::var(self, id)
    }
    #[inline]
    fn global_module(&self, id: Ident) -> RawLambda {
        RawArena::global_module(self, id)
    }
    #[inline]
    fn const_(&self, c: Constant) -> RawLambda {
        RawArena::const_(self, c)
    }
    #[inline]
    fn unit(&self) -> RawLambda {
        RawArena::unit(self)
    }
    #[inline]
    fn function_(
        &self,
        arity: i32,
        params: &[Ident],
        body: RawLambda,
        attr: FunctionAttribute,
        loc: LamLoc,
    ) -> RawLambda {
        RawArena::function_(self, arity, params, body, attr, loc)
    }
    #[inline]
    fn let_(&self, kind: LetKind, id: Ident, value: RawLambda, body: RawLambda) -> RawLambda {
        RawArena::let_(self, kind, id, value, body)
    }
    #[inline]
    fn letrec(&self, bindings: &[(Ident, RawLambda)], body: RawLambda) -> RawLambda {
        RawArena::letrec(self, bindings, body)
    }
    #[inline]
    fn prim(&self, primitive: Primitive, args: &[RawLambda], loc: LamLoc) -> RawLambda {
        RawArena::prim(self, primitive, args, loc)
    }
    #[inline]
    fn prim_folded(&self, primitive: Primitive, args: &[RawLambda], loc: LamLoc) -> RawLambda {
        RawArena::prim_folded(self, primitive, args, loc)
    }
    #[inline]
    fn if_(&self, cond: RawLambda, then_: RawLambda, else_: RawLambda) -> RawLambda {
        RawArena::if_(self, cond, then_, else_)
    }
    #[inline]
    fn if_raw(&self, cond: RawLambda, then_: RawLambda, else_: RawLambda) -> RawLambda {
        RawArena::if_raw(self, cond, then_, else_)
    }
    #[inline]
    fn seq(&self, first: RawLambda, second: RawLambda) -> RawLambda {
        RawArena::seq(self, first, second)
    }
    #[inline]
    fn apply(&self, func: RawLambda, args: &[RawLambda], info: ApInfo) -> RawLambda {
        RawArena::apply(self, func, args, info)
    }
    #[inline]
    fn switch(&self, scrut: RawLambda, sw: RawLambdaSwitch) -> RawLambda {
        RawArena::switch(self, scrut, sw)
    }
    #[inline]
    fn string_switch(
        &self,
        scrut: RawLambda,
        cases: &[(String, RawLambda)],
        default: Option<RawLambda>,
    ) -> RawLambda {
        RawArena::string_switch(self, scrut, cases, default)
    }
    #[inline]
    fn static_raise(&self, label: i32, args: &[RawLambda]) -> RawLambda {
        RawArena::static_raise(self, label, args)
    }
    #[inline]
    fn static_catch(
        &self,
        body: RawLambda,
        label: i32,
        params: &[Ident],
        handler: RawLambda,
    ) -> RawLambda {
        RawArena::static_catch(self, body, label, params, handler)
    }
    #[inline]
    fn try_finally(&self, body: RawLambda, finally: RawLambda) -> RawLambda {
        RawArena::try_finally(self, body, finally)
    }
    #[inline]
    fn try_with(&self, body: RawLambda, exn: Ident, handler: RawLambda) -> RawLambda {
        RawArena::try_with(self, body, exn, handler)
    }
    #[inline]
    fn while_(&self, cond: RawLambda, body: RawLambda) -> RawLambda {
        RawArena::while_(self, cond, body)
    }
    #[inline]
    fn for_(
        &self,
        var: Ident,
        start: RawLambda,
        finish: RawLambda,
        dir: DirectionFlag,
        body: RawLambda,
    ) -> RawLambda {
        RawArena::for_(self, var, start, finish, dir, body)
    }
    #[inline]
    fn for_of(&self, var: Ident, iterable: RawLambda, body: RawLambda) -> RawLambda {
        RawArena::for_of(self, var, iterable, body)
    }
    #[inline]
    fn for_await_of(&self, var: Ident, iterable: RawLambda, body: RawLambda) -> RawLambda {
        RawArena::for_await_of(self, var, iterable, body)
    }
    #[inline]
    fn break_(&self) -> RawLambda {
        RawArena::break_(self)
    }
    #[inline]
    fn continue_(&self) -> RawLambda {
        RawArena::continue_(self)
    }
    #[inline]
    fn assign(&self, id: Ident, value: RawLambda) -> RawLambda {
        RawArena::assign(self, id, value)
    }
    fn subst_idents(
        &self,
        subst: &crate::fast_hash::AHashMap<Ident, Ident>,
        lam: RawLambda,
    ) -> RawLambda {
        if subst.is_empty() {
            return lam;
        }
        fn go(
            a: &mut LamArena,
            subst: &crate::fast_hash::AHashMap<Ident, Ident>,
            lam: RawLambda,
        ) -> RawLambda {
            if let Some(id) = a.as_var(lam) {
                return match subst.get(&id) {
                    Some(id) => a.var(*id),
                    None => lam,
                };
            }
            a.shallow_map_plain(lam, &mut |a, child| go(a, subst, child))
        }
        self.with_mut(|a| go(a, subst, lam))
    }
    fn switch_with_range_default(
        &self,
        arg: RawLambda,
        lo: i32,
        hi: i32,
        ifso: RawLambda,
        ifno: RawLambda,
    ) -> Option<RawLambda> {
        self.with_mut(|a| {
            let Node::Switch {
                scrut,
                actions,
                info,
            } = a.node(ifno)
            else {
                return None;
            };
            let p = a.switch_payload(info);
            let same_var =
                matches!((a.as_var(arg), a.as_var(scrut)), (Some(x), Some(y)) if x.same(&y));
            if !(same_var
                && p.n_blocks() == 0
                && p.blocks_full
                && !p.has_fail
                && super::switch::covers_range(a.switch_const_keys(info), lo, hi))
            {
                return None;
            }
            let (blocks_full, dispatch) = (p.blocks_full, p.dispatch.clone());
            let keys = a.switch_const_keys(info).to_vec();
            let mut cases = a.list_small(actions);
            cases.push(ifso);
            let actions = a.add_list(&cases);
            let info = a.add_switch(false, keys, blocks_full, [], true, dispatch);
            Some(a.switch_raw(scrut, actions, info))
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lambda::{SwitchDispatch, SwitchKey};

    // Exercise the boundary from generic code: no arena-specific method or
    // mutable borrow is available to this caller.
    fn build_and_inspect<B: RawLambdaBuilder>(b: &B) -> RawLambda {
        let id = Ident::create_local("argument");
        let var = b.var(id);
        let unit = b.unit();
        let raised = b.static_raise(7, &[var]);
        let caught = b.static_catch(raised, 7, &[id], var);
        let body = b.seq(caught, unit);
        let function = b.function_(1, &[id], body, FunctionAttribute::default(), LamLoc::NONE);
        let (arity, params, actual_body, _, loc) = b.function_parts(function).unwrap();
        assert_eq!(
            (arity, params, actual_body, loc),
            (1, vec![id], body, LamLoc::NONE)
        );
        let read = b.get();
        assert_eq!(read.as_var(var), Some(id));
        assert!(matches!(read.view(raised), View::StaticRaise(7, [arg]) if *arg == var));
        let mut children = Vec::new();
        read.iter_children(body, |child| children.push(child));
        assert_eq!(children, vec![caught, unit]);
        drop(read);
        b.let_(LetKind::Strict, id, unit, function)
    }

    #[test]
    fn generic_construction_preserves_raw_nodes_and_readbacks() {
        let b = RawArena::new();
        let root = build_and_inspect(&b);
        assert!(matches!(
            b.get().view(root),
            View::Let(LetKind::Strict, _, _, _)
        ));
    }

    #[test]
    fn builder_substitution_preserves_original_and_rewrites_references() {
        fn substitute<B: RawLambdaBuilder>(b: &B) {
            let old = Ident::create_local("old");
            let new = Ident::create_local("new");
            let value = b.var(old);
            let root = b.seq(value, b.unit());
            let subst = [(old, new)].into_iter().collect();
            let changed = b.subst_idents(&subst, root);
            let read = b.get();
            let View::Sequence(first, _) = read.view(changed) else {
                panic!("sequence")
            };
            assert_eq!(read.as_var(first), Some(new));
            assert_eq!(read.as_var(value), Some(old));
        }
        substitute(&RawArena::new());
    }

    #[test]
    fn builder_range_default_requires_the_same_variable_and_full_range() {
        fn check<B: RawLambdaBuilder>(b: &B) {
            let var = b.var(Ident::create_local("scrutinee"));
            let other = b.var(Ident::create_local("other"));
            let action = b.unit();
            let fail = b.static_raise(9, &[]);
            let switch = b.switch(
                var,
                RawLambdaSwitch {
                    sw_consts_full: true,
                    sw_consts: vec![(SwitchKey::Int(0), action), (SwitchKey::Int(1), action)],
                    sw_blocks_full: true,
                    sw_blocks: vec![],
                    sw_failaction: None,
                    sw_dispatch: SwitchDispatch::Direct,
                },
            );
            assert!(
                b.switch_with_range_default(other, 0, 1, fail, switch)
                    .is_none()
            );
            assert!(
                b.switch_with_range_default(var, 0, 2, fail, switch)
                    .is_none()
            );
            let result = b
                .switch_with_range_default(var, 0, 1, fail, switch)
                .unwrap();
            let (scrut, parts) = b.switch_parts(result).unwrap();
            assert_eq!(scrut, var);
            assert!(!parts.sw_consts_full);
            assert_eq!(parts.sw_consts.len(), 2);
            assert_eq!(parts.sw_failaction, Some(fail));
            assert_eq!(b.switch_parts(switch).unwrap().1.sw_failaction, None);
        }
        check(&RawArena::new());
    }
}
