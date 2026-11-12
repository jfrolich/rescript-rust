//! P: compile_primitive_js comparison helpers. Literal folds belong to lowering;
//! constructor rewrites remain in the named section-6 J rules.
use super::*;
use crate::bir::j::{norm, plain};
use crate::js_ir::BinOp;
use crate::lambda::lam_compat::Comparison;

pub(super) fn comparison_op(cmp: Comparison, float: bool) -> BinOp {
    use Comparison::*;
    match (cmp, float) {
        (Eq, _) => BinOp::EqEqEq, (Neq, _) => BinOp::NotEqEq,
        (Lt, false) => BinOp::Lt, (Le, false) => BinOp::Le,
        (Gt, false) => BinOp::Gt, (Ge, false) => BinOp::Ge,
        (Lt, true) => BinOp::FloatLt, (Le, true) => BinOp::FloatLe,
        (Gt, true) => BinOp::FloatGt, (Ge, true) => BinOp::FloatGe,
    }
}
impl State {
    pub(super) fn primitive_bool(&self, node: NodeId) -> Option<bool> {
        matches!(self.arena.view(node), View::JBool).then(|| self.arena.node(node).aux() != 0)
    }
    pub(super) fn primitive_string(&self, node: NodeId) -> Option<&str> {
        match self.arena.view(node) {
            View::JStr { text } => Some(self.arena.text(text)),
            View::JTemplate { info, .. } if self.arena.node(node).aux() == 1 => {
                let crate::bir::JsPayload::Template(parts) = self.arena.javascript(info) else { unreachable!() };
                parts[0].cooked.map(|s| self.arena.text(s))
            }
            _ => None,
        }
    }
    fn primitive_bigint(&self, node: NodeId) -> Option<&str> {
        if let View::JNumber { value } = self.arena.view(node) {
            if let crate::bir::Constant::BigInt(s) = self.arena.constant(value) {
                return Some(self.arena.text(*s));
            }
        }
        None
    }
    pub(super) fn comparison_constant(&mut self, left: NodeId, right: NodeId, value: bool) -> NodeId {
        self.arena.release(left);
        self.arena.release(right);
        plain::boolean(&mut self.arena, value)
    }
    /// P: compile_bool_comparison, including one-sided folds preserving effects.
    pub(super) fn primitive_bool_comparison(&mut self, cmp: Comparison, left: NodeId, right: NodeId) -> NodeId {
        use Comparison::*;
        let l = self.primitive_bool(left);
        let r = self.primitive_bool(right);
        if let (Some(l), Some(r)) = (l, r) {
            return self.comparison_constant(left, right, cmp.cmp_int32(i32::from(l), i32::from(r)));
        }
        let fold = if l == Some(true) || r == Some(false) {
            match cmp { Lt => Some(false), Ge => Some(true), _ => None }
        } else if r == Some(true) || l == Some(false) {
            match cmp { Le => Some(true), Gt => Some(false), _ => None }
        } else { None };
        if let Some(value) = fold {
            let kept = if l.is_some() { self.arena.release(left); right } else { self.arena.release(right); left };
            let value = plain::boolean(&mut self.arena, value);
            return norm::jm1_js_seq(&mut self.arena, kept, value);
        }
        norm::je4_bin(&mut self.arena, comparison_op(cmp, false), left, right)
    }
    /// P: compile_int_comparison; compare-call stripping consumes shells once.
    pub(super) fn primitive_int_comparison(&mut self, cmp: Comparison, mut left: NodeId, mut right: NodeId) -> NodeId {
        use Comparison::*;
        loop {
            if let (Some(l), Some(r)) = (self.primitive_int(left), self.primitive_int(right)) {
                return self.comparison_constant(left, right, cmp.cmp_int32(l, r));
            }
            let pair = if self.primitive_int(right) == Some(0) {
                if let View::JCall { callee, args: [l, r], .. } = self.arena.view(left) {
                    if let View::JQualified { module, member: Some(member) } = self.arena.view(callee) {
                        (matches!(self.arena.pools.j_modules[module.index()].kind, crate::js_ir::Kind::Runtime)
                            && self.arena.text(member) == "compare").then_some((*l, *r))
                    } else { None }
                } else { None }
            } else { None };
            if let Some((l, r)) = pair {
                self.arena.detach(l); self.arena.detach(r);
                self.arena.release(left); self.arena.release(right);
                left = l; right = r;
            } else { break; }
        }
        let lv = self.arena.view(left);
        let rv = self.arena.view(right);
        let optional_undefined = matches!((lv, rv),
            (View::JOptional { .. }, View::JUndefined) | (View::JUndefined, View::JOptional { .. }));
        let block_number = matches!((lv, rv),
            (View::JBlockLit { .. }, View::JNumber { .. }) | (View::JNumber { .. }, View::JBlockLit { .. }));
        if (optional_undefined && matches!(cmp, Eq | Neq) || block_number && cmp == Neq)
            && crate::bir::j::facts::strictly_pure(&self.arena, left)
            && crate::bir::j::facts::strictly_pure(&self.arena, right) {
            return self.comparison_constant(left, right, cmp == Neq);
        }
        match cmp {
            Eq => norm::jm2_int_equality(&mut self.arena, left, right),
            Neq => plain::bin(&mut self.arena, BinOp::NotEqEq, left, right),
            _ => norm::je4_bin(&mut self.arena, comparison_op(cmp, false), left, right),
        }
    }
    /// P: compile_string_comparison / compile_bigint_comparison.
    pub(super) fn primitive_literal_comparison(&mut self, cmp: Comparison, left: NodeId, right: NodeId, bigint: bool) -> NodeId {
        let equal = if bigint {
            self.primitive_bigint(left).zip(self.primitive_bigint(right)).map(|(l, r)| {
                l.as_bytes()[0] == r.as_bytes()[0]
                    && l[1..].chars().filter(|c| *c != '_').skip_while(|c| *c == '0')
                    .eq(r[1..].chars().filter(|c| *c != '_').skip_while(|c| *c == '0'))
            })
        } else { self.primitive_string(left).zip(self.primitive_string(right)).map(|(l, r)| l == r) };
        if let Some(equal) = equal {
            if matches!(cmp, Comparison::Eq | Comparison::Neq) {
                return self.comparison_constant(left, right, equal != (cmp == Comparison::Neq));
            }
        }
        norm::je4_bin(&mut self.arena, comparison_op(cmp, false), left, right)
    }
    /// P: compile_object_comparison. Only nullish equality bypasses the runtime.
    pub(super) fn primitive_object_comparison(&mut self, cmp: Comparison, left: NodeId, right: NodeId) -> NodeId {
        use Comparison::*;
        if matches!(cmp, Eq | Neq) && [left, right].iter().any(|&n| matches!(self.arena.view(n), View::JNull | View::JUndefined)) {
            return norm::jm2_nullish_strict_comparison(&mut self.arena, cmp == Neq, left, right);
        }
        let member = match cmp { Eq => "equal", Neq => "notequal", Lt => "lessthan", Le => "lessequal", Gt => "greaterthan", Ge => "greaterequal" };
        self.primitive_runtime("Primitive_object", member, &[left, right])
    }
    /// P: compile_typed_min_max. Only literal leaves are copied for the test;
    /// operands that may execute code use a runtime call instead.
    pub(super) fn primitive_min_max(&mut self, kind: &str, max: bool, left: NodeId, right: NodeId) -> NodeId {
        let literals = match kind {
            "bool" => self.primitive_bool(left).is_some() && self.primitive_bool(right).is_some(),
            "int" => self.primitive_int(left).is_some() && self.primitive_int(right).is_some(),
            "string" => self.primitive_string(left).is_some() && self.primitive_string(right).is_some(),
            "bigint" => self.primitive_bigint(left).is_some() && self.primitive_bigint(right).is_some(),
            "float" => [left, right].iter().all(|&n| matches!(self.arena.view(n), View::JNumber { value } if matches!(self.arena.constant(value), crate::bir::Constant::Float(_)))),
            "object" => false,
            _ => unreachable!("comparison type"),
        };
        if literals {
            let l = self.arena.copy_subtree(left, &[]);
            let r = self.arena.copy_subtree(right, &[]);
            let op = comparison_op(if max { Comparison::Gt } else { Comparison::Lt }, kind != "bigint");
            let test = norm::je4_bin(&mut self.arena, op, l, r);
            norm::je7_cond(&mut self.arena, test, left, right)
        } else {
            self.primitive_runtime(&format!("Primitive_{kind}"), if max { "max" } else { "min" }, &[left, right])
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lambda::{arena::LamArena, lam_constant::Constant as C, lam_primitive::Primitive as P, LamLoc};

    fn literals() -> Vec<C> {
        vec![C::JsTrue, C::JsFalse, C::JsNull, C::JsUndefined { is_unit: false },
            C::Int { i: -1, comment: None }, C::Int { i: 0, comment: None }, C::Int { i: 1, comment: None },
            C::Float("1.".into()), C::Float("nan".into()),
            C::String("a".into()), C::String("b".into()),
            C::BigInt { negative: false, value: "00_12".into() },
            C::BigInt { negative: false, value: "12".into() },
            C::BigInt { negative: true, value: "12".into() },
            C::Some(Box::new(C::JsUndefined { is_unit: false })),
            C::Block { tag_info: Box::new(crate::lambda::TagInfo::Tuple), elements: vec![C::JsTrue] }]
    }

    #[test]
    fn comparison_arms_and_literal_folds_match_legacy() {
        for cmp in [Comparison::Eq, Comparison::Neq, Comparison::Lt, Comparison::Le, Comparison::Gt, Comparison::Ge] {
            for primitive in [P::Pboolcomp(cmp), P::Pintcomp(cmp), P::Pfloatcomp(cmp), P::Pstringcomp(cmp), P::Pbigintcomp(cmp), P::Pobjcomp(cmp), P::Pjscomp(cmp)] {
                check_pairs(primitive);
            }
        }
    }

    #[test]
    fn order_and_min_max_arms_match_legacy() {
        for primitive in [P::Pboolorder, P::Pintorder, P::Pfloatorder, P::Pstringorder, P::Pbigintorder, P::Pobjorder,
            P::Pboolmin, P::Pboolmax, P::Pintmin, P::Pintmax, P::Pfloatmin, P::Pfloatmax,
            P::Pstringmin, P::Pstringmax, P::Pbigintmin, P::Pbigintmax, P::Pobjmin, P::Pobjmax] {
            check_pairs(primitive);
        }
    }

    fn check_pairs(primitive: P) {
        let literals = literals();
        for l in 0..literals.len() + 2 {
            for r in 0..literals.len() + 2 {
                let mut a = LamArena::new();
                let mut operand = |index: usize, stamp| {
                    if let Some(value) = literals.get(index) { a.const_(value.clone()) }
                    else {
                        let value = a.var(Ident::new("value", stamp, crate::ident::IdentFlags::NONE));
                        if index == literals.len() { value }
                        else { a.prim_raw(P::PinitMod, &[value], LamLoc::NONE) }
                    }
                };
                let left = operand(l, 10);
                let right = operand(r, 11);
                let root = a.prim_raw(primitive.clone(), &[left, right], LamLoc::NONE);
                super::super::oracle_tests::compare(a, root);
            }
        }
    }

    #[test]
    fn integer_comparison_strips_runtime_compare_before_zero() {
        for primitive in [P::Pintorder, P::Pboolorder, P::Pstringorder, P::Pfloatorder, P::Pbigintorder, P::Pobjorder] {
            for cmp in [Comparison::Eq, Comparison::Neq, Comparison::Lt, Comparison::Le, Comparison::Gt, Comparison::Ge] {
                let mut a = LamArena::new();
                let l = a.var(Ident::new("left", 10, crate::ident::IdentFlags::NONE));
                let r = a.var(Ident::new("right", 11, crate::ident::IdentFlags::NONE));
                let order = a.prim_raw(primitive.clone(), &[l, r], LamLoc::NONE);
                let zero = a.const_(C::Int { i: 0, comment: None });
                let root = a.prim_raw(P::Pintcomp(cmp), &[order, zero], LamLoc::NONE);
                super::super::oracle_tests::compare(a, root);
            }
        }
    }
}
