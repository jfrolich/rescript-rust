//! P: compile_primitive_js comparison helpers. Literal folds belong to lowering;
//! constructor rewrites remain in the named section-6 J rules.
use super::*;
use crate::emit::row::{Kind, flag};
use crate::js_ir::BinOp;
use crate::lambda::lam_compat::Comparison;

/// O(1): map one comparison tag without inspecting operands.
pub(super) fn comparison_op(cmp: Comparison, float: bool) -> BinOp {
    use Comparison::*;
    match (cmp, float) {
        (Eq, _) => BinOp::EqEqEq,
        (Neq, _) => BinOp::NotEqEq,
        (Lt, false) => BinOp::Lt,
        (Le, false) => BinOp::Le,
        (Gt, false) => BinOp::Gt,
        (Ge, false) => BinOp::Ge,
        (Lt, true) => BinOp::FloatLt,
        (Le, true) => BinOp::FloatLe,
        (Gt, true) => BinOp::FloatGt,
        (Ge, true) => BinOp::FloatGe,
    }
}
impl<B: super::js_stmt::JsStmt> State<'_, B> {
    /// O(1): read a boolean leaf tag, for the two readers in `prim.rs`.
    pub(super) fn primitive_bool(&self, node: NodeId) -> Option<bool> {
        self.bool_of(B::at(node))
    }
    /// O(1): the value of a boolean literal: its kind and its `aux`.
    fn bool_of(&self, r: B::Ref<'_>) -> Option<bool> {
        (self.js.kind(&self.arena, r) == Kind::Bool).then(|| self.js.aux(&self.arena, r) != 0)
    }
    /// O(released operand nodes): consume both trees and build one boolean.
    pub(super) fn comparison_constant(&mut self, left: B::E, right: B::E, value: bool) -> B::E {
        self.js.release(&mut self.arena, left);
        self.js.release(&mut self.arena, right);
        self.js.boolean(&mut self.arena, value)
    }
    /// P: compile_bool_comparison, including one-sided folds preserving effects.
    /// O(1) shape decisions, plus discarded-node release and J-rule work.
    pub(super) fn primitive_bool_comparison(
        &mut self,
        cmp: Comparison,
        left: B::E,
        right: B::E,
    ) -> B::E {
        use Comparison::*;
        let l = self.bool_of(B::of(&left));
        let r = self.bool_of(B::of(&right));
        if let (Some(l), Some(r)) = (l, r) {
            return self.comparison_constant(
                left,
                right,
                cmp.cmp_int32(i32::from(l), i32::from(r)),
            );
        }
        let fold = if l == Some(true) || r == Some(false) {
            match cmp {
                Lt => Some(false),
                Ge => Some(true),
                _ => None,
            }
        } else if r == Some(true) || l == Some(false) {
            match cmp {
                Le => Some(true),
                Gt => Some(false),
                _ => None,
            }
        } else {
            None
        };
        if let Some(value) = fold {
            let kept = if l.is_some() {
                self.js.release(&mut self.arena, left);
                right
            } else {
                self.js.release(&mut self.arena, right);
                left
            };
            let value = self.js.boolean(&mut self.arena, value);
            return self.js.seq_rule(&mut self.arena, kept, value);
        }
        self.js
            .bin(&mut self.arena, comparison_op(cmp, false), left, right)
    }
    /// O(1): whether `r` is `compare(l, r)` of a runtime module: a call of
    /// three operands whose callee is the member `compare` of a module of
    /// the runtime.
    fn runtime_compare<'r>(&'r self, r: B::Ref<'r>) -> bool {
        if self.js.kind(&self.arena, r) != Kind::Call || self.js.arity(&self.arena, r) != 3 {
            return false;
        }
        let callee = self.js.operand(&self.arena, r, 0);
        matches!(
            self.js.qualified_of(&self.arena, callee),
            Some((module, Some(member)))
                if matches!(self.arena.pools.j_modules[module.index()].kind, crate::js_ir::Kind::Runtime)
                    && self.arena.text(member) == "compare"
        )
    }
    /// P: compile_int_comparison; compare-call stripping consumes shells once.
    /// O(compare-call spine length + discarded nodes), plus J-rule work.
    pub(super) fn primitive_int_comparison(
        &mut self,
        cmp: Comparison,
        mut left: B::E,
        mut right: B::E,
    ) -> B::E {
        use Comparison::*;
        loop {
            self.primitive_steps += 1;
            let r = self.js.int(&self.arena, B::of(&right));
            if let (Some(l), Some(r)) = (self.js.int(&self.arena, B::of(&left)), r) {
                return self.comparison_constant(left, right, cmp.cmp_int32(l, r));
            }
            if r != Some(0) || !self.runtime_compare(B::of(&left)) {
                break;
            }
            self.js.release(&mut self.arena, right);
            self.js.unpack_rev(&mut self.arena, left);
            let callee = self.js.pop();
            self.js.release(&mut self.arena, callee);
            left = self.js.pop();
            right = self.js.pop();
        }
        let kinds = (
            self.js.kind(&self.arena, B::of(&left)),
            self.js.kind(&self.arena, B::of(&right)),
        );
        let optional_undefined = matches!(
            kinds,
            (Kind::Optional, Kind::Undefined) | (Kind::Undefined, Kind::Optional)
        );
        let block_number = matches!(
            kinds,
            (Kind::BlockLit, Kind::Number) | (Kind::Number, Kind::BlockLit)
        );
        if (optional_undefined && matches!(cmp, Eq | Neq) || block_number && cmp == Neq)
            && self.js.has(&self.arena, B::of(&left), flag::STRICT)
            && self.js.has(&self.arena, B::of(&right), flag::STRICT)
        {
            return self.comparison_constant(left, right, cmp == Neq);
        }
        match cmp {
            Eq => self.js.int_eq(&mut self.arena, left, right),
            Neq => self
                .js
                .bin_plain(&mut self.arena, BinOp::NotEqEq, left, right),
            _ => self
                .js
                .bin(&mut self.arena, comparison_op(cmp, false), left, right),
        }
    }
    /// P: compile_string_comparison / compile_bigint_comparison.
    /// O(literal bytes + discarded nodes), otherwise the J-E4 constructor cost.
    pub(super) fn primitive_literal_comparison(
        &mut self,
        cmp: Comparison,
        left: B::E,
        right: B::E,
        bigint: bool,
    ) -> B::E {
        let (l, r) = (B::of(&left), B::of(&right));
        let equal = if bigint {
            self.js
                .bigint(&self.arena, l)
                .zip(self.js.bigint(&self.arena, r))
                .map(|(l, r)| {
                    l.as_bytes()[0] == r.as_bytes()[0]
                        && l[1..]
                            .chars()
                            .filter(|c| *c != '_')
                            .skip_while(|c| *c == '0')
                            .eq(r[1..]
                                .chars()
                                .filter(|c| *c != '_')
                                .skip_while(|c| *c == '0'))
                })
        } else {
            self.js
                .text(&self.arena, l)
                .zip(self.js.text(&self.arena, r))
                .map(|(l, r)| l == r)
        };
        if let Some(equal) = equal {
            if matches!(cmp, Comparison::Eq | Comparison::Neq) {
                return self.comparison_constant(left, right, equal != (cmp == Comparison::Neq));
            }
        }
        self.js
            .bin(&mut self.arena, comparison_op(cmp, false), left, right)
    }
    /// P: compile_object_comparison. Only nullish equality bypasses the runtime.
    /// O(1) shape decisions, then J-M2 or runtime-constructor work.
    pub(super) fn primitive_object_comparison(
        &mut self,
        cmp: Comparison,
        left: B::E,
        right: B::E,
    ) -> B::E {
        use Comparison::*;
        if matches!(cmp, Eq | Neq)
            && [&left, &right].into_iter().any(|n| {
                matches!(
                    self.js.kind(&self.arena, B::of(n)),
                    Kind::Null | Kind::Undefined
                )
            })
        {
            return self.js.nullish_eq(&mut self.arena, cmp == Neq, left, right);
        }
        let member = match cmp {
            Eq => "equal",
            Neq => "notequal",
            Lt => "lessthan",
            Le => "lessequal",
            Gt => "greaterthan",
            Ge => "greaterequal",
        };
        B::from_node(self.primitive_runtime(
            "Primitive_object",
            member,
            &[B::node(left), B::node(right)],
        ))
    }
    /// O(1): copy a literal leaf using existing payload handles, preserving cold
    /// decoration. No generic subtree copier, hash table or variable-use repair.
    fn primitive_literal_copy(&mut self, node: B::Ref<'_>) -> B::E {
        let mut copy = self.js.copy_leaf(&mut self.arena, node);
        self.js.copy_cold(&mut self.arena, node, &mut copy);
        copy
    }

    /// P: compile_typed_min_max. Only literal leaves are copied for the test;
    /// operands that may execute code use a runtime call instead.
    /// O(1) leaf tests/copies, then J-E4/J-E7 or runtime-constructor work.
    pub(super) fn primitive_min_max(
        &mut self,
        kind: &str,
        max: bool,
        left: B::E,
        right: B::E,
    ) -> B::E {
        let (l, r) = (B::of(&left), B::of(&right));
        let literals = match kind {
            "bool" => self.bool_of(l).is_some() && self.bool_of(r).is_some(),
            "int" => self.js.int(&self.arena, l).is_some() && self.js.int(&self.arena, r).is_some(),
            "string" => {
                self.js.text(&self.arena, l).is_some() && self.js.text(&self.arena, r).is_some()
            }
            "bigint" => {
                self.js.bigint(&self.arena, l).is_some() && self.js.bigint(&self.arena, r).is_some()
            }
            "float" => self.js.is_float(&self.arena, l) && self.js.is_float(&self.arena, r),
            "object" => false,
            _ => unreachable!("comparison type"),
        };
        if literals {
            let l = self.primitive_literal_copy(B::of(&left));
            let r = self.primitive_literal_copy(B::of(&right));
            let op = comparison_op(
                if max { Comparison::Gt } else { Comparison::Lt },
                kind != "bigint",
            );
            let test = self.js.bin(&mut self.arena, op, l, r);
            self.js.cond(&mut self.arena, test, left, right)
        } else {
            B::from_node(self.primitive_runtime(
                match kind {
                    "bool" => "Primitive_bool",
                    "int" => "Primitive_int",
                    "float" => "Primitive_float",
                    "bigint" => "Primitive_bigint",
                    "string" => "Primitive_string",
                    "object" => "Primitive_object",
                    _ => unreachable!("comparison type"),
                },
                if max { "max" } else { "min" },
                &[B::node(left), B::node(right)],
            ))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lambda::{
        LamLoc, arena::LamArena, lam_constant::Constant as C, lam_primitive::Primitive as P,
    };

    fn literals() -> Vec<C> {
        vec![
            C::JsTrue,
            C::JsFalse,
            C::JsNull,
            C::JsUndefined { is_unit: false },
            C::Int {
                i: -1,
                comment: None,
            },
            C::Int {
                i: 0,
                comment: None,
            },
            C::Int {
                i: 1,
                comment: None,
            },
            C::Float("1.".into()),
            C::Float("nan".into()),
            C::String("a".into()),
            C::String("b".into()),
            C::BigInt {
                negative: false,
                value: "00_12".into(),
            },
            C::BigInt {
                negative: false,
                value: "12".into(),
            },
            C::BigInt {
                negative: true,
                value: "12".into(),
            },
            C::Some(Box::new(C::JsUndefined { is_unit: false })),
            C::Block {
                tag_info: Box::new(crate::lambda::TagInfo::Tuple),
                elements: vec![C::JsTrue],
            },
        ]
    }

    #[test]
    fn ten_thousand_compare_shells_are_consumed_once() {
        let mut a = LamArena::new();
        let mut root = a.var(Ident::new("left", 10, crate::ident::IdentFlags::NONE));
        for _ in 0..10_000 {
            let zero = a.const_(C::Int {
                i: 0,
                comment: None,
            });
            root = a.prim_raw(P::Pintorder, &[root, zero], LamLoc::NONE);
        }
        let zero = a.const_(C::Int {
            i: 0,
            comment: None,
        });
        let root = a.prim_raw(P::Pintcomp(Comparison::Lt), &[root, zero], LamLoc::NONE);
        let input = crate::bir::bridge::import_lambda(&a, root).unwrap();
        let root = input.root;
        let mut state = State::new(input);
        let result = state.probe(Cx::value(), root).unwrap();
        assert_eq!(state.source_steps, 20_003);
        assert_eq!(state.sequence_steps, 20_002);
        // Three units per two-operand primitive, and one per stripped shell
        // plus the final comparison iteration: four per nested compare.
        assert_eq!(state.primitive_steps, 40_004);
        let output = state.complete(Cx::value(), result);
        output
            .program
            .arena
            .validate(Some(output.program.root))
            .unwrap();
    }

    #[test]
    fn comparison_arms_and_literal_folds_match_legacy() {
        for cmp in [
            Comparison::Eq,
            Comparison::Neq,
            Comparison::Lt,
            Comparison::Le,
            Comparison::Gt,
            Comparison::Ge,
        ] {
            for primitive in [
                P::Pboolcomp(cmp),
                P::Pintcomp(cmp),
                P::Pfloatcomp(cmp),
                P::Pstringcomp(cmp),
                P::Pbigintcomp(cmp),
                P::Pobjcomp(cmp),
                P::Pjscomp(cmp),
            ] {
                check_pairs(primitive);
            }
        }
    }

    #[test]
    fn order_and_min_max_arms_match_legacy() {
        for primitive in [
            P::Pboolorder,
            P::Pintorder,
            P::Pfloatorder,
            P::Pstringorder,
            P::Pbigintorder,
            P::Pobjorder,
            P::Pboolmin,
            P::Pboolmax,
            P::Pintmin,
            P::Pintmax,
            P::Pfloatmin,
            P::Pfloatmax,
            P::Pstringmin,
            P::Pstringmax,
            P::Pbigintmin,
            P::Pbigintmax,
            P::Pobjmin,
            P::Pobjmax,
        ] {
            check_pairs(primitive);
        }
    }

    fn check_pairs(primitive: P) {
        let literals = literals();
        for l in 0..literals.len() + 2 {
            for r in 0..literals.len() + 2 {
                let mut a = LamArena::new();
                let mut operand = |index: usize, stamp| {
                    if let Some(value) = literals.get(index) {
                        a.const_(value.clone())
                    } else {
                        let value =
                            a.var(Ident::new("value", stamp, crate::ident::IdentFlags::NONE));
                        if index == literals.len() {
                            value
                        } else {
                            a.prim_raw(P::PinitMod, &[value], LamLoc::NONE)
                        }
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
        for primitive in [
            P::Pintorder,
            P::Pboolorder,
            P::Pstringorder,
            P::Pfloatorder,
            P::Pbigintorder,
            P::Pobjorder,
        ] {
            for cmp in [
                Comparison::Eq,
                Comparison::Neq,
                Comparison::Lt,
                Comparison::Le,
                Comparison::Gt,
                Comparison::Ge,
            ] {
                let mut a = LamArena::new();
                let l = a.var(Ident::new("left", 10, crate::ident::IdentFlags::NONE));
                let r = a.var(Ident::new("right", 11, crate::ident::IdentFlags::NONE));
                let order = a.prim_raw(primitive.clone(), &[l, r], LamLoc::NONE);
                let zero = a.const_(C::Int {
                    i: 0,
                    comment: None,
                });
                let root = a.prim_raw(P::Pintcomp(cmp), &[order, zero], LamLoc::NONE);
                super::super::oracle_tests::compare(a, root);
            }
        }
    }
}
