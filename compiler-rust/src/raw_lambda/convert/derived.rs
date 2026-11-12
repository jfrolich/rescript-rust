//! Lowering of a discharged derived item (`Tstr_derived`) to raw Lambda.
//!
//! The item has no typed expressions: its bindings are lowered from the body
//! nodes of its plan and from what the checker recorded for its obligations
//! (`types::derived`). The result is the term the converter makes for the
//! item's general form: applications go through the converter's own
//! `transl_apply_of`, identifiers through its path translation.
//! (`compiler-rust/docs/DERIVED_CODECS.md`, "The cheapest sound path".)

use smallvec::SmallVec;

use super::{ArgLowering, RawLambdaConverter, SrcLoc};
use crate::binary_ast::derive::plan::{
    Binding, BodyIdx, BodyNode, DerivedIdx, ExprLoc, Obligation, Plans,
};
use crate::ident::Ident;
use crate::lambda::lam_compat::LetKind;
use crate::lambda::{FunctionAttribute, InlineAttribute, LamLoc};
use crate::raw_lambda::RawLambda;
use crate::raw_lambda::builder::RawLambdaBuilder;
use crate::types::derived::DerivedTable;
use crate::types::env::Env;
use crate::types::type_expr::{TypeDesc, TypeExprRef};

/// The steps of a lowering, for the test that proves its cost. The converter
/// passes `()`, whose method is empty.
pub(super) trait Steps {
    /// A body node is lowered.
    fn node(&mut self);
}

impl Steps for () {
    #[inline(always)]
    fn node(&mut self) {}
}

/// What lowering the bodies of one item reads and keeps.
struct Lowering<'a, S> {
    plans: &'a Plans,
    table: &'a DerivedTable,
    /// The environment the item was checked in.
    env: &'a Env,
    /// The location the generator gives every function and application.
    loc: LamLoc,
    /// The parameters of the enclosing functions, outermost first.
    locals: SmallVec<[Ident; 4]>,
    steps: &'a mut S,
}

/// Lower the bindings of a discharged item around `body`, the term of the
/// items that follow it: `let b_1 = e_1 in ... let b_n = e_n in body`
/// (translcore.ml `transl_let`, a non-recursive group of variables).
/// Cost: O(body nodes of the item): each node is visited once and makes a
/// fixed number of terms (a local one, a free value its path, a function
/// one, an application one, or, when it is partial, one per parameter it
/// leaves and per term it protects). No heap allocation per node: the
/// arguments of an application and the values of the item are gathered
/// inline, up to four.
pub(super) fn lower<B: RawLambdaBuilder>(
    conv: &mut RawLambdaConverter<'_, B>,
    idx: DerivedIdx,
    body: RawLambda,
    steps: &mut impl Steps,
) -> RawLambda {
    let arena = conv.arena;
    let plans = arena.plans();
    let table = &conv.ta.derived;
    let bindings = plans.bindings(plans.item(idx));
    let mut bound = table.bound(idx).peekable();
    let Some(first) = bound.peek() else {
        return body;
    };
    let env = conv
        .type_ctx
        .get_typed_env(first.env)
        .expect("the environment of a discharged item is stored");
    let dummy = arena.dummy_loc();
    let mut lowering = Lowering {
        plans,
        table,
        env: &env,
        loc: conv.lam_loc(dummy),
        locals: SmallVec::new(),
        steps,
    };
    let mut values: SmallVec<[(Ident, RawLambda); 4]> = SmallVec::new();
    for (binding, bound) in bindings.iter().zip(bound) {
        let mut value = conv.with_warning_scope(&binding.attributes, |conv| {
            lowering.binding(conv, binding, bound.ty)
        });
        // translcore.ml `transl_let` applies the binding's inline attribute.
        let inline = conv.get_inline_attribute_from(&binding.attributes);
        value = conv.apply_inline_attribute_raw(value, dummy, inline);
        values.push((bound.ident, value));
    }
    values.into_iter().rev().fold(body, |body, (id, value)| {
        conv.b.let_(LetKind::Strict, id, value, body)
    })
}

impl<S: Steps> Lowering<'_, S> {
    /// The value of a binding: the function at the root of its body, whose
    /// type is the binding's (translcore.ml `transl_function`).
    /// Cost: O(body nodes of the binding).
    fn binding<B: RawLambdaBuilder>(
        &mut self,
        conv: &mut RawLambdaConverter<'_, B>,
        binding: &Binding,
        ty: TypeExprRef,
    ) -> RawLambda {
        self.steps.node();
        let BodyNode::Function { param, body } = self.plans.body(binding.body) else {
            unreachable!("the body of a planned binding is a function")
        };
        let result = match &*conv.type_ctx.get_desc(conv.type_ctx.repr(ty)) {
            TypeDesc::Tarrow { ret, .. } => *ret,
            _ => unreachable!("a discharged binding has a function type"),
        };
        // `transl_function` tests the result type before it translates the
        // body (translcore.ml:1395-1409).
        let return_unit = conv.is_base_type_with_env(result, "unit", self.env);
        let param = conv.fresh_ident(conv.arena.get_string(param));
        self.locals.push(param);
        let (body, _) = self.node(conv, body);
        self.locals.pop();
        conv.b.function_(
            1,
            &[param],
            body,
            FunctionAttribute {
                return_unit,
                async_: false,
                directive: None,
                inline: InlineAttribute::Default,
                // The parameter is a variable (translcore.ml:1015-1022).
                one_unit_arg: false,
                is_a_functor: false,
            },
            self.loc,
        )
    }

    /// Lower a body node: its term, and, for a partial application, the
    /// number of parameters its result still takes.
    /// Cost: O(nodes under `idx`); recursion depth is the body's depth.
    fn node<B: RawLambdaBuilder>(
        &mut self,
        conv: &mut RawLambdaConverter<'_, B>,
        idx: BodyIdx,
    ) -> (RawLambda, Option<i32>) {
        self.steps.node();
        match self.plans.body(idx) {
            BodyNode::Local(level) => (conv.b.var(self.locals[level as usize]), None),
            BodyNode::Free(obligation) => {
                let Obligation::Value {
                    name_loc, expr_loc, ..
                } = self.plans.obligation(obligation)
                else {
                    unreachable!("a body node names a value obligation")
                };
                let loc = match expr_loc {
                    ExprLoc::OfName => name_loc,
                    ExprLoc::Dummy => conv.arena.dummy_loc(),
                };
                let path = self.table.resolved(obligation).path();
                let lam = conv.translate_value_path_raw_in_env(self.env, &path, SrcLoc::from(loc));
                (lam, None)
            }
            BodyNode::Apply {
                funct,
                args,
                len,
                partial,
            } => {
                let (funct_lam, remaining) = self.node(conv, funct);
                // translcore.ml `Texp_apply`: a partial application of a
                // function that takes more parameters makes a function of
                // the rest.
                let arity = if partial {
                    let arity = match self.plans.body(funct) {
                        BodyNode::Free(obligation) => conv.get_function_arity_from_type(
                            self.env,
                            self.table.resolved(obligation).instance(),
                        ),
                        BodyNode::Apply { .. } => remaining,
                        // A plan applies no parameter and no function
                        // partially; neither has a recorded type.
                        BodyNode::Local(_) | BodyNode::Function { .. } => None,
                    };
                    arity.filter(|arity| *arity > i32::from(len))
                } else {
                    None
                };
                let args = self.plans.apply_args(args, len);
                let loc = self.loc;
                let lam = conv.transl_apply_of(funct_lam, args, loc, arity, self);
                (lam, arity.map(|arity| arity - i32::from(len)))
            }
            BodyNode::Function { .. } => {
                unreachable!("a plan's only function is the root of a binding's body")
            }
        }
    }
}

impl<B: RawLambdaBuilder, S: Steps> ArgLowering<B, BodyIdx> for Lowering<'_, S> {
    #[inline(always)]
    fn supplied(&self, _: &BodyIdx) -> bool {
        true
    }

    #[inline(always)]
    fn optional(&self, _: &BodyIdx) -> bool {
        false
    }

    #[inline(always)]
    fn lower(&mut self, conv: &mut RawLambdaConverter<'_, B>, arg: &BodyIdx) -> RawLambda {
        self.node(conv, *arg).0
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::binary_ast::derive::Scope;
    use crate::binary_ast::derive::plan::{SkeletonNode, Span};
    use crate::parse_arena::VbList;
    use crate::parser::ast::Attributes;
    use crate::parser::{Parser, module};
    use crate::raw_lambda::RawArena;
    use crate::raw_lambda::print::RawLambdaPrinter;
    use crate::types::derived::tests::{DECLARATIONS, derive_source, type_context};
    use crate::types::typecore::TypeCheckContext;
    use crate::types::typedtree::StructureItemDesc;
    use crate::types::{initial_env, typemod};

    /// The printed raw Lambda of a program whose derived items are planned
    /// (`TopLevel`) or general (`Nested`), with its stamps renumbered in
    /// order of first appearance, and the number of items lowered from plans.
    fn raw_lambda(source: &str, scope: Scope) -> (String, usize) {
        let (parser, structure) = derive_source(source, scope);
        let arena = parser.arena();
        let type_ctx = type_context();
        let mut tctx = TypeCheckContext::new(&type_ctx, arena);
        let env = initial_env(&type_ctx);
        let (typed, _) = typemod::type_structure(&mut tctx, &env, arena, &structure).unwrap();
        let planned = tctx
            .typed
            .structure_items(typed.str_items)
            .iter()
            .filter(|item| matches!(item.str_desc, StructureItemDesc::Tstr_derived(_)))
            .count();
        let rb = RawArena::new();
        let mut converter = RawLambdaConverter::new(arena, &tctx.typed, &type_ctx, &env, &rb);
        let lam = converter.convert_structure(&typed);
        let printed = RawLambdaPrinter::new(&rb.get(), lam).to_string();
        (renumber(&printed), planned)
    }

    /// Replace each `/<stamp>` by the order of the stamp's first appearance.
    fn renumber(printed: &str) -> String {
        let mut seen: Vec<&str> = Vec::new();
        let mut out = String::new();
        let mut rest = printed;
        while let Some(at) = rest.find('/') {
            let digits = rest[at + 1..]
                .find(|c: char| !c.is_ascii_digit())
                .unwrap_or(rest.len() - at - 1);
            out.push_str(&rest[..=at]);
            let stamp = &rest[at + 1..at + 1 + digits];
            if !stamp.is_empty() {
                let order = seen.iter().position(|s| *s == stamp).unwrap_or_else(|| {
                    seen.push(stamp);
                    seen.len() - 1
                });
                out.push_str(&order.to_string());
            }
            rest = &rest[at + 1 + digits..];
        }
        out + rest
    }

    /// A planned item lowers to the raw Lambda of its general form.
    #[test]
    fn a_plan_lowers_to_the_lambda_of_the_general_form() {
        for source in DECLARATIONS {
            let (planned, items) = raw_lambda(source, Scope::TopLevel);
            let (general, none) = raw_lambda(source, Scope::Nested);
            assert_eq!(items, source.matches("type ").count());
            assert_eq!(none, 0);
            assert!(planned.contains("_decode") || planned.contains("_encode"), "{planned}");
            assert_eq!(planned, general, "{source}");
        }
    }

    struct Counted(usize);

    impl Steps for Counted {
        fn node(&mut self) {
            self.0 += 1;
        }
    }

    /// A body of 10,000 nodes is lowered in 10,000 steps that make 10,000
    /// terms: one per node.
    #[test]
    fn ten_thousand_body_nodes_take_ten_thousand_steps() {
        const ARGS: u32 = 9_997;
        let mut parser = Parser::new("Test.res", "let f = (x: int) => x");
        let structure = module::parse_structure(&mut parser);
        assert!(!parser.has_errors());
        // let derived = v => f(v, ..., v)
        let arena = parser.arena_mut();
        let first = arena.plans().next_binding();
        let f = arena.intern_string("f");
        let f = arena.push_lident_from_idx(f);
        let name_loc = arena.none_loc();
        let name = arena.intern_string("derived");
        let param = arena.intern_string("v");
        let plans = arena.plans_mut();
        let skeleton = plans.push_skeleton(SkeletonNode::Var(0));
        let obligation = plans.push_obligation(Obligation::Value {
            name: f,
            name_loc,
            skeleton,
            expr_loc: ExprLoc::Dummy,
            called: true,
        });
        let funct = plans.push_body(BodyNode::Free(obligation));
        let args: Vec<BodyIdx> = (0..ARGS)
            .map(|_| plans.push_body(BodyNode::Local(0)))
            .collect();
        let applied = plans.push_apply(funct, &args, false);
        let body = plans.push_body(BodyNode::Function {
            param,
            body: applied,
        });
        assert_eq!(body.0 - funct.0 + 1, 10_000);
        plans.push_binding(Binding {
            name,
            attributes: Attributes::new(),
            obligations: Span {
                start: obligation.0,
                len: 1,
            },
            body,
            vars: 1,
            result_of: obligation,
            applied: 0,
        });
        let item = plans.push_item(first, VbList::EMPTY);
        crate::types::typecore::prepare_typecheck_arena(parser.arena_mut());
        let arena = parser.arena();
        let type_ctx = type_context();
        let mut tctx = TypeCheckContext::new(&type_ctx, arena);
        let env = initial_env(&type_ctx);
        let (_, env) = typemod::type_structure(&mut tctx, &env, arena, &structure).unwrap();
        crate::types::derived::discharge(&mut tctx, &env, item).unwrap();

        let rb = RawArena::new();
        let mut converter = RawLambdaConverter::new(arena, &tctx.typed, &type_ctx, &env, &rb);
        let tail = rb.unit();
        let before = rb.get().node_count();
        let mut steps = Counted(0);
        let lam = lower(&mut converter, item, tail, &mut steps);
        assert_eq!(steps.0, 10_000);
        // One term per body node, and the `let` of the binding.
        assert_eq!(rb.get().node_count() - before, 10_001);
        let printed = RawLambdaPrinter::new(&rb.get(), lam).to_string();
        assert!(printed.starts_with("(let\n  (derived/") || printed.starts_with("(let (derived/"), "{}", &printed[..80]);
    }
}
