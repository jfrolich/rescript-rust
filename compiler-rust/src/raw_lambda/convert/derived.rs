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
    use crate::binary_ast::derive::plan::{SkeletonNode, Span};
    use crate::parser::ast::Attributes;
    use crate::parser::{Parser, module};
    use crate::raw_lambda::RawArena;
    use crate::raw_lambda::print::RawLambdaPrinter;
    use crate::binary_ast::derive::fixtures::{DECLARATIONS, derive_source};
    use crate::types::derived::tests::type_context;
    use crate::types::typecore::TypeCheckContext;
    use crate::types::{initial_env, typemod};

    /// The printed raw Lambda of a program whose derived items are planned
    /// or syntax, with its stamps renumbered in order of first appearance,
    /// and the number of items lowered from plans.
    fn raw_lambda(source: &str, plans: bool) -> (String, usize) {
        let (parser, structure) = derive_source(source, plans);
        let arena = parser.arena();
        let type_ctx = type_context();
        let mut tctx = TypeCheckContext::new(&type_ctx, arena);
        let env = initial_env(&type_ctx);
        let (typed, _) = typemod::type_structure(&mut tctx, &env, arena, &structure).unwrap();
        let planned = tctx.typed.derived.discharged();
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
            let (planned, items) = raw_lambda(source, true);
            let (general, none) = raw_lambda(source, false);
            assert_eq!(items, source.matches("type ").count());
            assert_eq!(none, 0);
            assert!(planned.contains("_decode") || planned.contains("_encode"), "{planned}");
            assert_eq!(planned, general, "{source}");
        }
    }

    /// The printed raw Lambda of the value `probe` of `source`, compiled
    /// after the record library by the converter of typed trees, with its
    /// stamps renumbered in order of first appearance.
    fn probe(source: &str) -> String {
        let (parser, structure) =
            crate::binary_ast::derive::fixtures::frontend_source(source, false);
        let arena = parser.arena();
        let type_ctx = type_context();
        let mut tctx = TypeCheckContext::new(&type_ctx, arena);
        let env = initial_env(&type_ctx);
        let (typed, _) = typemod::type_structure(&mut tctx, &env, arena, &structure)
            .unwrap_or_else(|error| panic!("{error:?}"));
        let rb = RawArena::new();
        let mut converter = RawLambdaConverter::new(arena, &tctx.typed, &type_ctx, &env, &rb);
        let lam = converter.convert_structure(&typed);
        let printed = RawLambdaPrinter::new(&rb.get(), lam).to_string();
        let at = printed.find(" probe/").expect("a value named probe") + 1;
        let end = printed.rfind("\n  (makeblock module/exports").expect("the unit's exports");
        // The term is printed as the last binding of a `let`: its closing
        // parenthesis belongs to the list of bindings.
        let term = printed[at..end].strip_suffix(')').expect("the end of the bindings");
        renumber(term)
    }

    /// The raw Lambda the converter of typed trees makes today for each form
    /// the body of a record codec is made of (`records_generate_encoder`,
    /// `records_generate_flat_decoder_expr`). Lowering a plan must give
    /// these terms.
    #[test]
    fn the_forms_of_a_record_body() {
        let record = "type r = {x: int, y?: string}\n";
        for (source, lambda) in [
            // Field access.
            ("let probe = (v: r) => v.x", "probe/0 = (function v/1 (field:x/2 v/1))"),
            // Record construction with an optional field.
            (
                "let probe = (a, b): r => {x: a, y: ?b}",
                "probe/0 = (function a/1 b/2 (makeblock [x;y] a/1 b/2))",
            ),
            // `Some(e)` where `e : JSON.t`: the payload cannot be `undefined`.
            (
                "let probe = (e: JSON.t) => Some(e)",
                "probe/0 = (function e/1 (makeblock some_not_nested e/1))",
            ),
            // `Ok(None)` is a constant block.
            (
                "let probe = (): result<option<int>, string> => Ok(None)",
                "probe/0 = (function param/1 [Ok: shape_none])",
            ),
            // `JSON.Object(d)` is the identity: `JSON.t` is untagged.
            ("let probe = (d): JSON.t => JSON.Object(d)", "probe/0 = (function d/1 d/1)"),
            // `Dict.fromArray` and `Dict.get` are externals.
            (
                "let probe = e => Dict.fromArray(e)",
                "probe/0 = (function e/1 (Object.fromEntries e/1))",
            ),
            ("let probe = (d, k) => Dict.get(d, k)", "probe/0 = (function d/1 k/2 ( d/1 k/2))"),
            // `Spice.error` with and without its optional `~path`.
            (
                "let probe = (p, m, v) => Spice.error(~path=p, m, v)",
                "probe/0 =
     (function p/1 m/2 v/3
       (apply (field:error/4 Spice/5) (makeblock some_not_nested p/1)
         m/2 v/3))",
            ),
            (
                "let probe = (m, v) => Spice.error(m, v)",
                "probe/0 =
     (function m/1 v/2
       (apply (field:error/3 Spice/4) shape_none m/1 v/2))",
            ),
            // String concatenation is a primitive.
            (
                "let probe = (a, b) => a ++ b",
                "probe/0 = (function a/1 b/2 (string.concat a/1 b/2))",
            ),
            // The match on `JSON.t` of a decoder.
            (JSON_MATCH, JSON_MATCH_LAMBDA),
            // The match on the result of a field's decoder.
            (RESULT_MATCH, RESULT_MATCH_LAMBDA),
        ] {
            let source = format!("{record}{source}");
            assert_eq!(probe(&source), lambda, "{source}");
        }
    }

    const JSON_MATCH: &str = "let probe = (v, e1, e2) =>
  switch (v: JSON.t) {
  | JSON.Object(dict) => e1(dict)
  | _ => e2
  }";
    const JSON_MATCH_LAMBDA: &str = "probe/0 =
     (function v/1 e1/2 e2/3
       (catch
         (switch v/1
          case constructor \"Object\":
           (let (dict/4 =a v/1) (apply e1/2 dict/4))
          default: (exit 1))
        with (1) e2/3))";
    const RESULT_MATCH: &str = "let probe = (r, e1, e2) =>
  switch r {
  | Ok(x) => e1(x)
  | Error(e: Spice.decodeError) => e2(e)
  }";
    const RESULT_MATCH_LAMBDA: &str = "probe/0 =
     (function r/1 e1/2 e2/3
       (switch* r/1
        case constructor \"Ok\":
         (let (x/4 =a (field:var/5 r/1)) (apply e1/2 x/4))
        case constructor \"Error\":
         (let (e/6 =a (field:var/5 r/1)) (apply e2/3 e/6))))";

    /// A printed term without its stamps and its layout.
    fn shape(printed: &str) -> String {
        let mut out = String::new();
        let mut rest = printed;
        while let Some(at) = rest.find('/') {
            out.push_str(&rest[..at]);
            rest = rest[at + 1..].trim_start_matches(|c: char| c.is_ascii_digit());
        }
        out.push_str(rest);
        out.split_whitespace().collect::<Vec<_>>().join(" ")
    }

    /// The match of `scrutinee` against `cases`, each a constructor of
    /// `open_module` with the variable its argument binds, or a wildcard,
    /// compiled by `compile_matching` from patterns that are built in its
    /// overlay from the constructors' descriptions: no typed pattern and no
    /// typed expression. A case with a binder applies `e<n>` to it; one
    /// without is `e<n>`.
    fn match_from_descriptions(
        open_module: &str,
        scrutinee: &str,
        cases: &[Option<(&str, &str)>],
    ) -> String {
        use crate::parse_arena::Located;
        use crate::raw_lambda::matching::{CaseAction, MatchEnv, PatArena, PatStore, compile_matching};
        use crate::types::typedtree::{Partial, Pattern, PatternDesc};
        let (mut parser, structure) = crate::binary_ast::derive::fixtures::frontend_source(
            &format!("{open_module}\nlet used = 0"),
            false,
        );
        let lids: Vec<_> = cases
            .iter()
            .map(|case| case.map(|(constructor, _)| parser.arena_mut().push_lident(constructor)))
            .collect();
        crate::types::typecore::prepare_typecheck_arena(parser.arena_mut());
        let arena = parser.arena();
        let type_ctx = type_context();
        let mut tctx = TypeCheckContext::new(&type_ctx, arena);
        let env = initial_env(&type_ctx);
        let (_, final_env) = typemod::type_structure(&mut tctx, &env, arena, &structure).unwrap();
        let env_ref = type_ctx.store_typed_env(&final_env);
        let rb = RawArena::new();
        let mut conv = RawLambdaConverter::new(arena, &tctx.typed, &type_ctx, &env, &rb);
        let scrutinee = conv.fresh_ident(scrutinee);

        let store = PatStore::default();
        let pa = PatArena::new(conv.ta, &store);
        let none = crate::parse_arena::LocIdx::none();
        let mut pat_act_list = Vec::new();
        let mut scrutinee_type = None;
        for (i, (case, lid)) in cases.iter().zip(&lids).enumerate() {
            let action = conv.fresh_ident(&format!("e{}", i + 1));
            let Some((constructor, binder)) = case else {
                let any = pa.alloc(Pattern::new(
                    PatternDesc::Tpat_any,
                    none,
                    scrutinee_type.expect("a wildcard follows a constructor"),
                    env_ref,
                ));
                pat_act_list.push((any, CaseAction::unguarded(rb.var(action))));
                continue;
            };
            let description = std::sync::Arc::new(
                final_env.find_constructor(*constructor).expect("the constructor").clone(),
            );
            scrutinee_type = Some(description.cstr_res);
            let binder = conv.fresh_ident(binder);
            // The matcher reads a variable's identifier, never its name.
            let variable = pa.push(Pattern::new(
                PatternDesc::Tpat_var(binder, Located::new(String::new(), none)),
                none,
                description.cstr_args[0],
                env_ref,
            ));
            let pattern = pa.alloc(Pattern::new(
                PatternDesc::Tpat_construct(
                    Located::new(lid.expect("a constructor has a name"), none),
                    description.clone(),
                    pa.push_list([variable]),
                ),
                none,
                description.cstr_res,
                env_ref,
            ));
            let body = rb.apply(
                rb.var(action),
                &[rb.var(binder)],
                crate::lambda::ApInfo {
                    loc: LamLoc::NONE,
                    status: crate::lambda::ApplyStatus::Na,
                },
            );
            pat_act_list.push((pattern, CaseAction::unguarded(body)));
        }
        let loc_arena = crate::raw_lambda::loc::LocArena::new(conv.arena, &conv.lam_locs, conv.b);
        let lam = compile_matching(
            MatchEnv {
                ctx_ref: conv.type_ctx,
                pa: &pa,
                arena: &loc_arena,
                next_raise_count: &mut conv.next_static_raise,
            },
            || unreachable!("both matches are total"),
            rb.var(scrutinee),
            pat_act_list,
            Partial::Total,
        );
        shape(&RawLambdaPrinter::new(&rb.get(), lam).to_string())
    }

    /// The decision of the design (`DERIVED_CODECS.md`, Q2): both matches of
    /// a record decoder are produced by `compile_matching` from patterns
    /// allocated in its `PatArena` from the constructor descriptions, and
    /// they are the terms the converter of typed trees makes.
    #[test]
    fn the_matches_compile_from_constructor_descriptions() {
        let json = match_from_descriptions("open JSON", "v", &[Some(("Object", "dict")), None]);
        assert_eq!(
            json,
            "(catch (switch v case constructor \"Object\": (let (dict =a v) (apply e1 dict)) \
             default: (exit 1)) with (1) e2)"
        );
        assert!(shape(JSON_MATCH_LAMBDA).contains(&json));

        let result = match_from_descriptions("", "r", &[Some(("Ok", "x")), Some(("Error", "e"))]);
        assert_eq!(
            result,
            "(switch* r case constructor \"Ok\": (let (x =a (field:var r)) (apply e1 x)) \
             case constructor \"Error\": (let (e =a (field:var r)) (apply e2 e)))"
        );
        assert!(shape(RESULT_MATCH_LAMBDA).contains(&result));
    }

    /// A planned item inside a module expression lowers to the raw Lambda
    /// of its general form.
    #[test]
    fn a_nested_plan_lowers_to_the_lambda_of_the_general_form() {
        for (source, items) in crate::binary_ast::derive::fixtures::NESTED {
            let (planned, lowered) = raw_lambda(source, true);
            let (general, none) = raw_lambda(source, false);
            assert_eq!(lowered, items, "{source}");
            assert_eq!(none, 0);
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
        let item = plans.push_item(first);
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
