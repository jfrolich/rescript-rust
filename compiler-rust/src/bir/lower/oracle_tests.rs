use super::*;
use crate::bir::{bridge, bridge_j};
use crate::ident::IdentFlags;
use crate::js_ir::arena::{JsDepsProgram, JsProgram, StmtKind};
use crate::lambda::arena::{Lam, LamArena};
use crate::lambda::lam_compile::LambdaCompiler;
use crate::lambda::lam_constant::{Constant as C, PointerInfo};

pub(super) fn compare(arena: LamArena, root: Lam) {
    compare_with_resolver(arena, root, None);
}

pub(super) fn compare_with_resolver(arena: LamArena, root: Lam, resolver: Option<&crate::js_ir::ModulePathResolver>) {
    compare_with_options(arena, root, resolver, true);
}

pub(super) fn compare_with_checks(arena: LamArena, root: Lam, checks: bool) {
    compare_with_options(arena, root, None, checks);
}

fn compare_with_options(mut arena: LamArena, root: Lam, resolver: Option<&crate::js_ir::ModulePathResolver>, checks: bool) {
    let target = Ident::new("result", arena.ident_stamp_bound() + 1, IdentFlags::NONE);
    for direct in [false, true] {
        for context in 0..5 {
            let mut input = bridge::import_lambda(&arena, root).unwrap();
            let var = input
                .arena
                .new_var_id(target.name_atom(), target.stamp() as u32);
            input.idents.push(target);
            let cx = match context {
                0 => Cx::value(),
                1 => Cx::effect(),
                2 => Cx::declare(LetKind::Strict, var),
                3 => Cx::assign(var),
                4 => Cx::returning(),
                _ => unreachable!(),
            };
            let source_root = input.root;
            let mut state = State::new(input);
            state.direct = direct;
            state.check_div_by_zero = checks;
            state.resolver = resolver.cloned();
            let probed = state.probe(cx, source_root).unwrap();
            let lowered = state.complete(cx, probed);
            lowered
                .program
                .arena
                .validate(Some(lowered.program.root))
                .unwrap();
            let actual = bridge_j::export_js(&lowered.program).unwrap();
            let mut counts = crate::lambda::js_pass_tailcall_inline::UseCounts::default();
            crate::js_ir::walk::walk_block(&mut counts, &actual.program.arena, &actual.program.block);
            let scope = lowered.program.arena.js_scope.as_ref().unwrap();
            for (index, row) in scope.uses.iter().enumerate() {
                let ident = lowered.program.idents[index];
                assert_eq!(row.built as usize, counts.counts.get(&ident).copied().unwrap_or(0),
                    "built occurrences for {ident:?}, context {cx:?}");
                assert_eq!(row.remaining, row.built);
            }
            let mut compiler = LambdaCompiler::new();
            compiler.module_path_resolver = resolver.cloned();
            compiler.check_div_by_zero = checks;
            let compiled = compiler.bir_lower_oracle(&mut arena, root, cx.cont, target);
            use crate::lambda::lam_compile::OutputFinished;
            let expected_finished = match compiled.finished {
                OutputFinished::True => Finished::True,
                OutputFinished::False => Finished::False,
                OutputFinished::Dummy => Finished::Dummy,
            };
            assert_eq!(lowered.finished, expected_finished);
            let mut block = compiled.prelude;
            block.push(compiler.j.stmt(StmtKind::Exp(compiled.expr)));
            let expected = JsDepsProgram {
                program: JsProgram::new_in(block, vec![], compiler.j),
                modules: vec![],
                side_effect: None,
            };
            let print = |p: &JsDepsProgram| {
                crate::js_ir::print_deps_program_with_directives_and_options(
                    p,
                    None,
                    &[],
                    false,
                    false,
                    false,
                )
            };
            assert_eq!(print(&actual), print(&expected), "context {cx:?}");
        }
    }
}

#[test]
fn var_and_global_in_all_five_contexts() {
    let id = Ident::new("value", 10, IdentFlags::NONE);
    let mut a = LamArena::new();
    let root = a.var(id);
    compare(a, root);
    let mut a = LamArena::new();
    let root = a.global_module(Ident::create_persistent("Module"));
    compare(a, root);
}

#[test]
fn constants_in_all_five_contexts() {
    let constants = vec![
        C::JsNull,
        C::JsUndefined { is_unit: false },
        C::JsUndefined { is_unit: true },
        C::JsTrue,
        C::JsFalse,
        C::Int {
            i: i32::MIN,
            comment: None,
        },
        C::Int {
            i: 0,
            comment: Some(Box::new(PointerInfo::AssertFalse)),
        },
        C::NativeInt {
            i: i64::MAX,
            comment: None,
        },
        C::Char(65),
        C::Float("-0.".into()),
        C::Float("1e999".into()),
        C::BigInt {
            negative: true,
            value: "123456789012345678901".into(),
        },
        C::String("a\n\"b".into()),
        C::ImmString("immutable".into()),
        C::Pointer("pointer".into()),
        C::Some(Box::new(C::JsUndefined { is_unit: true })),
        C::Some(Box::new(C::Some(Box::new(C::ModuleAlias)))),
        C::Some(Box::new(C::Int {
            i: 7,
            comment: None,
        })),
        C::Block {
            tag_info: Box::new(crate::lambda::lam_tag_info::TagInfo::Tuple),
            elements: vec![C::JsTrue, C::JsNull],
        },
        C::ModuleAlias,
    ];
    for constant in constants {
        let mut a = LamArena::new();
        let root = a.const_(constant);
        compare(a, root);
    }
}

#[test]
fn decorated_and_nominal_constructors_in_all_contexts() {
    use crate::lambda::lam_constant::{ConstructorRuntimeTag as R, ConstructorTag};
    use crate::types::{VariantLiteralTag as L, VariantTag};
    for literal in [
        L::Int(9),
        L::String("tag".into()),
        L::Float("1.25".into()),
        L::BigInt("-123n".into()),
        L::Bool(false),
        L::Null,
        L::Undefined,
    ] {
        let mut a = LamArena::new();
        let root = a.const_(C::Constructor(VariantTag {
            name: "Name".into(),
            literal,
        }));
        compare(a, root);
    }
    for runtime_tag in [
        None,
        Some(R::Int(i64::MAX)),
        Some(R::String("text".into())),
        Some(R::Float("2.".into())),
        Some(R::BigInt("123".into())),
        Some(R::Bool(true)),
        Some(R::Null),
        Some(R::Undefined),
    ] {
        let mut a = LamArena::new();
        let root = a.const_(C::Int {
            i: 0,
            comment: Some(Box::new(PointerInfo::Constructor(ConstructorTag {
                name: "[]".into(),
                const_: 1,
                non_const: 0,
                runtime_tag,
            }))),
        });
        compare(a, root);
    }
}

#[test]
fn strict_and_delay_safe_flags_use_variable_facts() {
    let mut a = LamArena::new();
    let id = Ident::new("assigned", 1, IdentFlags::NONE);
    let root = a.var(id);
    let mut input = bridge::import_lambda(&a, root).unwrap();
    let source_root = input.root;
    input.arena.vars.flags[0].0 |= crate::bir::VarFlags::ASSIGNED;
    let mut state = State::new(input);
    let probed = state.probe(Cx::value(), source_root).unwrap();
    let out = state.realize(Cx::value(), probed);
    let flags = state.arena.node(out.value.unwrap()).flags();
    assert!(flags.contains(crate::bir::NodeFlags::PURE));
    assert!(flags.contains(crate::bir::NodeFlags::STRICT));
    assert!(!flags.contains(crate::bir::NodeFlags::DELAY_SAFE));
}

#[test]
fn lets_and_sequences_in_all_contexts() {
    for kind in [
        LetKind::Strict,
        LetKind::Alias,
        LetKind::StrictOpt,
        LetKind::Variable,
    ] {
        let mut a = LamArena::new();
        let x = Ident::new("x", 10, IdentFlags::NONE);
        let y = Ident::new("y", 11, IdentFlags::NONE);
        let z = Ident::new("z", 12, IdentFlags::NONE);
        let one = a.const_(C::Int {
            i: 1,
            comment: None,
        });
        let y_use = a.var(y);
        let nested = a.let_(LetKind::Strict, y, one, y_use);
        let two = a.const_(C::Int {
            i: 2,
            comment: None,
        });
        let x_use = a.var(x);
        let tail = a.let_(LetKind::Alias, z, two, x_use);
        let root = a.let_(kind, x, nested, tail);
        compare(a, root);
    }
    for first_position in [false, true] {
        let mut a = LamArena::new();
        let x = Ident::new("x", 10, IdentFlags::NONE);
        let value = a.const_(C::JsTrue);
        let body = a.var(x);
        let binding = a.let_(LetKind::Strict, x, value, body);
        let constant = a.const_(C::String("discarded".into()));
        let inner = if first_position {
            a.seq_raw(binding, constant)
        } else {
            a.seq_raw(constant, binding)
        };
        let tail = a.const_(C::Int {
            i: 9,
            comment: None,
        });
        let root = a.seq_raw(inner, tail);
        compare(a, root);
    }
}

#[test]
fn functions_and_function_attributes_in_all_contexts() {
    use crate::lambda::{FunctionAttribute, LamLoc};
    for return_unit in [false, true] {
        for async_ in [false, true] {
            for one_unit_arg in [false, true] {
                let mut a = LamArena::new();
                let param = Ident::new("arg", 10, IdentFlags::NONE);
                let body = if return_unit || one_unit_arg {
                    a.const_(C::JsUndefined {
                        is_unit: return_unit,
                    })
                } else {
                    a.var(param)
                };
                let attr = FunctionAttribute {
                    return_unit,
                    async_,
                    one_unit_arg,
                    directive: Some("use test".into()),
                    ..Default::default()
                };
                let root = a.function_(1, &[param], body, attr, LamLoc::NONE);
                compare(a, root);
            }
        }
    }
    let mut a = LamArena::new();
    let outer = Ident::new("x", 10, IdentFlags::NONE);
    let inner = Ident::new("x", 11, IdentFlags::NONE);
    let value = a.const_(C::Int {
        i: 1,
        comment: None,
    });
    let read = a.var(outer);
    let fun = a.function_(
        1,
        &[inner],
        read,
        FunctionAttribute::default(),
        LamLoc::NONE,
    );
    let root = a.let_(LetKind::Strict, outer, value, fun);
    compare(a, root);
}

#[test]
fn supported_constructs_preserve_identities_without_touching_the_legacy_counter() {
    let mut a = LamArena::new();
    let id = Ident::new("preserved", 50_000, IdentFlags::NONE);
    let value = a.const_(C::JsNull);
    let body = a.var(id);
    let root = a.let_(LetKind::Strict, id, value, body);
    let input = bridge::import_lambda(&a, root).unwrap();
    let source_root = input.root;
    let identities = input.idents.clone();
    let stamp = Ident::current_local_stamp();
    let mut state = State::new(input);
    let probed = state.probe(Cx::value(), source_root).unwrap();
    assert_eq!(state.idents, identities);
    assert_eq!(state.arena.vars.order(VarId(0)), 50_000);
    state.complete(Cx::value(), probed);
    assert_eq!(Ident::current_local_stamp(), stamp);
}

#[test]
fn ten_thousand_deep_supported_nodes_use_linear_work() {
    for shape in 0..4 {
        let mut source = LamArena::new();
        let mut root = source.const_(C::JsNull);
        let mut nodes = 1;
        for i in 0..10_000 {
            root = if shape == 3 {
                nodes += 1;
                source.function_(
                    0,
                    &[],
                    root,
                    Default::default(),
                    crate::lambda::LamLoc::NONE,
                )
            } else {
                let leaf = source.const_(C::JsTrue);
                nodes += 2;
                match shape {
                    0 => source.seq_raw(leaf, root),
                    1 => source.seq_raw(root, leaf),
                    2 => source.let_(
                        LetKind::Strict,
                        Ident::new("binding", i + 1, IdentFlags::NONE),
                        leaf,
                        root,
                    ),
                    _ => unreachable!(),
                }
            };
        }
        let input = bridge::import_lambda(&source, root).unwrap();
        let root = input.root;
        let mut state = State::new(input);
        let probed = state.probe(Cx::value(), root).unwrap();
        let out = state.realize(Cx::value(), probed);
        assert_eq!(state.source_steps, nodes);
        assert!(state.free.realized <= nodes);
        assert!(state.statements.copied <= state.statements.pushed);
        let lowered = state.complete(Cx::value(), Probed::Out(out));
        lowered
            .program
            .arena
            .validate(Some(lowered.program.root))
            .unwrap();
    }
}

#[test]
fn located_functions_match_mapping_sequences() {
    for application in [false, true] {
    use crate::js_ir::source_map::SourceMapMode;
    use crate::lambda::{FunctionAttribute, LamLocTable};
    use std::sync::Arc;
    let mut locations = LamLocTable::located(Default::default());
    let loc = locations.intern(crate::location::Location::new(Default::default(), 1, 8));
    let mut source = LamArena::new();
    let body = source.const_(C::JsTrue);
    let root = if application {
        let callee = source.var(Ident::new("call", 10, IdentFlags::NONE));
        source.apply_raw(callee, &[body], crate::lambda::ApInfo { status: crate::lambda::ApplyStatus::InferFull, loc })
    } else {
        source.function_(0, &[], body, FunctionAttribute::default(), loc)
    };
    let input = bridge::import_lambda(&source, root).unwrap();
    let lowered = super::lower(input, Some(&locations), false).unwrap();
    let actual = bridge_j::export_js(&lowered.program).unwrap();
    let mut compiler = LambdaCompiler::new();
    compiler.set_source_map_enabled(true);
    compiler.set_lam_locs(locations.clone());
    let compiled = compiler.bir_lower_oracle(
        &mut source,
        root,
        Cx::value().cont,
        Ident::new("unused", 1, IdentFlags::NONE),
    );
    let stmt = compiler.j.stmt(StmtKind::Exp(compiled.expr));
    let expected = JsDepsProgram {
        program: JsProgram::new_in(vec![stmt], vec![], compiler.j),
        modules: vec![],
        side_effect: None,
    };
    let locations = Arc::new(locations);
    let print = |p| {
        crate::js_ir::print_deps_program_with_source_map(
            p,
            None,
            &[],
            false,
            false,
            false,
            std::path::Path::new("Mapping.js"),
            std::path::Path::new("Mapping.res"),
            SourceMapMode::Hidden,
            false,
            "",
            locations.clone(),
        )
    };
    let expected = print(&expected);
    let actual = print(&actual);
    assert_eq!(actual, expected);
    let map: serde_json::Value = serde_json::from_str(actual.1.as_ref().unwrap()).unwrap();
    assert_ne!(map["mappings"], "");
    }
}

#[test]
fn local_applications_in_all_five_contexts() {
    use crate::lambda::{ApInfo, ApplyStatus, LamLoc};
    for status in [ApplyStatus::Na, ApplyStatus::InferFull, ApplyStatus::Uncurry] {
        for nested in [false, true] {
            let mut a = LamArena::new();
            let f = Ident::new("f", 10, IdentFlags::NONE);
            let mut func = a.var(f);
            if nested {
                let one = a.const_(C::Int { i: 1, comment: None });
                func = a.apply_raw(func, &[one], ApInfo { status, loc: LamLoc::NONE });
            }
            let arg = a.const_(C::Int { i: 2, comment: None });
            let root = a.apply_raw(func, &[arg], ApInfo { status, loc: LamLoc::NONE });
            compare(a, root);
        }
    }
}

#[test]
fn cross_module_applications_without_summary_in_all_contexts() {
    use crate::lambda::{ApInfo, ApplyStatus, FieldDbgInfo, LamLoc, lam_primitive::Primitive};
    for status in [ApplyStatus::Na, ApplyStatus::InferFull, ApplyStatus::Uncurry] {
        let mut a = LamArena::new();
        let global = a.global_module(Ident::create_persistent("Other"));
        let callee = a.prim_raw(Primitive::Pfield(0, FieldDbgInfo::Module { name: crate::name::Name::new("run") }), &[global], LamLoc::NONE);
        let arg = a.const_(C::JsNull);
        let root = a.apply_raw(callee, &[arg], ApInfo { status, loc: LamLoc::NONE });
        compare(a, root);
    }
}

#[test]
fn call_effects_and_statement_arguments_in_all_contexts() {
    use crate::lambda::{ApInfo, ApplyStatus, LamLoc};
    for shape in 0..8 {
        let mut a = LamArena::new();
        let f = Ident::new("f", 10, IdentFlags::NONE);
        let x = Ident::new("x", 11, IdentFlags::NONE);
        let callee = a.var(f);
        let call = a.apply_raw(callee, &[], ApInfo { status: ApplyStatus::InferFull, loc: LamLoc::NONE });
        let value = a.const_(C::Int { i: 42, comment: None });
        let read = a.var(x);
        let binding = a.let_(LetKind::Strict, x, value, read);
        let root = match shape {
            0 => a.seq_raw(call, value),
            1 => a.seq_raw(value, call),
            2 => a.seq_raw(call, binding),
            3 => a.seq_raw(binding, call),
            4 => { let seq = a.seq_raw(call, value); a.seq_raw(seq, binding) },
            5 => { let seq = a.seq_raw(binding, call); a.seq_raw(value, seq) },
            6 => { let func = a.var(f); a.apply_raw(func, &[call, binding], ApInfo { status: ApplyStatus::Na, loc: LamLoc::NONE }) },
            7 => { let func = a.var(f); a.apply_raw(func, &[binding, call], ApInfo { status: ApplyStatus::Na, loc: LamLoc::NONE }) },
            _ => unreachable!(),
        };
        compare(a, root);
    }
}

#[test]
fn application_width_and_na_spines_have_linear_step_counts() {
    use crate::lambda::{ApInfo, ApplyStatus, LamLoc};
    for shape in 0..3 {
        let mut source = LamArena::new();
        let f = Ident::new("f", 1, IdentFlags::NONE);
        let mut root = source.var(f);
        let mut args = Vec::new();
        for i in 0..10_000 {
            let mut arg = source.const_(C::JsNull);
            if shape == 1 && i == 9_999 {
                let var = Ident::new("last", 2, IdentFlags::NONE);
                let value = source.var(var);
                arg = source.let_(LetKind::Strict, var, arg, value);
            }
            if shape == 2 {
                root = source.apply_raw(root, &[arg], ApInfo { status: ApplyStatus::Na, loc: LamLoc::NONE });
            } else { args.push(arg); }
        }
        if shape != 2 {
            root = source.apply_raw(root, &args, ApInfo { status: ApplyStatus::Na, loc: LamLoc::NONE });
        }
        let input = bridge::import_lambda(&source, root).unwrap();
        let root = input.root;
        let mut state = State::new(input);
        let probed = state.probe(Cx::value(), root).unwrap();
        let nodes = if shape == 2 { 20_001 } else if shape == 1 { 10_004 } else { 10_002 };
        assert_eq!(state.source_steps, nodes);
        assert_eq!(state.sequence_steps, if shape == 1 { 20_001 } else { 10_001 });
        let lowered = state.complete(Cx::value(), probed);
        lowered.program.arena.validate(Some(lowered.program.root)).unwrap();
    }
}

#[test]
fn unsupported_arguments_keep_their_own_reason_and_loops_wait_for_rec() {
    use crate::lambda::{ApInfo, ApplyStatus, LamLoc};
    let mut source = LamArena::new();
    let f = source.var(Ident::new("f", 1, IdentFlags::NONE));
    let a = source.const_(C::JsNull);
    let b = source.const_(C::JsTrue);
    let arg = source.prim_raw(crate::lambda::lam_primitive::Primitive::Pawait, &[a, b], LamLoc::NONE);
    let root = source.apply_raw(f, &[arg], ApInfo { status: ApplyStatus::Na, loc: LamLoc::NONE });
    let input = bridge::import_lambda(&source, root).unwrap();
    let root = input.root;
    let mut state = State::new(input);
    assert!(matches!(state.probe(Cx::value(), root), Err(Unsupported("await"))));
    let cx = Cx::new(Cont::Effect(Tail::Return(Ret::Named { loop_: Some(LoopRef(0)), in_catch: false })));
    assert!(matches!(state.probe(cx, root), Err(Unsupported("let rec"))));
}

#[test]
fn export_summaries_and_partial_calls_in_all_five_contexts() {
    use crate::cmi::persistent_env::CmjExportArity;
    use crate::js_ir::ModulePathResolver;
    use crate::lambda::{ApInfo, ApplyStatus, FieldDbgInfo, LamLoc, lam_arity::Arity, lam_primitive::Primitive};
    for groups in [vec![], vec![0], vec![2], vec![1, 2], vec![2, 1, 3]] {
        for count in 0..7 {
            for effectful in [false, true] {
                for status in [ApplyStatus::Na, ApplyStatus::InferFull, ApplyStatus::Uncurry] {
                    let resolver = ModulePathResolver::from_compile_options(None, None, None, None, None, None, false);
                    resolver.set_bir_test_export("Other", "run", CmjExportArity::Single(Arity::info(groups.clone(), false)), None);
                    let mut a = LamArena::new();
                    let global = a.global_module(Ident::create_persistent("Other"));
                    let callee = a.prim_raw(Primitive::Pfield(0, FieldDbgInfo::Module { name: crate::name::Name::new("run") }), &[global], LamLoc::NONE);
                    let mut args = Vec::new();
                    for _ in 0..count {
                        let mut arg = a.const_(C::JsNull);
                        if effectful {
                            arg = a.apply_raw(arg, &[], ApInfo { status: ApplyStatus::InferFull, loc: LamLoc::NONE });
                        }
                        args.push(arg);
                    }
                    let root = a.apply_raw(callee, &args, ApInfo { status, loc: LamLoc::NONE });
                    compare_with_resolver(a, root, Some(&resolver));
                }
            }
        }
    }
}

#[test]
fn eligible_cross_module_inline_has_its_named_fallback() {
    use crate::cmi::persistent_env::CmjExportArity;
    use crate::js_ir::ModulePathResolver;
    use crate::lambda::{ApInfo, ApplyStatus, FieldDbgInfo, LamLoc, Lambda, lam_arity::Arity, lam_primitive::Primitive};
    let resolver = ModulePathResolver::from_compile_options(None, None, None, None, None, None, false);
    let param = Ident::new("arg", 100, IdentFlags::NONE);
    resolver.set_bir_test_export("Other", "run", CmjExportArity::Single(Arity::info(vec![1], false)),
        Some(Lambda::function_(1, vec![param], Lambda::var(param), Default::default(), LamLoc::NONE)));
    let mut a = LamArena::new();
    let global = a.global_module(Ident::create_persistent("Other"));
    let callee = a.prim_raw(Primitive::Pfield(0, FieldDbgInfo::Module { name: crate::name::Name::new("run") }), &[global], LamLoc::NONE);
    let arg = a.const_(C::JsNull);
    let root = a.apply_raw(callee, &[arg], ApInfo { status: ApplyStatus::Na, loc: LamLoc::NONE });
    compare_with_resolver(a.clone(), root, Some(&resolver));
    for cx in [Cx::value(), Cx::effect(), Cx::declare(LetKind::Strict, VarId(0)), Cx::assign(VarId(0)), Cx::returning()] {
        let input = bridge::import_lambda(&a, root).unwrap();
        let root = input.root;
        let mut state = State::new(input);
        state.resolver = Some(resolver.clone());
        state.cross_module_inline = true;
        assert!(matches!(state.probe(cx, root), Err(Unsupported("cross-module inline"))));
    }
}

#[test]
fn block_substitution_and_dead_removal_do_not_commute_with_tailcall_inlining() {
    // T1 boundary regression: the old tailcall pass counts the original tree.
    // Substituting pair[0] and physically dropping pair first removes a use of
    // pair_0, so rerunning the unchanged counter enables an additional inline.
    // This is a pass-order probe, not a replacement for the byte-exact gate.
    use crate::lambda::{ApInfo, ApplyStatus, LamLoc, TagInfo};
    use crate::lambda::lam_primitive::{Primitive, Mutable};
    use crate::lambda::lam_compat::FieldDbgInfo;
    use crate::lambda::js_pass_flatten_and_mark_dead::apply_js_flatten_and_mark_dead_pass as dead;
    use crate::lambda::js_pass_tailcall_inline::apply_js_tailcall_inline_pass as inline;
    use crate::lambda::js_shake::apply_js_shake_pass as shake;
    let mut a = LamArena::new();
    let p = Ident::new("pair", 10, IdentFlags::NONE);
    let x = Ident::new("x", 11, IdentFlags::NONE);
    let exported = Ident::new("run", 12, IdentFlags::NONE);
    let arg = a.var(x);
    let fun = a.function_(1, &[x], arg, Default::default(), LamLoc::NONE);
    let one = a.const_(C::Int { i: 1, comment: None });
    let block = a.prim_raw(Primitive::Pmakeblock(TagInfo::Tuple, Mutable::Immutable), &[fun, one], LamLoc::NONE);
    let target = a.var(p);
    let field = a.prim_raw(Primitive::Pfield(0, FieldDbgInfo::Tuple), &[target], LamLoc::NONE);
    let arg = a.const_(C::Int { i: 2, comment: None });
    let call = a.apply_raw(field, &[arg], ApInfo { loc: LamLoc::NONE, status: ApplyStatus::InferFull });
    let wrapper = a.function_(0, &[], call, Default::default(), LamLoc::NONE);
    let root = a.let_(LetKind::Strict, p, block, wrapper);
    let mut compiler = LambdaCompiler::new();
    let compiled = compiler.bir_lower_oracle(&mut a, root, Cont::Declare(LetKind::Strict, VarId(0)), exported);
    let program = JsDepsProgram { program: JsProgram::new_in(compiled.prelude, vec![exported], compiler.j), modules: vec![], side_effect: None };
    let old = shake(dead(inline(program.clone()), false));
    let mut moved = crate::lambda::js_pass_flatten_and_mark_dead::apply_js_flatten_pass(dead(program, false));
    let j = &moved.program.arena;
    moved.program.block.retain(|&stmt| !matches!(j.sk(stmt), StmtKind::Variable(v)
        if j.var(v).ident_info.used_stats == crate::js_ir::op::UsedStats::DeadPure));
    let new = shake(inline(moved));
    let print = |p: &JsDepsProgram| crate::js_ir::print_deps_program_with_directives_and_options(p, None, &[], false, false, false);
    assert_eq!(print(&old), "\n\n\nfunction pair_0(x) {\n  return x;\n}\n\nfunction run() {\n  return pair_0(2);\n}\n\nexport {\n  run,\n}\n/* No side effect */\n");
    assert_eq!(print(&new), "\n\n\nfunction run() {\n  return 2;\n}\n\nexport {\n  run,\n}\n/* No side effect */\n");
}
