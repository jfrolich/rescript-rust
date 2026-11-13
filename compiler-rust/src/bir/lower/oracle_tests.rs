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

fn compare_with_options(arena: LamArena, root: Lam, resolver: Option<&crate::js_ir::ModulePathResolver>, checks: bool) {
    compare_in_contexts(arena, root, resolver, checks, &[0, 1, 2, 3, 4]);
}

pub(super) fn compare_in_contexts(arena: LamArena, root: Lam, resolver: Option<&crate::js_ir::ModulePathResolver>, checks: bool, contexts: &[u8]) {
    compare_oracle(arena, root, resolver, checks, contexts, None, false);
}

pub(super) fn compare_mapped(arena: LamArena, root: Lam, locations: &crate::lambda::LamLocTable) {
    compare_oracle(arena, root, None, true, &[0,1,2,3,4], Some(locations), false);
}

fn compare_oracle(mut arena: LamArena, root: Lam, resolver: Option<&crate::js_ir::ModulePathResolver>, checks: bool, contexts: &[u8], locations: Option<&crate::lambda::LamLocTable>, inline: bool) {
    let target = Ident::new("result", arena.ident_stamp_bound() + 1, IdentFlags::NONE);
    for direct in [false, true] {
        for &context in contexts {
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
            state.cross_module_inline = inline;
            state.locations = locations.cloned();
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
            compiler.cross_module_inline = inline;
            compiler.module_path_resolver = resolver.cloned();
            if let Some(locations) = locations {
                compiler.set_source_map_enabled(true);
                compiler.set_lam_locs(locations.clone());
            }
            compiler.check_div_by_zero = checks;
            compiler.awaited_units = crate::lambda::lam_compile_main::awaited_units(&arena, root);
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
            for preserve in [false, true] {
            let print = |p: &JsDepsProgram| {
                crate::js_ir::print_deps_program_with_directives_and_options(
                    p,
                    None,
                    &[],
                    false,
                    preserve,
                    false,
                )
            };
            assert_eq!(print(&actual), print(&expected), "context {cx:?}, preserve {preserve}");
            if let Some(locations) = locations {
                let locations = std::sync::Arc::new(locations.clone());
                let mapped = |p| crate::js_ir::print_deps_program_with_source_map(
                    p,None,&[],false,preserve,false,std::path::Path::new("Mapping.js"),
                    std::path::Path::new("Mapping.res"),crate::js_ir::source_map::SourceMapMode::Hidden,
                    false,"",locations.clone());
                assert_eq!(mapped(&actual),mapped(&expected),"mappings, context {cx:?}");
            }
            }
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
fn method_receiver_is_held_without_detaching_method() {
    use crate::lambda::{ApInfo, ApplyStatus, LamLoc, lam_primitive::Primitive};
    let mut a = LamArena::new();
    let object = a.var(Ident::new("object", 1, IdentFlags::NONE));
    let callee = a.prim_raw(Primitive::PjsObjectGet("m".into()), &[object], LamLoc::NONE);
    let one = a.const_(C::int(1));
    let arg = a.assign(Ident::new("state", 2, IdentFlags::NONE), one);
    let root = a.apply_raw(callee, &[arg], ApInfo { status: ApplyStatus::Uncurry, loc: LamLoc::NONE });
    compare(a, root);
}

#[test]
fn loop_arguments_match_legacy() {
    use crate::lambda::{ApInfo, ApplyStatus, LamLoc};
    let mut source = LamArena::new();
    let f = source.var(Ident::new("f", 1, IdentFlags::NONE));
    let a = source.const_(C::JsNull);
    let b = source.const_(C::JsTrue);
    let arg = source.while_(b, a);
    let root = source.apply_raw(f, &[arg], ApInfo { status: ApplyStatus::Na, loc: LamLoc::NONE });
    compare(source, root);
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
fn eligible_cross_module_inline_matches_legacy() {
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
    compare_oracle(a, root, Some(&resolver), true, &[0,1,2,3,4], None, true);
}

#[test]
fn inline_body_with_effectful_argument_matches_legacy() {
    use crate::cmi::persistent_env::CmjExportArity;
    use crate::js_ir::ModulePathResolver;
    use crate::lambda::{ApInfo, ApplyStatus, FieldDbgInfo, LamLoc, Lambda, lam_arity::Arity, lam_primitive::Primitive};
    let resolver = ModulePathResolver::from_compile_options(None, None, None, None, None, None, false);
    let param = Ident::new("arg", 100, IdentFlags::NONE);
    let mut body = LamArena::new();
    let arg = body.var(param);
    let root = body.prim_raw(Primitive::Pmakearray, &[arg, arg], LamLoc::NONE);
    resolver.set_bir_test_export("Other", "run", CmjExportArity::Single(Arity::info(vec![1], false)),
        Some(Lambda::function_(1, vec![param], body.export(root), Default::default(), LamLoc::NONE)));
    let mut a = LamArena::new();
    let global = a.global_module(Ident::create_persistent("Other"));
    let callee = a.prim_raw(Primitive::Pfield(0, FieldDbgInfo::Module { name: crate::name::Name::new("run") }), &[global], LamLoc::NONE);
    let arg = a.prim_raw(Primitive::PinitMod, &[], LamLoc::NONE);
    let root = a.apply_raw(callee, &[arg], ApInfo { status: ApplyStatus::Na, loc: LamLoc::NONE });
    compare_oracle(a.clone(), root, Some(&resolver), true, &[0,1,2,3,4], None, true);
    resolver.set_bir_test_export("Other", "run", CmjExportArity::Single(Arity::info(vec![1], false)),
        Some(Lambda::function_(1, vec![param], Lambda::Lwhile(Box::new(Lambda::var(param)), Box::new(Lambda::var(param))), Default::default(), LamLoc::NONE)));
    compare_oracle(a, root, Some(&resolver), true, &[0,1,2,3,4], None, true);
}

#[test]
fn block_substitution_and_dead_removal_do_not_commute_with_tailcall_inlining() {
    // THREE_TREES.md T1/T4 boundary: the old tailcall pass counts the original tree.
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

#[test]
fn a_return_conditional_does_not_fold_over_a_statement_form() {
    // C:5139 lambda_contains_statement_value_form: the branch is a string
    // switch of one complete case, lowered to its body `e; return 5`. The
    // conditional stays a statement instead of `return x ? (e, 5) : 2`.
    use crate::lambda::LamLoc;
    use crate::lambda::lam_primitive::Primitive as P;
    let mut a = LamArena::new();
    let one = a.const_(C::Int { i: 1, comment: None });
    let effect = a.prim_raw(P::PinitMod, &[one], LamLoc::NONE);
    let five = a.const_(C::Int { i: 5, comment: None });
    let body = a.seq_raw(effect, five);
    let y = a.var(Ident::new("y", 11, IdentFlags::NONE));
    let branch = a.string_switch(y, &[("a", body)], None);
    let x = a.var(Ident::new("x", 10, IdentFlags::NONE));
    let two = a.const_(C::Int { i: 2, comment: None });
    let root = a.if_(x, branch, two);
    compare(a, root);
}

#[test]
fn a_result_the_lowering_assigns_is_not_held_before_a_statement_argument() {
    // A:28 delay_safe reads C:404 `assignable`, the targets of level-L
    // assignments: the temporary of the first argument is passed as it is.
    use crate::lambda::lam_primitive::Primitive as P;
    use crate::lambda::{ApInfo, ApplyStatus, LamLoc};
    let mut a = LamArena::new();
    let arg = |a: &mut LamArena, name: &str, stamp: i32| {
        let test = a.var(Ident::new(name, stamp, IdentFlags::NONE));
        let thrown = a.const_(C::Int { i: stamp, comment: None });
        let yes = a.prim_raw(P::Praise, &[thrown], LamLoc::NONE);
        let value = a.const_(C::Int { i: stamp + 1, comment: None });
        let no = a.prim_raw(P::PinitMod, &[value], LamLoc::NONE);
        a.if_(test, yes, no)
    };
    let first = arg(&mut a, "x", 10);
    let second = arg(&mut a, "y", 20);
    let f = a.var(Ident::new("f", 30, IdentFlags::NONE));
    let info = ApInfo { status: ApplyStatus::Na, loc: LamLoc::NONE };
    let root = a.apply_raw(f, &[first, second], info);
    compare(a, root);
}

#[test]
fn a_result_the_lowering_assigns_is_not_held_before_a_statement_argument_of_an_external() {
    // The same arguments through the external argument holding: a result
    // temporary the lowering assigned stays delay-safe there as well.
    use crate::lambda::lam_primitive::{DeclKind, ExternalDecl, JsCall, Param, Primitive as P};
    use crate::lambda::LamLoc;
    for (kind, count) in [
        (DeclKind::DeclVal { name: "f".into() }, 2),
        (DeclKind::DeclVal { name: "f".into() }, 3),
        (DeclKind::DeclNew { name: "F".into() }, 2),
        (DeclKind::DeclSend { name: "f".into() }, 3),
    ] {
        let mut a = LamArena::new();
        let args: Vec<_> = (0..count)
            .map(|i| {
                let stamp = 10 * (i + 1);
                let test = a.var(Ident::new("x", stamp, IdentFlags::NONE));
                let thrown = a.const_(C::Int { i: stamp, comment: None });
                let yes = a.prim_raw(P::Praise, &[thrown], LamLoc::NONE);
                let value = a.const_(C::Int { i: stamp + 1, comment: None });
                let no = a.prim_raw(P::PinitMod, &[value], LamLoc::NONE);
                a.if_(test, yes, no)
            })
            .collect();
        let call = JsCall {
            prim_name: "f".into(),
            arg_types: vec![Param::dummy(); count as usize],
            ffi: ExternalDecl {
                kind,
                module_: None,
                scopes: vec![],
                variadic: false,
                effective_arity: count as _,
            },
        };
        let root = a.prim_raw(P::PjsCall(Box::new(call)), &args, LamLoc::NONE);
        compare(a, root);
    }
}

#[test]
fn an_inlined_function_that_holds_a_catch_is_lowered_after_a_catch_of_the_unit() {
    // The inlined body brings a catch header the unit did not have when its
    // first catch sized the jump table.
    use crate::cmi::persistent_env::CmjExportArity;
    use crate::js_ir::ModulePathResolver;
    use crate::lambda::lam_primitive::Primitive as P;
    use crate::lambda::{ApInfo, ApplyStatus, FieldDbgInfo, LamLoc, Lambda, lam_arity::Arity};
    let effect = |a: &mut LamArena, i: i32| {
        let value = a.const_(C::Int { i, comment: None });
        a.prim_raw(P::PinitMod, &[value], LamLoc::NONE)
    };
    let catch = |a: &mut LamArena, test: Ident, label: i32| {
        let test = a.var(test);
        let (exit, other) = (a.static_raise(label, &[]), effect(a, label));
        let body = a.if_(test, exit, other);
        let first = effect(a, label + 1);
        let second = effect(a, label + 2);
        let handler = a.seq_raw(first, second);
        a.static_catch(body, label, &[], handler)
    };
    let resolver = ModulePathResolver::from_compile_options(None, None, None, None, None, None, false);
    let param = Ident::new("arg", 100, IdentFlags::NONE);
    let mut body = LamArena::new();
    let root = catch(&mut body, param, 50);
    resolver.set_bir_test_export("Other", "run", CmjExportArity::Single(Arity::info(vec![1], false)),
        Some(Lambda::function_(1, vec![param], body.export(root), Default::default(), LamLoc::NONE)));
    let mut a = LamArena::new();
    let own = catch(&mut a, Ident::new("x", 10, IdentFlags::NONE), 1);
    let global = a.global_module(Ident::create_persistent("Other"));
    let callee = a.prim_raw(P::Pfield(0, FieldDbgInfo::Module { name: crate::name::Name::new("run") }), &[global], LamLoc::NONE);
    let arg = a.var(Ident::new("y", 11, IdentFlags::NONE));
    let call = a.apply_raw(callee, &[arg], ApInfo { status: ApplyStatus::Na, loc: LamLoc::NONE });
    let root = a.seq_raw(own, call);
    compare_oracle(a, root, Some(&resolver), true, &[0, 1, 2, 3, 4], None, true);
}

#[test]
fn cross_module_inline_after_lowering_a_closure_with_assignment() {
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
    let call = a.apply_raw(callee, &[arg], ApInfo { status: ApplyStatus::Na, loc: LamLoc::NONE });
    let mutable = Ident::new("mutable", 10, IdentFlags::NONE);
    let assignment = a.assign(mutable, arg);
    let unit = Ident::new("unit", 11, IdentFlags::NONE);
    let attr = crate::lambda::FunctionAttribute { one_unit_arg: true, ..Default::default() };
    let closure = a.function_(1, &[unit], assignment, attr, LamLoc::NONE);
    let root = a.seq_raw(closure, call);
    compare_oracle(a, root, Some(&resolver), true, &[0,1,2,3,4], None, true);
}

/// The legacy pipeline on one function bound to an exported `run`, with the
/// passes `order` names (1 flatten, 3 tail-call inlining, 5 substitution and
/// dead marks, 6 shake), printed. For the T4 ordering findings below.
fn legacy_text(build: impl Fn(&mut LamArena) -> Lam, order: &[u8]) -> String {
    use crate::lambda::js_pass_flatten_and_mark_dead::{apply_js_flatten_and_mark_dead_pass as dead, apply_js_flatten_pass as flatten};
    use crate::lambda::js_pass_tailcall_inline::apply_js_tailcall_inline_pass as inline;
    use crate::lambda::js_shake::apply_js_shake_pass as shake;
    let mut a = LamArena::new();
    let root = build(&mut a);
    let exported = Ident::new("run", 900, IdentFlags::NONE);
    let mut compiler = LambdaCompiler::new();
    let compiled = compiler.bir_lower_oracle(&mut a, root, Cont::Declare(LetKind::Strict, VarId(0)), exported);
    let mut program = JsDepsProgram { program: JsProgram::new_in(compiled.prelude, vec![exported], compiler.j), modules: vec![], side_effect: None };
    for pass in order {
        program = match pass {
            1 => flatten(program),
            3 => inline(program),
            5 => dead(program, false),
            6 => shake(program),
            _ => unreachable!("pass number"),
        };
    }
    crate::js_ir::print_deps_program_with_directives_and_options(&program, None, &[], false, false, false)
}

fn call(a: &mut LamArena, callee: Lam, args: &[Lam]) -> Lam {
    use crate::lambda::{ApInfo, ApplyStatus, LamLoc};
    a.apply_raw(callee, args, ApInfo { loc: LamLoc::NONE, status: ApplyStatus::InferFull })
}

#[test]
fn a_tail_call_site_inside_a_returned_conditional_exists_only_after_the_flatten_pass() {
    // THREE_TREES.md 11.4, finding 1. `run = c => { let f = p => ext(p, p); return c ? f(1) : 2 }`.
    use crate::lambda::LamLoc;
    let build = |a: &mut LamArena| {
        let (f, p, c) = (Ident::new("f", 10, IdentFlags::NONE), Ident::new("p", 11, IdentFlags::NONE), Ident::new("c", 12, IdentFlags::NONE));
        let ext = a.var(Ident::new("ext", 13, IdentFlags::NONE));
        let (p1, p2) = (a.var(p), a.var(p));
        let body = call(a, ext, &[p1, p2]);
        let function = a.function_(1, &[p], body, Default::default(), LamLoc::NONE);
        let one = a.const_(C::Int { i: 1, comment: None });
        let two = a.const_(C::Int { i: 2, comment: None });
        let callee = a.var(f);
        let applied = call(a, callee, &[one]);
        let test = a.var(c);
        let branch = a.if_(test, applied, two);
        let inner = a.let_(LetKind::Strict, f, function, branch);
        a.function_(1, &[c], inner, Default::default(), LamLoc::NONE)
    };
    // The lowering hands over one `return` of a conditional: no block ends
    // in `return f(1)`.
    assert!(legacy_text(build, &[]).contains("  return c ? f(1) : 2;\n"));
    // The flatten pass splits it; the tail-call pass then finds the site.
    let legacy = legacy_text(build, &[1, 3, 5, 6]);
    assert!(legacy.contains("  if (c) {\n    return ext(1, 1);\n  } else {\n    return 2;\n  }\n"), "{legacy}");
    assert!(!legacy.contains("let f"));
    // Deciding on the shape the lowering wrote keeps the function.
    let early = legacy_text(build, &[3, 1, 5, 6]);
    assert!(early.contains("  let f = p => ext(p, p);\n  if (c) {\n    return f(1);\n"), "{early}");
}

#[test]
fn inlining_from_an_outer_scope_takes_the_last_use_of_a_variable_of_a_closed_scope() {
    // THREE_TREES.md 11.4, finding 3 (late zero).
    // `run = () => { let f = p => 1; return () => { let y = ext(); return f(y) } }`.
    use crate::lambda::LamLoc;
    let build = |a: &mut LamArena| {
        let (f, p, y) = (Ident::new("f", 10, IdentFlags::NONE), Ident::new("p", 11, IdentFlags::NONE), Ident::new("y", 12, IdentFlags::NONE));
        let one = a.const_(C::Int { i: 1, comment: None });
        let function = a.function_(1, &[p], one, Default::default(), LamLoc::NONE);
        let ext = a.var(Ident::new("ext", 13, IdentFlags::NONE));
        let value = call(a, ext, &[]);
        let callee = a.var(f);
        let arg = a.var(y);
        let applied = call(a, callee, &[arg]);
        let body = a.let_(LetKind::Strict, y, value, applied);
        let inner = a.function_(0, &[], body, Default::default(), LamLoc::NONE);
        let outer = a.let_(LetKind::Strict, f, function, inner);
        a.function_(0, &[], outer, Default::default(), LamLoc::NONE)
    };
    assert!(legacy_text(build, &[]).contains("    let y = ext();\n    return f(y);\n"));
    // `p` is renamed to `y` and the body never reads it: the dead marks, which
    // run after every inlining, turn `let y = ext()` into `ext()`.
    let legacy = legacy_text(build, &[1, 3, 5, 6]);
    assert!(legacy.contains("  return () => {\n    ext();\n    return 1;\n  };\n"), "{legacy}");
    // When the inner function's statements are complete, `y` has one use.
    let mut a = LamArena::new();
    let root = build(&mut a);
    let input = bridge::import_lambda(&a, root).unwrap();
    let source_root = input.root;
    let mut state = State::new(input);
    let probed = state.probe(Cx::value(), source_root).unwrap();
    let lowered = state.complete(Cx::value(), probed);
    let y = lowered.program.idents.iter().position(|ident| ident.name() == "y").unwrap();
    let uses = lowered.program.arena.js_scope.as_ref().unwrap().uses[y];
    assert_eq!((uses.built, uses.remaining), (1, 1));
}

#[test]
fn a_declaration_the_tail_call_pass_finds_dead_is_not_materialised() {
    // THREE_TREES.md 11.4, finding 5. `run = () => { let x = (ext(1), ext(2)); 3 }`.
    use crate::lambda::{LamLoc, TagInfo};
    use crate::lambda::lam_primitive::{Primitive, Mutable};
    let build = |a: &mut LamArena| {
        let x = Ident::new("x", 10, IdentFlags::NONE);
        let ext = Ident::new("ext", 13, IdentFlags::NONE);
        let one = a.const_(C::Int { i: 1, comment: None });
        let two = a.const_(C::Int { i: 2, comment: None });
        let (e1, e2) = (a.var(ext), a.var(ext));
        let first = call(a, e1, &[one]);
        let second = call(a, e2, &[two]);
        let block = a.prim_raw(Primitive::Pmakeblock(TagInfo::Tuple, Mutable::Immutable), &[first, second], LamLoc::NONE);
        let three = a.const_(C::Int { i: 3, comment: None });
        let body = a.let_(LetKind::Strict, x, block, three);
        a.function_(0, &[], body, Default::default(), LamLoc::NONE)
    };
    // The tail-call pass counts no use of `x` and turns the declaration into
    // an expression statement before the substitution sees a block binding.
    let legacy = legacy_text(build, &[1, 3, 5, 6]);
    assert!(legacy.contains("  [\n    ext(1),\n    ext(2)\n  ];\n  return 3;\n"), "{legacy}");
    // Materialising where the declaration is lowered hoists the fields.
    let early = legacy_text(build, &[1, 5, 6]);
    assert!(early.contains("  let x_0 = ext(1);\n  let x_1 = ext(2);\n  return 3;\n"), "{early}");
}
