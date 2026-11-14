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
    // THREE_TREES 11.4, "T5 part B as redesigned": the naming log against
    // the pass, on the root lowered as a unit (`unit_of`).
    // A unit the pass does not support is not compared, as check mode
    // counts it in `names_uncompared`.
    let (unit, unit_root) = unit_of(arena.clone(), root);
    // Both ways of printing JSX: a unit that preserves it does not print
    // the runtime callee of an element.
    for jsx_preserve in [false, true] {
        if compared_names(unit.clone(), unit_root, resolver, inline, jsx_preserve).is_some() {
            names_agree_printing(unit.clone(), unit_root, resolver, inline, jsx_preserve);
        }
    }
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
    // The unit exports the value, so that it is printed. The gate compares
    // both texts and their mapping sequences.
    let root = source.prim_raw(
        crate::lambda::lam_primitive::Primitive::Pmakeblock(
            crate::lambda::TagInfo::ModuleExport(vec![Ident::new("value", 11, IdentFlags::NONE)]),
            crate::lambda::lam_primitive::Mutable::Immutable,
        ),
        &[root],
        crate::lambda::LamLoc::NONE,
    );
    let mut compiler = LambdaCompiler::new();
    compiler.set_source_map_enabled(true);
    compiler.set_lam_locs(locations.clone());
    let (deps, check) = compiler.compile_deps_program_with_lower_check::<true>(source, root, Default::default());
    let check = check.unwrap();
    assert!(matches!(check, crate::bir::shadow::LowerCheck::Supported(_)));
    crate::bir::shadow::check_lower(check, "Mapping.res", false).unwrap();
    let locations = Arc::new(locations);
    let actual = crate::js_ir::print_deps_program_with_source_map(
        &deps,
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
    );
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
    for groups in [vec![], vec![0], vec![2], vec![1, 2], vec![2, 1, 3], vec![1, 1, 1, 1, 2, 1]] {
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

#[test]
fn cross_module_inline_of_a_body_that_holds_a_function() {
    // The function inside the inlined body gets its header while the fragment
    // is imported, after the unit's own header (the closure's). The lowering
    // reads headers from its own arena, so that header must be made there: a
    // header left in the source's table is read out of bounds, or as the
    // closure's.
    use crate::cmi::persistent_env::CmjExportArity;
    use crate::js_ir::ModulePathResolver;
    use crate::lambda::{ApInfo, ApplyStatus, FieldDbgInfo, LamLoc, Lambda, lam_arity::Arity, lam_primitive::Primitive};
    let resolver = ModulePathResolver::from_compile_options(None, None, None, None, None, None, false);
    let param = Ident::new("arg", 100, IdentFlags::NONE);
    let first = Ident::new("first", 101, IdentFlags::NONE);
    let second = Ident::new("second", 102, IdentFlags::NONE);
    let inner = Lambda::function_(2, vec![first, second], Lambda::var(param), Default::default(), LamLoc::NONE);
    resolver.set_bir_test_export("Other", "run", CmjExportArity::Single(Arity::info(vec![1], false)),
        Some(Lambda::function_(1, vec![param], inner, Default::default(), LamLoc::NONE)));
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
/// passes `order` names (1 flatten, 2 external shadow, 3 tail-call inlining,
/// 4 record rest, 5 substitution and dead marks, 6 shake), printed. For the T4
/// ordering findings below.
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
            2 => crate::lambda::js_pass_external_shadow::apply_external_shadow_pass(program),
            3 => inline(program),
            4 => crate::lambda::js_pass_record_rest::apply_js_record_rest_pass(program),
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

#[test]
fn export_coercion_consumes_the_export_tuple_occurrence() {
    // Reduced from Dom_storage.getItem. The output tuple carries one
    // reference, which export coercion consumes before P1/P2. While the
    // lowering left coercion to the legacy code, `built` kept that reference
    // (1 against the tail-call pass's 0: the drift the T4b count experiment
    // met). With coercion on rows (T4a) the lowering releases the reference
    // itself, so `built` is the count the tail-call pass reads.
    use crate::lambda::{LamLoc, TagInfo};
    use crate::lambda::lam_primitive::{Mutable, Primitive};
    use crate::lambda::js_pass_flatten_and_mark_dead::apply_js_flatten_pass;
    use crate::lambda::js_pass_external_shadow::apply_external_shadow_pass;
    use crate::lambda::js_pass_tailcall_inline::UseCounts;
    use crate::bir::shadow::LowerCheck;
    let mut a = LamArena::new();
    let f = Ident::new("f", 10, IdentFlags::NONE);
    let one = a.const_(C::Int { i: 1, comment: None });
    let function = a.function_(0, &[], one, Default::default(), LamLoc::NONE);
    let reference = a.var(f);
    let exports = a.prim_raw(Primitive::Pmakeblock(TagInfo::ModuleExport(vec![f]), Mutable::Immutable), &[reference], LamLoc::NONE);
    let root = a.let_(LetKind::Strict, f, function, exports);
    // The lowering reads the variables the importer records for an export
    // block, so the unit is imported the way the gate imports it.
    let input = bridge::import_for_lowering(&a, root).0.unwrap();
    let lowered = lower(input, None, false).unwrap();
    let var = lowered.program.idents.iter().position(|&id| id == f).unwrap();
    let built = lowered.program.arena.js_scope.as_ref().unwrap().uses[var].built;
    assert_eq!(built, 0);

    let mut compiler = LambdaCompiler::new();
    let (_, check) = compiler.compile_deps_program_with_lower_check::<true>(a, root, Default::default());
    let Some(LowerCheck::Supported(pair)) = check else { panic!("supported export tuple") };
    let legacy = apply_external_shadow_pass(apply_js_flatten_pass(pair.before[0].clone()));
    let mut counts = UseCounts::default();
    crate::js_ir::walk::walk_block(&mut counts, &legacy.program.arena, &legacy.program.block);
    assert_eq!(counts.counts.get(&f).copied().unwrap_or(0), 0);
    let print = |p: &JsDepsProgram| crate::js_ir::print_deps_program_with_directives_and_options(p, None, &[], false, false, false);
    let expected = "\n\n\nfunction f() {\n  return 1;\n}\n\nexport {\n  f,\n}\n/* No side effect */\n";
    assert_eq!(print(&pair.after[0]), expected);
    assert_eq!(print(&pair.after[1]), expected);
}

#[test]
fn flattening_a_copied_return_branch_changes_the_simplify_if_head_reader() {
    // Reduced from Primitive_object.res, lower mismatch at line 75. A one-case
    // string switch lowers via State::if_statement: take_list, then J-S3.
    // R5 changes its last then-statement from Return(Cond) to If. The
    // simplify_if_head exit test stops recognizing it as a return and keeps
    // the else branch, whereas the legacy order moves that branch after it.
    use crate::js_ir::arena::ExprKind;
    use crate::js_ir::build::stmt;
    use crate::lambda::{LamLoc, lam_primitive::Primitive};
    use crate::lambda::js_pass_flatten_and_mark_dead::{apply_js_flatten_pass as flatten, apply_js_flatten_and_mark_dead_pass as dead};
    use crate::lambda::js_pass_external_shadow::apply_external_shadow_pass as shadow;
    use crate::lambda::js_pass_tailcall_inline::apply_js_tailcall_inline_pass as inline;
    use crate::lambda::js_pass_record_rest::apply_js_record_rest_pass as rest;
    use crate::lambda::js_shake::apply_js_shake_pass as shake;
    let mut a = LamArena::new();
    let x = Ident::new("x", 10, IdentFlags::NONE);
    let y = Ident::new("y", 11, IdentFlags::NONE);
    let exported = Ident::new("run", 900, IdentFlags::NONE);
    let test = a.var(y);
    let one = a.const_(C::Int { i: 1, comment: None });
    let two = a.const_(C::Int { i: 2, comment: None });
    let yes = a.if_(test, one, two);
    let effect = a.prim_raw(Primitive::PinitMod, &[], LamLoc::NONE);
    let three = a.const_(C::Int { i: 3, comment: None });
    let no = a.seq_raw(effect, three);
    let test = a.var(x);
    let switch = a.string_switch(test, &[("a", yes)], Some(no));
    let root = a.function_(2, &[x, y], switch, Default::default(), LamLoc::NONE);
    let mut compiler = LambdaCompiler::new();
    let compiled = compiler.bir_lower_oracle(&mut a, root, Cont::Declare(LetKind::Strict, VarId(0)), exported);
    let raw = JsDepsProgram { program: JsProgram::new_in(compiled.prelude, vec![exported], compiler.j), modules: vec![], side_effect: None };
    let mut early = raw.clone();
    let j = &early.program.arena;
    let StmtKind::Variable(declaration) = j.sk(early.program.block[0]) else { panic!("run declaration") };
    let mut declaration = j.var(declaration).clone();
    let ExprKind::Fun(function) = j.ek(declaration.value.unwrap()) else { panic!("run function") };
    let mut function = j.fun(function);
    let mut body = j.stmts(function.body).to_vec();
    while let [statement] = body.as_slice() {
        let StmtKind::Block(inner) = j.sk(*statement) else { break; };
        body = j.stmts(inner).to_vec();
    }
    let StmtKind::If(test, yes, no) = j.sk(body[0]) else { panic!("switch guard") };
    assert!(j.stmts(no).is_empty());
    let &[returned] = j.stmts(yes) else { panic!("one returned conditional") };
    let StmtKind::Return(value) = j.sk(returned) else { panic!("R5 input") };
    assert!(matches!(j.ek(value), ExprKind::Cond(..)));
    assert_eq!(body.len(), 3);

    // Recreate exactly the copied-branch boundary, not a new production path.
    // The legacy Flatten is the oracle for R5; all other input is unchanged.
    early.program.block = j.stmts(yes).to_vec();
    early = flatten(early);
    let yes = std::mem::take(&mut early.program.block);
    assert!(matches!(early.program.arena.sk(yes[0]), StmtKind::If(..)));
    let j = &mut early.program.arena;
    let statement = stmt::if_(test, &yes, &body[1..], j);
    function.body = j.stmt_list(&[statement]);
    let function = j.fun_id(function);
    declaration.value = Some(j.expr(ExprKind::Fun(function)));
    let declaration = j.var_id(declaration);
    early.program.block = vec![j.stmt(StmtKind::Variable(declaration))];
    let finish = |p| shake(dead(rest(inline(shadow(p))), false));
    let legacy = finish(flatten(raw));
    let moved = finish(early);
    let print = |p: &JsDepsProgram| crate::js_ir::print_deps_program_with_directives_and_options(p, None, &[], false, false, false);
    assert_eq!(print(&legacy), "\n\n\nfunction run(x, y) {\n  if (x === \"a\") {\n    if (y) {\n      return 1;\n    } else {\n      return 2;\n    }\n  }\n  Primitive_module.init();\n  return 3;\n}\n\nexport {\n  run,\n}\n/* No side effect */\n");
    assert_eq!(print(&moved), "\n\n\nfunction run(x, y) {\n  if (x === \"a\") {\n    if (y) {\n      return 1;\n    } else {\n      return 2;\n    }\n  } else {\n    Primitive_module.init();\n    return 3;\n  }\n}\n\nexport {\n  run,\n}\n/* No side effect */\n");
}

#[test]
fn inlining_before_the_external_shadow_pass_hides_the_binding_that_shadows_a_global() {
    // THREE_TREES.md 11.4, "T4c design" (c), first counterexample.
    // `run = a => { let g = location => ext(location, <global location>); return g(a) }`.
    // P2 qualifies a global that a binding of its scope shadows. With P3 after
    // it, P2 sees the parameter `location` around the reference. With the
    // splice before it, the parameter was renamed to `a` and is gone.
    use crate::lambda::LamLoc;
    let build = |a: &mut LamArena| {
        let (g, p, arg) = (Ident::new("g", 10, IdentFlags::NONE), Ident::new("location", 11, IdentFlags::NONE), Ident::new("a", 12, IdentFlags::NONE));
        let ext = a.var(Ident::new("ext", 13, IdentFlags::NONE));
        let (read, global) = (a.var(p), a.var(Ident::create_js("location")));
        let body = call(a, ext, &[read, global]);
        let function = a.function_(1, &[p], body, Default::default(), LamLoc::NONE);
        let callee = a.var(g);
        let x = a.var(arg);
        let applied = call(a, callee, &[x]);
        let inner = a.let_(LetKind::Strict, g, function, applied);
        a.function_(1, &[arg], inner, Default::default(), LamLoc::NONE)
    };
    let text = |value: &str| format!("\n\n\nfunction run(a) {{\n  return ext(a, {value});\n}}\n\nexport {{\n  run,\n}}\n/* No side effect */\n");
    // The legacy order.
    assert_eq!(legacy_text(build, &[1, 2, 3, 4, 5, 6]), text("globalThis.location"));
    // Step A in the lowering: the inlining decided before P1 and P2 run.
    assert_eq!(legacy_text(build, &[3, 1, 2, 4, 5, 6]), text("location"));
}

#[test]
fn flattening_after_a_site_in_a_returned_conditional_was_spliced_maps_its_predicate() {
    // THREE_TREES.md 11.4, "T4c design" (c), second counterexample.
    // `run = c => { let f = p => ext(p, p); return ext(z => z ? 1 : 2) ? f(c) : 3 }`.
    // The site is inside a returned conditional, so the statement has to
    // become an `if` before the callee's statements can stand in a branch.
    // P1's own rule for a returned conditional leaves the predicate as it
    // is; P1 run on the `if` maps the predicate and flattens the callback.
    use crate::lambda::LamLoc;
    let build = |a: &mut LamArena| {
        let (f, p, c, z) = (Ident::new("f", 10, IdentFlags::NONE), Ident::new("p", 11, IdentFlags::NONE), Ident::new("c", 12, IdentFlags::NONE), Ident::new("z", 14, IdentFlags::NONE));
        let ext = Ident::new("ext", 13, IdentFlags::NONE);
        let callee = a.var(ext);
        let (p1, p2) = (a.var(p), a.var(p));
        let body = call(a, callee, &[p1, p2]);
        let function = a.function_(1, &[p], body, Default::default(), LamLoc::NONE);
        let one = a.const_(C::Int { i: 1, comment: None });
        let two = a.const_(C::Int { i: 2, comment: None });
        let three = a.const_(C::Int { i: 3, comment: None });
        let test = a.var(z);
        let chosen = a.if_(test, one, two);
        let callback = a.function_(1, &[z], chosen, Default::default(), LamLoc::NONE);
        let callee = a.var(ext);
        let test = call(a, callee, &[callback]);
        let callee = a.var(f);
        let arg = a.var(c);
        let applied = call(a, callee, &[arg]);
        let branch = a.if_(test, applied, three);
        let inner = a.let_(LetKind::Strict, f, function, branch);
        a.function_(1, &[c], inner, Default::default(), LamLoc::NONE)
    };
    assert!(legacy_text(build, &[]).contains("  return ext(z => z ? 1 : 2) ? f(c) : 3;\n"));
    let text = |predicate: &str| format!("\n\n\nfunction run(c) {{\n  if (ext({predicate})) {{\n    return ext(c, c);\n  }} else {{\n    return 3;\n  }}\n}}\n\nexport {{\n  run,\n}}\n/* No side effect */\n");
    // The legacy order: the callback keeps its returned conditional.
    assert_eq!(legacy_text(build, &[1, 2, 3, 4, 5, 6]), text("z => z ? 1 : 2"));
    // The `if` exists before P1 runs: the first flatten stands for the
    // reshaping of the path to the site, the second is P1 after step A.
    assert_eq!(
        legacy_text(build, &[1, 3, 1, 2, 4, 5, 6]),
        text("z => {\n      if (z) {\n        return 1;\n      } else {\n        return 2;\n      }\n    }"),
    );
}

/// Step A's decisions for one Lambda (not simplified first) against the
/// legacy tail-call pass on the same program after P1 and P2: the comparison
/// counters, and `(name, status, inline, built)` per decided declaration.
fn step_a(build: impl Fn(&mut LamArena) -> Lam) -> (DecisionStats, Vec<(String, crate::js_ir::op::UsedStats, bool, u32)>) {
    use crate::js_ir::op::UsedStats;
    use crate::lambda::js_pass_external_shadow::apply_external_shadow_pass as shadow;
    use crate::lambda::js_pass_flatten_and_mark_dead::apply_js_flatten_pass as flatten;
    let mut a = LamArena::new();
    let root = build(&mut a);
    let input = bridge::import_lambda(&a, root).unwrap();
    let source_root = input.root;
    let mut state = State::new(input);
    let probed = state.probe(Cx::value(), source_root).unwrap();
    let lowered = state.complete(Cx::value(), probed);
    let program = shadow(flatten(bridge_j::export_js(&lowered.program).unwrap()));
    let scope = lowered.program.arena.js_scope.as_ref().unwrap();
    let decisions: Vec<_> = scope.decisions.iter().map(|decision| (lowered.program.idents[decision.var.index()], *decision)).collect();
    let stats = crate::bir::shadow::compare_decisions(&decisions, &program.program);
    let status = |bits| [UsedStats::DeadPure, UsedStats::DeadNonPure, UsedStats::Exported, UsedStats::OncePure, UsedStats::Used]
        .into_iter().find(|status| *status as u32 == bits).unwrap();
    let rows = decisions.iter().map(|(ident, d)| (ident.name().to_string(), status(d.status()), d.inline(), d.built())).collect();
    (stats, rows)
}

fn agrees(stats: &DecisionStats) {
    assert_eq!(
        (stats.decision_extra, stats.decision_missing, stats.decision_copied, stats.decision_count_differences, stats.decision_status_differences, stats.decision_site_differences),
        (0, 0, 0, 0, 0, 0)
    );
    assert_eq!(stats.decision_rows, stats.decision_legacy);
    assert_eq!(stats.decision_inline, stats.decision_legacy_inline);
}

/// `c => { let f = p => ext(p, p); <body(f, c)> }`.
fn with_local_function(a: &mut LamArena, body: impl Fn(&mut LamArena, Ident, Ident) -> Lam) -> Lam {
    use crate::lambda::LamLoc;
    let (f, p, c) = (Ident::new("f", 10, IdentFlags::NONE), Ident::new("p", 11, IdentFlags::NONE), Ident::new("c", 12, IdentFlags::NONE));
    let ext = a.var(Ident::new("ext", 13, IdentFlags::NONE));
    let (p1, p2) = (a.var(p), a.var(p));
    let value = call(a, ext, &[p1, p2]);
    let function = a.function_(1, &[p], value, Default::default(), LamLoc::NONE);
    let body = body(a, f, c);
    let inner = a.let_(LetKind::Strict, f, function, body);
    a.function_(1, &[c], inner, Default::default(), LamLoc::NONE)
}

#[test]
fn step_a_decides_as_the_tail_call_pass_does() {
    // THREE_TREES.md 11.4, "T4c design" (a) and (b): the decisions only.
    use crate::js_ir::op::UsedStats;
    use crate::lambda::LamLoc;
    use crate::lambda::lam_primitive::Primitive;
    let int = |a: &mut LamArena, i| a.const_(C::Int { i, comment: None });
    let apply_f = |a: &mut LamArena, f: Ident, i: i32| {
        let callee = a.var(f);
        let arg = a.const_(C::Int { i, comment: None });
        call(a, callee, &[arg])
    };
    let row = |rows: &[(String, UsedStats, bool, u32)], name: &str| rows.iter().find(|row| row.0 == name).cloned().unwrap();
    // A function called once, by the `return` that ends its scope.
    let (stats, rows) = step_a(|a| with_local_function(a, |a, f, _| apply_f(a, f, 1)));
    agrees(&stats);
    assert_eq!(row(&rows, "f"), ("f".into(), UsedStats::OncePure, true, 1));
    // The same call in a branch of a returned conditional (finding 1).
    let (stats, rows) = step_a(|a| with_local_function(a, |a, f, c| {
        let applied = apply_f(a, f, 1);
        let (test, two) = (a.var(c), int(a, 2));
        a.if_(test, applied, two)
    }));
    agrees(&stats);
    assert_eq!(row(&rows, "f"), ("f".into(), UsedStats::OncePure, true, 1));
    // Below two conditionals and as the last operand of a sequence.
    let (stats, rows) = step_a(|a| with_local_function(a, |a, f, c| {
        let applied = apply_f(a, f, 1);
        let effect = a.prim_raw(Primitive::PinitMod, &[], LamLoc::NONE);
        let sequence = a.seq_raw(effect, applied);
        let (test, two) = (a.var(c), int(a, 2));
        let inner = a.if_(test, sequence, two);
        let (test, three) = (a.var(c), int(a, 3));
        a.if_(test, three, inner)
    }));
    agrees(&stats);
    assert_eq!(row(&rows, "f"), ("f".into(), UsedStats::OncePure, true, 1));
    // Two calls: used, no candidate.
    let (stats, rows) = step_a(|a| with_local_function(a, |a, f, c| {
        let (first, second, test) = (apply_f(a, f, 1), apply_f(a, f, 2), a.var(c));
        a.if_(test, first, second)
    }));
    agrees(&stats);
    assert_eq!(row(&rows, "f"), ("f".into(), UsedStats::Used, false, 2));
    // One use that is no tail call: an argument.
    let (stats, rows) = step_a(|a| with_local_function(a, |a, f, _| {
        let (ext, argument) = (a.var(Ident::new("ext", 13, IdentFlags::NONE)), a.var(f));
        call(a, ext, &[argument])
    }));
    agrees(&stats);
    assert_eq!(row(&rows, "f"), ("f".into(), UsedStats::OncePure, false, 1));
    // The call is a predicate, or the head of a sequence: no site.
    let (stats, rows) = step_a(|a| with_local_function(a, |a, f, _| {
        let (test, one, two) = (apply_f(a, f, 1), int(a, 1), int(a, 2));
        a.if_(test, one, two)
    }));
    agrees(&stats);
    assert_eq!(row(&rows, "f"), ("f".into(), UsedStats::OncePure, false, 1));
    // Never used: dead and pure.
    let (stats, rows) = step_a(|a| with_local_function(a, |a, _, _| int(a, 3)));
    agrees(&stats);
    assert_eq!(row(&rows, "f"), ("f".into(), UsedStats::DeadPure, false, 0));
}

#[test]
fn step_a_finds_a_dead_block_binding_and_no_site_in_the_boundary_shape() {
    use crate::js_ir::op::UsedStats;
    use crate::lambda::{LamLoc, TagInfo};
    use crate::lambda::lam_compat::FieldDbgInfo;
    use crate::lambda::lam_primitive::{Mutable, Primitive};
    // Finding 5: `() => { let x = (ext(1), ext(2)); 3 }`.
    let (stats, rows) = step_a(|a| {
        let x = Ident::new("x", 10, IdentFlags::NONE);
        let ext = Ident::new("ext", 13, IdentFlags::NONE);
        let (one, two) = (a.const_(C::Int { i: 1, comment: None }), a.const_(C::Int { i: 2, comment: None }));
        let (e1, e2) = (a.var(ext), a.var(ext));
        let (first, second) = (call(a, e1, &[one]), call(a, e2, &[two]));
        let block = a.prim_raw(Primitive::Pmakeblock(TagInfo::Tuple, Mutable::Immutable), &[first, second], LamLoc::NONE);
        let three = a.const_(C::Int { i: 3, comment: None });
        let body = a.let_(LetKind::Strict, x, block, three);
        a.function_(0, &[], body, Default::default(), LamLoc::NONE)
    });
    agrees(&stats);
    assert_eq!(rows, vec![("x".to_string(), UsedStats::DeadNonPure, false, 0)]);
    // The boundary shape: `() => { let pair = (x => x, 1); pair[0](2) }`.
    let (stats, rows) = step_a(|a| {
        let (pair, x) = (Ident::new("pair", 10, IdentFlags::NONE), Ident::new("x", 11, IdentFlags::NONE));
        let read = a.var(x);
        let function = a.function_(1, &[x], read, Default::default(), LamLoc::NONE);
        let one = a.const_(C::Int { i: 1, comment: None });
        let block = a.prim_raw(Primitive::Pmakeblock(TagInfo::Tuple, Mutable::Immutable), &[function, one], LamLoc::NONE);
        let target = a.var(pair);
        let field = a.prim_raw(Primitive::Pfield(0, FieldDbgInfo::Tuple), &[target], LamLoc::NONE);
        let two = a.const_(C::Int { i: 2, comment: None });
        let applied = call(a, field, &[two]);
        let body = a.let_(LetKind::Strict, pair, block, applied);
        a.function_(0, &[], body, Default::default(), LamLoc::NONE)
    });
    agrees(&stats);
    assert_eq!(rows, vec![("pair".to_string(), UsedStats::OncePure, false, 1)]);
    assert_eq!(stats.decision_inline, 0);
}

#[test]
fn step_a_reads_the_export_set_at_the_top_level() {
    // The unit path: `let f = () => 1` exported, and `g` called once by the
    // exported `h`. Lambda simplification is skipped by lowering directly.
    use crate::bir::shadow::LowerCheck;
    use crate::lambda::{LamLoc, TagInfo};
    use crate::lambda::lam_primitive::{Mutable, Primitive};
    let mut a = LamArena::new();
    let f = Ident::new("f", 10, IdentFlags::NONE);
    let one = a.const_(C::Int { i: 1, comment: None });
    let function = a.function_(0, &[], one, Default::default(), LamLoc::NONE);
    let reference = a.var(f);
    let exports = a.prim_raw(Primitive::Pmakeblock(TagInfo::ModuleExport(vec![f]), Mutable::Immutable), &[reference], LamLoc::NONE);
    let root = a.let_(LetKind::Strict, f, function, exports);
    let mut compiler = LambdaCompiler::new();
    let (_, check) = compiler.compile_deps_program_with_lower_check::<true>(a, root, Default::default());
    let Some(LowerCheck::Supported(pair)) = check else { panic!("supported unit") };
    let stats = pair.stats.decisions;
    agrees(&stats);
    assert_eq!((stats.decision_rows, stats.decision_inline), (1, 0));
}

#[test]
fn ten_thousand_declarations_close_in_three_steps_each() {
    // A run of 10,000 declarations: `f_i = p => ext(p)` and
    // `g_i = () => f_i(1)`, alternating; every `f_i` has one use, the tail
    // call of `g_i`. `close::decide` takes one step per declaration and two
    // per function body (its `return` and the call it returns).
    use crate::lambda::LamLoc;
    let mut a = LamArena::new();
    let mut root = a.const_(C::JsNull);
    for i in (0..5_000).rev() {
        let (f, g, p) = (Ident::new("f", 3 * i + 1, IdentFlags::NONE), Ident::new("g", 3 * i + 2, IdentFlags::NONE), Ident::new("p", 3 * i + 3, IdentFlags::NONE));
        let (ext, read) = (a.var(Ident::new("ext", 20_000, IdentFlags::NONE)), a.var(p));
        let value = call(&mut a, ext, &[read]);
        let callee_function = a.function_(1, &[p], value, Default::default(), LamLoc::NONE);
        let (callee, one) = (a.var(f), a.const_(C::Int { i: 1, comment: None }));
        let applied = call(&mut a, callee, &[one]);
        let caller = a.function_(0, &[], applied, Default::default(), LamLoc::NONE);
        root = a.let_(LetKind::Strict, g, caller, root);
        root = a.let_(LetKind::Strict, f, callee_function, root);
    }
    let input = bridge::import_lambda(&a, root).unwrap();
    let source_root = input.root;
    let mut state = State::new(input);
    let probed = state.probe(Cx::value(), source_root).unwrap();
    let lowered = state.complete(Cx::value(), probed);
    let scope = lowered.program.arena.js_scope.as_ref().unwrap();
    assert_eq!(scope.decisions.len(), 10_000);
    assert_eq!(scope.decisions.iter().filter(|decision| decision.inline()).count(), 5_000);
    // 10,000 declarations and the sentinel statement, 10,000 bodies.
    assert_eq!(lowered.switch_stats.close_steps, 10_001 + 2 * 10_000);
}

#[test]
fn a_pure_branch_the_flatten_pass_drops_takes_an_occurrence_built_still_counts() {
    // THREE_TREES.md 11.4, "T4c design" (b), first hazard.
    // `c => { let x = ext(); ignore(c ? x : ext()); 3 }`: the lowering writes
    // the expression statement `c ? x : ext();`. P1 drops the branch `x`
    // (`if (!c) { ext(); }`), so P3 counts no use of `x` and makes the
    // declaration an expression statement; `built` is still one.
    use crate::js_ir::op::UsedStats;
    use crate::lambda::LamLoc;
    use crate::lambda::lam_primitive::Primitive;
    let build = |a: &mut LamArena| {
        let (c, x) = (Ident::new("c", 12, IdentFlags::NONE), Ident::new("x", 14, IdentFlags::NONE));
        let ext = Ident::new("ext", 13, IdentFlags::NONE);
        let callee = a.var(ext);
        let effect = call(a, callee, &[]);
        let (test, read) = (a.var(c), a.var(x));
        let chosen = a.if_(test, read, effect);
        let ignored = a.prim_raw(Primitive::Pignore, &[chosen], LamLoc::NONE);
        let three = a.const_(C::Int { i: 3, comment: None });
        let body = a.seq_raw(ignored, three);
        let callee = a.var(ext);
        let value = call(a, callee, &[]);
        let body = a.let_(LetKind::Strict, x, value, body);
        a.function_(1, &[c], body, Default::default(), LamLoc::NONE)
    };
    assert!(legacy_text(build, &[]).contains("  let x = ext();\n  c ? x : ext();\n  return 3;\n"));
    assert!(legacy_text(build, &[1, 2, 3, 4, 5, 6]).contains("  ext();\n  if (!c) {\n    ext();\n  }\n  return 3;\n"));
    let (stats, rows) = step_a(build);
    // The lowering's decision, from `built`: used once (and not pure).
    assert_eq!(rows, vec![("x".to_string(), UsedStats::Used, false, 1)]);
    // The legacy pass counts zero after P1: one count and one status differ.
    assert_eq!((stats.decision_count_differences, stats.decision_status_differences), (1, 1));
}

#[test]
fn a_copied_function_doubles_the_legacy_count_of_the_variables_declared_inside_it() {
    // THREE_TREES.md 11.4, "T4c design" (b), second hazard.
    // `() => { let g = p => ext(p); g(1) }`, then the function value copied
    // as the J normaliser copies a repeated pure function (`copy_j`): the
    // copy's `g` is a variable of its own that prints as the original. The
    // run inside the function closed before the copy: `g` was decided an
    // inline candidate with `built` one. P3 counts the identifier: two.
    use crate::js_ir::op::UsedStats;
    use crate::lambda::LamLoc;
    use crate::lambda::js_pass_external_shadow::apply_external_shadow_pass as shadow;
    use crate::lambda::js_pass_flatten_and_mark_dead::apply_js_flatten_pass as flatten;
    let mut a = LamArena::new();
    let (g, p) = (Ident::new("g", 10, IdentFlags::NONE), Ident::new("p", 11, IdentFlags::NONE));
    let (ext, read) = (a.var(Ident::new("ext", 13, IdentFlags::NONE)), a.var(p));
    let value = call(&mut a, ext, &[read]);
    let function = a.function_(1, &[p], value, Default::default(), LamLoc::NONE);
    let (callee, one) = (a.var(g), a.const_(C::Int { i: 1, comment: None }));
    let applied = call(&mut a, callee, &[one]);
    let body = a.let_(LetKind::Strict, g, function, applied);
    let root = a.function_(0, &[], body, Default::default(), LamLoc::NONE);
    let input = bridge::import_lambda(&a, root).unwrap();
    let source_root = input.root;
    let mut state = State::new(input);
    let probed = state.probe(Cx::value(), source_root).unwrap();
    let out = state.realize(Cx::value(), probed);
    let copy = crate::bir::j::logic::copy_j(&mut state.arena, out.value.unwrap());
    let statement = state.arena.new_node(View::SExp { value: copy }, 0);
    state.statements.push(statement);
    let lowered = state.complete(Cx::value(), Probed::Out(out));
    lowered.program.arena.validate(Some(lowered.program.root)).unwrap();
    let scope = lowered.program.arena.js_scope.as_ref().unwrap();
    let origin = |var: usize| lowered.program.arena.vars.j_origin[var].index();
    let copies: Vec<usize> = (0..scope.uses.len()).filter(|&var| lowered.program.idents[origin(var)] == g).collect();
    // Two variables print as `g`; each has one occurrence.
    assert_eq!(copies.len(), 2);
    assert!(copies.iter().all(|&var| scope.uses[var].built == 1));
    // One decision, taken before the copy: an inline candidate.
    let decisions: Vec<_> = scope.decisions.iter().map(|decision| (lowered.program.idents[origin(decision.var.index())], *decision)).collect();
    assert_eq!(decisions.len(), 1);
    assert_eq!((decisions[0].1.status(), decisions[0].1.inline(), decisions[0].1.built()), (UsedStats::OncePure as u32, true, 1));
    // The legacy pass on the same program: `g` is used twice, no candidate.
    let program = shadow(flatten(bridge_j::export_js(&lowered.program).unwrap()));
    let legacy = crate::lambda::js_pass_tailcall_inline::decisions(&program.program);
    assert_eq!(legacy[&g], (UsedStats::Used, 2, false));
    let stats = crate::bir::shadow::compare_decisions(&decisions, &program.program);
    assert_eq!((stats.decision_count_differences, stats.decision_status_differences, stats.decision_inline, stats.decision_legacy_inline), (1, 1, 1, 0));
}

#[test]
fn ten_thousand_return_sites_are_read_in_two_steps_each() {
    // One `return` of 10,000 nested conditionals, each with a call of its own
    // callee in one branch: `scope::return_sites` takes one step per
    // conditional and one per call, and records every callee's site.
    use crate::lambda::LamLoc;
    let mut a = LamArena::new();
    let callee = a.var(Ident::new("f", 1, IdentFlags::NONE));
    let mut root = call(&mut a, callee, &[]);
    for i in 0..10_000 {
        let test = a.var(Ident::new("c", 20_000, IdentFlags::NONE));
        let callee = a.var(Ident::new("f", i + 2, IdentFlags::NONE));
        let applied = call(&mut a, callee, &[]);
        root = a.if_(test, applied, root);
    }
    let root = a.function_(0, &[], root, Default::default(), LamLoc::NONE);
    let input = bridge::import_lambda(&a, root).unwrap();
    let source_root = input.root;
    let mut state = State::new(input);
    let probed = state.probe(Cx::value(), source_root).unwrap();
    let lowered = state.complete(Cx::value(), probed);
    let scope = lowered.program.arena.js_scope.as_ref().unwrap();
    let sites = scope.facts.iter().filter(|facts| facts.site != super::scope::VarFacts::NO_SITE).count();
    assert_eq!(sites, 10_001);
    // 10,000 conditionals and 10,001 calls, the `return`, the sentinel.
    assert_eq!(lowered.switch_stats.close_steps, 10_000 + 10_001 + 2);
    assert_eq!(lowered.switch_stats.statements_copied, 2);
}

#[test]
fn a_declaration_is_decided_once_per_copy_of_its_statement() {
    // `close::decide` runs where a list is copied, so a statement the
    // lowering moves and copies again is decided again: the number of
    // decisions is bounded by `StatementStack::copied`, not by the number of
    // declarations. 10,000 nested `if c { let y = ext(); y } else { ... }`:
    // every declaration is copied, and decided, once here.
    use crate::lambda::LamLoc;
    let mut a = LamArena::new();
    let ext = Ident::new("ext", 6, IdentFlags::NONE);
    let mut root = a.const_(C::Int { i: 1, comment: None });
    for i in 0..10_000 {
        let test = a.var(Ident::new("c", 5, IdentFlags::NONE));
        let callee = a.var(ext);
        let effect = call(&mut a, callee, &[]);
        let y = Ident::new("y", 1000 + i, IdentFlags::NONE);
        let read = a.var(y);
        let yes = a.let_(LetKind::Strict, y, effect, read);
        root = a.if_(test, yes, root);
    }
    let root = a.function_(0, &[], root, Default::default(), LamLoc::NONE);
    let input = bridge::import_lambda(&a, root).unwrap();
    let source_root = input.root;
    let mut state = State::new(input);
    let probed = state.probe(Cx::value(), source_root).unwrap();
    let lowered = state.complete(Cx::value(), probed);
    let scope = lowered.program.arena.js_scope.as_ref().unwrap();
    let stats = lowered.switch_stats;
    assert_eq!(scope.decisions.len(), 10_000);
    assert!(scope.decisions.len() <= stats.statements_copied);
    // One step per copied statement and one per returned value.
    assert!(stats.close_steps <= 2 * stats.statements_copied, "{} steps, {} copied", stats.close_steps, stats.statements_copied);
}

#[test]
fn cached_external_templates_keep_fresh_binders_and_import_once() {
    use crate::cmi::persistent_env::CmjExportArity;
    use crate::lambda::{ApInfo, ApplyStatus, FieldDbgInfo, LamLoc, Lambda, lam_arity::Arity, lam_primitive::Primitive};
    for (copied, width) in [(false, 1), (true, 1), (true, 16)] {
        let params: Vec<_> = (0..width).map(|i| Ident::new("arg", 100 + i, IdentFlags::NONE)).collect();
        let local = Ident::new("local", 200, IdentFlags::NONE);
        let mut body = LamArena::new();
        let value = body.var(params[0]);
        let body_root = if copied {
            let init = body.prim_raw(Primitive::PinitMod, &[value], LamLoc::NONE);
            let mut uses = vec![body.var(local), body.var(local)];
            uses.extend(params[1..].iter().map(|&p| body.var(p)));
            let result = body.prim_raw(Primitive::Pmakearray, &uses, LamLoc::NONE);
            body.let_(LetKind::Strict, local, init, result)
        } else { value };
        let resolver = crate::js_ir::ModulePathResolver::from_compile_options(None, None, None, None, None, None, false);
        resolver.set_bir_test_export("Other", "run", CmjExportArity::Single(Arity::info(vec![width], false)),
            Some(Lambda::function_(width, params, body.export(body_root), Default::default(), LamLoc::NONE)));
        for count in [2, 10_000] {
            let mut a = LamArena::new();
            let calls: Vec<_> = (0..count).map(|i| {
                let module = a.global_module(Ident::create_persistent("Other"));
                let callee = a.prim_raw(Primitive::Pfield(0, FieldDbgInfo::Module { name: "run".into() }), &[module], LamLoc::NONE);
                let args: Vec<_> = (0..width).map(|j| {
                    let arg = a.const_(C::Int { i: i + j, comment: None });
                    if width > 1 && j % 3 == 0 { a.prim_raw(Primitive::PinitMod, &[arg], LamLoc::NONE) } else { arg }
                }).collect();
                a.apply_raw(callee, &args, ApInfo { status: ApplyStatus::Na, loc: LamLoc::NONE })
            }).collect();
            let root = a.prim_raw(Primitive::Pmakearray, &calls, LamLoc::NONE);
            if count == 2 { compare_oracle(a.clone(), root, Some(&resolver), true, &[0,1,2,3,4], None, true); }
            let input = bridge::import_lambda(&a, root).unwrap(); let root = input.root;
            let mut state = State::new(input); state.cross_module_inline = true; state.resolver = Some(resolver.clone());
            let out = state.probe(Cx::returning(), root).unwrap(); let out = state.realize(Cx::returning(), out);
            assert_eq!(state.inline_imports, 1); assert_eq!(state.inline_reductions, count as usize);
            assert_eq!(state.inline_templates.len(), 1); assert_eq!(state.inline_param_stats.len(), width as usize);
            assert!(state.inline_foreign.is_empty() && state.inline_engine.stats.renames.is_empty());
            for node in state.statements.statements(out.stmts) { state.arena.release(node); }
            if let Some(value) = out.value { state.arena.release(value); }
            state.statements.kill(out.stmts);
        }
    }
}

/// The new side of the gate on the function `build` gives, bound to an
/// exported `run`: lowered, the references the lowering marked written as
/// `globalThis.name` (`bridge_j::qualify`), then the legacy passes `order`
/// names (as `legacy_text`), printed. `order` never holds pass 2 here: the
/// new side runs no external-shadow pass (THREE_TREES 11.4, "T5 design").
fn new_text(build: impl Fn(&mut LamArena) -> Lam, resolver: Option<&crate::js_ir::ModulePathResolver>, order: &[u8]) -> (String, usize) {
    use crate::lambda::js_pass_flatten_and_mark_dead::{apply_js_flatten_and_mark_dead_pass as dead, apply_js_flatten_pass as flatten};
    let mut a = LamArena::new();
    let root = build(&mut a);
    let exported = Ident::new("run", 900, IdentFlags::NONE);
    let mut input = bridge::import_lambda(&a, root).unwrap();
    let var = input.arena.new_var_id(exported.name_atom(), exported.stamp() as u32);
    input.idents.push(exported);
    let source_root = input.root;
    let mut state = State::new(input);
    state.resolver = resolver.cloned();
    let cx = Cx::declare(LetKind::Strict, var);
    let probed = state.probe(cx, source_root).unwrap();
    // As `bir_lower_oracle`: the statements, without a value.
    let out = state.realize(cx, probed);
    let run = state.statements.since(Span { start: out.stmts.start, len: 0 });
    let list = state.statements.take_list(&mut state.arena, run);
    let lowered = state.finish(list, out.finished, Default::default());
    lowered.program.arena.validate(Some(lowered.program.root)).unwrap();
    let bridge_j::Exported { mut program, qualified } = bridge_j::export_lowered(&lowered.program).unwrap();
    bridge_j::qualify(&mut program, &qualified);
    let mut program = JsDepsProgram { program: JsProgram::new_in(program.program.block, vec![exported], program.program.arena), modules: vec![], side_effect: None };
    for pass in order {
        program = match pass {
            1 => flatten(program),
            3 => crate::lambda::js_pass_tailcall_inline::apply_js_tailcall_inline_pass(program),
            4 => crate::lambda::js_pass_record_rest::apply_js_record_rest_pass(program),
            5 => dead(program, false),
            6 => crate::lambda::js_shake::apply_js_shake_pass(program),
            _ => unreachable!("pass number"),
        };
    }
    (crate::js_ir::print_deps_program_with_directives_and_options(&program, None, &[], false, false, false), qualified.len())
}

/// The oracle form of one external-shadow rule: the new side without pass 2
/// prints what the legacy side prints with it, after the flatten pass alone
/// and after all passes. Returns the final text and the number of
/// references the lowering marked.
fn shadow_rule(build: impl Fn(&mut LamArena) -> Lam + Copy) -> (String, usize) {
    assert_eq!(new_text(build, None, &[1]).0, legacy_text(build, &[1, 2]));
    let (text, marked) = new_text(build, None, &[1, 3, 4, 5, 6]);
    assert_eq!(text, legacy_text(build, &[1, 2, 3, 4, 5, 6]));
    (text, marked)
}

fn js_global(a: &mut LamArena, name: &str) -> Lam {
    a.var(Ident::create_js(name))
}

fn ext_call(a: &mut LamArena, args: &[Lam]) -> Lam {
    let ext = a.var(Ident::new("ext", 13, IdentFlags::NONE));
    call(a, ext, args)
}

#[test]
fn the_lowering_decides_the_shadowed_global_the_tail_call_pass_would_hide() {
    // THREE_TREES.md 11.4, "T4c design" (c), first counterexample, on the
    // new side: lowered, then P1, P3, P4, P5, P6 and no P2. The parameter
    // `location` is around the reference when the lowering decides, so the
    // reference is qualified although P3 then removes the parameter.
    use crate::lambda::LamLoc;
    let build = |a: &mut LamArena| {
        let (g, p, arg) = (Ident::new("g", 10, IdentFlags::NONE), Ident::new("location", 11, IdentFlags::NONE), Ident::new("a", 12, IdentFlags::NONE));
        let (read, global) = (a.var(p), js_global(a, "location"));
        let body = ext_call(a, &[read, global]);
        let function = a.function_(1, &[p], body, Default::default(), LamLoc::NONE);
        let callee = a.var(g);
        let x = a.var(arg);
        let applied = call(a, callee, &[x]);
        let inner = a.let_(LetKind::Strict, g, function, applied);
        a.function_(1, &[arg], inner, Default::default(), LamLoc::NONE)
    };
    let (text, marked) = new_text(build, None, &[1, 3, 4, 5, 6]);
    assert_eq!(text, "\n\n\nfunction run(a) {\n  return ext(a, globalThis.location);\n}\n\nexport {\n  run,\n}\n/* No side effect */\n");
    assert_eq!(marked, 1);
    assert_eq!(text, legacy_text(build, &[1, 2, 3, 4, 5, 6]));
}

#[test]
fn a_declaration_the_tail_call_pass_moves_into_the_list_of_a_global_reference_leaves_it_plain() {
    // The reverse case: `run = a => { let g = p => { let location = ext(p);
    // ext(location, p) }; ext(<global location>); return g(a) }`. When the
    // lowering decides, `let location` is in the callee's list and the
    // caller's reference is not below it: plain. P3 then moves the
    // declaration into the caller's list; the reference stays plain, as in
    // the legacy order.
    use crate::lambda::LamLoc;
    let build = |a: &mut LamArena| {
        let (g, p, arg, local) = (Ident::new("g", 10, IdentFlags::NONE), Ident::new("p", 11, IdentFlags::NONE), Ident::new("a", 12, IdentFlags::NONE), Ident::new("location", 14, IdentFlags::NONE));
        let read = a.var(p);
        let value = ext_call(a, &[read]);
        let (first, second) = (a.var(local), a.var(p));
        let result = ext_call(a, &[first, second]);
        let body = a.let_(LetKind::Strict, local, value, result);
        let function = a.function_(1, &[p], body, Default::default(), LamLoc::NONE);
        let global = js_global(a, "location");
        let effect = ext_call(a, &[global]);
        let callee = a.var(g);
        let x = a.var(arg);
        let applied = call(a, callee, &[x]);
        let rest = a.seq_raw(effect, applied);
        let inner = a.let_(LetKind::Strict, g, function, rest);
        a.function_(1, &[arg], inner, Default::default(), LamLoc::NONE)
    };
    let (text, marked) = shadow_rule(build);
    assert_eq!(marked, 0);
    assert_eq!(text, "\n\n\nfunction run(a) {\n  ext(location);\n  let location$1 = ext(a);\n  return ext(location$1, a);\n}\n\nexport {\n  run,\n}\n/* No side effect */\n");
}

#[test]
fn a_declaration_after_the_reference_in_the_same_list_shadows_it() {
    // `run = () => { ext(<global location>); let location = ext(); return ext(location) }`.
    use crate::lambda::LamLoc;
    let build = |a: &mut LamArena| {
        let local = Ident::new("location", 14, IdentFlags::NONE);
        let global = js_global(a, "location");
        let effect = ext_call(a, &[global]);
        let value = ext_call(a, &[]);
        let read = a.var(local);
        let result = ext_call(a, &[read]);
        let declared = a.let_(LetKind::Strict, local, value, result);
        let body = a.seq_raw(effect, declared);
        a.function_(0, &[], body, Default::default(), LamLoc::NONE)
    };
    let (text, marked) = shadow_rule(build);
    assert_eq!(marked, 1);
    assert!(text.contains("  ext(globalThis.location);\n  let location = ext();\n"), "{text}");
}

#[test]
fn a_parameter_shadows_the_global_in_the_function_and_not_beside_it() {
    // `run = () => { ext(location => ext(location, <global location>)); return ext(<global location>) }`.
    use crate::lambda::LamLoc;
    let build = |a: &mut LamArena| {
        let p = Ident::new("location", 11, IdentFlags::NONE);
        let (read, global) = (a.var(p), js_global(a, "location"));
        let inner = ext_call(a, &[read, global]);
        let function = a.function_(1, &[p], inner, Default::default(), LamLoc::NONE);
        let effect = ext_call(a, &[function]);
        let global = js_global(a, "location");
        let result = ext_call(a, &[global]);
        let body = a.seq_raw(effect, result);
        a.function_(0, &[], body, Default::default(), LamLoc::NONE)
    };
    let (text, marked) = shadow_rule(build);
    assert_eq!(marked, 1);
    assert!(text.contains("ext(location, globalThis.location)"), "{text}");
    assert!(text.contains("  return ext(location);\n"), "{text}");
}

#[test]
fn a_loop_variable_shadows_the_global_in_the_loop() {
    // `run = () => { for location = 0 to ext(<global location>) { ext(<global location>) }; return ext(<global location>) }`.
    use crate::lambda::{DirectionFlag, LamLoc};
    let build = |a: &mut LamArena| {
        let index = Ident::new("location", 11, IdentFlags::NONE);
        let start = a.const_(C::Int { i: 0, comment: None });
        let bound = js_global(a, "location");
        let finish = ext_call(a, &[bound]);
        let inside = js_global(a, "location");
        let effect = ext_call(a, &[inside]);
        let looped = a.for_(index, start, finish, DirectionFlag::Upto, effect);
        let after = js_global(a, "location");
        let result = ext_call(a, &[after]);
        let body = a.seq_raw(looped, result);
        a.function_(0, &[], body, Default::default(), LamLoc::NONE)
    };
    let (text, marked) = shadow_rule(build);
    assert!(marked >= 1, "{text}");
    assert!(text.contains("    ext(globalThis.location);\n"), "{text}");
    assert!(text.contains("  return ext(location);\n"), "{text}");
}

#[test]
fn a_catch_variable_shadows_the_global_in_the_handler() {
    // `run = () => { try { ext(<global location>) } catch location { ext(location, <global location>) } }`.
    use crate::lambda::LamLoc;
    let build = |a: &mut LamArena| {
        let exception = Ident::new("location", 11, IdentFlags::NONE);
        let tried = js_global(a, "location");
        let body = ext_call(a, &[tried]);
        let (read, global) = (a.var(exception), js_global(a, "location"));
        let handler = ext_call(a, &[read, global]);
        let whole = a.try_(body, exception, handler);
        a.function_(0, &[], whole, Default::default(), LamLoc::NONE)
    };
    let (text, marked) = shadow_rule(build);
    assert_eq!(marked, 1);
    assert!(text.contains("ext(location);\n"), "{text}");
    assert!(text.contains(", globalThis.location)"), "{text}");
}

#[test]
fn a_declaration_in_one_case_of_a_switch_shadows_the_global_in_its_sibling_cases_and_not_in_the_discriminant() {
    // `run = x => switch ext(x, <global location>) { | 0 => { let location = ext(); ext(location, location) }
    // | 1 => ext(<global location>) | 2 => 2 | 3 => 3 }`.
    use crate::lambda::{LamLoc, SwitchDispatch, SwitchKey};
    let build = |a: &mut LamArena| {
        let (x, local) = (Ident::new("x", 10, IdentFlags::NONE), Ident::new("location", 14, IdentFlags::NONE));
        let (read, global) = (a.var(x), js_global(a, "location"));
        let scrutinee = ext_call(a, &[read, global]);
        let value = ext_call(a, &[]);
        let (first, second) = (a.var(local), a.var(local));
        let used = ext_call(a, &[first, second]);
        let zero = a.let_(LetKind::Strict, local, value, used);
        let sibling = js_global(a, "location");
        let one = ext_call(a, &[sibling]);
        let two = a.const_(C::Int { i: 2, comment: None });
        let three = a.const_(C::Int { i: 3, comment: None });
        let actions = a.add_list(&[zero, one, two, three]);
        let info = a.add_switch(true, (0..4).map(SwitchKey::Int), false, std::iter::empty(), false, SwitchDispatch::Direct);
        let body = a.switch_raw(scrutinee, actions, info);
        a.function_(1, &[x], body, Default::default(), LamLoc::NONE)
    };
    let (text, marked) = shadow_rule(build);
    assert_eq!(marked, 1, "{text}");
    assert!(text.contains("switch (ext(x, location)) {"), "{text}");
    assert!(text.contains("return ext(globalThis.location);"), "{text}");
}

#[test]
fn an_imported_module_shadows_the_global_of_its_name_everywhere() {
    // `run = () => ext(Other.run, <global Other>)`.
    use crate::cmi::persistent_env::CmjExportArity;
    use crate::js_ir::ModulePathResolver;
    use crate::lambda::{FieldDbgInfo, LamLoc, lam_arity::Arity, lam_primitive::Primitive};
    let resolver = ModulePathResolver::from_compile_options(None, None, None, None, None, None, false);
    resolver.set_bir_test_export("Other", "run", CmjExportArity::Single(Arity::info(vec![1], false)), None);
    let build = |a: &mut LamArena| {
        let module = a.global_module(Ident::create_persistent("Other"));
        let field = a.prim_raw(Primitive::Pfield(0, FieldDbgInfo::Module { name: crate::name::Name::new("run") }), &[module], LamLoc::NONE);
        let global = js_global(a, "Other");
        let body = ext_call(a, &[field, global]);
        a.function_(0, &[], body, Default::default(), LamLoc::NONE)
    };
    let (text, marked) = new_text(build, Some(&resolver), &[1, 3, 4, 5, 6]);
    assert_eq!(marked, 1);
    assert!(text.contains("return ext(Other.run, globalThis.Other);"), "{text}");
}

#[test]
fn a_module_whose_only_reference_the_flatten_pass_drops_still_shadows_the_global_of_its_name() {
    // THREE_TREES.md 11.4, "T5 design" (a), the hazard: `run = c => {
    // ignore(c ? Other.run : ext()); return ext(<global Other>) }`. The
    // lowering counts one live reference to the module `Other` and
    // qualifies the global; P1 drops the pure branch `Other.run`, so the
    // legacy external-shadow pass, after P1, sees no reference to the
    // module and leaves the global plain. Both texts are pinned.
    use crate::cmi::persistent_env::CmjExportArity;
    use crate::js_ir::ModulePathResolver;
    use crate::lambda::{FieldDbgInfo, LamLoc, lam_arity::Arity, lam_primitive::Primitive};
    let resolver = ModulePathResolver::from_compile_options(None, None, None, None, None, None, false);
    resolver.set_bir_test_export("Other", "run", CmjExportArity::Single(Arity::info(vec![1], false)), None);
    let build = |a: &mut LamArena| {
        let c = Ident::new("c", 12, IdentFlags::NONE);
        let module = a.global_module(Ident::create_persistent("Other"));
        let field = a.prim_raw(Primitive::Pfield(0, FieldDbgInfo::Module { name: crate::name::Name::new("run") }), &[module], LamLoc::NONE);
        let test = a.var(c);
        let other = ext_call(a, &[]);
        let chosen = a.if_(test, field, other);
        let ignored = a.prim_raw(Primitive::Pignore, &[chosen], LamLoc::NONE);
        let global = js_global(a, "Other");
        let result = ext_call(a, &[global]);
        let body = a.seq_raw(ignored, result);
        a.function_(1, &[c], body, Default::default(), LamLoc::NONE)
    };
    let (new, marked) = new_text(build, Some(&resolver), &[1, 3, 4, 5, 6]);
    let legacy = legacy_text(build, &[1, 2, 3, 4, 5, 6]);
    assert_eq!(marked, 1);
    // The new side: qualified.
    assert_eq!(new, "\n\n\nfunction run(c) {\n  if (!c) {\n    ext();\n  }\n  return ext(globalThis.Other);\n}\n\nexport {\n  run,\n}\n/* No side effect */\n");
    // The legacy side: the global stays plain.
    assert_eq!(legacy, "\n\n\nfunction run(c) {\n  if (!c) {\n    ext();\n  }\n  return ext(Other);\n}\n\nexport {\n  run,\n}\n/* No side effect */\n");
}

/// THREE_TREES 11.4, "T5 part B as redesigned": the naming log of the unit
/// `root` against the pass. Lowers the Lambda as a unit (`inline` as
/// `compare_oracle` takes it), replays the log (`names::replay`, at
/// `State::finish`), and compares with `emit::naming::compare_with_pass` on
/// the lowering's own exported program. Returns the comparison and what the
/// replay did. Panics when the lowering or the pass does not support the
/// unit.
fn names_of(arena: LamArena, root: Lam, resolver: Option<&crate::js_ir::ModulePathResolver>, inline: bool, jsx_preserve: bool) -> (crate::emit::NameStats, names::Replayed) {
    compared_names(arena, root, resolver, inline, jsx_preserve).expect("the pass supports the unit")
}

/// `names_of`, or `None` when the pass does not support the unit. Every
/// module the unit reads gets a path, as in a build: the default resolver
/// of a test resolves no module of its own, and the pass names a module
/// that is not imported where it is used, which a built unit does not
/// have.
fn compared_names(arena: LamArena, root: Lam, resolver: Option<&crate::js_ir::ModulePathResolver>, inline: bool, jsx_preserve: bool) -> Option<(crate::emit::NameStats, names::Replayed)> {
    let mut resolver = resolver.cloned().unwrap_or_else(|| {
        crate::js_ir::ModulePathResolver::from_compile_options(None, None, None, None, None, None, false)
    });
    let globals = bridge::import_for_lowering(&arena, root).0.expect("lowering input").into_imported().globals;
    for id in globals {
        let module = crate::js_ir::ModuleId { id, kind: crate::js_ir::op::Kind::Ml, dynamic_import: false };
        if resolver.resolve_module_path(&module).is_none() {
            resolver.set_module_path_override(id.name(), format!("./{}.js", id.name()));
        }
    }
    let resolver = &resolver;
    let mut lowered = lower_for_names(&arena, root, resolver, inline, jsx_preserve);
    // The variables' names are in the arena's column (`State::replay_names`).
    lowered.printed.names = lowered.program.arena.vars.printed.clone();
    let bir = &lowered.program.arena;
    let idents: Vec<Ident> = (0..bir.vars.len())
        .map(|var| lowered.program.idents[bir.vars.j_origin[var].index()])
        .collect();
    let modules: Vec<Ident> = bir.pools.j_modules.iter().map(|module| module.id).collect();
    let free = names::free_lists(bir, &lowered.program.idents);
    let exported = bridge_j::export_lowered(&lowered.program).expect("lowered program exports").program;
    let mut program = LambdaCompiler::bir_coerced_program(
        exported.program.arena,
        exported.program.block,
        lowered.coerced.exports.clone(),
        lowered.coerced.reservations.clone(),
    );
    program.modules = lowered.name_imports.iter().map(|import| bir.pools.j_modules[import.index()].clone()).collect();
    let stats = crate::emit::compare_with_pass(&lowered.printed, &idents, &modules, &free, &program, resolver, jsx_preserve).ok()?;
    // Shown when an assertion of the caller fails: the text the pass names
    // and the replay's names by variable and by import.
    println!("{}", crate::js_ir::print_deps_program_with_directives_and_options(&program, None, &[], false, false, false));
    for (var, name) in lowered.printed.names.iter().enumerate() {
        println!("replay: {:?} -> {name:?}", idents[var]);
    }
    for (import, name) in lowered.printed.modules.iter().enumerate() {
        println!("replay: {:?} -> {name:?}", modules[import]);
    }
    let mut start = 0;
    for &end in &free.ends {
        println!("replay free: {:?}", &free.idents[start..end as usize]);
        start = end as usize;
    }
    if let Ok((pass_free, pass_names)) = crate::emit::pass_tables(&program, resolver, jsx_preserve) {
        for list in pass_free {
            println!("pass free: {list:?}");
        }
        for (ident, name) in pass_names {
            println!("pass: {ident:?} -> {name:?}");
        }
    }
    Some((stats, lowered.switch_stats.replayed))
}

/// `root` as a unit: a rule test's root reads variables it does not bind,
/// which no unit does (the pass names such a variable where it is used;
/// the replay names binders only, `names::replay`). The root becomes the
/// body of `let unit = (free...) => root`, its free variables with a stamp
/// (in `Ident`'s order) the parameters; a root without one is a unit as it
/// is. Stamp zero (JavaScript globals, modules) stays free.
fn unit_of(mut arena: LamArena, root: Lam) -> (LamArena, Lam) {
    let mut free: Vec<Ident> = crate::lambda::lam_analysis::free_variables(&arena, root)
        .into_iter()
        .filter(|ident| ident.stamp() != 0)
        .collect();
    if free.is_empty() {
        return (arena, root);
    }
    free.sort();
    let unit = Ident::new("unit", arena.ident_stamp_bound() + 2, IdentFlags::NONE);
    let function = arena.function_(free.len() as i32, &free, root, Default::default(), crate::lambda::LamLoc::NONE);
    let end = arena.var(unit);
    let closed = arena.let_(LetKind::Strict, unit, function, end);
    (arena, closed)
}

/// `root` lowered as a unit (`lower_with_resolver`), as `names_of` and
/// `adopted_nodes_of` read it.
fn lower_for_names(arena: &LamArena, root: Lam, resolver: &crate::js_ir::ModulePathResolver, inline: bool, jsx_preserve: bool) -> Lowered {
    let input = bridge::import_for_lowering(arena, root).0.expect("lowering input");
    lower_with_resolver(input, None, false, Some(resolver), inline, true, jsx_preserve).expect("the lowering supports the unit")
}

/// `Log::adopted_nodes` of `root` lowered as a unit: whether an input
/// reaches a site of G10 (`names::adopt`).
fn adopted_nodes_of(arena: LamArena, root: Lam, resolver: Option<&crate::js_ir::ModulePathResolver>) -> usize {
    let default = crate::js_ir::ModulePathResolver::from_compile_options(None, None, None, None, None, None, false);
    let lowered = lower_for_names(&arena, root, resolver.unwrap_or(&default), false, false);
    lowered.program.arena.js_scope.as_ref().expect("lowering scope").names.adopted_nodes
}

/// The log and the pass agree on `root`: every name, every cached bound,
/// every free list; no reservation whose order is in question, no
/// reference the replay left unnamed.
fn names_agree(arena: LamArena, root: Lam, resolver: Option<&crate::js_ir::ModulePathResolver>, inline: bool) -> crate::emit::NameStats {
    names_agree_printing(arena, root, resolver, inline, false)
}

/// `names_agree` for a unit that prints JSX through the runtime
/// (`jsx_preserve` false) or preserves it.
fn names_agree_printing(arena: LamArena, root: Lam, resolver: Option<&crate::js_ir::ModulePathResolver>, inline: bool, jsx_preserve: bool) -> crate::emit::NameStats {
    let (stats, replayed) = names_of(arena, root, resolver, inline, jsx_preserve);
    assert_eq!((stats.name_differences, stats.finish_differences, stats.free_differences), (0, 0, 0), "{stats:?}");
    assert_eq!((replayed.ambiguous_orders, replayed.unnamed_references), (0, 0), "{replayed:?}");
    assert_eq!(stats.names_replayed, stats.names_pass, "{stats:?}");
    stats
}

#[test]
fn the_naming_log_agrees_on_a_function_whose_unit_parameter_is_dropped() {
    // Gap 2: `let f = (unit) => { mutable = null }` with `one_unit_arg`: the
    // literal gets a header without the parameter after its body was
    // lowered (`finish_expression`). `f` and nothing else is named.
    use crate::lambda::LamLoc;
    let mut a = LamArena::new();
    let (f, unit, mutable) = (Ident::new("f", 1, IdentFlags::NONE), Ident::new("unit", 2, IdentFlags::NONE), Ident::new("mutable", 3, IdentFlags::NONE));
    let null = a.const_(C::JsNull);
    let assignment = a.assign(mutable, null);
    let attr = crate::lambda::FunctionAttribute { one_unit_arg: true, ..Default::default() };
    let function = a.function_(1, &[unit], assignment, attr, LamLoc::NONE);
    let end = a.var(f);
    let body = a.let_(LetKind::Strict, f, function, end);
    let initial = a.const_(C::JsNull);
    let root = a.let_(LetKind::Variable, mutable, initial, body);
    let stats = names_agree(a, root, None, false);
    assert_eq!(stats.names_pass, 2);
}

#[test]
fn the_naming_log_agrees_on_the_aliases_of_a_tail_call_loop() {
    // Gap 2: `let rec loop = (i, acc) => { later(() => i + acc); loop(i + 1, acc) }`.
    // The closure captures the parameters, so the tail-call rewrite gives
    // the header copies of them and declares the originals inside the loop
    // (`loop_function_body`), after the body was lowered.
    use crate::lambda::lam_primitive::Primitive as P;
    use crate::lambda::LamLoc;
    let mut a = LamArena::new();
    let ident = |name: &str, stamp: i32| Ident::new(name, stamp, IdentFlags::NONE);
    let (f, i, acc, later) = (ident("loop", 1), ident("i", 2), ident("acc", 3), ident("later", 4));
    let (left, right) = (a.var(i), a.var(acc));
    let captured = a.prim_raw(P::Paddint, &[left, right], LamLoc::NONE);
    let closure = a.function_(0, &[], captured, Default::default(), LamLoc::NONE);
    let callee = a.var(later);
    let effect = call(&mut a, callee, &[closure]);
    let (left, one) = (a.var(i), a.const_(C::Int { i: 1, comment: None }));
    let next = a.prim_raw(P::Paddint, &[left, one], LamLoc::NONE);
    let (callee, same) = (a.var(f), a.var(acc));
    let again = call(&mut a, callee, &[next, same]);
    let body = a.seq_raw(effect, again);
    let function = a.function_(2, &[i, acc], body, Default::default(), LamLoc::NONE);
    let end = a.var(f);
    let root = a.letrec(&[(f, function)], end);
    names_agree(a, root, None, false);
}

#[test]
fn the_naming_log_agrees_on_a_body_imported_from_another_module() {
    // (c): `Other.run(null)` with `run = arg => (first, second) => arg`
    // inlined: the function inside the imported body is lowered here, after
    // a closure of the unit, with variables and a header made during the
    // import (`inline_external_function`, `swap_fragment_tables`).
    use crate::cmi::persistent_env::CmjExportArity;
    use crate::js_ir::ModulePathResolver;
    use crate::lambda::{ApInfo, ApplyStatus, FieldDbgInfo, LamLoc, Lambda, lam_arity::Arity, lam_primitive::Primitive};
    let resolver = ModulePathResolver::from_compile_options(None, None, None, None, None, None, false);
    let param = Ident::new("arg", 100, IdentFlags::NONE);
    let first = Ident::new("first", 101, IdentFlags::NONE);
    let second = Ident::new("second", 102, IdentFlags::NONE);
    let inner = Lambda::function_(2, vec![first, second], Lambda::var(param), Default::default(), LamLoc::NONE);
    resolver.set_bir_test_export("Other", "run", CmjExportArity::Single(Arity::info(vec![1], false)),
        Some(Lambda::function_(1, vec![param], inner, Default::default(), LamLoc::NONE)));
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
    names_agree(a, root, Some(&resolver), true);
}

#[test]
fn the_naming_log_agrees_on_a_partial_application_whose_argument_reads_a_local() {
    // G10: `let f = param => Other.run(param)` with `run` of arity 2: the
    // lowering eta-expands (`apply_with_arity`) to
    // `param$1 => Other.run(param, param$1)`. The argument was lowered
    // before the expansion's function existed (`names::adopt`).
    use crate::cmi::persistent_env::CmjExportArity;
    use crate::js_ir::ModulePathResolver;
    use crate::lambda::{ApInfo, ApplyStatus, FieldDbgInfo, LamLoc, lam_arity::Arity, lam_primitive::Primitive};
    for status in [ApplyStatus::Na, ApplyStatus::InferFull, ApplyStatus::Uncurry] {
        let resolver = ModulePathResolver::from_compile_options(None, None, None, None, None, None, false);
        resolver.set_bir_test_export("Other", "run", CmjExportArity::Single(Arity::info(vec![2], false)), None);
        let mut a = LamArena::new();
        let (f, param) = (Ident::new("f", 1, IdentFlags::NONE), Ident::new("param", 2, IdentFlags::NONE));
        let global = a.global_module(Ident::create_persistent("Other"));
        let callee = a.prim_raw(Primitive::Pfield(0, FieldDbgInfo::Module { name: crate::name::Name::new("run") }), &[global], LamLoc::NONE);
        let arg = a.var(param);
        let applied = a.apply_raw(callee, &[arg], ApInfo { status, loc: LamLoc::NONE });
        let function = a.function_(1, &[param], applied, Default::default(), LamLoc::NONE);
        let end = a.var(f);
        let root = a.let_(LetKind::Strict, f, function, end);
        names_agree(a, root, Some(&resolver), false);
    }
}

#[test]
fn the_naming_log_agrees_on_a_dispatch_function_whose_scrutinee_reads_a_local() {
    // G10: `let g = value => f(value)` with `f` an external whose argument
    // is a polymorphic variant mapped to strings: the argument becomes the
    // scrutinee of `(() => { switch (value) { ... } })()`
    // (`external_dispatch`), lowered before that function existed.
    use crate::lambda::lam_primitive::{Attr, DeclKind, ExternalDecl, JsCall, LabelNoname, Param, Primitive as P};
    use crate::lambda::LamLoc;
    let mut a = LamArena::new();
    let (g, value) = (Ident::new("g", 1, IdentFlags::NONE), Ident::new("value", 2, IdentFlags::NONE));
    let arg = a.var(value);
    let call = JsCall {
        prim_name: "f".into(),
        arg_types: vec![Param { arg_label: LabelNoname::ArgEmpty, arg_type: Attr::PolyVarString { descr: vec![("tag".into(), "mapped".into())] } }],
        ffi: ExternalDecl { kind: DeclKind::DeclVal { name: "f".into() }, module_: None, scopes: vec![], variadic: false, effective_arity: 1 },
    };
    let applied = a.prim_raw(P::PjsCall(Box::new(call)), &[arg], LamLoc::NONE);
    let function = a.function_(1, &[value], applied, Default::default(), LamLoc::NONE);
    let end = a.var(g);
    let root = a.let_(LetKind::Strict, g, function, end);
    names_agree(a, root, None, false);
}

#[test]
fn a_partial_application_whose_argument_reads_a_local_reaches_the_adoption() {
    // The input of `the_naming_log_agrees_on_a_partial_application_whose_argument_reads_a_local`:
    // with `ApplyStatus::Na` the eta-expansion is built (`apply_with_arity`),
    // so `names::adopt` reads the callee and the argument. `InferFull` and
    // `Uncurry` build the call without consulting the arity (`call.rs`,
    // `application`): those two inputs do not reach the site.
    use crate::cmi::persistent_env::CmjExportArity;
    use crate::js_ir::ModulePathResolver;
    use crate::lambda::{ApInfo, ApplyStatus, FieldDbgInfo, LamLoc, lam_arity::Arity, lam_primitive::Primitive};
    for status in [ApplyStatus::Na, ApplyStatus::InferFull, ApplyStatus::Uncurry] {
        let resolver = ModulePathResolver::from_compile_options(None, None, None, None, None, None, false);
        resolver.set_bir_test_export("Other", "run", CmjExportArity::Single(Arity::info(vec![2], false)), None);
        let mut a = LamArena::new();
        let (f, param) = (Ident::new("f", 1, IdentFlags::NONE), Ident::new("param", 2, IdentFlags::NONE));
        let global = a.global_module(Ident::create_persistent("Other"));
        let callee = a.prim_raw(Primitive::Pfield(0, FieldDbgInfo::Module { name: crate::name::Name::new("run") }), &[global], LamLoc::NONE);
        let arg = a.var(param);
        let applied = a.apply_raw(callee, &[arg], ApInfo { status, loc: LamLoc::NONE });
        let function = a.function_(1, &[param], applied, Default::default(), LamLoc::NONE);
        let end = a.var(f);
        let root = a.let_(LetKind::Strict, f, function, end);
        let adopted = adopted_nodes_of(a, root, Some(&resolver));
        assert_eq!(adopted > 0, status == ApplyStatus::Na, "{status:?}: {adopted}");
    }
}

#[test]
fn a_dispatch_function_whose_scrutinee_reads_a_local_reaches_the_adoption() {
    // The input of `the_naming_log_agrees_on_a_dispatch_function_whose_scrutinee_reads_a_local`:
    // the dispatch function is built, so `names::adopt` reads its scrutinee.
    use crate::lambda::lam_primitive::{Attr, DeclKind, ExternalDecl, JsCall, LabelNoname, Param, Primitive as P};
    use crate::lambda::LamLoc;
    let mut a = LamArena::new();
    let (g, value) = (Ident::new("g", 1, IdentFlags::NONE), Ident::new("value", 2, IdentFlags::NONE));
    let arg = a.var(value);
    let call = JsCall {
        prim_name: "f".into(),
        arg_types: vec![Param { arg_label: LabelNoname::ArgEmpty, arg_type: Attr::PolyVarString { descr: vec![("tag".into(), "mapped".into())] } }],
        ffi: ExternalDecl { kind: DeclKind::DeclVal { name: "f".into() }, module_: None, scopes: vec![], variadic: false, effective_arity: 1 },
    };
    let applied = a.prim_raw(P::PjsCall(Box::new(call)), &[arg], LamLoc::NONE);
    let function = a.function_(1, &[value], applied, Default::default(), LamLoc::NONE);
    let end = a.var(g);
    let root = a.let_(LetKind::Strict, g, function, end);
    assert!(adopted_nodes_of(a, root, None) > 0);
}

#[test]
fn the_naming_log_agrees_on_a_function_the_printer_eta_reduces() {
    // `let f = x => g(x)` with `g` a JavaScript global prints as
    // `let f = g`: neither side names `x`, which still has a reference.
    // Reduced from `inventory_tests::pintmax`
    // (`let unit = (arg0, arg1) => Primitive_int.max(arg0, arg1)`).
    use crate::lambda::LamLoc;
    let mut a = LamArena::new();
    let (f, x) = (Ident::new("f", 1, IdentFlags::NONE), Ident::new("x", 2, IdentFlags::NONE));
    let callee = js_global(&mut a, "g");
    let arg = a.var(x);
    let applied = call(&mut a, callee, &[arg]);
    let function = a.function_(1, &[x], applied, Default::default(), LamLoc::NONE);
    let end = a.var(f);
    let root = a.let_(LetKind::Strict, f, function, end);
    let stats = names_agree(a, root, None, false);
    assert_eq!(stats.names_pass, 1);
}

#[test]
fn the_naming_log_agrees_on_a_function_whose_module_reference_folds_away() {
    // `let f = (left, right) => Primitive_int.compare(left, right) == 0`
    // prints `left === right`: the comparison builds a reference to
    // `Primitive_int`, which the constructor of `===` releases before `f`
    // closes. The reference has a site, the release clears it, and the
    // close of `f` skips it: the free list is empty, as the pass's is.
    // Reduced from `prim_cmp::tests::integer_comparison_strips_runtime_compare_before_zero`.
    use crate::lambda::lam_compat::Comparison;
    use crate::lambda::lam_primitive::Primitive as P;
    use crate::lambda::LamLoc;
    let mut a = LamArena::new();
    let (f, left, right) = (Ident::new("f", 1, IdentFlags::NONE), Ident::new("left", 2, IdentFlags::NONE), Ident::new("right", 3, IdentFlags::NONE));
    let (l, r) = (a.var(left), a.var(right));
    let order = a.prim_raw(P::Pintorder, &[l, r], LamLoc::NONE);
    let zero = a.const_(C::Int { i: 0, comment: None });
    let equal = a.prim_raw(P::Pintcomp(Comparison::Eq), &[order, zero], LamLoc::NONE);
    let function = a.function_(2, &[left, right], equal, Default::default(), LamLoc::NONE);
    let end = a.var(f);
    let root = a.let_(LetKind::Strict, f, function, end);
    names_agree(a, root, None, false);
}

#[test]
fn the_naming_log_agrees_on_a_function_whose_option_wrapper_folds_away() {
    // `let f = value => isNotNone(Some(Primitive_module.init(value)))`:
    // `Some` builds `Primitive_option.some(...)`, and the test for `None`
    // releases that call with its module reference before `f` closes
    // (`prim.rs`, `PisNotNone`). The free list of `f` holds
    // `Primitive_module` only. Reduced from
    // `prim::tests::option_arms_match_legacy` (`PisNotNone`, shape 8).
    use crate::lambda::lam_primitive::Primitive as P;
    use crate::lambda::LamLoc;
    let mut a = LamArena::new();
    let (f, value) = (Ident::new("f", 1, IdentFlags::NONE), Ident::new("value", 2, IdentFlags::NONE));
    let read = a.var(value);
    let module = a.prim_raw(P::PinitMod, &[read], LamLoc::NONE);
    let some = a.prim_raw(P::Psome, &[module], LamLoc::NONE);
    let test = a.prim_raw(P::PisNotNone, &[some], LamLoc::NONE);
    let function = a.function_(1, &[value], test, Default::default(), LamLoc::NONE);
    let end = a.var(f);
    let root = a.let_(LetKind::Strict, f, function, end);
    names_agree(a, root, None, false);
}

#[test]
fn the_naming_log_agrees_on_the_order_of_a_free_list_with_a_javascript_name() {
    // `let f = value => new F(Primitive_module.init(value))` with `F` an
    // external: the free list of `f` is `[F, Primitive_module]` in
    // `Ident`'s order (both stamp zero, then the name). The variable the
    // lowering makes for `F` has an order of its own, which is not its
    // stamp, so the list is sorted by the identifiers, as the pass sorts
    // it. Reduced from
    // `a_result_the_lowering_assigns_is_not_held_before_a_statement_argument_of_an_external`
    // (`DeclNew`).
    use crate::lambda::lam_primitive::{DeclKind, ExternalDecl, JsCall, Param, Primitive as P};
    use crate::lambda::LamLoc;
    let mut a = LamArena::new();
    let (f, value) = (Ident::new("f", 1, IdentFlags::NONE), Ident::new("value", 2, IdentFlags::NONE));
    let read = a.var(value);
    let module = a.prim_raw(P::PinitMod, &[read], LamLoc::NONE);
    let call = JsCall {
        prim_name: "F".into(),
        arg_types: vec![Param::dummy()],
        ffi: ExternalDecl { kind: DeclKind::DeclNew { name: "F".into() }, module_: None, scopes: vec![], variadic: false, effective_arity: 1 },
    };
    let made = a.prim_raw(P::PjsCall(Box::new(call)), &[module], LamLoc::NONE);
    let function = a.function_(1, &[value], made, Default::default(), LamLoc::NONE);
    let end = a.var(f);
    let root = a.let_(LetKind::Strict, f, function, end);
    names_agree(a, root, None, false);
}

#[test]
fn the_naming_log_agrees_on_a_function_made_a_method_after_its_close() {
    // `let m = function (o, x) { return o + x }` as a method (`@this`):
    // the lowering closes the function and then makes it a method
    // (`prim.rs`, `PjsFnMethod`), which prints `let o = this;` when the
    // body reads `o`. Whether the body reads the first parameter is so
    // recorded for every function (`ScopeRow::FIRST_READ`); a method that
    // does not read it names no `this`. Reduced from
    // tests/tests/src/test_bs_this.res (`name_differences: 6`,
    // `unnamed_references: 6`).
    use crate::lambda::lam_primitive::Primitive as P;
    use crate::lambda::LamLoc;
    for reads_this in [true, false] {
        let mut a = LamArena::new();
        let ident = |name: &str, stamp: i32| Ident::new(name, stamp, IdentFlags::NONE);
        let (m, o, x) = (ident("m", 1), ident("o", 2), ident("x", 3));
        let (left, right) = (a.var(if reads_this { o } else { x }), a.var(x));
        let sum = a.prim_raw(P::Paddint, &[left, right], LamLoc::NONE);
        let function = a.function_(2, &[o, x], sum, Default::default(), LamLoc::NONE);
        let method = a.prim_raw(P::PjsFnMethod, &[function], LamLoc::NONE);
        let end = a.var(m);
        let root = a.let_(LetKind::Strict, m, method, end);
        let stats = names_agree(a, root, None, false);
        assert_eq!(stats.names_pass, if reads_this { 3 } else { 2 });
    }
}

#[test]
fn the_naming_log_agrees_on_a_method_with_the_shape_the_printer_eta_reduces() {
    // `let m = function (o, x) { return g(o, x) }` as a method: at its
    // close the function has the eta shape and is no method yet. The
    // printer does not eta-reduce a method (`walk::eta_target`), so the
    // replay reads the header's method flag when it reaches the literal
    // and names the parameters.
    use crate::lambda::lam_primitive::Primitive as P;
    use crate::lambda::LamLoc;
    let mut a = LamArena::new();
    let ident = |name: &str, stamp: i32| Ident::new(name, stamp, IdentFlags::NONE);
    let (m, o, x) = (ident("m", 1), ident("o", 2), ident("x", 3));
    let callee = js_global(&mut a, "g");
    let (first, second) = (a.var(o), a.var(x));
    let applied = call(&mut a, callee, &[first, second]);
    let function = a.function_(2, &[o, x], applied, Default::default(), LamLoc::NONE);
    let method = a.prim_raw(P::PjsFnMethod, &[function], LamLoc::NONE);
    let end = a.var(m);
    let root = a.let_(LetKind::Strict, m, method, end);
    let stats = names_agree(a, root, None, false);
    assert_eq!(stats.names_pass, 3);
}

#[test]
fn the_naming_log_agrees_on_a_function_that_reads_one_module_through_two_imports() {
    // `let f = value => ext(Primitive_module.run, Primitive_module.init(value))`:
    // the unit reads the module `Primitive_module` (an import of kind
    // `Ml`) and the lowering reads the runtime module of that name (an
    // import of its own, kind `Runtime`). Both have one identifier; the
    // pass keeps a set of identifiers, so the free list of `f` has one
    // entry for it. Reduced from tests/tests/src/exception_raise_test.res
    // (`[Primitive_exceptions, Primitive_exceptions]`, `free_differences: 2`).
    use crate::cmi::persistent_env::CmjExportArity;
    use crate::js_ir::ModulePathResolver;
    use crate::lambda::{FieldDbgInfo, LamLoc, lam_arity::Arity, lam_primitive::Primitive as P};
    let resolver = ModulePathResolver::from_compile_options(None, None, None, None, None, None, false);
    resolver.set_bir_test_export("Primitive_module", "run", CmjExportArity::Single(Arity::info(vec![1], false)), None);
    let mut a = LamArena::new();
    let (f, value) = (Ident::new("f", 1, IdentFlags::NONE), Ident::new("value", 2, IdentFlags::NONE));
    let module = a.global_module(Ident::create_persistent("Primitive_module"));
    let field = a.prim_raw(P::Pfield(0, FieldDbgInfo::Module { name: crate::name::Name::new("run") }), &[module], LamLoc::NONE);
    let read = a.var(value);
    let made = a.prim_raw(P::PinitMod, &[read], LamLoc::NONE);
    let applied = ext_call(&mut a, &[field, made]);
    let function = a.function_(1, &[value], applied, Default::default(), LamLoc::NONE);
    let end = a.var(f);
    let root = a.let_(LetKind::Strict, f, function, end);
    names_agree(a, root, Some(&resolver), false);
}

#[test]
fn the_naming_log_agrees_on_a_preserved_element_whose_runtime_callee_is_not_printed() {
    // `let f = label => <div title={label} />` in a unit that preserves
    // JSX: the lowering builds `JsxRuntime.jsx("div", {title: label})`, and
    // the printer writes the element and no callee, so `JsxRuntime` is not
    // free in `f` (naming.rs `children`, `ExprKind::Jsx`: the callee is
    // visited for the runtime form only). Printed through the runtime, it
    // is. The fragment `<></>` prints neither its callee nor its tag.
    // Reduced from tests/tests/src/jsx_preserve_test.res
    // (`free_differences: 3`).
    use crate::lambda::lam_primitive::{DeclKind, ExternalDecl, ExternalModuleName, JsxElement, ModuleBindName, ModuleSource, Primitive as P};
    use crate::lambda::LamLoc;
    let runtime = || ModuleSource::ModuleNamed(ExternalModuleName { bundle: "react/jsx-runtime".into(), module_bind_name: ModuleBindName::PhintNothing, import_attributes: None });
    for fragment in [false, true] {
        for jsx_preserve in [false, true] {
            let mut a = LamArena::new();
            let (f, label) = (Ident::new("f", 1, IdentFlags::NONE), Ident::new("label", 2, IdentFlags::NONE));
            let tag = if fragment {
                let decl = ExternalDecl { kind: DeclKind::DeclVal { name: "Fragment".into() }, module_: Some(runtime()), scopes: vec![], variadic: false, effective_arity: 0 };
                let call = crate::lambda::lam_primitive::JsCall { prim_name: "Fragment".into(), arg_types: vec![], ffi: decl };
                a.prim_raw(P::PjsCall(Box::new(call)), &[], LamLoc::NONE)
            } else {
                a.const_(C::String("div".into()))
            };
            let jsx = JsxElement {
                jsx_name: "jsx".into(),
                jsx_ffi: ExternalDecl { kind: DeclKind::DeclVal { name: "jsx".into() }, module_: Some(runtime()), scopes: vec![], variadic: false, effective_arity: 2 },
                jsx_multi: false,
                jsx_fragment: fragment,
                jsx_spread: false,
                jsx_props: if fragment { vec![] } else { vec![("title".into(), false)] },
                jsx_children: None,
                jsx_key: false,
            };
            let mut args = vec![tag];
            if !fragment {
                args.push(a.var(label));
            }
            let element = a.prim_raw(P::Pjsx(Box::new(jsx)), &args, LamLoc::NONE);
            let function = a.function_(1, &[label], element, Default::default(), LamLoc::NONE);
            let end = a.var(f);
            let root = a.let_(LetKind::Strict, f, function, end);
            names_agree_printing(a, root, None, false, jsx_preserve);
        }
    }
}

#[test]
fn the_naming_log_agrees_on_a_closure_dropped_before_the_function_around_it_closes() {
    // `let f = c => { ignore(() => Primitive_module.init(c)); 3 }`: the
    // closure closes with `Primitive_module` free, and the lowering drops
    // it as a pure effect before `f` closes. A closed child gives its free
    // entries to the function around it when that function closes, and
    // only when its literal is still there, so `f` has an empty free list,
    // as the pass's `f` has. Reduced from a unit of the application corpus
    // (a closure in a branch the lowering dropped; `free_differences: 2`).
    use crate::lambda::lam_primitive::Primitive as P;
    use crate::lambda::LamLoc;
    let mut a = LamArena::new();
    let (f, c) = (Ident::new("f", 1, IdentFlags::NONE), Ident::new("c", 2, IdentFlags::NONE));
    let read = a.var(c);
    let made = a.prim_raw(P::PinitMod, &[read], LamLoc::NONE);
    let closure = a.function_(0, &[], made, Default::default(), LamLoc::NONE);
    let ignored = a.prim_raw(P::Pignore, &[closure], LamLoc::NONE);
    let three = a.const_(C::Int { i: 3, comment: None });
    let body = a.seq_raw(ignored, three);
    let function = a.function_(1, &[c], body, Default::default(), LamLoc::NONE);
    let end = a.var(f);
    let root = a.let_(LetKind::Strict, f, function, end);
    names_agree(a, root, None, false);
}
