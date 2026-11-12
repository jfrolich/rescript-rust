use super::*;
use crate::bir::{bridge, bridge_j};
use crate::ident::IdentFlags;
use crate::js_ir::arena::{JsDepsProgram, JsProgram, StmtKind};
use crate::lambda::arena::{Lam, LamArena};
use crate::lambda::lam_compile::LambdaCompiler;
use crate::lambda::lam_constant::{Constant as C, PointerInfo};

pub(super) fn compare(mut arena: LamArena, root: Lam) {
    let target = Ident::new("result", arena.ident_stamp_bound() + 1, IdentFlags::NONE);
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
        let probed = state.probe(cx, source_root).unwrap();
        let lowered = state.complete(cx, probed);
        lowered
            .program
            .arena
            .validate(Some(lowered.program.root), false)
            .unwrap();
        let actual = bridge_j::export_js(&lowered.program).unwrap();
        let mut compiler = LambdaCompiler::new();
        let compiled = compiler.bir_lower_oracle(&mut arena, root, cx.cont, target);
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
