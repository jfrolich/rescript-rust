//! K: compile_field_access / compile_set_field and P block constructors.
use super::*;
use crate::bir::j::{norm, plain};
use crate::js_ir::arena::FieldPos;
use crate::lambda::lam_compat::FieldDbgInfo;

impl State {
    /// K: resolve_cmj_module_field_constant / compile_field_access.
    pub(super) fn primitive_field(&mut self, idx: i32, info: FieldDbgInfo, target: NodeId) -> NodeId {
        if let FieldDbgInfo::Module { name } = info {
            if let View::JQualified { module, member: None } = self.arena.view(target) {
                let module_name = self.arena.pools.j_modules[module.index()].id.name();
                let constant = self.resolver.as_ref()
                    .and_then(|r| r.module_cmj_export_constants(module_name))
                    .and_then(|t| t.get(name.as_str()).copied());
                self.arena.release(target);
                if let Some(constant) = constant {
                    use crate::cmi::persistent_env::CmjExportConstant as C;
                    return match constant {
                        C::Bool(value) => plain::boolean(&mut self.arena, value),
                        C::Null => plain::node(&mut self.arena, View::JNull, 0),
                        C::Undefined { is_unit } => plain::node(&mut self.arena, View::JUndefined, u16::from(is_unit)),
                    };
                }
                let member = Some(self.arena.intern_text(name.as_str()));
                return plain::node(&mut self.arena, View::JQualified { module, member }, 0);
            }
        }
        let record = matches!(info, FieldDbgInfo::Record { .. } | FieldDbgInfo::RecordInline { .. } | FieldDbgInfo::RecordExtension { .. });
        match info {
            FieldDbgInfo::PolyVarTag => return norm::jm11_poly_var_access(&mut self.arena, target, false),
            FieldDbgInfo::PolyVarContent => return norm::jm11_poly_var_access(&mut self.arena, target, true),
            _ => {}
        }
        if let Some(value) = norm::jm11_projection(&mut self.arena, target, if record { info.name() } else { None }, Some(idx)) {
            return value;
        }
        let field = match info {
            FieldDbgInfo::Module { name } => crate::js_ir::printer::convert_ident_cow(&name).into_owned(),
            FieldDbgInfo::Record { name } | FieldDbgInfo::RecordInline { name } | FieldDbgInfo::RecordExtension { name } => name.to_string(),
            FieldDbgInfo::Extension | FieldDbgInfo::Variant => format!("_{idx}"),
            FieldDbgInfo::Cons => match idx { 0 => "hd".into(), 1 => "tl".into(), _ => format!("_{idx}") },
            FieldDbgInfo::VariantTag => "TAG".into(),
            FieldDbgInfo::Tuple => {
                let index = plain::int(&mut self.arena, idx);
                return plain::node(&mut self.arena, View::JIndex { object: target, index }, 0);
            }
            FieldDbgInfo::PolyVarTag | FieldDbgInfo::PolyVarContent => unreachable!(),
        };
        let property = self.arena.intern_text(&field);
        let position = FieldPos::new(if matches!(info, FieldDbgInfo::VariantTag) { None } else { Some(idx) });
        plain::node(&mut self.arena, View::JDot { object: target, property, position }, 0)
    }

    /// K: compile_set_field, including the pure literal receiver rule.
    pub(super) fn primitive_set_field(&mut self, idx: i32, field: &str, target: NodeId, value: NodeId) -> NodeId {
        let assignment = if crate::bir::j::facts::strictly_pure(&self.arena, target)
            && matches!(self.arena.view(target), View::JArray { .. } | View::JBlockLit { .. }) {
            self.arena.release(target); value
        } else {
            let property = self.arena.intern_text(field);
            let target = plain::node(&mut self.arena, View::JDot { object: target, property, position: FieldPos::new(Some(idx)) }, 0);
            norm::je4_bin(&mut self.arena, crate::js_ir::BinOp::Eq, target, value)
        };
        let unit = plain::node(&mut self.arena, View::JUndefined, 0);
        plain::seq(&mut self.arena, assignment, unit)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lambda::{arena::LamArena, lam_constant::Constant as C, lam_primitive::{Primitive as P, Mutable}, LamLoc, TagInfo};
    use crate::name::Name;

    #[test]
    fn block_field_and_indexing_arms_match_legacy() {
        let field = Name::new("name");
        let mut primitives = vec![(P::Pmakearray, 2), (P::Pmakelist, 2), (P::Pobjtag, 1), (P::Pobjsize, 1), (P::PisPolyVarBlock, 1),
            (P::Pstringrefs, 2), (P::Pstringrefu, 2), (P::Parrayrefs, 2), (P::Parrayrefu, 2), (P::Parraysetu, 3)];
        for mutable in [Mutable::Mutable, Mutable::Immutable] {
            for tag in [TagInfo::Tuple, TagInfo::Module(vec!["name".into(), "other".into()]), TagInfo::constructor("Pair", 2),
                TagInfo::record(vec![("other".into(), false), ("name".into(), false)], crate::parser::ast::MutableFlag::Immutable)] {
                primitives.push((P::Pmakeblock(tag, mutable), 2));
            }
        }
        for info in [FieldDbgInfo::Record { name: field }, FieldDbgInfo::Module { name: field }, FieldDbgInfo::RecordInline { name: field }, FieldDbgInfo::RecordExtension { name: field },
            FieldDbgInfo::Tuple, FieldDbgInfo::Extension, FieldDbgInfo::Variant, FieldDbgInfo::VariantTag, FieldDbgInfo::Cons, FieldDbgInfo::PolyVarTag, FieldDbgInfo::PolyVarContent] {
            primitives.push((P::Pfield(0, info), 1));
            primitives.push((P::Pfield(1, info), 1));
        }
        use crate::lambda::lam_compat::SetFieldDbgInfo as S;
        for info in [S::RecordSet(field), S::RecordInlineSet(field), S::RecordExtensionSet(field)] { primitives.push((P::Psetfield(1, info), 2)); }
        for (primitive, arity) in primitives {
            for shape in 0..4 {
                let mut a = LamArena::new();
                let mut args = Vec::new();
                for i in 0..arity {
                    let value = if i == 0 && shape != 0 {
                        let one = a.const_(C::JsTrue);
                        let two = a.const_(C::JsNull);
                        let tag = if shape == 1 { TagInfo::Tuple } else { TagInfo::record(vec![("other".into(), false), ("name".into(), false)], crate::parser::ast::MutableFlag::Immutable) };
                        let two = if shape == 3 { a.prim_raw(P::PinitMod, &[two], LamLoc::NONE) } else { two };
                        a.prim_raw(P::Pmakeblock(tag, Mutable::Immutable), &[one, two], LamLoc::NONE)
                    } else { a.var(Ident::new(&format!("arg{i}"), 10 + i, crate::ident::IdentFlags::NONE)) };
                    args.push(value);
                }
                let root = a.prim_raw(primitive.clone(), &args, LamLoc::NONE);
                super::super::oracle_tests::compare(a, root);
            }
        }
    }

    #[test]
    fn module_constants_and_flat_make_reason() {
        use crate::cmi::persistent_env::CmjExportConstant as Cc;
        for constant in [None, Some(Cc::Bool(true)), Some(Cc::Bool(false)), Some(Cc::Null), Some(Cc::Undefined { is_unit: true }), Some(Cc::Undefined { is_unit: false })] {
            let resolver = crate::js_ir::ModulePathResolver::from_compile_options(None, None, None, None, None, None, false);
            if let Some(constant) = constant { resolver.set_bir_test_constant("Other", "value", constant); }
            let mut a = LamArena::new();
            let global = a.global_module(Ident::create_persistent("Other"));
            let root = a.prim_raw(P::Pfield(0, FieldDbgInfo::Module { name: Name::new("value") }), &[global], LamLoc::NONE);
            super::super::oracle_tests::compare_with_resolver(a, root, Some(&resolver));
        }
        let mut a = LamArena::new();
        let global = a.global_module(Ident::create_persistent("Other"));
        let inner = a.prim_raw(P::Pfield(0, FieldDbgInfo::Module { name: Name::new("Inner") }), &[global], LamLoc::NONE);
        let root = a.prim_raw(P::Pfield(0, FieldDbgInfo::Module { name: Name::new("make") }), &[inner], LamLoc::NONE);
        let input = crate::bir::bridge::import_lambda(&a, root).unwrap();
        assert!(matches!(super::super::lower(input, None, false), Err(Unsupported("flat make"))));
    }

    #[test]
    fn templates_match_legacy() {
        for tagged in [false, true] {
            for literal in [false, true] {
                for count in 0..4 {
                    let mut a = LamArena::new();
                    let mut args = Vec::new();
                    if tagged { args.push(a.var(Ident::new("tag", 10, crate::ident::IdentFlags::NONE))); }
                    for i in 0..count {
                        args.push(if literal { a.const_(C::String("value".into())) } else { a.var(Ident::new(&format!("value{i}"), 11 + i, crate::ident::IdentFlags::NONE)) });
                    }
                    let primitive = if tagged { P::PtaggedTemplate(vec!["segment".into(); count as usize + 1]) }
                        else { P::Ptemplate(vec![crate::string_literal::template_from_semantic("segment"); count as usize + 1]) };
                    let root = a.prim_raw(primitive, &args, LamLoc::NONE);
                    super::super::oracle_tests::compare(a, root);
                }
            }
        }
    }

    #[test]
    fn primitive_depth_and_block_width_are_linear() {
        for wide in [false, true] {
            let mut a = LamArena::new();
            let root = if wide {
                let args: Vec<_> = (0..10_000).map(|_| a.const_(C::JsNull)).collect();
                a.prim_raw(P::Pmakeblock(TagInfo::Tuple, Mutable::Immutable), &args, LamLoc::NONE)
            } else {
                let mut root = a.const_(C::JsNull);
                for _ in 0..10_000 { root = a.prim_raw(P::Pidentity, &[root], LamLoc::NONE); }
                root
            };
            let input = crate::bir::bridge::import_lambda(&a, root).unwrap();
            let root = input.root;
            let mut state = State::new(input);
            let result = state.probe(Cx::value(), root).unwrap();
            assert_eq!(state.source_steps, 10_001);
            assert_eq!(state.sequence_steps, 10_000);
            let output = state.complete(Cx::value(), result);
            output.program.arena.validate(Some(output.program.root), false).unwrap();
        }
    }
}
