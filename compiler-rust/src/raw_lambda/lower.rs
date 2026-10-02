//! Raw Lambda -> lowered Lambda boundary.
//!
//! This stage is the Rust port of the first `Lam_convert.convert` slice used
//! by optimized-lambda parity dumps and now also feeds the JS backend entry
//! point in `driver.rs`.

use crate::fast_hash::{AHashMap as HashMap, AHashSet as HashSet};
use std::sync::Arc;

use crate::context::IdGenerator;
use crate::ident::Ident;
use crate::lambda::lam_compat::{Comparison, FieldDbgInfo, LetKind};
use crate::lambda::lam_constant::{Constant, ConstructorRuntimeTag, PointerInfo};
use crate::lambda::lam_primitive::{ExternalFfiSpec, ExternalReturnWrapper, Primitive};
use crate::lambda::lam_tag_info::TagInfo;
use crate::lambda::{ApInfo, Apply, ApplyStatus, LFunction, Lambda, LambdaSwitch, PrimInfo};
use crate::location::Location;
use crate::raw_lambda::{RawApply, RawLambda, RawLambdaSwitch};

const SETTER_SUFFIX: &str = "#=";
const EXCEPTION_ID_FIELD: &str = "RE_EXN_ID";

struct LoweringContext<'a> {
    alias_tbl: HashMap<Ident, Ident>,
    exit_map: HashMap<i32, i32>,
    exported_idents: HashSet<Ident>,
    id_gen: &'a IdGenerator,
}

impl<'a> LoweringContext<'a> {
    fn with_id_gen(exported_idents: HashSet<Ident>, id_gen: &'a IdGenerator) -> Self {
        Self {
            alias_tbl: HashMap::new(),
            exit_map: HashMap::new(),
            exported_idents,
            id_gen,
        }
    }

    fn lower_lambda(&mut self, raw: RawLambda) -> Lambda {
        self.lower_lambda_with_dynamic_import(raw, false)
    }

    fn lower_lambda_with_dynamic_import(&mut self, raw: RawLambda, dynamic_import: bool) -> Lambda {
        match raw {
            RawLambda::Lshared(inner) => self.lower_lambda_with_dynamic_import(
                std::sync::Arc::unwrap_or_clone(inner),
                dynamic_import,
            ),
            RawLambda::Lvar(id) => Lambda::var(self.alias_target(id)),
            RawLambda::LglobalModule(id, imported) => {
                if id.is_predef_exn() {
                    Lambda::const_(Constant::String {
                        s: id.name().to_string(),
                        delim: None,
                    })
                } else {
                    Lambda::global_module(id, dynamic_import || imported)
                }
            }
            RawLambda::Lconst(c) => Lambda::const_(lower_constant(c)),
            RawLambda::Lapply(apply) => self.lower_apply(*apply),
            RawLambda::Lfunction(func) => {
                let (renamed_params, renamed_body) =
                    rename_optional_parameters(&self.id_gen, func.params, *func.body);
                Lambda::function_(
                    func.arity,
                    renamed_params,
                    self.lower_lambda(renamed_body),
                    func.attr,
                )
            }
            RawLambda::Llet(kind, id, value, body) if dynamic_import => {
                if let RawLambda::LglobalModule(global_id, _) = value.as_ref() {
                    return Lambda::global_module(global_id.clone(), true);
                }
                self.lower_let(kind, id, *value, *body)
            }
            RawLambda::Llet(kind, id, value, body) => self.lower_let(kind, id, *value, *body),
            RawLambda::Lletrec(bindings, body) => self.lower_letrec(bindings, *body),
            RawLambda::Lprim(info) => {
                self.lower_primitive(info.primitive, info.args, info.loc, dynamic_import)
            }
            RawLambda::Lswitch(scrutinee, switch, _) => self.lower_switch(*scrutinee, *switch),
            RawLambda::LstringSwitch(scrutinee, cases, default) => {
                // `Lam.stringswitch (convert_aux e) ... (convert_aux default)` depends on
                // OCaml's right-to-left argument evaluation, so lower the tail before
                // the scrutinee to keep alias/exit-map visibility aligned.
                let lowered_default = default.map(|lam| Box::new(self.lower_lambda(*lam)));
                let lowered_cases = cases
                    .into_iter()
                    .map(|(name, lam)| (name, self.lower_lambda(lam)))
                    .collect();
                let lowered_scrutinee = self.lower_lambda(*scrutinee);
                Lambda::LstringSwitch(Box::new(lowered_scrutinee), lowered_cases, lowered_default)
            }
            RawLambda::LstaticRaise(id, args) if args.is_empty() => {
                Lambda::static_raise(self.remap_exit(id), Vec::new())
            }
            RawLambda::LstaticRaise(id, args) => Lambda::static_raise(
                id,
                args.into_iter().map(|arg| self.lower_lambda(arg)).collect(),
            ),
            RawLambda::LstaticCatch(body, (i, ids), handler)
                if ids.is_empty()
                    && matches!(&*handler, RawLambda::LstaticRaise(_, inner) if inner.is_empty()) =>
            {
                let RawLambda::LstaticRaise(j, _) = *handler else {
                    unreachable!();
                };
                self.exit_map.insert(i, self.remap_exit(j));
                self.lower_lambda(*body)
            }
            RawLambda::LstaticCatch(body, (i, ids), handler) => {
                let lowered_handler = self.lower_lambda(*handler);
                let lowered_body = self.lower_lambda(*body);
                Lambda::static_catch(lowered_body, i, ids, lowered_handler)
            }
            RawLambda::LtryWith(body, id, handler) => self.lower_try_with(*body, id, *handler),
            RawLambda::LifThenElse(cond, then_, else_) => {
                let lowered_else = self.lower_lambda(*else_);
                let lowered_then = self.lower_lambda(*then_);
                let lowered_cond = self.lower_lambda(*cond);
                Lambda::if_(lowered_cond, lowered_then, lowered_else)
            }
            RawLambda::Lsequence(first, second) => {
                let lowered_second = self.lower_lambda(*second);
                let lowered_first = self.lower_lambda(*first);
                Lambda::seq(lowered_first, lowered_second)
            }
            RawLambda::Lwhile(cond, body) => {
                let lowered_body = self.lower_lambda(*body);
                let lowered_cond = self.lower_lambda(*cond);
                Lambda::while_(lowered_cond, lowered_body)
            }
            RawLambda::Lfor(var, start, end, dir, body) => {
                let lowered_body = self.lower_lambda(*body);
                let lowered_end = self.lower_lambda(*end);
                let lowered_start = self.lower_lambda(*start);
                Lambda::for_(var, lowered_start, lowered_end, dir, lowered_body)
            }
            RawLambda::Lfor_of(var, iterable, body) => {
                let lowered_body = self.lower_lambda(*body);
                let lowered_iterable = self.lower_lambda(*iterable);
                Lambda::for_of(var, lowered_iterable, lowered_body)
            }
            RawLambda::Lfor_await_of(var, iterable, body) => {
                let lowered_body = self.lower_lambda(*body);
                let lowered_iterable = self.lower_lambda(*iterable);
                Lambda::for_await_of(var, lowered_iterable, lowered_body)
            }
            RawLambda::Lbreak => Lambda::break_(),
            RawLambda::Lcontinue => Lambda::continue_(),
            RawLambda::Lassign(id, value) => Lambda::assign(id, self.lower_lambda(*value)),
            RawLambda::Lsend(name, obj, loc) => Lambda::prim(
                Primitive::PjsUnsafeDowngrade {
                    name,
                    setter: false,
                },
                vec![self.lower_lambda(*obj)],
                loc,
            ),
        }
    }

    fn alias_target(&self, id: Ident) -> Ident {
        self.alias_tbl.get(&id).cloned().unwrap_or(id)
    }

    fn remap_exit(&self, id: i32) -> i32 {
        self.exit_map.get(&id).copied().unwrap_or(id)
    }

    fn lower_apply(&mut self, apply: RawApply) -> Lambda {
        let RawApply {
            ap_func,
            ap_args,
            ap_info,
            ap_transformed_jsx,
        } = apply;

        let func = *ap_func;
        if let RawLambda::Lsend(name, obj, loc) = func {
            if let Some(property) = name.strip_suffix(SETTER_SUFFIX) {
                let mut args = vec![self.lower_lambda(*obj)];
                args.extend(ap_args.into_iter().map(|arg| self.lower_lambda(arg)));
                return Lambda::prim(
                    Primitive::PjsUnsafeDowngrade {
                        name: property.to_string(),
                        setter: true,
                    },
                    args,
                    loc,
                );
            }

            let lowered_args = ap_args
                .into_iter()
                .map(|arg| self.lower_lambda(arg))
                .collect();
            let lowered_func = self.lower_lambda(RawLambda::Lsend(name, obj, loc));
            return make_apply(
                lowered_func,
                lowered_args,
                ApInfo {
                    loc: ap_info.loc,
                    inlined: ap_info.inlined,
                    status: ApplyStatus::Uncurry,
                },
                ap_transformed_jsx,
            );
        }

        let lowered_args = ap_args
            .into_iter()
            .map(|arg| self.lower_lambda(arg))
            .collect();
        let lowered_func = self.lower_lambda(func);
        make_apply(
            lowered_func,
            lowered_args,
            ApInfo {
                loc: ap_info.loc,
                inlined: ap_info.inlined,
                status: ApplyStatus::Uncurry,
            },
            ap_transformed_jsx,
        )
    }

    fn lower_let(&mut self, kind: LetKind, id: Ident, value: RawLambda, body: RawLambda) -> Lambda {
        if kind == LetKind::Alias {
            if let RawLambda::Lvar(target) = value {
                let target = self.alias_target(target);
                self.alias_tbl.insert(id.clone(), target.clone());
                let lowered_body = self.lower_lambda(body);
                if self.exported_idents.contains(&id) {
                    return Lambda::let_(kind, id, Lambda::var(target), lowered_body);
                }
                return lowered_body;
            }
        }

        let lowered_value = self.lower_lambda(value);
        let lowered_body = self.lower_lambda(body);

        if kind == LetKind::Alias {
            if let Some(rewritten) = fold_offset_switch_alias(&id, &lowered_value, &lowered_body) {
                return rewritten;
            }
        }

        Lambda::let_(kind, id, lowered_value, lowered_body)
    }

    fn lower_letrec(&mut self, bindings: Vec<(Ident, RawLambda)>, body: RawLambda) -> Lambda {
        let lowered_bindings = bindings
            .into_iter()
            .map(|(id, lam)| (id, self.lower_lambda(lam)))
            .collect::<Vec<_>>();
        let lowered_body = self.lower_lambda(body);
        rebuild_recursive_bindings(lowered_bindings, lowered_body)
    }

    fn lower_primitive(
        &mut self,
        primitive: Primitive,
        args: Vec<RawLambda>,
        loc: Location,
        dynamic_import_scope: bool,
    ) -> Lambda {
        if let Primitive::PrawJsCode(info) = &primitive {
            let mut info = info.clone();
            match args.as_slice() {
                [RawLambda::Lconst(Constant::String { s, .. })]
                | [RawLambda::Lconst(Constant::ImmString(s))] => {
                    info.code = s.clone();
                    return Lambda::prim(Primitive::PrawJsCode(info), Vec::new(), loc);
                }
                [] => return Lambda::prim(Primitive::PrawJsCode(info), Vec::new(), loc),
                _ => {}
            }
        }

        let arg_dynamic_import = matches!(primitive, Primitive::Pimport).then_some(true);
        let args = args
            .into_iter()
            .map(|arg| {
                self.lower_lambda_with_dynamic_import(
                    arg,
                    arg_dynamic_import.unwrap_or(dynamic_import_scope),
                )
            })
            .collect::<Vec<_>>();

        match primitive {
            Primitive::Pidentity => args.into_iter().next().unwrap_or_else(Lambda::unit),
            Primitive::Pnull => Lambda::const_(Constant::JsNull),
            Primitive::Pundefined => Lambda::const_(Constant::JsUndefined { is_unit: false }),
            Primitive::PextensionSlotEq => match args.as_slice() {
                [lhs, rhs] => Lambda::prim(
                    Primitive::Pstringcomp(Comparison::Eq),
                    vec![
                        Lambda::prim(
                            Primitive::Pfield(
                                0,
                                FieldDbgInfo::Record {
                                    name: EXCEPTION_ID_FIELD.to_string(),
                                },
                            ),
                            vec![lhs.clone()],
                            loc,
                        ),
                        rhs.clone(),
                    ],
                    loc,
                ),
                _ => unreachable!("PextensionSlotEq expects exactly two arguments"),
            },
            Primitive::Pignore => {
                let arg = args.into_iter().next().unwrap_or_else(Lambda::unit);
                Lambda::seq(arg, Lambda::unit())
            }
            Primitive::PjsCall { ffi, .. } if args.is_empty() && ffi.inline_constant.is_some() => {
                Lambda::const_(ffi.inline_constant.expect("guarded inline constant"))
            }
            Primitive::PjsCall {
                prim_name,
                arg_types,
                ffi,
                dynamic_import: _call_dynamic_import,
                transformed_jsx,
            } if is_object_create_call(&prim_name, &arg_types, &ffi) => Lambda::prim(
                Primitive::PjsObjectCreate(
                    ffi.obj_params
                        .clone()
                        .expect("guarded object-create metadata"),
                ),
                args,
                loc,
            ),
            Primitive::PjsCall {
                prim_name,
                arg_types,
                ffi,
                dynamic_import: call_dynamic_import,
                transformed_jsx,
            } => {
                let return_wrapper = ffi.return_wrapper;
                let call = Lambda::prim(
                    Primitive::PjsCall {
                        prim_name,
                        arg_types,
                        ffi,
                        dynamic_import: call_dynamic_import || dynamic_import_scope,
                        transformed_jsx,
                    },
                    args,
                    loc,
                );
                wrap_ffi_result(call, return_wrapper, loc)
            }
            Primitive::Pmakeblock(TagInfo::PolyVar(name), mutable_flag) => match args.as_slice() {
                [_, value] => Lambda::prim(
                    Primitive::Pmakeblock(TagInfo::PolyVar(name.clone()), mutable_flag),
                    vec![
                        Lambda::const_(polyvar_block_tag_constant(&name)),
                        value.clone(),
                    ],
                    loc,
                ),
                _ => unreachable!("polyvariant blocks expect tag and payload"),
            },
            Primitive::Pmakeblock(TagInfo::SomeNotNested, _) => {
                Lambda::prim(Primitive::PsomeNotNest, args, loc)
            }
            Primitive::Pmakeblock(TagInfo::Some, _) => Lambda::prim(Primitive::Psome, args, loc),
            Primitive::Pisout(range) => match args.as_slice() {
                [Lambda::Lprim(inner)]
                    if inner.args.len() == 1
                        && matches!(inner.primitive, Primitive::Poffsetint(_)) =>
                {
                    let Primitive::Poffsetint(offset) = inner.primitive.clone() else {
                        unreachable!();
                    };
                    Lambda::prim(
                        Primitive::Pisout(offset),
                        vec![
                            Lambda::const_(Constant::Int {
                                i: range,
                                comment: None,
                            }),
                            inner.args[0].clone(),
                        ],
                        loc,
                    )
                }
                [arg] => Lambda::prim(
                    Primitive::Pisout(0),
                    vec![
                        Lambda::const_(Constant::Int {
                            i: range,
                            comment: None,
                        }),
                        arg.clone(),
                    ],
                    loc,
                ),
                _ => Lambda::prim(Primitive::Pisout(range), args, loc),
            },
            primitive @ Primitive::PinitMod => match args.as_slice() {
                [_, shape] if is_empty_module_shape_constant(shape) => Lambda::unit(),
                _ => Lambda::prim(primitive, args, loc),
            },
            primitive @ Primitive::PupdateMod => match args.as_slice() {
                [shape, _, _] if is_empty_module_shape_constant(shape) => Lambda::unit(),
                _ => lower_primitive_default(primitive, args, loc),
            },
            other => lower_primitive_default(other, args, loc),
        }
    }

    fn lower_switch(&mut self, scrutinee: RawLambda, switch: RawLambdaSwitch) -> Lambda {
        // `convert_switch` builds the switch record before passing the
        // scrutinee to `Lam.switch`, so OCaml's right-to-left evaluation keeps
        // case/failaction exit-alias updates visible to the scrutinee, not the
        // other way around.
        let const_only_switch = switch.sw_failaction.is_none()
            && switch.sw_blocks.is_empty()
            && switch.sw_numblocks == 0;
        let lowered_consts = switch
            .sw_consts
            .into_iter()
            .map(|(tag, lam)| (tag, self.lower_lambda(lam)))
            .collect::<Vec<_>>();
        let lowered_blocks = switch
            .sw_blocks
            .into_iter()
            .map(|(tag, lam)| (tag, self.lower_lambda(lam)))
            .collect::<Vec<_>>();
        let lowered_failaction = switch
            .sw_failaction
            .map(|lam| Box::new(self.lower_lambda(*lam)));
        let lowered_scrutinee = self.lower_lambda(scrutinee);

        if const_only_switch {
            if let Some(diff) = happens_to_be_diff(&lowered_consts, &switch.sw_dispatch) {
                if diff == 0 {
                    return lowered_scrutinee;
                }
                return Lambda::prim(
                    Primitive::Paddint,
                    vec![
                        lowered_scrutinee,
                        Lambda::const_(Constant::Int {
                            i: diff,
                            comment: None,
                        }),
                    ],
                    Location::none(),
                );
            }
        }

        if const_only_switch {
            Lambda::Lswitch(
                Box::new(lowered_scrutinee),
                Box::new(LambdaSwitch {
                    sw_consts_full: lowered_consts.len() >= switch.sw_numconsts,
                    sw_consts: lowered_consts,
                    sw_blocks_full: true,
                    sw_blocks: lowered_blocks,
                    sw_failaction: lowered_failaction,
                    sw_dispatch: switch.sw_dispatch,
                }),
            )
        } else {
            Lambda::Lswitch(
                Box::new(lowered_scrutinee),
                Box::new(LambdaSwitch {
                    sw_consts_full: lowered_consts.len() >= switch.sw_numconsts,
                    sw_consts: lowered_consts,
                    sw_blocks_full: lowered_blocks.len() >= switch.sw_numblocks,
                    sw_blocks: lowered_blocks,
                    sw_failaction: lowered_failaction,
                    sw_dispatch: switch.sw_dispatch,
                }),
            )
        }
    }

    fn lower_try_with(&mut self, body: RawLambda, id: Ident, handler: RawLambda) -> Lambda {
        let lowered_body = self.lower_lambda(body);
        let lowered_handler = self.lower_lambda(handler);
        if exception_id_destructed(&lowered_handler, &id) {
            let raw_id = self.id_gen.create(&format!("raw_{}", id.name()));
            let wrapped = Lambda::let_(
                LetKind::StrictOpt,
                id,
                Lambda::prim(
                    Primitive::PwrapExn,
                    vec![Lambda::var(raw_id.clone())],
                    Location::none(),
                ),
                lowered_handler,
            );
            Lambda::try_(lowered_body, raw_id, wrapped)
        } else {
            Lambda::try_(lowered_body, id, lowered_handler)
        }
    }
}

fn collect_exported_idents(raw: &RawLambda, exports: &mut HashSet<Ident>) {
    match raw {
        RawLambda::Lshared(inner) => collect_exported_idents(inner, exports),
        RawLambda::Lvar(_) | RawLambda::LglobalModule(_, _) | RawLambda::Lconst(_) => {}
        RawLambda::Lapply(apply) => {
            collect_exported_idents(&apply.ap_func, exports);
            for arg in &apply.ap_args {
                collect_exported_idents(arg, exports);
            }
        }
        RawLambda::Lfunction(func) => collect_exported_idents(&func.body, exports),
        RawLambda::Llet(_, _, value, body) => {
            collect_exported_idents(value, exports);
            collect_exported_idents(body, exports);
        }
        RawLambda::Lletrec(bindings, body) => {
            for (_, lam) in bindings {
                collect_exported_idents(lam, exports);
            }
            collect_exported_idents(body, exports);
        }
        RawLambda::Lprim(info) => {
            if let Primitive::Pmakeblock(TagInfo::ModuleExport(ids), _) = &info.primitive {
                exports.extend(ids.iter().cloned());
            }
            for arg in &info.args {
                collect_exported_idents(arg, exports);
            }
        }
        RawLambda::Lswitch(scrutinee, switch, _) => {
            collect_exported_idents(scrutinee, exports);
            for (_, lam) in &switch.sw_consts {
                collect_exported_idents(lam, exports);
            }
            for (_, lam) in &switch.sw_blocks {
                collect_exported_idents(lam, exports);
            }
            if let Some(failaction) = &switch.sw_failaction {
                collect_exported_idents(failaction, exports);
            }
        }
        RawLambda::LstringSwitch(scrutinee, cases, default) => {
            collect_exported_idents(scrutinee, exports);
            for (_, lam) in cases {
                collect_exported_idents(lam, exports);
            }
            if let Some(default) = default {
                collect_exported_idents(default, exports);
            }
        }
        RawLambda::LstaticRaise(_, args) => {
            for arg in args {
                collect_exported_idents(arg, exports);
            }
        }
        RawLambda::LstaticCatch(body, (_, _), handler)
        | RawLambda::LtryWith(body, _, handler)
        | RawLambda::Lsequence(body, handler)
        | RawLambda::Lwhile(body, handler) => {
            collect_exported_idents(body, exports);
            collect_exported_idents(handler, exports);
        }
        RawLambda::LifThenElse(cond, then_, else_) => {
            collect_exported_idents(cond, exports);
            collect_exported_idents(then_, exports);
            collect_exported_idents(else_, exports);
        }
        RawLambda::Lfor(_, start, end, _, body) => {
            collect_exported_idents(start, exports);
            collect_exported_idents(end, exports);
            collect_exported_idents(body, exports);
        }
        RawLambda::Lfor_of(_, iterable, body) | RawLambda::Lfor_await_of(_, iterable, body) => {
            collect_exported_idents(iterable, exports);
            collect_exported_idents(body, exports);
        }
        RawLambda::Lbreak | RawLambda::Lcontinue => {}
        RawLambda::Lassign(_, value) | RawLambda::Lsend(_, value, _) => {
            collect_exported_idents(value, exports);
        }
    }
}

fn lower_constant(constant: Constant) -> Constant {
    match constant {
        Constant::Constructor(tag) if tag.name == "()" => Constant::JsUndefined { is_unit: true },
        Constant::Constructor(tag) => match tag.tag_type {
            Some(crate::types::VariantTagType::Int(value)) => Constant::Int {
                i: value,
                comment: None,
            },
            _ => Constant::Constructor(tag),
        },
        Constant::NativeInt { i, comment } => Constant::Int {
            // OCaml's lam_constant_convert.ml truncates source ints here with Int32.of_int.
            i: i as i32,
            comment,
        },
        Constant::Int {
            comment: Some(info),
            ..
        } if matches!(*info, PointerInfo::ShapeNone) => {
            // OCaml compiler/core/lam_constant_convert.ml:40-43 maps
            // Pt_shape_none to Lam_constant.lam_none.
            Constant::JsUndefined { is_unit: false }
        }
        Constant::Int {
            i,
            comment: Some(info),
        } if matches!(*info, PointerInfo::Constructor(_)) => {
            let PointerInfo::Constructor(tag) = *info else {
                unreachable!()
            };
            let i = match tag.runtime_tag.as_ref() {
                Some(ConstructorRuntimeTag::Int(runtime_int)) => {
                    i32::try_from(*runtime_int).unwrap_or(i)
                }
                _ => i,
            };
            match tag.name.as_str() {
                "()" if tag.const_ == 1 && tag.non_const == 0 => {
                    Constant::JsUndefined { is_unit: true }
                }
                _ => Constant::Int {
                    i,
                    comment: Some(Box::new(PointerInfo::Constructor(tag))),
                },
            }
        }
        Constant::Int {
            i: _,
            comment: Some(info),
        } if matches!(*info, PointerInfo::PolyVariant(_)) => {
            let PointerInfo::PolyVariant(name) = *info else {
                unreachable!()
            };
            name.parse::<i32>()
                .map(|i| Constant::Int { i, comment: None })
                .unwrap_or_else(|_| Constant::Pointer(name))
        }
        Constant::String { s, delim } => Constant::String { s, delim },
        Constant::ImmString(s) => Constant::String { s, delim: None },
        Constant::Pointer(name) => match name.strip_suffix('a') {
            Some(raw_int) => raw_int
                .parse::<i32>()
                .map(|i| Constant::Int { i, comment: None })
                .unwrap_or(Constant::Pointer(name)),
            None => Constant::Pointer(name),
        },
        Constant::Block { tag_info, elements } => {
            let mut elements = elements.into_iter().map(lower_constant).collect::<Vec<_>>();
            match *tag_info {
                TagInfo::Some | TagInfo::SomeNotNested if elements.len() == 1 => {
                    Constant::Some(Box::new(elements.remove(0)))
                }
                TagInfo::PolyVar(name) => match elements.len() {
                    2 => {
                        let value = elements.pop().expect("polyvariant block payload");
                        Constant::Block {
                            tag_info: Box::new(TagInfo::PolyVar(name.clone())),
                            elements: vec![polyvar_block_tag_constant(&name), value],
                        }
                    }
                    _ => Constant::Block {
                        tag_info: Box::new(TagInfo::PolyVar(name)),
                        elements,
                    },
                },
                other => Constant::Block {
                    tag_info: Box::new(other),
                    elements,
                },
            }
        }
        Constant::Some(inner) => Constant::Some(Box::new(lower_constant(*inner))),
        other => other,
    }
}

fn polyvar_block_tag_constant(name: &str) -> Constant {
    if is_valid_hash_number(name) {
        Constant::Int {
            i: name
                .parse::<i32>()
                .expect("validated polyvariant hash should fit in i32"),
            comment: None,
        }
    } else {
        Constant::String {
            s: name.to_string(),
            delim: None,
        }
    }
}

fn is_valid_hash_number(value: &str) -> bool {
    let bytes = value.as_bytes();
    match bytes {
        [] => false,
        [b'0'..=b'9'] => true,
        [b'1'..=b'9', rest @ ..] => rest.iter().all(u8::is_ascii_digit),
        _ => false,
    }
}

fn rename_optional_parameters(
    id_gen: &IdGenerator,
    params: Vec<Ident>,
    body: RawLambda,
) -> (Vec<Ident>, RawLambda) {
    let (param_map, body) = rename_optional_parameter_prefix(id_gen, &params, body);
    let params = params
        .into_iter()
        .map(|param| param_map.get(&param).cloned().unwrap_or(param))
        .collect();
    (params, body)
}

fn rename_optional_parameter_prefix(
    id_gen: &IdGenerator,
    params: &[Ident],
    body: RawLambda,
) -> (HashMap<Ident, Ident>, RawLambda) {
    let RawLambda::Llet(kind, id, value, rest) = body else {
        return (HashMap::new(), body);
    };

    let should_rename = matches_optional_parameter_binding(params, value.as_ref());
    if !should_rename {
        return (HashMap::new(), RawLambda::Llet(kind, id, value, rest));
    }

    let (mut param_map, renamed_rest) = rename_optional_parameter_prefix(id_gen, params, *rest);
    let RawLambda::LifThenElse(cond, then_, else_) = *value else {
        unreachable!("validated optional parameter binding")
    };
    let RawLambda::Lprim(cond_info) = *cond else {
        unreachable!("validated optional parameter binding")
    };
    let RawLambda::Lprim(then_info) = *then_ else {
        unreachable!("validated optional parameter binding")
    };
    let [RawLambda::Lvar(opt)] = cond_info.args.as_slice() else {
        unreachable!("validated optional parameter binding")
    };
    let new_id = id_gen.create(&format!("{}Opt", id.name()));
    param_map.insert(opt.clone(), new_id.clone());

    let renamed_value = RawLambda::LifThenElse(
        Box::new(RawLambda::prim(
            cond_info.primitive,
            vec![RawLambda::var(new_id.clone())],
            cond_info.loc,
        )),
        Box::new(RawLambda::prim(
            then_info.primitive,
            vec![RawLambda::var(new_id)],
            then_info.loc,
        )),
        else_,
    );

    (
        param_map,
        RawLambda::Llet(kind, id, Box::new(renamed_value), Box::new(renamed_rest)),
    )
}

fn matches_optional_parameter_binding(params: &[Ident], value: &RawLambda) -> bool {
    let RawLambda::LifThenElse(cond, then_, _) = value else {
        return false;
    };
    let RawLambda::Lprim(cond_info) = cond.as_ref() else {
        return false;
    };
    let RawLambda::Lprim(then_info) = then_.as_ref() else {
        return false;
    };
    let [RawLambda::Lvar(opt)] = cond_info.args.as_slice() else {
        return false;
    };
    let [RawLambda::Lvar(opt2)] = then_info.args.as_slice() else {
        return false;
    };
    opt.same(opt2) && params.iter().any(|param| param.same(opt))
}

fn make_apply(
    func: Lambda,
    args: Vec<Lambda>,
    ap_info: ApInfo,
    ap_transformed_jsx: bool,
) -> Lambda {
    match func {
        Lambda::Lfunction(function) => {
            if let Some(reduced) = eta_reduce_function_apply(&function, &args, &ap_info) {
                return reduced;
            }
            make_lapply(
                Lambda::Lfunction(function),
                args,
                ap_info,
                ap_transformed_jsx,
            )
        }
        Lambda::Llet(kind, id, value, body) => match *body {
            body @ Lambda::Lfunction(_) => Lambda::let_(
                kind,
                id,
                *value,
                make_apply(body, args, ap_info, ap_transformed_jsx),
            ),
            body => make_lapply(
                Lambda::Llet(kind, id, value, Box::new(body)),
                args,
                ap_info,
                ap_transformed_jsx,
            ),
        },
        func => make_lapply(func, args, ap_info, ap_transformed_jsx),
    }
}

fn eta_reduce_function_apply(
    function: &LFunction,
    args: &[Lambda],
    ap_info: &ApInfo,
) -> Option<Lambda> {
    match function.body.as_ref() {
        Lambda::Lprim(__prim1)
            if matches!(
                __prim1.as_ref(),
                PrimInfo {
                    primitive: Primitive::PnullToOpt
                        | Primitive::PnullUndefinedToOpt
                        | Primitive::PisNull
                        | Primitive::PisNullUndefined
                        | Primitive::Ptypeof,
                    args: _wrap_args,
                    ..
                }
            ) =>
        {
            let PrimInfo {
                primitive:
                    Primitive::PnullToOpt
                    | Primitive::PnullUndefinedToOpt
                    | Primitive::PisNull
                    | Primitive::PisNullUndefined
                    | Primitive::Ptypeof,
                args: wrap_args,
                ..
            } = __prim1.as_ref()
            else {
                unreachable!()
            };

            let [Lambda::Lprim(inner_call)] = wrap_args.as_slice() else {
                return None;
            };
            let eta_args = eta_conversion_args(&function.params, &inner_call.args, args)?;
            Some(Lambda::Lprim(Box::new(PrimInfo {
                primitive: function_primitive(function.body.as_ref())?,
                args: vec![Lambda::Lprim(Box::new(PrimInfo {
                    primitive: inner_call.primitive.clone(),
                    args: eta_args,
                    loc: ap_info.loc.clone(),
                }))],
                loc: ap_info.loc.clone(),
            })))
        }
        Lambda::Lprim(inner_call) => {
            let eta_args = eta_conversion_args(&function.params, &inner_call.args, args)?;
            Some(Lambda::Lprim(Box::new(PrimInfo {
                primitive: inner_call.primitive.clone(),
                args: eta_args,
                loc: ap_info.loc.clone(),
            })))
        }
        Lambda::Lsequence(first, second) => {
            let Lambda::Lprim(inner_call) = first.as_ref() else {
                return None;
            };
            let Lambda::Lconst(constant) = second.as_ref() else {
                return None;
            };
            let eta_args = eta_conversion_args(&function.params, &inner_call.args, args)?;
            Some(Lambda::Lsequence(
                Box::new(Lambda::Lprim(Box::new(PrimInfo {
                    primitive: inner_call.primitive.clone(),
                    args: eta_args,
                    loc: ap_info.loc.clone(),
                }))),
                Box::new(Lambda::Lconst(constant.clone())),
            ))
        }
        _ => None,
    }
}

fn function_primitive(body: &Lambda) -> Option<Primitive> {
    match body {
        Lambda::Lprim(__prim0) => {
            let PrimInfo { primitive, .. } = __prim0.as_ref();
            Some(primitive.clone())
        }
        _ => None,
    }
}

fn eta_conversion_args(
    params: &[Ident],
    inner_args: &[Lambda],
    outer_args: &[Lambda],
) -> Option<Vec<Lambda>> {
    if params.len() != inner_args.len() || params.len() != outer_args.len() {
        return None;
    }

    params
        .iter()
        .zip(inner_args.iter())
        .zip(outer_args.iter())
        .map(|((param, inner_arg), outer_arg)| match inner_arg {
            Lambda::Lvar(id) if param.same(id) => Some(outer_arg.clone()),
            _ => None,
        })
        .collect()
}

fn make_lapply(
    func: Lambda,
    args: Vec<Lambda>,
    ap_info: ApInfo,
    ap_transformed_jsx: bool,
) -> Lambda {
    Lambda::Lapply(Box::new(Apply {
        ap_func: Box::new(func),
        ap_args: args,
        ap_info,
        ap_transformed_jsx,
    }))
}

fn bool_const(value: bool) -> Lambda {
    if value {
        Lambda::true_()
    } else {
        Lambda::false_()
    }
}

fn int_const_value_any(lam: &Lambda) -> Option<i32> {
    match lam {
        Lambda::Lconst(Constant::Int { i, .. }) => Some(*i),
        _ => None,
    }
}

fn string_constant_value(constant: &Constant) -> Option<(&str, bool)> {
    match constant {
        Constant::String { s, delim } => Some((s.as_str(), delim.is_none())),
        _ => None,
    }
}

fn float_constant_value(constant: &Constant) -> Option<f64> {
    match constant {
        Constant::Float(value) => value.parse().ok(),
        _ => None,
    }
}

fn pointer_constant_value(constant: &Constant) -> Option<&str> {
    match constant {
        Constant::Pointer(name) => Some(name.as_str()),
        _ => None,
    }
}

fn is_object_create_call(
    prim_name: &str,
    _arg_types: &[crate::lambda::lam_primitive::ExternalArgSpec],
    ffi: &ExternalFfiSpec,
) -> bool {
    prim_name.is_empty() && ffi.obj_params.is_some()
}

fn wrap_ffi_result(call: Lambda, return_wrapper: ExternalReturnWrapper, loc: Location) -> Lambda {
    match return_wrapper {
        ExternalReturnWrapper::Identity => call,
        ExternalReturnWrapper::NullToOpt => Lambda::prim(Primitive::PnullToOpt, vec![call], loc),
        ExternalReturnWrapper::NullUndefinedToOpt => {
            Lambda::prim(Primitive::PnullUndefinedToOpt, vec![call], loc)
        }
        ExternalReturnWrapper::ReplacedWithUnit => Lambda::seq(call, Lambda::unit()),
    }
}

fn lower_primitive_default(primitive: Primitive, args: Vec<Lambda>, loc: Location) -> Lambda {
    match args.as_slice() {
        [Lambda::Lconst(constant)] => match (&primitive, constant) {
            (Primitive::Pnegint, Constant::Int { i, .. }) => {
                return Lambda::const_(Constant::Int {
                    i: i.wrapping_neg(),
                    comment: None,
                });
            }
            (Primitive::Pintoffloat, Constant::Float(value)) => {
                if let Ok(value) = value.parse::<f64>() {
                    return Lambda::const_(Constant::Int {
                        i: value as i32,
                        comment: None,
                    });
                }
            }
            (Primitive::Pstringlength, constant) => {
                if let Some((value, true)) = string_constant_value(constant) {
                    return Lambda::const_(Constant::Int {
                        i: value.len() as i32,
                        comment: None,
                    });
                }
            }
            (Primitive::Pnot, Constant::JsTrue) => return Lambda::false_(),
            (Primitive::Pnot, Constant::JsFalse) => return Lambda::true_(),
            _ => {}
        },
        [Lambda::Lconst(lhs), Lambda::Lconst(rhs)] => match (&primitive, lhs, rhs) {
            (
                Primitive::Pintcomp(comparison),
                Constant::Int { i: lhs, .. },
                Constant::Int { i: rhs, .. },
            ) => {
                return bool_const(comparison.cmp_int32(*lhs, *rhs));
            }
            (Primitive::Pfloatcomp(comparison), lhs, rhs) => {
                if let (Some(lhs), Some(rhs)) =
                    (float_constant_value(lhs), float_constant_value(rhs))
                {
                    return bool_const(comparison.cmp_float(lhs, rhs));
                }
            }
            (Primitive::Pintcomp(Comparison::Eq), lhs, rhs) => {
                if let (Some(lhs), Some(rhs)) =
                    (pointer_constant_value(lhs), pointer_constant_value(rhs))
                {
                    return bool_const(lhs == rhs);
                }
            }
            (Primitive::Pintcomp(Comparison::Neq), lhs, rhs) => {
                if let (Some(lhs), Some(rhs)) =
                    (pointer_constant_value(lhs), pointer_constant_value(rhs))
                {
                    return bool_const(lhs != rhs);
                }
            }
            (Primitive::Paddint, _, _)
            | (Primitive::Psubint, _, _)
            | (Primitive::Pmulint, _, _)
            | (Primitive::Pdivint, _, _)
            | (Primitive::Pmodint, _, _)
            | (Primitive::Pandint, _, _)
            | (Primitive::Porint, _, _)
            | (Primitive::Pxorint, _, _)
            | (Primitive::Plslint, _, _)
            | (Primitive::Plsrint, _, _)
            | (Primitive::Pasrint, _, _) => {
                let Some(lhs) = int_const_value_any(&Lambda::Lconst(lhs.clone())) else {
                    return Lambda::prim(primitive, args, loc);
                };
                let Some(rhs) = int_const_value_any(&Lambda::Lconst(rhs.clone())) else {
                    return Lambda::prim(primitive, args, loc);
                };
                let folded = match primitive {
                    Primitive::Paddint => Some(lhs.wrapping_add(rhs)),
                    Primitive::Psubint => Some(lhs.wrapping_sub(rhs)),
                    Primitive::Pmulint => Some(lhs.wrapping_mul(rhs)),
                    Primitive::Pdivint => (rhs != 0).then(|| lhs.wrapping_div(rhs)),
                    Primitive::Pmodint => (rhs != 0).then(|| lhs.wrapping_rem(rhs)),
                    Primitive::Pandint => Some(lhs & rhs),
                    Primitive::Porint => Some(lhs | rhs),
                    Primitive::Pxorint => Some(lhs ^ rhs),
                    Primitive::Plslint => Some(lhs.wrapping_shl((rhs & 31) as u32)),
                    Primitive::Plsrint => Some(((lhs as u32) >> ((rhs & 31) as u32)) as i32),
                    Primitive::Pasrint => Some(lhs.wrapping_shr((rhs & 31) as u32)),
                    _ => None,
                };
                if let Some(value) = folded {
                    return Lambda::const_(Constant::Int {
                        i: value,
                        comment: None,
                    });
                }
            }
            (Primitive::Psequand, Constant::JsFalse, Constant::JsTrue | Constant::JsFalse)
            | (Primitive::Psequand, Constant::JsTrue, Constant::JsFalse)
            | (Primitive::Psequor, Constant::JsFalse, Constant::JsFalse) => {
                return Lambda::false_();
            }
            (Primitive::Psequand, Constant::JsTrue, Constant::JsTrue)
            | (Primitive::Psequor, Constant::JsTrue, Constant::JsTrue | Constant::JsFalse)
            | (Primitive::Psequor, Constant::JsFalse, Constant::JsTrue) => {
                return Lambda::true_();
            }
            (Primitive::Pstringadd, lhs, rhs) => {
                if let (Some((lhs, true)), Some((rhs, true))) =
                    (string_constant_value(lhs), string_constant_value(rhs))
                {
                    return Lambda::const_(Constant::String {
                        s: format!("{lhs}{rhs}"),
                        delim: None,
                    });
                }
            }
            (Primitive::Pstringrefs | Primitive::Pstringrefu, lhs, Constant::Int { i, .. }) => {
                if let Some((value, true)) = string_constant_value(lhs) {
                    if let Ok(index) = usize::try_from(*i) {
                        if let Some(byte) = value.as_bytes().get(index) {
                            return Lambda::const_(Constant::Char((*byte).into()));
                        }
                    }
                }
            }
            _ => {}
        },
        _ => {}
    }

    if let Primitive::Pmakeblock(TagInfo::Module(fields), _) = &primitive {
        if let Some(module_alias) = collapse_module_alias(fields, &args) {
            return module_alias;
        }
    }

    Lambda::prim(primitive, args, loc)
}

fn is_empty_module_shape_constant(lam: &Lambda) -> bool {
    matches!(
        lam,
        Lambda::Lconst(Constant::Block { elements, .. })
            if matches!(
                elements.as_slice(),
                [Constant::Block { elements: inner, .. }] if inner.is_empty()
            )
    )
}

fn int_constant_value(lam: &Lambda) -> Option<i32> {
    match lam {
        Lambda::Lconst(Constant::Int { i, comment: None }) => Some(*i),
        Lambda::Lconst(Constant::NativeInt { i, comment: None }) => i32::try_from(*i).ok(),
        _ => None,
    }
}

fn happens_to_be_diff(
    sw_consts: &[(crate::lambda::SwitchKey, Lambda)],
    sw_dispatch: &crate::lambda::SwitchDispatch,
) -> Option<i32> {
    if !matches!(sw_dispatch, crate::lambda::SwitchDispatch::Direct) {
        return None;
    }
    let ((crate::lambda::SwitchKey::Int(a), a_lam), rest) = sw_consts.split_first()? else {
        return None;
    };
    let (crate::lambda::SwitchKey::Int(b), b_lam) = rest.first()? else {
        return None;
    };
    let diff = int_constant_value(a_lam)?.checked_sub(*a)?;
    if int_constant_value(b_lam)?.checked_sub(*b)? != diff {
        return None;
    }
    for (key, lam) in rest.iter().skip(1) {
        let crate::lambda::SwitchKey::Int(value) = key else {
            return None;
        };
        if int_constant_value(lam)?.checked_sub(*value)? != diff {
            return None;
        }
    }
    Some(diff)
}

fn collapse_module_alias(fields: &[String], args: &[Lambda]) -> Option<Lambda> {
    let (first_field, rest_fields) = fields.split_first()?;
    let (first_arg, rest_args) = args.split_first()?;

    let (field_name, first_index, module_value) = module_field_access(first_arg)?;
    if field_name != first_field.as_str() || first_index != 0 {
        return None;
    }

    let mut expected_index = 1i32;
    for (field, arg) in rest_fields.iter().zip(rest_args.iter()) {
        let (field_name, arg_index, arg_module_value) = module_field_access(arg)?;
        if field_name != field.as_str()
            || arg_index != expected_index
            || !same_module_source(&module_value, &arg_module_value)
        {
            return None;
        }
        expected_index += 1;
    }

    if rest_fields.len() != rest_args.len() {
        return None;
    }

    Some(module_value)
}

fn module_field_access(arg: &Lambda) -> Option<(String, i32, Lambda)> {
    let Lambda::Lprim(__prim200) = arg else {
        return None;
    };
    let PrimInfo {
        primitive: Primitive::Pfield(index, FieldDbgInfo::Module { name }),
        args,
        ..
    } = __prim200.as_ref()
    else {
        return None;
    };
    let [module_value @ (Lambda::LglobalModule(_, _) | Lambda::Lvar(_))] = args.as_slice() else {
        return None;
    };
    if *index < 0 {
        return None;
    }
    Some((name.clone(), *index, module_value.clone()))
}

fn same_module_source(lhs: &Lambda, rhs: &Lambda) -> bool {
    match (lhs, rhs) {
        (Lambda::Lvar(lhs), Lambda::Lvar(rhs)) => lhs.same(rhs),
        (Lambda::LglobalModule(lhs, lhs_dynamic), Lambda::LglobalModule(rhs, rhs_dynamic)) => {
            lhs.same(rhs) && lhs_dynamic == rhs_dynamic
        }
        _ => false,
    }
}

fn exception_id_destructed(lam: &Lambda, exn: &Ident) -> bool {
    match lam {
        Lambda::Lprim(info)
            if matches!(info.primitive, Primitive::Praise)
                && matches!(info.args.as_slice(), [Lambda::Lvar(_)]) =>
        {
            false
        }
        Lambda::Lprim(info) => info
            .args
            .iter()
            .any(|arg| exception_id_destructed(arg, exn)),
        Lambda::Lvar(id) => id.same(exn),
        Lambda::Lassign(id, expr) => id.same(exn) || exception_id_destructed(expr, exn),
        Lambda::LstaticCatch(body, _, handler) | Lambda::LtryWith(body, _, handler) => {
            exception_id_destructed(body, exn) || exception_id_destructed(handler, exn)
        }
        Lambda::Lfunction(func) => exception_id_destructed(&func.body, exn),
        Lambda::Llet(_, _, arg, body) => {
            exception_id_destructed(arg, exn) || exception_id_destructed(body, exn)
        }
        Lambda::Lletrec(bindings, body) => {
            exception_id_destructed(body, exn)
                || bindings
                    .iter()
                    .any(|(_, lam)| exception_id_destructed(lam, exn))
        }
        Lambda::Lfor(_, lo, hi, _, body) => {
            exception_id_destructed(lo, exn)
                || exception_id_destructed(hi, exn)
                || exception_id_destructed(body, exn)
        }
        Lambda::Lfor_of(_, iterable, body) | Lambda::Lfor_await_of(_, iterable, body) => {
            exception_id_destructed(iterable, exn) || exception_id_destructed(body, exn)
        }
        Lambda::Lconst(_) | Lambda::LglobalModule(_, _) => false,
        Lambda::Lapply(apply) => {
            exception_id_destructed(&apply.ap_func, exn)
                || apply
                    .ap_args
                    .iter()
                    .any(|arg| exception_id_destructed(arg, exn))
        }
        Lambda::Lswitch(arg, switch) => {
            exception_id_destructed(arg, exn)
                || switch
                    .sw_consts
                    .iter()
                    .any(|(_, lam)| exception_id_destructed(lam, exn))
                || switch
                    .sw_blocks
                    .iter()
                    .any(|(_, lam)| exception_id_destructed(lam, exn))
                || switch
                    .sw_failaction
                    .as_deref()
                    .is_some_and(|lam| exception_id_destructed(lam, exn))
        }
        Lambda::LstringSwitch(arg, cases, default) => {
            exception_id_destructed(arg, exn)
                || cases
                    .iter()
                    .any(|(_, lam)| exception_id_destructed(lam, exn))
                || default
                    .as_deref()
                    .is_some_and(|lam| exception_id_destructed(lam, exn))
        }
        Lambda::LstaticRaise(_, args) => args.iter().any(|arg| exception_id_destructed(arg, exn)),
        Lambda::LifThenElse(cond, then_, else_) => {
            exception_id_destructed(cond, exn)
                || exception_id_destructed(then_, exn)
                || exception_id_destructed(else_, exn)
        }
        Lambda::Lsequence(first, second) | Lambda::Lwhile(first, second) => {
            exception_id_destructed(first, exn) || exception_id_destructed(second, exn)
        }
        Lambda::Lbreak | Lambda::Lcontinue => false,
    }
}

fn hit_variable(target: &Ident, lam: &Lambda) -> bool {
    match lam {
        Lambda::Lvar(id) => id.same(target),
        Lambda::LglobalModule(_, _) | Lambda::Lconst(_) => false,
        Lambda::Lapply(apply) => {
            hit_variable(target, &apply.ap_func)
                || apply.ap_args.iter().any(|arg| hit_variable(target, arg))
        }
        Lambda::Lfunction(func) => hit_variable(target, &func.body),
        Lambda::Llet(_, _, value, body) => {
            hit_variable(target, value) || hit_variable(target, body)
        }
        Lambda::Lletrec(bindings, body) => {
            hit_variable(target, body) || bindings.iter().any(|(_, lam)| hit_variable(target, lam))
        }
        Lambda::Lprim(info) => info.args.iter().any(|arg| hit_variable(target, arg)),
        Lambda::Lswitch(arg, switch) => {
            hit_variable(target, arg)
                || switch
                    .sw_consts
                    .iter()
                    .any(|(_, lam)| hit_variable(target, lam))
                || switch
                    .sw_blocks
                    .iter()
                    .any(|(_, lam)| hit_variable(target, lam))
                || switch
                    .sw_failaction
                    .as_deref()
                    .is_some_and(|lam| hit_variable(target, lam))
        }
        Lambda::LstringSwitch(arg, cases, default) => {
            hit_variable(target, arg)
                || cases.iter().any(|(_, lam)| hit_variable(target, lam))
                || default
                    .as_deref()
                    .is_some_and(|lam| hit_variable(target, lam))
        }
        Lambda::LstaticRaise(_, args) => args.iter().any(|arg| hit_variable(target, arg)),
        Lambda::LstaticCatch(body, _, handler) | Lambda::LtryWith(body, _, handler) => {
            hit_variable(target, body) || hit_variable(target, handler)
        }
        Lambda::LifThenElse(cond, then_, else_) => {
            hit_variable(target, cond) || hit_variable(target, then_) || hit_variable(target, else_)
        }
        Lambda::Lsequence(first, second) | Lambda::Lwhile(first, second) => {
            hit_variable(target, first) || hit_variable(target, second)
        }
        Lambda::Lfor(_, start, end, _, body) => {
            hit_variable(target, start) || hit_variable(target, end) || hit_variable(target, body)
        }
        Lambda::Lfor_of(_, iterable, body) | Lambda::Lfor_await_of(_, iterable, body) => {
            hit_variable(target, iterable) || hit_variable(target, body)
        }
        Lambda::Lbreak | Lambda::Lcontinue => false,
        Lambda::Lassign(id, value) => id.same(target) || hit_variable(target, value),
    }
}

fn fold_offset_switch_alias(id: &Ident, value: &Lambda, body: &Lambda) -> Option<Lambda> {
    let Lambda::Lprim(info) = value else {
        return None;
    };
    let Primitive::Poffsetint(offset) = info.primitive else {
        return None;
    };
    let [matcher] = info.args.as_slice() else {
        return None;
    };
    let Lambda::Lswitch(scrutinee, switch) = body else {
        return None;
    };
    let Lambda::Lvar(switch_id) = scrutinee.as_ref() else {
        return None;
    };
    if !switch_id.same(id) {
        return None;
    }
    if !switch.sw_blocks.is_empty() {
        return None;
    }
    if switch
        .sw_failaction
        .as_deref()
        .is_some_and(|lam| hit_variable(id, lam))
    {
        return None;
    }
    if switch
        .sw_consts
        .iter()
        .any(|(_, lam)| hit_variable(id, lam))
    {
        return None;
    }

    Some(Lambda::Lswitch(
        Box::new(matcher.clone()),
        Box::new(LambdaSwitch {
            sw_consts_full: switch.sw_consts_full,
            sw_consts: switch
                .sw_consts
                .iter()
                .map(|(key, lam)| match key {
                    crate::lambda::SwitchKey::Int(value) => {
                        (crate::lambda::SwitchKey::Int(*value - offset), lam.clone())
                    }
                    crate::lambda::SwitchKey::Constructor(_) => {
                        unreachable!("offset constructor switch")
                    }
                })
                .collect(),
            sw_blocks_full: switch.sw_blocks_full,
            sw_blocks: Vec::new(),
            sw_failaction: switch.sw_failaction.clone(),
            sw_dispatch: switch.sw_dispatch.clone(),
        }),
    ))
}

fn rebuild_recursive_bindings(bindings: Vec<(Ident, Lambda)>, body: Lambda) -> Lambda {
    match bindings.as_slice() {
        [] => body,
        [(id, bind)] => {
            if hit_variable(id, bind) {
                Lambda::letrec(bindings, body)
            } else {
                Lambda::let_(LetKind::Strict, id.clone(), bind.clone(), body)
            }
        }
        _ => {
            if bindings.iter().all(|(id, bind)| hit_variable(id, bind)) {
                return Lambda::letrec(bindings, body);
            }
            let deps = binding_dependencies(&bindings);
            let components = strongly_connected_binding_components(&deps);
            if components.len() <= 1 {
                Lambda::letrec(bindings, body)
            } else {
                rebuild_component_groups(&bindings, &deps, components, body)
            }
        }
    }
}

enum RecursiveComponentGroup {
    Strict(usize),
    Recursive(Vec<usize>),
}

fn rebuild_component_groups(
    bindings: &[(Ident, Lambda)],
    deps: &[Vec<usize>],
    components: Vec<Vec<usize>>,
    body: Lambda,
) -> Lambda {
    let mut groups: Vec<RecursiveComponentGroup> = Vec::new();

    for component in components {
        if let [index] = component.as_slice() {
            if !deps[*index].contains(index) && !has_incoming_dependency(*index, deps) {
                groups.push(RecursiveComponentGroup::Strict(*index));
                continue;
            }
        }

        match groups.last_mut() {
            Some(RecursiveComponentGroup::Recursive(indices)) => indices.extend(component),
            _ => groups.push(RecursiveComponentGroup::Recursive(component)),
        }
    }

    groups
        .into_iter()
        .rev()
        .fold(body, |acc, group| match group {
            RecursiveComponentGroup::Strict(index) => {
                let (id, bind) = bindings[index].clone();
                Lambda::let_(LetKind::Strict, id, bind, acc)
            }
            RecursiveComponentGroup::Recursive(indices) => {
                let group = indices
                    .into_iter()
                    .map(|index| bindings[index].clone())
                    .collect::<Vec<_>>();
                Lambda::letrec(group, acc)
            }
        })
}

fn has_incoming_dependency(target: usize, deps: &[Vec<usize>]) -> bool {
    deps.iter()
        .enumerate()
        .any(|(source, outgoing)| source != target && outgoing.contains(&target))
}

fn binding_dependencies(bindings: &[(Ident, Lambda)]) -> Vec<Vec<usize>> {
    let len = bindings.len();
    if len == 0 {
        return Vec::new();
    }

    // OCaml's Lam_scc.preprocess_deps accidentally shares one Vec_int across
    // every row (`Array.make ... (Vec_int.empty ())`) at lam_scc.ml:80-88.
    // Preserve that exact dependency graph: each row receives the union of all
    // group-local hits, appended in Ordered_hash_map_local_ident.iter order.
    let domain_order = ocaml_local_ident_hash_iteration_order(bindings);
    let mask_order = ocaml_ident_mask_iteration_order(bindings);
    let mut shared = Vec::new();

    for binding_index in domain_order {
        let lam = &bindings[binding_index].1;
        for dep_index in &mask_order {
            if hit_variable(&bindings[*dep_index].0, lam) {
                shared.push(*dep_index);
            }
        }
    }

    vec![shared; len]
}

fn ocaml_local_ident_hash_iteration_order(bindings: &[(Ident, Lambda)]) -> Vec<usize> {
    let bucket_len = ocaml_hashtbl_power_2_above(16, bindings.len());
    let mut buckets = vec![Vec::<usize>::new(); bucket_len];
    for (index, (id, _)) in bindings.iter().enumerate() {
        let bucket = (ocaml_hash_int(id.stamp()) as usize) & (bucket_len - 1);
        buckets[bucket].insert(0, index);
    }
    buckets.into_iter().flatten().collect()
}

fn ocaml_ident_mask_iteration_order(bindings: &[(Ident, Lambda)]) -> Vec<usize> {
    let bucket_len = ocaml_hashtbl_power_2_above(8, bindings.len());
    let mut buckets = vec![Vec::<usize>::new(); bucket_len];
    for (index, (id, _)) in bindings.iter().enumerate() {
        let bucket = (ocaml_hash_string_int(id.name(), id.stamp()) as usize) & (bucket_len - 1);
        buckets[bucket].insert(0, index);
    }
    buckets.into_iter().flatten().collect()
}

fn ocaml_hashtbl_power_2_above(mut x: usize, n: usize) -> usize {
    while x < n {
        x <<= 1;
    }
    x
}

fn ocaml_hash_int(i: i32) -> u32 {
    ocaml_hash_final_mix(ocaml_hash_mix_uint32(0, ocaml_tagged_int_bits(i))) & 0x3fff_ffff
}

fn ocaml_hash_string_int(s: &str, i: i32) -> u32 {
    let h = ocaml_hash_mix_string(0, s);
    ocaml_hash_final_mix(ocaml_hash_mix_uint32(h, ocaml_tagged_int_bits(i))) & 0x3fff_ffff
}

fn ocaml_tagged_int_bits(i: i32) -> u32 {
    ((i as u32) << 1) | 1
}

fn ocaml_hash_mix_string(mut h: u32, s: &str) -> u32 {
    let bytes = s.as_bytes();
    let len = bytes.len();
    let mut i = 0usize;

    while i + 4 <= len {
        let word = u32::from_le_bytes([bytes[i], bytes[i + 1], bytes[i + 2], bytes[i + 3]]);
        h = ocaml_hash_mix_uint32(h, word);
        i += 4;
    }

    let rem = len & 3;
    if rem != 0 {
        let mut word = 0u32;
        if rem >= 3 {
            word |= (bytes[i + 2] as u32) << 16;
        }
        if rem >= 2 {
            word |= (bytes[i + 1] as u32) << 8;
        }
        word |= bytes[i] as u32;
        h = ocaml_hash_mix_uint32(h, word);
    }

    h ^ (len as u32)
}

fn ocaml_hash_mix_uint32(mut h: u32, mut d: u32) -> u32 {
    d = d.wrapping_mul(0xcc9e2d51);
    d = d.rotate_left(15);
    d = d.wrapping_mul(0x1b873593);
    h ^= d;
    h = h.rotate_left(13);
    h = h.wrapping_mul(5).wrapping_add(0xe6546b64);
    h
}

fn ocaml_hash_final_mix(mut h: u32) -> u32 {
    h ^= h >> 16;
    h = h.wrapping_mul(0x85ebca6b);
    h ^= h >> 13;
    h = h.wrapping_mul(0xc2b2ae35);
    h ^= h >> 16;
    h
}

fn strongly_connected_binding_components(deps: &[Vec<usize>]) -> Vec<Vec<usize>> {
    struct TarjanState {
        index: usize,
        stack: Vec<usize>,
        on_stack: Vec<bool>,
        indices: Vec<Option<usize>>,
        lowlink: Vec<usize>,
        components: Vec<Vec<usize>>,
    }

    fn strong_connect(node: usize, deps: &[Vec<usize>], state: &mut TarjanState) {
        state.indices[node] = Some(state.index);
        state.lowlink[node] = state.index;
        state.index += 1;
        state.stack.push(node);
        state.on_stack[node] = true;

        for &dep in &deps[node] {
            if state.indices[dep].is_none() {
                strong_connect(dep, deps, state);
                state.lowlink[node] = state.lowlink[node].min(state.lowlink[dep]);
            } else if state.on_stack[dep] {
                state.lowlink[node] =
                    state.lowlink[node].min(state.indices[dep].expect("visited node"));
            }
        }

        if state.lowlink[node] == state.indices[node].expect("visited node") {
            let mut component = Vec::new();
            loop {
                let current = state.stack.pop().expect("tarjan stack");
                state.on_stack[current] = false;
                component.push(current);
                if current == node {
                    break;
                }
            }
            // OCaml's Ext_scc.graph returns the contiguous stack range in stack
            // order (`Vec_int.get_and_delete_range`) at ext_scc.ml:80-91.
            component.reverse();
            state.components.push(component);
        }
    }

    let len = deps.len();
    let mut state = TarjanState {
        index: 0,
        stack: Vec::new(),
        on_stack: vec![false; len],
        indices: vec![None; len],
        lowlink: vec![0; len],
        components: Vec::new(),
    };

    for node in 0..len {
        if state.indices[node].is_none() {
            strong_connect(node, &deps, &mut state);
        }
    }

    state.components
}

/// Lower raw lambda into the existing JS-facing Lambda IR.
fn max_ident_stamp(raw: &RawLambda) -> i32 {
    fn visit_ident(max_stamp: &mut i32, id: &Ident) {
        *max_stamp = (*max_stamp).max(id.stamp());
    }

    fn visit_raw(max_stamp: &mut i32, raw: &RawLambda) {
        match raw {
            RawLambda::Lshared(inner) => visit_raw(max_stamp, inner),
            RawLambda::Lvar(id) | RawLambda::LglobalModule(id, _) => visit_ident(max_stamp, id),
            RawLambda::Lconst(_) => {}
            RawLambda::Lapply(apply) => {
                visit_raw(max_stamp, &apply.ap_func);
                for arg in &apply.ap_args {
                    visit_raw(max_stamp, arg);
                }
            }
            RawLambda::Lfunction(func) => {
                for param in &func.params {
                    visit_ident(max_stamp, param);
                }
                visit_raw(max_stamp, &func.body);
            }
            RawLambda::Llet(_, id, value, body) => {
                visit_ident(max_stamp, id);
                visit_raw(max_stamp, value);
                visit_raw(max_stamp, body);
            }
            RawLambda::Lletrec(bindings, body) => {
                for (id, lam) in bindings {
                    visit_ident(max_stamp, id);
                    visit_raw(max_stamp, lam);
                }
                visit_raw(max_stamp, body);
            }
            RawLambda::Lprim(info) => {
                if let Primitive::Pmakeblock(TagInfo::ModuleExport(ids), _) = &info.primitive {
                    for id in ids {
                        visit_ident(max_stamp, id);
                    }
                }
                for arg in &info.args {
                    visit_raw(max_stamp, arg);
                }
            }
            RawLambda::Lswitch(scrutinee, switch, _) => {
                visit_raw(max_stamp, scrutinee);
                for (_, lam) in &switch.sw_consts {
                    visit_raw(max_stamp, lam);
                }
                for (_, lam) in &switch.sw_blocks {
                    visit_raw(max_stamp, lam);
                }
                if let Some(failaction) = &switch.sw_failaction {
                    visit_raw(max_stamp, failaction);
                }
            }
            RawLambda::LstringSwitch(scrutinee, cases, default) => {
                visit_raw(max_stamp, scrutinee);
                for (_, lam) in cases {
                    visit_raw(max_stamp, lam);
                }
                if let Some(default) = default {
                    visit_raw(max_stamp, default);
                }
            }
            RawLambda::LstaticRaise(_, args) => {
                for arg in args {
                    visit_raw(max_stamp, arg);
                }
            }
            RawLambda::LstaticCatch(body, (_, ids), handler) => {
                for id in ids {
                    visit_ident(max_stamp, id);
                }
                visit_raw(max_stamp, body);
                visit_raw(max_stamp, handler);
            }
            RawLambda::LtryWith(body, id, handler) => {
                visit_ident(max_stamp, id);
                visit_raw(max_stamp, body);
                visit_raw(max_stamp, handler);
            }
            RawLambda::LifThenElse(cond, then_, else_) => {
                visit_raw(max_stamp, cond);
                visit_raw(max_stamp, then_);
                visit_raw(max_stamp, else_);
            }
            RawLambda::Lsequence(first, second) => {
                visit_raw(max_stamp, first);
                visit_raw(max_stamp, second);
            }
            RawLambda::Lwhile(cond, body) => {
                visit_raw(max_stamp, cond);
                visit_raw(max_stamp, body);
            }
            RawLambda::Lfor(id, start, end, _, body) => {
                visit_ident(max_stamp, id);
                visit_raw(max_stamp, start);
                visit_raw(max_stamp, end);
                visit_raw(max_stamp, body);
            }
            RawLambda::Lfor_of(id, iterable, body)
            | RawLambda::Lfor_await_of(id, iterable, body) => {
                visit_ident(max_stamp, id);
                visit_raw(max_stamp, iterable);
                visit_raw(max_stamp, body);
            }
            RawLambda::Lassign(id, value) => {
                visit_ident(max_stamp, id);
                visit_raw(max_stamp, value);
            }
            RawLambda::Lsend(_, obj, _) => visit_raw(max_stamp, obj),
            RawLambda::Lbreak | RawLambda::Lcontinue => {}
        }
    }

    let mut max_stamp = 0;
    visit_raw(&mut max_stamp, raw);
    max_stamp
}

#[cfg(test)]
pub(crate) fn max_ident_stamp_for_test(raw: &RawLambda) -> i32 {
    max_ident_stamp(raw)
}

pub fn lower_to_lambda_with_start_stamp(raw: RawLambda, start_stamp: i32) -> Lambda {
    let mut exported_idents = HashSet::new();
    collect_exported_idents(&raw, &mut exported_idents);
    let id_gen = IdGenerator::with_start_stamp(start_stamp);
    LoweringContext::with_id_gen(exported_idents, &id_gen).lower_lambda(raw)
}

/// Additive M5 entrypoint for the inactive indexed pipeline. The caller keeps
/// this exact generator through optimization and later JS lowering.
pub(crate) fn lower_to_lambda_with_id_gen(raw: RawLambda, id_gen: Arc<IdGenerator>) -> Lambda {
    let mut exported_idents = HashSet::new();
    collect_exported_idents(&raw, &mut exported_idents);
    LoweringContext::with_id_gen(exported_idents, &id_gen).lower_lambda(raw)
}

pub fn lower_to_lambda(raw: RawLambda) -> Lambda {
    let start_stamp = max_ident_stamp(&raw);
    lower_to_lambda_with_start_stamp(raw, start_stamp)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lambda::FunctionAttribute;
    use crate::lambda::InlineAttribute;
    use crate::lambda::lam_compat::LetKind;
    use crate::lambda::lam_constant::{ConstructorRuntimeTag, ConstructorTag, StringDelim};
    use crate::lambda::lam_primitive::{ExternalFfiKind, JsRawInfo, Mutable};

    #[test]
    fn shared_generator_entrypoint_preserves_the_caller_owned_stamp_stream() {
        let generator = Arc::new(IdGenerator::with_start_stamp(41));
        let exception = Ident::new("caught", 7, crate::ident::IdentFlags::NONE);
        let lowered = lower_to_lambda_with_id_gen(
            RawLambda::LtryWith(
                Box::new(RawLambda::unit()),
                exception.clone(),
                Box::new(RawLambda::var(exception)),
            ),
            generator.clone(),
        );
        let Lambda::LtryWith(_, raw_exception, handler) = lowered else {
            panic!("expected lowered try-with");
        };
        assert_eq!(raw_exception.name(), "raw_caught");
        assert_eq!(raw_exception.stamp(), 42);
        assert!(matches!(
            *handler,
            Lambda::Llet(LetKind::StrictOpt, _, _, _)
        ));
        assert_eq!(generator.create("after_lower").stamp(), 43);
    }

    #[test]
    fn lowers_unit_constructor_pointer_to_unit_constant() {
        let raw = RawLambda::const_(Constant::Int {
            i: 0,
            comment: Some(Box::new(PointerInfo::Constructor(ConstructorTag {
                name: "()".to_string(),
                const_: 1,
                non_const: 0,
                runtime_tag: None,
            }))),
        });

        assert!(matches!(
            lower_to_lambda(raw),
            Lambda::Lconst(Constant::JsUndefined { is_unit: true })
        ));
    }

    #[test]
    fn lowers_apply_to_uncurry_status() {
        let func = Ident::create_local("f");
        let arg = Ident::create_local("x");
        let raw = RawLambda::Lapply(Box::new(RawApply {
            ap_func: Box::new(RawLambda::var(func)),
            ap_args: vec![RawLambda::var(arg)],
            ap_info: ApInfo {
                loc: Location::none(),
                inlined: InlineAttribute::Default,
                status: ApplyStatus::Na,
            },
            ap_transformed_jsx: false,
        }));

        let lowered = lower_to_lambda(raw);
        let Lambda::Lapply(apply) = lowered else {
            panic!("expected Lapply");
        };
        assert_eq!(apply.ap_info.status, ApplyStatus::Uncurry);
    }

    #[test]
    fn eta_reduces_primitive_wrapper_application() {
        let prim0 = Ident::create_local("prim0");
        let prim1 = Ident::create_local("prim1");
        let lhs = Ident::create_local("lhs");
        let rhs = Ident::create_local("rhs");
        let raw = RawLambda::Lapply(Box::new(RawApply {
            ap_func: Box::new(RawLambda::function_(
                2,
                vec![prim0.clone(), prim1.clone()],
                RawLambda::prim(
                    Primitive::Paddint,
                    vec![RawLambda::var(prim0.clone()), RawLambda::var(prim1.clone())],
                    Location::none(),
                ),
                crate::lambda::FunctionAttribute::default(),
            )),
            ap_args: vec![RawLambda::var(lhs.clone()), RawLambda::var(rhs.clone())],
            ap_info: ApInfo {
                loc: Location::none(),
                inlined: InlineAttribute::Default,
                status: ApplyStatus::Na,
            },
            ap_transformed_jsx: false,
        }));

        let lowered = lower_to_lambda(raw);
        let Lambda::Lprim(info) = lowered else {
            panic!("expected primitive application");
        };
        assert!(matches!(info.primitive, Primitive::Paddint));
        let [Lambda::Lvar(actual_lhs), Lambda::Lvar(actual_rhs)] = info.args.as_slice() else {
            panic!("expected lowered primitive arguments");
        };
        assert!(actual_lhs.same(&lhs));
        assert!(actual_rhs.same(&rhs));
    }

    #[test]
    fn renames_optional_parameter_guards_from_prefix_lets() {
        let opt_x = Ident::create_local("*opt*");
        let y = Ident::create_local("y");
        let opt_z = Ident::create_local("*opt*");
        let x = Ident::create_local("x");
        let z = Ident::create_local("z");
        let raw = RawLambda::function_(
            3,
            vec![opt_x.clone(), y.clone(), opt_z.clone()],
            RawLambda::let_(
                LetKind::Strict,
                x.clone(),
                RawLambda::LifThenElse(
                    Box::new(RawLambda::prim(
                        Primitive::PisNotNone,
                        vec![RawLambda::var(opt_x.clone())],
                        Location::none(),
                    )),
                    Box::new(RawLambda::prim(
                        Primitive::PvalFromOptionNotNest,
                        vec![RawLambda::var(opt_x.clone())],
                        Location::none(),
                    )),
                    Box::new(RawLambda::const_(Constant::int(3))),
                ),
                RawLambda::let_(
                    LetKind::Strict,
                    z.clone(),
                    RawLambda::LifThenElse(
                        Box::new(RawLambda::prim(
                            Primitive::PisNotNone,
                            vec![RawLambda::var(opt_z.clone())],
                            Location::none(),
                        )),
                        Box::new(RawLambda::prim(
                            Primitive::PvalFromOptionNotNest,
                            vec![RawLambda::var(opt_z.clone())],
                            Location::none(),
                        )),
                        Box::new(RawLambda::const_(Constant::int(4))),
                    ),
                    RawLambda::prim(
                        Primitive::Paddint,
                        vec![RawLambda::var(x), RawLambda::var(z)],
                        Location::none(),
                    ),
                ),
            ),
            crate::lambda::FunctionAttribute::default(),
        );

        let lowered = lower_to_lambda_with_start_stamp(raw, 41);
        let Lambda::Lfunction(func) = lowered else {
            panic!("expected function");
        };
        assert_eq!(func.params[0].name(), "xOpt");
        assert_eq!(func.params[1].name(), "y");
        assert_eq!(func.params[2].name(), "zOpt");
        assert_eq!(func.params[0].stamp(), 43);
        assert_eq!(func.params[2].stamp(), 42);

        let Lambda::Llet(LetKind::Strict, _, first_value, first_rest) = func.body.as_ref() else {
            panic!("expected first strict let");
        };
        let Lambda::LifThenElse(first_cond, first_then, _) = first_value.as_ref() else {
            panic!("expected first optional guard");
        };
        let Lambda::Lprim(first_cond_prim) = first_cond.as_ref() else {
            panic!("expected first guard primitive");
        };
        let [Lambda::Lvar(first_guard_param)] = first_cond_prim.args.as_slice() else {
            panic!("expected first guard to use renamed param");
        };
        assert!(first_guard_param.same(&func.params[0]));
        let Lambda::Lprim(first_then_prim) = first_then.as_ref() else {
            panic!("expected first unwrap primitive");
        };
        let [Lambda::Lvar(first_unwrap_param)] = first_then_prim.args.as_slice() else {
            panic!("expected first unwrap to use renamed param");
        };
        assert!(first_unwrap_param.same(&func.params[0]));

        let Lambda::Llet(LetKind::Strict, _, second_value, _) = first_rest.as_ref() else {
            panic!("expected second strict let");
        };
        let Lambda::LifThenElse(second_cond, second_then, _) = second_value.as_ref() else {
            panic!("expected second optional guard");
        };
        let Lambda::Lprim(second_cond_prim) = second_cond.as_ref() else {
            panic!("expected second guard primitive");
        };
        let [Lambda::Lvar(second_guard_param)] = second_cond_prim.args.as_slice() else {
            panic!("expected second guard to use renamed param");
        };
        assert!(second_guard_param.same(&func.params[2]));
        let Lambda::Lprim(second_then_prim) = second_then.as_ref() else {
            panic!("expected second unwrap primitive");
        };
        let [Lambda::Lvar(second_unwrap_param)] = second_then_prim.args.as_slice() else {
            panic!("expected second unwrap to use renamed param");
        };
        assert!(second_unwrap_param.same(&func.params[2]));
    }

    #[test]
    fn lowers_blank_js_call_to_object_create() {
        let raw = RawLambda::prim(
            Primitive::PjsCall {
                prim_name: String::new(),
                arg_types: vec![crate::lambda::lam_primitive::ExternalArgSpec::dummy()],
                ffi: Box::new(crate::lambda::lam_primitive::ExternalFfiSpec {
                    kind: ExternalFfiKind::ObjCreate,
                    spec: None,
                    obj_params: Some(vec![crate::lambda::lam_primitive::ExternalObjSpec {
                        obj_arg_type: crate::lambda::lam_primitive::ExternalArgAttr::Nothing,
                        obj_arg_label: crate::lambda::lam_primitive::ExternalObjLabel::Label {
                            name: "name".to_string(),
                        },
                    }]),
                    return_wrapper: ExternalReturnWrapper::Identity,
                    inline_constant: None,
                }),
                dynamic_import: false,
                transformed_jsx: false,
            },
            vec![RawLambda::unit()],
            Location::none(),
        );

        let lowered = lower_to_lambda(raw);
        let Lambda::Lprim(info) = lowered else {
            panic!("expected Lprim");
        };
        assert!(matches!(info.primitive, Primitive::PjsObjectCreate(_)));
    }

    #[test]
    fn lowers_labeled_blank_js_call_to_object_create_without_objcreate_kind() {
        let raw = RawLambda::prim(
            Primitive::PjsCall {
                prim_name: String::new(),
                arg_types: vec![crate::lambda::lam_primitive::ExternalArgSpec::dummy()],
                ffi: Box::new(crate::lambda::lam_primitive::ExternalFfiSpec {
                    kind: ExternalFfiKind::Default,
                    spec: None,
                    obj_params: Some(vec![crate::lambda::lam_primitive::ExternalObjSpec {
                        obj_arg_type: crate::lambda::lam_primitive::ExternalArgAttr::Nothing,
                        obj_arg_label: crate::lambda::lam_primitive::ExternalObjLabel::Label {
                            name: "name".to_string(),
                        },
                    }]),
                    return_wrapper: ExternalReturnWrapper::Identity,
                    inline_constant: None,
                }),
                dynamic_import: false,
                transformed_jsx: false,
            },
            vec![RawLambda::unit()],
            Location::none(),
        );

        let lowered = lower_to_lambda(raw);
        let Lambda::Lprim(info) = lowered else {
            panic!("expected Lprim");
        };
        assert!(matches!(info.primitive, Primitive::PjsObjectCreate(_)));
    }

    #[test]
    fn lowers_extension_slot_eq_via_exception_id_field() {
        let exn = Ident::create_local("exn");
        let slot = Ident::create_local("slot");
        let lowered = lower_to_lambda(RawLambda::prim(
            Primitive::PextensionSlotEq,
            vec![RawLambda::var(exn.clone()), RawLambda::var(slot.clone())],
            Location::none(),
        ));

        let Lambda::Lprim(info) = lowered else {
            panic!("expected Lprim");
        };
        assert!(matches!(
            info.primitive,
            Primitive::Pstringcomp(Comparison::Eq)
        ));
        let [lhs, Lambda::Lvar(rhs)] = info.args.as_slice() else {
            panic!("expected string comparison arguments");
        };
        assert!(rhs.same(&slot));

        let Lambda::Lprim(field) = lhs else {
            panic!("expected exception id field access");
        };
        assert!(matches!(
            field.primitive,
            Primitive::Pfield(
                0,
                FieldDbgInfo::Record { ref name }
            ) if name == EXCEPTION_ID_FIELD
        ));
        let [Lambda::Lvar(field_exn)] = field.args.as_slice() else {
            panic!("expected exception id field receiver");
        };
        assert!(field_exn.same(&exn));
    }

    #[test]
    fn keeps_unlabeled_blank_js_call_as_call() {
        let raw = RawLambda::prim(
            Primitive::PjsCall {
                prim_name: String::new(),
                arg_types: vec![
                    crate::lambda::lam_primitive::ExternalArgSpec::dummy(),
                    crate::lambda::lam_primitive::ExternalArgSpec::dummy(),
                ],
                ffi: Box::new(crate::lambda::lam_primitive::ExternalFfiSpec {
                    kind: ExternalFfiKind::Default,
                    spec: None,
                    obj_params: None,
                    return_wrapper: ExternalReturnWrapper::Identity,
                    inline_constant: None,
                }),
                dynamic_import: false,
                transformed_jsx: false,
            },
            vec![RawLambda::unit(), RawLambda::unit()],
            Location::none(),
        );

        let lowered = lower_to_lambda(raw);
        let Lambda::Lprim(info) = lowered else {
            panic!("expected Lprim");
        };
        assert!(matches!(
            info.primitive,
            Primitive::PjsCall { ref prim_name, .. } if prim_name.is_empty()
        ));
    }

    #[test]
    fn lowers_blank_js_call_with_inline_constant_to_constant() {
        let lowered = lower_to_lambda(RawLambda::prim(
            Primitive::PjsCall {
                prim_name: String::new(),
                arg_types: Vec::new(),
                ffi: Box::new(crate::lambda::lam_primitive::ExternalFfiSpec {
                    kind: ExternalFfiKind::Default,
                    spec: None,
                    obj_params: None,
                    return_wrapper: ExternalReturnWrapper::Identity,
                    inline_constant: Some(Constant::String {
                        s: "hello".to_string(),
                        delim: Some(crate::lambda::lam_constant::StringDelim::StarJ),
                    }),
                }),
                dynamic_import: false,
                transformed_jsx: false,
            },
            Vec::new(),
            Location::none(),
        ));

        assert!(matches!(
            lowered,
            Lambda::Lconst(Constant::String { ref s, delim: Some(crate::lambda::lam_constant::StringDelim::StarJ) }) if s == "hello"
        ));
    }

    #[test]
    fn wraps_null_to_opt_return_wrapper_around_js_call() {
        let lowered = lower_to_lambda(RawLambda::prim(
            Primitive::PjsCall {
                prim_name: "get".to_string(),
                arg_types: vec![crate::lambda::lam_primitive::ExternalArgSpec::dummy()],
                ffi: Box::new(crate::lambda::lam_primitive::ExternalFfiSpec {
                    kind: ExternalFfiKind::Default,
                    spec: None,
                    obj_params: None,
                    return_wrapper: ExternalReturnWrapper::NullToOpt,
                    inline_constant: None,
                }),
                dynamic_import: false,
                transformed_jsx: false,
            },
            vec![RawLambda::var(Ident::create_local("obj"))],
            Location::none(),
        ));

        let Lambda::Lprim(info) = lowered else {
            panic!("expected wrapper primitive");
        };
        assert!(matches!(info.primitive, Primitive::PnullToOpt));
        let [Lambda::Lprim(inner)] = info.args.as_slice() else {
            panic!("expected wrapped js call");
        };
        assert!(matches!(
            inner.primitive,
            Primitive::PjsCall { ref prim_name, .. } if prim_name == "get"
        ));
    }

    #[test]
    fn wraps_nullable_return_wrapper_around_js_call() {
        let lowered = lower_to_lambda(RawLambda::prim(
            Primitive::PjsCall {
                prim_name: "get".to_string(),
                arg_types: vec![crate::lambda::lam_primitive::ExternalArgSpec::dummy()],
                ffi: Box::new(crate::lambda::lam_primitive::ExternalFfiSpec {
                    kind: ExternalFfiKind::Default,
                    spec: None,
                    obj_params: None,
                    return_wrapper: ExternalReturnWrapper::NullUndefinedToOpt,
                    inline_constant: None,
                }),
                dynamic_import: false,
                transformed_jsx: false,
            },
            vec![RawLambda::var(Ident::create_local("obj"))],
            Location::none(),
        ));

        let Lambda::Lprim(info) = lowered else {
            panic!("expected wrapper primitive");
        };
        assert!(matches!(info.primitive, Primitive::PnullUndefinedToOpt));
    }

    #[test]
    fn lowers_shape_none_to_none_constant() {
        let raw = RawLambda::const_(Constant::Int {
            i: 0,
            comment: Some(Box::new(PointerInfo::ShapeNone)),
        });

        assert!(matches!(
            lower_to_lambda(raw),
            Lambda::Lconst(Constant::JsUndefined { is_unit: false })
        ));
    }

    #[test]
    fn keeps_constructor_named_none_without_shape_info() {
        let raw = RawLambda::const_(Constant::Int {
            i: 0,
            comment: Some(Box::new(PointerInfo::Constructor(ConstructorTag {
                name: "None".to_string(),
                const_: 1,
                non_const: 1,
                runtime_tag: None,
            }))),
        });

        assert!(matches!(
            lower_to_lambda(raw),
            Lambda::Lconst(Constant::Int {
                i: 0,
                comment: Some(comment),
            }) if matches!(*comment, PointerInfo::Constructor(_))
        ));
    }

    #[test]
    fn folds_integer_comparison_constants_to_boolean_constant() {
        let lowered = lower_to_lambda(RawLambda::prim(
            Primitive::Pintcomp(Comparison::Eq),
            vec![
                RawLambda::const_(Constant::int(1)),
                RawLambda::const_(Constant::int(2)),
            ],
            Location::none(),
        ));

        assert!(matches!(lowered, Lambda::Lconst(Constant::JsFalse)));
    }

    #[test]
    fn lowers_predef_exception_global_module_to_string_constant() {
        let lowered = lower_to_lambda(RawLambda::global_module(
            crate::types::predef::ident_assert_failure(),
            false,
        ));

        assert!(matches!(
            lowered,
            Lambda::Lconst(Constant::String { ref s, delim: None }) if s == "Assert_failure"
        ));
    }

    #[test]
    fn aliases_follow_original_binding() {
        let source = Ident::create_local("source");
        let alias = Ident::create_local("alias");
        let raw = RawLambda::let_(
            LetKind::Alias,
            alias.clone(),
            RawLambda::var(source.clone()),
            RawLambda::var(alias),
        );

        let lowered = lower_to_lambda(raw);
        let Lambda::Lvar(id) = lowered else {
            panic!("expected alias to collapse");
        };
        assert!(id.same(&source));
    }

    #[test]
    fn keeps_exported_alias_binding_while_rewriting_export_uses() {
        let source = Ident::create_local("source");
        let alias = Ident::create_local("alias");
        let raw = RawLambda::let_(
            LetKind::Alias,
            alias.clone(),
            RawLambda::var(source.clone()),
            RawLambda::prim(
                Primitive::Pmakeblock(
                    TagInfo::ModuleExport(vec![alias.clone()]),
                    Mutable::Immutable,
                ),
                vec![RawLambda::var(alias.clone())],
                Location::none(),
            ),
        );

        let lowered = lower_to_lambda(raw);
        let Lambda::Llet(LetKind::Alias, kept_alias, value, body) = lowered else {
            panic!("expected exported alias let to remain");
        };
        assert!(kept_alias.same(&alias));
        let Lambda::Lvar(id) = value.as_ref() else {
            panic!("expected alias value to stay a variable");
        };
        assert!(id.same(&source));
        let Lambda::Lprim(info) = body.as_ref() else {
            panic!("expected module export block");
        };
        let [Lambda::Lvar(exported)] = info.args.as_slice() else {
            panic!("expected rewritten export argument");
        };
        assert!(exported.same(&source));
    }

    #[test]
    fn lowers_plain_string_delim_for_typed_constants() {
        let lowered = lower_to_lambda(RawLambda::const_(Constant::String {
            s: "hello".to_string(),
            delim: Some(StringDelim::Plain),
        }));

        assert!(matches!(
            lowered,
            Lambda::Lconst(Constant::String {
                s,
                delim: Some(StringDelim::Plain)
            }) if s == "hello"
        ));
    }

    #[test]
    fn lowers_native_int_constants_to_wrapped_int32() {
        let lowered = lower_to_lambda(RawLambda::const_(Constant::NativeInt {
            i: 0xAFAFAFAF,
            comment: None,
        }));

        assert!(matches!(
            lowered,
            Lambda::Lconst(Constant::Int {
                i: -1347440721,
                comment: None,
            })
        ));
    }

    #[test]
    fn lowers_polyvariant_hash_to_pointer_name() {
        let lowered = lower_to_lambda(RawLambda::const_(Constant::Int {
            i: crate::types::btype::hash_variant("One"),
            comment: Some(Box::new(PointerInfo::PolyVariant("One".to_string()))),
        }));

        assert!(matches!(
            lowered,
            Lambda::Lconst(Constant::Pointer(name)) if name == "One"
        ));
    }

    #[test]
    fn lowers_polyvariant_block_payload_tag_from_name() {
        let lowered = lower_to_lambda(RawLambda::prim(
            Primitive::Pmakeblock(TagInfo::PolyVar("V".to_string()), Mutable::Immutable),
            vec![
                RawLambda::const_(Constant::Int {
                    i: crate::types::btype::hash_variant("V"),
                    comment: Some(Box::new(PointerInfo::PolyVariant("V".to_string()))),
                }),
                RawLambda::const_(Constant::int(1)),
            ],
            Location::none(),
        ));

        let Lambda::Lprim(info) = lowered else {
            panic!("expected lowered polyvariant block");
        };
        assert!(matches!(
            info.args.as_slice(),
            [
                Lambda::Lconst(Constant::String { s, delim: None }),
                Lambda::Lconst(Constant::Int { i: 1, comment: None }),
            ] if s == "V"
        ));
    }

    #[test]
    fn lowers_constant_polyvariant_block_payload_tag_from_name() {
        let lowered = lower_to_lambda(RawLambda::const_(Constant::Block {
            tag_info: Box::new(TagInfo::PolyVar("Pair".to_string())),
            elements: vec![
                Constant::Int {
                    i: crate::types::btype::hash_variant("Pair"),
                    comment: Some(Box::new(PointerInfo::PolyVariant("Pair".to_string()))),
                },
                Constant::Block {
                    tag_info: Box::new(TagInfo::Tuple),
                    elements: vec![
                        Constant::Int {
                            i: 1,
                            comment: None,
                        },
                        Constant::Int {
                            i: 2,
                            comment: None,
                        },
                    ],
                },
            ],
        }));

        assert!(matches!(
            lowered,
            Lambda::Lconst(Constant::Block { elements, .. })
                if matches!(
                    elements.as_slice(),
                    [
                        Constant::String { s, delim: None },
                        Constant::Block { tag_info, elements }
                    ] if s == "Pair"
                        && matches!(**tag_info, TagInfo::Tuple)
                        && matches!(
                            elements.as_slice(),
                            [
                                Constant::Int { i: 1, comment: None },
                                Constant::Int { i: 2, comment: None },
                            ]
                        )
                )
        ));
    }

    #[test]
    fn lowers_constructor_runtime_int_tag() {
        let lowered = lower_to_lambda(RawLambda::const_(Constant::Int {
            i: 0,
            comment: Some(Box::new(PointerInfo::Constructor(ConstructorTag {
                name: "One1".to_string(),
                const_: 3,
                non_const: 0,
                runtime_tag: Some(ConstructorRuntimeTag::Int(1)),
            }))),
        }));

        assert!(matches!(
            lowered,
            Lambda::Lconst(Constant::Int {
                i: 1,
                comment: Some(comment),
            }) if matches!(*comment, PointerInfo::Constructor(_))
        ));
    }

    #[test]
    fn folds_orint_over_lowered_constructor_ints() {
        let lowered = lower_to_lambda(RawLambda::prim(
            Primitive::Porint,
            vec![
                RawLambda::const_(Constant::Int {
                    i: 0,
                    comment: None,
                }),
                RawLambda::const_(Constant::Int {
                    i: 1,
                    comment: Some(Box::new(PointerInfo::Constructor(ConstructorTag {
                        name: "B".to_string(),
                        const_: 2,
                        non_const: 0,
                        runtime_tag: Some(ConstructorRuntimeTag::Int(2)),
                    }))),
                }),
            ],
            Location::none(),
        ));

        assert!(matches!(
            lowered,
            Lambda::Lconst(Constant::Int {
                i: 2,
                comment: None,
            })
        ));
    }

    #[test]
    fn marks_switch_full_when_names_cover_all_cases() {
        let lowered = lower_to_lambda(RawLambda::Lswitch(
            Box::new(RawLambda::var(Ident::create_local("v"))),
            Box::new(RawLambdaSwitch {
                sw_numconsts: 1,
                sw_consts_full: false,
                sw_consts: vec![(
                    crate::lambda::SwitchKey::Constructor(
                        crate::types::VariantConstructorCase::Constant(crate::types::VariantTag {
                            name: "A".to_string(),
                            tag_type: None,
                        }),
                    ),
                    RawLambda::const_(Constant::int(0)),
                )],
                sw_numblocks: 0,
                sw_blocks_full: false,
                sw_blocks: Vec::new(),
                sw_failaction: None,
                sw_dispatch: crate::lambda::SwitchDispatch::Variant(
                    crate::types::VariantMatchingFacts {
                        tag_name: None,
                        block_types: vec![],
                        literal_tags: vec![crate::types::VariantTagType::String(
                            "A".to_string().clone(),
                        )],
                        has_null: false,
                        has_undefined: false,
                        has_other_literal: true,
                    },
                ),
            }),
            Location::none(),
        ));

        let Lambda::Lswitch(_, switch) = lowered else {
            panic!("expected switch");
        };
        assert!(switch.sw_consts_full);
        assert!(switch.sw_blocks_full);
    }

    #[test]
    fn keeps_const_only_switch_consts_full_from_input_without_names() {
        let lowered = lower_to_lambda(RawLambda::Lswitch(
            Box::new(RawLambda::var(Ident::create_local("v"))),
            Box::new(RawLambdaSwitch {
                sw_numconsts: 3,
                sw_consts_full: false,
                sw_consts: vec![
                    (
                        crate::lambda::SwitchKey::Int(0),
                        RawLambda::const_(Constant::int(7)),
                    ),
                    (
                        crate::lambda::SwitchKey::Int(1),
                        RawLambda::const_(Constant::int(9)),
                    ),
                ],
                sw_numblocks: 0,
                sw_blocks_full: false,
                sw_blocks: Vec::new(),
                sw_failaction: None,
                sw_dispatch: crate::lambda::SwitchDispatch::Direct,
            }),
            Location::none(),
        ));

        let Lambda::Lswitch(_, switch) = lowered else {
            panic!("expected switch");
        };
        assert!(!switch.sw_consts_full);
        assert!(switch.sw_blocks_full);
    }

    fn raw_exit_alias(alias_from: i32, alias_to: i32) -> RawLambda {
        RawLambda::LstaticCatch(
            Box::new(RawLambda::LstaticRaise(alias_from, Vec::new())),
            (alias_from, Vec::new()),
            Box::new(RawLambda::LstaticRaise(alias_to, Vec::new())),
        )
    }

    #[test]
    fn lowers_sequence_rhs_before_lhs_for_exit_aliases() {
        let lowered = lower_to_lambda(RawLambda::Lsequence(
            Box::new(RawLambda::LstaticRaise(7, Vec::new())),
            Box::new(raw_exit_alias(7, 8)),
        ));

        let Lambda::Lsequence(first, second) = lowered else {
            panic!("expected sequence");
        };
        assert!(matches!(
            first.as_ref(),
            Lambda::LstaticRaise(8, args) if args.is_empty()
        ));
        assert!(matches!(
            second.as_ref(),
            Lambda::LstaticRaise(8, args) if args.is_empty()
        ));
    }

    #[test]
    fn lowers_if_else_before_then_before_cond_for_exit_aliases() {
        let lowered = lower_to_lambda(RawLambda::LifThenElse(
            Box::new(RawLambda::LstaticRaise(7, Vec::new())),
            Box::new(RawLambda::const_(Constant::int(1))),
            Box::new(raw_exit_alias(7, 8)),
        ));

        let Lambda::LifThenElse(cond, _, else_) = lowered else {
            panic!("expected if");
        };
        assert!(matches!(
            cond.as_ref(),
            Lambda::LstaticRaise(8, args) if args.is_empty()
        ));
        assert!(matches!(
            else_.as_ref(),
            Lambda::LstaticRaise(8, args) if args.is_empty()
        ));
    }

    #[test]
    fn lowers_staticcatch_handler_before_body_for_exit_aliases() {
        let lowered = lower_to_lambda(RawLambda::LstaticCatch(
            Box::new(raw_exit_alias(7, 8)),
            (9, vec![Ident::create_local("param")]),
            Box::new(RawLambda::LstaticRaise(7, Vec::new())),
        ));

        let Lambda::LstaticCatch(body, (id, params), handler) = lowered else {
            panic!("expected static catch");
        };
        assert_eq!(id, 9);
        assert_eq!(params.len(), 1);
        assert!(matches!(
            body.as_ref(),
            Lambda::LstaticRaise(8, args) if args.is_empty()
        ));
        assert!(matches!(
            handler.as_ref(),
            Lambda::LstaticRaise(7, args) if args.is_empty()
        ));
    }

    #[test]
    fn lowers_apply_arguments_before_function_for_exit_aliases() {
        let lowered = lower_to_lambda(RawLambda::Lapply(Box::new(RawApply {
            ap_func: Box::new(RawLambda::LstaticRaise(7, Vec::new())),
            ap_args: vec![raw_exit_alias(7, 8)],
            ap_info: ApInfo {
                loc: Location::none(),
                inlined: InlineAttribute::Default,
                status: ApplyStatus::Na,
            },
            ap_transformed_jsx: false,
        })));

        let Lambda::Lapply(apply) = lowered else {
            panic!("expected apply");
        };
        assert!(matches!(
            apply.ap_func.as_ref(),
            Lambda::LstaticRaise(8, args) if args.is_empty()
        ));
        assert!(matches!(
            apply.ap_args.as_slice(),
            [Lambda::LstaticRaise(8, args)] if args.is_empty()
        ));
    }

    #[test]
    fn lowers_switch_cases_before_scrutinee_for_exit_aliases() {
        let lowered = lower_to_lambda(RawLambda::Lswitch(
            Box::new(raw_exit_alias(7, 8)),
            Box::new(RawLambdaSwitch {
                sw_numconsts: 1,
                sw_consts_full: true,
                sw_consts: vec![(
                    crate::lambda::SwitchKey::Int(0),
                    RawLambda::LstaticRaise(7, Vec::new()),
                )],
                sw_numblocks: 0,
                sw_blocks_full: false,
                sw_blocks: Vec::new(),
                sw_failaction: None,
                sw_dispatch: crate::lambda::SwitchDispatch::Direct,
            }),
            Location::none(),
        ));

        let Lambda::Lswitch(scrutinee, switch) = lowered else {
            panic!("expected switch");
        };
        assert!(matches!(
            scrutinee.as_ref(),
            Lambda::LstaticRaise(8, args) if args.is_empty()
        ));
        assert!(matches!(
            switch.sw_consts.as_slice(),
            [(crate::lambda::SwitchKey::Int(0), Lambda::LstaticRaise(7, args))] if args.is_empty()
        ));
    }

    #[test]
    fn lowers_switch_failaction_before_scrutinee_for_exit_aliases() {
        let lowered = lower_to_lambda(RawLambda::Lswitch(
            Box::new(RawLambda::LstaticRaise(7, Vec::new())),
            Box::new(RawLambdaSwitch {
                sw_numconsts: 0,
                sw_consts_full: false,
                sw_consts: Vec::new(),
                sw_numblocks: 0,
                sw_blocks_full: false,
                sw_blocks: Vec::new(),
                sw_failaction: Some(Box::new(raw_exit_alias(7, 8))),
                sw_dispatch: crate::lambda::SwitchDispatch::Direct,
            }),
            Location::none(),
        ));

        let Lambda::Lswitch(scrutinee, switch) = lowered else {
            panic!("expected switch");
        };
        assert!(matches!(
            scrutinee.as_ref(),
            Lambda::LstaticRaise(8, args) if args.is_empty()
        ));
        assert!(matches!(
            switch.sw_failaction.as_deref(),
            Some(Lambda::LstaticRaise(8, args)) if args.is_empty()
        ));
    }

    #[test]
    fn keeps_named_linear_switches_instead_of_collapsing_to_scrutinee() {
        let scrutinee = Ident::create_local("scrutinee");
        let lowered = lower_to_lambda(RawLambda::Lswitch(
            Box::new(RawLambda::var(scrutinee.clone())),
            Box::new(RawLambdaSwitch {
                sw_numconsts: 2,
                sw_consts_full: true,
                sw_consts: vec![
                    (
                        crate::lambda::SwitchKey::Constructor(
                            crate::types::VariantConstructorCase::Constant(
                                crate::types::VariantTag {
                                    name: "A".to_string(),
                                    tag_type: None,
                                },
                            ),
                        ),
                        RawLambda::const_(Constant::int(0)),
                    ),
                    (
                        crate::lambda::SwitchKey::Constructor(
                            crate::types::VariantConstructorCase::Constant(
                                crate::types::VariantTag {
                                    name: "B".to_string(),
                                    tag_type: None,
                                },
                            ),
                        ),
                        RawLambda::const_(Constant::int(1)),
                    ),
                ],
                sw_numblocks: 0,
                sw_blocks_full: false,
                sw_blocks: Vec::new(),
                sw_failaction: None,
                sw_dispatch: crate::lambda::SwitchDispatch::Variant(
                    crate::types::VariantMatchingFacts {
                        tag_name: None,
                        block_types: vec![],
                        literal_tags: vec![
                            crate::types::VariantTagType::String("B".to_string().clone()),
                            crate::types::VariantTagType::String("A".to_string().clone()),
                        ],
                        has_null: false,
                        has_undefined: false,
                        has_other_literal: true,
                    },
                ),
            }),
            Location::none(),
        ));

        let Lambda::Lswitch(arg, switch) = lowered else {
            panic!("expected named switch to remain a switch");
        };
        let Lambda::Lvar(id) = arg.as_ref() else {
            panic!("expected switch scrutinee");
        };
        assert!(id.same(&scrutinee));
        assert_eq!(switch.sw_consts.len(), 2);
    }

    #[test]
    fn lowers_const_only_switch_with_full_blocks_for_if_rewrite() {
        let loc = Location::none();
        let scrutinee = Ident::create_local("x");
        let exit = 1;
        let lowered = lower_to_lambda(RawLambda::LifThenElse(
            Box::new(RawLambda::prim(
                Primitive::Pisout(2),
                vec![RawLambda::prim(
                    Primitive::Poffsetint(-1),
                    vec![RawLambda::var(scrutinee.clone())],
                    loc.clone(),
                )],
                loc.clone(),
            )),
            Box::new(RawLambda::LstaticRaise(exit, Vec::new())),
            Box::new(RawLambda::Lswitch(
                Box::new(RawLambda::var(scrutinee.clone())),
                Box::new(RawLambdaSwitch {
                    sw_numconsts: 3,
                    sw_consts_full: false,
                    sw_consts: vec![
                        (
                            crate::lambda::SwitchKey::Int(1),
                            RawLambda::const_(Constant::Char(97)),
                        ),
                        (
                            crate::lambda::SwitchKey::Int(2),
                            RawLambda::const_(Constant::Char(98)),
                        ),
                        (
                            crate::lambda::SwitchKey::Int(3),
                            RawLambda::const_(Constant::Char(99)),
                        ),
                    ],
                    sw_numblocks: 0,
                    sw_blocks_full: false,
                    sw_blocks: Vec::new(),
                    sw_failaction: None,
                    sw_dispatch: crate::lambda::SwitchDispatch::Direct,
                }),
                loc,
            )),
        ));

        let Lambda::Lswitch(switch_arg, switch) = lowered else {
            panic!("expected if/switch lowering to rewrite into a switch");
        };
        let Lambda::Lvar(id) = switch_arg.as_ref() else {
            panic!("expected switch scrutinee to remain a variable");
        };
        assert!(id.same(&scrutinee));
        assert!(switch.sw_blocks_full);
        assert!(matches!(
            switch.sw_failaction.as_deref(),
            Some(Lambda::LstaticRaise(id, args)) if *id == exit && args.is_empty()
        ));
    }

    #[test]
    fn splits_non_recursive_binding_out_of_letrec() {
        let fake_y = Ident::create_local("fake_y");
        let fake_z = Ident::create_local("fake_z");
        let raw = RawLambda::letrec(
            vec![
                (
                    fake_y.clone(),
                    RawLambda::prim(
                        Primitive::Pmakeblock(
                            TagInfo::Tuple,
                            crate::lambda::lam_primitive::Mutable::Immutable,
                        ),
                        vec![RawLambda::var(fake_y.clone())],
                        Location::none(),
                    ),
                ),
                (
                    fake_z.clone(),
                    RawLambda::prim(
                        Primitive::Pmakeblock(
                            TagInfo::Tuple,
                            crate::lambda::lam_primitive::Mutable::Immutable,
                        ),
                        vec![RawLambda::var(fake_y.clone())],
                        Location::none(),
                    ),
                ),
            ],
            RawLambda::var(fake_z.clone()),
        );

        let lowered = lower_to_lambda(raw);
        let Lambda::Lletrec(bindings, body) = lowered else {
            panic!("expected outer letrec");
        };
        assert_eq!(bindings.len(), 1);
        assert!(bindings[0].0.same(&fake_y));
        let Lambda::Llet(LetKind::Strict, id, _, _) = *body else {
            panic!("expected strict let after letrec");
        };
        assert!(id.same(&fake_z));
    }

    #[test]
    fn keeps_fully_recursive_function_groups_in_single_letrec() {
        let find_end = Ident::create_local("find_end");
        let find_beg = Ident::create_local("find_beg");
        let end_param = Ident::create_local("n");
        let beg_param = Ident::create_local("p");

        let function_attr = FunctionAttribute::default();
        let find_end_binding = Lambda::function_(
            1,
            vec![end_param],
            Lambda::seq(Lambda::var(find_end.clone()), Lambda::var(find_beg.clone())),
            function_attr.clone(),
        );
        let find_beg_binding = Lambda::function_(
            1,
            vec![beg_param],
            Lambda::var(find_beg.clone()),
            function_attr,
        );

        let lowered = rebuild_recursive_bindings(
            vec![
                (find_end.clone(), find_end_binding),
                (find_beg.clone(), find_beg_binding),
            ],
            Lambda::var(find_end.clone()),
        );

        let Lambda::Lletrec(bindings, body) = lowered else {
            panic!("expected a single letrec");
        };
        assert_eq!(bindings.len(), 2);
        assert!(bindings[0].0.same(&find_end));
        assert!(bindings[1].0.same(&find_beg));
        assert!(matches!(body.as_ref(), Lambda::Lvar(id) if id.same(&find_end)));
    }

    #[test]
    fn marks_imported_field_global_module_as_dynamic() {
        let module_id = Ident::create_local("Belt_List");
        let raw = RawLambda::prim(
            Primitive::Pimport,
            vec![RawLambda::prim(
                Primitive::Pfield(
                    36,
                    crate::lambda::lam_compat::FieldDbgInfo::Module {
                        name: "forEach".to_string(),
                    },
                ),
                vec![RawLambda::global_module(module_id.clone(), false)],
                Location::none(),
            )],
            Location::none(),
        );

        let lowered = lower_to_lambda(raw);
        let Lambda::Lprim(import) = lowered else {
            panic!("expected import primitive");
        };
        let [Lambda::Lprim(field)] = import.args.as_slice() else {
            panic!("expected field primitive under import");
        };
        let [Lambda::LglobalModule(id, true)] = field.args.as_slice() else {
            panic!("expected dynamic imported global module");
        };
        assert!(id.same(&module_id));
    }

    #[test]
    fn marks_imported_js_call_as_dynamic() {
        let raw = RawLambda::prim(
            Primitive::Pimport,
            vec![RawLambda::prim(
                Primitive::PjsCall {
                    prim_name: "default".to_string(),
                    arg_types: Vec::new(),
                    ffi: Box::new(ExternalFfiSpec {
                        kind: ExternalFfiKind::Default,
                        spec: None,
                        obj_params: None,
                        return_wrapper: ExternalReturnWrapper::Identity,
                        inline_constant: None,
                    }),
                    dynamic_import: false,
                    transformed_jsx: false,
                },
                Vec::new(),
                Location::none(),
            )],
            Location::none(),
        );

        let lowered = lower_to_lambda(raw);
        let Lambda::Lprim(import) = lowered else {
            panic!("expected import primitive");
        };
        let [Lambda::Lprim(call)] = import.args.as_slice() else {
            panic!("expected js call under import");
        };
        let Primitive::PjsCall { dynamic_import, .. } = &call.primitive else {
            panic!("expected lowered js call primitive");
        };
        assert!(*dynamic_import);
    }

    #[test]
    fn keeps_module_alias_import_body_non_dynamic() {
        let alias = Ident::create_local("let");
        let module_id = Ident::create_local("Belt_List");
        let raw = RawLambda::prim(
            Primitive::Pimport,
            vec![RawLambda::let_(
                LetKind::Alias,
                alias,
                RawLambda::const_(Constant::ModuleAlias),
                RawLambda::global_module(module_id.clone(), false),
            )],
            Location::none(),
        );

        let lowered = lower_to_lambda(raw);
        let Lambda::Lprim(import) = lowered else {
            panic!("expected import primitive");
        };
        let [Lambda::Llet(LetKind::Alias, _, value, body)] = import.args.as_slice() else {
            panic!("expected alias let under import");
        };
        assert!(matches!(
            value.as_ref(),
            Lambda::Lconst(Constant::ModuleAlias)
        ));
        let Lambda::LglobalModule(id, false) = body.as_ref() else {
            panic!("expected non-dynamic imported global module in alias body");
        };
        assert!(id.same(&module_id));
    }

    #[test]
    fn preserves_module_makeblock_shape() {
        let module_id = Ident::create_local("A");
        let lowered = lower_to_lambda(RawLambda::prim(
            Primitive::Pmakeblock(
                TagInfo::Module(vec!["presentLight".to_string()]),
                Mutable::Immutable,
            ),
            vec![RawLambda::prim(
                Primitive::Pfield(
                    1,
                    FieldDbgInfo::Module {
                        name: "presentLight".to_string(),
                    },
                ),
                vec![RawLambda::var(module_id.clone())],
                Location::none(),
            )],
            Location::none(),
        ));

        let Lambda::Lprim(block) = lowered else {
            panic!("expected module makeblock to be preserved");
        };
        assert!(matches!(
            block.primitive,
            Primitive::Pmakeblock(TagInfo::Module(_), Mutable::Immutable)
        ));
        let [Lambda::Lprim(field)] = block.args.as_slice() else {
            panic!("expected module field access to stay under makeblock");
        };
        assert!(matches!(
            field.primitive,
            Primitive::Pfield(1, FieldDbgInfo::Module { ref name }) if name == "presentLight"
        ));
        let [Lambda::Lvar(id)] = field.args.as_slice() else {
            panic!("expected module source variable");
        };
        assert!(id.same(&module_id));
    }

    #[test]
    fn collapses_imported_global_module_let_to_dynamic_global_module() {
        let module_id = Ident::create_local("ModuleWithAlias");
        let raw = RawLambda::prim(
            Primitive::Pimport,
            vec![RawLambda::let_(
                LetKind::Strict,
                Ident::create_local("let"),
                RawLambda::global_module(module_id.clone(), false),
                RawLambda::unit(),
            )],
            Location::none(),
        );

        let lowered = lower_to_lambda(raw);
        let Lambda::Lprim(import) = lowered else {
            panic!("expected import primitive");
        };
        let [Lambda::LglobalModule(id, true)] = import.args.as_slice() else {
            panic!("expected collapsed dynamic global module");
        };
        assert!(id.same(&module_id));
    }

    #[test]
    fn lowers_raw_js_code_to_code_payload_without_args() {
        let lowered = lower_to_lambda(RawLambda::prim(
            Primitive::PrawJsCode(JsRawInfo {
                code: String::new(),
                is_stmt: false,
            }),
            vec![RawLambda::const_(Constant::String {
                s: "__DEV__".to_string(),
                delim: Some(StringDelim::Plain),
            })],
            Location::none(),
        ));

        let Lambda::Lprim(info) = lowered else {
            panic!("expected raw js primitive");
        };
        assert!(info.args.is_empty());
        assert!(matches!(
            info.primitive,
            Primitive::PrawJsCode(JsRawInfo {
                ref code,
                is_stmt: false,
            }) if code == "__DEV__"
        ));
    }
}
