//! Raw Lambda -> lowered Lambda boundary.
//!
//! This stage is the Rust port of the first `Lam_convert.convert` slice used
//! by optimized-lambda parity dumps. It intentionally only feeds the parity
//! printer path; JS compilation still uses the legacy lowered-lambda route.

use std::collections::HashMap;

use crate::ident::Ident;
use crate::lambda::compat::LetKind;
use crate::lambda::constant::{Constant, ConstructorRuntimeTag, PointerInfo};
use crate::lambda::free_variables::free_variables;
use crate::lambda::primitive::ExternalFfiKind;
use crate::lambda::primitive::Primitive;
use crate::lambda::tag_info::TagInfo;
use crate::lambda::{ApInfo, Apply, ApplyStatus, Lambda, LambdaSwitch};
use crate::location::Location;
use crate::raw_lambda::{RawApply, RawLambda, RawLambdaSwitch};

const SETTER_SUFFIX: &str = "#=";

struct LoweringContext {
    alias_tbl: HashMap<Ident, Ident>,
    exit_map: HashMap<i32, i32>,
}

impl LoweringContext {
    fn new() -> Self {
        Self {
            alias_tbl: HashMap::new(),
            exit_map: HashMap::new(),
        }
    }

    fn lower_lambda(&mut self, raw: RawLambda) -> Lambda {
        self.lower_lambda_with_dynamic_import(raw, false)
    }

    fn lower_lambda_with_dynamic_import(
        &mut self,
        raw: RawLambda,
        dynamic_import: bool,
    ) -> Lambda {
        match raw {
            RawLambda::Lvar(id) => Lambda::var(self.alias_target(id)),
            RawLambda::LglobalModule(id, imported) => {
                Lambda::global_module(id, dynamic_import || imported)
            }
            RawLambda::Lconst(c) => Lambda::const_(lower_constant(c)),
            RawLambda::Lapply(apply) => self.lower_apply(apply),
            RawLambda::Lfunction(func) => Lambda::function_(
                func.arity,
                func.params,
                self.lower_lambda(*func.body),
                func.attr,
            ),
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
            RawLambda::Lswitch(scrutinee, switch, _) => self.lower_switch(*scrutinee, switch),
            RawLambda::LstringSwitch(scrutinee, cases, default) => Lambda::LstringSwitch(
                Box::new(self.lower_lambda(*scrutinee)),
                cases
                    .into_iter()
                    .map(|(name, lam)| (name, self.lower_lambda(lam)))
                    .collect(),
                default.map(|lam| Box::new(self.lower_lambda(*lam))),
            ),
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
            RawLambda::LstaticCatch(body, (i, ids), handler) => Lambda::static_catch(
                self.lower_lambda(*body),
                i,
                ids,
                self.lower_lambda(*handler),
            ),
            RawLambda::LtryWith(body, id, handler) => self.lower_try_with(*body, id, *handler),
            RawLambda::LifThenElse(cond, then_, else_) => Lambda::if_(
                self.lower_lambda(*cond),
                self.lower_lambda(*then_),
                self.lower_lambda(*else_),
            ),
            RawLambda::Lsequence(first, second) => {
                Lambda::seq(self.lower_lambda(*first), self.lower_lambda(*second))
            }
            RawLambda::Lwhile(cond, body) => {
                Lambda::while_(self.lower_lambda(*cond), self.lower_lambda(*body))
            }
            RawLambda::Lfor(var, start, end, dir, body) => Lambda::for_(
                var,
                self.lower_lambda(*start),
                self.lower_lambda(*end),
                dir,
                self.lower_lambda(*body),
            ),
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

            let lowered_func = self.lower_lambda(RawLambda::Lsend(name, obj, loc));
            return Lambda::Lapply(Apply {
                ap_func: Box::new(lowered_func),
                ap_args: ap_args
                    .into_iter()
                    .map(|arg| self.lower_lambda(arg))
                    .collect(),
                ap_info: ApInfo {
                    loc: ap_info.loc,
                    inlined: ap_info.inlined,
                    status: ApplyStatus::Uncurry,
                },
                ap_transformed_jsx,
            });
        }

        Lambda::Lapply(Apply {
            ap_func: Box::new(self.lower_lambda(func)),
            ap_args: ap_args
                .into_iter()
                .map(|arg| self.lower_lambda(arg))
                .collect(),
            ap_info: ApInfo {
                loc: ap_info.loc,
                inlined: ap_info.inlined,
                status: ApplyStatus::Uncurry,
            },
            ap_transformed_jsx,
        })
    }

    fn lower_let(&mut self, kind: LetKind, id: Ident, value: RawLambda, body: RawLambda) -> Lambda {
        if kind == LetKind::Alias {
            if let RawLambda::Lvar(target) = value {
                self.alias_tbl.insert(id, self.alias_target(target));
                return self.lower_lambda(body);
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
        dynamic_import: bool,
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
                    arg_dynamic_import.unwrap_or(dynamic_import),
                )
            })
            .collect::<Vec<_>>();

        match primitive {
            Primitive::Pidentity => args.into_iter().next().unwrap_or_else(Lambda::unit),
            Primitive::Pnull => Lambda::const_(Constant::JsNull),
            Primitive::Pundefined => Lambda::const_(Constant::JsUndefined { is_unit: false }),
            Primitive::Pignore => {
                let arg = args.into_iter().next().unwrap_or_else(Lambda::unit);
                Lambda::seq(arg, Lambda::unit())
            }
            Primitive::PjsCall {
                prim_name,
                arg_types,
                ffi,
                dynamic_import,
                transformed_jsx,
            } if prim_name.is_empty() && ffi.kind == ExternalFfiKind::ObjCreate => {
                Lambda::prim(Primitive::PjsObjectCreate(arg_types), args, loc)
            }
            Primitive::PjsCall {
                prim_name,
                arg_types,
                ffi,
                dynamic_import,
                transformed_jsx,
            } => {
                let returns_unit = ffi.returns_unit;
                let call = Lambda::prim(
                    Primitive::PjsCall {
                        prim_name,
                        arg_types,
                        ffi,
                        dynamic_import,
                        transformed_jsx,
                    },
                    args,
                    loc,
                );
                if returns_unit {
                    Lambda::seq(call, Lambda::unit())
                } else {
                    call
                }
            }
            Primitive::Pmakeblock(_, TagInfo::SomeNotNested, _) => {
                Lambda::prim(Primitive::PsomeNotNest, args, loc)
            }
            Primitive::Pmakeblock(_, TagInfo::Some, _) => Lambda::prim(Primitive::Psome, args, loc),
            primitive @ Primitive::Pisout(_) => match args.as_slice() {
                [range, Lambda::Lprim(inner)]
                    if inner.args.len() == 1
                        && matches!(inner.primitive, Primitive::Poffsetint(_)) =>
                {
                    let Primitive::Poffsetint(offset) = inner.primitive.clone() else {
                        unreachable!();
                    };
                    Lambda::prim(
                        Primitive::Pisout(offset),
                        vec![range.clone(), inner.args[0].clone()],
                        loc,
                    )
                }
                _ => Lambda::prim(primitive, args, loc),
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
        let lowered_scrutinee = self.lower_lambda(scrutinee);
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

        if lowered_failaction.is_none() && lowered_blocks.is_empty() {
            if let Some(diff) = happens_to_be_diff(&lowered_consts) {
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

        Lambda::Lswitch(
            Box::new(lowered_scrutinee),
            LambdaSwitch {
                sw_consts_full: switch.sw_consts_full
                    || switch
                        .sw_names
                        .as_ref()
                        .is_some_and(|names| names.consts.len() == lowered_consts.len()),
                sw_consts: lowered_consts,
                sw_blocks_full: switch.sw_blocks_full
                    || switch
                        .sw_names
                        .as_ref()
                        .is_some_and(|names| names.blocks.len() == lowered_blocks.len()),
                sw_blocks: lowered_blocks,
                sw_failaction: lowered_failaction,
                sw_names: switch.sw_names,
            },
        )
    }

    fn lower_try_with(&mut self, body: RawLambda, id: Ident, handler: RawLambda) -> Lambda {
        let lowered_body = self.lower_lambda(body);
        let lowered_handler = self.lower_lambda(handler);
        if exception_id_destructed(&lowered_handler, &id) {
            let raw_id = Ident::create_local(format!("raw_{}", id.name()));
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

fn lower_constant(constant: Constant) -> Constant {
    match constant {
        Constant::Int {
            i,
            comment: Some(PointerInfo::Constructor(tag)),
        } => {
            let i = match tag.runtime_tag.as_ref() {
                Some(ConstructorRuntimeTag::Int(runtime_int)) => *runtime_int,
                _ => i,
            };
            match tag.name.as_str() {
                "()" if tag.const_ == 1 && tag.non_const == 0 => {
                    Constant::JsUndefined { is_unit: true }
                }
                "None" if tag.const_ == 1 && tag.non_const == 1 => {
                    Constant::JsUndefined { is_unit: false }
                }
                _ => Constant::Int {
                    i,
                    comment: Some(PointerInfo::Constructor(tag)),
                },
            }
        }
        Constant::Int {
            i,
            comment: Some(PointerInfo::PolyVariant(name)),
        } => name
            .parse::<i32>()
            .map(|i| Constant::Int { i, comment: None })
            .unwrap_or_else(|_| Constant::Pointer(name)),
        Constant::String { s, delim } => Constant::String { s, delim },
        Constant::ImmString(s) => Constant::String { s, delim: None },
        Constant::Pointer(name) => match name.strip_suffix('a') {
            Some(raw_int) => raw_int
                .parse::<i32>()
                .map(|i| Constant::Int { i, comment: None })
                .unwrap_or(Constant::Pointer(name)),
            None => Constant::Pointer(name),
        },
        Constant::Block {
            tag,
            tag_info,
            elements,
        } => {
            let mut elements = elements.into_iter().map(lower_constant).collect::<Vec<_>>();
            match tag_info {
                TagInfo::Some | TagInfo::SomeNotNested if elements.len() == 1 => {
                    Constant::Some(Box::new(elements.remove(0)))
                }
                other => Constant::Block {
                    tag,
                    tag_info: other,
                    elements,
                },
            }
        }
        Constant::Some(inner) => Constant::Some(Box::new(lower_constant(*inner))),
        other => other,
    }
}

fn int_const_value_any(lam: &Lambda) -> Option<i32> {
    match lam {
        Lambda::Lconst(Constant::Int { i, .. }) => Some(*i),
        _ => None,
    }
}

fn lower_primitive_default(primitive: Primitive, args: Vec<Lambda>, loc: Location) -> Lambda {
    match args.as_slice() {
        [lhs, rhs] => {
            let Some(lhs) = int_const_value_any(lhs) else {
                return Lambda::prim(primitive, args, loc);
            };
            let Some(rhs) = int_const_value_any(rhs) else {
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
            Lambda::prim(primitive, args, loc)
        }
        _ => Lambda::prim(primitive, args, loc),
    }
}

fn is_empty_module_shape_constant(lam: &Lambda) -> bool {
    matches!(
        lam,
        Lambda::Lconst(Constant::Block { tag: 0, elements, .. })
            if matches!(
                elements.as_slice(),
                [Constant::Block { tag: 0, elements: inner, .. }] if inner.is_empty()
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

fn happens_to_be_diff(sw_consts: &[(i32, Lambda)]) -> Option<i32> {
    let ((a, a_lam), rest) = sw_consts.split_first()?;
    let (b, b_lam) = rest.first()?;
    let a0 = int_constant_value(a_lam)?;
    let b0 = int_constant_value(b_lam)?;
    let diff = a0.checked_sub(*a)?;
    if b0.checked_sub(*b)? != diff {
        return None;
    }
    for (x, lam) in rest.iter().skip(1) {
        if int_constant_value(lam)?.checked_sub(*x)? != diff {
            return None;
        }
    }
    Some(diff)
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
        LambdaSwitch {
            sw_consts_full: switch.sw_consts_full,
            sw_consts: switch
                .sw_consts
                .iter()
                .map(|(tag, lam)| (*tag - offset, lam.clone()))
                .collect(),
            sw_blocks_full: switch.sw_blocks_full,
            sw_blocks: Vec::new(),
            sw_failaction: switch.sw_failaction.clone(),
            sw_names: switch.sw_names.clone(),
        },
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
            let deps = binding_dependencies(&bindings);
            let components = strongly_connected_binding_components(&deps);
            if components.len() <= 1 {
                Lambda::letrec(bindings, body)
            } else {
                components.into_iter().rev().fold(body, |acc, component| {
                    let singleton_index = component[0];
                    let group = component
                        .into_iter()
                        .map(|index| bindings[index].clone())
                        .collect::<Vec<_>>();
                    match group.as_slice() {
                        [(id, bind)]
                            if !deps[singleton_index].contains(&singleton_index)
                                && !has_incoming_dependency(singleton_index, &deps) =>
                        {
                            Lambda::let_(LetKind::Strict, id.clone(), bind.clone(), acc)
                        }
                        _ => Lambda::letrec(group, acc),
                    }
                })
            }
        }
    }
}

fn has_incoming_dependency(target: usize, deps: &[Vec<usize>]) -> bool {
    deps.iter()
        .enumerate()
        .any(|(source, outgoing)| source != target && outgoing.contains(&target))
}

fn binding_dependencies(bindings: &[(Ident, Lambda)]) -> Vec<Vec<usize>> {
    let index_by_id = bindings
        .iter()
        .enumerate()
        .map(|(index, (id, _))| (id.clone(), index))
        .collect::<HashMap<_, _>>();
    bindings
        .iter()
        .map(|(_, lam)| {
            let fv = free_variables(lam);
            let mut indices = fv
                .into_iter()
                .filter_map(|id| index_by_id.get(&id).copied())
                .collect::<Vec<_>>();
            indices.sort_unstable();
            indices.dedup();
            indices
        })
        .collect::<Vec<_>>()
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
            component.sort_unstable();
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
pub fn lower_to_lambda(raw: RawLambda) -> Lambda {
    LoweringContext::new().lower_lambda(raw)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lambda::compat::LetKind;
    use crate::lambda::constant::{ConstructorRuntimeTag, ConstructorTag, StringDelim};
    use crate::lambda::primitive::JsRawInfo;
    use crate::lambda::InlineAttribute;

    #[test]
    fn lowers_unit_constructor_pointer_to_unit_constant() {
        let raw = RawLambda::const_(Constant::Int {
            i: 0,
            comment: Some(PointerInfo::Constructor(ConstructorTag {
                name: "()".to_string(),
                const_: 1,
                non_const: 0,
                runtime_tag: None,
            })),
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
        let raw = RawLambda::Lapply(RawApply {
            ap_func: Box::new(RawLambda::var(func)),
            ap_args: vec![RawLambda::var(arg)],
            ap_info: ApInfo {
                loc: Location::none(),
                inlined: InlineAttribute::Default,
                status: ApplyStatus::Na,
            },
            ap_transformed_jsx: false,
        });

        let lowered = lower_to_lambda(raw);
        let Lambda::Lapply(apply) = lowered else {
            panic!("expected Lapply");
        };
        assert_eq!(apply.ap_info.status, ApplyStatus::Uncurry);
    }

    #[test]
    fn lowers_blank_js_call_to_object_create() {
        let raw = RawLambda::prim(
            Primitive::PjsCall {
                prim_name: String::new(),
                arg_types: vec![crate::lambda::primitive::ExternalArgSpec {
                    label: Some("name".to_string()),
                }],
                ffi: crate::lambda::primitive::ExternalFfiSpec {
                    module_name: None,
                    kind: ExternalFfiKind::ObjCreate,
                    returns_unit: false,
                },
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
    fn keeps_unlabeled_blank_js_call_as_call() {
        let raw = RawLambda::prim(
            Primitive::PjsCall {
                prim_name: String::new(),
                arg_types: vec![
                    crate::lambda::primitive::ExternalArgSpec { label: None },
                    crate::lambda::primitive::ExternalArgSpec { label: None },
                ],
                ffi: crate::lambda::primitive::ExternalFfiSpec {
                    module_name: None,
                    kind: ExternalFfiKind::Default,
                    returns_unit: false,
                },
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
    fn lowers_none_constructor_to_none_constant() {
        let raw = RawLambda::const_(Constant::Int {
            i: 0,
            comment: Some(PointerInfo::Constructor(ConstructorTag {
                name: "None".to_string(),
                const_: 1,
                non_const: 1,
                runtime_tag: None,
            })),
        });

        assert!(matches!(
            lower_to_lambda(raw),
            Lambda::Lconst(Constant::JsUndefined { is_unit: false })
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
    fn lowers_polyvariant_hash_to_pointer_name() {
        let lowered = lower_to_lambda(RawLambda::const_(Constant::Int {
            i: crate::types::btype::hash_variant("One"),
            comment: Some(PointerInfo::PolyVariant("One".to_string())),
        }));

        assert!(matches!(
            lowered,
            Lambda::Lconst(Constant::Pointer(name)) if name == "One"
        ));
    }

    #[test]
    fn lowers_constructor_runtime_int_tag() {
        let lowered = lower_to_lambda(RawLambda::const_(Constant::Int {
            i: 0,
            comment: Some(PointerInfo::Constructor(ConstructorTag {
                name: "One1".to_string(),
                const_: 3,
                non_const: 0,
                runtime_tag: Some(ConstructorRuntimeTag::Int(1)),
            })),
        }));

        assert!(matches!(
            lowered,
            Lambda::Lconst(Constant::Int {
                i: 1,
                comment: Some(PointerInfo::Constructor(_)),
            })
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
                    comment: Some(PointerInfo::Constructor(ConstructorTag {
                        name: "B".to_string(),
                        const_: 2,
                        non_const: 0,
                        runtime_tag: Some(ConstructorRuntimeTag::Int(2)),
                    })),
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
            RawLambdaSwitch {
                sw_consts_full: false,
                sw_consts: vec![(0, RawLambda::const_(Constant::int(0)))],
                sw_blocks_full: false,
                sw_blocks: Vec::new(),
                sw_failaction: None,
                sw_names: Some(crate::lambda::SwitchNames {
                    consts: vec!["A".to_string()],
                    blocks: Vec::new(),
                }),
            },
            Location::none(),
        ));

        let Lambda::Lswitch(_, switch) = lowered else {
            panic!("expected switch");
        };
        assert!(switch.sw_consts_full);
        assert!(switch.sw_blocks_full);
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
                            0,
                            TagInfo::Tuple,
                            crate::lambda::primitive::Mutable::Immutable,
                        ),
                        vec![RawLambda::var(fake_y.clone())],
                        Location::none(),
                    ),
                ),
                (
                    fake_z.clone(),
                    RawLambda::prim(
                        Primitive::Pmakeblock(
                            0,
                            TagInfo::Tuple,
                            crate::lambda::primitive::Mutable::Immutable,
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
    fn marks_imported_field_global_module_as_dynamic() {
        let module_id = Ident::create_local("Belt_List");
        let raw = RawLambda::prim(
            Primitive::Pimport,
            vec![RawLambda::prim(
                Primitive::Pfield(
                    36,
                    crate::lambda::compat::FieldDbgInfo::Module {
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
        assert!(matches!(value.as_ref(), Lambda::Lconst(Constant::ModuleAlias)));
        let Lambda::LglobalModule(id, false) = body.as_ref() else {
            panic!("expected non-dynamic imported global module in alias body");
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
