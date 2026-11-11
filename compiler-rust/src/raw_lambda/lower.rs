//! Raw Lambda -> lowered Lambda boundary.
//!
//! The Rust port of the `Lam_convert.convert` slice that turns the
//! translation's Lambda into the backend's, building straight into a
//! [`LamArena`].

use crate::fast_hash::AHashSet as HashSet;
use crate::lambda::LamLoc;

use crate::ident::Ident;
use crate::lambda::arena::{Lam, LamArena, Node, View};
use crate::lambda::lam_compat::{Comparison, FieldDbgInfo};
use crate::lambda::lam_constant::{Constant, ConstructorRuntimeTag, PointerInfo};
use crate::lambda::lam_primitive::Primitive;
use crate::lambda::lam_tag_info::TagInfo;
use crate::lambda::{ApInfo, ApplyStatus, Lambda};
use crate::raw_lambda::{RawArena, RawLambda};

const EXCEPTION_ID_FIELD: &str = "RE_EXN_ID";

/// Lowers raw Lambda into an arena. It holds no other state: raw and
/// lowered expressions share their identifiers.
struct Lowering<'a> {
    a: &'a mut LamArena,
}

use crate::lambda::arena::{ApplyId, ConstId, LamList, PrimId, SwitchId};
use smallvec::SmallVec;

impl Lowering<'_> {
    /// A lowered constant: the raw payload when lowering leaves it as is.
    fn lower_const(&mut self, c: ConstId) -> Lam {
        let raw = self.a.constant(c);
        if constant_is_lowered(raw) {
            return self.a.push(Node::Const(c));
        }
        let lowered = lower_constant(raw.clone());
        self.a.const_(lowered)
    }

    fn lower_list(&mut self, list: LamList) -> SmallVec<[Lam; 8]> {
        let items = self.a.list_small(list);
        items.into_iter().map(|arg| self.lower(arg)).collect()
    }

    fn lower(&mut self, raw: RawLambda) -> Lam {
        match self.a.node(raw) {
            Node::Var(id) => self.a.push(Node::Var(id)),
            Node::GlobalModule(id) => {
                let ident = self.a.ident(id);
                if ident.is_predef_exn() {
                    self.a.const_(Constant::String(ident.name().to_string()))
                } else {
                    self.a.push(Node::GlobalModule(id))
                }
            }
            Node::Const(c) => self.lower_const(c),
            Node::Apply { func, args, info } => self.lower_apply(func, args, info),
            Node::Function { body, info } => {
                let body = self.lower(body);
                self.a.function_with(info, body)
            }
            Node::Let {
                kind,
                id,
                value,
                body,
            } => {
                let value = self.lower(value);
                let body = self.lower(body);
                self.a.let_with(kind, id, value, body)
            }
            Node::LetRec { ids, values, body } => {
                let values = self.lower_list(values);
                let body = self.lower(body);
                // `Lambda_scc.bind_rec` already split the group at translation
                // (compiler/ml/lambda_scc.ml); conversion is the identity.
                let values = self.a.add_list(&values);
                self.a.letrec_with(ids, values, body)
            }
            Node::Prim { args, info } => self.lower_primitive(info, args),
            Node::Switch {
                scrut,
                actions,
                info,
            } => self.lower_switch(scrut, actions, info),
            Node::StringSwitch {
                scrut,
                actions,
                info,
            } => {
                // `Lam.stringswitch (convert_aux e) ... (convert_aux default)`:
                // OCaml evaluates the arguments right to left.
                let raw_actions = self.a.list_small(actions);
                let n = self.a.str_switch_payload(info).n_cases();
                let default = raw_actions.get(n).map(|lam| self.lower(*lam));
                let mut lowered: SmallVec<[Lam; 8]> = raw_actions[..n]
                    .iter()
                    .map(|lam| self.lower(*lam))
                    .collect();
                let scrutinee = self.lower(scrut);
                lowered.extend(default);
                let actions = self.a.add_list(&lowered);
                self.a.string_switch_raw(scrutinee, actions, info)
            }
            Node::StaticRaise { label, args } => {
                let args = self.lower_list(args);
                self.a.static_raise(label, &args)
            }
            Node::StaticCatch {
                body,
                handler,
                info,
            } => {
                let handler = self.lower(handler);
                let body = self.lower(body);
                self.a.static_catch_with(body, info, handler)
            }
            Node::TryWith { body, id, handler } => {
                // The conversion already packed the caught value
                // (`Translcore.pack_trywith_exn`).
                let body = self.lower(body);
                let handler = self.lower(handler);
                self.a.try_with(body, id, handler)
            }
            Node::If { cond, then_, else_ } => {
                let else_ = self.lower(else_);
                let then_ = self.lower(then_);
                let cond = self.lower(cond);
                self.a.if_(cond, then_, else_)
            }
            Node::Sequence(first, second) => {
                let second = self.lower(second);
                let first = self.lower(first);
                self.a.seq(first, second)
            }
            Node::While(cond, body) => {
                let body = self.lower(body);
                let cond = self.lower(cond);
                self.a.while_(cond, body)
            }
            Node::For { dir, id, kids } => {
                let (start, end, body) = self.a.for_parts(kids);
                let body = self.lower(body);
                let end = self.lower(end);
                let start = self.lower(start);
                self.a.for_with(id, start, end, dir, body)
            }
            Node::ForOf { id, iter, body } => {
                let body = self.lower(body);
                let iter = self.lower(iter);
                self.a.push(Node::ForOf { id, iter, body })
            }
            Node::ForAwaitOf { id, iter, body } => {
                let body = self.lower(body);
                let iter = self.lower(iter);
                self.a.push(Node::ForAwaitOf { id, iter, body })
            }
            Node::Break => self.a.break_(),
            Node::Continue => self.a.continue_(),
            Node::Assign { id, value } => {
                let value = self.lower(value);
                self.a.assign_with(id, value)
            }
        }
    }

    fn lower_apply(&mut self, func: RawLambda, args: LamList, info: ApplyId) -> Lam {
        let args = self.lower_list(args);
        let func = self.lower(func);
        let payload = self.a.apply_payload(info);
        let ap_info = ApInfo {
            loc: payload.info.loc,
            inlined: payload.info.inlined,
            status: ApplyStatus::Uncurry,
        };
        let transformed_jsx = payload.transformed_jsx;
        make_apply(self.a, func, &args, ap_info, transformed_jsx)
    }

    fn lower_primitive(&mut self, info: PrimId, raw_args: LamList) -> Lam {
        let loc = self.a.prim_payload(info).loc;
        if let Primitive::PrawJsCode(code) = &self.a.prim_payload(info).primitive {
            let raw_args = self.a.list(raw_args);
            let code_arg = match raw_args {
                [] => Some(None),
                [arg] => match self.a.as_const(*arg) {
                    Some(Constant::String(s) | Constant::ImmString(s)) => Some(Some(s.clone())),
                    _ => None,
                },
                _ => None,
            };
            if let Some(code_arg) = code_arg {
                let mut code = code.clone();
                if let Some(s) = code_arg {
                    code.code = s;
                }
                return self.a.prim(Primitive::PrawJsCode(code), &[], loc);
            }
        }

        let args = self.lower_list(raw_args);
        let a = &mut *self.a;
        match &a.prim_payload(info).primitive {
            Primitive::Pidentity => match args.first() {
                Some(arg) => *arg,
                None => a.unit(),
            },
            Primitive::PextensionSlotEq => {
                let [lhs, rhs] = args[..] else {
                    unreachable!("PextensionSlotEq expects exactly two arguments")
                };
                let id = a.prim(
                    Primitive::Pfield(
                        0,
                        FieldDbgInfo::Record {
                            name: crate::name::Name::new(EXCEPTION_ID_FIELD),
                        },
                    ),
                    &[lhs],
                    loc,
                );
                a.prim(Primitive::Pstringcomp(Comparison::Eq), &[id, rhs], loc)
            }
            // lambda.ml `mk_builtin`: `Lsequence (arg, lambda_unit)`, not the
            // folding `Lambda.seq`.
            Primitive::Pignore => {
                let arg = match args.first() {
                    Some(arg) => *arg,
                    None => a.unit(),
                };
                let unit = a.unit();
                a.seq_raw(arg, unit)
            }
            Primitive::Pmakeblock(TagInfo::PolyVar(name), _) => {
                let [_, value] = args[..] else {
                    unreachable!("polyvariant blocks expect tag and payload")
                };
                let tag = polyvar_block_tag_constant(name);
                let tag = a.const_(tag);
                a.prim_with_id(info, &[tag, value])
            }
            Primitive::Pmakeblock(TagInfo::SomeNotNested, _) => {
                a.prim(Primitive::PsomeNotNest, &args, loc)
            }
            Primitive::Pmakeblock(TagInfo::Some, _) => a.prim(Primitive::Psome, &args, loc),
            Primitive::PinitMod => a.prim_with_id(info, &args),
            _ => lower_primitive_default(a, info, &args),
        }
    }

    fn lower_switch(&mut self, scrut: RawLambda, actions: LamList, info: SwitchId) -> Lam {
        // `convert_switch` builds the switch record before passing the
        // scrutinee to `Lam.switch` (OCaml evaluates right to left).
        let payload = self.a.switch_payload(info);
        let const_only_switch = !payload.has_fail && payload.n_blocks() == 0 && payload.blocks_full;
        let lowered = self.lower_list(actions);
        let scrutinee = self.lower(scrut);
        let a = &mut *self.a;

        if const_only_switch && let Some(diff) = happens_to_be_diff(a, info, &lowered) {
            if diff == 0 {
                return scrutinee;
            }
            let diff = a.const_(Constant::Int {
                i: diff,
                comment: None,
            });
            return a.prim(Primitive::Paddint, &[scrutinee, diff], LamLoc::NONE);
        }

        let actions = a.add_list(&lowered);
        a.switch_raw(scrutinee, actions, info)
    }
}

/// Whether [`lower_constant`] returns `constant` unchanged.
fn constant_is_lowered(constant: &Constant) -> bool {
    match constant {
        Constant::JsNull
        | Constant::JsUndefined { .. }
        | Constant::JsTrue
        | Constant::JsFalse
        | Constant::Char(_)
        | Constant::String(_) => true,
        Constant::Int { comment, .. } => !matches!(
            comment.as_deref(),
            Some(
                PointerInfo::ShapeNone | PointerInfo::Constructor(_) | PointerInfo::PolyVariant(_)
            )
        ),
        _ => false,
    }
}

/// `Translcore.wrap_exn` (compiler/ml/translcore.ml:912-920): apply
/// `Primitive_exceptions.internalToException` to a caught value, so matching
/// sees a ReScript exception. Used by the conversion's `pack_trywith_exn`.
pub(crate) fn wrap_exn_raw(b: &RawArena, loc: LamLoc, arg: RawLambda) -> RawLambda {
    let module = b.global_module(Ident::create_persistent("Primitive_exceptions"));
    let internal_to_exception = b.prim(
        Primitive::Pfield(
            0,
            FieldDbgInfo::Module {
                name: crate::name::Name::new("internalToException"),
            },
        ),
        &[module],
        loc,
    );
    b.apply(
        internal_to_exception,
        &[arg],
        ApInfo {
            loc,
            inlined: crate::lambda::InlineAttribute::Default,
            status: ApplyStatus::Uncurry,
        },
        false,
    )
}

/// [`wrap_exn_raw`] in Lambda, for the backend tests.
#[cfg(test)]
pub(crate) fn wrap_exn(loc: LamLoc, arg: Lambda) -> Lambda {
    let internal_to_exception = Lambda::prim(
        Primitive::Pfield(
            0,
            FieldDbgInfo::Module {
                name: crate::name::Name::new("internalToException"),
            },
        ),
        vec![Lambda::global_module(Ident::create_persistent(
            "Primitive_exceptions",
        ))],
        loc,
    );
    Lambda::apply(
        internal_to_exception,
        vec![arg],
        ApInfo {
            loc,
            inlined: crate::lambda::InlineAttribute::Default,
            status: ApplyStatus::Uncurry,
        },
        false,
    )
}

fn collect_exported_idents(a: &LamArena, raw: RawLambda, exports: &mut HashSet<Ident>) {
    if let Node::Prim { info, .. } = a.node(raw)
        && let Primitive::Pmakeblock(TagInfo::ModuleExport(ids), _) =
            &a.prim_payload(info).primitive
    {
        exports.extend(ids.iter().cloned());
    }
    a.iter_children(raw, |child| collect_exported_idents(a, child, exports));
}

pub(crate) fn lower_constant(constant: Constant) -> Constant {
    match constant {
        Constant::Constructor(tag) if tag.name == "()" => Constant::JsUndefined { is_unit: true },
        Constant::Constructor(tag) => match tag.literal {
            Some(crate::types::VariantLiteralTag::Int(value)) => Constant::Int {
                i: value as i32,
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
        Constant::String(s) => Constant::String(s),
        Constant::ImmString(s) => Constant::String(s),
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
        Constant::String(name.to_string())
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

/// `Lambda.apply` (lambda.ml): eta-reduce an applied primitive wrapper and
/// push the application under `let`s that bind a function.
fn make_apply(
    a: &mut LamArena,
    func: Lam,
    args: &[Lam],
    ap_info: ApInfo,
    ap_transformed_jsx: bool,
) -> Lam {
    match a.node(func) {
        Node::Function { body, info } => {
            if let Some(reduced) = eta_reduce_function_apply(a, info, body, args, &ap_info) {
                return reduced;
            }
            a.apply_raw(func, args, ap_info, ap_transformed_jsx)
        }
        Node::Let {
            kind,
            id,
            value,
            body,
        } if matches!(a.node(body), Node::Function { .. }) => {
            let body = make_apply(a, body, args, ap_info, ap_transformed_jsx);
            a.let_with(kind, id, value, body)
        }
        _ => a.apply_raw(func, args, ap_info, ap_transformed_jsx),
    }
}

fn eta_reduce_function_apply(
    a: &mut LamArena,
    function: crate::lambda::arena::FuncId,
    body: Lam,
    args: &[Lam],
    ap_info: &ApInfo,
) -> Option<Lam> {
    let params: Vec<Ident> = a.params(function).to_vec();
    match a.as_prim(body) {
        Some((
            wrap @ (Primitive::PnullToOpt
            | Primitive::PnullUndefinedToOpt
            | Primitive::PisNull
            | Primitive::PisNullUndefined
            | Primitive::Ptypeof),
            [inner_call],
            _,
        )) => {
            let wrap = wrap.clone();
            let (inner, inner_args, _) = a.as_prim(*inner_call)?;
            let inner = inner.clone();
            let eta_args = eta_conversion_args(a, &params, inner_args, args)?;
            // lambda.ml `apply` builds the result through the folding `prim`.
            let inner = a.prim(inner, &eta_args, ap_info.loc);
            Some(a.prim(wrap, &[inner], ap_info.loc))
        }
        Some((
            Primitive::PnullToOpt
            | Primitive::PnullUndefinedToOpt
            | Primitive::PisNull
            | Primitive::PisNullUndefined
            | Primitive::Ptypeof,
            _,
            _,
        )) => None,
        Some((inner, inner_args, _)) => {
            let inner = inner.clone();
            let eta_args = eta_conversion_args(a, &params, inner_args, args)?;
            Some(a.prim(inner, &eta_args, ap_info.loc))
        }
        None => {
            let Node::Sequence(first, second) = a.node(body) else {
                return None;
            };
            let (inner, inner_args, _) = a.as_prim(first)?;
            if !a.is_const(second) {
                return None;
            }
            let inner = inner.clone();
            let eta_args = eta_conversion_args(a, &params, inner_args, args)?;
            let call = a.prim(inner, &eta_args, ap_info.loc);
            Some(a.seq(call, second))
        }
    }
}

fn eta_conversion_args(
    a: &LamArena,
    params: &[Ident],
    inner_args: &[Lam],
    outer_args: &[Lam],
) -> Option<Vec<Lam>> {
    if params.len() != inner_args.len() || params.len() != outer_args.len() {
        return None;
    }
    params
        .iter()
        .zip(inner_args)
        .zip(outer_args)
        .map(
            |((param, inner_arg), outer_arg)| match a.as_var(*inner_arg) {
                Some(id) if param.same(&id) => Some(*outer_arg),
                _ => None,
            },
        )
        .collect()
}

fn bool_const(a: &mut LamArena, value: bool) -> Lam {
    if value { a.true_() } else { a.false_() }
}

fn string_constant_value(constant: &Constant) -> Option<&str> {
    match constant {
        Constant::String(s) => Some(s.as_str()),
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

/// Constant folding of `Lam.prim` for the operands lowering sees, before
/// the generic smart constructor.
fn fold_constants(primitive: &Primitive, args: &[&Constant]) -> Option<Folded> {
    match *args {
        [constant] => match (primitive, constant) {
            (Primitive::Pnegint, Constant::Int { i, .. }) => Some(Folded::Int(i.wrapping_neg())),
            (Primitive::Pintoffloat, Constant::Float(value)) => value
                .parse::<f64>()
                .ok()
                .map(|value| Folded::Int(value as i32)),
            // lambda.ml `Lambda.prim`: `String_literal.utf16_length`.
            (Primitive::Pstringlength, constant) => string_constant_value(constant).map(|value| {
                Folded::Int(
                    crate::string_literal::utf16_length(value)
                        .expect("String_literal.utf16_length: Invalid_utf8")
                        as i32,
                )
            }),
            (Primitive::Pnot, Constant::JsTrue) => Some(Folded::Bool(false)),
            (Primitive::Pnot, Constant::JsFalse) => Some(Folded::Bool(true)),
            _ => None,
        },
        [lhs, rhs] => match (primitive, lhs, rhs) {
            (
                Primitive::Pintcomp(comparison),
                Constant::Int { i: lhs, .. },
                Constant::Int { i: rhs, .. },
            ) => Some(Folded::Bool(comparison.cmp_int32(*lhs, *rhs))),
            (Primitive::Pfloatcomp(comparison), lhs, rhs) => {
                let (lhs, rhs) = (float_constant_value(lhs)?, float_constant_value(rhs)?);
                Some(Folded::Bool(comparison.cmp_float(lhs, rhs)))
            }
            (Primitive::Pintcomp(Comparison::Eq), lhs, rhs) => {
                let (lhs, rhs) = (pointer_constant_value(lhs)?, pointer_constant_value(rhs)?);
                Some(Folded::Bool(lhs == rhs))
            }
            (Primitive::Pintcomp(Comparison::Neq), lhs, rhs) => {
                let (lhs, rhs) = (pointer_constant_value(lhs)?, pointer_constant_value(rhs)?);
                Some(Folded::Bool(lhs != rhs))
            }
            (
                Primitive::Paddint
                | Primitive::Psubint
                | Primitive::Pmulint
                | Primitive::Pdivint
                | Primitive::Pmodint
                | Primitive::Pandint
                | Primitive::Porint
                | Primitive::Pxorint
                | Primitive::Plslint
                | Primitive::Plsrint
                | Primitive::Pasrint,
                lhs,
                rhs,
            ) => {
                let (&Constant::Int { i: lhs, .. }, &Constant::Int { i: rhs, .. }) = (lhs, rhs)
                else {
                    return Some(Folded::Unfolded);
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
                folded.map(Folded::Int)
            }
            (Primitive::Psequand, Constant::JsFalse, Constant::JsTrue | Constant::JsFalse)
            | (Primitive::Psequand, Constant::JsTrue, Constant::JsFalse)
            | (Primitive::Psequor, Constant::JsFalse, Constant::JsFalse) => {
                Some(Folded::Bool(false))
            }
            (Primitive::Psequand, Constant::JsTrue, Constant::JsTrue)
            | (Primitive::Psequor, Constant::JsTrue, Constant::JsTrue | Constant::JsFalse)
            | (Primitive::Psequor, Constant::JsFalse, Constant::JsTrue) => Some(Folded::Bool(true)),
            (Primitive::Pstringadd, lhs, rhs) => {
                let (lhs, rhs) = (string_constant_value(lhs)?, string_constant_value(rhs)?);
                Some(Folded::String(format!("{lhs}{rhs}")))
            }
            // lambda.ml `Lambda.prim`: `String_literal.code_point_at_utf16_index`.
            (Primitive::Pstringrefs | Primitive::Pstringrefu, lhs, Constant::Int { i, .. }) => {
                let value = string_constant_value(lhs)?;
                match crate::string_literal::code_point_at_utf16_index(value, *i as i64) {
                    Ok(Some(codepoint)) => Some(Folded::Char(codepoint as i32)),
                    _ => None,
                }
            }
            _ => None,
        },
        _ => None,
    }
}

enum Folded {
    Int(i32),
    Bool(bool),
    String(String),
    Char(i32),
    /// An integer operation on non-integer constants: build it as is.
    Unfolded,
}

fn lower_primitive_default(a: &mut LamArena, info: PrimId, args: &[Lam]) -> Lam {
    let folded = {
        let primitive = &a.prim_payload(info).primitive;
        let constants: smallvec::SmallVec<[&Constant; 2]> =
            args.iter().map_while(|arg| a.as_const(*arg)).collect();
        (constants.len() == args.len())
            .then(|| fold_constants(primitive, &constants))
            .flatten()
    };
    match folded {
        Some(Folded::Int(i)) => return a.const_(Constant::Int { i, comment: None }),
        Some(Folded::Bool(value)) => return bool_const(a, value),
        Some(Folded::String(s)) => return a.const_(Constant::String(s)),
        Some(Folded::Char(c)) => return a.const_(Constant::Char(c)),
        Some(Folded::Unfolded) => return a.prim_with_id(info, args),
        None => {}
    }
    if let Primitive::Pmakeblock(TagInfo::Module(fields), _) = &a.prim_payload(info).primitive
        && let Some(module_alias) = collapse_module_alias(a, fields, args)
    {
        return module_alias;
    }
    a.prim_with_id(info, args)
}

fn int_constant_value(a: &LamArena, lam: Lam) -> Option<i32> {
    match a.as_const(lam)? {
        Constant::Int { i, comment: None } => Some(*i),
        Constant::NativeInt { i, comment: None } => i32::try_from(*i).ok(),
        _ => None,
    }
}

fn happens_to_be_diff(a: &LamArena, info: SwitchId, actions: &[Lam]) -> Option<i32> {
    if !matches!(
        a.switch_payload(info).dispatch,
        crate::lambda::SwitchDispatch::Direct
    ) {
        return None;
    }
    let keys = a.switch_const_keys(info);
    if keys.len() < 2 {
        return None;
    }
    let mut diff = None;
    for (key, lam) in keys.iter().zip(actions) {
        let crate::lambda::SwitchKey::Int(value) = key else {
            return None;
        };
        let d = int_constant_value(a, *lam)?.checked_sub(*value)?;
        if *diff.get_or_insert(d) != d {
            return None;
        }
    }
    diff
}

/// A module block whose fields are, in order, all fields of one module:
/// that module (lambda.ml `Lambda.prim`, `Blk_module`).
fn collapse_module_alias(a: &LamArena, fields: &[String], args: &[Lam]) -> Option<Lam> {
    let (first_field, rest_fields) = fields.split_first()?;
    let (first_arg, rest_args) = args.split_first()?;
    let (field_name, first_index, module_value) = module_field_access(a, *first_arg)?;
    if field_name != first_field || first_index != 0 {
        return None;
    }
    for (expected_index, (field, arg)) in (1i32..).zip(rest_fields.iter().zip(rest_args)) {
        let (field_name, arg_index, arg_module_value) = module_field_access(a, *arg)?;
        if field_name != field
            || arg_index != expected_index
            || !same_module_source(a, module_value, arg_module_value)
        {
            return None;
        }
    }
    if rest_fields.len() != rest_args.len() {
        return None;
    }
    Some(module_value)
}

fn module_field_access(a: &LamArena, arg: Lam) -> Option<(&str, i32, Lam)> {
    let (Primitive::Pfield(index, FieldDbgInfo::Module { name }), [module_value], _) =
        a.as_prim(arg)?
    else {
        return None;
    };
    if !matches!(a.node(*module_value), Node::GlobalModule(_) | Node::Var(_)) || *index < 0 {
        return None;
    }
    Some((name.as_str(), *index, *module_value))
}

fn same_module_source(a: &LamArena, lhs: Lam, rhs: Lam) -> bool {
    match (a.node(lhs), a.node(rhs)) {
        (Node::Var(lhs), Node::Var(rhs)) | (Node::GlobalModule(lhs), Node::GlobalModule(rhs)) => {
            a.ident(lhs).same(&a.ident(rhs))
        }
        _ => false,
    }
}

/// `Translcore.exception_id_destructed` (translcore.ml:921-955): does `lam`
/// use the caught value `exn` other than by re-raising it?
pub(crate) fn exception_id_destructed_raw(a: &LamArena, lam: RawLambda, exn: &Ident) -> bool {
    match a.view(lam) {
        View::Prim(Primitive::Praise, [arg], _) if a.as_var(*arg).is_some() => false,
        View::Var(id) => id.same(exn),
        View::Assign(id, _) if id.same(exn) => true,
        _ => {
            let mut hit = false;
            a.iter_children(lam, |child| {
                hit = hit || exception_id_destructed_raw(a, child, exn);
            });
            hit
        }
    }
}

#[cfg(test)]
pub(crate) fn max_ident_stamp_for_test(a: &LamArena, raw: RawLambda) -> i32 {
    fn visit(a: &LamArena, raw: RawLambda, max_stamp: &mut i32) {
        let mut ident = |id: &Ident| *max_stamp = (*max_stamp).max(id.stamp());
        match a.view(raw) {
            View::Var(id)
            | View::GlobalModule(id)
            | View::Let(_, id, _, _)
            | View::TryWith(_, id, _)
            | View::For(id, _, _, _, _)
            | View::ForOf(id, _, _)
            | View::ForAwaitOf(id, _, _)
            | View::Assign(id, _) => ident(&id),
            View::Function { params, .. } => params.iter().for_each(ident),
            View::LetRec(ids, _, _) => ids.iter().for_each(ident),
            View::StaticCatch(_, _, ids, _) => ids.iter().for_each(ident),
            View::Prim(Primitive::Pmakeblock(TagInfo::ModuleExport(ids), _), _, _) => {
                ids.iter().for_each(ident)
            }
            _ => {}
        }
        a.iter_children(raw, |child| visit(a, child, max_stamp));
    }
    let mut max_stamp = 0;
    visit(a, raw, &mut max_stamp);
    max_stamp
}

/// The Lambda `Translmod.transl_implementation` returns, as `-drawlambda`
/// prints it, and the module's exported identifiers. Lowering creates no
/// identifiers: the conversion made them where OCaml's translation does.
pub fn lower_to_translmod_lambda(
    mut arena: LamArena,
    raw: RawLambda,
) -> (LamArena, Lam, HashSet<Ident>) {
    let mut exported_idents = HashSet::new();
    collect_exported_idents(&arena, raw, &mut exported_idents);
    let lam = Lowering { a: &mut arena }.lower(raw);
    (arena, lam, exported_idents)
}

/// The lowered Lambda after `Lam_pass_collapse_var_aliases`, the first pass
/// of `Lam_compile_main.compile` (lam_compile_main.ml:288-290).
pub fn lower_to_arena(arena: LamArena, raw: RawLambda) -> (LamArena, Lam) {
    let (mut arena, lam, exports) = lower_to_translmod_lambda(arena, raw);
    let lam = crate::lambda::lam_pass_collapse_var_aliases::collapse(&mut arena, lam, &exports);
    (arena, lam)
}

/// [`lower_to_arena`] as a tree.
pub fn lower_to_lambda(arena: LamArena, raw: RawLambda) -> Lambda {
    let (arena, lam) = lower_to_arena(arena, raw);
    arena.export(lam)
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::lambda::InlineAttribute;
    use crate::lambda::lam_compat::LetKind;
    use crate::lambda::lam_constant::{ConstructorRuntimeTag, ConstructorTag};
    use crate::lambda::lam_primitive::{JsRawInfo, Mutable};
    use crate::raw_lambda::RawLambdaSwitch;

    #[test]
    fn lowers_unit_constructor_pointer_to_unit_constant() {
        let b = RawArena::new();
        let raw = b.const_(Constant::Int {
            i: 0,
            comment: Some(Box::new(PointerInfo::Constructor(ConstructorTag {
                name: "()".to_string(),
                const_: 1,
                non_const: 0,
                runtime_tag: None,
            }))),
        });

        assert!(matches!(
            lower_to_lambda(b.into_inner(), raw),
            Lambda::Lconst(Constant::JsUndefined { is_unit: true })
        ));
    }

    #[test]
    fn lowers_apply_to_uncurry_status() {
        let b = RawArena::new();
        let func = Ident::create_local("f");
        let arg = Ident::create_local("x");
        let raw = b.apply(
            b.var(func),
            &[b.var(arg)],
            ApInfo {
                loc: LamLoc::NONE,
                inlined: InlineAttribute::Default,
                status: ApplyStatus::Na,
            },
            false,
        );

        let lowered = lower_to_lambda(b.into_inner(), raw);
        let Lambda::Lapply(apply) = lowered else {
            panic!("expected Lapply");
        };
        assert_eq!(apply.ap_info.status, ApplyStatus::Uncurry);
    }

    #[test]
    fn eta_reduces_primitive_wrapper_application() {
        let b = RawArena::new();
        let prim0 = Ident::create_local("prim0");
        let prim1 = Ident::create_local("prim1");
        let lhs = Ident::create_local("lhs");
        let rhs = Ident::create_local("rhs");
        let raw = b.apply(
            b.function_(
                2,
                &[prim0, prim1],
                b.prim(
                    Primitive::Paddint,
                    &[b.var(prim0), b.var(prim1)],
                    LamLoc::NONE,
                ),
                crate::lambda::FunctionAttribute::default(),
                LamLoc::NONE,
            ),
            &[b.var(lhs), b.var(rhs)],
            ApInfo {
                loc: LamLoc::NONE,
                inlined: InlineAttribute::Default,
                status: ApplyStatus::Na,
            },
            false,
        );

        let lowered = lower_to_lambda(b.into_inner(), raw);
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
    fn lowers_extension_slot_eq_via_exception_id_field() {
        let b = RawArena::new();
        let exn = Ident::create_local("exn");
        let slot = Ident::create_local("slot");
        let lowered = {
            let raw = b.prim(
                Primitive::PextensionSlotEq,
                &[b.var(exn), b.var(slot)],
                LamLoc::NONE,
            );
            lower_to_lambda(b.into_inner(), raw)
        };

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
    fn lowers_shape_none_to_none_constant() {
        let b = RawArena::new();
        let raw = b.const_(Constant::Int {
            i: 0,
            comment: Some(Box::new(PointerInfo::ShapeNone)),
        });

        assert!(matches!(
            lower_to_lambda(b.into_inner(), raw),
            Lambda::Lconst(Constant::JsUndefined { is_unit: false })
        ));
    }

    #[test]
    fn keeps_constructor_named_none_without_shape_info() {
        let b = RawArena::new();
        let raw = b.const_(Constant::Int {
            i: 0,
            comment: Some(Box::new(PointerInfo::Constructor(ConstructorTag {
                name: "None".to_string(),
                const_: 1,
                non_const: 1,
                runtime_tag: None,
            }))),
        });

        assert!(matches!(
            lower_to_lambda(b.into_inner(), raw),
            Lambda::Lconst(Constant::Int {
                i: 0,
                comment: Some(comment),
            }) if matches!(*comment, PointerInfo::Constructor(_))
        ));
    }

    #[test]
    fn folds_integer_comparison_constants_to_boolean_constant() {
        let b = RawArena::new();
        let lowered = {
            let raw = b.prim(
                Primitive::Pintcomp(Comparison::Eq),
                &[b.const_(Constant::int(1)), b.const_(Constant::int(2))],
                LamLoc::NONE,
            );
            lower_to_lambda(b.into_inner(), raw)
        };

        assert!(matches!(lowered, Lambda::Lconst(Constant::JsFalse)));
    }

    #[test]
    fn lowers_predef_exception_global_module_to_string_constant() {
        let b = RawArena::new();
        let lowered = {
            let raw = b.global_module(crate::types::predef::ident_assert_failure());
            lower_to_lambda(b.into_inner(), raw)
        };

        assert!(matches!(
            lowered,
            Lambda::Lconst(Constant::String(ref s)) if s == "Assert_failure"
        ));
    }

    #[test]
    fn aliases_follow_original_binding() {
        let b = RawArena::new();
        let source = Ident::create_local("source");
        let alias = Ident::create_local("alias");
        let raw = b.let_(LetKind::Alias, alias, b.var(source), b.var(alias));

        let lowered = lower_to_lambda(b.into_inner(), raw);
        let Lambda::Lvar(id) = lowered else {
            panic!("expected alias to collapse");
        };
        assert!(id.same(&source));
    }

    #[test]
    fn keeps_exported_alias_binding_while_rewriting_export_uses() {
        let b = RawArena::new();
        let source = Ident::create_local("source");
        let alias = Ident::create_local("alias");
        let raw = b.let_(
            LetKind::Alias,
            alias,
            b.var(source),
            b.prim(
                Primitive::Pmakeblock(TagInfo::ModuleExport(vec![alias]), Mutable::Immutable),
                &[b.var(alias)],
                LamLoc::NONE,
            ),
        );

        let lowered = lower_to_lambda(b.into_inner(), raw);
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
        let b = RawArena::new();
        let lowered = {
            let raw = b.const_(Constant::String("hello".to_string()));
            lower_to_lambda(b.into_inner(), raw)
        };

        assert!(matches!(
            lowered,
            Lambda::Lconst(Constant::String(s)) if s == "hello"
        ));
    }

    #[test]
    fn lowers_native_int_constants_to_wrapped_int32() {
        let b = RawArena::new();
        let lowered = {
            let raw = b.const_(Constant::NativeInt {
                i: 0xAFAFAFAF,
                comment: None,
            });
            lower_to_lambda(b.into_inner(), raw)
        };

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
        let b = RawArena::new();
        let lowered = {
            let raw = b.const_(Constant::Int {
                i: crate::types::btype::hash_variant("One"),
                comment: Some(Box::new(PointerInfo::PolyVariant("One".to_string()))),
            });
            lower_to_lambda(b.into_inner(), raw)
        };

        assert!(matches!(
            lowered,
            Lambda::Lconst(Constant::Pointer(name)) if name == "One"
        ));
    }

    #[test]
    fn lowers_polyvariant_block_payload_tag_from_name() {
        let b = RawArena::new();
        let lowered = {
            let raw = b.prim(
                Primitive::Pmakeblock(TagInfo::PolyVar("V".to_string()), Mutable::Immutable),
                &[
                    b.const_(Constant::Int {
                        i: crate::types::btype::hash_variant("V"),
                        comment: Some(Box::new(PointerInfo::PolyVariant("V".to_string()))),
                    }),
                    b.const_(Constant::int(1)),
                ],
                LamLoc::NONE,
            );
            lower_to_lambda(b.into_inner(), raw)
        };

        let Lambda::Lprim(info) = lowered else {
            panic!("expected lowered polyvariant block");
        };
        assert!(matches!(
            info.args.as_slice(),
            [
                Lambda::Lconst(Constant::String(s)),
                Lambda::Lconst(Constant::Int { i: 1, comment: None }),
            ] if s == "V"
        ));
    }

    #[test]
    fn lowers_constant_polyvariant_block_payload_tag_from_name() {
        let b = RawArena::new();
        let lowered = {
            let raw = b.const_(Constant::Block {
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
            });
            lower_to_lambda(b.into_inner(), raw)
        };

        assert!(matches!(
            lowered,
            Lambda::Lconst(Constant::Block { elements, .. })
                if matches!(
                    elements.as_slice(),
                    [
                        Constant::String(s),
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
        let b = RawArena::new();
        let lowered = {
            let raw = b.const_(Constant::Int {
                i: 0,
                comment: Some(Box::new(PointerInfo::Constructor(ConstructorTag {
                    name: "One1".to_string(),
                    const_: 3,
                    non_const: 0,
                    runtime_tag: Some(ConstructorRuntimeTag::Int(1)),
                }))),
            });
            lower_to_lambda(b.into_inner(), raw)
        };

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
        let b = RawArena::new();
        let lowered = {
            let raw = b.prim(
                Primitive::Porint,
                &[
                    b.const_(Constant::Int {
                        i: 0,
                        comment: None,
                    }),
                    b.const_(Constant::Int {
                        i: 1,
                        comment: Some(Box::new(PointerInfo::Constructor(ConstructorTag {
                            name: "B".to_string(),
                            const_: 2,
                            non_const: 0,
                            runtime_tag: Some(ConstructorRuntimeTag::Int(2)),
                        }))),
                    }),
                ],
                LamLoc::NONE,
            );
            lower_to_lambda(b.into_inner(), raw)
        };

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
        let b = RawArena::new();
        let lowered = {
            let raw = b.switch(
                b.var(Ident::create_local("v")),
                RawLambdaSwitch {
                    sw_consts_full: true,
                    sw_consts: vec![(
                        crate::lambda::SwitchKey::Constructor(
                            crate::types::VariantConstructorCase::Constant(
                                crate::types::VariantTag {
                                    name: crate::name::Name::new("A"),
                                    literal: None,
                                },
                            ),
                        ),
                        b.const_(Constant::int(0)),
                    )],
                    sw_blocks_full: true,
                    sw_blocks: Vec::new(),
                    sw_failaction: None,
                    sw_dispatch: crate::lambda::SwitchDispatch::Variant(
                        crate::types::VariantMatchingFacts {
                            tag_name: None,
                            block_types: vec![],
                            literal_tags: vec![crate::types::VariantLiteralTag::String(
                                "A".to_string().clone(),
                            )],
                            has_null: false,
                            has_undefined: false,
                            has_other_literal: true,
                        },
                    ),
                },
            );
            lower_to_lambda(b.into_inner(), raw)
        };

        let Lambda::Lswitch(_, switch) = lowered else {
            panic!("expected switch");
        };
        assert!(switch.sw_consts_full);
        assert!(switch.sw_blocks_full);
    }

    #[test]
    fn keeps_const_only_switch_consts_full_from_input_without_names() {
        let b = RawArena::new();
        let lowered = {
            let raw = b.switch(
                b.var(Ident::create_local("v")),
                RawLambdaSwitch {
                    sw_consts_full: false,
                    sw_consts: vec![
                        (crate::lambda::SwitchKey::Int(0), b.const_(Constant::int(7))),
                        (crate::lambda::SwitchKey::Int(1), b.const_(Constant::int(9))),
                    ],
                    sw_blocks_full: true,
                    sw_blocks: Vec::new(),
                    sw_failaction: None,
                    sw_dispatch: crate::lambda::SwitchDispatch::Direct,
                },
            );
            lower_to_lambda(b.into_inner(), raw)
        };

        let Lambda::Lswitch(_, switch) = lowered else {
            panic!("expected switch");
        };
        assert!(!switch.sw_consts_full);
        assert!(switch.sw_blocks_full);
    }

    #[test]
    fn keeps_named_linear_switches_instead_of_collapsing_to_scrutinee() {
        let b = RawArena::new();
        let scrutinee = Ident::create_local("scrutinee");
        let lowered = {
            let raw = b.switch(
                b.var(scrutinee),
                RawLambdaSwitch {
                    sw_consts_full: true,
                    sw_consts: vec![
                        (
                            crate::lambda::SwitchKey::Constructor(
                                crate::types::VariantConstructorCase::Constant(
                                    crate::types::VariantTag {
                                        name: crate::name::Name::new("A"),
                                        literal: None,
                                    },
                                ),
                            ),
                            b.const_(Constant::int(0)),
                        ),
                        (
                            crate::lambda::SwitchKey::Constructor(
                                crate::types::VariantConstructorCase::Constant(
                                    crate::types::VariantTag {
                                        name: crate::name::Name::new("B"),
                                        literal: None,
                                    },
                                ),
                            ),
                            b.const_(Constant::int(1)),
                        ),
                    ],
                    sw_blocks_full: true,
                    sw_blocks: Vec::new(),
                    sw_failaction: None,
                    sw_dispatch: crate::lambda::SwitchDispatch::Variant(
                        crate::types::VariantMatchingFacts {
                            tag_name: None,
                            block_types: vec![],
                            literal_tags: vec![
                                crate::types::VariantLiteralTag::String("B".to_string().clone()),
                                crate::types::VariantLiteralTag::String("A".to_string().clone()),
                            ],
                            has_null: false,
                            has_undefined: false,
                            has_other_literal: true,
                        },
                    ),
                },
            );
            lower_to_lambda(b.into_inner(), raw)
        };

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
    fn preserves_module_makeblock_shape() {
        let b = RawArena::new();
        let module_id = Ident::create_local("A");
        let lowered = {
            let raw = b.prim(
                Primitive::Pmakeblock(
                    TagInfo::Module(vec!["presentLight".to_string()]),
                    Mutable::Immutable,
                ),
                &[b.prim(
                    Primitive::Pfield(
                        1,
                        FieldDbgInfo::Module {
                            name: crate::name::Name::new("presentLight"),
                        },
                    ),
                    &[b.var(module_id)],
                    LamLoc::NONE,
                )],
                LamLoc::NONE,
            );
            lower_to_lambda(b.into_inner(), raw)
        };

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
    fn lowers_raw_js_code_to_code_payload_without_args() {
        let b = RawArena::new();
        let lowered = {
            let raw = b.prim(
                Primitive::PrawJsCode(JsRawInfo {
                    code: String::new(),
                    is_stmt: false,
                }),
                &[b.const_(Constant::String("__DEV__".to_string()))],
                LamLoc::NONE,
            );
            lower_to_lambda(b.into_inner(), raw)
        };

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
