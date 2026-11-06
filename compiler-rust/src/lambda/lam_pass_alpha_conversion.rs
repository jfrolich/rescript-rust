//! `Lam_pass_alpha_conversion.alpha_conversion` and
//! `Lam_eta_conversion.transform_under_supply` over the Lambda arena.

use crate::context::IdGenerator;
use crate::ident::Ident;
use crate::lambda::LamLoc;
use crate::lambda::arena::{Lam, LamArena, LamList, Node};
use crate::lambda::lam_arity::Arity;
use crate::lambda::lam_compat::{FieldDbgInfo, LetKind};
use crate::lambda::lam_constant::Constant;
use crate::lambda::lam_pass_collect::ExternalArityResolver;
use crate::lambda::lam_pass_collect::get_arity_with_external_arity;
use crate::lambda::lam_primitive::Primitive;
use crate::lambda::lam_stats::LamStats;
use crate::lambda::{ApInfo, ApplyStatus, FunctionAttribute};

/// `Lam_pass_alpha_conversion.alpha_conversion`
/// (lam_pass_alpha_conversion.ml:25-129).
pub fn alpha_conversion(
    a: &mut LamArena,
    meta: &mut LamStats,
    lam: Lam,
    external_arity: &mut ExternalArityResolver<'_>,
) -> Lam {
    Alpha {
        meta,
        external_arity,
    }
    .simpl(a, lam)
}

struct Alpha<'a, 'r> {
    meta: &'a mut LamStats,
    external_arity: &'a mut ExternalArityResolver<'r>,
}

impl Alpha<'_, '_> {
    fn arity(&mut self, a: &LamArena, lam: Lam) -> Arity {
        get_arity_with_external_arity(a, self.meta, lam, self.external_arity)
    }

    fn simpl_list(&mut self, a: &mut LamArena, xs: &[Lam]) -> smallvec::SmallVec<[Lam; 8]> {
        xs.iter().map(|x| self.simpl(a, *x)).collect()
    }

    /// `populate_apply_info` (lam_pass_alpha_conversion.ml:26-49).
    fn populate_apply_info(
        &mut self,
        a: &mut LamArena,
        jsx: bool,
        args_arity: &[i32],
        func: Lam,
        args: LamList,
        ap_info: ApInfo,
    ) -> Lam {
        let args = a.list_vec(args);
        let len = args.len() as i32;
        let infer_full = || ApInfo {
            status: ApplyStatus::InferFull,
            ..ap_info.clone()
        };
        match args_arity.first().copied() {
            None | Some(0) => {
                let f = self.simpl(a, func);
                let xs = self.simpl_list(a, &args);
                a.apply(f, &xs, ap_info, jsx)
            }
            // lam_pass_alpha_conversion.ml:33-36
            Some(x) if x == len => {
                let f = self.simpl(a, func);
                let xs = self.simpl_list(a, &args);
                a.apply(f, &xs, infer_full(), jsx)
            }
            // lam_pass_alpha_conversion.ml:37-42
            Some(x) if x > len => {
                let f = self.simpl(a, func);
                let xs = self.simpl_list(a, &args);
                let info = infer_full();
                transform_under_supply(a, &self.meta.id_gen, x - len, &info, f, &xs)
            }
            // lam_pass_alpha_conversion.ml:43-48
            Some(x) => {
                let split = x as usize;
                let first = self.simpl_list(a, &args[..split]);
                let rest = self.simpl_list(a, &args[split..]);
                let f = self.simpl(a, func);
                let inner = a.apply(f, &first, infer_full(), false);
                a.apply(inner, &rest, ap_info, jsx)
            }
        }
    }

    /// `simpl` (lam_pass_alpha_conversion.ml:50-126).
    fn simpl(&mut self, a: &mut LamArena, lam: Lam) -> Lam {
        match a.node(lam) {
            Node::Const(_) | Node::Var(_) | Node::GlobalModule(_) => lam,
            Node::Apply { func, args, info } => {
                let args_arity = self.arity(a, func).extract_arity();
                let p = a.apply_payload(info).clone();
                self.populate_apply_info(a, p.transformed_jsx, &args_arity, func, args, p.info)
            }
            Node::Let {
                kind,
                id,
                value,
                body,
            } => {
                let v = self.simpl(a, value);
                let b = self.simpl(a, body);
                if v == value && b == body {
                    lam
                } else {
                    a.let_with(kind, id, v, b)
                }
            }
            Node::LetRec { ids, values, body } => {
                let (nv, changed) = a.map_list(values, &mut |a, x| self.simpl(a, x));
                let nb = self.simpl(a, body);
                if !changed && nb == body {
                    lam
                } else {
                    a.letrec_with(ids, nv, nb)
                }
            }
            // `Lam.prim` refolds every primitive.
            Node::Prim { args, info } => {
                let (nargs, _) = a.map_list(args, &mut |a, x| self.simpl(a, x));
                a.prim_with(info, nargs)
            }
            Node::Function { body, info } => {
                let nb = self.simpl(a, body);
                if nb == body {
                    lam
                } else {
                    a.function_with(info, nb)
                }
            }
            Node::Switch {
                scrut,
                actions,
                info,
            } => {
                let ns = self.simpl(a, scrut);
                let (na, _) = a.map_list(actions, &mut |a, x| self.simpl(a, x));
                a.switch_with(ns, na, info)
            }
            Node::StringSwitch {
                scrut,
                actions,
                info,
            } => {
                let ns = self.simpl(a, scrut);
                let (na, _) = a.map_list(actions, &mut |a, x| self.simpl(a, x));
                a.string_switch_with(ns, na, info)
            }
            Node::If { cond, then_, else_ } => {
                let c = self.simpl(a, cond);
                let t = self.simpl(a, then_);
                let e = self.simpl(a, else_);
                a.if_(c, t, e)
            }
            // Every other node is rebuilt with its plain constructor.
            _ => a.shallow_map_plain(lam, &mut |a, x| self.simpl(a, x)),
        }
    }
}

/// `Lam_eta_conversion.transform_under_supply` (lam_eta_conversion.ml:37-75):
/// `function(extra) { fn(args ++ extra) }`, binding the operands that are not
/// safe to share to let-bound temporaries first.
pub fn transform_under_supply(
    a: &mut LamArena,
    id_gen: &IdGenerator,
    n: i32,
    ap_info: &ApInfo,
    func: Lam,
    args: &[Lam],
) -> Lam {
    // OCaml uses the shared Ident.create counter (lam_eta_conversion.ml:37-39).
    let extra_args: smallvec::SmallVec<[Ident; 4]> =
        (0..n).map(|_| id_gen.create("param")).collect();
    let mut operands: smallvec::SmallVec<[Lam; 8]> =
        smallvec::SmallVec::with_capacity(args.len() + 1);
    let mut bindings: smallvec::SmallVec<[(Ident, Lam); 4]> = smallvec::SmallVec::new();
    for &lam in std::iter::once(&func).chain(args) {
        if is_safe_to_share(a, lam) {
            operands.push(lam);
        } else {
            let v = id_gen.create("partial_arg");
            bindings.push((v, lam));
            let var = a.var(v);
            operands.push(var);
        }
    }
    let f = operands[0];
    let mut all_args: smallvec::SmallVec<[Lam; 8]> = operands[1..].iter().copied().collect();
    for id in &extra_args {
        let v = a.var(*id);
        all_args.push(v);
    }
    let body = a.apply(f, &all_args, ap_info.clone(), false);
    let mut result = a.function_(
        n,
        &extra_args,
        body,
        FunctionAttribute::default(),
        LamLoc::NONE,
    );
    for (id, x) in bindings.into_iter().rev() {
        result = a.let_(LetKind::Strict, id, x, result);
    }
    result
}

/// lam_eta_conversion.ml:42-50.
fn is_safe_to_share(a: &LamArena, lam: Lam) -> bool {
    match a.node(lam) {
        Node::Var(_) | Node::Function { .. } => true,
        Node::Const(c) => matches!(
            a.constant(c),
            Constant::Int { .. }
                | Constant::Char(_)
                | Constant::String(_)
                | Constant::ImmString(_)
                | Constant::Float(_)
                | Constant::BigInt { .. }
                | Constant::Pointer(_)
                | Constant::JsTrue
                | Constant::JsFalse
                | Constant::JsUndefined { .. }
        ),
        Node::Prim { info, .. } => matches!(
            a.prim_payload(info).primitive,
            Primitive::Pfield(_, FieldDbgInfo::Module { .. })
        ),
        _ => false,
    }
}
