//! `Lam_util` over the Lambda arena: `refine_let` and `field_flatten_get`.

use crate::ident::Ident;
use crate::lambda::LamLoc;
use crate::lambda::arena::{Lam, LamArena, Node};
use crate::lambda::lam_analysis::no_side_effects;
use crate::lambda::lam_compat::{FieldDbgInfo, LetKind};
use crate::lambda::lam_constant::Constant;
use crate::lambda::lam_hit::hit_variable;
use crate::lambda::lam_primitive::Primitive;
use crate::lambda::lam_stats::{Element, IdKind, IdentTable};
use crate::lambda::lam_tag_info::TagInfo;

/// `is_safe_to_alias` (lam_util.ml:79-98).
fn is_safe_to_alias(a: &LamArena, lam: Lam) -> bool {
    match a.node(lam) {
        Node::Var(_) | Node::Const(_) => true,
        Node::Prim { .. } => {
            let (primitive, args, _) = a.as_prim(lam).expect("checked primitive");
            match (primitive, args) {
                // A template without interpolations is a JavaScript literal.
                (Primitive::Ptemplate(segments), []) if segments.len() == 1 => true,
                (Primitive::Pfield(_, FieldDbgInfo::Module { .. }), [x]) => {
                    matches!(a.node(*x), Node::GlobalModule(_) | Node::Var(_))
                }
                (Primitive::PsomeNotNest, [x]) => is_safe_to_alias(a, *x),
                _ => false,
            }
        }
        _ => false,
    }
}

/// `Lam_util.refine_let` (lam_util.ml:68-138).
pub fn refine_let(a: &mut LamArena, kind: LetKind, param: Ident, arg: Lam, body: Lam) -> Lam {
    match refine_let_parts(a, kind, param, arg, body) {
        Some(refined) => refined,
        None => a.let_(kind, param, arg, body),
    }
}

/// `Lam_util.refine_let ~original`: when no clause applies and neither part
/// changed, the original binding `original` is handed back.
pub fn refine_let_original(
    a: &mut LamArena,
    original: Lam,
    kind: LetKind,
    param: Ident,
    arg: Lam,
    body: Lam,
) -> Lam {
    if let Some(refined) = refine_let_parts(a, kind, param, arg, body) {
        return refined;
    }
    match a.node(original) {
        Node::Let {
            kind: k,
            id,
            value,
            body: b,
        } if k == kind && value == arg && b == body && a.ident(id) == param => original,
        _ => a.let_(kind, param, arg, body),
    }
}

fn refine_let_parts(
    a: &mut LamArena,
    kind: LetKind,
    param: Ident,
    arg: Lam,
    body: Lam,
) -> Option<Lam> {
    match a.node(body) {
        // (Return) `let[k] x = e in x` -> `e` (lam_util.ml:100-104).
        Node::Var(w) if a.ident(w) == param => return Some(arg),
        // (Prim) `let[k] x = e in prim p [x]` -> `prim p [e]` unless `p`
        // constructs a block (lam_util.ml:105-111).
        Node::Prim { args, info } => {
            if let [w] = a.list(args)
                && a.as_var(*w).is_some_and(|w| w == param)
                && !matches!(a.prim_payload(info).primitive, Primitive::Pmakeblock(_, _))
            {
                let args = a.add_list(&[arg]);
                return Some(a.prim_with(info, args));
            }
        }
        // (Call) `let[k] x = e in fn(x)` -> `fn(e)` when fn does not mention
        // x (lam_util.ml:112-117).
        Node::Apply { func, args, info } => {
            if let [w] = a.list(args)
                && a.as_var(*w).is_some_and(|w| w == param)
                && !hit_variable(a, &param, func)
            {
                let args = a.add_list(&[arg]);
                return Some(a.apply_raw_with(func, args, info));
            }
        }
        _ => {}
    }
    match kind {
        // (Alias) lam_util.ml:118-124.
        LetKind::Strict | LetKind::StrictOpt if is_safe_to_alias(a, arg) => {
            Some(a.let_(LetKind::Alias, param, arg, body))
        }
        // (Strict λ) lam_util.ml:125-130.
        LetKind::Strict if matches!(a.node(arg), Node::Function { .. }) => {
            Some(a.let_(LetKind::StrictOpt, param, arg, body))
        }
        // (Strict Pure) lam_util.ml:131-136.
        LetKind::Strict if no_side_effects(a, arg) => {
            Some(a.let_(LetKind::StrictOpt, param, arg, body))
        }
        _ => None,
    }
}

/// `Lam_util.field_flatten_get` (lam_util.ml:202-232). `fallback` builds the
/// unfolded field access.
pub fn field_flatten_get(
    a: &mut LamArena,
    fallback: impl FnOnce(&mut LamArena) -> Lam,
    v: &Ident,
    i: i32,
    info: &FieldDbgInfo,
    tbl: &IdentTable,
) -> Lam {
    match tbl.get(v) {
        // lam_util.ml:204-207.
        Some(IdKind::Module(g)) => {
            let g = a.global_module(*g);
            a.prim(Primitive::Pfield(i, info.clone()), &[g], LamLoc::NONE)
        }
        // lam_util.ml:208-213.
        Some(IdKind::ImmutableBlock(arr)) => match arr.get(i as usize) {
            Some(Element::SimpleForm(l)) => *l,
            Some(Element::Na) | None => fallback(a),
        },
        Some(IdKind::Constant(c)) => {
            let picked = match a.constant(*c) {
                // lam_util.ml:214-224.
                Constant::Block {
                    tag_info, elements, ..
                } if matches!(**tag_info, TagInfo::Record { .. }) => {
                    let TagInfo::Record { fields, .. } = &**tag_info else {
                        unreachable!()
                    };
                    match info {
                        FieldDbgInfo::Record { name } => fields
                            .iter()
                            .position(|(field_name, _)| field_name == name)
                            .and_then(|idx| elements.get(idx))
                            .filter(|c| !c.is_allocating())
                            .cloned(),
                        _ => None,
                    }
                }
                // lam_util.ml:225-230.
                Constant::Block { elements, .. } => elements
                    .get(i as usize)
                    .filter(|c| !c.is_allocating())
                    .cloned(),
                _ => None,
            };
            match picked {
                Some(c) => a.const_(c),
                None => fallback(a),
            }
        }
        // lam_util.ml:231-232.
        _ => fallback(a),
    }
}
