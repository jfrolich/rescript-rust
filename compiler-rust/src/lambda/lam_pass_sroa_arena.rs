//! `Lam_pass_sroa`: scalar replacement of local mutable blocks, over the
//! Lambda arena.
//!
//! A block can be replaced by mutable scalar bindings when every occurrence
//! of it is a direct, statically indexed field read or write. JavaScript
//! closures capture bindings, so accesses from nested functions remain
//! eligible. Analysis is separate from rewriting so a failed eligibility
//! check cannot partially transform the term.

use crate::context::IdGenerator;
use crate::ident::Ident;
use crate::lambda::TagInfo;
use crate::lambda::arena::{Lam, LamArena, Node};
use crate::lambda::lam_analysis_arena::no_side_effects;
use crate::lambda::lam_compat::LetKind;
use crate::lambda::lam_primitive::Primitive;
use crate::lambda::lam_util_arena::refine_let;
use crate::parser::ast::MutableFlag;

#[derive(Clone, Copy, Default)]
struct FieldUse {
    read: bool,
    written: bool,
}

/// The direct field access `lam` makes of `block`.
enum Access {
    Read(i32),
    Write(i32, Lam),
}

fn access_of(a: &LamArena, block: &Ident, lam: Lam) -> Option<Access> {
    let (primitive, args, _) = a.as_prim(lam)?;
    match (primitive, args) {
        (Primitive::Pfield(index, _), [v]) if a.as_var(*v).is_some_and(|v| v == *block) => {
            Some(Access::Read(*index))
        }
        (Primitive::Psetfield(index, _), [v, value])
            if a.as_var(*v).is_some_and(|v| v == *block) =>
        {
            Some(Access::Write(*index, *value))
        }
        _ => None,
    }
}

fn valid_field(uses: &[FieldUse], index: i32) -> bool {
    index >= 0 && (index as usize) < uses.len()
}

/// Is `block` used only as direct, in-range field reads and writes? Records
/// how each field is used.
fn analyze(a: &LamArena, block: &Ident, uses: &mut [FieldUse], lam: Lam) -> bool {
    match a.node(lam) {
        Node::Var(id) => a.ident(id) != *block,
        Node::Assign { id, value } => a.ident(id) != *block && analyze(a, block, uses, value),
        _ => match access_of(a, block, lam) {
            Some(Access::Read(index)) => {
                if valid_field(uses, index) {
                    uses[index as usize].read = true;
                    true
                } else {
                    false
                }
            }
            Some(Access::Write(index, value)) => {
                if valid_field(uses, index) {
                    uses[index as usize].written = true;
                    analyze(a, block, uses, value)
                } else {
                    false
                }
            }
            None => !shallow_exists(a, lam, &mut |a, x| !analyze(a, block, uses, x)),
        },
    }
}

/// `Lambda_traverse.shallow_exists`, in its child order (the body of a
/// `let rec` before its bindings).
fn shallow_exists(a: &LamArena, lam: Lam, f: &mut impl FnMut(&LamArena, Lam) -> bool) -> bool {
    if let Node::LetRec { values, body, .. } = a.node(lam) {
        return f(a, body) || a.list(values).iter().any(|x| f(a, *x));
    }
    let mut found = false;
    a.iter_children(lam, |x| {
        if !found && f(a, x) {
            found = true;
        }
    });
    found
}

fn discard_value(a: &mut LamArena, value: Lam, body: Lam) -> Lam {
    if no_side_effects(a, value) {
        body
    } else {
        a.seq(value, body)
    }
}

fn rewrite(a: &mut LamArena, block: &Ident, fields: &[Ident], uses: &[FieldUse], lam: Lam) -> Lam {
    match access_of(a, block, lam) {
        Some(Access::Read(index)) => a.var(fields[index as usize]),
        Some(Access::Write(index, value)) => {
            let value = rewrite(a, block, fields, uses, value);
            let index = index as usize;
            if !uses[index].read {
                let unit = a.unit();
                discard_value(a, value, unit)
            } else {
                a.assign(fields[index], value)
            }
        }
        None => a.shallow_map(lam, &mut |a, x| rewrite(a, block, fields, uses, x)),
    }
}

fn fields_for_block(
    id_gen: &IdGenerator,
    block: &Ident,
    info: &TagInfo,
    field_count: usize,
) -> Vec<Ident> {
    if field_count == 1 {
        return vec![*block];
    }
    let named = |name: &str| id_gen.create(&format!("{}_{}", block.name(), name));
    match info {
        TagInfo::Record { fields, .. } | TagInfo::RecordInlined { fields, .. }
            if fields.len() == field_count =>
        {
            return fields.iter().map(|(name, _)| named(name)).collect();
        }
        TagInfo::RecordExt { fields, .. } if fields.len() == field_count => {
            return fields.iter().map(|name| named(name)).collect();
        }
        _ => {}
    }
    (0..field_count)
        .map(|index| {
            if index == 0 {
                *block
            } else {
                block.rename(id_gen)
            }
        })
        .collect()
}

/// `Lam_pass_sroa.replace`: `None` when the block is used other than by
/// direct field access.
fn replace(
    a: &mut LamArena,
    id_gen: &IdGenerator,
    block: &Ident,
    info: &TagInfo,
    initializers: &[Lam],
    body: Lam,
) -> Option<Lam> {
    if initializers.is_empty() {
        return None;
    }
    let mut uses = vec![FieldUse::default(); initializers.len()];
    if !analyze(a, block, &mut uses, body) {
        return None;
    }
    let fields = fields_for_block(id_gen, block, info, initializers.len());
    let mut body = rewrite(a, block, &fields, &uses, body);
    // `bind_fields` recurses before binding: the last field is innermost.
    for (index, &init) in initializers.iter().enumerate().rev() {
        let use_ = uses[index];
        body = if !use_.read {
            discard_value(a, init, body)
        } else if !use_.written {
            refine_let(a, LetKind::Strict, fields[index], init, body)
        } else {
            a.let_(LetKind::Variable, fields[index], init, body)
        };
    }
    Some(body)
}

fn simplify_inner(a: &mut LamArena, id_gen: &IdGenerator, lam: Lam) -> Lam {
    match a.node(lam) {
        Node::Let {
            kind,
            id,
            value,
            body,
        } => {
            let init = simplify_inner(a, id_gen, value);
            let nbody = simplify_inner(a, id_gen, body);
            let block = a.ident(id);
            if matches!(kind, LetKind::Strict | LetKind::StrictOpt)
                && let Node::Prim { args, info } = a.node(init)
                && let Primitive::Pmakeblock(tag, _) = &a.prim_payload(info).primitive
                && tag.mutable_flag() != MutableFlag::Immutable
            {
                let tag = tag.clone();
                let args = a.list_vec(args);
                if let Some(replacement) = replace(a, id_gen, &block, &tag, &args, nbody) {
                    return replacement;
                }
            }
            if init == value && nbody == body {
                lam
            } else {
                a.let_with(kind, id, init, nbody)
            }
        }
        _ => a.shallow_map(lam, &mut |a, x| simplify_inner(a, id_gen, x)),
    }
}

/// `Lam_pass_sroa.simplify`.
pub fn simplify(a: &mut LamArena, lam: Lam, id_gen: &IdGenerator) -> Lam {
    simplify_inner(a, id_gen, lam)
}
