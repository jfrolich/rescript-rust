//! Port of `compiler/core/lam_pass_sroa.ml`: scalar replacement of
//! aggregates for local mutable blocks.
//!
//! A block can be replaced by mutable scalar bindings when every occurrence
//! of the block is a direct, statically indexed field read or write.
//! JavaScript closures capture bindings, so direct accesses from nested
//! functions remain eligible. Analysis is kept separate from rewriting so a
//! failed eligibility check cannot partially transform the term.

use crate::context::IdGenerator;
use crate::ident::Ident;
use crate::lambda::lam_analysis::no_side_effects;
use crate::lambda::lam_compat::LetKind;
use crate::lambda::lam_primitive::Primitive;
use crate::lambda::lam_util::refine_let;
use crate::lambda::lambda_traverse::{Mapped, shallow_exists, shallow_map_sharing};
use crate::lambda::{Lambda, PrimInfo, TagInfo};
use crate::parser::ast::MutableFlag;

#[derive(Clone, Copy, Default)]
struct FieldUse {
    read: bool,
    written: bool,
}

fn valid_field(uses: &[FieldUse], index: i32) -> bool {
    index >= 0 && (index as usize) < uses.len()
}

/// The direct field access `lam` makes of `block`: the primitive's index and,
/// for a write, the value written.
enum Access<'a> {
    Read(i32),
    Write(i32, &'a Lambda),
}

fn access_of<'a>(block: &Ident, lam: &'a Lambda) -> Option<Access<'a>> {
    let Lambda::Lprim(prim) = lam else {
        return None;
    };
    match (&prim.primitive, prim.args.as_slice()) {
        (Primitive::Pfield(index, _), [Lambda::Lvar(id)]) if id == block => {
            Some(Access::Read(*index))
        }
        (Primitive::Psetfield(index, _), [Lambda::Lvar(id), value]) if id == block => {
            Some(Access::Write(*index, value))
        }
        _ => None,
    }
}

/// Does the block appear only as direct, in-range field reads and writes?
/// While answering, record how every field is used. [`analyze`] and
/// [`rewrite`] are a matched pair: `rewrite` handles exactly the occurrences
/// `analyze` accepts.
fn analyze(block: &Ident, uses: &mut [FieldUse], lam: &Lambda) -> bool {
    match lam {
        Lambda::Lvar(id) => id != block,
        Lambda::Lassign(id, value) => id != block && analyze(block, uses, value),
        _ => match access_of(block, lam) {
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
                    analyze(block, uses, value)
                } else {
                    false
                }
            }
            None => !shallow_exists(lam, &mut |child| !analyze(block, uses, child)),
        },
    }
}

fn discard_value(value: Lambda, body: Lambda) -> Lambda {
    if no_side_effects(&value) {
        body
    } else {
        Lambda::seq(value, body)
    }
}

fn rewrite(block: &Ident, fields: &[Ident], uses: &[FieldUse], lam: Lambda) -> Mapped {
    match access_of(block, &lam) {
        Some(Access::Read(index)) => (Lambda::var(fields[index as usize]), true),
        Some(Access::Write(index, _)) => {
            let Lambda::Lprim(prim) = lam else {
                unreachable!()
            };
            let PrimInfo { mut args, .. } = *prim;
            let value = args.pop().expect("checked setfield value");
            let (value, _) = rewrite(block, fields, uses, value);
            let index = index as usize;
            if !uses[index].read {
                (discard_value(value, Lambda::unit()), true)
            } else {
                (Lambda::assign(fields[index], value), true)
            }
        }
        None => match &lam {
            // Unreachable: `analyze` rejected the block for both of these.
            Lambda::Lvar(id) if id == block => unreachable!("sroa: block escapes"),
            Lambda::Lassign(id, _) if id == block => unreachable!("sroa: block reassigned"),
            _ => shallow_map_sharing(lam, &mut |child| rewrite(block, fields, uses, child)),
        },
    }
}

fn fields_for_block(
    id_gen: &IdGenerator,
    block: &Ident,
    info: &TagInfo,
    field_count: usize,
) -> Vec<Ident> {
    let fallback = || {
        (0..field_count)
            .map(|index| {
                if index == 0 {
                    *block
                } else {
                    block.rename(id_gen)
                }
            })
            .collect::<Vec<_>>()
    };
    if field_count == 1 {
        return vec![*block];
    }
    let names: Option<Vec<String>> = match info {
        TagInfo::Record { fields, .. } | TagInfo::RecordInlined { fields, .. } => (fields.len()
            == field_count)
            .then(|| fields.iter().map(|(name, _)| name.clone()).collect()),
        TagInfo::RecordExt { fields, .. } => (fields.len() == field_count).then(|| fields.clone()),
        TagInfo::Tuple
        | TagInfo::Constructor { .. }
        | TagInfo::PolyVar(_)
        | TagInfo::Module(_)
        | TagInfo::ModuleExport(_)
        | TagInfo::Extension
        | TagInfo::Some
        | TagInfo::SomeNotNested => None,
    };
    match names {
        None => fallback(),
        Some(names) => names
            .iter()
            .map(|name| id_gen.create(&format!("{}_{}", block.name(), name)))
            .collect(),
    }
}

/// `Lam_pass_sroa.replace`: replace a non-escaping local block with
/// independent scalar values, or hand the pieces back when the block is used
/// other than by direct field access.
fn replace(
    id_gen: &IdGenerator,
    block: &Ident,
    info: &TagInfo,
    initializers: Vec<Lambda>,
    body: Lambda,
) -> Result<Lambda, (Vec<Lambda>, Lambda)> {
    if initializers.is_empty() {
        return Err((initializers, body));
    }
    let field_count = initializers.len();
    let mut uses = vec![FieldUse::default(); field_count];
    if !analyze(block, &mut uses, &body) {
        return Err((initializers, body));
    }
    let fields = fields_for_block(id_gen, block, info, field_count);
    let (mut body, _) = rewrite(block, &fields, &uses, body);
    // `bind_fields` recurses before binding, so the innermost binding is the
    // last field: fold from the right.
    for (index, init) in initializers.into_iter().enumerate().rev() {
        let use_ = uses[index];
        // A never-read field needs no storage; its initializer and writes are
        // retained only when they have effects. A read-only field can use a
        // normal refined let, while a field that is both read and written
        // still needs a mutable scalar binding.
        body = if !use_.read {
            discard_value(init, body)
        } else if !use_.written {
            refine_let(LetKind::Strict, fields[index], init, body)
        } else {
            Lambda::let_(LetKind::Variable, fields[index], init, body)
        };
    }
    Ok(body)
}

fn simplify_inner(id_gen: &IdGenerator, lam: Lambda) -> Mapped {
    match lam {
        Lambda::Llet(kind, block, init, body) => {
            let (init, c1) = simplify_inner(id_gen, *init);
            let (body, c2) = simplify_inner(id_gen, *body);
            let eligible = matches!(kind, LetKind::Strict | LetKind::StrictOpt)
                && matches!(&init, Lambda::Lprim(prim)
                    if matches!(&prim.primitive, Primitive::Pmakeblock(info, _)
                        if info.mutable_flag() != MutableFlag::Immutable));
            if eligible {
                let Lambda::Lprim(prim) = init else {
                    unreachable!()
                };
                let PrimInfo {
                    primitive,
                    args,
                    loc,
                } = *prim;
                let Primitive::Pmakeblock(info, mutable) = primitive else {
                    unreachable!()
                };
                match replace(id_gen, &block, &info, args, body) {
                    Ok(replacement) => (replacement, true),
                    Err((args, body)) => {
                        let init = Lambda::Lprim(Box::new(PrimInfo {
                            primitive: Primitive::Pmakeblock(info, mutable),
                            args,
                            loc,
                        }));
                        (Lambda::let_(kind, block, init, body), c1 || c2)
                    }
                }
            } else {
                (Lambda::let_(kind, block, init, body), c1 || c2)
            }
        }
        _ => shallow_map_sharing(lam, &mut |child| simplify_inner(id_gen, child)),
    }
}

/// `Lam_pass_sroa.simplify`: scalar-replace eligible local mutable blocks
/// throughout a Lambda term.
pub fn simplify(lam: Lambda, id_gen: &IdGenerator) -> Lambda {
    simplify_inner(id_gen, lam).0
}
