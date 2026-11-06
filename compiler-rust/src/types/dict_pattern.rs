//! Dict patterns in exhaustiveness checking and match compilation
//! (OCaml `compiler/ml/dict_pattern.ml`).
//!
//! Exhaustiveness checking and match compilation see a dict pattern
//! `dict{"a": p}` as a record pattern of the `dict` type, whose labels are its
//! keys: an optional field per key. `lowering` gives the labels to the keys of
//! one match, so they line up across its cases.

use std::borrow::Cow;
use std::sync::Arc;

use crate::fast_hash::AHashMap;
use crate::parse_arena::LidentIdx;
use crate::parser::ast::ClosedFlag;
use crate::types::asttypes::{MutableFlag, PrivateFlag};
use crate::types::context::TypeContext;
use crate::types::decl::{LabelDescription, RecordRepresentation};
use crate::types::predef;
use crate::types::typedtree::{Loc, Pattern, PatternDesc};

/// The direct subpatterns of `p` (OCaml `Typedtree.iter_pattern_desc`).
fn for_each_subpattern<'p>(p: &'p Pattern, f: &mut impl FnMut(&'p Pattern)) {
    match &p.pat_desc {
        PatternDesc::Tpat_any
        | PatternDesc::Tpat_var(..)
        | PatternDesc::Tpat_constant(_)
        | PatternDesc::Tpat_interval(..)
        | PatternDesc::Tpat_variant(_, None, _) => {}
        PatternDesc::Tpat_alias(inner, _, _) => f(inner),
        PatternDesc::Tpat_variant(_, Some(inner), _) => f(inner),
        PatternDesc::Tpat_tuple(ps)
        | PatternDesc::Tpat_construct(_, _, ps)
        | PatternDesc::Tpat_array(ps) => ps.iter().for_each(f),
        PatternDesc::Tpat_record(fields, _, _) => fields.iter().for_each(|(_, _, p, _)| f(p)),
        PatternDesc::Tpat_dict(entries) => entries.iter().for_each(|e| f(&e.tdp_pattern)),
        PatternDesc::Tpat_or(p1, p2, _) => {
            f(p1);
            f(p2);
        }
    }
}

/// `Dict_pattern.contains_dict`.
fn contains_dict(p: &Pattern) -> bool {
    if matches!(p.pat_desc, PatternDesc::Tpat_dict(_)) {
        return true;
    }
    let mut found = false;
    for_each_subpattern(p, &mut |sub| found = found || contains_dict(sub));
    found
}

/// `Dict_pattern.keys`: the keys of the dict patterns in `pats`, in order of
/// appearance.
fn keys(pats: &[&Pattern]) -> Vec<String> {
    fn collect(p: &Pattern, keys: &mut Vec<String>) {
        if let PatternDesc::Tpat_dict(entries) = &p.pat_desc {
            for entry in entries {
                if !keys.contains(&entry.tdp_key.txt) {
                    keys.push(entry.tdp_key.txt.clone());
                }
            }
        }
        for_each_subpattern(p, &mut |sub| collect(sub, keys));
    }
    let mut keys = Vec::new();
    for p in pats {
        collect(p, &mut keys);
    }
    keys
}

/// `Dict_pattern.labels_of_keys`: an optional field of type `'a` in
/// `dict<'a>` per key.
fn labels_of_keys(ctx: &TypeContext, keys: Vec<String>) -> Vec<LabelDescription> {
    let value = ctx.new_generic_var(None);
    let lbl_res = ctx.new_generic_predef_constr(predef::path_dict(), vec![value]);
    let lbl_arg = ctx.new_generic_predef_constr(predef::path_option(), vec![value]);
    ctx.alloc_label_array(|lbl_all| {
        keys.into_iter()
            .enumerate()
            .map(|(pos, key)| LabelDescription {
                lbl_runtime_name: key.clone(),
                lbl_name: key,
                lbl_res,
                lbl_arg,
                lbl_mut: MutableFlag::Immutable,
                lbl_optional: true,
                lbl_pos: pos as i32,
                lbl_all,
                lbl_repres: RecordRepresentation::RecordRegular,
                lbl_private: PrivateFlag::Public,
                lbl_loc: crate::types::DeclLoc::none(),
                lbl_attributes: Vec::new(),
            })
            .collect()
    })
}

/// `Dict_pattern.lowering`: turns the dict patterns of a match into record
/// patterns of the `dict` type, with an optional field per key.
pub struct Lowering {
    /// The label of each key; `None` when the match has no dict patterns and
    /// lowering is the identity.
    labels: Option<AHashMap<String, Arc<LabelDescription>>>,
}

impl Lowering {
    /// The lowering for a match whose patterns are `pats`.
    pub fn new(ctx: &TypeContext, pats: &[&Pattern]) -> Lowering {
        if !pats.iter().any(|p| contains_dict(p)) {
            return Lowering { labels: None };
        }
        let labels = labels_of_keys(ctx, keys(pats))
            .into_iter()
            .map(|lbl| (lbl.lbl_name.clone(), Arc::new(lbl)))
            .collect();
        Lowering {
            labels: Some(labels),
        }
    }

    /// Lower `p`, borrowing it when there's nothing to lower.
    pub fn lower<'p>(&self, p: &'p Pattern) -> Cow<'p, Pattern> {
        match &self.labels {
            None => Cow::Borrowed(p),
            Some(labels) => Cow::Owned(lower(labels, p)),
        }
    }
}

fn lower(labels: &AHashMap<String, Arc<LabelDescription>>, p: &Pattern) -> Pattern {
    let lower_box = |p: &Pattern| Box::new(lower(labels, p));
    let lower_all = |ps: &[Pattern]| ps.iter().map(|p| lower(labels, p)).collect();
    let pat_desc = match &p.pat_desc {
        PatternDesc::Tpat_dict(entries) => {
            let mut fields: Vec<_> = entries
                .iter()
                .map(|entry| {
                    // The field's longident is never read once lowered: the
                    // label carries the key.
                    let lid = Loc {
                        txt: LidentIdx(0),
                        loc: entry.tdp_key.loc,
                    };
                    (
                        lid,
                        labels[&entry.tdp_key.txt].clone(),
                        lower(labels, &entry.tdp_pattern),
                        entry.tdp_optional,
                    )
                })
                .collect();
            // Record patterns are sorted in the typed tree.
            fields.sort_by_key(|(_, lbl, _, _)| lbl.lbl_pos);
            PatternDesc::Tpat_record(fields, ClosedFlag::Open, None)
        }
        PatternDesc::Tpat_any
        | PatternDesc::Tpat_var(..)
        | PatternDesc::Tpat_constant(_)
        | PatternDesc::Tpat_interval(..)
        | PatternDesc::Tpat_variant(_, None, _) => p.pat_desc.clone(),
        PatternDesc::Tpat_alias(inner, id, name) => {
            PatternDesc::Tpat_alias(lower_box(inner), *id, name.clone())
        }
        PatternDesc::Tpat_variant(label, Some(inner), row) => {
            PatternDesc::Tpat_variant(label.clone(), Some(lower_box(inner)), *row)
        }
        PatternDesc::Tpat_tuple(ps) => PatternDesc::Tpat_tuple(lower_all(ps)),
        PatternDesc::Tpat_construct(lid, cstr, ps) => {
            PatternDesc::Tpat_construct(*lid, cstr.clone(), lower_all(ps))
        }
        PatternDesc::Tpat_array(ps) => PatternDesc::Tpat_array(lower_all(ps)),
        PatternDesc::Tpat_record(fields, closed, rest) => PatternDesc::Tpat_record(
            fields
                .iter()
                .map(|(lid, lbl, p, opt)| (*lid, lbl.clone(), lower(labels, p), *opt))
                .collect(),
            *closed,
            rest.clone(),
        ),
        PatternDesc::Tpat_or(p1, p2, row) => {
            PatternDesc::Tpat_or(lower_box(p1), lower_box(p2), row.clone())
        }
    };
    Pattern {
        pat_desc,
        pat_loc: p.pat_loc,
        pat_extra: p.pat_extra.clone(),
        pat_type: p.pat_type,
        pat_env: p.pat_env,
        pat_attributes: p.pat_attributes.clone(),
    }
}
