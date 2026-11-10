//! Dict patterns in exhaustiveness checking and match compilation
//! (OCaml `compiler/ml/dict_pattern.ml`).
//!
//! Exhaustiveness checking and match compilation see a dict pattern
//! `dict{"a": p}` as a record pattern of the `dict` type, whose labels are its
//! keys: an optional field per key. `lowering` gives the labels to the keys of
//! one match, so they line up across its cases.

use std::sync::Arc;

use crate::fast_hash::AHashMap;
use crate::parse_arena::LidentIdx;
use crate::parser::ast::ClosedFlag;
use crate::types::asttypes::{MutableFlag, PrivateFlag};
use crate::types::context::TypeContext;
use crate::types::decl::{LabelDescription, RecordRepresentation};
use crate::types::predef;
use crate::types::typedtree::{Loc, Pattern, PatternDesc, TPatIdx, TPatList, TypedArena};

/// Where lowering reads patterns and stores the ones it builds: the typed
/// arena, or the match compiler's overlay of it.
pub trait PatternStore {
    /// A pattern by handle.
    fn pat(&self, idx: TPatIdx) -> &Pattern;
    /// The handles of a pattern list.
    fn pat_list(&self, list: TPatList) -> &[TPatIdx];
    /// Store a pattern.
    fn push_pat(&mut self, p: Pattern) -> TPatIdx;
    /// Store a list of pattern handles.
    fn push_pat_list(&mut self, items: &[TPatIdx]) -> TPatList;
}

/// The direct subpatterns of `p` (OCaml `Typedtree.iter_pattern_desc`).
fn for_each_subpattern<'s>(
    ta: &'s impl PatternStore,
    p: &Pattern,
    f: &mut impl FnMut(&'s Pattern),
) {
    match &p.pat_desc {
        PatternDesc::Tpat_any
        | PatternDesc::Tpat_var(..)
        | PatternDesc::Tpat_constant(_)
        | PatternDesc::Tpat_interval(..)
        | PatternDesc::Tpat_variant(_, None, _) => {}
        PatternDesc::Tpat_alias(inner, _, _) => f(ta.pat(*inner)),
        PatternDesc::Tpat_variant(_, Some(inner), _) => f(ta.pat(*inner)),
        PatternDesc::Tpat_tuple(ps)
        | PatternDesc::Tpat_construct(_, _, ps)
        | PatternDesc::Tpat_array(ps) => ta.pat_list(*ps).iter().for_each(|&p| f(ta.pat(p))),
        PatternDesc::Tpat_record(fields, _, _) => {
            fields.iter().for_each(|(_, _, p, _)| f(ta.pat(*p)))
        }
        PatternDesc::Tpat_dict(entries) => {
            entries.iter().for_each(|e| f(ta.pat(e.tdp_pattern)))
        }
        PatternDesc::Tpat_or(p1, p2, _) => {
            f(ta.pat(*p1));
            f(ta.pat(*p2));
        }
    }
}

/// `Dict_pattern.contains_dict`.
fn contains_dict(ta: &impl PatternStore, p: &Pattern) -> bool {
    if matches!(p.pat_desc, PatternDesc::Tpat_dict(_)) {
        return true;
    }
    let mut found = false;
    for_each_subpattern(ta, p, &mut |sub| found = found || contains_dict(ta, sub));
    found
}

/// `Dict_pattern.keys`: the keys of the dict patterns in `pats`, in order of
/// appearance.
fn keys(ta: &impl PatternStore, pats: &[&Pattern]) -> Vec<String> {
    fn collect(ta: &impl PatternStore, p: &Pattern, keys: &mut Vec<String>) {
        if let PatternDesc::Tpat_dict(entries) = &p.pat_desc {
            for entry in entries {
                if !keys.contains(&entry.tdp_key.txt) {
                    keys.push(entry.tdp_key.txt.clone());
                }
            }
        }
        for_each_subpattern(ta, p, &mut |sub| collect(ta, sub, keys));
    }
    let mut keys = Vec::new();
    for p in pats {
        collect(ta, p, &mut keys);
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
    pub fn new(ctx: &TypeContext, ta: &impl PatternStore, pats: &[&Pattern]) -> Lowering {
        if !pats.iter().any(|p| contains_dict(ta, p)) {
            return Lowering { labels: None };
        }
        let labels = labels_of_keys(ctx, keys(ta, pats))
            .into_iter()
            .map(|lbl| (lbl.lbl_name.clone(), Arc::new(lbl)))
            .collect();
        Lowering {
            labels: Some(labels),
        }
    }

    /// Whether lowering is the identity: the match has no dict patterns.
    pub fn is_identity(&self) -> bool {
        self.labels.is_none()
    }

    /// Lower the stored pattern `p`, storing the lowered nodes in `ta`;
    /// `p` itself when there's nothing to lower.
    pub fn lower(&self, ta: &mut impl PatternStore, p: TPatIdx) -> TPatIdx {
        match &self.labels {
            None => p,
            Some(labels) => lower(ta, labels, p),
        }
    }
}

fn lower(
    ta: &mut impl PatternStore,
    labels: &AHashMap<String, Arc<LabelDescription>>,
    idx: TPatIdx,
) -> TPatIdx {
    let p = ta.pat(idx).clone();
    fn lower_list(
        ta: &mut impl PatternStore,
        labels: &AHashMap<String, Arc<LabelDescription>>,
        ps: TPatList,
    ) -> TPatList {
        let handles = ta.pat_list(ps).to_vec();
        let lowered: Vec<TPatIdx> = handles.into_iter().map(|p| lower(ta, labels, p)).collect();
        ta.push_pat_list(&lowered)
    }
    let pat_desc = match p.pat_desc {
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
                        lower(ta, labels, entry.tdp_pattern),
                        entry.tdp_optional,
                    )
                })
                .collect();
            // Record patterns are sorted in the typed tree.
            fields.sort_by_key(|(_, lbl, _, _)| lbl.lbl_pos);
            PatternDesc::Tpat_record(fields, ClosedFlag::Open, None)
        }
        desc @ (PatternDesc::Tpat_any
        | PatternDesc::Tpat_var(..)
        | PatternDesc::Tpat_constant(_)
        | PatternDesc::Tpat_interval(..)
        | PatternDesc::Tpat_variant(_, None, _)) => desc,
        PatternDesc::Tpat_alias(inner, id, name) => {
            PatternDesc::Tpat_alias(lower(ta, labels, inner), id, name)
        }
        PatternDesc::Tpat_variant(label, Some(inner), row) => {
            PatternDesc::Tpat_variant(label, Some(lower(ta, labels, inner)), row)
        }
        PatternDesc::Tpat_tuple(ps) => PatternDesc::Tpat_tuple(lower_list(ta, labels, ps)),
        PatternDesc::Tpat_construct(lid, cstr, ps) => {
            PatternDesc::Tpat_construct(lid, cstr, lower_list(ta, labels, ps))
        }
        PatternDesc::Tpat_array(ps) => PatternDesc::Tpat_array(lower_list(ta, labels, ps)),
        PatternDesc::Tpat_record(fields, closed, rest) => PatternDesc::Tpat_record(
            fields
                .into_iter()
                .map(|(lid, lbl, p, opt)| (lid, lbl, lower(ta, labels, p), opt))
                .collect(),
            closed,
            rest,
        ),
        PatternDesc::Tpat_or(p1, p2, row) => {
            let p1 = lower(ta, labels, p1);
            let p2 = lower(ta, labels, p2);
            PatternDesc::Tpat_or(p1, p2, row)
        }
    };
    // The lowered pattern shares the original's extras and attributes.
    ta.push_pat(Pattern { pat_desc, ..p })
}

impl PatternStore for TypedArena {
    fn pat(&self, idx: TPatIdx) -> &Pattern {
        self.pattern(idx)
    }
    fn pat_list(&self, list: TPatList) -> &[TPatIdx] {
        self.pattern_list(list)
    }
    fn push_pat(&mut self, p: Pattern) -> TPatIdx {
        self.push_pattern(p)
    }
    fn push_pat_list(&mut self, items: &[TPatIdx]) -> TPatList {
        self.push_pattern_list(items)
    }
}
