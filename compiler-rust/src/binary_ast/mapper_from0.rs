//! Mapper from parsetree0 to current parsetree
//!
//! This module converts the frozen parsetree0 format back to the current Rust
//! parsetree types. This is the inverse of `mapper_to0`.
//!
//! Key transformations:
//! - [@res.arity N] attribute + Function$ wrapper → function arity
//! - function$ type constructor → arrow type arity
//! - [@res.async] attribute → async flag
//! - [@res.await] attribute → Pexp_await
//! - [@res.partial] attribute → partial flag
//! - [@res.optional] attribute → optional record fields
//!
//! This mirrors `compiler/ml/ast_mapper_from0.ml`.

use std::borrow::Cow;

use crate::intern::StrIdx;
use crate::location::Located as OldLocated;
use crate::location::Location as FullLocation;
use crate::parse_arena::{
    CoreTypeIdx, ExprIdx, LocIdx, Located, ModExprIdx, ModTypeIdx, ParseArena, PatIdx,
};
use crate::parser::ast::{self as current, Attributes};
use crate::parser::longident::Longident;

use super::parsetree0 as pt0;
use crate::parser::ast::{PexpApply, PexpFun};

// ========== Public API ==========

/// Convert a structure from parsetree0 to current parsetree
pub fn map_structure(
    arena: &mut ParseArena,
    str: &[pt0::StructureItem],
) -> Vec<current::StructureItem> {
    let mut mapper = Mapper::new(arena);
    mapper.map_structure(str)
}

/// Convert a signature from parsetree0 to current parsetree
pub fn map_signature(
    arena: &mut ParseArena,
    sig: &[pt0::SignatureItem],
) -> Vec<current::SignatureItem> {
    let mut mapper = Mapper::new(arena);
    mapper.map_signature(sig)
}

// ========== Helper functions ==========

fn map_closed_flag(flag: &pt0::ClosedFlag) -> current::ClosedFlag {
    match flag {
        pt0::ClosedFlag::Closed => current::ClosedFlag::Closed,
        pt0::ClosedFlag::Open => current::ClosedFlag::Open,
    }
}

fn map_arity(arity: &pt0::Arity, arena: &mut ParseArena) -> current::Arity {
    // pt0::Arity is Option<i32>, current::Arity is ArityIdx
    arena.push_arity(*arity)
}

// ========== Attribute helpers ==========

fn has_await_attribute(attrs: &[pt0::Attribute]) -> bool {
    attrs.iter().any(|(name, _)| name.txt == "res.await")
}

fn remove_await_attribute(attrs: &[pt0::Attribute]) -> Vec<pt0::Attribute> {
    attrs
        .iter()
        .filter(|(name, _)| name.txt != "res.await")
        .cloned()
        .collect()
}

fn has_async_attribute(arena: &ParseArena, attrs: &[current::Attribute]) -> bool {
    attrs
        .iter()
        .any(|(name, _)| arena.get_string(name.txt) == "res.async")
}

fn has_partial_attribute(attrs: &[pt0::Attribute]) -> bool {
    attrs.iter().any(|(name, _)| name.txt == "res.partial")
}

fn remove_partial_attribute(attrs: &[pt0::Attribute]) -> Vec<pt0::Attribute> {
    attrs
        .iter()
        .filter(|(name, _)| name.txt != "res.partial")
        .cloned()
        .collect()
}

fn has_optional_attribute(arena: &ParseArena, attrs: &[current::Attribute]) -> bool {
    attrs
        .iter()
        .any(|(name, _)| arena.get_string(name.txt) == "res.optional")
}

fn remove_optional_attribute(arena: &ParseArena, attrs: &[current::Attribute]) -> Attributes {
    attrs
        .iter()
        .filter(|(name, _)| arena.get_string(name.txt) != "res.optional")
        .cloned()
        .collect::<Vec<_>>()
        .into()
}

fn get_arity_from_attributes(arena: &ParseArena, attrs: &[current::Attribute]) -> Option<i32> {
    for (name, payload) in attrs {
        if arena.get_string(name.txt) == "res.arity" {
            if let current::Payload::PStr(items) = payload {
                if let Some(item) = items.first() {
                    if let current::StructureItemDesc::Pstr_eval(inner) = item.pstr_desc.as_ref() {
                        let (ref eval_expr_idx, _) = **inner;
                        let eval_expr = arena.get_expr(*eval_expr_idx);
                        if let current::ExpressionDesc::Pexp_constant(c) =
                            eval_expr.pexp_desc.as_ref()
                        {
                            if let current::Constant::Integer(s, _) = c.as_ref() {
                                return s.parse().ok();
                            }
                        }
                    }
                }
            }
        }
    }
    None
}

fn remove_arity_attribute(
    arena: &ParseArena,
    attrs: &[current::Attribute],
) -> Vec<current::Attribute> {
    attrs
        .iter()
        .filter(|(name, _)| arena.get_string(name.txt) != "res.arity")
        .cloned()
        .collect()
}

// ========== for-of helpers (upstream #7887) ==========

const FOR_OF_ATTR_NAME: &str = "_res.for_of";
const FOR_AWAIT_OF_ATTR_NAME: &str = "_res.for_await_of";

fn extract_for_of_iterable(attrs: &[pt0::Attribute]) -> Option<&pt0::Expression> {
    extract_for_of_iterable_with_name(attrs, FOR_OF_ATTR_NAME)
}

fn extract_for_await_of_iterable(attrs: &[pt0::Attribute]) -> Option<&pt0::Expression> {
    extract_for_of_iterable_with_name(attrs, FOR_AWAIT_OF_ATTR_NAME)
}

fn extract_for_of_iterable_with_name<'a>(
    attrs: &'a [pt0::Attribute],
    name: &str,
) -> Option<&'a pt0::Expression> {
    attrs.iter().find_map(|(attr_name, payload)| {
        if attr_name.txt != name {
            return None;
        }
        match payload {
            pt0::Payload::PPat(_, Some(expr)) => Some(expr.as_ref()),
            _ => None,
        }
    })
}

fn remove_for_of_attributes(attrs: &[pt0::Attribute]) -> Vec<pt0::Attribute> {
    attrs
        .iter()
        .filter(|(name, _)| name.txt != FOR_OF_ATTR_NAME && name.txt != FOR_AWAIT_OF_ATTR_NAME)
        .cloned()
        .collect()
}

fn has_for_of_attribute(attrs: &[pt0::Attribute]) -> bool {
    attrs
        .iter()
        .any(|(name, _)| name.txt == FOR_OF_ATTR_NAME || name.txt == FOR_AWAIT_OF_ATTR_NAME)
}

// ========== JSX helpers ==========

fn has_jsx_attribute(attrs: &[pt0::Attribute]) -> bool {
    attrs.iter().any(|(name, _)| name.txt == "JSX")
}

fn remove_jsx_attribute(attrs: &[pt0::Attribute]) -> Vec<pt0::Attribute> {
    attrs
        .iter()
        .filter(|(name, _)| name.txt != "JSX")
        .cloned()
        .collect()
}

// ========== Flag conversions ==========

fn map_rec_flag(flag: pt0::RecFlag) -> current::RecFlag {
    match flag {
        pt0::RecFlag::Nonrecursive => current::RecFlag::Nonrecursive,
        pt0::RecFlag::Recursive => current::RecFlag::Recursive,
    }
}

fn map_direction_flag(flag: pt0::DirectionFlag) -> current::DirectionFlag {
    match flag {
        pt0::DirectionFlag::Upto => current::DirectionFlag::Upto,
        pt0::DirectionFlag::Downto => current::DirectionFlag::Downto,
    }
}

fn map_private_flag(flag: pt0::PrivateFlag) -> current::PrivateFlag {
    match flag {
        pt0::PrivateFlag::Private => current::PrivateFlag::Private,
        pt0::PrivateFlag::Public => current::PrivateFlag::Public,
    }
}

fn map_mutable_flag(flag: pt0::MutableFlag) -> current::MutableFlag {
    match flag {
        pt0::MutableFlag::Immutable => current::MutableFlag::Immutable,
        pt0::MutableFlag::Mutable => current::MutableFlag::Mutable,
    }
}

fn map_override_flag(flag: pt0::OverrideFlag) -> current::OverrideFlag {
    match flag {
        pt0::OverrideFlag::Override => current::OverrideFlag::Override,
        pt0::OverrideFlag::Fresh => current::OverrideFlag::Fresh,
    }
}

fn map_variance(v: pt0::Variance) -> current::Variance {
    match v {
        pt0::Variance::Covariant => current::Variance::Covariant,
        pt0::Variance::Contravariant => current::Variance::Contravariant,
        pt0::Variance::Invariant => current::Variance::Invariant,
    }
}

// ========== Constant conversion ==========

fn map_constant(c: &pt0::Constant) -> current::Constant {
    match c {
        pt0::Constant::Integer(s, suffix) => {
            current::Constant::Integer(Cow::Owned(s.clone()), suffix.clone())
        }
        pt0::Constant::Char(c) => current::Constant::Char(*c),
        pt0::Constant::String(s, delim) => {
            // Reverse the "*j" transformation from mapper_to0:
            // - Some("*j") -> None (regular double-quoted string)
            // - Other delimiters -> keep as is
            let mapped_delim = match delim {
                Some(d) if d == "*j" => None,
                other => other.as_ref().map(|d| Cow::Owned(d.clone())),
            };
            current::Constant::String(Cow::Owned(s.clone()), mapped_delim)
        }
        pt0::Constant::Float(s, suffix) => {
            current::Constant::Float(Cow::Owned(s.clone()), suffix.clone())
        }
    }
}

/// Mapper from parsetree0 to current parsetree.
/// Holds a mutable reference to the arena for creating LocIdx values.
pub struct Mapper<'a> {
    arena: &'a mut ParseArena,
}

impl<'a> Mapper<'a> {
    pub fn new(arena: &'a mut ParseArena) -> Self {
        Self { arena }
    }

    /// Convert a full Location to LocIdx
    fn loc(&mut self, loc: &FullLocation) -> LocIdx {
        self.arena.from_location(loc)
    }

    /// Create a Located value from old Located
    fn map_loc<T: Clone>(&mut self, old: &OldLocated<T>) -> Located<T> {
        Located {
            txt: old.txt.clone(),
            loc: self.loc(&old.loc),
        }
    }

    /// Convert a Located<String> to Located<Cow<'static, str>>
    fn map_label_loc(&mut self, old: &OldLocated<String>) -> Located<Cow<'static, str>> {
        Located {
            txt: Cow::Owned(old.txt.clone()),
            loc: self.loc(&old.loc),
        }
    }

    /// Map a Located<String> to Located<StrIdx> by interning the string.
    /// This is used for attribute names and other StringLoc values.
    fn map_string_loc(&mut self, old: &OldLocated<String>) -> Located<StrIdx> {
        // Use intern() for attribute names so they can be shared
        let str_idx = self.arena.intern(&old.txt);
        Located {
            txt: str_idx,
            loc: self.loc(&old.loc),
        }
    }

    /// Check if a StrIdx matches a string literal
    fn str_eq(&self, idx: StrIdx, s: &str) -> bool {
        self.arena.get_string(idx) == s
    }

    /// Create a Located<StrIdx> with an interned string and location
    fn mk_string_loc(&mut self, s: &str, loc: &FullLocation) -> Located<StrIdx> {
        let str_idx = self.arena.intern(s);
        Located {
            txt: str_idx,
            loc: self.loc(loc),
        }
    }

    /// Create a Located<StrIdx> with an interned string and no location
    fn mk_string_noloc(&mut self, s: &str) -> Located<StrIdx> {
        let str_idx = self.arena.intern(s);
        Located::mknoloc(str_idx)
    }

    /// Map a Located<Longident> to Located<LidentIdx> by pushing to arena
    fn map_longident_loc(
        &mut self,
        old: &OldLocated<Longident>,
    ) -> Located<crate::parse_arena::LidentIdx> {
        let lid_idx = self.arena.push_longident(old.txt.clone());
        Located {
            txt: lid_idx,
            loc: self.loc(&old.loc),
        }
    }

    /// Push a longident to the arena and get back an index
    fn push_longident(&mut self, lid: Longident) -> crate::parse_arena::LidentIdx {
        self.arena.push_longident(lid)
    }

    /// Create a Located value with given text and location
    fn mkloc<T>(&mut self, txt: T, loc: &FullLocation) -> Located<T> {
        Located {
            txt,
            loc: self.loc(loc),
        }
    }

    /// Get a string from a StrIdx
    fn get_str(&self, idx: StrIdx) -> &str {
        self.arena.get_string(idx)
    }

    // ========== Arena push helpers ==========
    // These methods map a pt0 value and push the result into the arena,
    // returning an arena index suitable for the current AST types.

    fn push_expr(&mut self, expr: &pt0::Expression) -> ExprIdx {
        let mapped = self.map_expression(expr);
        self.arena.push_expr(mapped)
    }

    fn push_pat(&mut self, pat: &pt0::Pattern) -> PatIdx {
        let mapped = self.map_pattern(pat);
        self.arena.push_pat(mapped)
    }

    fn push_core_type(&mut self, ct: &pt0::CoreType) -> CoreTypeIdx {
        let mapped = self.map_core_type(ct);
        self.arena.push_core_type(mapped)
    }

    fn push_mod_expr(&mut self, me: &pt0::ModuleExpr) -> ModExprIdx {
        let mapped = self.map_module_expr(me);
        self.arena.push_mod_expr(mapped)
    }

    fn push_mod_type(&mut self, mt: &pt0::ModuleType) -> ModTypeIdx {
        let mapped = self.map_module_type(mt);
        self.arena.push_mod_type(mapped)
    }

    // ========== Public API ==========

    /// Convert a structure from parsetree0 to current parsetree
    pub fn map_structure(&mut self, str: &[pt0::StructureItem]) -> Vec<current::StructureItem> {
        str.iter()
            .map(|item| self.map_structure_item(item))
            .collect()
    }

    /// Convert a signature from parsetree0 to current parsetree
    pub fn map_signature(&mut self, sig: &[pt0::SignatureItem]) -> Vec<current::SignatureItem> {
        sig.iter()
            .map(|item| self.map_signature_item(item))
            .collect()
    }

    // ========== Arg label mapping ==========

    fn map_arg_label(&mut self, lbl: &pt0::ArgLabel) -> current::ArgLabel {
        match lbl {
            pt0::ArgLabel::Nolabel => current::ArgLabel::Nolabel,
            // parsetree0 doesn't have location info, so use mknoloc
            pt0::ArgLabel::Labelled(s) => current::ArgLabel::Labelled(Located::mknoloc(s.clone())),
            pt0::ArgLabel::Optional(s) => current::ArgLabel::Optional(Located::mknoloc(s.clone())),
        }
    }

    // ========== Attribute mapping ==========

    fn map_attribute(&mut self, attr: &pt0::Attribute) -> current::Attribute {
        (self.map_string_loc(&attr.0), self.map_payload(&attr.1))
    }

    fn map_attributes(&mut self, attrs: &[pt0::Attribute]) -> Attributes {
        let v: Vec<current::Attribute> = attrs.iter().map(|a| self.map_attribute(a)).collect();
        v.into()
    }

    fn map_extension(&mut self, ext: &pt0::Extension) -> current::Extension {
        (self.map_string_loc(&ext.0), self.map_payload(&ext.1))
    }

    fn map_payload(&mut self, payload: &pt0::Payload) -> current::Payload {
        match payload {
            pt0::Payload::PStr(str) => current::Payload::PStr(Box::new(self.map_structure(str))),
            pt0::Payload::PSig(sig) => current::Payload::PSig(Box::new(self.map_signature(sig))),
            pt0::Payload::PTyp(t) => current::Payload::PTyp(self.push_core_type(t)),
            pt0::Payload::PPat(p, guard) => current::Payload::PPat(Box::new((
                self.push_pat(p),
                guard.as_ref().map(|g| self.push_expr(g)),
            ))),
        }
    }

    // ========== Core type mapping ==========

    fn map_core_type(&mut self, typ: &pt0::CoreType) -> current::CoreType {
        let loc = self.loc(&typ.ptyp_loc);
        let attrs = self.map_attributes(&typ.ptyp_attributes);

        let desc = match &typ.ptyp_desc {
            pt0::CoreTypeDesc::Any => current::CoreTypeDesc::Ptyp_any,
            pt0::CoreTypeDesc::Var(s) => {
                current::CoreTypeDesc::Ptyp_var(Box::new(Cow::Owned(s.clone())))
            }
            pt0::CoreTypeDesc::Arrow(lbl, t1, t2) => {
                let lbl = self.map_arg_label(lbl);
                let ret_idx = self.push_core_type(t2);
                let typ_idx = self.push_core_type(t1);
                return current::CoreType {
                    ptyp_desc: Box::new(current::CoreTypeDesc::Ptyp_arrow(Box::new((
                        Box::new(current::TypeArg {
                            attrs: attrs,
                            lbl,
                            typ: typ_idx,
                        }),
                        ret_idx,
                        self.arena.push_arity(None),
                    )))),
                    ptyp_loc: loc,
                    ptyp_attributes: Attributes::new(),
                };
            }
            pt0::CoreTypeDesc::Tuple(tl) => current::CoreTypeDesc::Ptyp_tuple(Box::new(
                tl.iter().map(|t| self.push_core_type(t)).collect(),
            )),
            pt0::CoreTypeDesc::Constr(lid, tl) => {
                // First map to CoreType for inspection (function$ detection), then push to arena
                let mapped_types: Vec<current::CoreType> =
                    tl.iter().map(|t| self.map_core_type(t)).collect();

                if let Longident::Lident(name) = &lid.txt {
                    if self.get_str(*name) == "function$" && mapped_types.len() == 2 {
                        if let current::CoreTypeDesc::Ptyp_arrow(ptyp_inner) =
                            &*mapped_types[0].ptyp_desc
                        {
                            let (ref arg, ref ret, _) = **ptyp_inner;
                            if let current::CoreTypeDesc::Ptyp_variant(variant_inner) =
                                &*mapped_types[1].ptyp_desc
                            {
                                let (ref rows, _, _) = **variant_inner;
                                if let Some(row) = rows.first() {
                                    if let current::RowField::Rtag(tag, _, _, _) = row {
                                        if tag.txt.starts_with("Has_arity") {
                                            if let Ok(arity) = tag.txt[9..].parse::<usize>() {
                                                return current::CoreType {
                                                    ptyp_desc: Box::new(
                                                        current::CoreTypeDesc::Ptyp_arrow(
                                                            Box::new((
                                                                arg.clone(),
                                                                ret.clone(),
                                                                self.arena
                                                                    .push_arity(Some(arity as i32)),
                                                            )),
                                                        ),
                                                    ),
                                                    ptyp_loc: loc,
                                                    ptyp_attributes: attrs.into(),
                                                };
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }

                // Convert mapped CoreTypes to CoreTypeIdx for the arena
                let type_indices: Vec<CoreTypeIdx> = mapped_types
                    .into_iter()
                    .map(|t| self.arena.push_core_type(t))
                    .collect();
                current::CoreTypeDesc::Ptyp_constr(Box::new((
                    self.map_longident_loc(lid),
                    type_indices,
                )))
            }
            pt0::CoreTypeDesc::Object(fields, closed) => {
                let fields = fields.iter().map(|f| self.map_object_field(f)).collect();
                current::CoreTypeDesc::Ptyp_object(Box::new((fields, map_closed_flag(closed))))
            }
            pt0::CoreTypeDesc::Alias(t, s) => {
                let ct_idx = self.push_core_type(t);
                current::CoreTypeDesc::Ptyp_alias(Box::new((ct_idx, Cow::Owned(s.clone()))))
            }
            pt0::CoreTypeDesc::Variant(rows, closed, labels) => {
                let rows = rows.iter().map(|r| self.map_row_field(r)).collect();
                current::CoreTypeDesc::Ptyp_variant(Box::new((
                    rows,
                    map_closed_flag(closed),
                    labels
                        .clone()
                        .map(|l| l.iter().map(|s| Cow::Owned(s.clone())).collect()),
                )))
            }
            pt0::CoreTypeDesc::Poly(vars, t) => {
                let ct_idx = self.push_core_type(t);
                current::CoreTypeDesc::Ptyp_poly(Box::new((
                    vars.iter().map(|v| self.map_string_loc(v)).collect(),
                    ct_idx,
                )))
            }
            pt0::CoreTypeDesc::Package(pkg) => {
                let (lid, constraints) = pkg;
                let constraints = constraints
                    .iter()
                    .map(|(l, t)| (self.map_longident_loc(l), self.push_core_type(t)))
                    .collect();
                current::CoreTypeDesc::Ptyp_package(Box::new((
                    self.map_longident_loc(lid),
                    constraints,
                )))
            }
            pt0::CoreTypeDesc::Extension(ext) => {
                current::CoreTypeDesc::Ptyp_extension(Box::new(self.map_extension(ext)))
            }
            pt0::CoreTypeDesc::Class => current::CoreTypeDesc::Ptyp_any,
        };

        current::CoreType {
            ptyp_desc: Box::new(desc),
            ptyp_loc: loc,
            ptyp_attributes: attrs.into(),
        }
    }

    fn map_row_field(&mut self, rf: &pt0::RowField) -> current::RowField {
        match rf {
            pt0::RowField::Rtag(label, attrs, empty, types) => current::RowField::Rtag(
                self.map_label_loc(label),
                self.map_attributes(attrs),
                *empty,
                types.iter().map(|t| self.push_core_type(t)).collect(),
            ),
            pt0::RowField::Rinherit(t) => current::RowField::Rinherit(self.push_core_type(t)),
        }
    }

    fn map_object_field(&mut self, of: &pt0::ObjectField) -> current::ObjectField {
        match of {
            pt0::ObjectField::Otag(label, attrs, t) => current::ObjectField::Otag(
                self.map_string_loc(label),
                self.map_attributes(attrs),
                self.push_core_type(t),
            ),
            pt0::ObjectField::Oinherit(t) => current::ObjectField::Oinherit(self.push_core_type(t)),
        }
    }

    // ========== Pattern mapping ==========

    fn map_pattern(&mut self, pat: &pt0::Pattern) -> current::Pattern {
        let loc = self.loc(&pat.ppat_loc);
        let attrs = self.map_attributes(&pat.ppat_attributes);

        let desc = match &pat.ppat_desc {
            pt0::PatternDesc::Any => current::PatternDesc::Ppat_any,
            pt0::PatternDesc::Var(s) => current::PatternDesc::Ppat_var(self.map_string_loc(s)),
            pt0::PatternDesc::Alias(p, s) => {
                current::PatternDesc::Ppat_alias(self.push_pat(p), self.map_string_loc(s))
            }
            pt0::PatternDesc::Constant(c) => {
                current::PatternDesc::Ppat_constant(Box::new(map_constant(c)))
            }
            pt0::PatternDesc::Interval(c1, c2) => {
                current::PatternDesc::Ppat_interval(Box::new((map_constant(c1), map_constant(c2))))
            }
            pt0::PatternDesc::Tuple(pl) => current::PatternDesc::Ppat_tuple(Box::new(
                pl.iter().map(|p| self.push_pat(p)).collect(),
            )),
            pt0::PatternDesc::Construct(lid, arg) => current::PatternDesc::Ppat_construct(
                self.map_longident_loc(lid),
                arg.as_ref().map(|p| self.push_pat(p)),
            ),
            pt0::PatternDesc::Variant(tag, arg) => current::PatternDesc::Ppat_variant(Box::new((
                Cow::Owned(tag.clone()),
                arg.as_ref().map(|p| self.push_pat(p)),
            ))),
            pt0::PatternDesc::Record(fields, closed) => {
                let fields = fields
                    .iter()
                    .map(|pt0::RecordElement { lid, x: pat, opt }| {
                        let lid = self.map_longident_loc(lid);
                        let mapped_attrs = self.map_attributes(&pat.ppat_attributes);
                        let optional = *opt || has_optional_attribute(self.arena, &mapped_attrs);
                        let mapped_pat = if has_optional_attribute(self.arena, &mapped_attrs) {
                            let mut mapped = self.map_pattern(pat);
                            mapped.ppat_attributes =
                                remove_optional_attribute(self.arena, &mapped.ppat_attributes)
                                    .into();
                            mapped
                        } else {
                            self.map_pattern(pat)
                        };
                        let pat_idx = self.arena.push_pat(mapped_pat);
                        current::PatternRecordField {
                            lid,
                            pat: pat_idx,
                            opt: optional,
                        }
                    })
                    .collect();
                current::PatternDesc::Ppat_record(Box::new((fields, map_closed_flag(closed))))
            }
            pt0::PatternDesc::Array(pl) => current::PatternDesc::Ppat_array(Box::new(
                pl.iter().map(|p| self.push_pat(p)).collect(),
            )),
            pt0::PatternDesc::Or(p1, p2) => {
                current::PatternDesc::Ppat_or(self.push_pat(p1), self.push_pat(p2))
            }
            pt0::PatternDesc::Constraint(p, t) => current::PatternDesc::Ppat_constraint(Box::new(
                (self.push_pat(p), self.push_core_type(t)),
            )),
            pt0::PatternDesc::Type(lid) => {
                current::PatternDesc::Ppat_type(self.map_longident_loc(lid))
            }
            pt0::PatternDesc::Unpack(name) => {
                current::PatternDesc::Ppat_unpack(self.map_string_loc(name))
            }
            pt0::PatternDesc::Open(lid, p) => {
                current::PatternDesc::Ppat_open(self.map_longident_loc(lid), self.push_pat(p))
            }
            pt0::PatternDesc::Exception(p) => {
                current::PatternDesc::Ppat_exception(self.push_pat(p))
            }
            pt0::PatternDesc::Extension(ext) => {
                current::PatternDesc::Ppat_extension(Box::new(self.map_extension(ext)))
            }
            pt0::PatternDesc::Lazy(_) => {
                panic!("OCaml 'lazy' patterns are not supported in ReScript")
            }
        };

        current::Pattern {
            ppat_desc: Box::new(desc),
            ppat_loc: loc,
            ppat_attributes: attrs.into(),
        }
    }

    // ========== Expression mapping ==========

    /// Check if a Longident is a simple identifier with given name
    fn is_lident(&self, lid: &Longident, name: &str) -> bool {
        if let Longident::Lident(s) = lid {
            self.get_str(*s) == name
        } else {
            false
        }
    }

    /// Extracts JSX children from a cons-list expression
    fn extract_jsx_children(&mut self, expr: &pt0::Expression) -> Vec<ExprIdx> {
        let mut children = Vec::new();
        let mut current_expr = expr;
        loop {
            match &current_expr.pexp_desc {
                pt0::ExpressionDesc::Construct(lid, Some(arg))
                    if self.is_lident(&lid.txt, "::") =>
                {
                    if let pt0::ExpressionDesc::Tuple(items) = &arg.pexp_desc {
                        if items.len() == 2 {
                            children.push(self.push_expr(&items[0]));
                            current_expr = &items[1];
                            continue;
                        }
                    }
                    break;
                }
                pt0::ExpressionDesc::Construct(lid, None) if self.is_lident(&lid.txt, "[]") => {
                    break;
                }
                _ => {
                    // If it's not a proper list, just include this as a child
                    children.push(self.push_expr(current_expr));
                    break;
                }
            }
        }
        children
    }

    /// Extract an internal `[@<attr_name>]` loc-carrying attribute from the list,
    /// returning its location (if found) and the attributes with it removed.
    /// Mirrors OCaml `ast_mapper_from0.extract_internal_loc_attr`.
    fn extract_internal_loc_attr(
        &mut self,
        attr_name: &str,
        attrs: &[pt0::Attribute],
    ) -> (Option<FullLocation>, Vec<pt0::Attribute>) {
        let mut found: Option<FullLocation> = None;
        let mut out = Vec::with_capacity(attrs.len());
        for attr in attrs {
            let (name, payload) = attr;
            let is_match = found.is_none()
                && name.txt == attr_name
                && matches!(payload, pt0::Payload::PStr(items) if items.is_empty());
            if is_match {
                found = Some(name.loc.clone());
            } else {
                out.push(attr.clone());
            }
        }
        (found, out)
    }

    /// Tries to extract a JSX prop from a labeled argument
    fn try_map_jsx_prop(
        &mut self,
        label: &pt0::ArgLabel,
        expr: &pt0::Expression,
    ) -> Option<current::JsxProp> {
        const JSX_PROP_LOC_ATTR: &str = "res.jsxPropLoc";
        const JSX_SPREAD_LOC_ATTR: &str = "res.jsxSpreadLoc";

        match label {
            pt0::ArgLabel::Labelled(name_idx) if self.get_str(*name_idx) == "_spreadProps" => {
                let (loc, attrs) =
                    self.extract_internal_loc_attr(JSX_SPREAD_LOC_ATTR, &expr.pexp_attributes);
                let mut stripped = expr.clone();
                stripped.pexp_attributes = attrs;
                let loc = loc.unwrap_or_else(|| expr.pexp_loc.clone());
                Some(current::JsxProp::Spreading {
                    loc: self.loc(&loc),
                    expr: self.push_expr(&stripped),
                })
            }
            pt0::ArgLabel::Labelled(name_idx) => {
                let name_str = self.get_str(*name_idx).to_string();
                // Check for punning: labelled arg with ident of same name
                if let pt0::ExpressionDesc::Ident(lid) = &expr.pexp_desc {
                    if let Longident::Lident(v) = &lid.txt {
                        if self.get_str(*v) == name_str {
                            return Some(current::JsxProp::Punning {
                                optional: false,
                                name: self.mk_string_loc(&name_str, &lid.loc),
                            });
                        }
                    }
                }
                let (loc, attrs) =
                    self.extract_internal_loc_attr(JSX_PROP_LOC_ATTR, &expr.pexp_attributes);
                let mut stripped = expr.clone();
                stripped.pexp_attributes = attrs;
                let loc = loc.unwrap_or_else(|| expr.pexp_loc.clone());
                Some(current::JsxProp::Value {
                    name: self.mk_string_loc(&name_str, &loc),
                    optional: false,
                    value: self.push_expr(&stripped),
                })
            }
            pt0::ArgLabel::Optional(name_idx) => {
                let name_str = self.get_str(*name_idx).to_string();
                // Check for punning: optional arg with ident of same name
                if let pt0::ExpressionDesc::Ident(lid) = &expr.pexp_desc {
                    if let Longident::Lident(v) = &lid.txt {
                        if self.get_str(*v) == name_str {
                            return Some(current::JsxProp::Punning {
                                optional: true,
                                name: self.mk_string_loc(&name_str, &lid.loc),
                            });
                        }
                    }
                }
                let (loc, attrs) =
                    self.extract_internal_loc_attr(JSX_PROP_LOC_ATTR, &expr.pexp_attributes);
                let mut stripped = expr.clone();
                stripped.pexp_attributes = attrs;
                let loc = loc.unwrap_or_else(|| expr.pexp_loc.clone());
                Some(current::JsxProp::Value {
                    name: self.mk_string_loc(&name_str, &loc),
                    optional: true,
                    value: self.push_expr(&stripped),
                })
            }
            pt0::ArgLabel::Nolabel => None,
        }
    }

    /// Extracts props and children from JSX apply arguments
    fn extract_jsx_props_and_children(
        &mut self,
        args: &[(pt0::ArgLabel, pt0::Expression)],
    ) -> (Vec<current::JsxProp>, Vec<ExprIdx>) {
        let mut props = Vec::new();
        let mut children = Vec::new();

        for (label, expr) in args {
            match label {
                pt0::ArgLabel::Labelled(name_idx) if self.get_str(*name_idx) == "children" => {
                    children = self.extract_jsx_children(expr);
                }
                pt0::ArgLabel::Nolabel => {
                    // Unit argument at the end, skip
                }
                _ => {
                    if let Some(prop) = self.try_map_jsx_prop(label, expr) {
                        props.push(prop);
                    }
                }
            }
        }

        (props, children)
    }

    /// Helper to check if a string starts with lowercase
    fn starts_with_lowercase(&self, idx: StrIdx) -> bool {
        let s = self.get_str(idx);
        !s.is_empty() && s.chars().next().unwrap().is_lowercase()
    }

    /// Converts a longident to a JSX tag name
    fn longident_to_jsx_tag(&mut self, lid: &Longident) -> current::JsxTagName {
        match lid {
            Longident::Lident(s) if self.starts_with_lowercase(*s) => {
                current::JsxTagName::Lower(self.get_str(*s).to_string())
            }
            Longident::Lident(s) => {
                let lid_idx = self.push_longident(Longident::Lident(*s));
                current::JsxTagName::Upper(lid_idx)
            }
            Longident::Ldot(path, name) if self.starts_with_lowercase(*name) => {
                let path_idx = self.push_longident((**path).clone());
                current::JsxTagName::QualifiedLower {
                    path: path_idx,
                    name: self.get_str(*name).to_string(),
                }
            }
            other => {
                let lid_idx = self.push_longident(other.clone());
                current::JsxTagName::Upper(lid_idx)
            }
        }
    }

    fn map_expression(&mut self, expr: &pt0::Expression) -> current::Expression {
        let loc = self.loc(&expr.pexp_loc);
        // Strip the `_res.for_of` / `_res.for_await_of` attributes — they
        // exist purely as carrier of the iterable in the legacy parsetree0
        // encoding (see `ast_mapper_from0.ml` after #7887). The for-of /
        // for-await-of variant is reconstructed below via
        // `extract_for_*_iterable` on the original (unfiltered) attrs.
        let mut attrs = if has_for_of_attribute(&expr.pexp_attributes) {
            self.map_attributes(&remove_for_of_attributes(&expr.pexp_attributes))
        } else {
            self.map_attributes(&expr.pexp_attributes)
        };

        // Check for res.await attribute - convert to Pexp_await
        if has_await_attribute(&expr.pexp_attributes) {
            let new_attrs = remove_await_attribute(&expr.pexp_attributes);
            let inner_expr = pt0::Expression {
                pexp_desc: expr.pexp_desc.clone(),
                pexp_loc: expr.pexp_loc.clone(),
                pexp_attributes: new_attrs,
            };
            let await_idx = self.push_expr(&inner_expr);
            return current::Expression {
                pexp_desc: Box::new(current::ExpressionDesc::Pexp_await(await_idx)),
                pexp_loc: loc,
                pexp_attributes: Attributes::new(),
            };
        }

        let desc = match &expr.pexp_desc {
            pt0::ExpressionDesc::Ident(lid) => {
                current::ExpressionDesc::Pexp_ident(self.map_longident_loc(lid))
            }
            pt0::ExpressionDesc::Constant(c) => {
                current::ExpressionDesc::Pexp_constant(Box::new(map_constant(c)))
            }
            pt0::ExpressionDesc::Let(rec_flag, bindings, body) => {
                let body_idx = self.push_expr(body);
                current::ExpressionDesc::Pexp_let(Box::new((
                    map_rec_flag(*rec_flag),
                    bindings
                        .iter()
                        .map(|vb| self.map_value_binding(vb))
                        .collect(),
                    body_idx,
                )))
            }
            pt0::ExpressionDesc::Fun {
                arg_label: lbl,
                default,
                lhs: pat,
                rhs: body,
                arity,
                is_async,
            } => {
                let has_async_attr = has_async_attribute(self.arena, &attrs);
                let is_async = *is_async || has_async_attr;
                if is_async && !has_async_attr {
                    attrs.insert(
                        0,
                        (
                            self.mk_string_noloc("res.async"),
                            current::Payload::PStr(Box::new(vec![])),
                        ),
                    );
                }
                let default_idx = default.as_ref().map(|e| self.push_expr(e));
                let rhs_idx = self.push_expr(body);
                current::ExpressionDesc::Pexp_fun(Box::new(PexpFun {
                    arg_label: self.map_arg_label(lbl),
                    default: default_idx,
                    lhs: self.push_pat(pat),
                    rhs: rhs_idx,
                    arity: map_arity(arity, self.arena),
                    is_async,
                }))
            }
            pt0::ExpressionDesc::Apply {
                funct: func,
                args,
                partial: pt0_partial,
                transformed_jsx,
            } => {
                // Check for JSX attribute - convert back to JSX element
                if has_jsx_attribute(&expr.pexp_attributes) {
                    if let pt0::ExpressionDesc::Ident(tag_lid) = &func.pexp_desc {
                        let jsx_attrs =
                            self.map_attributes(&remove_jsx_attribute(&expr.pexp_attributes));
                        let (props, children) = self.extract_jsx_props_and_children(args);
                        let tag_name = self.longident_to_jsx_tag(&tag_lid.txt);
                        let tag_loc = Located::new(tag_name, self.loc(&tag_lid.loc));

                        // Get position indices for JSX element structure
                        let loc_start_idx = self.arena.loc_start_idx(loc);
                        let loc_end_idx = self.arena.loc_end_idx(loc);

                        let jsx_element = if children.is_empty() {
                            current::JsxElement::Unary(current::JsxUnaryElement {
                                tag_name: tag_loc,
                                props,
                            })
                        } else {
                            current::JsxElement::Container(current::JsxContainerElement {
                                tag_name_start: tag_loc.clone(),
                                opening_end: loc_start_idx,
                                props,
                                children,
                                closing_tag: Some(current::JsxClosingTag {
                                    start: loc_end_idx,
                                    name: tag_loc,
                                    end: loc_end_idx,
                                }),
                            })
                        };

                        return current::Expression {
                            pexp_desc: Box::new(current::ExpressionDesc::Pexp_jsx_element(
                                Box::new(jsx_element),
                            )),
                            pexp_loc: loc,
                            pexp_attributes: jsx_attrs.into(),
                        };
                    }
                }

                // Check for partial application attribute (legacy) or use pt0_partial
                let partial = *pt0_partial || has_partial_attribute(&expr.pexp_attributes);
                let attrs = if has_partial_attribute(&expr.pexp_attributes) {
                    self.map_attributes(&remove_partial_attribute(&expr.pexp_attributes))
                } else {
                    attrs.clone()
                };

                // Map operator names
                let func = if let pt0::ExpressionDesc::Ident(lid) = &func.pexp_desc {
                    match &lid.txt {
                        Longident::Lident(name) => {
                            let name_str = self.get_str(*name);
                            let new_name = match name_str {
                                "|." => Some("->"),
                                "^" => Some("++"),
                                "<>" => Some("!="),
                                "!=" => Some("!=="),
                                "=" => Some("=="),
                                "==" => Some("==="),
                                _ => None,
                            };
                            if let Some(new_name) = new_name {
                                let new_str_idx = self.arena.intern_string(new_name);
                                pt0::Expression {
                                    pexp_desc: pt0::ExpressionDesc::Ident(OldLocated {
                                        txt: Longident::Lident(new_str_idx),
                                        loc: lid.loc.clone(),
                                    }),
                                    pexp_loc: func.pexp_loc.clone(),
                                    pexp_attributes: func.pexp_attributes.clone(),
                                }
                            } else {
                                func.as_ref().clone()
                            }
                        }
                        _ => func.as_ref().clone(),
                    }
                } else {
                    func.as_ref().clone()
                };

                let funct_idx = {
                    let mapped = self.map_expression(&func);
                    self.arena.push_expr(mapped)
                };
                return current::Expression {
                    pexp_desc: Box::new(current::ExpressionDesc::Pexp_apply(Box::new(PexpApply {
                        funct: funct_idx,
                        args: args
                            .iter()
                            .map(|(lbl, e)| (self.map_arg_label(lbl), self.push_expr(e)))
                            .collect(),
                        partial,
                        transformed_jsx: *transformed_jsx,
                    }))),
                    pexp_loc: loc,
                    pexp_attributes: attrs.into(),
                };
            }
            pt0::ExpressionDesc::Match(e, cases) => {
                let e_idx = self.push_expr(e);
                current::ExpressionDesc::Pexp_match(Box::new((
                    e_idx,
                    cases.iter().map(|c| self.map_case(c)).collect(),
                )))
            }
            pt0::ExpressionDesc::Try(e, cases) => {
                let e_idx = self.push_expr(e);
                current::ExpressionDesc::Pexp_try(Box::new((
                    e_idx,
                    cases.iter().map(|c| self.map_case(c)).collect(),
                )))
            }
            pt0::ExpressionDesc::Tuple(el) => current::ExpressionDesc::Pexp_tuple(Box::new(
                el.iter().map(|e| self.push_expr(e)).collect(),
            )),
            pt0::ExpressionDesc::Construct(lid, arg) => {
                // Check for JSX fragment (list with [@JSX] attribute)
                if has_jsx_attribute(&expr.pexp_attributes) {
                    if let Longident::Lident(name) = &lid.txt {
                        let name_str = self.get_str(*name);
                        if name_str == "[]" || name_str == "::" {
                            let jsx_attrs =
                                self.map_attributes(&remove_jsx_attribute(&expr.pexp_attributes));
                            let children = self.extract_jsx_children(expr);
                            let loc_start_idx = self.arena.loc_start_idx(loc);
                            let loc_end_idx = self.arena.loc_end_idx(loc);
                            let jsx_element = current::JsxElement::Fragment(current::JsxFragment {
                                opening: loc_start_idx,
                                children,
                                closing: loc_end_idx,
                            });
                            return current::Expression {
                                pexp_desc: Box::new(current::ExpressionDesc::Pexp_jsx_element(
                                    Box::new(jsx_element),
                                )),
                                pexp_loc: loc,
                                pexp_attributes: jsx_attrs.into(),
                            };
                        }
                    }
                }

                // Check for Function$ wrapper (arity encoding)
                if let Longident::Lident(name) = &lid.txt {
                    if self.get_str(*name) == "Function$" {
                        if let Some(inner) = arg {
                            let mapped = self.map_expression(inner);
                            if let current::ExpressionDesc::Pexp_fun(fun_inner) = *mapped.pexp_desc
                            {
                                let PexpFun {
                                    arg_label,
                                    default,
                                    lhs,
                                    rhs,
                                    is_async,
                                    ..
                                } = *fun_inner;
                                // Extract arity from attributes
                                let arity_opt = get_arity_from_attributes(self.arena, &attrs);
                                let arity = self.arena.push_arity(arity_opt);
                                let new_attrs = remove_arity_attribute(self.arena, &attrs);
                                return current::Expression {
                                    pexp_desc: Box::new(current::ExpressionDesc::Pexp_fun(
                                        Box::new(PexpFun {
                                            arg_label,
                                            default,
                                            lhs,
                                            rhs,
                                            arity,
                                            is_async,
                                        }),
                                    )),
                                    pexp_loc: loc,
                                    pexp_attributes: new_attrs.into(),
                                };
                            }
                        }
                    }
                }
                current::ExpressionDesc::Pexp_construct(
                    self.map_longident_loc(lid),
                    arg.as_ref().map(|e| self.push_expr(e)),
                )
            }
            pt0::ExpressionDesc::Variant(label, arg) => {
                current::ExpressionDesc::Pexp_variant(Box::new((
                    Cow::Owned(label.clone()),
                    arg.as_ref().map(|e| self.push_expr(e)),
                )))
            }
            pt0::ExpressionDesc::Record(fields, base) => {
                let fields = fields
                    .iter()
                    .map(|pt0::RecordElement { lid, x: e, opt }| {
                        let mapped_expr = self.map_expression(e);
                        // Preserve opt from parsetree0 if present, or check for optional attribute
                        let optional = *opt
                            || has_optional_attribute(self.arena, &mapped_expr.pexp_attributes);
                        let expr_attrs =
                            if has_optional_attribute(self.arena, &mapped_expr.pexp_attributes) {
                                remove_optional_attribute(self.arena, &mapped_expr.pexp_attributes)
                            } else {
                                mapped_expr.pexp_attributes.clone()
                            };
                        current::ExpressionRecordField {
                            lid: self.map_longident_loc(lid),
                            expr: self.arena.push_expr(current::Expression {
                                pexp_desc: mapped_expr.pexp_desc,
                                pexp_loc: mapped_expr.pexp_loc,
                                pexp_attributes: expr_attrs,
                            }),
                            opt: optional,
                        }
                    })
                    .collect();
                current::ExpressionDesc::Pexp_record(Box::new((
                    fields,
                    base.as_ref().map(|e| self.push_expr(e)),
                )))
            }
            pt0::ExpressionDesc::Field(e, lid) => {
                let e_idx = self.push_expr(e);
                current::ExpressionDesc::Pexp_field(e_idx, self.map_longident_loc(lid))
            }
            pt0::ExpressionDesc::Setfield(e1, lid, e2) => {
                let e1_idx = self.push_expr(e1);
                let e2_idx = self.push_expr(e2);
                current::ExpressionDesc::Pexp_setfield(Box::new((
                    e1_idx,
                    self.map_longident_loc(lid),
                    e2_idx,
                )))
            }
            pt0::ExpressionDesc::Array(el) => current::ExpressionDesc::Pexp_array(Box::new(
                el.iter().map(|e| self.push_expr(e)).collect(),
            )),
            pt0::ExpressionDesc::Ifthenelse(e1, e2, e3) => {
                let e1_idx = self.push_expr(e1);
                let e2_idx = self.push_expr(e2);
                let e3_idx = e3.as_ref().map(|e| self.push_expr(e));
                current::ExpressionDesc::Pexp_ifthenelse(Box::new((e1_idx, e2_idx, e3_idx)))
            }
            pt0::ExpressionDesc::Sequence(e1, e2) => {
                let e1_idx = self.push_expr(e1);
                let e2_idx = self.push_expr(e2);
                current::ExpressionDesc::Pexp_sequence(e1_idx, e2_idx)
            }
            pt0::ExpressionDesc::While(e1, e2) => {
                let e1_idx = self.push_expr(e1);
                let e2_idx = self.push_expr(e2);
                current::ExpressionDesc::Pexp_while(e1_idx, e2_idx)
            }
            pt0::ExpressionDesc::For(pat, e1, e2, dir, e3) => {
                // Upstream #7887: a for-loop carrying `_res.for_of` /
                // `_res.for_await_of` attributes is actually a `for ... of`
                // / `for await ... of` loop in disguise — recover the proper
                // variant. Mirrors `compiler/ml/ast_mapper_from0.ml`.
                if let Some(iterable_expr) = extract_for_await_of_iterable(&expr.pexp_attributes) {
                    let pat_idx = self.push_pat(pat);
                    let it_idx = self.push_expr(iterable_expr);
                    let body_idx = self.push_expr(e3);
                    current::ExpressionDesc::Pexp_for_await_of(Box::new((
                        pat_idx, it_idx, body_idx,
                    )))
                } else if let Some(iterable_expr) = extract_for_of_iterable(&expr.pexp_attributes) {
                    let pat_idx = self.push_pat(pat);
                    let it_idx = self.push_expr(iterable_expr);
                    let body_idx = self.push_expr(e3);
                    current::ExpressionDesc::Pexp_for_of(Box::new((pat_idx, it_idx, body_idx)))
                } else {
                    let e1_idx = self.push_expr(e1);
                    let e2_idx = self.push_expr(e2);
                    let e3_idx = self.push_expr(e3);
                    current::ExpressionDesc::Pexp_for(Box::new((
                        self.push_pat(pat),
                        e1_idx,
                        e2_idx,
                        map_direction_flag(*dir),
                        e3_idx,
                    )))
                }
            }
            pt0::ExpressionDesc::Coerce(e, _, t) => {
                let e_idx = self.push_expr(e);
                current::ExpressionDesc::Pexp_coerce(Box::new((
                    e_idx,
                    None,
                    self.push_core_type(t),
                )))
            }
            pt0::ExpressionDesc::Constraint(e, t) => {
                let e_idx = self.push_expr(e);
                current::ExpressionDesc::Pexp_constraint(Box::new((e_idx, self.push_core_type(t))))
            }
            pt0::ExpressionDesc::Send(e, method) => {
                let e_idx = self.push_expr(e);
                current::ExpressionDesc::Pexp_send(Box::new((e_idx, self.map_label_loc(method))))
            }
            pt0::ExpressionDesc::Letmodule(name, me, body) => {
                let body_idx = self.push_expr(body);
                current::ExpressionDesc::Pexp_letmodule(Box::new((
                    self.map_string_loc(name),
                    self.push_mod_expr(me),
                    body_idx,
                )))
            }
            pt0::ExpressionDesc::Letexception(ec, body) => {
                let body_idx = self.push_expr(body);
                current::ExpressionDesc::Pexp_letexception(Box::new((
                    self.map_extension_constructor(ec),
                    body_idx,
                )))
            }
            pt0::ExpressionDesc::Assert(e) => {
                let e_idx = self.push_expr(e);
                current::ExpressionDesc::Pexp_assert(e_idx)
            }
            pt0::ExpressionDesc::Newtype(name, body) => {
                let body_idx = self.push_expr(body);
                current::ExpressionDesc::Pexp_newtype(Box::new((
                    self.map_string_loc(name),
                    body_idx,
                )))
            }
            pt0::ExpressionDesc::Pack(me) => {
                let me_idx = self.push_mod_expr(me);
                current::ExpressionDesc::Pexp_pack(me_idx)
            }
            pt0::ExpressionDesc::Open(ovf, lid, body) => {
                let body_idx = self.push_expr(body);
                current::ExpressionDesc::Pexp_open(Box::new((
                    map_override_flag(*ovf),
                    self.map_longident_loc(lid),
                    body_idx,
                )))
            }
            pt0::ExpressionDesc::Extension(ext) => {
                current::ExpressionDesc::Pexp_extension(Box::new(self.map_extension(ext)))
            }
            // OCaml-specific expressions that don't exist in ReScript
            pt0::ExpressionDesc::New(_) => {
                panic!("OCaml 'new' expressions are not supported in ReScript")
            }
            pt0::ExpressionDesc::Setinstvar(_, _) => {
                panic!("OCaml 'setinstvar' expressions are not supported in ReScript")
            }
            pt0::ExpressionDesc::Override(_) => {
                panic!("OCaml 'override' expressions are not supported in ReScript")
            }
            pt0::ExpressionDesc::Lazy(_) => {
                panic!("OCaml 'lazy' expressions are not supported in ReScript")
            }
            pt0::ExpressionDesc::Poly(_, _) => {
                panic!("OCaml 'poly' expressions are not supported in ReScript")
            }
            pt0::ExpressionDesc::Object => {
                panic!("OCaml 'object' expressions are not supported in ReScript")
            }
            pt0::ExpressionDesc::Unreachable => {
                // Unreachable is represented by a `.` pattern
                // Map to an extension point that represents unreachable
                current::ExpressionDesc::Pexp_extension(Box::new((
                    self.mk_string_loc("rescript.exprhole", &expr.pexp_loc),
                    current::Payload::PStr(Box::new(vec![])),
                )))
            }
        };

        current::Expression {
            pexp_desc: Box::new(desc),
            pexp_loc: loc,
            pexp_attributes: attrs.into(),
        }
    }

    fn map_case(&mut self, c: &pt0::Case) -> current::Case {
        current::Case {
            pc_bar: None,
            pc_lhs: self.push_pat(&c.pc_lhs),
            pc_guard: c.pc_guard.as_ref().map(|g| self.push_expr(g)),
            pc_rhs: self.push_expr(&c.pc_rhs),
        }
    }

    fn map_value_binding(&mut self, vb: &pt0::ValueBinding) -> current::ValueBinding {
        current::ValueBinding {
            pvb_pat: self.push_pat(&vb.pvb_pat),
            pvb_expr: self.push_expr(&vb.pvb_expr),
            pvb_attributes: self.map_attributes(&vb.pvb_attributes).into(),
            pvb_loc: self.loc(&vb.pvb_loc),
        }
    }

    // ========== Module expressions ==========

    fn map_module_expr(&mut self, me: &pt0::ModuleExpr) -> current::ModuleExpr {
        let loc = self.loc(&me.pmod_loc);
        let attrs = self.map_attributes(&me.pmod_attributes);

        let desc = match &me.pmod_desc {
            pt0::ModuleExprDesc::Ident(lid) => {
                current::ModuleExprDesc::Pmod_ident(self.map_longident_loc(lid))
            }
            pt0::ModuleExprDesc::Structure(str) => {
                current::ModuleExprDesc::Pmod_structure(Box::new(self.map_structure(str)))
            }
            pt0::ModuleExprDesc::Functor(name, mt, body) => {
                let mt_idx = mt.as_ref().map(|mt| self.push_mod_type(mt));
                let body_idx = self.push_mod_expr(body);
                current::ModuleExprDesc::Pmod_functor(Box::new((
                    self.map_string_loc(name),
                    mt_idx,
                    body_idx,
                )))
            }
            pt0::ModuleExprDesc::Apply(m1, m2) => {
                let m1_idx = self.push_mod_expr(m1);
                let m2_idx = self.push_mod_expr(m2);
                current::ModuleExprDesc::Pmod_apply(m1_idx, m2_idx)
            }
            pt0::ModuleExprDesc::Constraint(m, mt) => {
                let m_idx = self.push_mod_expr(m);
                let mt_idx = self.push_mod_type(mt);
                current::ModuleExprDesc::Pmod_constraint(m_idx, mt_idx)
            }
            pt0::ModuleExprDesc::Unpack(e) => {
                let e_idx = self.push_expr(e);
                current::ModuleExprDesc::Pmod_unpack(e_idx)
            }
            pt0::ModuleExprDesc::Extension(ext) => {
                current::ModuleExprDesc::Pmod_extension(Box::new(self.map_extension(ext)))
            }
        };

        current::ModuleExpr {
            pmod_desc: Box::new(desc),
            pmod_loc: loc,
            pmod_attributes: attrs.into(),
        }
    }

    // ========== Module types ==========

    fn map_module_type(&mut self, mt: &pt0::ModuleType) -> current::ModuleType {
        let loc = self.loc(&mt.pmty_loc);
        let attrs = self.map_attributes(&mt.pmty_attributes);

        let desc = match &mt.pmty_desc {
            pt0::ModuleTypeDesc::Ident(lid) => {
                current::ModuleTypeDesc::Pmty_ident(self.map_longident_loc(lid))
            }
            pt0::ModuleTypeDesc::Alias(lid) => {
                current::ModuleTypeDesc::Pmty_alias(self.map_longident_loc(lid))
            }
            pt0::ModuleTypeDesc::Signature(sig) => {
                current::ModuleTypeDesc::Pmty_signature(Box::new(self.map_signature(sig)))
            }
            pt0::ModuleTypeDesc::Functor(name, mt1, mt2) => {
                let mt1_idx = mt1.as_ref().map(|m| self.push_mod_type(m));
                let mt2_idx = self.push_mod_type(mt2);
                current::ModuleTypeDesc::Pmty_functor(Box::new((
                    self.map_string_loc(name),
                    mt1_idx,
                    mt2_idx,
                )))
            }
            pt0::ModuleTypeDesc::With(mt, constraints) => {
                let mt_idx = self.push_mod_type(mt);
                current::ModuleTypeDesc::Pmty_with(Box::new((
                    mt_idx,
                    constraints
                        .iter()
                        .map(|wc| self.map_with_constraint(wc))
                        .collect(),
                )))
            }
            pt0::ModuleTypeDesc::Typeof(me) => {
                let me_idx = self.push_mod_expr(me);
                current::ModuleTypeDesc::Pmty_typeof(me_idx)
            }
            pt0::ModuleTypeDesc::Extension(ext) => {
                current::ModuleTypeDesc::Pmty_extension(Box::new(self.map_extension(ext)))
            }
        };

        current::ModuleType {
            pmty_desc: Box::new(desc),
            pmty_loc: loc,
            pmty_attributes: attrs.into(),
        }
    }

    fn map_with_constraint(&mut self, wc: &pt0::WithConstraint) -> current::WithConstraint {
        match wc {
            pt0::WithConstraint::Type(lid, td) => current::WithConstraint::Pwith_type(
                self.map_longident_loc(lid),
                self.map_type_declaration(td),
            ),
            pt0::WithConstraint::Module(lid1, lid2) => current::WithConstraint::Pwith_module(
                self.map_longident_loc(lid1),
                self.map_longident_loc(lid2),
            ),
            pt0::WithConstraint::TypeSubst(lid, td) => current::WithConstraint::Pwith_typesubst(
                self.map_longident_loc(lid),
                self.map_type_declaration(td),
            ),
            pt0::WithConstraint::ModSubst(lid1, lid2) => current::WithConstraint::Pwith_modsubst(
                self.map_longident_loc(lid1),
                self.map_longident_loc(lid2),
            ),
        }
    }

    // ========== Structure items ==========

    fn map_structure_item(&mut self, item: &pt0::StructureItem) -> current::StructureItem {
        let loc = self.loc(&item.pstr_loc);

        let desc = match &item.pstr_desc {
            pt0::StructureItemDesc::Eval(e, attrs) => current::StructureItemDesc::Pstr_eval(
                Box::new((self.push_expr(e), self.map_attributes(attrs))),
            ),
            pt0::StructureItemDesc::Value(rec_flag, bindings) => {
                current::StructureItemDesc::Pstr_value(Box::new((
                    map_rec_flag(*rec_flag),
                    bindings
                        .iter()
                        .map(|vb| self.map_value_binding(vb))
                        .collect(),
                )))
            }
            pt0::StructureItemDesc::Primitive(vd) => {
                current::StructureItemDesc::Pstr_primitive(Box::new(self.map_value_description(vd)))
            }
            pt0::StructureItemDesc::Type(rec_flag, decls) => {
                current::StructureItemDesc::Pstr_type(Box::new((
                    map_rec_flag(*rec_flag),
                    decls
                        .iter()
                        .map(|td| self.map_type_declaration(td))
                        .collect(),
                )))
            }
            pt0::StructureItemDesc::Typext(te) => {
                current::StructureItemDesc::Pstr_typext(Box::new(self.map_type_extension(te)))
            }
            pt0::StructureItemDesc::Exception(ec) => current::StructureItemDesc::Pstr_exception(
                Box::new(self.map_extension_constructor(ec)),
            ),
            pt0::StructureItemDesc::Module(mb) => {
                current::StructureItemDesc::Pstr_module(Box::new(self.map_module_binding(mb)))
            }
            pt0::StructureItemDesc::Recmodule(mbs) => current::StructureItemDesc::Pstr_recmodule(
                Box::new(mbs.iter().map(|mb| self.map_module_binding(mb)).collect()),
            ),
            pt0::StructureItemDesc::Modtype(mtd) => current::StructureItemDesc::Pstr_modtype(
                Box::new(self.map_module_type_declaration(mtd)),
            ),
            pt0::StructureItemDesc::Open(od) => {
                current::StructureItemDesc::Pstr_open(Box::new(self.map_open_description(od)))
            }
            pt0::StructureItemDesc::Include(id) => {
                current::StructureItemDesc::Pstr_include(Box::new(self.map_include_declaration(id)))
            }
            pt0::StructureItemDesc::Extension(ext, attrs) => {
                current::StructureItemDesc::Pstr_extension(Box::new((
                    self.map_extension(ext),
                    self.map_attributes(attrs),
                )))
            }
            pt0::StructureItemDesc::Attribute(attr) => {
                current::StructureItemDesc::Pstr_attribute(Box::new(self.map_attribute(attr)))
            }
            pt0::StructureItemDesc::Class => {
                panic!("OCaml 'class' definitions are not supported in ReScript")
            }
            pt0::StructureItemDesc::ClassType => {
                panic!("OCaml 'class type' definitions are not supported in ReScript")
            }
        };

        current::StructureItem {
            pstr_desc: Box::new(desc),
            pstr_loc: loc,
        }
    }

    // ========== Signature items ==========

    fn map_signature_item(&mut self, item: &pt0::SignatureItem) -> current::SignatureItem {
        let loc = self.loc(&item.psig_loc);

        let desc = match &item.psig_desc {
            pt0::SignatureItemDesc::Value(vd) => {
                current::SignatureItemDesc::Psig_value(Box::new(self.map_value_description(vd)))
            }
            pt0::SignatureItemDesc::Type(rec_flag, decls) => {
                current::SignatureItemDesc::Psig_type(Box::new((
                    map_rec_flag(*rec_flag),
                    decls
                        .iter()
                        .map(|td| self.map_type_declaration(td))
                        .collect(),
                )))
            }
            pt0::SignatureItemDesc::Typext(te) => {
                current::SignatureItemDesc::Psig_typext(Box::new(self.map_type_extension(te)))
            }
            pt0::SignatureItemDesc::Exception(ec) => current::SignatureItemDesc::Psig_exception(
                Box::new(self.map_extension_constructor(ec)),
            ),
            pt0::SignatureItemDesc::Module(md) => {
                current::SignatureItemDesc::Psig_module(Box::new(self.map_module_declaration(md)))
            }
            pt0::SignatureItemDesc::Recmodule(mds) => {
                current::SignatureItemDesc::Psig_recmodule(Box::new(
                    mds.iter()
                        .map(|md| self.map_module_declaration(md))
                        .collect(),
                ))
            }
            pt0::SignatureItemDesc::Modtype(mtd) => current::SignatureItemDesc::Psig_modtype(
                Box::new(self.map_module_type_declaration(mtd)),
            ),
            pt0::SignatureItemDesc::Open(od) => {
                current::SignatureItemDesc::Psig_open(Box::new(self.map_open_description(od)))
            }
            pt0::SignatureItemDesc::Include(id) => {
                current::SignatureItemDesc::Psig_include(Box::new(self.map_include_description(id)))
            }
            pt0::SignatureItemDesc::Extension(ext, attrs) => {
                current::SignatureItemDesc::Psig_extension(Box::new((
                    self.map_extension(ext),
                    self.map_attributes(attrs),
                )))
            }
            pt0::SignatureItemDesc::Attribute(attr) => {
                current::SignatureItemDesc::Psig_attribute(Box::new(self.map_attribute(attr)))
            }
            pt0::SignatureItemDesc::Class => {
                panic!("OCaml 'class' declarations are not supported in ReScript")
            }
            pt0::SignatureItemDesc::ClassType => {
                panic!("OCaml 'class type' declarations are not supported in ReScript")
            }
        };

        current::SignatureItem {
            psig_desc: Box::new(desc),
            psig_loc: loc,
        }
    }

    // ========== Type declarations ==========

    fn map_type_declaration(&mut self, td: &pt0::TypeDeclaration) -> current::TypeDeclaration {
        current::TypeDeclaration {
            ptype_name: self.map_string_loc(&td.ptype_name),
            ptype_params: td
                .ptype_params
                .iter()
                .map(|(t, v)| (self.push_core_type(t), map_variance(*v)))
                .collect(),
            ptype_cstrs: td
                .ptype_cstrs
                .iter()
                .map(|(t1, t2, loc)| {
                    (
                        self.push_core_type(t1),
                        self.push_core_type(t2),
                        self.loc(loc),
                    )
                })
                .collect(),
            ptype_kind: self.map_type_kind(&td.ptype_kind),
            ptype_private: map_private_flag(td.ptype_private),
            ptype_manifest: td.ptype_manifest.as_ref().map(|t| self.push_core_type(t)),
            ptype_attributes: self.map_attributes(&td.ptype_attributes).into(),
            ptype_loc: self.loc(&td.ptype_loc),
        }
    }

    fn map_type_kind(&mut self, tk: &pt0::TypeKind) -> current::TypeKind {
        match tk {
            pt0::TypeKind::Abstract => current::TypeKind::Ptype_abstract,
            pt0::TypeKind::Variant(cds) => current::TypeKind::Ptype_variant(
                cds.iter()
                    .map(|cd| self.map_constructor_declaration(cd))
                    .collect(),
            ),
            pt0::TypeKind::Record(lds) => current::TypeKind::Ptype_record(
                lds.iter()
                    .map(|ld| self.map_label_declaration(ld))
                    .collect(),
            ),
            pt0::TypeKind::Open => current::TypeKind::Ptype_open,
        }
    }

    fn map_constructor_declaration(
        &mut self,
        cd: &pt0::ConstructorDeclaration,
    ) -> current::ConstructorDeclaration {
        current::ConstructorDeclaration {
            pcd_name: self.map_string_loc(&cd.pcd_name),
            pcd_args: self.map_constructor_arguments(&cd.pcd_args),
            pcd_res: cd.pcd_res.as_ref().map(|t| self.push_core_type(t)),
            pcd_loc: self.loc(&cd.pcd_loc),
            pcd_attributes: self.map_attributes(&cd.pcd_attributes).into(),
        }
    }

    fn map_constructor_arguments(
        &mut self,
        ca: &pt0::ConstructorArguments,
    ) -> current::ConstructorArguments {
        match ca {
            pt0::ConstructorArguments::Tuple(tl) => current::ConstructorArguments::Pcstr_tuple(
                tl.iter().map(|t| self.push_core_type(t)).collect(),
            ),
            pt0::ConstructorArguments::Record(lds) => current::ConstructorArguments::Pcstr_record(
                lds.iter()
                    .map(|ld| self.map_label_declaration(ld))
                    .collect(),
            ),
        }
    }

    fn map_label_declaration(&mut self, ld: &pt0::LabelDeclaration) -> current::LabelDeclaration {
        let attrs = self.map_attributes(&ld.pld_attributes);
        let optional = has_optional_attribute(self.arena, &attrs);
        let final_attrs = if optional {
            remove_optional_attribute(self.arena, &attrs)
        } else {
            attrs
        };

        current::LabelDeclaration {
            pld_name: self.map_string_loc(&ld.pld_name),
            pld_mutable: map_mutable_flag(ld.pld_mutable),
            pld_type: self.push_core_type(&ld.pld_type),
            pld_loc: self.loc(&ld.pld_loc),
            pld_attributes: final_attrs.into(),
            pld_optional: optional,
        }
    }

    fn map_type_extension(&mut self, te: &pt0::TypeExtension) -> current::TypeExtension {
        current::TypeExtension {
            ptyext_path: self.map_longident_loc(&te.ptyext_path),
            ptyext_params: te
                .ptyext_params
                .iter()
                .map(|(t, v)| (self.push_core_type(t), map_variance(*v)))
                .collect(),
            ptyext_constructors: te
                .ptyext_constructors
                .iter()
                .map(|ec| self.map_extension_constructor(ec))
                .collect(),
            ptyext_private: map_private_flag(te.ptyext_private),
            ptyext_attributes: self.map_attributes(&te.ptyext_attributes).into(),
        }
    }

    fn map_extension_constructor(
        &mut self,
        ec: &pt0::ExtensionConstructor,
    ) -> current::ExtensionConstructor {
        current::ExtensionConstructor {
            pext_name: self.map_string_loc(&ec.pext_name),
            pext_kind: self.map_extension_constructor_kind(&ec.pext_kind),
            pext_loc: self.loc(&ec.pext_loc),
            pext_attributes: self.map_attributes(&ec.pext_attributes).into(),
        }
    }

    fn map_extension_constructor_kind(
        &mut self,
        eck: &pt0::ExtensionConstructorKind,
    ) -> current::ExtensionConstructorKind {
        match eck {
            pt0::ExtensionConstructorKind::Decl(args, ret) => {
                current::ExtensionConstructorKind::Pext_decl(
                    self.map_constructor_arguments(args),
                    ret.as_ref().map(|t| self.push_core_type(t)),
                )
            }
            pt0::ExtensionConstructorKind::Rebind(lid) => {
                current::ExtensionConstructorKind::Pext_rebind(self.map_longident_loc(lid))
            }
        }
    }

    // ========== Other declarations ==========

    fn map_value_description(&mut self, vd: &pt0::ValueDescription) -> current::ValueDescription {
        current::ValueDescription {
            pval_name: self.map_string_loc(&vd.pval_name),
            pval_type: self.push_core_type(&vd.pval_type),
            pval_prim: vd
                .pval_prim
                .iter()
                .map(|s| self.arena.push_string(s.clone()))
                .collect(),
            pval_attributes: self.map_attributes(&vd.pval_attributes).into(),
            pval_loc: self.loc(&vd.pval_loc),
        }
    }

    fn map_module_declaration(
        &mut self,
        md: &pt0::ModuleDeclaration,
    ) -> current::ModuleDeclaration {
        current::ModuleDeclaration {
            pmd_name: self.map_string_loc(&md.pmd_name),
            pmd_type: self.push_mod_type(&md.pmd_type),
            pmd_attributes: self.map_attributes(&md.pmd_attributes).into(),
            pmd_loc: self.loc(&md.pmd_loc),
        }
    }

    fn map_module_type_declaration(
        &mut self,
        mtd: &pt0::ModuleTypeDeclaration,
    ) -> current::ModuleTypeDeclaration {
        current::ModuleTypeDeclaration {
            pmtd_name: self.map_string_loc(&mtd.pmtd_name),
            pmtd_type: mtd.pmtd_type.as_ref().map(|mt| self.push_mod_type(mt)),
            pmtd_attributes: self.map_attributes(&mtd.pmtd_attributes).into(),
            pmtd_loc: self.loc(&mtd.pmtd_loc),
        }
    }

    fn map_module_binding(&mut self, mb: &pt0::ModuleBinding) -> current::ModuleBinding {
        current::ModuleBinding {
            pmb_name: self.map_string_loc(&mb.pmb_name),
            pmb_expr: self.push_mod_expr(&mb.pmb_expr),
            pmb_attributes: self.map_attributes(&mb.pmb_attributes).into(),
            pmb_loc: self.loc(&mb.pmb_loc),
        }
    }

    fn map_open_description(&mut self, od: &pt0::OpenDescription) -> current::OpenDescription {
        current::OpenDescription {
            popen_lid: self.map_longident_loc(&od.popen_lid),
            popen_override: map_override_flag(od.popen_override),
            popen_loc: self.loc(&od.popen_loc),
            popen_attributes: self.map_attributes(&od.popen_attributes).into(),
        }
    }

    fn map_include_declaration(
        &mut self,
        id: &pt0::IncludeDeclaration,
    ) -> current::IncludeDeclaration {
        current::IncludeDeclaration {
            pincl_mod: self.push_mod_expr(&id.pincl_mod),
            pincl_loc: self.loc(&id.pincl_loc),
            pincl_attributes: self.map_attributes(&id.pincl_attributes).into(),
        }
    }

    fn map_include_description(
        &mut self,
        id: &pt0::IncludeDescription,
    ) -> current::IncludeDescription {
        current::IncludeDescription {
            pincl_mod: self.push_mod_type(&id.pincl_mod),
            pincl_loc: self.loc(&id.pincl_loc),
            pincl_attributes: self.map_attributes(&id.pincl_attributes).into(),
        }
    }
}
